import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41460

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
  Nat.testBit (4276813000 * 2 ^ 32 + 4276811904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0227221810a98d82#64 ++ 0x20044e443021531b#64 ++ 0x067f223831f99feb#64 ++ 0xde0cfe447063f33f#64 : BitVec 256),
   (0x88900ce8c6661695#64 ++ 0x41112019d18ccc2d#64 ++ 0x99903ff9ce661fdf#64 ++ 0xbb33207ff39ccc3f#64 : BitVec 256),
   (0x216143420b82a321#64 ++ 0x8042c28684170546#64 ++ 0x61e3c3c60f87e3bf#64 ++ 0x7ec3c7878c1f0fc7#64 : BitVec 256),
   (0x5602b40570055846#64 ++ 0x00ac05680ae00ab0#64 ++ 0xfe03fc07f007fc7e#64 ++ 0xfdfc07f80fe00ff8#64 : BitVec 256),
   (0x7dd80007ad500078#64 ++ 0x02fbb0000f5aa000#64 ++ 0xfffc0007fff80079#64 ++ 0xf3fff8000ffff000#64 : BitVec 256),
   (0x7ffffbb000000000#64 ++ 0x04fffff760000000#64 ++ 0x7ffffff800000007#64 ++ 0xf4fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [13, 3]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000810a98d82 0x200000001021531b 0x0000000000019f80 0x080000000000033f

def z1 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831f99feb 0xde0cfe447063f33f

def z2 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f87e3bf 0x7ec3c7878c1f0fc7

def z3 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f007fc7e 0xfdfc07f80fe00ff8

def z4 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007fff80079 0xf3fff8000ffff000

def z5 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff800000007 0xf4fffffff0000000

def z6 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce661fdf 0xbb33207ff39ccc3f

def z7 : W := mkw 0x2161430000808100 0x0042c28600010102 0x61e3c3c0018183af 0x7ec3c78780030307

def z8 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x1e1c3c3800000000 0x803c387870000000

def z9 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7980ddc000000004 0x20f301bb80000000

def z10 : W := mkw 0x002143400282a301 0x8000428680050546 0x000003c000000380 0x0000000780000007

def z11 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff800000007 0xb033207ff0000000

def z12 : W := mkw 0x2140000209000020 0x0042800004120000 0x61e000060f800039 0x72c3c0000c1f0000

def z13 : W := mkw 0x80000ce842261685 0x41000019d0844c2d 0x01803ff80e061f9f 0x3a03007ff01c0c3f

def z14 : W := mkw 0x000000020980a120 0x8000000004130142 0x000000060181e020 0x000000000c0303c0

def z15 : W := mkw 0x7dfd4bb000000000 0x04fbfa9760000000 0x7ffc03f800000001 0xf0fff807f0000000

def z16 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xe603c007f007fc78 0x4dcc07800fe00ff8

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z18 : W := mkw 0x2140000209000020 0x0042800004120000 0x67fc00063ff80079 0xf2cff8000c7ff000

def z19 : W := mkw 0x236763121989a922 0xa046cec624331352 0x666fc0063199e020 0x44ccdf800c6333c0

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0x067c000031f80069 0xd20cf8000063f000

def z21 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe7ffc07f1fffc7f 0xfffcfff80fe3fff8

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000600000038 0x70c000000c000000

def z23 : W := mkw 0x0206201810a98d82 0x20040c403021531b 0x061c203831f99fe8 0x8a0c38407063f33f

def z24 : W := mkw 0x29f14ba000000000 0x0053e29740000000 0x79f3fff800000007 0xf4f3e7fff0000000

def z25 : W := mkw 0xa9f14feacfe6b7b5 0xc153e29fd59fcd6f 0xf9f3ffffcfe7ffff 0xfff3e7ffff9fcfff

def z26 : W := mkw 0x2bfffbb000000000 0x0457fff760000000 0x01fffff800000007 0x0403fffff0000000

def z27 : W := mkw 0x7763f3420b82a321 0x80eec7e684170546 0x7fe3ffc60f87e3bf 0xfeffc7ff8c1f0fc7

def z28 : W := mkw 0x5e9ebcb570055846 0x04bd3d796ae00ab0 0x9e1c3c39f0001c40 0x813c387873e00038

def z29 : W := mkw 0x0000040040041004 0x0000000800800820 0x98003c01c0061c5e 0xb930007803800c38

def z30 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xfffffffffff8007f 0xf7fffffffffff000

def z31 : W := mkw 0x0025021800a88580 0x20004a043001510b 0x007c023801f80381 0x0200f8047003f007

def z32 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x0003fff800000006 0x040007fff0000000

def z33 : W := mkw 0x0000000800200480 0x0000000010004009 0x0010223800601fcb 0x9a0020447000c03f

def z34 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001ce661fd8 0x0b000000039ccc3f

def z35 : W := mkw 0x5400000520000040 0x00a800000a400000 0xfe000007f0000078 0xf1fc00000fe00000

def z36 : W := mkw 0x5627b61570055846 0x00ac4f6c2ae00ab0 0xfe7ffe3ff007fc7f 0xfdfcfffc7fe00ff8

def z37 : W := mkw 0x214041420b022221 0x8042808284160444 0x6180c3c60e06639f 0x3ac301878c1c0cc7

def z38 : W := mkw 0x2367631a19a9ada2 0xa046cec63433535b 0x667fe23e31f9ffeb 0xdeccffc47c63f3ff

def z39 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xf9800007ce000010 0x21f300000f9c0000

def z40 : W := mkw 0x8ab72ef8d6ef9f97 0x61156e5df1addf3f 0x9fff3ff9ffff9fff 0xff3ffe7ff3ffff3f

def z41 : W := mkw 0x776ff31000000000 0x04eedfe620000000 0x667fe23800000003 0xd4ccffc470000000

def z42 : W := mkw 0x0000004002020201 0x0000000080040404 0x018003c00e000381 0x02030007801c0007

def z43 : W := mkw 0x0000040570055846 0x000000080ae00ab0 0x80000007f007fc78 0x090000000fe00ff8

def z44 : W := mkw 0x5602b00000000000 0x00ac056000000000 0x7e03fc0000000006 0xf4fc07f800000000

def z45 : W := mkw 0x29fd4bf20b82a321 0x8453fa97e4170546 0x61ffc3fe0f87e3bf 0x7ec3ff87fc1f0fc7

def z46 : W := mkw 0x0890000084400010 0x0011200001088000 0x99900001ce600059 0xb3332000039cc000

def z47 : W := mkw 0x88900ceacfe6b7b5 0xc1112019d59fcd6f 0x99903fffcfe7ffff 0xbb33207fff9fcfff

def z48 : W := mkw 0x0202200010010802 0x0004044000200210 0x067f200031f99c6b 0xde0cfe400063f338

def z49 : W := mkw 0x00254bb000000000 0x04004a9760000000 0x000003f800000000 0x00000007f0000000

def z50 : W := mkw 0x0202200010010802 0x0004044000200210 0x0603200030019c6a 0xdc0c064000600338

def z51 : W := mkw 0x5627b61d70adddc6 0x20ac4f6c3ae15bbb 0xfe7ffe3ff1ffffff 0xfffcfffc7fe3ffff

def z52 : W := mkw 0x5400940560045044 0x00a801280ac008a0 0xf800dc07c0066014 0x21f001b80f800cc0

def z53 : W := mkw 0x7dd8d9a7ad500078 0x06fbb1b34f5aa000 0xfffcddc7fff8007d 0xf3fff9bb8ffff000

def z54 : W := mkw 0x0890000084400010 0x0011200001088000 0x9ffc0001fff80079 0xf33ff80003fff000

def z55 : W := mkw 0x776ff31000000000 0x04eedfe620000000 0x666fc00000000000 0x44ccdf8000000000

def z56 : W := mkw 0x7dd8000084400010 0x00fbb00001088000 0xfffc0001ce600059 0xf3fff800039cc000

def z57 : W := mkw 0x82272ef852af9f87 0x61044e5df0a55f3f 0x00033ff800079f86 0x0c00067ff0000f3f

def z58 : W := mkw 0x0000004002020201 0x0000000080040404 0x000003c000060386 0x0800000780000c07

def z59 : W := mkw 0x2367631810a98d82 0x2046cec63021531b 0x67ffe3f831f99fef 0xfecfffc7f063f33f

def z60 : W := mkw 0x216143020980a120 0x8042c28604130142 0x6063c0060181e020 0x44c0c7800c0303c0

def z61 : W := mkw 0x88900ca8c4641494 0x411120195188c829 0x98103c39c0601c40 0x813020787380c038

def z62 : W := mkw 0x7fdab00000000000 0x00ffb56000000000 0x7ffffc0000000007 0xf4fffff800000000

def z63 : W := mkw 0x216147477b87fb67 0x8042c28e8ef70ff6 0xe1e3c3c7ff87ffff 0x7fc3c7878fff0fff

def z64 : W := mkw 0x88900448c6661695 0x41112008918ccc2d 0x99900001ce661fd9 0xbb332000039ccc3f

def z65 : W := mkw 0x5623b6057085d946 0x00ac476c0ae10bb2 0xfe63fe07f187ffff 0xfffcc7fc0fe30fff

def z66 : W := mkw 0xffff2effffff9fff 0x63fffe5dffffff3f 0xffff3fffffff9fff 0xfffffe7fffffff3f

def z67 : W := mkw 0x0227221010898902 0x20044e4420211312 0x066f000031998020 0x440cde0000633300

def z68 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0x9ffc0001fff80041 0x833ff80003fff000

def z69 : W := mkw 0x5e9eb8b5a4500058 0x06bd3d716b48a000 0x9e1c3c39f0780040 0x813c387873e0f000

def z70 : W := mkw 0x88900ce842261685 0x41112019d0844c2d 0x19903ff800061f87 0xb833207ff0000c3f

def z71 : W := mkw 0x2367635a1babafa3 0xa046cec6b437575f 0x67ffe3fe3fffffff 0xfecfffc7fc7fffff

def z72 : W := mkw 0x0206201810290c82 0x20040c4030205219 0x061c203830781c40 0x800c38407060f038

def z73 : W := mkw 0x7ffffbb800200480 0x04fffff770004009 0x7ffffff800601fcf 0xfefffffff000c03f

def z74 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x6183c3c60e07e396 0x2cc307878c1c0fc7

def z75 : W := mkw 0x002143400282a301 0x8000428680050546 0x0003c3c00007e386 0x0c00078780000fc7

def z76 : W := mkw 0x5c980005a4500058 0x02b930000b48a000 0x9e1c0001f0780040 0x813c380003e0f000

def z77 : W := mkw 0x80000408c4641494 0x410000081188c829 0x80000001c0601c40 0x010000000380c038

def z78 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x01fc03f800000001 0x0003f807f0000000

def z79 : W := mkw 0x7fffb61ffdfdddfe 0x22ffff6c3ffbfbbb 0xfffffe3fffffffff 0xfffffffc7fffffff

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0x6003c0060001e020 0x44c007800c0003c0

def z81 : W := mkw 0x7df94347afd2a379 0x82fbf2868f5fa546 0xffffc3c7ffffe3ff 0xffffff878fffffc7

def z82 : W := mkw 0x0227fbf00282a301 0x84044ff7e0050546 0x0003fff80007e386 0x0c0007fff0000fc7

def z83 : W := mkw 0x2140410209002020 0x8042808204120040 0x6000c00600006000 0x00c001800c0000c0

def z84 : W := mkw 0x7dd89407ed54507c 0x02fbb1280fdaa8a0 0xf980dc07ce066014 0x21f301b80f9c0cc0

def z85 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0x0003fc000007fc06 0x0c0007f800000ff8

def z86 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x67ffc3c63fffe3ff 0xfecfff878c7fffc7

def z87 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c1c60f87e034 0x64c3c7838c1f0fc0

def z88 : W := mkw 0x7ffffbb010898902 0x24fffff760211312 0x7ffffff831998027 0xf4fffffff0633300

def z89 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x0003223800019f82 0x0c0006447000033f

def z90 : W := mkw 0x29d8000000000000 0x0053b00000000000 0x01fc000000000001 0x0003f80000000000

def z91 : W := mkw 0x5602b00530014842 0x00ac05600a600290 0xfe03c007f001e078 0xf5fc07800fe003c0

def z92 : W := mkw 0x8ab72ef8c6661695 0x41156e5df18ccc2d 0x9fff3ff9ce661fdf 0xff3ffe7ff39ccc3f

def z93 : W := mkw 0x7ffffbf20b82a321 0x84fffff7e4170546 0x7ffffffe0f87e3bf 0xfefffffffc1f0fc7

def z94 : W := mkw 0x889008e886620691 0x41112011d10cc40d 0x19903ff80e600387 0xb233207ff01cc007

def z95 : W := mkw 0x7548000729100068 0x02ea90000e522000 0xfe6c0007f1980078 0xf1fcd8000fe33000

def z96 : W := mkw 0x00000007ad500078 0x020000000f5aa000 0x80000007fff80078 0x030000000ffff000

def z97 : W := mkw 0x80000ce842261685 0x41000019d0844c2d 0x00003ff800061f86 0x0800007ff0000c3f

def z98 : W := mkw 0x2165435a0baaa7a1 0xa042ca86b417554f 0x61ffc3fe0fffe3bf 0x7ec3ff87fc1fffc7

def z99 : W := mkw 0x0000004002020201 0x0000000080040404 0x6183c3c60e07e3bf 0x7ec307878c1c0fc7

def z100 : W := mkw 0x2367fbf20b82a321 0x8446cff7e4170546 0x61e3fffe0f87e3bf 0x7ec3c7fffc1f0fc7

def z101 : W := mkw 0x0227221000000000 0x00044e4420000000 0x067f223800000003 0xd40cfe4470000000

def z102 : W := mkw 0xa9d00ceacf6616b5 0x4153a019d59ecc2d 0xf9f03fffcfe61fff 0xfbf3e07fff9fcc3f

def z103 : W := mkw 0x7fffffb570055846 0x04ffffff6ae00ab0 0xfffffffff007fc7f 0xfdffffffffe00ff8

def z104 : W := mkw 0x776ff31810a98d82 0x24eedfe63021531b 0x667fe23831f99feb 0xdeccffc47063f33f

def z105 : W := mkw 0x7fff221fbdf98dfa 0x22fffe443f7bf31b 0xffff223ffff99ffb 0xfffffe447ffff33f

def z106 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xffffffffce000017 0xf5ffffffff9c0000

def z107 : W := mkw 0x2161430000000000 0x0042c28600000000 0x61e3c3c000000007 0x74c3c78780000000

def z108 : W := mkw 0x7dd8000000000000 0x00fbb00000000000 0x7ffc000000000001 0xf0fff80000000000

def z109 : W := mkw 0x7ffffbf7afd2a379 0x86fffff7ef5fa546 0xffffffffffffe3ff 0xffffffffffffffc7

def z110 : W := mkw 0x0202200010010802 0x0004044000200210 0x0603000030018020 0x440c060000600300

def z111 : W := mkw 0x7548000729100068 0x02ea90000e522000 0x666c000631980020 0x40ccd8000c633000

def z112 : W := mkw 0x5400940560045044 0x00a801280ac008a0 0x98001c01c0000000 0x0130003803800000

def z113 : W := mkw 0x7ffffbb810a98d82 0x24fffff77021531b 0x7ffffff831f99fef 0xfefffffff063f33f

def z114 : W := mkw 0x000008a000000000 0x0000001140000000 0x00003ff800000006 0x0000007ff0000000

def z115 : W := mkw 0x88900ca8c4641494 0x411120195188c829 0x99903c39ce601c59 0xb3332078739cc038

def z116 : W := mkw 0x5602b00000000000 0x00ac056000000000 0x6603c00000000000 0x44cc078000000000

def z117 : W := mkw 0xde92bcedf6675ed7 0x41bd2579dbeccebd 0xff93fffffe67ffff 0xffff27fffffccfff

def z118 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x066f000031f99fe8 0x4e0cde000063f33f

def z119 : W := mkw 0x5400940560045044 0x00a801280ac008a0 0xfe00dc07f006607c 0xf1fc01b80fe00cc0

def z120 : W := mkw 0x7ffffbb520000040 0x04fffff76a400000 0xfffffffff000007f 0xf5ffffffffe00000

def z121 : W := mkw 0x7ffffbbfbdf98dfa 0x26fffff77f7bf31b 0xfffffffffff99fff 0xfffffffffffff33f

def z122 : W := mkw 0x88900ce0c6461215 0x41112019c18c8c24 0x99801dc1ce060014 0x2133003b839c0c00

def z123 : W := mkw 0x889008e886620691 0x41112011d10cc40d 0x019003f80e600381 0x02032007f01cc007

def z124 : W := mkw 0x0227221010898902 0x20044e4420211312 0x0003000000018000 0x0400060000000300

def z125 : W := mkw 0xfdd80cefef7616fd 0x43fbb019dfdeec2d 0xfffc3ffffffe1fff 0xfbfff87ffffffc3f

def z126 : W := mkw 0x7ffffbb5a4500058 0x06fffff76b48a000 0xfffffff9f0780047 0xf5fffffff3e0f000

def z127 : W := mkw 0x7fdeb8b7ad500078 0x06ffbd716f5aa000 0xfffc3c3ffff80079 0xf3fff8787ffff000

def z128 : W := mkw 0x5400000000000000 0x00a8000000000000 0x7e00000000000000 0xf0fc000000000000

def z129 : W := mkw 0x0000004002020201 0x0000000080040404 0x018003c00e06039f 0x3a030007801c0c07

def z130 : W := mkw 0x089008a084400010 0x0011201141088000 0x99903ff9ce60005f 0xb333207ff39cc000

def z131 : W := mkw 0x5602b40050055806 0x00ac056800a00ab0 0x7e03fc000007fc06 0xfcfc07f800000ff8

def z132 : W := mkw 0x7ffff31000000000 0x04ffffe620000000 0x7fffc00000000001 0xf4ffff8000000000

def z133 : W := mkw 0x29fd4bb800a88580 0x2453fa977001510b 0x01fc03f801f80381 0x0203f807f003f007

def z134 : W := mkw 0x7ffffbf00282a301 0x84fffff7e0050546 0x7ffffff80007e387 0xfcfffffff0000fc7

def z135 : W := mkw 0x7df94307ad500078 0x02fbf2860f5aa000 0xffffc3c7fff8007f 0xf7ffff878ffff000

def z136 : W := mkw 0x21614347afd2a379 0x8242c2868f5fa546 0xe1e3c3c7ffffe3ff 0x7fc3c7878fffffc7

def z137 : W := mkw 0x0000940040045004 0x00000128008008a0 0x0000dc0000066004 0x000001b800000cc0

def z138 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x01903ff80e661f87 0x0a03207ff01ccc3f

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x18003c0000000006 0xb030007800000000

def z140 : W := mkw 0x88900cedf6675ed7 0x41112019dbeccebd 0x99903ffffe67ffff 0xbb33207ffffccfff

def z141 : W := mkw 0x7fffffb040041004 0x04ffffff60800820 0xfffffff9c0061c5f 0xfdfffffff3800c38

def z142 : W := mkw 0x0206201010090802 0x20040c4020201210 0x060c000030180000 0x000c180000603000

def z143 : W := mkw 0x7dfddbb000000000 0x04fbfbb760000000 0x79fcdff800000005 0x20f3f9bff0000000

def z144 : W := mkw 0x0227221000000000 0x00044e4420000000 0x066f000000000000 0x440cde0000000000

def z145 : W := mkw 0xfffffff8c6661695 0x45fffffff18ccc2d 0xfffffff9ce661fdf 0xfffffffff39ccc3f

def z146 : W := mkw 0x2140000209000020 0x0042800004120000 0x01e000000f800001 0x0203c000001f0000

def z147 : W := mkw 0x000000420b82a321 0x8000000084170546 0x000000060f87e3b8 0x0a0000000c1f0fc7

def z148 : W := mkw 0x5627b615708dd946 0x20ac4f6c2ae11bb2 0xfe6ffc07f19ffc7e 0xfdfcdff80fe33ff8

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x6003c0060007e03e 0x7cc007800c000fc0

def z150 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067c223831f81fc1 0x820cf8447063f03f

def z151 : W := mkw 0x7742b40779055866 0x00ee85680ef20ab0 0xffe3fc07ff87fc7f 0xffffc7f80fff0ff8

def z152 : W := mkw 0x5602b00000000000 0x00ac056000000000 0x7e03fc060007e03e 0xfcfc07f80c000fc0

def z153 : W := mkw 0x8000044df6675ed7 0x410000089beccebd 0x80000007fe67fff8 0x0b0000000ffccfff

def z154 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x01e003c00f800381 0x0203c007801f0007

def z155 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0x9e003c01f0001c40 0x813c007803e00038

def z156 : W := mkw 0x7dd80047afd2a379 0x82fbb0008f5fa546 0xfffc0007ffffe3f9 0xfbfff8000fffffc7

def z157 : W := mkw 0x88900ce0c6461215 0x41112019c18c8c24 0x99903ff9ce060017 0xb133207ff39c0c00

def z158 : W := mkw 0x002102420b82a321 0x8000420484170546 0x006302060f87e3bb 0x5e00c6040c1f0fc7

def z159 : W := mkw 0x0025021810a98d82 0x20004a043021531b 0x007c023831f99fe9 0x0a00f8047063f33f

def z160 : W := mkw 0x7dd808a7ad500078 0x02fbb0114f5aa000 0xfffc3ffffff8007f 0xf3fff87ffffff000

def z161 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7fefddc000000004 0x64ffdfbb80000000

def z162 : W := mkw 0x7df9430000000000 0x00fbf28600000000 0x7fffc3c000000007 0xf4ffff8780000000

def z163 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f81e3a1 0x46c3c7878c1f03c7

def z164 : W := mkw 0x0206b8b000000000 0x04040d7160000000 0x00003c3800000000 0x0000007870000000

def z165 : W := mkw 0x0021020000808100 0x0000420400010102 0x00630200018183ab 0x5e00c60400030307

def z166 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99803ff9ce061f96 0x2933007ff39c0c3f

def z167 : W := mkw 0x0000040040041004 0x0000000800800820 0x80000001c0061c58 0x0900000003800c38

def z168 : W := mkw 0x0227f31000000000 0x04044fe620000000 0x0003c00000000000 0x0400078000000000

def z169 : W := mkw 0x0000040560045044 0x000000080ac008a0 0x80000007c0066010 0x010000000f800cc0

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x067c000000000001 0xd00cf80000000000

def z171 : W := mkw 0xfff3ffefffe7fff7 0xc1ffe7ffdfffcfff 0xfff3ffffffe7ffff 0xffffe7ffffffcfff

def z172 : W := mkw 0x216143400282a301 0x8042c28680050546 0x61e3c3c00007e387 0x7cc3c78780000fc7

def z173 : W := mkw 0x29f14be20b82a321 0x8053e297c4170546 0x79f3fffe0f87e3bf 0xfef3e7fffc1f0fc7

def z174 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000c00600066014 0x20c001800c000cc0

def z175 : W := mkw 0x0025021000000000 0x00004a0420000000 0x007c023800000001 0x0000f80470000000

def z176 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007ce000011 0xf1fff8000f9c0000

def z177 : W := mkw 0x216143020980a120 0x8042c28604130142 0x6063c2060181e3ab 0x5ec0c7840c0303c7

def z178 : W := mkw 0x7dd8d9e20b022221 0x84fbb1b3c4160444 0x7980ddc60e066014 0x20f301bb8c1c0cc0

def z179 : W := mkw 0x29d800028d500038 0x0253b000051aa000 0x01fc00000ff80001 0x0203f800001ff000

def z180 : W := mkw 0x5627fbb000000000 0x04ac4ff760000000 0x7e03fff800000006 0xf4fc07fff0000000

def z181 : W := mkw 0xffffffffef7616fd 0x47ffffffffdeec2d 0xfffffffffffe1fff 0xfffffffffffffc3f

def z182 : W := mkw 0xfdd8044fef7616fd 0x43fbb0089fdeec2d 0xfffc0007fffe1ff9 0xfbfff8000ffffc3f

def z183 : W := mkw 0x0ab72ab000000000 0x00156e5560000000 0x1fff3ff800000007 0xf43ffe7ff0000000

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x6003c00000000006 0x74c0078000000000

def z185 : W := mkw 0x0202b00010014802 0x0004056000200290 0x0003c0000001e000 0x04000780000003c0

def z186 : W := mkw 0x5602b00530014842 0x00ac05600a600290 0x6603c0063001e020 0x44cc07800c6003c0

def z187 : W := mkw 0x0227221000000000 0x00044e4420000000 0x0003223800000002 0x0400064470000000

def z188 : W := mkw 0x214041420b022221 0x8042808284160444 0x6180c1c60e066014 0x20c301838c1c0cc0

def z189 : W := mkw 0x214000420b020221 0x0042800084160404 0x61e003c60f8603bf 0x7ac3c0078c1f0c07

def z190 : W := mkw 0x7df94347afd2a379 0x82fbf2868f5fa546 0xf9e3c3c7cf87e3bf 0x7ff3c7878f9f0fc7

def z191 : W := mkw 0x7dd84147af522279 0x82fbb0828f5ea444 0xfffcc1c7fffe607d 0xf3fff9838ffffcc0

def z192 : W := mkw 0x216d431000000000 0x0442da8620000000 0x006c000000000000 0x0000d80000000000

def z193 : W := mkw 0x776ff71570055846 0x04eedfee2ae00ab0 0xfe6ffc07f007fc7e 0xfdfcdff80fe00ff8

def z194 : W := mkw 0x5400000520000040 0x00a800000a400000 0xf8000007c0000010 0x21f000000f800000

def z195 : W := mkw 0xde92bcedf6675ed7 0x41bd2579dbeccebd 0x9f903ff9fe661fdf 0xbb3f207ff3fccc3f

def z196 : W := mkw 0x0000000810a98d82 0x200000001021531b 0x0000000031f99fe8 0x0a0000000063f33f

def z197 : W := mkw 0x7fdab40570055846 0x00ffb5680ae00ab0 0xfffffc07f007fc7f 0xfdfffff80fe00ff8

def z198 : W := mkw 0x29f143428fc2a331 0x8053e286851f8546 0xf9f3c3c7cfe7e3ff 0xfff3e7878f9fcfc7

def z199 : W := mkw 0x5602b00530014842 0x00ac05600a600290 0x7e03fc063001e026 0xf4fc07f80c6003c0

def z200 : W := mkw 0x5602b00530014842 0x00ac05600a600290 0x6603e0063001fc6a 0xdccc07c00c6003f8

def z201 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e0c3c60f866395 0x22c3c1878c1f0cc7

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000030000068 0xd00c000000600000

def z203 : W := mkw 0x00000005a4500058 0x020000000b48a000 0x80000001f0780040 0x0100000003e0f000

def z204 : W := mkw 0xdc900cede66616d5 0x41b92019dbcccc2d 0xff903ffffe661fff 0xfbff207ffffccc3f

def z205 : W := mkw 0xde92bce8c6661695 0x41bd2579d18ccc2d 0xff93fff9ce661fdf 0xffff27fff39ccc3f

def z206 : W := mkw 0x7fff221810a98d82 0x20fffe443021531b 0x7fff223831f99feb 0xfefffe447063f33f

def z207 : W := mkw 0x5602b407fd55587e 0x02ac05680ffaaab0 0xfe03fc07fffffc7e 0xfffc07f80ffffff8

def z208 : W := mkw 0x7763f7477b87fb67 0x80eec7ee8ef70ff6 0xffe3ffc7ff87ffff 0xffffc7ff8fff0fff

def z209 : W := mkw 0x7ffffbf20b82a321 0x84fffff7e4170546 0x7ffffff80f800387 0xf6fffffff01f0007

def z210 : W := mkw 0x000000400282a301 0x8000000080050546 0x000000000007e380 0x0800000000000fc7

def z211 : W := mkw 0x2140000209000020 0x0042800004120000 0x61e3c0060f87e03f 0x7ec3c7800c1f0fc0

def z212 : W := mkw 0x7ffffbb28d500038 0x06fffff7651aa000 0x7ffffff80ff80007 0xf6fffffff01ff000

def z213 : W := mkw 0xa9fd4bf886620691 0x4553fa97f10cc40d 0x01fc03f80e600381 0x0203f807f01cc007

def z214 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xffffc007ffffe07f 0xffffff800fffffc0

def z215 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7990fff800000007 0xb0f321fff0000000

def z216 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x667fe23e31ffffff 0xfeccffc47c63ffff

def z217 : W := mkw 0x889008a884600490 0x411120115108c009 0x0010003800600000 0x000020007000c000

def z218 : W := mkw 0x2140000209000020 0x0042800004120000 0x6060000601800020 0x40c0c0000c030000

def z219 : W := mkw 0x0000000729100068 0x020000000e522000 0x0000000631980020 0x000000000c633000

def z220 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7983fff800000006 0x24f307fff0000000

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x066c000031980020 0x400cd80000633000

def z222 : W := mkw 0xfffffbf886620691 0x45fffff7f10cc40d 0x7ffffff80e600387 0xf6fffffff01cc007

def z223 : W := mkw 0x5e92bca570055846 0x00bd25794ae00ab0 0xff93fffff007fc7f 0xfdff27ffffe00ff8

def z224 : W := mkw 0x0000000800200480 0x0000000010004009 0x0010023800600381 0x020020047000c007

def z225 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x818003c1ce661fdf 0x3b030007839ccc3f

def z226 : W := mkw 0xde92bcadf4655cd6 0x41bd25795be8cab9 0x9e103c39f0601c40 0x813c207873e0c038

def z227 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x19fc3ff800000007 0xb033f87ff0000000

def z228 : W := mkw 0x7dd8d9a7ad500078 0x06fbb1b34f5aa000 0xf980ddc7ce000014 0x21f301bb8f9c0000

def z229 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce601fc1 0x8333207ff39cc03f

def z230 : W := mkw 0x0890004086420211 0x00112000810c8404 0x999003c1ce6603df 0xbb332007839ccc07

def z231 : W := mkw 0x7dfd4bb7ad500078 0x06fbfa976f5aa000 0xfffc03fffff80079 0xf3fff807fffff000

def z232 : W := mkw 0x0021020000808100 0x0000420400010102 0x0003020000018382 0x0c00060400000307

def z233 : W := mkw 0x88900ca0c4441014 0x4111201941888820 0x98001c01c0000000 0x0130003803800000

def z234 : W := mkw 0x0025021000888100 0x20004a0420011102 0x006c000001980000 0x0000d80000033000

def z235 : W := mkw 0x7fff221000000000 0x00fffe4420000000 0x7fff223800000003 0xf4fffe4470000000

def z236 : W := mkw 0x7fdab407fd55587e 0x02ffb5680ffaaab0 0xfffffc07fffffc7f 0xfffffff80ffffff8

def z237 : W := mkw 0x889008e886620691 0x41112011d10cc40d 0x019023f80e601fcb 0x9a032047f01cc03f

def z238 : W := mkw 0x0000000800200480 0x0000000010004009 0x0000223800001f82 0x080000447000003f

def z239 : W := mkw 0x5400000520000040 0x00a800000a400000 0x9e000001f0000040 0x813c000003e00000

def z240 : W := mkw 0x0000000810a98d82 0x200000001021531b 0x067c000031f99fe9 0xda0cf8000063f33f

def z241 : W := mkw 0x0000040570055846 0x000000080ae00ab0 0x98003c07f007fc7e 0xb93000780fe00ff8

def z242 : W := mkw 0x7fdaf9a000000000 0x04ffb5f340000000 0x7f83fdc000000006 0xf4ff07fb80000000

def z243 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0x9e03fc01f007fc46 0x8d3c07f803e00ff8

def z244 : W := mkw 0x2367fbb000000000 0x0446cff760000000 0x61e3fff800000007 0x74c3c7fff0000000

def z245 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7e7ffc3800000000 0xc4fcfff870000000

def z246 : W := mkw 0x214000420b82a321 0x8042800084170546 0x61e000060f87e3b9 0x7ac3c0000c1f0fc7

def z247 : W := mkw 0xa9d808ea8f7206b9 0x4353b011d51ee40d 0x01fc03f80ff80381 0x0203f807f01ff007

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x000002000000038b 0x1a00000400000007

def z249 : W := mkw 0xfffffff8d6ef9f97 0x65fffffff1addf3f 0xfffffff9ffff9fff 0xfffffffff3ffff3f

def z250 : W := mkw 0x5e9ab405f455585e 0x02bd35680be8aab0 0x9e1c3c01f0781c40 0x813c387803e0f038

def z251 : W := mkw 0x216143020980a120 0x8042c28604130142 0x61e3c3c60181e027 0x74c3c7878c0303c0

def z252 : W := mkw 0xfdd80cafed7414fc 0x43fbb0195fdae829 0xfffc3c3ffff81c79 0xf3fff8787ffff038

def z253 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f023831f983a1 0x460cfe047063f307

def z254 : W := mkw 0x776ffbb000000000 0x04eedff760000000 0x666ffff800000006 0x44ccdffff0000000

def z255 : W := mkw 0x889008e086420211 0x41112011c10c8404 0x018001c00e000000 0x00030003801c0000

def z256 : W := mkw 0x5602b00530014842 0x00ac05600a600290 0x6603c0063007e03e 0x7ccc07800c600fc0

def z257 : W := mkw 0x29d800028d500038 0x0253b000051aa000 0x99fc0001cff80059 0xb333f800039ff000

def z258 : W := mkw 0xfdd80ce7ef56127d 0x43fbb019cfdeac24 0xf9801dc7ce060014 0x21f3003b8f9c0c00

def z259 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x0063223801819fab 0x5e00c6447003033f

def z260 : W := mkw 0x0890000084400010 0x0011200001088000 0x98100001c0600040 0x813020000380c000

def z261 : W := mkw 0x0000d9a000000000 0x040001b340000000 0x0000ddc000000004 0x000001bb80000000

def z262 : W := mkw 0xfffffff0c6461215 0x45ffffffe18c8c24 0xfffffff9ce060017 0xf5fffffff39c0c00

def z263 : W := mkw 0x8ab7fff8c6661695 0x45156ffff18ccc2d 0x9993fff9ce661fdf 0xbf3327fff39ccc3f

def z264 : W := mkw 0x82272ef852af9f87 0x61044e5df0a55f3f 0x067f3ff831ff9fef 0xde0cfe7ff063ff3f

def z265 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x066f223831999fa2 0x4c0cde447063333f

def z266 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xf803fc07c007fc16 0x2df007f80f800ff8

def z267 : W := mkw 0x216143020980a120 0x8042c28604130142 0x61e3c0060f81e039 0x76c3c7800c1f03c0

def z268 : W := mkw 0x214041420b022221 0x8042808284160444 0x018001c00e000000 0x00030003801c0000

def z269 : W := mkw 0x7dd80005a4500058 0x02fbb0000b48a000 0xfffc0001f0780041 0xf1fff80003e0f000

def z270 : W := mkw 0x0227221010898902 0x20044e4420211312 0x066f0200319983ab 0x5e0cde0400633307

def z271 : W := mkw 0x0021430000000000 0x0000428600000000 0x0003c3c000000006 0x0400078780000000

def z272 : W := mkw 0x0000000800a88580 0x200000001001510b 0x0000000001f80380 0x020000000003f007

def z273 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0xf993ffffce67ffff 0xfff327ffff9ccfff

def z274 : W := mkw 0x5400040570055846 0x00a800080ae00ab0 0xfe000007f007fc78 0xf9fc00000fe00ff8

def z275 : W := mkw 0x0000040570055846 0x000000080ae00ab0 0xe003c007f007fc7e 0x7dc007800fe00ff8

def z276 : W := mkw 0x29f943428fd2a339 0x8253f286851fa546 0x61ffc3c60fffe3bf 0x7ec3ff878c1fffc7

def z277 : W := mkw 0x0000000084400010 0x0000000001088000 0x80000001ce600058 0x03000000039cc000

def z278 : W := mkw 0x5627b2153089c942 0x20ac4f642a611392 0x666fc0063199e020 0x44ccdf800c6333c0

def z279 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x98103c39ce661fd8 0x8b302078739ccc3f

def z280 : W := mkw 0x29fd4bf20b82a321 0x8453fa97e4170546 0x01fc03f80f800381 0x0203f807f01f0007

def z281 : W := mkw 0x776ff31000000000 0x04eedfe620000000 0x67efc3c000000007 0x74cfdf8780000000

def z282 : W := mkw 0x7dd8000729100068 0x02fbb0000e522000 0x7ffc000631980021 0xf0fff8000c633000

def z283 : W := mkw 0x80000ce842261685 0x41000019d0844c2d 0x00103ff800661fcf 0x9a00207ff000cc3f

def z284 : W := mkw 0x2161430209000020 0x0042c28604120000 0x61e3c3c60f80003f 0x76c3c7878c1f0000

def z285 : W := mkw 0x0227fbb810a98d82 0x24044ff77021531b 0x067ffff831f99fef 0xde0cfffff063f33f

def z286 : W := mkw 0x7ffbf747ffd7fb7f 0x82fff7ee8fffaff6 0xffffffc7ffffffff 0xffffffff8fffffff

def z287 : W := mkw 0x2161434a1babafa3 0xa042c2869437575f 0x61e3c3c63fffffff 0x7ec3c7878c7fffff

def z288 : W := mkw 0x0206201810290c82 0x20040c4030205219 0x061f203830799c6a 0xdc0c3e407060f338

def z289 : W := mkw 0x2140000209000020 0x0042800004120000 0x618000060e000010 0x20c300000c1c0000

def z290 : W := mkw 0x0000040040041004 0x0000000800800820 0xf803fc07c007fc7e 0xfdf007f80f800ff8

def z291 : W := mkw 0x7ffffbb20980a120 0x84fffff764130142 0x7ffffffe0181e027 0xf4fffffffc0303c0

def z292 : W := mkw 0x7dd80407fd55587e 0x02fbb0080ffaaab0 0xfffc0007fffffc79 0xfbfff8000ffffff8

def z293 : W := mkw 0x7ffffbb084400010 0x04fffff761088000 0xfffffff9ce60005f 0xf7fffffff39cc000

def z294 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x9ffc3ff9fffe1fff 0xfb3ff87ff3fffc3f

def z295 : W := mkw 0x5602200530010842 0x00ac04400a600210 0xfe032007f0019c7a 0xfdfc06400fe00338

def z296 : W := mkw 0x88900ca8c4641494 0x411120195188c829 0x98103c39c0661c5e 0xb93020787380cc38

def z297 : W := mkw 0x0000000800200480 0x0000000010004009 0x067c223831f81feb 0xda0cf8447063f03f

def z298 : W := mkw 0x00000007ad500078 0x020000000f5aa000 0x867c0007fff80079 0xd30cf8000ffff000

def z299 : W := mkw 0x7ffffff77b87fb67 0x84ffffffeef70ff6 0xffffffffff87ffff 0xffffffffffff0fff

def z300 : W := mkw 0x7fffffb7fd55587e 0x06ffffff6ffaaab0 0xfffffffffffffc7f 0xfffffffffffffff8

def z301 : W := mkw 0x8000044fef7616fd 0x430000089fdeec2d 0x80000007fffe1ff8 0x0b0000000ffffc3f

def z302 : W := mkw 0x0000004802220681 0x000000009004440d 0x019023f80e661fdf 0xba032047f01ccc3f

def z303 : W := mkw 0x80000ce042061205 0x41000019c0840c24 0x00001dc000060004 0x0000003b80000c00

def z304 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0x9e003c07f007fc78 0x893c00780fe00ff8

def z305 : W := mkw 0x0000040040041004 0x0000000800800820 0x00003c0000061c06 0x0800007800000c38

def z306 : W := mkw 0x0021020000808100 0x0000420400010102 0x6063c2060187e3bf 0x7ec0c7840c030fc7

def z307 : W := mkw 0xd602bced72275ec7 0x41ac0579dae44ebd 0xfe03fffff007fffe 0xfdfc07ffffe00fff

def z308 : W := mkw 0x7ffffbb000808100 0x04fffff760010102 0x7ffffff8018183af 0xfefffffff0030307

def z309 : W := mkw 0x0000000800200480 0x0000000010004009 0x0000000000601fc8 0x0a0000000000c03f

def z310 : W := mkw 0x5602b44572075a47 0x00ac05688ae40eb4 0xff83ffc7fe07ffff 0xffff07ff8ffc0fff

def z311 : W := mkw 0x000000420b82a321 0x8000000084170546 0x6003c0060f87e3be 0x7ec007800c1f0fc7

def z312 : W := mkw 0x756943472b92a369 0x82ead2868e572546 0x67efc3c63f9fe3bf 0x7ecfdf878c7f3fc7

def z313 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903df9ce661c54 0xa133207bf39ccc38

def z314 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0x9e003c01f0061c5e 0xb93c007803e00c38

def z315 : W := mkw 0x0ab7fbb000000000 0x04156ff760000000 0x1993fff800000007 0xb43327fff0000000

def z316 : W := mkw 0x7df90207add08178 0x02fbf2040f5ba102 0xffff0207fff983fb 0xfffffe040ffff307

def z317 : W := mkw 0x5408000520100048 0x02a810000a402000 0x060c000030180000 0x000c180000603000

def z318 : W := mkw 0x7ffff317ad500078 0x06ffffe62f5aa000 0xffffc007fff80079 0xf7ffff800ffff000

def z319 : W := mkw 0x8000044842261685 0x4100000890844c2d 0x0000000000061f80 0x0800000000000c3f

def z320 : W := mkw 0x2165435a0baaa7a1 0xa042ca86b417554f 0x01fc03f80ff80381 0x0203f807f01ff007

def z321 : W := mkw 0x2367631000000000 0x0046cec620000000 0x67ffe3f800000007 0xf4cfffc7f0000000

def z322 : W := mkw 0x089c08b000000000 0x0411381160000000 0x001c003800000000 0x0000380070000000

def z323 : W := mkw 0x776ff31000000000 0x04eedfe620000000 0x7e6ffc0000000006 0xf4fcdff800000000

def z324 : W := mkw 0x0202240050051806 0x0004044800a00a30 0x9e033c01f0079c7e 0xfd3c067803e00f38

def z325 : W := mkw 0x5400940560045044 0x00a801280ac008a0 0xf800fc07c0067c5e 0xb9f001f80f800cf8

def z326 : W := mkw 0x756943072990a168 0x82ead2860e532142 0x666fc0063199e020 0x44ccdf800c6333c0

def z327 : W := mkw 0x5400040560041044 0x00a800080ac00820 0xfe003c07f0061c7e 0xf9fc00780fe00c38

def z328 : W := mkw 0x236363421b83ab23 0x8046c6c684370756 0x67e3e3c63f87ffff 0xfecfc7c78c7f0fff

def z329 : W := mkw 0xabf76ffadfefbfb7 0xe157eedff5bfdf7f 0xffffffffffffffff 0xffffffffffffffff

def z330 : W := mkw 0x5400000520000040 0x00a800000a400000 0xfe7c0007f1f80079 0xf3fcf8000fe3f000

def z331 : W := mkw 0x7dfd021fadf885f8 0x22fbfa043f5bf10b 0xfffc023ffff803f9 0xf3fff8047ffff007

def z332 : W := mkw 0x00000047afd2a379 0x820000008f5fa546 0x80000007ffffe3f8 0x0b0000000fffffc7

def z333 : W := mkw 0x7ffffbfa1babafa3 0xa4fffff7f437575f 0x7ffffffe3fffffff 0xfefffffffc7fffff

def z334 : W := mkw 0x7ffffbb810a98d82 0x24fffff77021531b 0x7ffffff800019f87 0xfcfffffff000033f

def z335 : W := mkw 0xfdd80ce7ef56127d 0x43fbb019cfdeac24 0xfffc1dc7fffe007d 0xf3fff83b8ffffc00

def z336 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffffe0007e03f 0xfcfffffffc000fc0

def z337 : W := mkw 0xa9f14bea8fe2a7b1 0xc153e297d51fc54f 0x01f003f80fe00381 0x0203e007f01fc007

def z338 : W := mkw 0x7ffffbb530014842 0x04fffff76a600290 0x7ffffffe3001e027 0xf4fffffffc6003c0

def z339 : W := mkw 0x5627ffb570055846 0x04ac4fff6ae00ab0 0xfe03fffff007fc7e 0xfdfc07ffffe00ff8

def z340 : W := mkw 0x75480007ad500078 0x02ea90000f5aa000 0xe66c0007fff80078 0x43ccd8000ffff000

def z341 : W := mkw 0x5c9898a000000000 0x04b9313140000000 0x18001c0000000000 0x0030003800000000

def z342 : W := mkw 0x88900ce0c6461215 0x41112019c18c8c24 0x99803dc1ce061c5e 0xb933007b839c0c38

def z343 : W := mkw 0x2367635a1babafa3 0xa046cec6b437575f 0x61e3e3fe0f87ffbf 0x7ec3c7c7fc1f0fff

def z344 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc01f0001c46 0xf5fc07f803e00038

def z345 : W := mkw 0x5606b41d702d5cc6 0x20ac0d683ae05ab9 0xfe1ffc3ff07ffc7e 0xfdfc3ff87fe0fff8

def z346 : W := mkw 0x214041420b82a321 0x8042808284170546 0x6180c1c60f87e3bc 0x2ac301838c1f0fc7

def z347 : W := mkw 0x88900cefef7616fd 0x43112019dfdeec2d 0x99903ffffffe1fff 0xbb33207ffffffc3f

def z348 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010223800000003 0x9000204470000000

def z349 : W := mkw 0x7fff635fbffbaffb 0xa2fffec6bf7ff75f 0xffffe3ffffffffff 0xffffffc7ffffffff

def z350 : W := mkw 0x0202200010010802 0x0004044000200210 0x0003200000019c02 0x0c00064000000338

def z351 : W := mkw 0x5ebffbb000000000 0x04bd7ff760000000 0x1e1ffff800000006 0x843c3ffff0000000

def z352 : W := mkw 0x7dd84147af522279 0x82fbb0828f5ea444 0xf980c1c7ce066014 0x21f301838f9c0cc0

def z353 : W := mkw 0x776ff31729100068 0x06eedfe62e522000 0x666fc00631980020 0x44ccdf800c633000

def z354 : W := mkw 0x8a962cf8d66f1e97 0x61152c59f1acde3d 0x9f9c3ff9fe7e1fdf 0xbb3f387ff3fcfc3f

def z355 : W := mkw 0x236763520b82a321 0x8046cec6a4170546 0x67ffe3fe0f87e3bf 0xfecfffc7fc1f0fc7

def z356 : W := mkw 0xfdd808efaf7206f9 0x43fbb011df5ee40d 0xfffc03fffff803f9 0xf3fff807fffff007

def z357 : W := mkw 0x80000448d6ef9f97 0x6100000891addf3f 0x80000001ffff9ff8 0x0b00000003ffff3f

def z358 : W := mkw 0xa161474acfe6b7b5 0xc142c28e959fcd6f 0xe1e3c3c7cfe7ffff 0x7fc3c7878f9fcfff

def z359 : W := mkw 0x29d849a000000000 0x0453b09340000000 0x018001c000000000 0x0003000380000000

def z360 : W := mkw 0x7763f7077985f966 0x80eec7ee0ef30bf2 0xfe63fc07f187fc7e 0xfdfcc7f80fe30ff8

def z361 : W := mkw 0x5c900005a4400050 0x00b920000b488000 0xff900007fe600079 0xf3ff20000ffcc000

def z362 : W := mkw 0x5602b00520000040 0x00ac05600a400000 0xfe03fc07f000007e 0xf5fc07f80fe00000

def z363 : W := mkw 0x774ab4077915586e 0x02ee95680ef22ab0 0xfe6ffc07f19ffc7e 0xfdfcdff80fe33ff8

def z364 : W := mkw 0x8227fff842261685 0x45044ffff0844c2d 0x0003fff800061f86 0x0c0007fff0000c3f

def z365 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x01e303c00f8183ab 0x5e03c607801f0307

def z366 : W := mkw 0x5602b4477b87fb67 0x80ac05688ef70ff6 0xfe03fc07ff87fffe 0xfffc07f80fff0fff

def z367 : W := mkw 0x7fdafda570055846 0x04ffb5fb4ae00ab0 0xff83fdc7f007fc7e 0xfdff07fb8fe00ff8

def z368 : W := mkw 0x5c980007ad500078 0x02b930000f5aa000 0x9e1c0007fff80078 0x833c38000ffff000

def z369 : W := mkw 0x0000040050055806 0x0000000800a00ab0 0x000000000007fc00 0x0800000000000ff8

def z370 : W := mkw 0x7ffffbb010010802 0x04fffff760200210 0x7ffffff830019c6f 0xfcfffffff0600338

def z371 : W := mkw 0x0000040d70adddc6 0x200000081ae15bbb 0x80000007f1fffff8 0x0b0000000fe3ffff

def z372 : W := mkw 0x2161430000000000 0x0042c28600000000 0x01e003c000000001 0x0003c00780000000

def z373 : W := mkw 0x5602b00000000000 0x00ac056000000000 0x1e003c0000000000 0x803c007800000000

def z374 : W := mkw 0x7fffffbd70adddc6 0x24ffffff7ae15bbb 0xfffffffff1ffffff 0xffffffffffe3ffff

def z375 : W := mkw 0x0202b00000000000 0x0004056000000000 0x0003fc0000000006 0x040007f800000000

def z376 : W := mkw 0x776f22173999896a 0x22eede442e733312 0x666f000631998020 0x44ccde000c633300

def z377 : W := mkw 0x8a962cb8d46d1c96 0x61152c5971a8da39 0x9e1c3c39f0781c40 0x813c387873e0f038

def z378 : W := mkw 0x7ffffbb729100068 0x06fffff76e522000 0x7ffffffe31980027 0xf4fffffffc633000

def z379 : W := mkw 0x80000ce8c6661695 0x41000019d18ccc2d 0x80003ff9ce661fde 0x0b00007ff39ccc3f

def z380 : W := mkw 0xa1614fea4ba6b7a5 0xc142c29fd4974d6f 0x61e3fffe0f87ffbf 0x7ec3c7fffc1f0fff

def z381 : W := mkw 0x2161020209808120 0x0042c20404130102 0x61e302060f8183bb 0x7ec3c6040c1f0307

def z382 : W := mkw 0x08900ca040041004 0x0011201940800820 0x99903ff9c0061c5f 0xb933207ff3800c38

def z383 : W := mkw 0x0227261d70adddc6 0x20044e4c3ae15bbb 0x867f223ff1fffffb 0xdf0cfe447fe3ffff

def z384 : W := mkw 0x7fdef9b000000000 0x04ffbdf360000000 0x7f9cfdf800000004 0xa0ff39fbf0000000

def z385 : W := mkw 0x2140000000000000 0x0042800000000000 0x61e0000000000001 0x70c3c00000000000

def z386 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0x9803fc01c007fc5e 0xbd3007f803800ff8

def z387 : W := mkw 0x08900007ad500078 0x021120000f5aa000 0x99900007fff80079 0xb33320000ffff000

def z388 : W := mkw 0x0000004002020201 0x0000000080040404 0x000000000e060398 0x0a000000001c0c07

def z389 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x01e003c00f86039f 0x3a03c007801f0c07

def z390 : W := mkw 0x29fd021a8df885b8 0x2253fa04351bf10b 0x01fc02380ff80381 0x0203f804701ff007

def z391 : W := mkw 0x88900ce8d6ef9f97 0x61112019d1addf3f 0x99903ff9ffff9fff 0xbb33207ff3ffff3f

def z392 : W := mkw 0xa9f14fe2cfc6b335 0xc153e29fc59f8d66 0xf9e3dfc7cf87e3bf 0x7ff3c7bf8f9f0fc7

def z393 : W := mkw 0x7ffffbb209000020 0x04fffff764120000 0x7ffffffe0f80003f 0xf6fffffffc1f0000

def z394 : W := mkw 0x5e92b405f4455856 0x00bd25680be88ab0 0xff93fc07fe67fc7f 0xffff27f80ffccff8

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x018003c000000007 0x3003000780000000

def z396 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff831f8006f 0xf6fffffff063f000

def z397 : W := mkw 0xfdd80ce8c6661695 0x41fbb019d18ccc2d 0xfffc3ff9ce661fdf 0xfbfff87ff39ccc3f

def z398 : W := mkw 0x0000000000808100 0x0000000000010102 0x00000000018183a8 0x0a00000000030307

def z399 : W := mkw 0x29d800028d500038 0x0253b000051aa000 0x018000000e000000 0x00030000001c0000

def z400 : W := mkw 0x0227221010010802 0x00044e4420200210 0x067f223830019c6b 0xdc0cfe4470600338

def z401 : W := mkw 0x0000000800200480 0x0000000010004009 0x0010203800601c40 0x800020407000c038

def z402 : W := mkw 0x7fff2217ad500078 0x02fffe442f5aa000 0xffff223ffff8007b 0xf7fffe447ffff000

def z403 : W := mkw 0xdc909cede66656d5 0x41b92139dbccccad 0xf990ffffce667fdf 0xbbf321ffff9cccff

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000000600049 0x920020000000c000

def z405 : W := mkw 0x7fff2217bdd9897a 0x22fffe442f7bb312 0xffff0007fff98079 0xf7fffe000ffff300

def z406 : W := mkw 0x2363f7425b87fb27 0x8046c7ee84b70ff6 0x61e3ffc60f87ffbf 0x7ec3c7ff8c1f0fff

def z407 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe00fc07f0067c54 0xa1fc01f80fe00cf8

def z408 : W := mkw 0x88900ca8c4641494 0x411120195188c829 0x98103e39c0601fcb 0x9b30207c7380c03f

def z409 : W := mkw 0x216143020980a120 0x8042c28604130142 0x0060000001800000 0x0000c00000030000

def z410 : W := mkw 0x29d000028d400030 0x0053a000051a8000 0xf9f00007cfe00079 0xf3f3e0000f9fc000

def z411 : W := mkw 0x8000044acfe6b7b5 0xc1000008959fcd6f 0x80000007cfe7fff8 0x0b0000000f9fcfff

def z412 : W := mkw 0x2161434002020201 0x0042c28680040404 0x61e3c3c00e06039f 0x7ec3c787801c0c07

def z413 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0x9e033c01f0019c6a 0xdd3c067803e00338

def z414 : W := mkw 0x0000040840241484 0x0000000810804829 0x98103e39c0661fdf 0xbb30207c7380cc3f

def z415 : W := mkw 0x0223f7405287fb07 0x800447ee80a50ff6 0x0003ffc00007ff86 0x0c0007ff80000fff

def z416 : W := mkw 0x7763f30000000000 0x00eec7e600000000 0x7fe3ffc000000007 0xf4ffc7ff80000000

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x007c000001f80001 0x0200f8000003f000

def z418 : W := mkw 0x7548000729100068 0x02ea90000e522000 0x6000000600000000 0x00c000000c000000

def z419 : W := mkw 0x0898000084500018 0x021130000108a000 0x001c000000780000 0x000038000000f000

def z420 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0x6003fc060007fc3e 0x7cc007f80c000ff8

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000200000001c4a 0x9800004000000038

def z422 : W := mkw 0x5e9eb8b810290c82 0x24bd3d7170205219 0x1e1c3c3830781c40 0x803c38787060f038

def z423 : W := mkw 0x0000000520000040 0x000000000a400000 0x80000007f0000078 0x010000000fe00000

def z424 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223800019f83 0xdc0cfe447000033f

def z425 : W := mkw 0x0227b61850addd86 0x20044f6c30a15bbb 0x0003fe380007ff86 0x0c0007fc70000fff

def z426 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f203831f99c60 0xc40cfe407063f338

def z427 : W := mkw 0xd602b44df6675ed7 0x41ac05689beccebd 0xfe03fc07fe67fffe 0xfffc07f80ffccfff

def z428 : W := mkw 0x800008e802220681 0x41000011d004440d 0x000003f800000380 0x00000007f0000007

def z429 : W := mkw 0x0227221010898902 0x20044e4420211312 0x067f000031f98069 0xd60cfe000063f300

def z430 : W := mkw 0xfdd80cefef7616fd 0x43fbb019dfdeec2d 0xf9903fffce661fdf 0xbbf3207fff9ccc3f

def z431 : W := mkw 0x0206201810290c82 0x20040c4030205219 0x067c203831f81c69 0xd20cf8407063f038

def z432 : W := mkw 0x2bff6bb810a98d82 0x2457fed77021531b 0x07ff23f831f99feb 0xde0ffe47f063f33f

def z433 : W := mkw 0x2161430000000000 0x0042c28600000000 0x6063c00000000000 0x44c0c78000000000

def z434 : W := mkw 0x88900ca8c4641494 0x411120195188c829 0x99903ff9c0601c47 0xb133207ff380c038

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000031f80068 0x020000000063f000

def z436 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xf9800007fff80078 0x23f300000ffff000

def z437 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x0603223830019fea 0xdc0c06447060033f

def z438 : W := mkw 0x0227221010898902 0x20044e4420211312 0x066f200031999c6a 0xdc0cde4000633338

def z439 : W := mkw 0x7fdab407fd55587e 0x02ffb5680ffaaab0 0xff83fc07fe07fc7e 0xfdff07f80ffc0ff8

def z440 : W := mkw 0x7763f3473b83eb63 0x80eec7e68e7707d6 0x67e3c3c63f87e3bf 0x7ecfc7878c7f0fc7

def z441 : W := mkw 0x7540d5476b067265 0x80ea81aa8ed60ce4 0xf980ddc7ce066014 0x21f301bb8f9c0cc0

def z442 : W := mkw 0x5602b40560045044 0x00ac05680ac008a0 0xfe03fc07c0066016 0xf5fc07f80f800cc0

def z443 : W := mkw 0x5602b40d70255cc6 0x00ac05681ae04ab9 0xfe13fe3ff067ffff 0xfffc27fc7fe0cfff

def z444 : W := mkw 0x5602b00530014842 0x00ac05600a600290 0x0600000030000000 0x000c000000600000

def z445 : W := mkw 0x0227635812abaf83 0xa0044ec6b025575f 0x067fe3f831ffffef 0xde0cffc7f063ffff

def z446 : W := mkw 0x5c980005a4500058 0x02b930000b48a000 0x9f9c0001fe780059 0xb33f380003fcf000

def z447 : W := mkw 0x88b50af886ea8791 0x61116a15f10dd50f 0x01fc03f80ff80381 0x0203f807f01ff007

def z448 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x007f223801f99f83 0x0e00fe447003f33f

def z449 : W := mkw 0x0227261850ad9d86 0x20044e4c30a15b3b 0x9e7f3e39f1ff9fff 0xff3cfe7c73e3ff3f

def z450 : W := mkw 0x0ab72ab810a98d82 0x20156e557021531b 0x1fff3ff831f99fef 0xfe3ffe7ff063f33f

def z451 : W := mkw 0x0000044042061205 0x0000000880840c24 0x99803fc1ce061fdf 0xbb33007f839c0c3f

def z452 : W := mkw 0x7763f3073981e962 0x80eec7e60e7303d2 0x6663c0063181e020 0x44ccc7800c6303c0

def z453 : W := mkw 0x774ab0073911486a 0x02ee95600e722290 0x666fc0063199e020 0x44ccdf800c6333c0

def z454 : W := mkw 0x0227221810290c82 0x20044e4430205219 0x067f223830781c43 0xd40cfe447060f038

def z455 : W := mkw 0x08900400c4441014 0x0011200801888820 0x99903c01ce661c5f 0xbb332078039ccc38

def z456 : W := mkw 0x2367221a19a98da2 0x2046ce443433531b 0x67ff223e3ff99ffb 0xfecffe447c7ff33f

def z457 : W := mkw 0x7548000000000000 0x00ea900000000000 0x666c000000000000 0x40ccd80000000000

def z458 : W := mkw 0x7ffffbb800a88580 0x24fffff77001510b 0x7ffffff801f80387 0xf6fffffff003f007

def z459 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x1ffc3ff800000001 0x803ff87ff0000000

def z460 : W := mkw 0x29f943428fd2a339 0x8253f286851fa546 0x01fc03c00ff80381 0x0203f807801ff007

def z461 : W := mkw 0x7dd808a000000000 0x00fbb01140000000 0x7ffc3ff800000007 0xf0fff87ff0000000

def z462 : W := mkw 0x089008a000000000 0x0011201140000000 0x019003f800000001 0x00032007f0000000

def z463 : W := mkw 0x5c980005a4500058 0x02b930000b48a000 0x98000001c0000000 0x0130000003800000

def z464 : W := mkw 0x80000ca840241484 0x4100001950804829 0x00003c3800001c00 0x0000007870000038

def z465 : W := mkw 0x7fffffb050055806 0x04ffffff60a00ab0 0x7ffffff80007fc07 0xfcfffffff0000ff8

def z466 : W := mkw 0x7dd8000520000040 0x00fbb0000a400000 0xfffc0007f0000079 0xf1fff8000fe00000

def z467 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x0003223831f99fea 0x0e0006447063f33f

def z468 : W := mkw 0xa9fd4ff8c6661695 0x4553fa9ff18ccc2d 0x99fc3ff9ce661fdf 0xbb33f87ff39ccc3f

def z469 : W := mkw 0x5400900000000000 0x00a8012000000000 0x7800dc0000000004 0x20f001b800000000

def z470 : W := mkw 0x7763f70570055846 0x00eec7ee0ae00ab0 0xffe3ffc7f007fc7f 0xfdffc7ff8fe00ff8

def z471 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0x67fc00063ff80021 0x42cff8000c7ff000

def z472 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0x00003c0000001c00 0x0000007800000038

def z473 : W := mkw 0x5c98000000000000 0x00b9300000000000 0x1e1c000000000000 0x803c380000000000

def z474 : W := mkw 0x0202200000000000 0x0004044000000000 0x0603200000000002 0xd40c064000000000

def z475 : W := mkw 0xdc909ce5e6465255 0x41b92139cbcc8ca4 0xf980ddc7ce066014 0x21f301bb8f9c0cc0

def z476 : W := mkw 0x8a922ce8d6671e97 0x41152459d1acce3d 0x9f933ff9fe679fff 0xff3f267ff3fccf3f

def z477 : W := mkw 0x80000ce842261685 0x41000019d0844c2d 0x98003ff9c0061fde 0xb930007ff3800c3f

def z478 : W := mkw 0x7dd89407ed54507c 0x02fbb1280fdaa8a0 0xfffcdc07fffe607d 0xf3fff9b80ffffcc0

def z479 : W := mkw 0x776ff31530014842 0x04eedfe62a600290 0x666fc0063001e020 0x44ccdf800c6003c0

def z480 : W := mkw 0x8000004886620691 0x41000000910cc40d 0x000000000e600380 0x02000000001cc007

def z481 : W := mkw 0x776ff31010898902 0x24eedfe620211312 0x666fc00031998020 0x44ccdf8000633300

def z482 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x01e3c3c00f87e387 0x0e03c787801f0fc7

def z483 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x067ffff800000007 0xd40cfffff0000000

def z484 : W := mkw 0x000000420b82a321 0x8000000084170546 0x018003c60f87e3bf 0x3a0300078c1f0fc7

def z485 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f001fc60 0xc5fc07f80fe003f8

def z486 : W := mkw 0x0021020800a08580 0x000042041001410b 0x0073223801e19feb 0xde00e6447003c33f

def z487 : W := mkw 0x0000000810a98d82 0x200000001021531b 0x0010223831f99feb 0x9a0020447063f33f

def z488 : W := mkw 0x214041420b022221 0x8042808284160444 0x6183c1c60e07e03e 0x7cc307838c1c0fc0

def z489 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x7e1ffc3800000006 0xf4fc3ff870000000

def z490 : W := mkw 0x88b14fe8c6e6b795 0xc111629fd18dcd6f 0x9993fff9ce67ffdf 0xbf3327fff39ccfff

def z491 : W := mkw 0xa9d80ceacf7616bd 0x4353b019d59eec2d 0x99fc3ff9cffe1fdf 0xbb33f87ff39ffc3f

def z492 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x01e003c60f87e3b9 0x0a03c0078c1f0fc7

def z493 : W := mkw 0x80214fe842a6b785 0xc100429fd0854d6f 0x0003fff80007ff86 0x0c0007fff0000fff

def z494 : W := mkw 0x0025021800a88580 0x20004a043001510b 0x067c023831f803e9 0xd20cf8047063f007

def z495 : W := mkw 0x82272658d6ef9f97 0x61044e4cb1addf3f 0x867f2239ffff9ffb 0xdf0cfe4473ffff3f

def z496 : W := mkw 0x5602b40040041004 0x00ac056800800820 0xfe03fc01c0061c5e 0xfdfc07f803800c38

def z497 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99901ff9ce660395 0x2333203ff39ccc07

def z498 : W := mkw 0x5c980005a4500058 0x02b930000b48a000 0xfe1c0007f0780078 0xf1fc38000fe0f000

def z499 : W := mkw 0x756143472b82a361 0x80eac2868e570546 0xffe3c3c7ff87e3ff 0xffffc7878fff0fc7

def z500 : W := mkw 0x002143400282a301 0x8000428680050546 0x6003c3c60007e3be 0x7cc007878c000fc7

def z501 : W := mkw 0x8ab72af896eb8f93 0x61156e55f12dd71f 0x07ff23f83ff99feb 0xde0ffe47f07ff33f

def z502 : W := mkw 0x0890000000000000 0x0011200000000000 0x1990000000000001 0xb033200000000000

def z503 : W := mkw 0x0000004002020201 0x0000000080040404 0x018001c00e060014 0x20030003801c0c00

def z504 : W := mkw 0x889008e886620691 0x41112011d10cc40d 0x019003f80e66039f 0x3a032007f01ccc07

def z505 : W := mkw 0x29fd4bb28d500038 0x0653fa97651aa000 0x01fc03f80ff80001 0x0203f807f01ff000

def z506 : W := mkw 0x0ab7221894e98d92 0x20156e443129d31b 0x9fff2239fff99ffb 0xff3ffe4473fff33f

def z507 : W := mkw 0x5602b40d70adddc6 0x20ac05681ae15bbb 0xfe03fc07f1fffffe 0xfffc07f80fe3ffff

def z508 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x1f9c3ff800000007 0xb03f387ff0000000

def z509 : W := mkw 0x7ffffbf20b022221 0x84fffff7e4160444 0x7ffffffe0e066017 0xf4fffffffc1c0cc0

def z510 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80102239ce661fdb 0x9b002044739ccc3f

def z511 : W := mkw 0x0000040570055846 0x000000080ae00ab0 0x80000001f0001c40 0x0100000003e00038

def z512 : W := mkw 0xfffffffdf6675ed7 0x45fffffffbeccebd 0xfffffffffe67ffff 0xfffffffffffccfff

def z513 : W := mkw 0x88900ce0c6461215 0x41112019c18c8c24 0x99801fc1ce06039f 0x3b33003f839c0c07

def z514 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0x0603fc003007fc6e 0xdc0c07f800600ff8

def z515 : W := mkw 0x7548d10000000000 0x04ea91a200000000 0x6000c00000000000 0x00c0018000000000

def z516 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x6063c0060f87e3b8 0x4ec0c7800c1f0fc7

def z517 : W := mkw 0x0227221010898902 0x20044e4420211312 0x067f223831998023 0xd40cfe4470633300

def z518 : W := mkw 0x7742f5477b077a67 0x80ee85ea8ef60ef4 0xff83fdc7fe07fc7e 0xfdff07fb8ffc0ff8

def z519 : W := mkw 0x0000414002022201 0x8000008280040444 0x0000c1c000066004 0x0000018380000cc0

def z520 : W := mkw 0x7dd80047af520279 0x02fbb0008f5ea404 0xfffc03c7fffe03ff 0xfbfff8078ffffc07

def z521 : W := mkw 0x7ffffbf002020201 0x04fffff7e0040404 0x7ffffff80e06039f 0xfefffffff01c0c07

def z522 : W := mkw 0x80000440c6461215 0x41000008818c8c24 0x80000001ce060010 0x01000000039c0c00

def z523 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03dc07f007e034 0x65fc07b80fe00fc0

def z524 : W := mkw 0x0000040040041004 0x0000000800800820 0x98003c01c0001c40 0x8130007803800038

def z525 : W := mkw 0x0227225a1babafa3 0xa0044e44b437575f 0x067f223e3ffffffb 0xde0cfe447c7fffff

def z526 : W := mkw 0x5e9e201db4790cda 0x22bd3c403b68f219 0x9e1c2039f0781c40 0x813c384073e0f038

def z527 : W := mkw 0xde92bce5f6475a57 0x41bd2579cbec8eb4 0xff83fdc7fe07fc7e 0xfdff07fb8ffc0ff8

def z528 : W := mkw 0x0021020000808100 0x0000420400010102 0x0060020001800381 0x0200c00400030007

def z529 : W := mkw 0x0890000084400010 0x0011200001088000 0x019000000e600001 0x02032000001cc000

def z530 : W := mkw 0x089008a800200480 0x0011201150004009 0x19903ff800601fcf 0xba33207ff000c03f

def z531 : W := mkw 0x000000420b82a321 0x8000000084170546 0x000000000f800380 0x02000000001f0007

def z532 : W := mkw 0xffdabcefff775eff 0x43ffb579dffeeebd 0xffffffffffffffff 0xffffffffffffffff

def z533 : W := mkw 0x29d80007ad500078 0x0253b0000f5aa000 0x81fc0007fff80079 0x0303f8000ffff000

def z534 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe003c07f0001c78 0xf1fc00780fe00038

def z535 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x98003c01ce661fde 0xbb300078039ccc3f

def z536 : W := mkw 0x7dd8000000000000 0x00fbb00000000000 0x7980000000000000 0x20f3000000000000

def z537 : W := mkw 0x5400000520000040 0x00a800000a400000 0xfe03c007f007e07e 0xfdfc07800fe00fc0

def z538 : W := mkw 0x5ebf221db4f98dda 0x22bd7e443b69f31b 0x9e7f2239f1f99feb 0xdf3cfe4473e3f33f

def z539 : W := mkw 0x5627221d30a98dc2 0x20ac4e443a61531b 0xfe7f223ff1f99ffb 0xfffcfe447fe3f33f

def z540 : W := mkw 0x089008a000000000 0x0011201140000000 0x18103c3800000000 0x8030207870000000

def z541 : W := mkw 0x216143420b022221 0x8042c28684160444 0x61e3c3c60e066017 0x74c3c7878c1c0cc0

def z542 : W := mkw 0x0202240570055846 0x000404480ae00ab0 0x86032007f007fc7a 0xdd0c06400fe00ff8

def z543 : W := mkw 0xfdd8dde8c6661695 0x45fbb1bbd18ccc2d 0xf990fff9ce661fdf 0xbbf321fff39ccc3f

def z544 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x98103ff9c0661fc6 0x8930207ff380cc3f

def z545 : W := mkw 0x0202200010010802 0x0004044000200210 0x6603e0063007fc7e 0xfccc07c00c600ff8

def z546 : W := mkw 0x5ebfbab000000000 0x04bd7f7560000000 0x1e7f3e3800000003 0xd43cfe7c70000000

def z547 : W := mkw 0x236763521b8bab23 0xa046cec6a4371756 0x67efc3c63f9fe3bf 0x7ecfdf878c7f3fc7

def z548 : W := mkw 0xfdf94fefeff6b7fd 0xc3fbf29fdfdfed6f 0xffffffffffffffff 0xffffffffffffffff

def z549 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xf9fc0007cff80011 0x23f3f8000f9ff000

def z550 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xffec0007ff980030 0x61ffd8000fff3000

def z551 : W := mkw 0x5e9ebcb570055846 0x04bd3d796ae00ab0 0xfe1ffc3ff007fc7e 0xfdfc3ff87fe00ff8

def z552 : W := mkw 0x000000420b022221 0x8000000084160444 0x000000060e066010 0x000000000c1c0cc0

def z553 : W := mkw 0x2367635a1babafa3 0xa046cec6b437575f 0x07ff23f83ff99feb 0xde0ffe47f07ff33f

def z554 : W := mkw 0xde92bcadf4655cd6 0x41bd25795be8cab9 0xfe13fc3ff067fc7e 0xfdfc27f87fe0cff8

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0x061c000030780040 0x800c38000060f000

def z556 : W := mkw 0x0227ffb050055806 0x04044fff60a00ab0 0x0003fff80007fc06 0x0c0007fff0000ff8

def z557 : W := mkw 0x8202bce852275e87 0x41040579d0a44ebd 0x0003fff80007ff86 0x0c0007fff0000fff

def z558 : W := mkw 0x0227221000000000 0x00044e4420000000 0x067f223831f8006b 0xd60cfe447063f000

def z559 : W := mkw 0x002143400282a301 0x8000428680050546 0x0183c3c00e07e39f 0x3e030787801c0fc7

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000060007e038 0x080000000c000fc0

def z561 : W := mkw 0xdc980cede67616dd 0x43b93019dbccec2d 0x9f9c3ff9fe7e1fdf 0xbb3f387ff3fcfc3f

def z562 : W := mkw 0x2161430000000000 0x0042c28600000000 0x61e3c3c60007e03f 0x7cc3c7878c000fc0

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x000300000001802a 0x5c00060000000300

def z564 : W := mkw 0x54000007ad500078 0x02a800000f5aa000 0xfe000007fff80078 0xf3fc00000ffff000

def z565 : W := mkw 0x7dd800028d500038 0x02fbb000051aa000 0x7ffc00000ff80001 0xf2fff800001ff000

def z566 : W := mkw 0x5c980005a4500058 0x02b930000b48a000 0x9e7c0001f1f80069 0xd33cf80003e3f000

def z567 : W := mkw 0x889008e886620691 0x41112011d10cc40d 0x999003f9ce6003d9 0xb3332007f39cc007

def z568 : W := mkw 0x5e92b8a000000000 0x00bd257140000000 0x7f93fff800000007 0xf4ff27fff0000000

def z569 : W := mkw 0x0004001800280480 0x2000080030005009 0x001c003800780000 0x000038007000f000

def z570 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xf9e00007cf800039 0x73f3c0000f9f0000

def z571 : W := mkw 0x5400940570055846 0x00a801280ae00ab0 0xf800dc07f007fc7c 0x29f001b80fe00ff8

def z572 : W := mkw 0x7fdab007bd51487a 0x02ffb5600f7aa290 0xffffc007fff9e079 0xf7ffff800ffff3c0

def z573 : W := mkw 0x089008a000000000 0x0011201140000000 0x19801dc000000004 0x2033003b80000000

def z574 : W := mkw 0x0227221800a88580 0x20044e443001510b 0x067f223801f80383 0xd60cfe447003f007

def z575 : W := mkw 0x5627b21d30a9cdc2 0x20ac4f643a61539b 0x667fe23e31f9ffeb 0xdeccffc47c63f3ff

def z576 : W := mkw 0x5ebfbab810a98d82 0x24bd7f757021531b 0x1e7f3e3831f99feb 0xde3cfe7c7063f33f

def z577 : W := mkw 0x0202200810210c82 0x0004044010204219 0x0613223830619feb 0xde0c26447060c33f

def z578 : W := mkw 0x214041420b022221 0x8042808284160444 0x61e0c1c60f86603d 0x72c3c1838c1f0cc0

def z579 : W := mkw 0x0227fbb810a98d82 0x24044ff77021531b 0x0003fff800019f86 0x0c0007fff000033f

def z580 : W := mkw 0x7548000729100068 0x02ea90000e522000 0x67ec00063f980039 0x72cfd8000c7f3000

def z581 : W := mkw 0x0206201000000000 0x00040c4020000000 0x061c203800000000 0x800c384070000000

def z582 : W := mkw 0x0227221fbdf98dfa 0x22044e443f7bf31b 0x867f223ffff99ffb 0xdf0cfe447ffff33f

def z583 : W := mkw 0xdc980cade47414dc 0x43b930195bc8e829 0x9e1c3c39f0781c40 0x813c387873e0f038

def z584 : W := mkw 0x7dd8000209000020 0x00fbb00004120000 0x7ffc00060f800039 0xf2fff8000c1f0000

def z585 : W := mkw 0x0227225812ab8f83 0x20044e44b025571f 0x07ff23f83fff9fff 0xfe0ffe47f07fff3f

def z586 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x0013223800619fcb 0x9e0026447000c33f

def z587 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x061f223830799fc2 0x8c0c3e447060f33f

def z588 : W := mkw 0x0000040040041004 0x0000000800800820 0x98001c01c0060014 0x2130003803800c00

def z589 : W := mkw 0x0021024002828301 0x0000420480050506 0x01e303c00f8783bf 0x7e03c607801f0f07

def z590 : W := mkw 0x0890000884600490 0x001120001108c009 0x99902239ce601fdb 0xbb332044739cc03f

def z591 : W := mkw 0x0206201810290c82 0x20040c4030205219 0x061c223830781fcb 0x9a0c38447060f03f

def z592 : W := mkw 0x0227221800200480 0x00044e4430004009 0x067f223800601fcb 0xde0cfe447000c03f

def z593 : W := mkw 0x0000000810290c82 0x2000000010205219 0x0000000030781c40 0x000000000060f038

def z594 : W := mkw 0x7561d7476b86f365 0x80eac3ae8ed70de6 0xf9e3dfc7cf87e3bf 0x7ff3c7bf8f9f0fc7

def z595 : W := mkw 0x2bff6bb000000000 0x0457fed760000000 0x07ff23f800000003 0xd40ffe47f0000000

def z596 : W := mkw 0x5400900520004040 0x00a801200a400080 0x6000c00600006000 0x00c001800c0000c0

def z597 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7ffcddc000000005 0xf0fff9bb80000000

def z598 : W := mkw 0x5400000520000040 0x00a800000a400000 0x6600000630000020 0x40cc00000c600000

def z599 : W := mkw 0x00000407fd55587e 0x020000080ffaaab0 0x80000007fffffc78 0x0b0000000ffffff8

def z600 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x819003f9ce661fd9 0x0b032007f39ccc3f

def z601 : W := mkw 0x7dd80407ed54107c 0x02fbb0080fdaa820 0xfffc3c07fffe1c7f 0xfbfff8780ffffc38

def z602 : W := mkw 0x216143020980a120 0x8042c28604130142 0x6063c0060187e03e 0x7cc0c7800c030fc0

def z603 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0x6603fc063007fc26 0x4ccc07f80c600ff8

def z604 : W := mkw 0x7540000729000060 0x00ea80000e520000 0xffe00007ff800079 0xf3ffc0000fff0000

def z605 : W := mkw 0x000004477b87fb67 0x800000088ef70ff6 0x80000007ff87fff8 0x0b0000000fff0fff

def z606 : W := mkw 0x560eb01000000000 0x04ac1d6020000000 0x060c000000000000 0x000c180000000000

def z607 : W := mkw 0x5400940560045044 0x00a801280ac008a0 0xf803dc07c007e03e 0x7df007b80f800fc0

def z608 : W := mkw 0xa9d04deacf6636b5 0xc153a09bd59ecc6d 0xf990ffffce667fdf 0xbbf321ffff9cccff

def z609 : W := mkw 0xa9f14feacfe6b7b5 0xc153e29fd59fcd6f 0x99f03ff9cfe61fdf 0xbb33e07ff39fcc3f

def z610 : W := mkw 0x0202200010010802 0x0004044000200210 0x0600200030001c40 0x800c004000600038

def z611 : W := mkw 0x0227635812abaf83 0xa0044ec6b025575f 0x0003e3f80007ff86 0x0c0007c7f0000fff

def z612 : W := mkw 0xfffffffacfe6b7b5 0xc5fffffff59fcd6f 0xffffffffcfe7ffff 0xffffffffff9fcfff

def z613 : W := mkw 0x776ff3520b82a321 0x84eedfe6a4170546 0x67efc3c60f87e3bf 0x7ecfdf878c1f0fc7

def z614 : W := mkw 0x002143400282a301 0x8000428680050546 0x0063c3c00187e3af 0x5e00c78780030fc7

def z615 : W := mkw 0x29d800028d500038 0x0253b000051aa000 0x61fc00060ff80039 0x72c3f8000c1ff000

def z616 : W := mkw 0x2bff221a9df98dba 0x2257fe44353bf31b 0x07ff22383ff99feb 0xde0ffe44707ff33f

def z617 : W := mkw 0x0202200810a98d82 0x200404401021531b 0x0603200031f99fea 0xde0c06400063f33f

def z618 : W := mkw 0x88900ce0c6461215 0x41112019c18c8c24 0x99901dc1ce66005d 0xb333203b839ccc00

def z619 : W := mkw 0x5623f7457287fb47 0x80ac47ee8ae50ff6 0xfe03ffc7f007fffe 0xfdfc07ff8fe00fff

def z620 : W := mkw 0x7df94307add0a178 0x82fbf2860f5ba142 0xffffc007fff9e079 0xf7ffff800ffff3c0

def z621 : W := mkw 0xfdd8dde0c6461215 0x45fbb1bbc18c8c24 0xf980ddc1ce060014 0x21f301bb839c0c00

def z622 : W := mkw 0x0206201810290c82 0x20040c4030205219 0x0000203800001c00 0x0000004070000038

def z623 : W := mkw 0x776ff3120980a120 0x84eedfe624130142 0x666fc0060181e020 0x44ccdf800c0303c0

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x018000000e000019 0x32030000001c0000

def z625 : W := mkw 0xde9ebcf8c6661695 0x45bd3d79f18ccc2d 0x9f9c3ff9ce661fdf 0xbb3f387ff39ccc3f

def z626 : W := mkw 0x5627b61d70adddc6 0x20ac4f6c3ae15bbb 0xfe03fe3ff007fffe 0xfdfc07fc7fe00fff

def z627 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99801dc1ce661fdc 0x2b33003b839ccc3f

def z628 : W := mkw 0x7dd8000fad7004f8 0x02fbb0001f5ae009 0xfffc223ffff81ffb 0xfbfff8447ffff03f

def z629 : W := mkw 0x8a92bce8d6675e97 0x41152579d1accebd 0x9993fff9ce67ffdf 0xbf3327fff39ccfff

def z630 : W := mkw 0x7dd8000fbdf98dfa 0x22fbb0001f7bf31b 0xfffc0007fff99ff9 0xfbfff8000ffff33f

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000006001e 0x3800000000000c00

def z632 : W := mkw 0x002143420b82a321 0x8000428684170546 0x0003c3c60f87e3be 0x0e0007878c1f0fc7

def z633 : W := mkw 0x7df94347afd2a379 0x82fbf2868f5fa546 0xfffc03c7fff803f9 0xf3fff8078ffff007

def z634 : W := mkw 0x88b10ee8c6e69795 0x4111621dd18dcd2f 0x99f33ff9cfe79fff 0xff33e67ff39fcf3f

def z635 : W := mkw 0x0890000084400010 0x0011200001088000 0x99800001ce000010 0x21330000039c0000

def z636 : W := mkw 0x002143000080a100 0x8000428600010142 0x0003c0000001e000 0x04000780000003c0

def z637 : W := mkw 0x29d800028d500038 0x0253b000051aa000 0x07fc00003ff80069 0xd20ff800007ff000

def z638 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfe7c0007f1f80060 0xc1fcf8000fe3f000

def z639 : W := mkw 0xffffffb8c4641494 0x45ffffff7188c829 0xfffffff9c0601c47 0xf5fffffff380c038

def z640 : W := mkw 0x776f221f39b98dea 0x22eede443e73731b 0x667f223e31f99feb 0xdeccfe447c63f33f

def z641 : W := mkw 0x7fdeb8b000000000 0x04ffbd7160000000 0x7ffc3c3800000001 0xf0fff87870000000

def z642 : W := mkw 0xde9ebcb8c4641494 0x45bd3d797188c829 0x9e1c3c39c0601c40 0x813c38787380c038

def z643 : W := mkw 0x7fffffb570055846 0x04ffffff6ae00ab0 0xfffffff9f0001c47 0xf5fffffff3e00038

def z644 : W := mkw 0x0021020000808100 0x0000420400010102 0x067f020031f983eb 0xde0cfe040063f307

def z645 : W := mkw 0x2140410000000000 0x0042808200000000 0x6180c1c000000004 0x20c3018380000000

def z646 : W := mkw 0x7dd8000000000000 0x00fbb00000000000 0x7ffc000031f80069 0xf2fff8000063f000

def z647 : W := mkw 0x0000000fbdf98dfa 0x220000001f7bf31b 0x80000007fff99ff8 0x0b0000000ffff33f

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003c0000007e006 0x0c00078000000fc0

def z649 : W := mkw 0x8ab72eb8d4ed9d96 0x61156e5d71a9db3b 0x9e7f3e39f1f99feb 0xdf3cfe7c73e3f33f

def z650 : W := mkw 0x216147424b86b325 0x8042c28e84970d66 0xf9e3ffc7cf87ffff 0xfff3c7ff8f9f0fff

def z651 : W := mkw 0x7df9dba000000000 0x04fbf3b740000000 0x79e3dfc000000007 0x74f3c7bf80000000

def z652 : W := mkw 0x5627b21000000000 0x00ac4f6420000000 0x7e7ffe3800000007 0xf4fcfffc70000000

def z653 : W := mkw 0x88b50ef8c6ee9795 0x61116a1df18ddd2f 0x99fc3ff9cffe1fdf 0xbb33f87ff39ffc3f

def z654 : W := mkw 0x0025021800a88580 0x20004a043001510b 0x007f023801f983ab 0x5e00fe047003f307

def z655 : W := mkw 0x7fdab407fd55587e 0x02ffb5680ffaaab0 0xfffc3c07fff81c79 0xf3fff8780ffff038

def z656 : W := mkw 0x2148000209100028 0x0242900004122000 0x006c000001980000 0x0000d80000033000

def z657 : W := mkw 0x0025021800a88580 0x20004a043001510b 0x007c223801f81fcb 0x9a00f8447003f03f

def z658 : W := mkw 0x5606b41d702d5cc6 0x20ac0d683ae05ab9 0x9e1c3c39f0781c40 0x813c387873e0f038

def z659 : W := mkw 0x00000007ad500078 0x020000000f5aa000 0x80000007ce000010 0x010000000f9c0000

def z660 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xff9c0007fe780050 0xa1ff38000ffcf000

def z661 : W := mkw 0xa9f14fe8c6661695 0x4153e29fd18ccc2d 0xf9f3fff9ce661fdf 0xfff3e7fff39ccc3f

def z662 : W := mkw 0x7767f75f7bafffe7 0xa0eecfeebef75fff 0xffffffffffffffff 0xffffffffffffffff

def z663 : W := mkw 0x7548000729100068 0x02ea90000e522000 0x667c000631f80069 0xd2ccf8000c63f000

def z664 : W := mkw 0x0227221000808100 0x00044e4420010102 0x067f2238018183ab 0xde0cfe4470030307

def z665 : W := mkw 0x7dd8dda560045044 0x04fbb1bb4ac008a0 0xf980ddc7c0066014 0x21f301bb8f800cc0

def z666 : W := mkw 0x0021020000808100 0x0000420400010102 0x0063000001818020 0x4400c60000030300

def z667 : W := mkw 0x7ffffbb810290c82 0x24fffff770205219 0x7ffffff830781c47 0xf4fffffff060f038

def z668 : W := mkw 0x0000000010898902 0x2000000000211312 0x0000000031998020 0x0000000000633300

def z669 : W := mkw 0x0227b61850addd86 0x20044f6c30a15bbb 0x067ffe3831ffffef 0xde0cfffc7063ffff

def z670 : W := mkw 0xfffffff842261685 0x45fffffff0844c2d 0x7ffffff800061f87 0xfcfffffff0000c3f

def z671 : W := mkw 0x8ab72ef8d6ef9f97 0x61156e5df1addf3f 0x99933ff9ce679fdf 0xbf33267ff39ccf3f

def z672 : W := mkw 0x5627b61d70adddc6 0x20ac4f6c3ae15bbb 0x9e7f3e39f1f99feb 0xdf3cfe7c73e3f33f

def z673 : W := mkw 0x089008e002020201 0x00112011c0040404 0x19903ff80e06039f 0xba33207ff01c0c07

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x0060000001800029 0x5200c00000030000

def z675 : W := mkw 0x21400007ad500078 0x024280000f5aa000 0xe1e00007fff80079 0x73c3c0000ffff000

def z676 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x6063c3c60187e3a6 0x4cc0c7878c030fc7

def z677 : W := mkw 0xa9d04de2cf463235 0xc153a09bc59e8c64 0xf980ddc7ce066014 0x21f301bb8f9c0cc0

def z678 : W := mkw 0x000000028d500038 0x02000000051aa000 0x000000000ff80000 0x02000000001ff000

def z679 : W := mkw 0xa9f14bea8fe2a7b1 0xc153e297d51fc54f 0x61f3c3fe0fe7e3bf 0x7ec3e787fc1fcfc7

def z680 : W := mkw 0x7df943420b82a321 0x80fbf28684170546 0x7fffc3c60f87e3bf 0xfeffff878c1f0fc7

def z681 : W := mkw 0x0202b40570055846 0x000405680ae00ab0 0x8003fc07f007fc7e 0x0d0007f80fe00ff8

def z682 : W := mkw 0x5e9ab405f455585e 0x02bd35680be8aab0 0xfe1ffc07f07ffc7e 0xfdfc3ff80fe0fff8

def z683 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xff800007fe000078 0xf1ff00000ffc0000

def z684 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xf9900007ce600059 0xb3f320000f9cc000

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x98000001c0000058 0xb130000003800000

def z686 : W := mkw 0x0000004a1babafa3 0xa00000009437575f 0x000000063ffffff8 0x0a0000000c7fffff

def z687 : W := mkw 0x7fda2007bd51087a 0x02ffb4400f7aa210 0xffff2007fff99c7b 0xfffffe400ffff338

def z688 : W := mkw 0x0021020810a98d82 0x200042041021531b 0x0063020031f99feb 0x5e00c6040063f33f

def z689 : W := mkw 0x5627b21810a98d82 0x20ac4f643021531b 0x7e7ffe3831f99fef 0xfefcfffc7063f33f

def z690 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x67ffc3f800000001 0x44cfff87f0000000

def z691 : W := mkw 0x7fffffb560045044 0x04ffffff6ac008a0 0xffffffffc0066017 0xf5ffffffff800cc0

def z692 : W := mkw 0x5602b00010010802 0x00ac056000200210 0x7e03fc0030019c6e 0xfcfc07f800600338

def z693 : W := mkw 0x2161434a0ba2a7a1 0x8042c2869417454f 0x61f3e3fe0fe7ffff 0xfec3e7c7fc1fcfff

def z694 : W := mkw 0x0025021800a88580 0x20004a043001510b 0x0000023800000380 0x0000000470000007

def z695 : W := mkw 0x7df9dbe20b82a321 0x84fbf3b7c4170546 0x79e3dfc60f87e3bf 0x7ef3c7bf8c1f0fc7

def z696 : W := mkw 0x0000000010010802 0x0000000000200210 0x0000000030019c68 0x0800000000600338

def z697 : W := mkw 0x0000000209000020 0x0000000004120000 0x000000060f800038 0x020000000c1f0000

def z698 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c00f800387 0x76c3c787801f0007

def z699 : W := mkw 0x0223220010818902 0x0004464400210312 0x0663220031819feb 0xde0cc6440063033f

def z700 : W := mkw 0x0000000530014842 0x000000000a600290 0x000000063001e020 0x000000000c6003c0

def z701 : W := mkw 0x7fde201fbd790cfa 0x22ffbc403f7af219 0xfffc203ffff81c79 0xf3fff8407ffff038

def z702 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x61ffc3f800000007 0x74c3ff87f0000000

def z703 : W := mkw 0x0021020000000000 0x0000420400000000 0x0063020000000003 0x5400c60400000000

def z704 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e003c60f8003b9 0x72c3c0078c1f0007

def z705 : W := mkw 0xdeb7befdf6efdfd7 0x61bd6f7dfbeddfbf 0xffffffffffffffff 0xffffffffffffffff

def z706 : W := mkw 0x7fdab007ad500078 0x02ffb5600f5aa000 0xfffffc07fff8007f 0xf7fffff80ffff000

def z707 : W := mkw 0x7fdef9b000000000 0x04ffbdf360000000 0x7f9ffdf800000006 0xf4ff3ffbf0000000

def z708 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x19fc1ff800000005 0x2033f83ff0000000

def z709 : W := mkw 0x5cb94345a6d2a359 0x82b972868b4da546 0x9e1fc3c1f07fe3c6 0x8d3c3f8783e0ffc7

def z710 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61ffc3c60fffe3bf 0x7ec3ff878c1fffc7

def z711 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x067ffff831f8006f 0xd60cfffff063f000

def z712 : W := mkw 0xa140044acf6616b5 0x41428008959ecc2d 0xe1e00007cfe61ff9 0x7bc3c0000f9fcc3f

def z713 : W := mkw 0x7ffffbb010898902 0x24fffff760211312 0x7ffffff831f9806f 0xf6fffffff063f300

def z714 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0207fff803fb 0xfbfff8040ffff007

def z715 : W := mkw 0x5400940570055846 0x00a801280ae00ab0 0xf803dc07f007fc7e 0x7df007b80fe00ff8

def z716 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80100001ce661fd9 0x9b002000039ccc3f

def z717 : W := mkw 0x776ffbb000000000 0x04eedff760000000 0x67effff800000007 0x74cfdffff0000000

def z718 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c1c60f87e3bc 0x6ec3c7838c1f0fc7

def z719 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x00003ff800000000 0x0000007ff0000000

def z720 : W := mkw 0xa9f14faacde4b5b4 0xc153e29f559bc96b 0xf873fc3fc1e1fc60 0xc5f0e7f87f83c3f8

def z721 : W := mkw 0x2346615a1b2b2ea3 0xa0468cc2b436565d 0x679ce1fe3e7e7c54 0xa0cf39c3fc7cfcf8

def z722 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffffe00066017 0xf4fffffffc000cc0

def z723 : W := mkw 0x54000007ad500078 0x02a800000f5aa000 0xfe7c0007fff80079 0xf3fcf8000ffff000

def z724 : W := mkw 0x02272ab000000000 0x00044e5560000000 0x00033ff800000006 0x0400067ff0000000

def z725 : W := mkw 0x0227fbb7ad500078 0x06044ff76f5aa000 0x8003fffffff8007e 0x070007fffffff000

def z726 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xff83ffc7f007fc7f 0xfdff07ff8fe00ff8

def z727 : W := mkw 0x8227265852af9f87 0x61044e4cb0a55f3f 0x0003223800079f82 0x0c00064470000f3f

def z728 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x79fffff800000007 0xf4f3fffff0000000

def z729 : W := mkw 0xa9fd4bfa8fe2a7b1 0xc553fa97f51fc54f 0x01fc03f80fe00381 0x0203f807f01fc007

def z730 : W := mkw 0x7fff221fbdf98dfa 0x22fffe443f7bf31b 0xf983223fce019f92 0x2df306447f9c033f

def z731 : W := mkw 0x8ab72ef0d6cf9b17 0x61156e5de1ad9f36 0x9fef1dc1ff9f8034 0x653fde3b83ff3f00

def z732 : W := mkw 0x7dd8d9a7ad500078 0x06fbb1b34f5aa000 0xfffcfffffff8007f 0xf3fff9fffffff000

def z733 : W := mkw 0x214000420b020221 0x0042800084160404 0x61e3c3c60f87e3bf 0x7ec3c7878c1f0fc7

def z734 : W := mkw 0x776ff3173999896a 0x26eedfe62e733312 0x666fc00631998020 0x44ccdf800c633300

def z735 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfe7c0007fff80078 0xc3fcf8000ffff000

def z736 : W := mkw 0x7ffffbb7bd51087a 0x06fffff76f7aa210 0xfffffffffff99c7f 0xfffffffffffff338

def z737 : W := mkw 0xdc98044de67616dd 0x43b930089bccec2d 0x9e1c0001fe7e1fd8 0x8b3c380003fcfc3f

def z738 : W := mkw 0x216143420b82a321 0x8042c28684170546 0xf9e3c3c7cf87e3ff 0xfff3c7878f9f0fc7

def z739 : W := mkw 0x2bdab402dd55583e 0x0257b56805baaab0 0x01fffc000ffffc07 0x0e03fff8001ffff8

def z740 : W := mkw 0x8227fff852af9f87 0x65044ffff0a55f3f 0x0003fff800079f86 0x0c0007fff0000f3f

def z741 : W := mkw 0xfdd8044feff6b7fd 0xc3fbb0089fdfed6f 0xfffc0007fffffff9 0xfbfff8000fffffff

def z742 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001ce661fde 0x3b000000039ccc3f

def z743 : W := mkw 0x5ebffbb000000000 0x04bd7ff760000000 0x7e1ffff800000006 0xf4fc3ffff0000000

def z744 : W := mkw 0xde9ebcbdf4655cd6 0x45bd3d797be8cab9 0x9e1c3c39f0601c40 0x813c387873e0c038

def z745 : W := mkw 0x00000007ad500078 0x020000000f5aa000 0x866c0007fff80078 0x430cd8000ffff000

def z746 : W := mkw 0x7ffffbb729100068 0x06fffff76e522000 0xfffffffff198007f 0xf5ffffffffe33000

def z747 : W := mkw 0x7fdef9b7ad500078 0x06ffbdf36f5aa000 0xfffcfdfffff8007d 0xf3fff9fbfffff000

def z748 : W := mkw 0x8000044adfefbfb7 0xe100000895bfdf7f 0x80000007fffffff8 0x0b0000000fffffff

def z749 : W := mkw 0x7df9dba000000000 0x04fbf3b740000000 0x79f3fff800000007 0xf4f3e7fff0000000

def z750 : W := mkw 0x0227b21810a98d82 0x20044f643021531b 0x067ffe3831f99fef 0xde0cfffc7063f33f

def z751 : W := mkw 0xf76ff758c6661695 0x45eedfeeb18ccc2d 0xe66fc001ce661fd8 0x4fccdf80039ccc3f

def z752 : W := mkw 0x21400007ad500078 0x024280000f5aa000 0xe7fc0007fff80079 0xf3cff8000ffff000

def z753 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x9ffc3ff9ce661fdf 0xfb3ff87ff39ccc3f

def z754 : W := mkw 0x776ff3173981e962 0x84eedfe62e7303d2 0x666fc0063181e020 0x44ccdf800c6303c0

def z755 : W := mkw 0x7ffffbb20980a120 0x84fffff764130142 0x7ffffff801800007 0xf4fffffff0030000

def z756 : W := mkw 0x0227221800200480 0x00044e4430004009 0x067f223831f81feb 0xde0cfe447063f03f

def z757 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0xf990ffffce667fdf 0xbbf321ffff9cccff

def z758 : W := mkw 0x29fd4fb570055846 0x0453fa9f6ae00ab0 0x81fc03fff007fc79 0x0903f807ffe00ff8

def z759 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f87e397 0x2ec3c7878c1f0fc7

def z760 : W := mkw 0x7ffffbb72990a168 0x86fffff76e532142 0x7ffffffe3199e027 0xf4fffffffc6333c0

def z761 : W := mkw 0x7ffffbb5a4500058 0x06fffff76b48a000 0xfffffff9fe78005f 0xf7fffffff3fcf000

def z762 : W := mkw 0x0025021810a98d82 0x20004a043021531b 0x067c023831f99fe9 0xda0cf8047063f33f

def z763 : W := mkw 0x7ffffbb209100028 0x06fffff764122000 0x7ffffff801980007 0xf4fffffff0033000

def z764 : W := mkw 0x7ffffbb000808100 0x04fffff760010102 0x7ffffff801818027 0xf4fffffff0030300

def z765 : W := mkw 0x8000044fffe7fff7 0xc10000089fffcfff 0x80000007ffe7fff8 0x0b0000000fffcfff

def z766 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80e00001f 0xf6fffffff01c0000

def z767 : W := mkw 0x0202200810210c82 0x0004044010204219 0x067f223831f99feb 0xde0cfe447063f33f

def z768 : W := mkw 0x29d808a28d500038 0x0253b011451aa000 0x19fc3ff80ff80007 0xb233f87ff01ff000

def z769 : W := mkw 0x5425961d60acd5c4 0x20a84b2c3ac159ab 0xf87cde3fc1fe6395 0x23f0f9bc7f83fcc7

def z770 : W := mkw 0x089008a000000000 0x0011201140000000 0x7993fffe0007e03f 0xfcf327fffc000fc0

def z771 : W := mkw 0x5e9eb8f20b82a321 0x84bd3d71e4170546 0x1e1c3c3e0f87e3b8 0x8a3c38787c1f0fc7

def z772 : W := mkw 0x29d808a000000000 0x0053b01140000000 0x19fc3ff800000007 0xb033f87ff0000000

def z773 : W := mkw 0x82276ff852afbf87 0xe1044edff0a55f7f 0x0003fff80007ff86 0x0c0007fff0000fff

def z774 : W := mkw 0x5606b415700d5846 0x20ac0d682ae01ab0 0xfe0ffc07f01ffc7e 0xfdfc1ff80fe03ff8

def z775 : W := mkw 0x562ffbb000000000 0x04ac5ff760000000 0x060ffff800000006 0x040c1ffff0000000

def z776 : W := mkw 0x8000044fff775eff 0x430000089ffeeebd 0x80000007fffffff8 0x0b0000000fffffff

def z777 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xffff0007fff9807b 0xfffffe000ffff300

def z778 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99fc3ff9cffe1fdf 0xbb33f87ff39ffc3f

def z779 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000007ce67fff8 0x0b0000000f9ccfff

def z780 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe63fc07f187fc7f 0xfffcc7f80fe30ff8

def z781 : W := mkw 0x80210648c6e69795 0x4100420c918dcd2f 0x80630201cfe79ffb 0x5f00c604039fcf3f

def z782 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xffffffffff980037 0xf5ffffffffff3000

def z783 : W := mkw 0x8000044852af9f87 0x6100000890a55f3f 0x0000000000079f80 0x0800000000000f3f

def z784 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0x9ffc0007fff80079 0x833ff8000ffff000

def z785 : W := mkw 0x2bfffbb000000000 0x0457fff760000000 0x61fffff800000007 0x74c3fffff0000000

def z786 : W := mkw 0x0ab72ab010898902 0x20156e5560211312 0x1fff3ff831998027 0xf43ffe7ff0633300

def z787 : W := mkw 0x0a9228a000000000 0x0015245140000000 0x1f933ff800000007 0xf43f267ff0000000

def z788 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe6ffc07f19ffc7e 0xfdfcdff80fe33ff8

def z789 : W := mkw 0x5e92b8a000000000 0x00bd257140000000 0x1f903ff800000007 0xb03f207ff0000000

def z790 : W := mkw 0x7ffffbb520000040 0x04fffff76a400000 0xfffffffff007e07f 0xfdffffffffe00fc0

def z791 : W := mkw 0x7ffffbb209002020 0x84fffff764120040 0x7ffffffe00006007 0xf4fffffffc0000c0

def z792 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce661f97 0x2b33207ff39ccc3f

def z793 : W := mkw 0x29d849a000000000 0x0453b09340000000 0x19903ff800000007 0xb033207ff0000000

def z794 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe13fe3ff007fc7f 0xfdfc27fc7fe00ff8

def z795 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3e3c60f87ffff 0xfec3c7c78c1f0fff

def z796 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61f3e3fe0f87e3bf 0xfec3e7c7fc1f0fc7

def z797 : W := mkw 0x000000420b82a321 0x8000000084170546 0x6183c3c60f87e3bf 0x7ec307878c1f0fc7

def z798 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x1803fff800000006 0xb43007fff0000000

def z799 : W := mkw 0x7dfddbb000000000 0x04fbfbb760000000 0x19fc1ff800000001 0x0033f83ff0000000

def z800 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xffec0007fff80078 0x63ffd8000ffff000

def z801 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0xf9903fffce661fff 0xfbf3207fff9ccc3f

def z802 : W := mkw 0x0206201810290c82 0x20040c4030205219 0x067c223831f81feb 0xda0cf8447063f03f

def z803 : W := mkw 0x7ffffbb28d400030 0x04fffff7651a8000 0xffffffffcfe0007f 0xf7ffffffff9fc000

def z804 : W := mkw 0x5e9eb8b5a4500058 0x06bd3d716b48a000 0x9f9c3ff9fe78005f 0xb33f387ff3fcf000

def z805 : W := mkw 0x7fdeb8b000000000 0x04ffbd7160000000 0x7ffc3ff800000007 0xf0fff87ff0000000

def z806 : W := mkw 0x000008a000000000 0x0000001140000000 0x01803ff800000007 0x3003007ff0000000

def z807 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xe7fc0007fff80079 0x43cff8000ffff000

def z808 : W := mkw 0x5ebffbb000000000 0x04bd7ff760000000 0x1e7ffff800000007 0xd43cfffff0000000

def z809 : W := mkw 0xde92b8edb6634ed3 0x41bd2571db6cc69d 0x6793c3fe3e61e3a1 0x46cf2787fc7cc3c7

def z810 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80000038f 0xfefffffff0000007

def z811 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80007e007 0xfcfffffff0000fc0

def z812 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xfffffff9fff80047 0xf7fffffff3fff000

def z813 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc3c07fff8007f 0xf3fff8780ffff000

def z814 : W := mkw 0x0000000810a98d82 0x200000001021531b 0x067c223831f99feb 0xda0cf8447063f33f

def z815 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7fffdff800000005 0x64ffffbff0000000

def z816 : W := mkw 0x7dd8d9a810a98d82 0x24fbb1b35021531b 0x7980ddc031f99fec 0x2af301bb8063f33f

def z817 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0xf993fff9ce661fdf 0xfff327fff39ccc3f

def z818 : W := mkw 0x7fdab8a000000000 0x00ffb57140000000 0x7ffffff800000007 0xf4fffffff0000000

def z819 : W := mkw 0x089008a084400010 0x0011201141088000 0x19903ff80e600007 0xb233207ff01cc000

def z820 : W := mkw 0x7dd808a729100068 0x02fbb0114e522000 0x7ffc3ffe31980027 0xf0fff87ffc633000

def z821 : W := mkw 0x0000044842261685 0x0000000890844c2d 0x99903ff9ce661fdf 0xbb33207ff39ccc3f

def z822 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x1ffffff800000007 0x843ffffff0000000

def z823 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff80e00001f 0xb233207ff01c0000

def z824 : W := mkw 0x02272ab000000000 0x00044e5560000000 0x067f3ff800000007 0xd40cfe7ff0000000

def z825 : W := mkw 0x8000044852af9f87 0x6100000890a55f3f 0x0000000031ff9fe8 0x0a0000000063ff3f

def z826 : W := mkw 0x21614ba000000000 0x0042c29740000000 0x61e3fff800000007 0x74c3c7fff0000000

def z827 : W := mkw 0x5ebffbb5a4500058 0x06bd7ff76b48a000 0x9e1ffff9f0780046 0x853c3ffff3e0f000

def z828 : W := mkw 0x2bfffbb28d500038 0x0657fff7651aa000 0x01fffff80ff80007 0x0603fffff01ff000

def z829 : W := mkw 0x0000000084400010 0x0000000001088000 0x867c0001fff80079 0xd30cf80003fff000

def z830 : W := mkw 0x0000044f7bafffe7 0xa00000089ef75fff 0x80000007fffffff8 0x0b0000000fffffff

def z831 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xff83fc07fe07fc7f 0xffff07f80ffc0ff8

def z832 : W := mkw 0x5400000520000040 0x00a800000a400000 0xfe003c07f000007e 0xf1fc00780fe00000

def z833 : W := mkw 0x7ffffbb729100068 0x06fffff76e522000 0x7ffffffe00000007 0xf4fffffffc000000

def z834 : W := mkw 0x29f14ba20980a120 0x8053e29744130142 0x79f3fffe0181e027 0xf4f3e7fffc0303c0

def z835 : W := mkw 0x5606b41570055846 0x00ac0d682ae00ab0 0xfe1ffc3ff007fc7e 0xfdfc3ff87fe00ff8

def z836 : W := mkw 0x8000044de66656d5 0x410000089bccccad 0x80000007ce667fd8 0x0b0000000f9cccff

def z837 : W := mkw 0x2bf7fbb000000000 0x0457eff760000000 0x79f3fff800000007 0xf4f3e7fff0000000

def z838 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f007fc78 0xcdfc07f80fe00ff8

def z839 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc03c7fff8007f 0xf3fff8078ffff000

def z840 : W := mkw 0x2140000209000020 0x0042800004120000 0x61e003c60f80003f 0x72c3c0078c1f0000

def z841 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x0063fff800000007 0x5400c7fff0000000

def z842 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xf803fc07f007fc7e 0x2df007f80fe00ff8

def z843 : W := mkw 0x7fff2ab7ad500078 0x02fffe556f5aa000 0xffff3ffffff8007f 0xf7fffe7ffffff000

def z844 : W := mkw 0x0227631810a9ad82 0xa0044ec63021535b 0x067fe23831f9ffeb 0xde0cffc47063f3ff

def z845 : W := mkw 0x0227631810a98d82 0x20044ec63021531b 0x067fe3f831f99fef 0xde0cffc7f063f33f

def z846 : W := mkw 0xf5480cef6b3616ed 0x43ea9019ded66c2d 0x666c3ffe319e1fa6 0x48ccd87ffc633c3f

def z847 : W := mkw 0x08b14ba000000000 0x0011629740000000 0x1993fff800000007 0xb43327fff0000000

def z848 : W := mkw 0x0227fbb010014802 0x04044ff760200290 0x0003fff80001e006 0x040007fff00003c0

def z849 : W := mkw 0x5eb7bab000000000 0x00bd6f7560000000 0x7ffffff800000007 0xf4fffffff0000000

def z850 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x867c0001fffe1ff9 0xdb0cf80003fffc3f

def z851 : W := mkw 0x5ebffbb000000000 0x04bd7ff760000000 0x1f9ffff800000007 0xb43f3ffff0000000

def z852 : W := mkw 0x7dd808a7ad500078 0x02fbb0114f5aa000 0xfffc1dc7fff8007d 0xf3fff83b8ffff000

def z853 : W := mkw 0x7dd898a7ad500078 0x06fbb1314f5aa000 0xfffc1c07fff80079 0xf3fff8380ffff000

def z854 : W := mkw 0x80000448d6671e97 0x4100000891acce3d 0x80000001fe679ff8 0x0b00000003fccf3f

def z855 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce061f97 0xb933207ff39c0c3f

def z856 : W := mkw 0x0227b21810a9cd82 0x20044f643021539b 0x067fe23831f9ffeb 0xde0cffc47063f3ff

def z857 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xfffffffffe780057 0xf5fffffffffcf000

def z858 : W := mkw 0x7ffffbb729000060 0x04fffff76e520000 0xffffffffff80007f 0xf7ffffffffff0000

def z859 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001ce661c50 0x01000000039ccc38

def z860 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xffffffffcff80017 0xf7ffffffff9ff000

def z861 : W := mkw 0x7ffffbb53089c942 0x24fffff76a611392 0x7ffffffe3199e027 0xf4fffffffc6333c0

def z862 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x98000001ce661fd8 0xbb300000039ccc3f

def z863 : W := mkw 0xfdd8dde7ef56127d 0x47fbb1bbcfdeac24 0xf980ddc7ce060014 0x21f301bb8f9c0c00

def z864 : W := mkw 0x7ffffbb010010802 0x04fffff760200210 0x7ffffff830001c47 0xf4fffffff0600038

def z865 : W := mkw 0x0ab72ab000000000 0x00156e5560000000 0x19933ff800000007 0xb433267ff0000000

def z866 : W := mkw 0x5400940560045044 0x00a801280ac008a0 0xf803fc07c007fc7e 0xfdf007f80f800ff8

def z867 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x1f9c3df800000004 0xa03f387bf0000000

def z868 : W := mkw 0x0202240050051806 0x0004044800a00a30 0xfe03fc07f007fc7e 0xfdfc07f80fe00ff8

def z869 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff80006001f 0xb833207ff0000c00

def z870 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007fffe007f 0xfbfff8000ffffc00

def z871 : W := mkw 0x7ffffbb010014802 0x04fffff760200290 0x7ffffff80001e007 0xf4fffffff00003c0

def z872 : W := mkw 0x216543520b8aa321 0xa042ca86a4171546 0x61efc3c60f9fe3bf 0x7ec3df878c1f3fc7

def z873 : W := mkw 0x7ffffbb209000020 0x04fffff764120000 0x7ffffff80f800007 0xf6fffffff01f0000

def z874 : W := mkw 0x2367fbb000000000 0x0446cff760000000 0x6063fff800000006 0x44c0c7fff0000000

def z875 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe7ffc07f007fc7f 0xfdfcfff80fe00ff8

def z876 : W := mkw 0x5c9898a000000000 0x04b9313140000000 0x19903ff800000007 0xb033207ff0000000

def z877 : W := mkw 0x7ffffbb010898902 0x24fffff760211312 0x7ffffff800018007 0xf4fffffff0000300

def z878 : W := mkw 0x7ffffbb530014842 0x04fffff76a600290 0x7ffffffe3007e03f 0xfcfffffffc600fc0

def z879 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7993fff800000007 0xb4f327fff0000000

def z880 : W := mkw 0x0227fbb010898902 0x24044ff760211312 0x0003fff800018006 0x040007fff0000300

def z881 : W := mkw 0x7763f7477b87fb67 0x80eec7ee8ef70ff6 0x9fe03fc1ff801fc1 0x833fc07f83ff003f

def z882 : W := mkw 0x7ffffbb209000020 0x04fffff764120000 0x7ffffffe3ff8007f 0xf6fffffffc7ff000

def z883 : W := mkw 0x2161434002020201 0x0042c28680040404 0x61e3c3c60e07e3bf 0x7ec3c7878c1c0fc7

def z884 : W := mkw 0xfdd84de7ef56327d 0xc3fbb09bcfdeac64 0xf980ddc7ce066014 0x21f301bb8f9c0cc0

def z885 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x1e7f3e3831f99fef 0xfe3cfe7c7063f33f

def z886 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x9f9c3ff9fe7e1fdf 0xbb3f387ff3fcfc3f

def z887 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x667fe23831f99fef 0xfeccffc47063f33f

def z888 : W := mkw 0x089008a000000000 0x0011201140000000 0x7993fff800000007 0xf4f327fff0000000

def z889 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007fff80031 0x63fff8000ffff000

def z890 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xfffffffffe00007f 0xf5fffffffffc0000

def z891 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xf983ffffce000016 0x25f307ffff9c0000

def z892 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x6003fff800000006 0x74c007fff0000000

def z893 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xffffffffcf80003f 0xf7ffffffff9f0000

def z894 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99803ff9ce061fde 0xb933007ff39c0c3f

def z895 : W := mkw 0x8000044acf6616b5 0x41000008959ecc2d 0x80000007cfe61ff8 0x0b0000000f9fcc3f

def z896 : W := mkw 0x0a92b8a000000000 0x0015257140000000 0x1993fff800000007 0xb43327fff0000000

def z897 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60e07e397 0x7cc3c7878c1c0fc7

def z898 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xfffc3ffffff80079 0xf3fff87ffffff000

def z899 : W := mkw 0x2bfffbb000000000 0x0457fff760000000 0x01fc3ff800000001 0x0003f87ff0000000

def z900 : W := mkw 0x7ffffbb7add0a178 0x86fffff76f5ba142 0xfffffffffff9e07f 0xf7fffffffffff3c0

def z901 : W := mkw 0x7ffffbb28d500038 0x06fffff7651aa000 0xfffffff9cff8005f 0xf7fffffff39ff000

def z902 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x9993fff9ce67ffdf 0xbf3327fff39ccfff

def z903 : W := mkw 0x0206201810a98d82 0x20040c403021531b 0x067c203831f99fe9 0xda0cf8407063f33f

def z904 : W := mkw 0xd400044de66616d5 0x41a800089bcccc2d 0xfe000007fe661ff8 0xfbfc00000ffccc3f

def z905 : W := mkw 0x7ffffbb20980a120 0x84fffff764130142 0x7ffffffe0f81e03f 0xf6fffffffc1f03c0

def z906 : W := mkw 0x7ffffbb28d500038 0x06fffff7651aa000 0x7ffffff80e000007 0xf4fffffff01c0000

def z907 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff800000001 0xc4fffffff0000000

def z908 : W := mkw 0xdc90044df6675ed7 0x41b920089beccebd 0xff900007fe67fff9 0xfbff20000ffccfff

def z909 : W := mkw 0x7ffffbb010090802 0x24fffff760201210 0x7ffffff830180007 0xf4fffffff0603000

def z910 : W := mkw 0x0ab7fbb084400010 0x04156ff761088000 0x9993fff9ce60005f 0xb73327fff39cc000

def z911 : W := mkw 0x7dd84107ad500078 0x02fbb0820f5aa000 0xfffcc1c7fff8007d 0xf3fff9838ffff000

def z912 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x81800001ce661fd9 0x3b030000039ccc3f

def z913 : W := mkw 0x7ffffbb5a4500058 0x06fffff76b48a000 0xfffffff9f1f8006f 0xf7fffffff3e3f000

def z914 : W := mkw 0x089008a884600490 0x001120115108c009 0x99903ff9ce601fdf 0xbb33207ff39cc03f

def z915 : W := mkw 0xa161474acfe6b7b5 0xc142c28e959fcd6f 0xe063c007cfe7fff8 0x4fc0c7800f9fcfff

def z916 : W := mkw 0x0a9628b000000000 0x00152c5160000000 0x1f9c3ff800000007 0xb03f387ff0000000

def z917 : W := mkw 0x089c08b000000000 0x0411381160000000 0x199c3ff800000007 0xb033387ff0000000

def z918 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce601fcb 0x9b33207ff39cc03f

def z919 : W := mkw 0x7ffffbb010010802 0x04fffff760200210 0x7ffffff800019c07 0xfcfffffff0000338

def z920 : W := mkw 0x82272658d6ef9f97 0x61044e4cb1addf3f 0x866f0001ffff9ff8 0x4f0cde0003ffff3f

def z921 : W := mkw 0x7ffffbb28d500038 0x06fffff7651aa000 0x7ffffffe0ff8003f 0xf6fffffffc1ff000

def z922 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c63fffe3ff 0x7ec3c7878c7fffc7

def z923 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831f99fc3 0x8e0cfe447063f33f

def z924 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7e7ffff800000006 0xc4fcfffff0000000

def z925 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce661fd9 0x8b33207ff39ccc3f

def z926 : W := mkw 0x5eb7fbb000000000 0x04bd6ff760000000 0x7f93fff800000007 0xf4ff27fff0000000

def z927 : W := mkw 0x7fdef9b000000000 0x04ffbdf360000000 0x7ffcfdf800000005 0xf0fff9fbf0000000

def z928 : W := mkw 0x7ffffbb28d500038 0x06fffff7651aa000 0x7ffffff83ff8006f 0xf6fffffff07ff000

def z929 : W := mkw 0x7767f3173989e962 0xa0eecfe62e7313d2 0x666fc0063199e020 0x44ccdf800c6333c0

def z930 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7feffff800000006 0x64ffdffff0000000

def z931 : W := mkw 0x7dd808a7ad500078 0x02fbb0114f5aa000 0xfffc03fffff80079 0xf3fff807fffff000

def z932 : W := mkw 0x29d049a000000000 0x0053a09340000000 0x7990fff800000007 0xb0f321fff0000000

def z933 : W := mkw 0x8000044d72275ec7 0x410000089ae44ebd 0x80000007f007fff8 0x090000000fe00fff

def z934 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223e31fffffb 0xde0cfe447c63ffff

def z935 : W := mkw 0x7fdef9b000000000 0x04ffbdf360000000 0x7f9cfff800000007 0xb0ff39fff0000000

def z936 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001ce660390 0x03000000039ccc07

def z937 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x6183c3c60e07e39f 0x3ec307878c1c0fc7

def z938 : W := mkw 0x0021020800a08580 0x000042041001410b 0x067f223831f99feb 0xde0cfe447063f33f

def z939 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831f81fc3 0xd60cfe447063f03f

def z940 : W := mkw 0x7ffffbb010010802 0x04fffff760200210 0x7ffffff831f99c6f 0xfefffffff063f338

def z941 : W := mkw 0x0227f31810a98d82 0x24044fe63021531b 0x067fe23831f99feb 0xde0cffc47063f33f

def z942 : W := mkw 0x7fdabca7fd55587e 0x02ffb5794ffaaab0 0xfffffffffffffc7f 0xfffffffffffffff8

def z943 : W := mkw 0x089008a084400010 0x0011201141088000 0x99903ff9ce000017 0xb133207ff39c0000

def z944 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xffffffffce60005f 0xf7ffffffff9cc000

def z945 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0001fff80041 0xf3fff80003fff000

def z946 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0x9ffc0001fff80059 0xb33ff80003fff000

def z947 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x1fff3ff800000003 0xd43ffe7ff0000000

def z948 : W := mkw 0x8000044852275e87 0x4100000890a44ebd 0x000000000007ff80 0x0800000000000fff

def z949 : W := mkw 0x7ffffbb010898902 0x24fffff760211312 0x7ffffff831999c6f 0xfcfffffff0633338

def z950 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000201ce661fdb 0x1b000004039ccc3f

def z951 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x67e3c3c63f87e3ff 0xfecfc7878c7f0fc7

def z952 : W := mkw 0x5602b8a000000000 0x00ac057140000000 0x7e03fff800000006 0xf4fc07fff0000000

def z953 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x0003000000019f80 0x0c0006000000033f

def z954 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff800000001 0x8033207ff0000000

def z955 : W := mkw 0x08900007ad500078 0x021120000f5aa000 0x9ffc0007fff80079 0xf33ff8000ffff000

def z956 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7990fdf800000004 0xa0f321fbf0000000

def z957 : W := mkw 0x7dd89007ad504078 0x02fbb1200f5aa080 0xfffcc007fff86079 0xf3fff9800ffff0c0

def z958 : W := mkw 0x08b10aa000808100 0x0011621540010102 0x19f33ff8018183af 0xfe33e67ff0030307

def z959 : W := mkw 0x7ff3fba000000000 0x00ffe7f740000000 0x7ff3fff800000007 0xf4ffe7fff0000000

def z960 : W := mkw 0x7ffffbb084400010 0x04fffff761088000 0xfffffff9c0600047 0xf5fffffff380c000

def z961 : W := mkw 0x7ffffbb729100068 0x06fffff76e522000 0x7ffffffe3f98003f 0xf6fffffffc7f3000

def z962 : W := mkw 0x2bfffbb000000000 0x0457fff760000000 0x19fffff800000007 0xb433fffff0000000

def z963 : W := mkw 0x0025021800a88580 0x20004a043001510b 0x067c223831f81feb 0xda0cf8447063f03f

def z964 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007fff80070 0xe1fff8000ffff000

def z965 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x1ffc3ff800000007 0xb03ff87ff0000000

def z966 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f1fffc7e 0xfffc07f80fe3fff8

def z967 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffffe0001e027 0xf4fffffffc0003c0

def z968 : W := mkw 0x8000044acfe6b7b5 0xc1000008959fcd6f 0x80000001cfe61fd8 0x0b000000039fcc3f

def z969 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x67fffff800000007 0x44cffffff0000000

def z970 : W := mkw 0x216543520b82a321 0x8042ca86a4170546 0x61ffc3fe0f87e3bf 0x7ec3ff87fc1f0fc7

def z971 : W := mkw 0x0000000000000000 0x0000000000000000 0x067c223831f8006b 0xd20cf8447063f000

def z972 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff831980027 0xf4fffffff0633000

def z973 : W := mkw 0x000008a000000000 0x0000001140000000 0x00103ff800000007 0x9000207ff0000000

def z974 : W := mkw 0x5627fbb000000000 0x04ac4ff760000000 0x1e03fff800000006 0x843c07fff0000000

def z975 : W := mkw 0x8000044feff6b7fd 0xc30000089fdfed6f 0x80000007fffffff8 0x0b0000000fffffff

def z976 : W := mkw 0x560ab4057015584e 0x02ac15680ae02ab0 0xfe0ffc07f01ffc7e 0xfdfc1ff80fe03ff8

def z977 : W := mkw 0x8000044acf7616bd 0x43000008959eec2d 0x80000001cffe1fd8 0x0b000000039ffc3f

def z978 : W := mkw 0x216943420b92a329 0x8242d28684172546 0x61efc3c60f9fe3bf 0x7ec3df878c1f3fc7

def z979 : W := mkw 0x80000448c6e69795 0x41000008918dcd2f 0x80000001cfe79ff8 0x0b000000039fcf3f

def z980 : W := mkw 0x8000044a4ba6b7a5 0xc100000894974d6f 0x000000060f87ffb8 0x0a0000000c1f0fff

def z981 : W := mkw 0x7ffffbb010818902 0x04fffff760210312 0x7ffffff831819fef 0xfefffffff063033f

def z982 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831f99fe2 0xcc0cfe447063f33f

def z983 : W := mkw 0x5400040560041044 0x00a800080ac00820 0xfe03fc07f007fc7e 0xfdfc07f80fe00ff8

def z984 : W := mkw 0xfdd8044fff775eff 0x43fbb0089ffeeebd 0xfffc0007fffffff9 0xfbfff8000fffffff

def z985 : W := mkw 0x82022448d6671e97 0x4104044891acce3d 0x86032001fe679ffa 0xdf0c064003fccf3f

def z986 : W := mkw 0x776ffbb729100068 0x06eedff76e522000 0x666ffffe31980026 0x44ccdffffc633000

def z987 : W := mkw 0xf548044fef7616fd 0x43ea90089fdeec2d 0xe66c0007fffe1ff8 0x4bccd8000ffffc3f

def z988 : W := mkw 0x7fff2abfbdf98dfa 0x22fffe557f7bf31b 0xffff3ffffff99fff 0xfffffe7ffffff33f

def z989 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7ffcfff800000007 0xf0fff9fff0000000

def z990 : W := mkw 0x214041420b82a321 0x8042808284170546 0x6183c1c60f87e3be 0x7ec307838c1f0fc7

def z991 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x07ff22383ff99ffb 0xfe0ffe44707ff33f

def z992 : W := mkw 0x7dd808a7ad500078 0x02fbb0114f5aa000 0xfffc3c3ffff80079 0xf3fff8787ffff000

def z993 : W := mkw 0x7fff2ab000000000 0x00fffe5560000000 0x7fff3ff800000007 0xf4fffe7ff0000000

def z994 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007ffffe079 0xfbfff8000fffffc0

def z995 : W := mkw 0x236ffbb000000000 0x0446dff760000000 0x006ffff800000006 0x0400dffff0000000

def z996 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f203831f99fe8 0xce0cfe407063f33f

def z997 : W := mkw 0x29d000028d400030 0x0053a000051a8000 0xfffc0007fff80079 0xf3fff8000ffff000

def z998 : W := mkw 0x00254bb000000000 0x04004a9760000000 0x00003ff800000006 0x0000007ff0000000

def z999 : W := mkw 0x29fddbb000000000 0x0453fbb760000000 0x01fcdff800000005 0x0003f9bff0000000

def z1000 : W := mkw 0x7ffffbb520000040 0x04fffff76a400000 0xfffffff9f0000047 0xf5fffffff3e00000

def z1001 : W := mkw 0x7dfddbb000000000 0x04fbfbb760000000 0x7980dff800000004 0x20f301bff0000000

def z1002 : W := mkw 0x0227fbb000808100 0x04044ff760010102 0x0003fff800018386 0x0c0007fff0000307

def z1003 : W := mkw 0x5ebfbab000000000 0x04bd7f7560000000 0x1fff3ff800000007 0xf43ffe7ff0000000

def z1004 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80002001ce661fda 0x9b000040039ccc3f

def z1005 : W := mkw 0x7dfd4bb7ad500078 0x06fbfa976f5aa000 0xfffc3ffffff8007f 0xf3fff87ffffff000

def z1006 : W := mkw 0x7ffffbb530014842 0x04fffff76a600290 0xfffffffff001e07f 0xf5ffffffffe003c0

def z1007 : W := mkw 0x7ffffbb209000020 0x04fffff764120000 0x7ffffffe0e000017 0xf4fffffffc1c0000

def z1008 : W := mkw 0x5c900005a4400050 0x00b920000b488000 0xfffc0007fff80079 0xf3fff8000ffff000

def z1009 : W := mkw 0x089008a000000000 0x0011201140000000 0x01903ff800000007 0x0003207ff0000000

def z1010 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f007fc56 0xadfc07f80fe00ff8

def z1011 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce661fc7 0x8b33207ff39ccc3f

def z1012 : W := mkw 0x7dfddbb000000000 0x04fbfbb760000000 0x79ffdff800000007 0x74f3ffbff0000000

def z1013 : W := mkw 0x29d800028d500038 0x0253b000051aa000 0x9ffc0001fff80079 0xf33ff80003fff000

def z1014 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007fff80051 0xa3fff8000ffff000

def z1015 : W := mkw 0x00214ba000000000 0x0000429740000000 0x0003fff800000006 0x040007fff0000000

def z1016 : W := mkw 0x7df94ba7ad500078 0x02fbf2974f5aa000 0xfffffffffff8007f 0xf7fffffffffff000

def z1017 : W := mkw 0x7ffffbb21989a922 0xa4fffff764331352 0x7ffffffe3199e027 0xf4fffffffc6333c0

def z1018 : W := mkw 0x7df94be7afd2a379 0x82fbf297cf5fa546 0xffffffffffffe3ff 0xffffffffffffffc7

def z1019 : W := mkw 0x7ffffbb520000040 0x04fffff76a400000 0xfffffffff1f8007f 0xf7ffffffffe3f000

def z1020 : W := mkw 0x8000044fef7616fd 0x430000089fdeec2d 0x80000007ce661fd8 0x0b0000000f9ccc3f

def z1021 : W := mkw 0x7ffffbb520000040 0x04fffff76a400000 0x7ffffffe30000027 0xf4fffffffc600000

def z1022 : W := mkw 0x0ab7fbb000000000 0x04156ff760000000 0x0193fff800000007 0x040327fff0000000

def z1023 : W := mkw 0x7ffffbb000808100 0x04fffff760010102 0x7ffffffe0187e3bf 0xfefffffffc030fc7

def z1024 : W := mkw 0x5ebffbb000000000 0x04bd7ff760000000 0x1e1c3ff800000000 0x803c387ff0000000

def z1025 : W := mkw 0x0202b8a000000000 0x0004057140000000 0x0003fff800000006 0x040007fff0000000

def z1026 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff830780047 0xf4fffffff060f000

def z1027 : W := mkw 0x7ffffbb010898902 0x24fffff760211312 0x7ffffff8319983af 0xfefffffff0633307

def z1028 : W := mkw 0x29d808a28d500038 0x0253b011451aa000 0x01fc03f80ff80001 0x0203f807f01ff000

def z1029 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff801f80007 0xf6fffffff003f000

def z1030 : W := mkw 0x08b54bb000000000 0x04116a9760000000 0x19903ff800000007 0xb033207ff0000000

def z1031 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x1e1c3ff800000006 0x803c387ff0000000

def z1032 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe13fc07f067fc7f 0xfffc27f80fe0cff8

def z1033 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xf803fc07c007fc5e 0xbdf007f80f800ff8

def z1034 : W := mkw 0x0227fbb010010802 0x04044ff760200210 0x0003fff800019c06 0x0c0007fff0000338

def z1035 : W := mkw 0x7ffffbb000888100 0x24fffff760011102 0x7ffffff801980007 0xf4fffffff0033000

def z1036 : W := mkw 0x7ffffbb5a4500058 0x06fffff76b48a000 0xfffffff9c0000007 0xf5fffffff3800000

def z1037 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe1ffc07f07ffc7e 0xfdfc3ff80fe0fff8

def z1038 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903fffce67ffff 0xbb33207fff9ccfff

def z1039 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001c0661fc0 0x090000000380cc3f

def z1040 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61f3c3c60fe7e3ff 0xfec3e7878c1fcfc7

def z1041 : W := mkw 0x7dd8000084400010 0x00fbb00001088000 0xfffc0001fff80079 0xf3fff80003fff000

def z1042 : W := mkw 0x7dd84107ad502078 0x82fbb0820f5aa040 0xfffcc007fff86079 0xf3fff9800ffff0c0

def z1043 : W := mkw 0x7ffffbb73999896a 0x26fffff76e733312 0x7ffffffe31998027 0xf4fffffffc633300

def z1044 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffc3ff800000001 0xf0fff87ff0000000

def z1045 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x0003fff80007e006 0x0c0007fff0000fc0

def z1046 : W := mkw 0x75480007ad500078 0x02ea90000f5aa000 0xfe6c0007fff80078 0xf3fcd8000ffff000

def z1047 : W := mkw 0x8000044df6efdfd7 0x610000089beddfbf 0x80000007fffffff8 0x0b0000000fffffff

def z1048 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x7f9ffff800000007 0xf4ff3ffff0000000

def z1049 : W := mkw 0x7ffffbb00080a100 0x84fffff760010142 0x7ffffff80001e007 0xf4fffffff00003c0

def z1050 : W := mkw 0x0227fbb000808100 0x04044ff760010102 0x0063fff8018183af 0x5e00c7fff0030307

def z1051 : W := mkw 0x88900448d6ef9f97 0x6111200891addf3f 0x9ffc0001ffff9ff9 0xfb3ff80003ffff3f

def z1052 : W := mkw 0x88900448c6661695 0x41112008918ccc2d 0x81900001ce661fd9 0x0b032000039ccc3f

def z1053 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7990dff800000005 0x20f321bff0000000

def z1054 : W := mkw 0x7ffffbb5a4500058 0x06fffff76b48a000 0xfffffffff078007f 0xf5ffffffffe0f000

def z1055 : W := mkw 0x0021024002828301 0x0000420480050506 0x61e3c3c60f87e3bf 0x7ec3c7878c1f0fc7

def z1056 : W := mkw 0x2bff6bb000000000 0x0457fed760000000 0x1fff3ff800000007 0xf43ffe7ff0000000

def z1057 : W := mkw 0x7ffffbb530010842 0x04fffff76a600210 0xfffffffff0019c7f 0xfdffffffffe00338

def z1058 : W := mkw 0x75480007ad500078 0x02ea90000f5aa000 0xe67c0007fff80079 0xd3ccf8000ffff000

def z1059 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80006001f 0xfcfffffff0000c00

def z1060 : W := mkw 0x776ffbb000000000 0x04eedff760000000 0x6003fff800000006 0x04c007fff0000000

def z1061 : W := mkw 0x5c9008a000000000 0x00b9201140000000 0x7f903ff800000007 0xf0ff207ff0000000

def z1062 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff83000006f 0xf4fffffff0600000

def z1063 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001fffe1ff8 0x0b00000003fffc3f

def z1064 : W := mkw 0x80000448d6ef9f97 0x6100000891addf3f 0x80000001ce679fd8 0x0b000000039ccf3f

def z1065 : W := mkw 0x0890d9a000000000 0x041121b340000000 0x1990fff800000007 0xb03321fff0000000

def z1066 : W := mkw 0x7ffffbb084500018 0x06fffff76108a000 0x7ffffff800780007 0xf4fffffff000f000

def z1067 : W := mkw 0x002143400282a301 0x8000428680050546 0x6183c3c60e07e3bf 0x7ec307878c1c0fc7

def z1068 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80180002f 0xf6fffffff0030000

def z1069 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x79e3fff800000007 0x74f3c7fff0000000

def z1070 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f87e3b9 0x4ec3c7878c1f0fc7

def z1071 : W := mkw 0x7ffffbb000808100 0x04fffff760010102 0x7ffffff801800387 0xf6fffffff0030007

def z1072 : W := mkw 0x216d43520b82a321 0x8442da86a4170546 0x61efc3c60f87e3bf 0x7ec3df878c1f0fc7

def z1073 : W := mkw 0xfdd8044fef7616fd 0x43fbb0089fdeec2d 0xf9800007ce661fd8 0x2bf300000f9ccc3f

def z1074 : W := mkw 0x7ffffbb530014842 0x04fffff76a600290 0x7ffffff830000007 0xf4fffffff0600000

def z1075 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03dc07f007fc7c 0x6dfc07b80fe00ff8

def z1076 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffcfff800000005 0xa0fff9fff0000000

def z1077 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc2007fff81c7b 0xfbfff8400ffff038

def z1078 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce601fc7 0xb333207ff39cc03f

def z1079 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99933ff9ce679fff 0xff33267ff39ccf3f

def z1080 : W := mkw 0x7ffffbb20980a120 0x84fffff764130142 0x7ffffffe0181e3af 0xfefffffffc0303c7

def z1081 : W := mkw 0x7767fbb000000000 0x04eecff760000000 0x7fe3fff800000007 0xf4ffc7fff0000000

def z1082 : W := mkw 0x0a96b8b000000000 0x04152d7160000000 0x19903ff800000007 0xb033207ff0000000

def z1083 : W := mkw 0x776ffbb000000000 0x04eedff760000000 0x7e6ffff800000006 0xf4fcdffff0000000

def z1084 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f023831f99fe9 0x4e0cfe047063f33f

def z1085 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f87e3b5 0x66c3c7878c1f0fc7

def z1086 : W := mkw 0x7ffffbb084400010 0x04fffff761088000 0xfffffff9fff8007f 0xf7fffffff3fff000

def z1087 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f87e3b6 0x6cc3c7878c1f0fc7

def z1088 : W := mkw 0xfdd80448c6661695 0x41fbb008918ccc2d 0xfffc0001ce661fd9 0xfbfff800039ccc3f

def z1089 : W := mkw 0xa9f54bfa8feaa7b1 0xe153ea97f51fd54f 0x01fc03f80ff80381 0x0203f807f01ff007

def z1090 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99803ff9ce061f9f 0x3b33007ff39c0c3f

def z1091 : W := mkw 0x776ffbb000000000 0x04eedff760000000 0x667ffff800000007 0xd4ccfffff0000000

def z1092 : W := mkw 0x80000448d66f1e97 0x6100000891acde3d 0x80000001fe7e1fd8 0x0b00000003fcfc3f

def z1093 : W := mkw 0x5627fbb530014842 0x04ac4ff76a600290 0x6603fffe3001e026 0x44cc07fffc6003c0

def z1094 : W := mkw 0xde96bcbdf46d5cd6 0x61bd2d797be8dab9 0x9e1c3c39f0781c40 0x813c387873e0f038

def z1095 : W := mkw 0x29d008a000000000 0x0053a01140000000 0x79f03ff800000007 0xf0f3e07ff0000000

def z1096 : W := mkw 0x5e9ef9b000000000 0x04bd3df360000000 0x1e1cfdf800000004 0x803c39fbf0000000

def z1097 : W := mkw 0x7fdab8a7ad500078 0x02ffb5714f5aa000 0xfffffffffff8007f 0xf7fffffffffff000

def z1098 : W := mkw 0x560eb41570055846 0x04ac1d682ae00ab0 0xfe0ffc07f007fc7e 0xfdfc1ff80fe00ff8

def z1099 : W := mkw 0x75480007ad500078 0x02ea90000f5aa000 0xe7ec0007fff80079 0x73cfd8000ffff000

def z1100 : W := mkw 0x7ffffbb520100048 0x06fffff76a402000 0x7ffffff830180007 0xf4fffffff0603000

def z1101 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x061ffff800000006 0x840c3ffff0000000

def z1102 : W := mkw 0x29d80007ad500078 0x0253b0000f5aa000 0x87fc0007fff80079 0xd30ff8000ffff000

def z1103 : W := mkw 0x0227fbb00080a100 0x84044ff760010142 0x0003fff80001e006 0x040007fff00003c0

def z1104 : W := mkw 0x089008a7ad500078 0x021120114f5aa000 0x99903ffffff8007f 0xb333207ffffff000

def z1105 : W := mkw 0x5c980005a4500058 0x02b930000b48a000 0x9ffc0001fff80079 0xf33ff80003fff000

def z1106 : W := mkw 0x8000044842261685 0x4100000890844c2d 0x80000001c0061fd8 0x0900000003800c3f

def z1107 : W := mkw 0x5e92b8a5a4400050 0x00bd25714b488000 0xff93fffffe60007f 0xf7ff27fffffcc000

def z1108 : W := mkw 0x7dfddbb7ad500078 0x06fbfbb76f5aa000 0xfffcdffffff8007d 0xf3fff9bffffff000

def z1109 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff80060004f 0xb233207ff000c000

def z1110 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067c223831f81fcb 0x9a0cf8447063f03f

def z1111 : W := mkw 0x2367fbb000000000 0x0446cff760000000 0x67fffff800000007 0xf4cffffff0000000

def z1112 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80060004f 0xf6fffffff000c000

def z1113 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x61e3c3c60f87e3a7 0x4ec3c7878c1f0fc7

def z1114 : W := mkw 0x7fdef9b000000000 0x04ffbdf360000000 0x1f9c3df800000000 0x803f387bf0000000

def z1115 : W := mkw 0x7ffffbb7add08178 0x06fffff76f5ba102 0xfffffffffff983ff 0xfffffffffffff307

def z1116 : W := mkw 0x089008a000000000 0x0011201140000000 0x19901ff800000005 0x2033203ff0000000

def z1117 : W := mkw 0x8000044842a6b785 0xc100000890854d6f 0x000000000007ff80 0x0800000000000fff

def z1118 : W := mkw 0xd602b44df6675ed7 0x41ac05689beccebd 0xe603c007fe67fff8 0x4fcc07800ffccfff

def z1119 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0x0003c0000007fc00 0x0c00078000000ff8

def z1120 : W := mkw 0x5627fbb000000000 0x04ac4ff760000000 0x7803fff800000006 0x24f007fff0000000

def z1121 : W := mkw 0x7ffffbb209808120 0x04fffff764130102 0x7ffffffe0f8183bf 0xfefffffffc1f0307

def z1122 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x667f223e31f99ffb 0xfeccfe447c63f33f

def z1123 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xffffc007fff8007f 0xf7ffff800ffff000

def z1124 : W := mkw 0x88980ce8c676169d 0x43113019d18cec2d 0x999c3ff9ce7e1fdf 0xbb33387ff39cfc3f

def z1125 : W := mkw 0x089008a000000000 0x0011201140000000 0x18103ff800000006 0x8030207ff0000000

def z1126 : W := mkw 0xfdd8044fffff9fff 0x63fbb0089fffff3f 0xfffc0007ffff9ff9 0xfbfff8000fffff3f

def z1127 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831ff9fff 0xfe0cfe447063ff3f

def z1128 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xfffffffff1f80067 0xf5ffffffffe3f000

def z1129 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x6183c3c60f87e3be 0x2ec307878c1f0fc7

def z1130 : W := mkw 0x089008a000000000 0x0011201140000000 0x1ffc3ff800000007 0xf03ff87ff0000000

def z1131 : W := mkw 0x5c9808a000000000 0x00b9301140000000 0x1f9c3ff800000007 0xb03f387ff0000000

def z1132 : W := mkw 0x5c9808a5a4500058 0x02b930114b48a000 0x9f9c3ff9f0780047 0xb13f387ff3e0f000

def z1133 : W := mkw 0x7ffffbb5a4400050 0x04fffff76b488000 0xfffffffffe60007f 0xf7fffffffffcc000

def z1134 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7f83fff800000006 0xf4ff07fff0000000

def z1135 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x07ff23f831f99fef 0xfe0ffe47f063f33f

def z1136 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001ce061f90 0x09000000039c0c3f

def z1137 : W := mkw 0x7ffffbb530014842 0x04fffff76a600290 0x7ffffffe3001fc6f 0xfcfffffffc6003f8

def z1138 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce601fd9 0xb333207ff39cc03f

def z1139 : W := mkw 0x5602b40040041004 0x00ac056800800820 0xfe03fc07c007fc7e 0xfdfc07f80f800ff8

def z1140 : W := mkw 0x5c9098a000000000 0x00b9213140000000 0x7990fff800000007 0xb0f321fff0000000

def z1141 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x066ffff800000006 0x440cdffff0000000

def z1142 : W := mkw 0x2367fbb000000000 0x0446cff760000000 0x01e3fff800000007 0x0403c7fff0000000

def z1143 : W := mkw 0x0ab7fbb000000000 0x04156ff760000000 0x1813fff800000006 0x843027fff0000000

def z1144 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x007ffff800000007 0x0400fffff0000000

def z1145 : W := mkw 0x7ffffbb520000040 0x04fffff76a400000 0xffffffffc0000017 0xf5ffffffff800000

def z1146 : W := mkw 0x5c9008a520000040 0x00b920114a400000 0xff903ffff000007f 0xf1ff207fffe00000

def z1147 : W := mkw 0x7ffffbb084400010 0x04fffff761088000 0x7ffffff80e600007 0xf6fffffff01cc000

def z1148 : W := mkw 0x8000044acf6636b5 0xc1000008959ecc6d 0x80000007ce667fd8 0x0b0000000f9cccff

def z1149 : W := mkw 0x7ffffbb000808100 0x04fffff760010102 0x7ffffff831f983ef 0xfefffffff063f307

def z1150 : W := mkw 0x88900448c6661695 0x41112008918ccc2d 0x98100001ce661fd8 0x8b302000039ccc3f

def z1151 : W := mkw 0x214041420b022221 0x8042808284160444 0x6183c3c60e07e3bf 0x7ec307878c1c0fc7

def z1152 : W := mkw 0x7ffffbb7bdd9897a 0x26fffff76f7bb312 0xfffffffffff9807f 0xf7fffffffffff300

def z1153 : W := mkw 0x7dd8d9a000000000 0x04fbb1b340000000 0x7980fff800000006 0x20f301fff0000000

def z1154 : W := mkw 0x7dd808a7ad500078 0x02fbb0114f5aa000 0xf9801dc7ce000014 0x21f3003b8f9c0000

def z1155 : W := mkw 0x7dd849a7ad500078 0x06fbb0934f5aa000 0xfffc01c7fff80079 0xf3fff8038ffff000

def z1156 : W := mkw 0x7dfd4bb000000000 0x04fbfa9760000000 0x7ffc3ff800000007 0xf0fff87ff0000000

def z1157 : W := mkw 0x88900448c6661695 0x41112008918ccc2d 0x99800001ce661fd8 0x2b330000039ccc3f

def z1158 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0x9ffc0001fff80069 0xd33ff80003fff000

def z1159 : W := mkw 0x5627fbb520000040 0x04ac4ff76a400000 0xfe03fffff000007e 0xf5fc07ffffe00000

def z1160 : W := mkw 0x089008a000000000 0x0011201140000000 0x19803ff800000006 0x2033007ff0000000

def z1161 : W := mkw 0x0025dbb000000000 0x04004bb760000000 0x0000dff800000004 0x000001bff0000000

def z1162 : W := mkw 0x7df94ba000000000 0x00fbf29740000000 0x7ffffff800000007 0xf4fffffff0000000

def z1163 : W := mkw 0x0206b8b000000000 0x04040d7160000000 0x00003ff800000006 0x0000007ff0000000

def z1164 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f007fc66 0xcdfc07f80fe00ff8

def z1165 : W := mkw 0x0227fbb010898902 0x24044ff760211312 0x066ffff831998026 0x440cdffff0633300

def z1166 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903df800000004 0xa033207bf0000000

def z1167 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x6003fffe0007e03e 0x7cc007fffc000fc0

def z1168 : W := mkw 0x29f14ba000000000 0x0053e29740000000 0x19f03ff800000007 0xb033e07ff0000000

def z1169 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff80000038f 0xba33207ff0000007

def z1170 : W := mkw 0x0227f75852afff87 0xa0044feeb0a55fff 0x0003fff80007ff86 0x0c0007fff0000fff

def z1171 : W := mkw 0x0ab7fbb000000000 0x04156ff760000000 0x1983fff800000006 0x243307fff0000000

def z1172 : W := mkw 0x5e92b8a530014842 0x00bd25714a600290 0x7f93fffe3001e027 0xf4ff27fffc6003c0

def z1173 : W := mkw 0x08b10aa000000000 0x0011621540000000 0x19f33ff800000007 0xf433e67ff0000000

def z1174 : W := mkw 0x2bf76bb000000000 0x0057eed760000000 0x7ffffff800000007 0xf4fffffff0000000

def z1175 : W := mkw 0x7fdef9b7ad500078 0x06ffbdf36f5aa000 0xff9cfdfffe780054 0xa1ff39fbfffcf000

def z1176 : W := mkw 0x7fdaf9a000000000 0x04ffb5f340000000 0x7f93fff800000007 0xf4ff27fff0000000

def z1177 : W := mkw 0x7ffffbb73981e962 0x84fffff76e7303d2 0x7ffffffe3181e027 0xf4fffffffc6303c0

def z1178 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f007fc74 0xe5fc07f80fe00ff8

def z1179 : W := mkw 0x7dd89007ad500078 0x02fbb1200f5aa000 0xfffcdc07fff8007d 0xf3fff9b80ffff000

def z1180 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0xfffffff9c000005f 0xf5fffffff3800000

def z1181 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9fffe1fff 0xbb33207ff3fffc3f

def z1182 : W := mkw 0x7ddcd9b000000000 0x04fbb9b360000000 0x799cddf800000004 0x20f339bbf0000000

def z1183 : W := mkw 0x7ffffbb73911486a 0x06fffff76e722290 0x7ffffffe3199e027 0xf4fffffffc6333c0

def z1184 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce661fd6 0xa933207ff39ccc3f

def z1185 : W := mkw 0x7dd808a7ad500078 0x02fbb0114f5aa000 0xf9903fffce000017 0xb1f3207fff9c0000

def z1186 : W := mkw 0xa9d8044acf7616bd 0x4353b008959eec2d 0x81fc0001cffe1fd9 0x0b03f800039ffc3f

def z1187 : W := mkw 0x0227fbb010010802 0x04044ff760200210 0x0603fff830019c6e 0xdc0c07fff0600338

def z1188 : W := mkw 0x0a9228a010010802 0x0015245140200210 0x1f933ff830019c6f 0xfc3f267ff0600338

def z1189 : W := mkw 0x8000044842261685 0x4100000890844c2d 0x0000000000661fc8 0x0a0000000000cc3f

def z1190 : W := mkw 0x0000d9a000000000 0x040001b340000000 0x0000fff800000006 0x000001fff0000000

def z1191 : W := mkw 0x7767f31000000000 0x00eecfe620000000 0x7ffffff800000007 0xf4fffffff0000000

def z1192 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x80000001ce601fc0 0x03000000039cc03f

def z1193 : W := mkw 0xa9d0044acfe6b7b5 0xc153a008959fcd6f 0xf9f00007cfe7fff9 0xfbf3e0000f9fcfff

def z1194 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x9e7f2239f1f99ffb 0xff3cfe4473e3f33f

def z1195 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x67ffc3c60f87e3bf 0xfecfff878c1f0fc7

def z1196 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffffe0000003f 0xf4fffffffc000000

def z1197 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0xe003c007ce67fffe 0x7fc007800f9ccfff

def z1198 : W := mkw 0x80000448d6675e97 0x4100000891accebd 0x80000001ce67ffd8 0x0b000000039ccfff

def z1199 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x79e3ffc60f87e3bf 0xfef3c7ff8c1f0fc7

def z1200 : W := mkw 0x5c980007ad500078 0x02b930000f5aa000 0x9e7c0007fff80079 0xd33cf8000ffff000

def z1201 : W := mkw 0x5627fbb000000000 0x04ac4ff760000000 0x7e7ffff800000007 0xf4fcfffff0000000

def z1202 : W := mkw 0x7dd8d107ad500078 0x06fbb1a20f5aa000 0xfffcc007fff80079 0xf3fff9800ffff000

def z1203 : W := mkw 0x08900ce042061205 0x00112019c0840c24 0x99903ff9ce061fdf 0xbb33207ff39c0c3f

def z1204 : W := mkw 0x7ffffbb084400010 0x04fffff761088000 0xfffffff9ce000017 0xf5fffffff39c0000

def z1205 : W := mkw 0x0000040570055846 0x000000080ae00ab0 0xf803fc07f007fc7e 0xfdf007f80fe00ff8

def z1206 : W := mkw 0x8000044de66616d5 0x410000089bcccc2d 0x80000007fe661ff8 0x0b0000000ffccc3f

def z1207 : W := mkw 0x7dd808a000000000 0x00fbb01140000000 0x79903ff800000007 0xb0f3207ff0000000

def z1208 : W := mkw 0x80000448c6ee9795 0x61000008918ddd2f 0x80000001cffe1fd8 0x0b000000039ffc3f

def z1209 : W := mkw 0x80000448c6661695 0x41000008918ccc2d 0x000000000e661f80 0x0a000000001ccc3f

def z1210 : W := mkw 0x7ffffbb520004040 0x04fffff76a400080 0x7ffffffe00006007 0xf4fffffffc0000c0

def z1211 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc0007fff80061 0xc3fff8000ffff000

def z1212 : W := mkw 0x80000ce842261685 0x41000019d0844c2d 0x99803ff9ce061fdf 0xbb33007ff39c0c3f

def z1213 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99903ff9ce661fd5 0xa333207ff39ccc3f

def z1214 : W := mkw 0x8000044fffff9fff 0x630000089fffff3f 0x80000007ffff9ff8 0x0b0000000fffff3f

def z1215 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99f03ff9cfe61fff 0xfb33e07ff39fcc3f

def z1216 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x0603fff800000006 0xd40c07fff0000000

def z1217 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x67efc3c63f9fe3bf 0x7ecfdf878c7f3fc7

def z1218 : W := mkw 0x80000448c6e6b795 0xc1000008918dcd6f 0x80000001ce67ffd8 0x0b000000039ccfff

def z1219 : W := mkw 0x089008a084400010 0x0011201141088000 0x99903ff9c0600047 0xb133207ff380c000

def z1220 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x0013fff800000007 0x940027fff0000000

def z1221 : W := mkw 0x089008a000000000 0x0011201140000000 0x99903ff9c000005f 0xb133207ff3800000

def z1222 : W := mkw 0x216143420b82a321 0x8042c28684170546 0x6183c3c60e07e3be 0x7cc307878c1c0fc7

def z1223 : W := mkw 0x2367fbb000000000 0x0446cff760000000 0x6183fff800000006 0x24c307fff0000000

def z1224 : W := mkw 0x7ffffbb010010802 0x04fffff760200210 0x7ffffff830018027 0xf4fffffff0600300

def z1225 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831f99fe1 0xc60cfe447063f33f

def z1226 : W := mkw 0x29fd4bb28d500038 0x0653fa97651aa000 0x99fc3ff9cff8005f 0xb333f87ff39ff000

def z1227 : W := mkw 0x7ffffbb010010802 0x04fffff760200210 0x7ffffffe3007fc7f 0xfcfffffffc600ff8

def z1228 : W := mkw 0x7fdef9b000000000 0x04ffbdf360000000 0x7980fdf800000004 0x20f301fbf0000000

def z1229 : W := mkw 0x7fdeb8b7ad500078 0x06ffbd716f5aa000 0xfffc3ffffff8007f 0xf3fff87ffffff000

def z1230 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0x9ffc3ff9fff80041 0x833ff87ff3fff000

def z1231 : W := mkw 0x5c9808a5a4500058 0x02b930114b48a000 0x9e1c3c39f0780040 0x813c387873e0f000

def z1232 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x79fffff800000007 0x24f3fffff0000000

def z1233 : W := mkw 0x0ab7fbb000000000 0x04156ff760000000 0x1ffffff800000007 0xf43ffffff0000000

def z1234 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0xffffffffffffe07f 0xffffffffffffffc0

def z1235 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xffffc007fff9e079 0xf7ffff800ffff3c0

def z1236 : W := mkw 0x7ffffbb209000020 0x04fffff764120000 0x7ffffffe0f87e03f 0xfefffffffc1f0fc0

def z1237 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x01fc3ff800000007 0x0003f87ff0000000

def z1238 : W := mkw 0x089008a000000000 0x0011201140000000 0x1ffc3ff831f8006f 0xf23ff87ff063f000

def z1239 : W := mkw 0x8000044df6675ed7 0x410000089beccebd 0x80000001fe661fd8 0x0b00000003fccc3f

def z1240 : W := mkw 0x7dfddbb000000000 0x04fbfbb760000000 0x79fcfff800000007 0xb0f3f9fff0000000

def z1241 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067c223831f99fe9 0x8a0cf8447063f33f

def z1242 : W := mkw 0x000008a000000000 0x0000001140000000 0x18003ff800000006 0xb030007ff0000000

def z1243 : W := mkw 0x7dfddbb000000000 0x04fbfbb760000000 0x7ffcdff800000005 0xf0fff9bff0000000

def z1244 : W := mkw 0x29d008a209000020 0x0053a01144120000 0x79f03ffe0f80003f 0xf2f3e07ffc1f0000

def z1245 : W := mkw 0xa9f94bea8ff2a7b9 0xc353f297d51fe54f 0x01fc03f80ff80381 0x0203f807f01ff007

def z1246 : W := mkw 0xfdd89ce7ef56527d 0x43fbb139cfdeaca4 0xf980ddc7ce066014 0x21f301bb8f9c0cc0

def z1247 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff80001802f 0xfcfffffff0000300

def z1248 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x667fe23e31f9ffeb 0xdeccffc47c63f3ff

def z1249 : W := mkw 0x0202b40050055806 0x0004056800a00ab0 0xf803fc07c007fc7e 0xfdf007f80f800ff8

def z1250 : W := mkw 0x0227fbb000000000 0x04044ff760000000 0x0183fff800000007 0x340307fff0000000

def z1251 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067fe23831ffffef 0xde0cffc47063ffff

def z1252 : W := mkw 0x0206f9b000000000 0x04040df360000000 0x0000fdf800000004 0x000001fbf0000000

def z1253 : W := mkw 0x7ffffbb000808100 0x04fffff760010102 0x7ffffff800018387 0xfcfffffff0000307

def z1254 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07f007fc36 0x6dfc07f80fe00ff8

def z1255 : W := mkw 0x2367fbb209000020 0x0446cff764120000 0x61e3fffe0f80003f 0x76c3c7fffc1f0000

def z1256 : W := mkw 0xde9abcadf4755cde 0x43bd35795be8eab9 0x9e1c3c39f0781c40 0x813c387873e0f038

def z1257 : W := mkw 0x089008a000000000 0x0011201140000000 0x19903ff800001c4f 0xb833207ff0000038

def z1258 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x99803ff9ce661fde 0x2b33007ff39ccc3f

def z1259 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffc223ffff8007b 0xf3fff8447ffff000

def z1260 : W := mkw 0x29fd4bb000000000 0x0453fa9760000000 0x19fc3ff800000001 0x8033f87ff0000000

def z1261 : W := mkw 0x7ffffbb209000020 0x04fffff764120000 0x7ffffffe01800027 0xf4fffffffc030000

def z1262 : W := mkw 0x2bfffbb000000000 0x0457fff760000000 0x0183fff800000006 0x040307fff0000000

def z1263 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067c223831f81fe9 0xd20cf8447063f03f

def z1264 : W := mkw 0x8227bef852afdf87 0x61044f7df0a55fbf 0x0003fff80007ff86 0x0c0007fff0000fff

def z1265 : W := mkw 0x08b50ab000000000 0x00116a1560000000 0x19fc3ff800000007 0xb033f87ff0000000

def z1266 : W := mkw 0x7ffffbb729100068 0x06fffff76e522000 0x7ffffffe31f8006f 0xf6fffffffc63f000

def z1267 : W := mkw 0x0abffbb000000000 0x04157ff760000000 0x001ffff800000006 0x04003ffff0000000

def z1268 : W := mkw 0x0227221810a98d82 0x20044e443021531b 0x067f223831f99fa3 0x4e0cfe447063f33f

def z1269 : W := mkw 0x8000044de67616dd 0x430000089bccec2d 0x80000001fe7e1fd8 0x0b00000003fcfc3f

def z1270 : W := mkw 0x8000044842261685 0x4100000890844c2d 0x000000000e061f98 0x0a000000001c0c3f

def z1271 : W := mkw 0x7ffffbb7bd51487a 0x06fffff76f7aa290 0xfffffffffff9e07f 0xf7fffffffffff3c0

def z1272 : W := mkw 0x002143400282a301 0x8000428680050546 0x0003c0000007e380 0x0c00078000000fc7

def z1273 : W := mkw 0x5e9eb8b000000000 0x04bd3d7160000000 0x1f9c3ff800000001 0x803f387ff0000000

def z1274 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xf803fc07c007fc3e 0x7df007f80f800ff8

def z1275 : W := mkw 0x29f14ba28d400030 0x0053e297451a8000 0xf9f3ffffcfe0007f 0xf7f3e7ffff9fc000

def z1276 : W := mkw 0x5627fbb000000000 0x04ac4ff760000000 0x6603fff800000006 0x44cc07fff0000000

def z1277 : W := mkw 0x7dfddbb7ad500078 0x06fbfbb76f5aa000 0xf9fcdfffcff80015 0x23f3f9bfff9ff000

def z1278 : W := mkw 0x2367fbb20980a120 0x8446cff764130142 0x6063fffe0181e026 0x44c0c7fffc0303c0

def z1279 : W := mkw 0x0ab72ab084400010 0x00156e5561088000 0x9fff3ff9fff8007f 0xf73ffe7ff3fff000

def z1280 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffdf800000004 0xe4fffffbf0000000

def z1281 : W := mkw 0x5ebffbb000000000 0x04bd7ff760000000 0x1803fff800000006 0x043007fff0000000

def z1282 : W := mkw 0x2bfffbb000000000 0x0457fff760000000 0x07fffff800000007 0xd40ffffff0000000

def z1283 : W := mkw 0x7ffffbb7ad500078 0x06fffff76f5aa000 0x7ffffffe3ff80027 0xf6fffffffc7ff000

def z1284 : W := mkw 0x7ffffbb20980a120 0x84fffff764130142 0x7ffffffe0187e03f 0xfcfffffffc030fc0

def z1285 : W := mkw 0x7540000729000060 0x00ea80000e520000 0xfffc0007fff80079 0xf3fff8000ffff000

def z1286 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7ffffff800001c4f 0xfcfffffff0000038

def z1287 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fc07c007fc16 0xfdfc07f80f800ff8

def z1288 : W := mkw 0x7ffffbb000000000 0x04fffff760000000 0x7f9ffff800000006 0xa4ff3ffff0000000

def z1289 : W := mkw 0x5602b40570055846 0x00ac05680ae00ab0 0xfe03fe07f007ffff 0xfffc07fc0fe00fff

def z1290 : W := mkw 0x7dd80007ad500078 0x02fbb0000f5aa000 0xfffcc007fffe607d 0xf3fff9800ffffcc0

def z1291 : W := mkw 0x88900ce8c6661695 0x41112019d18ccc2d 0x9f903ff9fe661fff 0xfb3f207ff3fccc3f

def z1292 : W := mkw 0x7dd8d9a7ad500078 0x06fbb1b34f5aa000 0xf990ffffce60005f 0xb3f321ffff9cc000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z9,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z12,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z15,z5,z6]),(0,[z1,z2,z16,z3,z4,z5,z6])],[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z6]),(0,[z20,z1,z2,z21,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z24,z3,z4,z6,z25]),(1,[z1,z2,z26,z3,z4,z6]),(0,[z1,z2,z3,z27,z4,z5,z6]),(0,[z1,z2,z3,z28,z4,z5,z6]),(0,[z29,z1,z2,z3,z4,z30,z6]),(0,[z1,z11,z2,z3,z4,z6,z6])],[(0,[z31,z1,z32,z2,z3,z4,z6]),(0,[z33,z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z26,z35,z3,z4,z6])],[(0,[z1,z2,z3,z36,z4,z5,z6]),(0,[z1,z37,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z6])],[(0,[z1,z32,z2,z3,z39,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z40]),(0,[z1,z2,z3,z41,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z44,z4,z5,z6]),(0,[z1,z2,z45,z3,z4,z5,z6]),(0,[z1,z46,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z34,z6])],[(0,[z1,z2,z3,z4,z5,z6,z47]),(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z49,z1,z32,z2,z3,z4,z6])],[(0,[z50,z2,z3,z51,z4,z5,z6]),(0,[z31,z1,z2,z52,z4,z5,z6]),(0,[z1,z2,z3,z4,z53,z5,z6]),(0,[z1,z54,z2,z3,z5,z6,z40]),(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z55,z4,z6]),(0,[z1,z2,z3,z56,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z57,z6]),(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z59,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z5,z61]),(0,[z1,z2,z3,z4,z62,z5,z6]),(0,[z1,z2,z63,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z64,z6])]],
   [[(0,[z1,z2,z3,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z66]),(0,[z67,z1,z11,z2,z3,z4,z6]),(1,[z1,z2,z3,z68,z5,z6]),(0,[z1,z2,z3,z69,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z70,z6])],[(0,[z1,z2,z71,z3,z4,z34,z6]),(0,[z72,z2,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z6]),(0,[z1,z2,z3,z68,z4,z5,z6])],[(0,[z1,z74,z2,z3,z4,z5,z6]),(0,[z67,z1,z2,z3,z4,z5,z6]),(0,[z75,z1,z3,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z1,z2,z78,z44,z3,z4,z6])],[(0,[z1,z2,z3,z4,z79,z5,z6]),(0,[z80,z1,z2,z3,z4,z5,z6]),(1,[z1,z12,z3,z81,z5,z6]),(0,[z1,z82,z2,z3,z4,z5,z6])],[(0,[z1,z83,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z84,z5,z6]),(0,[z85,z1,z32,z2,z3,z4,z6])],[(0,[z1,z2,z86,z3,z4,z5,z6]),(0,[z1,z87,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z88,z6])],[(0,[z89,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z1,z2,z91,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z92]),(0,[z1,z32,z2,z3,z4,z93,z6]),(0,[z1,z2,z3,z4,z5,z94,z6]),(0,[z1,z2,z3,z95,z4,z5,z6]),(1,[z96,z1,z32,z2,z3,z6]),(0,[z1,z2,z3,z4,z34,z97,z6])]],
   [[(0,[z1,z2,z98,z3,z4,z5,z6]),(1,[z99,z1,z3,z4,z5,z6]),(0,[z1,z32,z2,z100,z3,z4,z6])],[(0,[z89,z1,z2,z3,z4,z30,z6]),(0,[z101,z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z5,z6,z102]),(0,[z1,z11,z2,z3,z4,z103,z6]),(0,[z1,z2,z3,z104,z4,z5,z6])],[(0,[z1,z2,z3,z4,z105,z34,z6]),(0,[z1,z2,z3,z39,z4,z106,z6]),(0,[z1,z107,z2,z3,z4,z34,z6])],[(0,[z33,z2,z3,z39,z4,z5,z6]),(0,[z1,z11,z2,z78,z3,z4,z6]),(0,[z1,z2,z3,z108,z4,z34,z6]),(0,[z1,z2,z3,z4,z30,z109,z6])],[(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z76,z5,z6]),(0,[z1,z107,z2,z3,z8,z4,z6]),(0,[z1,z2,z3,z4,z30,z93,z6]),(0,[z1,z2,z3,z111,z4,z5,z6])],[(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z93,z6]),(0,[z114,z1,z2,z3,z4,z97,z6])],[(0,[z1,z2,z3,z4,z9,z93,z6]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z116,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z6,z117]),(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z118,z1,z11,z2,z3,z4,z6])],[(0,[z1,z2,z119,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z120,z6]),(0,[z1,z2,z3,z55,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z1,z2,z3,z4,z5,z97,z122]),(0,[z1,z2,z3,z4,z5,z123,z25]),(0,[z1,z2,z78,z3,z4,z30,z6])],[(0,[z124,z1,z2,z3,z4,z5,z6]),(0,[z1,z32,z107,z2,z3,z4,z6]),(0,[z29,z1,z32,z2,z3,z4,z6]),(1,[z1,z2,z3,z30,z6,z125])],[(0,[z1,z2,z3,z76,z4,z126,z6]),(0,[z1,z2,z3,z4,z127,z5,z6]),(0,[z1,z2,z128,z3,z4,z5,z6])],[(0,[z1,z2,z3,z76,z4,z5,z6]),(0,[z129,z1,z3,z4,z5,z6,z25]),(1,[z1,z130,z2,z3,z4,z6]),(0,[z1,z2,z131,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z132,z5,z6])],[(0,[z1,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z133,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z134,z6]),(0,[z1,z2,z3,z4,z135,z5,z6]),(0,[z1,z2,z136,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z138,z6]),(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z140]),(0,[z1,z2,z3,z4,z5,z141,z6]),(0,[z1,z46,z2,z3,z4,z5,z125])],[(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z143,z5,z6]),(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z6,z145])],[(0,[z1,z146,z2,z3,z4,z5,z6]),(0,[z147,z1,z107,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z44,z4,z103,z6])]],
   [[(0,[z50,z1,z32,z2,z3,z4,z6])],[(0,[z1,z2,z3,z148,z4,z5,z6]),(0,[z149,z150,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z151,z4,z5,z6]),(0,[z1,z2,z152,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z153,z6])],[(0,[z1,z154,z155,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z156,z5,z6])],[(0,[z2,z3,z39,z4,z5,z122,z6]),(0,[z1,z2,z3,z4,z5,z157,z6]),(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z103,z6])],[],[(0,[z2,z52,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z61,z6]),(0,[z1,z2,z3,z4,z160,z5,z6])],[(0,[z1,z2,z3,z4,z161,z5,z6]),(0,[z1,z2,z3,z4,z162,z5,z6]),(0,[z1,z163,z2,z3,z4,z5,z6]),(0,[z164,z1,z32,z2,z3,z4,z6])],[(0,[z165,z2,z71,z3,z4,z5,z6]),(0,[z165,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z166,z6]),(0,[z147,z1,z11,z2,z3,z4,z6]),(0,[z167,z1,z2,z3,z4,z5,z6]),(0,[z1,z168,z32,z2,z3,z4,z6])]],
   [[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z170,z1,z2,z3,z4,z5,z6]),(0,[z101,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z3,z4,z5,z6,z171]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z172,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z6,z125]),(0,[z1,z11,z2,z173,z3,z4,z6])],[(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z174,z1,z2,z3,z4,z5,z6]),(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z6]),(0,[z1,z177,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z178,z5,z6]),(0,[z1,z2,z179,z3,z180,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z181]),(0,[z1,z2,z3,z4,z5,z6,z182])],[(0,[z31,z2,z71,z3,z4,z5,z6]),(0,[z31,z1,z11,z2,z3,z4,z6]),(1,[z1,z183,z2,z3,z4,z6]),(0,[z149,z1,z154,z3,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z5,z6]),(0,[z129,z1,z60,z3,z4,z5,z6]),(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z186,z3,z4,z6]),(0,[z187,z1,z32,z2,z3,z4,z6]),(0,[z1,z32,z2,z3,z4,z97,z6])],[(0,[z1,z188,z2,z3,z4,z34,z6]),(1,[z75,z1,z3,z76,z5,z6]),(0,[z1,z189,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z190,z5,z6]),(0,[z67,z1,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z25,z117]),(0,[z1,z2,z3,z4,z103,z34,z6])],[(0,[z1,z2,z3,z4,z191,z5,z6]),(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z1,z2,z3,z193,z4,z5,z6])],[(0,[z1,z2,z194,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z195])],[(0,[z20,z2,z3,z4,z5,z122,z6]),(0,[z101,z1,z2,z3,z4,z113,z6]),(0,[z196,z2,z3,z4,z9,z5,z6]),(0,[z149,z1,z2,z155,z4,z5,z6]),(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z197,z5,z6]),(0,[z1,z2,z3,z4,z30,z97,z6]),(0,[z1,z2,z198,z3,z4,z5,z6]),(0,[z1,z2,z199,z3,z4,z34,z6])]],
   [[(0,[z1,z2,z200,z3,z4,z5,z6]),(0,[z43,z1,z2,z78,z4,z5,z6])],[(0,[z1,z2,z71,z3,z4,z30,z6]),(0,[z1,z201,z2,z3,z4,z5,z6]),(0,[z202,z1,z2,z3,z4,z5,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z129,z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z5,z6,z204]),(0,[z1,z2,z3,z4,z5,z6,z205]),(0,[z1,z2,z3,z4,z206,z5,z6]),(0,[z1,z2,z3,z207,z4,z5,z6])],[(0,[z1,z2,z3,z51,z4,z30,z6]),(0,[z89,z1,z46,z2,z3,z5,z6]),(0,[z149,z1,z2,z208,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z209,z6]),(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z6]),(0,[z1,z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z212,z6]),(0,[z1,z2,z3,z4,z5,z6,z213])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z89,z1,z2,z3,z5,z30,z6]),(1,[z1,z2,z3,z214,z5,z6])],[(0,[z1,z2,z3,z4,z215,z5,z6]),(0,[z149,z216,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z217,z6]),(0,[z1,z218,z2,z3,z4,z5,z6]),(0,[z85,z1,z11,z2,z3,z4,z6]),(0,[z219,z1,z2,z3,z4,z5,z6])],[(1,[z1,z86,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z220,z6]),(0,[z221,z1,z2,z3,z4,z5,z6]),(1,[z149,z1,z208,z4,z5,z6]),(0,[z1,z12,z3,z4,z81,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z222]),(0,[z1,z11,z2,z3,z223,z4,z6])],[(0,[z224,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z113,z6]),(0,[z1,z2,z155,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z225,z6])],[(1,[z1,z2,z3,z4,z5,z166]),(0,[z20,z96,z1,z2,z3,z5,z6]),(0,[z75,z1,z2,z3,z4,z34,z6]),(0,[z85,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z6,z226]),(1,[z1,z2,z227,z3,z4,z6]),(0,[z1,z2,z3,z4,z34,z123,z6]),(0,[z1,z2,z3,z4,z228,z5,z6])]],
   [[(0,[z33,z1,z2,z3,z4,z5,z40]),(0,[z149,z1,z2,z3,z4,z34,z6]),(0,[z1,z12,z2,z3,z4,z5,z6])],[(0,[z101,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z1,z230,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z1,z32,z2,z3,z4,z6,z145]),(0,[z1,z2,z3,z4,z5,z97,z6])],[(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z6]),(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z235,z5,z6]),(1,[z1,z2,z35,z236,z5,z6])],[(0,[z1,z2,z3,z4,z5,z237,z6]),(1,[z20,z2,z3,z105,z5,z6]),(0,[z238,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z30,z6]),(0,[z240,z1,z32,z2,z3,z4,z6]),(0,[z241,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z242,z5,z6]),(0,[z20,z1,z32,z2,z3,z4,z6]),(0,[z101,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z243,z3,z4,z5,z6]),(0,[z1,z2,z244,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z245,z5,z6]),(0,[z43,z1,z2,z3,z4,z103,z6]),(0,[z1,z32,z246,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z247])],[(0,[z248,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z249]),(0,[z1,z2,z3,z5,z57,z6,z40]),(1,[z1,z107,z3,z4,z93,z6]),(0,[z1,z2,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z250,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z34,z6]),(1,[z1,z11,z2,z3,z160,z6]),(0,[z1,z251,z2,z3,z4,z5,z6])],[(0,[z196,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z208,z4,z30,z6]),(0,[z29,z1,z154,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z252]),(0,[z43,z1,z2,z78,z3,z4,z6]),(0,[z1,z2,z3,z4,z30,z6,z145])],[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z179,z3,z81,z5,z6]),(0,[z253,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z4,z30,z6]),(1,[z129,z1,z3,z4,z5,z25]),(0,[z1,z32,z2,z3,z4,z61,z6]),(0,[z1,z46,z2,z3,z254,z4,z6])],[(0,[z1,z2,z3,z4,z5,z255,z6]),(0,[z1,z2,z256,z3,z4,z5,z6]),(0,[z29,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z257,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z258,z125])],[(0,[z1,z32,z2,z71,z3,z4,z6]),(0,[z96,z89,z1,z2,z3,z5,z6]),(0,[z259,z1,z2,z3,z4,z5,z6]),(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z261,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z34,z6,z182])],[(0,[z1,z2,z3,z4,z5,z6,z262]),(0,[z29,z1,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z6,z263]),(0,[z1,z32,z2,z3,z4,z6,z125]),(0,[z1,z2,z3,z4,z5,z264,z6])],[(0,[z75,z1,z188,z3,z4,z5,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z46,z11,z2,z3,z4,z6])],[(1,[z1,z2,z266,z4,z5,z6]),(0,[z2,z3,z4,z9,z5,z113,z6]),(0,[z1,z2,z3,z4,z81,z34,z6]),(0,[z1,z2,z3,z4,z30,z61,z6]),(0,[z1,z267,z2,z3,z4,z5,z6])],[(0,[z1,z268,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z26,z3,z4,z5,z6]),(0,[z271,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z100,z3,z4,z5,z6]),(0,[z1,z46,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z111,z4,z6])],[(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z105,z6]),(0,[z1,z11,z2,z3,z4,z6,z40]),(0,[z149,z1,z2,z3,z4,z5,z273]),(0,[z75,z1,z2,z3,z81,z5,z6]),(0,[z1,z2,z274,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z34,z6]),(0,[z1,z2,z173,z3,z4,z5,z6])]],
   [[(0,[z50,z1,z11,z2,z3,z4,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z276,z3,z4,z5,z6]),(0,[z114,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z145]),(0,[z277,z1,z2,z3,z4,z34,z6])],[(0,[z1,z2,z3,z278,z4,z5,z6]),(0,[z1,z3,z76,z4,z81,z5,z6]),(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z8,z4,z6]),(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z123]),(0,[z96,z1,z2,z3,z111,z5,z6]),(0,[z1,z2,z3,z282,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z283,z6]),(0,[z1,z216,z2,z3,z4,z5,z6]),(1,[z43,z1,z2,z78,z4,z6]),(0,[z1,z284,z2,z3,z4,z30,z6]),(0,[z1,z32,z285,z2,z3,z4,z6])],[(0,[z72,z1,z11,z2,z3,z4,z6]),(0,[z50,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z40,z125]),(0,[z1,z2,z3,z4,z286,z5,z6]),(0,[z1,z2,z3,z4,z34,z6,z25])],[(0,[z1,z2,z287,z3,z4,z5,z6]),(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z155,z3,z4,z6]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z1,z46,z2,z3,z5,z6,z125])],[(0,[z1,z289,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z291,z6]),(0,[z1,z2,z3,z4,z292,z5,z6]),(0,[z1,z2,z4,z5,z123,z6,z117]),(0,[z1,z2,z3,z4,z4,z30,z6]),(1,[z1,z2,z3,z4,z293,z6])],[(0,[z72,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z6,z294]),(0,[z1,z2,z295,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z296,z6]),(1,[z297,z2,z3,z4,z5,z6])],[(0,[z165,z72,z2,z3,z4,z5,z6]),(0,[z298,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z1,z32,z2,z3,z208,z4,z6]),(0,[z1,z2,z3,z4,z5,z61,z6]),(0,[z1,z2,z3,z4,z5,z300,z6]),(0,[z1,z2,z3,z4,z153,z6,z117]),(0,[z1,z2,z3,z4,z5,z301,z6])]],
   [[(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z303,z6]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z304,z3,z4,z5,z6]),(0,[z305,z1,z2,z3,z4,z5,z6])],[(0,[z72,z1,z71,z3,z4,z5,z6]),(0,[z306,z1,z2,z3,z4,z5,z6]),(0,[z101,z1,z32,z2,z3,z4,z6]),(0,[z149,z129,z1,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z236,z34,z6]),(0,[z1,z2,z3,z4,z30,z121,z6]),(0,[z1,z168,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z307]),(0,[z1,z2,z3,z4,z34,z6,z6])],[(1,[z1,z2,z3,z4,z308,z6]),(0,[z31,z72,z2,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z143,z6]),(0,[z309,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z57,z6]),(0,[z1,z2,z3,z310,z4,z5,z6]),(0,[z311,z1,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z123,z6]),(0,[z1,z2,z3,z4,z5,z6,z263]),(0,[z1,z2,z3,z4,z5,z6,z125]),(0,[z1,z2,z3,z312,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z313,z6]),(0,[z85,z1,z2,z52,z4,z5,z6]),(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z20,z1,z74,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z5,z97,z6]),(0,[z1,z2,z314,z3,z4,z5,z6]),(0,[z1,z315,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z316,z5,z6]),(1,[z20,z1,z2,z3,z30,z6]),(0,[z187,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z317,z3,z4,z5,z6]),(0,[z85,z1,z2,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z318,z5,z6]),(0,[z1,z2,z3,z4,z319,z34,z6]),(0,[z17,z1,z2,z3,z4,z34,z6])],[(0,[z1,z2,z320,z3,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z323,z4,z5,z6]),(0,[z1,z130,z2,z3,z4,z30,z6])],[(0,[z1,z11,z2,z3,z39,z4,z6]),(0,[z1,z32,z2,z3,z4,z113,z6]),(0,[z324,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z325,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z122,z6]),(0,[z1,z2,z3,z326,z4,z5,z6]),(0,[z1,z2,z179,z3,z4,z30,z6]),(0,[z1,z2,z327,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z328,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z122,z125]),(0,[z1,z60,z3,z4,z5,z61,z6]),(0,[z1,z11,z2,z3,z55,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6,z329]),(0,[z1,z2,z330,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z331,z5,z6]),(1,[z150,z2,z3,z4,z5,z6]),(0,[z332,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z333,z6]),(0,[z1,z2,z3,z4,z5,z334,z6]),(0,[z1,z2,z3,z4,z5,z6,z335]),(0,[z1,z2,z3,z4,z5,z336,z6]),(1,[z1,z2,z4,z5,z6,z337]),(0,[z1,z2,z78,z3,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z338,z6]),(0,[z1,z32,z2,z3,z339,z4,z6]),(0,[z1,z2,z3,z340,z4,z5,z6])],[(0,[z1,z2,z3,z341,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z342,z6]),(0,[z1,z2,z343,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z113,z6]),(0,[z1,z2,z344,z3,z4,z5,z6]),(0,[z118,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z345,z4,z5,z6]),(0,[z1,z346,z2,z3,z4,z5,z6]),(0,[z1,z3,z8,z4,z5,z93,z6]),(0,[z1,z2,z3,z4,z5,z6,z347]),(0,[z348,z1,z11,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z349,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z67,z1,z2,z3,z4,z34,z6]),(0,[z1,z154,z2,z3,z4,z30,z6]),(0,[z1,z12,z2,z3,z351,z4,z6]),(0,[z1,z2,z179,z3,z4,z212,z6])],[(0,[z1,z2,z3,z4,z352,z5,z6]),(0,[z1,z32,z2,z35,z3,z4,z6]),(0,[z1,z2,z3,z353,z4,z30,z6]),(1,[z1,z11,z2,z3,z4,z34])],[(0,[z1,z2,z3,z4,z5,z6,z354]),(0,[z1,z2,z355,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z226]),(0,[z1,z2,z3,z4,z5,z6,z356])]],
   [[(1,[z72,z188,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z357,z6]),(0,[z149,z1,z2,z3,z4,z30,z6]),(0,[z1,z32,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z34,z6,z358])],[(0,[z1,z2,z359,z3,z4,z5,z6]),(0,[z2,z3,z39,z4,z105,z5,z6]),(0,[z196,z101,z2,z3,z4,z5,z6]),(0,[z129,z1,z155,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z93,z6]),(0,[z1,z2,z3,z360,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z123,z6]),(0,[z1,z2,z3,z361,z4,z5,z6]),(0,[z1,z2,z362,z3,z4,z5,z6]),(0,[z1,z2,z3,z363,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z364,z6])],[(0,[z75,z1,z71,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z122,z6,z40]),(0,[z1,z11,z2,z3,z4,z236,z6]),(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z1,z2,z3,z4,z30,z6,z181]),(0,[z1,z315,z2,z3,z111,z4,z6])],[(0,[z1,z365,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z366,z4,z5,z6]),(0,[z114,z1,z32,z2,z3,z4,z6])],[(0,[z20,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z106,z6]),(0,[z1,z2,z3,z4,z367,z5,z6]),(0,[z1,z2,z3,z368,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z61,z117]),(0,[z1,z2,z179,z4,z236,z5,z6]),(0,[z369,z1,z2,z3,z4,z30,z6]),(1,[z114,z1,z2,z3,z4,z6])],[(0,[z50,z1,z2,z3,z4,z370,z6]),(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z240,z1,z2,z3,z4,z5,z6])],[(0,[z72,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z52,z3,z4,z34,z6]),(1,[z1,z2,z3,z4,z220,z6]),(0,[z67,z1,z2,z3,z4,z88,z6]),(0,[z1,z372,z2,z3,z4,z5,z6]),(0,[z1,z2,z373,z3,z4,z5,z6]),(1,[z290,z1,z2,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z6,z25])],[(0,[z50,z1,z2,z52,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z20,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z9,z30,z6]),(0,[z1,z2,z179,z35,z3,z5,z6]),(0,[z1,z2,z186,z3,z4,z30,z6]),(0,[z375,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z339,z4,z5,z6]),(0,[z1,z46,z2,z3,z111,z5,z6]),(0,[z1,z2,z3,z111,z4,z34,z6])]],
   [[(0,[z2,z71,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z376,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z377]),(0,[z1,z32,z154,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z378,z6]),(0,[z1,z2,z3,z111,z4,z5,z97])],[(0,[z1,z155,z3,z208,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z379,z6]),(0,[z1,z2,z3,z4,z5,z6,z380])],[(0,[z1,z381,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z123,z61]),(0,[z85,z1,z2,z35,z4,z5,z6]),(1,[z1,z2,z3,z180,z4,z6]),(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z1,z383,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z55,z4,z34,z6])],[(1,[z1,z2,z3,z4,z384,z6]),(0,[z1,z385,z2,z3,z4,z5,z6]),(0,[z1,z11,z107,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z30,z6,z25])],[(0,[z1,z32,z2,z3,z76,z4,z6]),(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z387,z2,z3,z4,z5,z6])],[(0,[z31,z1,z2,z51,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z30,z6]),(0,[z67,z1,z2,z3,z4,z215,z6]),(0,[z388,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z76,z4,z34,z6]),(0,[z1,z389,z2,z3,z4,z5,z6])],[(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z75,z1,z12,z3,z4,z5,z6]),(0,[z1,z32,z60,z2,z3,z4,z6]),(0,[z1,z2,z35,z3,z4,z120,z6]),(0,[z1,z2,z3,z4,z5,z30,z6])]],
   [[(0,[z1,z2,z390,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z391]),(0,[z1,z2,z3,z4,z5,z6,z392]),(0,[z149,z1,z3,z208,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z393,z6]),(0,[z1,z2,z3,z4,z5,z6,z337]),(0,[z1,z2,z3,z394,z4,z5,z6]),(0,[z395,z1,z11,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z160,z6]),(1,[z1,z2,z3,z4,z34,z6])],[(0,[z20,z1,z2,z3,z4,z396,z6]),(0,[z129,z1,z32,z2,z3,z4,z6]),(0,[z1,z60,z2,z3,z4,z291,z6]),(0,[z1,z2,z3,z4,z5,z6,z397])],[(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z384,z5,z6]),(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z122,z6]),(0,[z395,z1,z2,z3,z4,z5,z6]),(1,[z1,z60,z3,z4,z5,z61]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z34,z6])],[(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z402,z5,z6])],[(0,[z1,z2,z3,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z403]),(0,[z85,z1,z2,z179,z3,z5,z6])],[(1,[z1,z2,z21,z4,z5,z6]),(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z405,z5,z6]),(0,[z1,z2,z179,z3,z76,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z25]),(0,[z1,z2,z406,z3,z4,z5,z6])],[(0,[z1,z2,z407,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z408,z6]),(0,[z1,z2,z3,z4,z30,z122,z6]),(0,[z1,z409,z2,z3,z4,z5,z6]),(0,[z75,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z410,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z411,z6]),(0,[z1,z285,z2,z3,z4,z5,z6]),(0,[z1,z412,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z413,z3,z4,z5,z6]),(0,[z414,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z155,z3,z4,z5,z6]),(0,[z149,z1,z32,z2,z3,z4,z6]),(0,[z415,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z416,z4,z5,z6]),(0,[z1,z32,z32,z2,z3,z4,z6])],[(0,[z417,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z396,z6]),(0,[z1,z2,z3,z418,z4,z5,z6]),(0,[z101,z1,z11,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z88,z6]),(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6])],[(0,[z421,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z422,z4,z5,z6]),(0,[z423,z1,z2,z3,z4,z5,z6]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z5,z34])],[(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z0,z1,z2,z3,z4,z30,z6]),(0,[z96,z1,z2,z3,z4,z34,z6])],[(0,[z165,z1,z2,z3,z4,z34,z6]),(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z5,z294]),(0,[z147,z1,z2,z3,z4,z34,z6]),(0,[z426,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z97,z6]),(0,[z1,z2,z3,z4,z34,z6,z427])],[(0,[z1,z2,z3,z4,z105,z30,z6]),(0,[z1,z107,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z428,z6]),(0,[z297,z2,z3,z4,z5,z6,z125])],[(1,[z1,z54,z2,z3,z5,z6]),(0,[z147,z1,z2,z3,z8,z4,z6]),(0,[z429,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z430]),(0,[z1,z2,z3,z4,z5,z97,z40]),(1,[z1,z2,z3,z4,z5,z273]),(0,[z431,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z432,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z215,z6]),(0,[z1,z2,z3,z208,z4,z5,z6]),(0,[z1,z433,z2,z3,z4,z5,z6]),(0,[z1,z2,z227,z186,z3,z4,z6]),(1,[z1,z32,z2,z3,z30,z6])],[(0,[z1,z2,z3,z4,z5,z122,z6]),(0,[z1,z2,z3,z4,z5,z434,z6])],[(0,[z435,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z436,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z32,z2,z3,z5,z30,z6]),(1,[z1,z2,z3,z4,z64,z6])],[(0,[z1,z32,z188,z2,z3,z4,z6]),(0,[z89,z1,z2,z3,z105,z5,z6]),(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z99,z1,z3,z4,z5,z6,z117]),(0,[z438,z1,z2,z3,z4,z5,z6])],[(0,[z89,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z1,z2,z78,z3,z4,z93,z6]),(0,[z1,z2,z3,z440,z4,z5,z6])],[(0,[z33,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z441,z4,z5,z6]),(1,[z1,z2,z24,z3,z4,z6]),(0,[z1,z2,z35,z3,z4,z34,z6])],[(0,[z1,z2,z442,z3,z4,z5,z6]),(0,[z1,z2,z3,z443,z4,z5,z6]),(0,[z1,z2,z444,z3,z4,z5,z6]),(0,[z1,z445,z2,z3,z4,z5,z6])],[(0,[z31,z2,z52,z3,z4,z5,z6]),(0,[z1,z2,z3,z446,z4,z5,z6])]],
   [[(0,[z20,z1,z46,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z447]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z449,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z300,z6]),(0,[z1,z450,z2,z3,z4,z5,z6])],[(0,[z165,z1,z188,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z370,z6]),(0,[z1,z11,z2,z3,z51,z4,z6]),(0,[z20,z1,z2,z3,z5,z30,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z452,z4,z5,z6]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z2,z3,z4,z319,z97,z6])],[(0,[z1,z32,z2,z52,z3,z4,z6]),(0,[z1,z2,z3,z76,z236,z5,z6]),(0,[z454,z1,z2,z3,z4,z5,z6]),(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z160,z6]),(0,[z1,z11,z2,z3,z160,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z358])],[(0,[z1,z2,z456,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z34,z6]),(0,[z1,z32,z2,z179,z3,z4,z6]),(0,[z1,z2,z3,z457,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z6,z125]),(0,[z1,z11,z2,z3,z4,z6,z145])],[(1,[z33,z2,z3,z4,z5,z40]),(0,[z1,z284,z2,z3,z4,z5,z6])],[(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z458,z6]),(0,[z1,z2,z3,z4,z220,z5,z6]),(0,[z149,z1,z2,z3,z4,z459,z6]),(0,[z1,z2,z3,z81,z236,z5,z6]),(0,[z1,z2,z460,z3,z4,z5,z6]),(0,[z1,z2,z227,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z461,z6,z125])],[(0,[z1,z2,z52,z3,z4,z30,z6]),(0,[z149,z1,z2,z3,z4,z336,z6]),(0,[z1,z2,z3,z351,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z226,z117]),(0,[z1,z462,z11,z2,z3,z4,z6])],[(0,[z1,z2,z3,z463,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z290,z1,z2,z4,z5,z6,z25])]],
   [[(0,[z72,z1,z2,z3,z4,z5,z6]),(0,[z1,z462,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z117]),(0,[z1,z32,z2,z3,z4,z4,z6]),(0,[z1,z251,z2,z3,z4,z34,z6])],[(0,[z196,z1,z2,z3,z4,z34,z6]),(0,[z1,z54,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z1,z2,z3,z4,z5,z465,z6]),(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z467,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z319,z6])],[(0,[z1,z11,z2,z3,z4,z61,z6]),(0,[z1,z2,z3,z4,z5,z6,z468]),(1,[z1,z2,z3,z111,z5,z97])],[(0,[z1,z2,z469,z3,z4,z5,z6]),(0,[z67,z1,z2,z3,z4,z5,z40]),(0,[z1,z2,z3,z470,z4,z5,z6])],[(0,[z1,z11,z2,z71,z3,z4,z6]),(1,[z1,z2,z3,z53,z5,z6]),(0,[z1,z2,z3,z471,z4,z5,z6]),(0,[z1,z2,z186,z4,z5,z123,z6]),(0,[z1,z2,z3,z4,z77,z34,z6])],[(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z473,z4,z5,z6]),(0,[z129,z1,z2,z3,z4,z5,z25]),(0,[z1,z32,z2,z44,z3,z4,z6]),(1,[z1,z2,z3,z4,z6,z182])],[(0,[z188,z2,z71,z3,z4,z5,z6]),(0,[z1,z188,z2,z3,z4,z30,z6]),(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z4,z93,z6]),(0,[z1,z2,z3,z4,z5,z6,z475])],[(0,[z1,z2,z3,z4,z5,z6,z476]),(0,[z1,z2,z3,z4,z5,z477,z6]),(0,[z1,z130,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z478,z5,z6]),(0,[z1,z2,z3,z479,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z480,z6])],[(0,[z1,z11,z2,z3,z4,z105,z6]),(0,[z1,z2,z3,z481,z4,z5,z6]),(0,[z129,z1,z11,z2,z3,z4,z6]),(0,[z1,z482,z2,z3,z4,z5,z6]),(0,[z1,z2,z179,z3,z4,z5,z6]),(0,[z1,z46,z2,z3,z4,z34,z6])],[(1,[z89,z2,z3,z39,z5,z6]),(0,[z1,z483,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z103,z6]),(0,[z1,z2,z3,z4,z30,z123,z6]),(0,[z1,z32,z2,z3,z108,z4,z6]),(0,[z1,z46,z2,z3,z4,z5,z97]),(0,[z484,z1,z2,z3,z4,z5,z6])],[(0,[z1,z71,z3,z4,z81,z5,z6]),(0,[z1,z12,z2,z3,z81,z5,z6]),(0,[z1,z2,z485,z3,z4,z5,z6]),(0,[z486,z1,z2,z3,z4,z5,z6]),(0,[z29,z1,z2,z3,z4,z5,z117]),(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z480,z34,z6])],[(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z489,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z490]),(0,[z129,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z6,z491]),(0,[z1,z492,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z34,z6]),(0,[z1,z2,z3,z282,z4,z34,z6])],[(0,[z1,z2,z3,z55,z4,z5,z34])],[(0,[z1,z32,z2,z3,z4,z81,z6]),(1,[z1,z2,z3,z4,z212,z6])],[(0,[z1,z154,z2,z3,z4,z5,z6]),(0,[z75,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z3,z8,z4,z103,z6]),(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z495,z6])]],
   [[(0,[z149,z1,z11,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z411,z6]),(0,[z1,z2,z3,z108,z5,z30,z6]),(0,[z1,z2,z3,z353,z4,z5,z6]),(0,[z1,z32,z11,z2,z3,z4,z6]),(0,[z1,z2,z496,z3,z4,z5,z6])],[(0,[z165,z1,z2,z3,z4,z308,z6]),(0,[z1,z2,z3,z4,z5,z497,z6]),(0,[z348,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z208,z4,z6]),(0,[z1,z2,z3,z498,z4,z5,z6]),(0,[z1,z2,z3,z499,z4,z5,z6]),(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z5,z103,z6]),(0,[z1,z2,z3,z4,z5,z6,z501]),(0,[z1,z246,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z258]),(0,[z1,z502,z11,z2,z3,z4,z6]),(0,[z1,z2,z3,z55,z4,z5,z145])],[(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z3,z4,z30,z6]),(0,[z1,z32,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z108,z30,z6]),(0,[z1,z2,z3,z111,z4,z378,z6])],[(1,[z298,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z504,z6]),(0,[z1,z502,z2,z3,z4,z5,z6]),(0,[z1,z2,z505,z3,z4,z30,z6]),(0,[z1,z506,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z507,z4,z5,z6]),(1,[z1,z2,z3,z508,z4,z6]),(0,[z1,z11,z2,z3,z4,z123,z6])],[(0,[z1,z2,z3,z4,z214,z5,z6]),(0,[z1,z107,z3,z4,z5,z93,z6]),(0,[z1,z2,z3,z5,z97,z6,z125]),(1,[z1,z11,z2,z3,z4,z145]),(0,[z309,z1,z2,z3,z4,z34,z6])],[(0,[z1,z2,z3,z4,z5,z509,z6]),(0,[z89,z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z5,z510,z6]),(0,[z369,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z427])],[(0,[z149,z29,z1,z2,z4,z5,z6]),(0,[z511,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z512])]],
   [[(0,[z1,z11,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z4,z30,z30,z6]),(0,[z1,z32,z2,z274,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z513,z6]),(0,[z20,z1,z2,z3,z4,z5,z6]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z6,z117])],[(0,[z1,z2,z3,z515,z4,z5,z6]),(0,[z1,z11,z516,z2,z3,z4,z6]),(0,[z517,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z518,z4,z5,z6]),(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z183,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z520,z5,z6]),(0,[z1,z2,z3,z4,z5,z521,z6]),(0,[z1,z2,z3,z4,z5,z120,z6])],[(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z298,z1,z2,z3,z9,z5,z6]),(0,[z1,z2,z523,z3,z4,z5,z6]),(0,[z524,z1,z2,z3,z4,z5,z6])],[(0,[z33,z1,z11,z2,z3,z4,z6]),(0,[z1,z525,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z337,z25]),(0,[z1,z2,z78,z3,z4,z34,z6])],[(0,[z1,z2,z3,z526,z4,z5,z6]),(0,[z1,z32,z12,z2,z3,z4,z6]),(0,[z29,z1,z2,z186,z4,z5,z6])],[(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z527]),(1,[z216,z2,z3,z4,z5,z6]),(0,[z1,z2,z78,z3,z8,z4,z6]),(2,[z1,z2,z3,z160,z6])]],
   [[(0,[z528,z1,z2,z3,z4,z5,z6]),(0,[z72,z188,z2,z3,z4,z5,z6]),(0,[z20,z2,z3,z4,z105,z5,z6]),(0,[z1,z2,z3,z4,z81,z30,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z1,z11,z2,z35,z3,z4,z6]),(0,[z1,z529,z2,z3,z4,z5,z6]),(1,[z1,z32,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z530,z2,z3,z4,z5,z6]),(0,[z531,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z61,z6,z25]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z2,z533,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z111,z4,z6])],[(0,[z1,z2,z3,z39,z4,z34,z6]),(1,[z196,z2,z3,z4,z9,z6]),(0,[z1,z2,z534,z3,z4,z5,z6]),(0,[z1,z2,z78,z4,z5,z103,z6]),(0,[z43,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z535,z6]),(0,[z1,z11,z2,z3,z4,z30,z6]),(0,[z1,z32,z46,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z461,z6])],[(0,[z1,z2,z3,z536,z4,z5,z6]),(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z271,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z2,z3,z539,z4,z5,z6]),(0,[z1,z540,z11,z2,z3,z4,z6]),(1,[z1,z2,z3,z160,z5,z6])],[(0,[z1,z541,z2,z3,z4,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z543]),(0,[z1,z2,z3,z4,z5,z544,z6]),(0,[z1,z2,z3,z508,z4,z5,z6])],[(0,[z545,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z9,z6]),(0,[z1,z2,z547,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z6])],[(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z548]),(0,[z147,z1,z3,z8,z4,z5,z6])],[(0,[z1,z2,z3,z549,z4,z5,z6]),(0,[z89,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z1,z2,z3,z551,z4,z5,z6])]],
   [[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z552,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z553,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z6,z25]),(0,[z1,z2,z3,z4,z34,z495,z6])],[(0,[z1,z483,z2,z3,z39,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z554]),(0,[z1,z46,z2,z3,z4,z293,z6])],[(0,[z165,z1,z2,z3,z4,z384,z6]),(0,[z555,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z51,z4,z5,z6]),(0,[z1,z11,z154,z2,z3,z4,z6]),(0,[z1,z556,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z557,z6]),(0,[z558,z1,z2,z3,z4,z30,z6])],[(0,[z1,z2,z3,z4,z357,z6,z40]),(0,[z96,z1,z32,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z301,z6]),(0,[z559,z1,z2,z3,z4,z5,z6])],[(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z561]),(0,[z1,z60,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z236,z30,z6]),(0,[z1,z562,z2,z3,z4,z5,z6]),(0,[z17,z1,z11,z2,z3,z4,z6])],[(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z564,z3,z4,z5,z6]),(0,[z167,z1,z2,z3,z4,z34,z6])],[(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z76,z4,z6]),(0,[z1,z2,z3,z565,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z117]),(0,[z1,z2,z3,z111,z5,z97,z6])],[(0,[z1,z2,z3,z566,z4,z5,z6]),(0,[z1,z2,z3,z4,z105,z5,z6]),(1,[z1,z2,z244,z3,z4,z6]),(0,[z1,z107,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z567,z6]),(0,[z1,z32,z2,z3,z4,z103,z6]),(0,[z1,z2,z3,z568,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z30,z6])]],
   [[(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z570,z4,z5,z6]),(0,[z1,z2,z571,z3,z4,z5,z6]),(0,[z33,z67,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z3,z76,z5,z6]),(0,[z1,z2,z3,z4,z572,z5,z6]),(0,[z1,z2,z3,z108,z4,z5,z6]),(0,[z1,z573,z11,z2,z3,z4,z6]),(0,[z388,z1,z2,z3,z4,z34,z6])],[(0,[z20,z1,z86,z3,z4,z5,z6]),(0,[z1,z11,z60,z2,z3,z4,z6]),(0,[z574,z1,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z78,z3,z4,z6]),(0,[z1,z2,z3,z575,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z5,z145])],[(0,[z31,z1,z2,z3,z4,z34,z6]),(0,[z1,z573,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z576,z4,z5,z6]),(0,[z577,z1,z2,z3,z4,z5,z6])],[(0,[z20,z1,z2,z3,z4,z5,z166]),(0,[z1,z578,z2,z3,z4,z5,z6]),(0,[z1,z579,z2,z3,z4,z5,z6]),(0,[z1,z2,z244,z3,z76,z4,z6]),(0,[z1,z2,z3,z580,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z258])],[(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z122,z6]),(0,[z1,z2,z44,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z30,z103,z6]),(0,[z1,z32,z2,z3,z4,z6,z117]),(0,[z1,z11,z2,z16,z3,z4,z6]),(1,[z1,z2,z3,z340,z5,z6]),(1,[z1,z2,z3,z55,z4,z34]),(0,[z1,z2,z3,z4,z522,z34,z6])],[(0,[z1,z2,z3,z4,z113,z103,z6]),(1,[z1,z2,z3,z4,z459,z6]),(0,[z149,z1,z2,z3,z4,z5,z229]),(0,[z1,z582,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z583])],[(0,[z1,z2,z3,z4,z9,z103,z6]),(1,[z1,z2,z3,z4,z336,z6]),(0,[z1,z2,z3,z584,z4,z5,z6]),(0,[z1,z2,z3,z69,z4,z30,z6]),(1,[z1,z11,z2,z3,z340,z6])],[(0,[z1,z2,z3,z51,z4,z34,z6]),(1,[z1,z74,z3,z4,z5,z6]),(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z254,z4,z5,z6]),(0,[z586,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z67,z1,z2,z3,z4,z30,z6]),(0,[z1,z60,z2,z3,z508,z4,z6])],[(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z6,z117])],[(0,[z588,z1,z2,z3,z4,z5,z6]),(0,[z589,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z319,z6])],[(0,[z1,z2,z78,z3,z4,z113,z6]),(0,[z1,z2,z155,z3,z4,z34,z6])],[(0,[z1,z590,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z357,z6]),(0,[z591,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z34,z6]),(0,[z1,z11,z2,z3,z340,z4,z6]),(0,[z592,z1,z2,z3,z4,z5,z6])],[(0,[z593,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z594,z4,z5,z6]),(0,[z1,z2,z595,z3,z4,z5,z6]),(0,[z1,z2,z596,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z597,z5,z6]),(0,[z1,z154,z2,z4,z5,z123,z6]),(0,[z1,z2,z598,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z236,z6]),(0,[z599,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z600,z6]),(0,[z1,z2,z3,z4,z601,z5,z6]),(0,[z1,z602,z2,z3,z4,z5,z6]),(0,[z96,z1,z32,z2,z3,z5,z6])],[(0,[z50,z1,z2,z51,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z103,z6]),(1,[z1,z2,z3,z4,z338,z6]),(0,[z1,z2,z603,z3,z4,z5,z6])],[(0,[z1,z2,z3,z604,z4,z5,z6]),(0,[z605,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z606,z4,z5,z6])]],
   [[(0,[z1,z2,z607,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z608]),(0,[z1,z2,z52,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z106,z6]),(1,[z1,z483,z2,z3,z4,z6]),(0,[z149,z1,z2,z3,z68,z5,z6]),(0,[z149,z1,z2,z4,z5,z123,z6]),(0,[z1,z2,z3,z4,z5,z6,z609]),(0,[z1,z2,z3,z4,z93,z34,z6])],[(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z20,z1,z2,z266,z4,z5,z6]),(0,[z196,z1,z32,z2,z3,z4,z6]),(0,[z33,z1,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z411,z6,z25])],[(0,[z1,z611,z2,z3,z4,z5,z6]),(0,[z20,z33,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z612]),(0,[z1,z2,z3,z111,z4,z30,z6]),(0,[z1,z2,z3,z613,z4,z5,z6])],[(0,[z614,z1,z2,z3,z4,z5,z6]),(0,[z67,z2,z3,z4,z5,z122,z6]),(0,[z1,z2,z3,z208,z4,z34,z6]),(0,[z1,z2,z615,z3,z4,z5,z6]),(0,[z1,z2,z616,z3,z4,z5,z6]),(0,[z617,z1,z2,z3,z4,z5,z6]),(1,[z1,z46,z2,z3,z5,z125])],[(0,[z375,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z254,z4,z6])],[(0,[z1,z188,z3,z4,z81,z5,z6]),(0,[z1,z11,z188,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z618,z6]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z34,z6]),(0,[z1,z2,z3,z55,z4,z30,z6])],[(0,[z1,z2,z3,z9,z53,z5,z6]),(0,[z1,z2,z3,z4,z620,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z621])],[(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z17,z1,z32,z2,z3,z4,z6])]],
   [[(0,[z1,z188,z2,z3,z4,z5,z6]),(0,[z1,z2,z78,z3,z4,z9,z6]),(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z625]),(0,[z1,z32,z2,z186,z3,z4,z6]),(0,[z1,z11,z2,z3,z4,z6,z125]),(0,[z139,z1,z11,z2,z3,z4,z6]),(1,[z1,z11,z2,z3,z4,z6])],[(0,[z20,z1,z2,z3,z105,z5,z6]),(0,[z1,z2,z3,z626,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z627,z6]),(0,[z1,z2,z3,z4,z628,z5,z6]),(1,[z1,z2,z3,z4,z126,z6]),(0,[z1,z2,z3,z76,z4,z30,z6]),(0,[z29,z1,z2,z3,z4,z34,z6])],[(0,[z20,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z39,z4,z30,z6]),(0,[z1,z2,z3,z4,z34,z6,z40]),(0,[z1,z2,z3,z4,z5,z109,z6]),(0,[z1,z2,z3,z4,z5,z6,z629]),(0,[z43,z1,z11,z2,z3,z4,z6]),(0,[z1,z2,z3,z223,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z34,z6])],[(0,[z1,z2,z3,z4,z630,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z93,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z301,z6,z125])],[(0,[z1,z11,z2,z52,z3,z4,z6]),(0,[z1,z2,z3,z4,z633,z5,z6]),(1,[z1,z2,z3,z4,z393,z6]),(0,[z1,z2,z362,z3,z4,z30,z6]),(0,[z1,z2,z199,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z634]),(0,[z1,z635,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z273]),(0,[z1,z11,z2,z179,z3,z4,z6]),(0,[z43,z1,z2,z3,z4,z30,z6])],[(0,[z1,z2,z52,z4,z236,z5,z6]),(0,[z1,z2,z3,z4,z459,z5,z6]),(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z129,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z340,z5,z6])],[(1,[z1,z315,z2,z3,z4,z6])]],
   [[(0,[z50,z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z637,z3,z4,z5,z6]),(0,[z67,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z638,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z639]),(0,[z1,z2,z3,z640,z4,z5,z6])],[(0,[z1,z2,z3,z4,z641,z5,z6]),(0,[z1,z2,z3,z4,z5,z291,z6]),(0,[z1,z2,z3,z568,z4,z6,z117]),(0,[z1,z2,z3,z4,z5,z293,z6]),(0,[z1,z2,z3,z4,z5,z6,z642])],[(1,[z1,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z4,z5,z643,z6]),(0,[z644,z1,z2,z3,z4,z5,z6])],[(0,[z72,z1,z2,z3,z4,z34,z6]),(0,[z1,z645,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z646,z4,z5,z6]),(0,[z29,z1,z2,z3,z4,z5,z123]),(0,[z29,z1,z2,z4,z5,z6,z117]),(0,[z96,z1,z11,z2,z3,z4,z6]),(0,[z297,z1,z2,z3,z4,z5,z6])],[(0,[z647,z1,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z35,z3,z236,z5,z6])],[(1,[z1,z2,z3,z4,z396,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z186,z4,z5,z123]),(0,[z1,z2,z505,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z308,z6]),(0,[z89,z1,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z649]),(0,[z96,z1,z2,z3,z4,z30,z6])],[(0,[z165,z1,z2,z3,z4,z30,z6]),(0,[z147,z1,z2,z3,z4,z30,z6]),(0,[z129,z1,z2,z3,z4,z5,z61]),(0,[z1,z11,z2,z44,z3,z4,z6]),(0,[z1,z2,z650,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z651,z5,z6]),(0,[z1,z2,z3,z652,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z653]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z655,z5,z6]),(0,[z85,z1,z2,z3,z236,z5,z6]),(0,[z1,z656,z2,z3,z4,z5,z6]),(0,[z99,z1,z2,z3,z4,z5,z6]),(0,[z657,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z658,z4,z5,z6]),(0,[z1,z154,z2,z155,z4,z5,z6]),(0,[z1,z107,z2,z3,z4,z93,z6])],[(0,[z165,z1,z71,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z30,z6]),(0,[z659,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z660,z4,z5,z6]),(1,[z50,z2,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z661]),(0,[z96,z1,z2,z3,z5,z6,z125]),(0,[z1,z2,z3,z111,z4,z5,z125])],[(0,[z1,z2,z3,z662,z4,z5,z6]),(0,[z1,z2,z266,z3,z4,z5,z6]),(0,[z1,z2,z3,z663,z4,z5,z6]),(0,[z1,z154,z2,z208,z4,z5,z6]),(0,[z664,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z179,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z665,z5,z6]),(0,[z1,z11,z2,z3,z108,z4,z6]),(0,[z1,z2,z3,z4,z461,z5,z6])],[(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z667,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z1,z669,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z670])],[(0,[z1,z2,z3,z4,z5,z6,z671]),(0,[z1,z2,z3,z672,z4,z5,z6])],[(0,[z1,z673,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z108,z5,z6])]],
   [[(0,[z674,z1,z2,z3,z4,z5,z6]),(0,[z72,z1,z188,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z294]),(0,[z1,z11,z2,z3,z4,z81,z6]),(0,[z1,z2,z35,z3,z4,z30,z6]),(0,[z210,z1,z2,z3,z4,z30,z6])],[(0,[z1,z675,z2,z3,z4,z5,z6]),(0,[z1,z676,z2,z3,z4,z5,z6])],[(1,[z165,z71,z3,z4,z5,z6]),(0,[z196,z1,z2,z3,z4,z113,z6]),(0,[z1,z154,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z81,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z677]),(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z679]),(0,[z1,z2,z3,z4,z680,z5,z6]),(0,[z681,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z11,z2,z3,z4,z6])],[(0,[z1,z2,z3,z682,z4,z5,z6]),(1,[z1,z2,z3,z568,z4,z6])],[(0,[z1,z32,z2,z3,z51,z4,z6]),(0,[z1,z2,z3,z683,z4,z5,z6]),(1,[z101,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z684,z4,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z6]),(1,[z29,z1,z2,z4,z5,z117]),(0,[z1,z2,z3,z111,z5,z30,z6]),(0,[z1,z11,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z687,z5,z6]),(1,[z1,z2,z3,z4,z370,z6]),(0,[z20,z89,z2,z3,z4,z5,z6]),(1,[z89,z1,z2,z3,z30,z6]),(0,[z1,z32,z2,z3,z4,z6,z40]),(0,[z1,z155,z3,z4,z5,z61,z6]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6]),(0,[z1,z2,z3,z4,z690,z5,z6]),(0,[z1,z2,z3,z4,z228,z30,z6]),(0,[z277,z1,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z34,z6])],[(0,[z1,z2,z3,z4,z5,z691,z6]),(0,[z1,z2,z692,z3,z4,z5,z6]),(0,[z1,z2,z693,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z30,z6]),(0,[z1,z11,z450,z2,z3,z4,z6])],[(0,[z694,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z695,z5,z6]),(0,[z1,z12,z2,z3,z4,z393,z6]),(0,[z1,z32,z2,z3,z8,z4,z6])]],
   [[(0,[z696,z1,z2,z3,z4,z5,z6]),(0,[z697,z1,z2,z3,z4,z5,z6]),(0,[z1,z540,z2,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z5,z25]),(0,[z1,z698,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z30,z6,z125])],[(0,[z196,z1,z11,z2,z3,z4,z6]),(0,[z699,z1,z2,z3,z4,z5,z6]),(0,[z700,z1,z2,z3,z4,z5,z6]),(0,[z1,z516,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z701,z5,z6]),(0,[z1,z2,z3,z4,z30,z6,z40]),(0,[z1,z2,z702,z3,z4,z5,z6]),(0,[z1,z32,z2,z155,z3,z4,z6])],[(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z34,z6]),(0,[z33,z2,z3,z4,z5,z6,z40]),(0,[z149,z1,z2,z3,z214,z5,z6]),(0,[z1,z704,z2,z3,z4,z5,z6])],[(0,[z31,z50,z2,z3,z4,z5,z6]),(0,[z1,z2,z51,z4,z236,z5,z6]),(0,[z20,z1,z2,z3,z4,z34,z6]),(0,[z196,z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z9,z34,z6]),(0,[z149,z1,z3,z4,z5,z61,z6]),(0,[z1,z2,z186,z3,z4,z34,z6]),(1,[z1,z2,z3,z111,z30,z6]),(0,[z558,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z378,z6])],[(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z89,z1,z2,z3,z5,z97,z6]),(1,[z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z35,z4,z236,z5,z6]),(0,[z1,z2,z3,z4,z706,z5,z6]),(1,[z1,z2,z3,z4,z319,z6]),(0,[z517,z1,z2,z3,z4,z34,z6])],[(0,[z1,z183,z2,z3,z4,z6,z40]),(0,[z1,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z236,z5,z6])],[(0,[z165,z1,z32,z2,z3,z4,z6]),(0,[z196,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z351,z4,z6]),(0,[z147,z1,z32,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z707,z6]),(0,[z1,z2,z708,z3,z4,z6]),(0,[z1,z2,z3,z4,z126,z6]),(1,[z1,z3,z709,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z297,z1,z2,z3,z30,z6])],[(0,[z72,z188,z3,z4,z30,z6]),(0,[z1,z710,z3,z4,z5,z6]),(0,[z1,z711,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z712]),(0,[z1,z2,z3,z471,z30,z6]),(0,[z1,z3,z4,z153,z6,z226]),(0,[z1,z2,z3,z4,z713,z6])],[(0,[z1,z2,z3,z714,z5,z6]),(0,[z1,z2,z715,z4,z5,z6]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z2,z3,z30,z122,z125]),(0,[z1,z2,z3,z214,z336,z6]),(0,[z149,z1,z4,z5,z123,z61]),(0,[z1,z2,z3,z717,z4,z6]),(0,[z1,z2,z44,z4,z103,z6]),(0,[z139,z1,z2,z3,z160,z6])],[(0,[z1,z425,z2,z3,z30,z6]),(0,[z1,z718,z3,z4,z5,z6]),(0,[z1,z719,z2,z3,z4,z6]),(0,[z149,z1,z208,z4,z459,z6]),(0,[z1,z2,z3,z160,z93,z6]),(0,[z1,z32,z2,z3,z127,z6]),(0,[z1,z2,z3,z4,z5,z720]),(0,[z1,z11,z3,z4,z6,z226]),(0,[z1,z2,z3,z111,z378,z97])],[(0,[z72,z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z722,z6]),(0,[z1,z2,z723,z3,z5,z6]),(0,[z1,z724,z2,z3,z4,z6]),(0,[z1,z2,z3,z30,z6,z335]),(0,[z149,z1,z208,z4,z336,z6]),(0,[z1,z2,z3,z4,z153,z6]),(0,[z96,z1,z725,z2,z3,z6])],[(0,[z1,z2,z71,z3,z160,z6]),(0,[z33,z2,z3,z4,z34,z40]),(0,[z1,z2,z726,z4,z5,z6]),(0,[z1,z315,z2,z3,z4,z6])],[(0,[z20,z1,z86,z3,z30,z6]),(0,[z1,z725,z2,z3,z30,z6]),(0,[z1,z46,z11,z2,z3,z125]),(0,[z1,z2,z3,z5,z727,z6])]],
   [[(0,[z1,z74,z3,z4,z5,z166]),(0,[z1,z2,z728,z3,z4,z6]),(0,[z1,z2,z4,z5,z6,z729]),(0,[z290,z1,z2,z4,z30,z6]),(0,[z297,z32,z2,z3,z4,z6])],[(0,[z2,z3,z39,z730,z5,z6]),(0,[z2,z3,z4,z5,z731,z40]),(0,[z67,z1,z2,z3,z732,z6]),(0,[z1,z733,z3,z4,z5,z6]),(0,[z1,z2,z3,z734,z4,z30]),(0,[z369,z1,z2,z505,z4,z6]),(0,[z1,z11,z2,z3,z735,z6])],[(0,[z165,z32,z71,z3,z4,z6]),(0,[z1,z2,z3,z30,z6,z356]),(0,[z297,z2,z3,z4,z461,z6])],[(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z579,z2,z3,z30,z6]),(0,[z1,z2,z3,z4,z6,z737]),(0,[z1,z32,z675,z2,z3,z6]),(0,[z1,z738,z3,z4,z5,z6]),(0,[z1,z2,z739,z3,z5,z6]),(0,[z1,z168,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z396,z6]),(0,[z20,z74,z3,z105,z5,z6]),(0,[z1,z2,z3,z5,z740,z6]),(0,[z1,z2,z3,z4,z6,z741]),(0,[z1,z2,z186,z4,z5,z123]),(0,[z1,z2,z3,z30,z364,z6]),(0,[z1,z2,z3,z56,z30,z6]),(0,[z1,z2,z3,z111,z34,z97])],[(0,[z20,z89,z2,z3,z30,z6]),(0,[z1,z2,z3,z4,z742,z6]),(0,[z1,z2,z3,z743,z4,z6]),(0,[z1,z3,z4,z5,z6,z744]),(0,[z29,z1,z11,z2,z4,z117]),(0,[z99,z1,z3,z568,z4,z6])],[(0,[z745,z1,z2,z3,z215,z6]),(0,[z1,z3,z4,z5,z61,z195]),(0,[z75,z1,z3,z76,z126,z6]),(0,[z1,z2,z3,z4,z746,z6])],[(0,[z1,z2,z3,z4,z747,z6]),(0,[z1,z2,z3,z4,z748,z6]),(0,[z1,z2,z3,z4,z749,z6]),(0,[z1,z2,z3,z68,z5,z229]),(0,[z75,z1,z3,z76,z5,z6]),(0,[z750,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z751])]],
   [[(0,[z20,z1,z130,z2,z3,z6]),(0,[z20,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z663,z5,z97]),(0,[z290,z1,z2,z4,z411,z6]),(0,[z1,z462,z2,z16,z4,z6])],[(0,[z1,z752,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z89,z1,z2,z3,z106,z6]),(0,[z1,z54,z2,z3,z357,z6]),(0,[z1,z2,z3,z754,z4,z5]),(0,[z1,z2,z3,z4,z755,z6]),(0,[z756,z2,z3,z4,z30,z6])],[(0,[z221,z1,z2,z3,z30,z6]),(0,[z20,z582,z2,z3,z5,z6]),(0,[z129,z1,z3,z4,z5,z273])],[(0,[z1,z2,z3,z4,z5,z757]),(0,[z50,z11,z2,z51,z4,z6]),(0,[z298,z1,z2,z3,z220,z6]),(0,[z150,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z208,z160,z6]),(0,[z1,z32,z12,z3,z81,z6]),(0,[z1,z2,z758,z44,z4,z6]),(0,[z297,z2,z3,z4,z301,z6])],[(0,[z1,z759,z3,z4,z5,z6]),(0,[z89,z2,z3,z39,z34,z6]),(0,[z1,z2,z3,z176,z30,z6]),(0,[z33,z54,z2,z3,z5,z40]),(0,[z1,z2,z3,z4,z760,z6]),(0,[z1,z11,z2,z3,z4,z225]),(0,[z1,z2,z3,z4,z761,z6]),(0,[z1,z60,z3,z4,z30,z61]),(0,[z762,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z763,z6])],[(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z1,z2,z3,z4,z766,z6]),(0,[z767,z2,z3,z4,z5,z6]),(0,[z1,z2,z768,z3,z4,z6]),(0,[z1,z32,z387,z2,z3,z6])],[(0,[z1,z74,z266,z4,z5,z6])],[(0,[z2,z769,z3,z4,z5,z6]),(0,[z149,z216,z208,z4,z5,z6]),(0,[z1,z2,z3,z214,z5,z6]),(0,[z1,z770,z2,z3,z4,z6]),(0,[z1,z3,z771,z4,z5,z6]),(0,[z1,z2,z772,z3,z4,z6]),(0,[z1,z2,z3,z30,z6,z182])]],
   [[(0,[z1,z2,z3,z5,z773,z6]),(0,[z1,z2,z774,z4,z5,z6]),(0,[z75,z1,z3,z566,z5,z6]),(0,[z1,z107,z3,z771,z4,z6]),(0,[z1,z2,z3,z775,z4,z6]),(0,[z1,z2,z3,z4,z776,z6])],[(0,[z1,z2,z3,z777,z5,z6]),(0,[z1,z86,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z1,z11,z2,z3,z4,z166]),(0,[z664,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z4,z779,z273]),(0,[z1,z3,z4,z34,z6,z226]),(0,[z1,z130,z2,z3,z4,z125])],[(0,[z1,z2,z780,z4,z5,z6]),(0,[z1,z2,z3,z4,z781,z6]),(0,[z20,z2,z3,z30,z122,z6]),(0,[z1,z2,z3,z4,z782,z6]),(0,[z1,z2,z3,z4,z783,z6]),(0,[z1,z2,z3,z784,z5,z6]),(0,[z149,z1,z208,z4,z30,z6]),(0,[z1,z2,z785,z3,z4,z6]),(0,[z1,z2,z3,z568,z4,z6])],[(0,[z1,z2,z3,z4,z5,z166]),(0,[z96,z1,z2,z3,z220,z6]),(0,[z1,z786,z2,z3,z4,z6]),(0,[z1,z3,z4,z5,z61,z720]),(0,[z29,z1,z2,z4,z5,z117])],[(0,[z2,z721,z3,z4,z5,z6]),(0,[z1,z787,z2,z3,z4,z6]),(0,[z1,z2,z769,z4,z5,z6]),(0,[z1,z2,z788,z4,z5,z6]),(0,[z20,z33,z2,z3,z30,z6]),(0,[z1,z2,z3,z789,z4,z6]),(0,[z1,z2,z3,z4,z790,z6]),(0,[z1,z2,z3,z30,z6,z397]),(0,[z1,z2,z3,z461,z30,z6]),(0,[z1,z32,z725,z2,z3,z6]),(0,[z1,z516,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z791,z6]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z2,z793,z3,z4,z6]),(0,[z150,z2,z3,z4,z5,z229]),(0,[z1,z11,z2,z794,z4,z6])],[(0,[z1,z795,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z97,z671]),(0,[z1,z796,z3,z4,z5,z6]),(0,[z797,z1,z3,z4,z5,z6]),(0,[z1,z798,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z751])],[(0,[z1,z2,z3,z4,z799,z6]),(0,[z20,z2,z3,z105,z5,z6]),(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z2,z3,z4,z5,z801]),(0,[z802,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z803,z6]),(0,[z1,z2,z3,z804,z4,z6]),(0,[z1,z2,z35,z236,z30,z6]),(0,[z29,z1,z2,z4,z153,z117]),(0,[z114,z1,z2,z3,z4,z64]),(0,[z114,z1,z2,z3,z4,z263]),(0,[z297,z2,z3,z5,z97,z6]),(0,[z1,z2,z3,z160,z97,z6])]],
   [[(0,[z1,z32,z2,z3,z436,z6]),(0,[z1,z54,z2,z3,z30,z6]),(0,[z1,z2,z3,z4,z805,z6]),(0,[z806,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z638,z30,z6]),(0,[z1,z60,z3,z508,z4,z61]),(0,[z1,z11,z2,z3,z807,z6]),(0,[z1,z2,z3,z34,z727,z6])],[(0,[z1,z2,z3,z808,z4,z6]),(0,[z1,z2,z3,z4,z30,z273]),(0,[z1,z2,z186,z4,z5,z809])],[(0,[z1,z2,z3,z4,z810,z6]),(0,[z1,z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z811,z6]),(0,[z1,z2,z3,z68,z812,z6]),(0,[z1,z2,z3,z771,z4,z6]),(0,[z1,z2,z35,z3,z160,z6]),(0,[z99,z1,z4,z5,z123,z6])],[(0,[z1,z2,z3,z813,z5,z6]),(0,[z814,z2,z3,z4,z5,z6])],[(0,[z165,z71,z3,z4,z384,z6]),(0,[z1,z2,z3,z4,z815,z6]),(0,[z1,z86,z3,z4,z396,z6]),(0,[z2,z3,z4,z9,z816,z6]),(0,[z1,z11,z2,z3,z57,z6]),(0,[z1,z2,z3,z4,z5,z817]),(0,[z1,z2,z3,z4,z818,z6]),(0,[z1,z819,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z319,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z277,z1,z2,z3,z6,z182])],[(0,[z821,z1,z2,z3,z4,z5]),(0,[z196,z2,z3,z9,z53,z6]),(0,[z1,z2,z3,z4,z822,z6]),(0,[z149,z1,z32,z208,z4,z6]),(0,[z1,z823,z2,z3,z4,z6]),(0,[z129,z1,z3,z4,z30,z25]),(0,[z96,z1,z2,z3,z160,z6]),(0,[z2,z3,z4,z461,z6,z258]),(0,[z1,z824,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z825,z6]),(0,[z1,z2,z826,z3,z4,z6])],[(0,[z20,z1,z2,z266,z30,z6]),(0,[z1,z2,z3,z4,z396,z166]),(0,[z101,z450,z2,z3,z4,z6]),(0,[z216,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z351,z4,z6]),(0,[z1,z2,z3,z827,z4,z6]),(0,[z1,z2,z828,z3,z4,z6]),(0,[z829,z1,z2,z3,z34,z6])],[(0,[z830,z1,z2,z3,z4,z6]),(0,[z542,z1,z2,z78,z4,z6]),(0,[z1,z2,z831,z4,z5,z6]),(0,[z1,z2,z44,z223,z4,z6])]],
   [[(0,[z1,z2,z330,z3,z30,z6]),(0,[z1,z2,z21,z4,z220,z6]),(0,[z1,z2,z26,z3,z4,z6]),(0,[z96,z1,z315,z2,z3,z6]),(0,[z1,z2,z832,z3,z160,z6])],[(0,[z165,z71,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z833,z6]),(0,[z150,z2,z3,z4,z336,z6]),(0,[z1,z2,z834,z3,z4,z6])],[(0,[z1,z2,z835,z4,z5,z6]),(0,[z1,z2,z3,z4,z836,z6]),(0,[z20,z2,z3,z105,z396,z6]),(0,[z1,z530,z2,z3,z4,z34]),(0,[z1,z2,z3,z4,z732,z6]),(0,[z1,z2,z837,z3,z4,z6]),(0,[z85,z1,z2,z179,z30,z6]),(0,[z1,z46,z2,z3,z293,z125]),(0,[z1,z11,z2,z838,z4,z6])],[(0,[z33,z2,z3,z5,z57,z40]),(0,[z149,z451,z1,z4,z5,z6]),(0,[z1,z2,z3,z839,z5,z6]),(0,[z1,z107,z173,z3,z4,z6]),(0,[z1,z673,z2,z3,z4,z34]),(0,[z1,z130,z2,z3,z5,z125]),(0,[z297,z46,z2,z3,z5,z125]),(0,[z1,z840,z2,z3,z160,z6])],[(0,[z1,z841,z2,z3,z4,z6]),(0,[z1,z2,z842,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z731]),(0,[z1,z2,z3,z4,z843,z6]),(0,[z1,z154,z2,z3,z160,z6]),(0,[z844,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z661]),(1,[z1,z2,z4,z5,z809]),(0,[z845,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z846])],[(0,[z1,z847,z2,z3,z4,z6]),(0,[z1,z11,z2,z3,z4,z279]),(0,[z129,z1,z3,z4,z411,z25]),(0,[z1,z2,z758,z4,z5,z6]),(0,[z43,z1,z2,z4,z6,z427]),(0,[z1,z848,z2,z3,z4,z6]),(0,[z11,z2,z3,z4,z6,z258]),(0,[z1,z2,z3,z160,z160,z6])],[(0,[z1,z2,z3,z849,z4,z6]),(0,[z1,z2,z3,z4,z850,z6]),(0,[z298,z1,z32,z2,z3,z6]),(0,[z149,z1,z310,z4,z5,z6]),(0,[z1,z2,z3,z851,z4,z6]),(0,[z1,z2,z739,z4,z5,z6]),(0,[z43,z1,z2,z78,z4,z6]),(0,[z1,z2,z3,z319,z6,z182]),(0,[z1,z11,z2,z3,z852,z6]),(0,[z1,z2,z3,z160,z6,z145])],[(0,[z1,z2,z3,z853,z5,z6]),(0,[z431,z188,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z854,z6]),(0,[z1,z86,z3,z4,z5,z294]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z2,z3,z68,z5,z6]),(0,[z1,z2,z3,z4,z34,z434]),(0,[z129,z1,z4,z5,z337,z25]),(0,[z1,z32,z2,z564,z3,z6])]],
   [[(0,[z2,z3,z39,z5,z6,z335]),(0,[z1,z2,z3,z357,z57,z6]),(0,[z1,z32,z2,z3,z68,z6]),(0,[z1,z2,z3,z76,z160,z6]),(0,[z856,z2,z3,z4,z5,z6]),(0,[z297,z11,z2,z3,z4,z6]),(0,[z2,z3,z4,z301,z6,z258])],[(0,[z1,z2,z3,z4,z857,z6]),(0,[z1,z2,z3,z646,z30,z6]),(0,[z1,z32,z2,z3,z214,z6]),(0,[z1,z602,z3,z4,z5,z61]),(0,[z1,z462,z2,z3,z160,z6])],[(0,[z165,z11,z71,z3,z4,z6]),(0,[z1,z2,z3,z4,z858,z6])],[(0,[z1,z2,z3,z4,z859,z6]),(0,[z1,z2,z3,z4,z860,z6]),(0,[z1,z2,z3,z4,z861,z6]),(0,[z1,z32,z74,z3,z4,z6]),(0,[z75,z1,z32,z3,z76,z6]),(0,[z1,z60,z2,z3,z160,z6]),(0,[z1,z2,z3,z4,z862,z6]),(0,[z297,z2,z3,z4,z30,z6]),(0,[z2,z3,z4,z30,z6,z863]),(0,[z1,z502,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z266,z4,z396,z6]),(0,[z1,z865,z2,z3,z4,z6]),(0,[z1,z2,z3,z111,z30,z97])],[(0,[z1,z2,z866,z4,z5,z6]),(0,[z1,z2,z3,z867,z4,z6]),(0,[z1,z2,z3,z160,z61,z6]),(0,[z1,z2,z3,z4,z34,z347])],[(0,[z165,z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z53,z30,z6]),(0,[z29,z1,z2,z3,z160,z6]),(0,[z96,z1,z32,z2,z3,z6]),(0,[z1,z2,z16,z3,z160,z6]),(0,[z114,z1,z2,z3,z340,z6])],[(0,[z868,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z663,z30,z6]),(0,[z1,z2,z3,z4,z812,z6]),(0,[z1,z869,z2,z3,z4,z6]),(0,[z1,z2,z3,z870,z5,z6]),(0,[z1,z32,z2,z3,z135,z6]),(0,[z1,z2,z3,z4,z871,z6]),(0,[z99,z29,z1,z4,z5,z6])]],
   [[(0,[z1,z872,z3,z4,z5,z6]),(0,[z89,z2,z3,z228,z5,z6]),(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z2,z874,z3,z4,z6]),(0,[z1,z2,z3,z160,z6,z125])],[(0,[z1,z2,z875,z4,z5,z6]),(0,[z20,z2,z3,z105,z5,z166]),(0,[z2,z3,z4,z730,z5,z6]),(0,[z20,z32,z2,z3,z105,z6]),(0,[z20,z2,z3,z628,z5,z6]),(0,[z196,z1,z2,z3,z160,z6]),(0,[z1,z54,z2,z3,z5,z125]),(0,[z1,z32,z2,z3,z4,z273]),(0,[z1,z32,z2,z186,z4,z123]),(0,[z1,z2,z3,z282,z30,z6])],[(0,[z1,z2,z3,z876,z4,z6]),(0,[z1,z2,z3,z4,z877,z6]),(1,[z1,z2,z3,z732,z6]),(0,[z1,z2,z3,z214,z5,z229])],[(0,[z216,z2,z3,z4,z459,z6]),(0,[z149,z1,z650,z4,z5,z6]),(0,[z1,z11,z12,z3,z81,z6]),(0,[z1,z2,z3,z4,z878,z6]),(0,[z1,z2,z758,z3,z4,z6])],[(0,[z1,z2,z3,z30,z6,z294]),(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z2,z3,z160,z105,z6]),(0,[z1,z880,z2,z3,z4,z6]),(0,[z216,z2,z3,z4,z336,z6]),(0,[z149,z1,z208,z4,z5,z229]),(0,[z1,z881,z208,z4,z5,z6]),(0,[z1,z562,z3,z4,z93,z6]),(0,[z1,z32,z2,z3,z160,z6]),(0,[z1,z2,z3,z55,z4,z64])],[(0,[z150,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z882,z6]),(0,[z1,z883,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z64,z125])],[(0,[z89,z1,z2,z3,z319,z6]),(0,[z1,z2,z4,z5,z6,z337]),(0,[z2,z3,z4,z5,z6,z884]),(0,[z1,z2,z3,z4,z120,z6]),(0,[z885,z2,z3,z4,z5,z6]),(0,[z49,z1,z2,z274,z4,z6]),(0,[z1,z2,z3,z340,z160,z6])],[(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z266,z4,z5,z294]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z1,z888,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z2,z3,z4,z890,z6]),(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z892,z2,z3,z68,z6]),(0,[z1,z2,z3,z709,z5,z6]),(0,[z43,z1,z2,z505,z4,z6])],[(0,[z1,z74,z3,z4,z34,z6]),(0,[z1,z2,z4,z5,z6,z809])],[(0,[z1,z2,z3,z4,z893,z6]),(0,[z188,z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z2,z3,z4,z895,z6]),(0,[z1,z12,z3,z81,z34,z6]),(0,[z1,z896,z2,z3,z4,z6]),(0,[z1,z130,z2,z3,z4,z6]),(0,[z586,z1,z2,z3,z30,z6])],[(0,[z1,z897,z3,z4,z5,z6]),(0,[z20,z506,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z898,z6]),(0,[z1,z3,z4,z5,z6,z226]),(0,[z1,z2,z899,z3,z4,z6]),(0,[z1,z2,z3,z353,z4,z319])],[(0,[z72,z188,z3,z4,z5,z6]),(0,[z72,z488,z3,z4,z5,z6]),(0,[z89,z2,z3,z5,z264,z6]),(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z2,z3,z4,z901,z6])],[(0,[z298,z1,z2,z3,z30,z6]),(0,[z1,z2,z3,z4,z5,z902]),(0,[z903,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z904]),(0,[z1,z2,z3,z111,z319,z6]),(0,[z1,z2,z3,z4,z905,z6])],[(0,[z1,z2,z3,z4,z906,z6]),(0,[z33,z32,z2,z3,z4,z40]),(0,[z1,z32,z2,z533,z3,z6])],[(0,[z1,z188,z2,z3,z160,z6]),(0,[z149,z1,z208,z68,z5,z6]),(0,[z99,z1,z3,z4,z34,z6]),(0,[z1,z2,z3,z160,z123,z6]),(0,[z558,z2,z3,z4,z121,z6])]],
   [[(0,[z72,z1,z2,z3,z160,z6]),(0,[z297,z2,z3,z4,z5,z294]),(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z2,z3,z4,z6,z908]),(0,[z114,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z909,z6]),(0,[z1,z2,z3,z4,z34,z391]),(0,[z196,z2,z3,z4,z495,z6]),(0,[z2,z3,z30,z6,z258,z125]),(0,[z1,z910,z2,z3,z4,z6])],[(0,[z1,z18,z3,z81,z5,z6]),(0,[z1,z611,z2,z3,z30,z6]),(0,[z1,z2,z3,z911,z5,z6]),(0,[z196,z2,z3,z4,z816,z6]),(0,[z290,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z912,z6]),(0,[z1,z2,z758,z4,z103,z6]),(0,[z1,z32,z2,z3,z231,z6]),(0,[z96,z1,z2,z3,z6,z182]),(0,[z1,z573,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z913,z6]),(0,[z1,z2,z3,z891,z30,z6]),(0,[z1,z914,z2,z3,z4,z5]),(0,[z1,z2,z3,z160,z113,z6]),(0,[z33,z1,z2,z3,z160,z6]),(0,[z290,z1,z2,z24,z4,z6]),(0,[z1,z2,z3,z4,z6,z915])],[(0,[z1,z916,z2,z3,z4,z6]),(0,[z1,z2,z3,z628,z30,z6]),(0,[z1,z917,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z378,z6])],[(0,[z1,z2,z3,z4,z5,z918]),(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z2,z3,z4,z920,z6]),(0,[z1,z2,z3,z4,z921,z6]),(0,[z1,z46,z2,z3,z34,z125])],[(0,[z165,z71,z3,z4,z308,z6]),(0,[z1,z2,z52,z3,z160,z6]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z30,z294]),(0,[z1,z2,z3,z630,z30,z6]),(0,[z216,z11,z2,z3,z4,z6]),(0,[z923,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z459,z273]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z1,z46,z2,z3,z5,z846])],[(0,[z1,z2,z3,z4,z384,z6]),(0,[z1,z2,z637,z3,z30,z6]),(0,[z1,z2,z3,z4,z34,z157]),(0,[z1,z2,z3,z34,z57,z6]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z1,z2,z3,z4,z336,z273]),(0,[z1,z2,z179,z3,z160,z6])]],
   [[(0,[z1,z11,z2,z3,z4,z92]),(0,[z1,z60,z3,z4,z5,z720]),(0,[z1,z2,z3,z926,z4,z6]),(0,[z1,z11,z2,z3,z800,z6])],[(0,[z1,z2,z3,z4,z927,z6]),(0,[z1,z2,z3,z4,z928,z6]),(0,[z1,z32,z2,z21,z4,z6]),(0,[z1,z183,z2,z3,z4,z6]),(0,[z216,z2,z3,z4,z30,z6]),(0,[z1,z3,z568,z4,z6,z226])],[(0,[z1,z2,z3,z929,z4,z5]),(0,[z1,z2,z3,z4,z930,z6]),(1,[z1,z2,z758,z4,z6]),(0,[z1,z11,z2,z3,z931,z6]),(1,[z1,z2,z3,z4,z751])],[(0,[z124,z1,z2,z3,z30,z6]),(0,[z150,z2,z3,z214,z5,z6]),(0,[z129,z1,z2,z3,z160,z6]),(0,[z756,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z34,z6]),(0,[z1,z2,z932,z3,z4,z6]),(0,[z1,z2,z3,z5,z846,z125]),(0,[z297,z46,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z933,z6]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z167,z1,z2,z4,z6,z427])],[(0,[z934,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z160,z30,z6]),(0,[z297,z2,z3,z5,z30,z6])],[(0,[z1,z2,z3,z4,z935,z6]),(0,[z1,z60,z3,z4,z5,z61]),(0,[z43,z1,z2,z758,z4,z6]),(0,[z1,z540,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z937,z3,z4,z5,z6]),(0,[z938,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z34,z6,z337]),(0,[z99,z1,z11,z3,z4,z6]),(0,[z1,z2,z3,z319,z6,z125]),(0,[z240,z261,z2,z3,z4,z6])]],
   [[(0,[z2,z769,z51,z4,z5,z6]),(0,[z1,z2,z3,z160,z9,z6]),(0,[z1,z11,z2,z3,z68,z6]),(0,[z939,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z940,z6]),(0,[z941,z32,z2,z3,z4,z6]),(0,[z1,z2,z3,z160,z942,z6])],[(0,[z1,z943,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z944,z6]),(0,[z1,z11,z2,z3,z214,z6]),(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z2,z3,z946,z5,z6]),(0,[z1,z2,z44,z3,z160,z6])],[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z2,z21,z4,z30,z6]),(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z2,z3,z4,z949,z6]),(0,[z114,z1,z2,z3,z111,z97])],[(0,[z1,z2,z3,z4,z950,z6]),(0,[z1,z951,z3,z4,z5,z6]),(0,[z1,z11,z74,z3,z4,z6]),(0,[z1,z2,z3,z8,z53,z6]),(0,[z1,z2,z3,z160,z6,z25]),(0,[z1,z2,z35,z236,z120,z6]),(0,[z1,z2,z3,z353,z4,z34]),(0,[z1,z2,z3,z5,z6,z846]),(0,[z1,z2,z3,z952,z4,z6]),(0,[z953,z1,z2,z3,z160,z6])],[(0,[z149,z150,z208,z4,z5,z6]),(0,[z149,z1,z208,z4,z5,z6]),(0,[z1,z954,z2,z3,z4,z6]),(0,[z1,z3,z709,z81,z5,z6]),(0,[z75,z1,z2,z3,z160,z6]),(0,[z1,z11,z2,z3,z4,z625]),(0,[z1,z11,z2,z726,z4,z6])],[(0,[z1,z2,z3,z191,z30,z6]),(0,[z1,z2,z3,z4,z88,z6]),(0,[z1,z955,z2,z3,z5,z6]),(0,[z1,z2,z24,z4,z6,z337]),(0,[z1,z2,z3,z4,z956,z6])],[(0,[z1,z2,z3,z957,z5,z6]),(0,[z1,z11,z2,z3,z4,z510]),(0,[z451,z1,z11,z2,z3,z4]),(0,[z75,z1,z244,z3,z76,z6]),(0,[z1,z2,z227,z3,z4,z6]),(0,[z1,z2,z3,z108,z160,z6])],[(0,[z1,z958,z2,z3,z4,z6]),(0,[z1,z2,z186,z4,z34,z123])]],
   [[(0,[z1,z2,z3,z4,z220,z294]),(0,[z1,z2,z3,z4,z959,z6]),(0,[z1,z2,z3,z4,z960,z6]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z2,z962,z3,z4,z6]),(0,[z1,z2,z3,z4,z97,z64])],[(0,[z545,z2,z51,z4,z5,z6]),(0,[z1,z2,z3,z566,z30,z6]),(0,[z20,z11,z2,z3,z105,z6]),(0,[z1,z11,z2,z3,z4,z273]),(0,[z1,z2,z35,z236,z5,z6]),(0,[z963,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z186,z4,z123]),(0,[z1,z2,z3,z160,z6,z6])],[(0,[z1,z2,z3,z964,z5,z6]),(0,[z1,z54,z2,z3,z5,z6]),(0,[z33,z2,z3,z4,z357,z40]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z75,z1,z3,z76,z34,z6]),(0,[z1,z32,z2,z35,z236,z6])],[(0,[z1,z32,z86,z3,z4,z6]),(0,[z1,z32,z46,z2,z3,z125])],[(1,[z721,z3,z4,z5,z6]),(0,[z1,z2,z21,z4,z396,z6]),(0,[z1,z2,z966,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z6]),(0,[z1,z2,z3,z732,z5,z6]),(0,[z1,z2,z3,z4,z967,z6]),(0,[z1,z2,z3,z4,z968,z6]),(0,[z1,z107,z3,z4,z93,z6]),(0,[z1,z2,z78,z16,z4,z6]),(0,[z29,z1,z32,z2,z4,z117]),(0,[z1,z32,z2,z3,z30,z6]),(0,[z1,z11,z2,z3,z160,z6])],[(0,[z50,z2,z51,z4,z34,z6]),(0,[z1,z107,z100,z3,z4,z6]),(0,[z1,z2,z3,z4,z969,z6])],[(0,[z1,z970,z3,z4,z5,z6]),(0,[z1,z3,z76,z709,z5,z6]),(0,[z1,z2,z3,z4,z64,z6]),(0,[z1,z2,z3,z340,z30,z6]),(0,[z971,z1,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z972,z6]),(0,[z973,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z160,z122,z6]),(0,[z1,z2,z3,z974,z4,z6]),(0,[z1,z2,z3,z4,z975,z6]),(0,[z1,z2,z976,z4,z5,z6]),(0,[z129,z1,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z96,z1,z2,z3,z461,z6])]],
   [[(0,[z1,z2,z3,z4,z979,z6]),(0,[z306,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z550,z30,z6]),(0,[z29,z1,z2,z4,z5,z273]),(0,[z1,z2,z3,z4,z980,z6]),(0,[z1,z450,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z981,z6]),(0,[z982,z2,z3,z4,z5,z6]),(0,[z1,z2,z983,z4,z5,z6]),(0,[z1,z2,z24,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z984])],[(0,[z1,z2,z3,z4,z985,z6]),(0,[z1,z2,z3,z4,z34,z294]),(0,[z1,z2,z3,z214,z34,z6])],[(0,[z150,z2,z3,z68,z5,z6]),(0,[z500,z1,z3,z76,z5,z6]),(0,[z1,z11,z2,z3,z4,z379]),(0,[z1,z2,z3,z986,z4,z6]),(0,[z1,z2,z3,z4,z6,z987]),(0,[z1,z2,z3,z160,z988,z6])],[(0,[z1,z2,z266,z4,z5,z6]),(0,[z1,z2,z3,z4,z989,z6])],[(0,[z1,z990,z3,z4,z5,z6]),(0,[z1,z724,z2,z3,z57,z6]),(0,[z991,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z992,z5,z6]),(0,[z1,z130,z2,z3,z4,z319])],[(0,[z1,z2,z3,z4,z34,z166]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z33,z11,z2,z3,z4,z40]),(0,[z1,z2,z3,z994,z5,z6]),(0,[z29,z1,z2,z4,z34,z117]),(0,[z1,z2,z995,z3,z4,z6])],[(0,[z1,z2,z21,z4,z5,z294]),(0,[z1,z54,z11,z2,z3,z6]),(0,[z85,z1,z2,z3,z160,z6]),(0,[z1,z11,z2,z3,z4,z600]),(0,[z1,z2,z78,z274,z4,z6]),(0,[z348,z450,z2,z3,z4,z6]),(0,[z996,z11,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z997,z3,z5,z6]),(0,[z20,z1,z2,z3,z106,z6]),(0,[z1,z211,z3,z81,z5,z6]),(0,[z129,z1,z3,z4,z5,z720]),(0,[z1,z2,z3,z457,z30,z6]),(0,[z118,z573,z2,z3,z4,z6])],[(0,[z33,z2,z3,z4,z30,z40]),(0,[z1,z2,z3,z623,z4,z34]),(0,[z297,z2,z3,z30,z6,z125])],[(0,[z72,z32,z188,z3,z4,z6]),(0,[z20,z2,z3,z105,z34,z6]),(0,[z688,z2,z3,z4,z9,z6]),(0,[z149,z1,z208,z214,z5,z6]),(0,[z1,z12,z2,z3,z160,z6]),(0,[z75,z1,z3,z709,z5,z6]),(0,[z1,z11,z2,z3,z4,z205]),(0,[z998,z1,z2,z3,z4,z6])],[(0,[z1,z2,z999,z3,z4,z6]),(0,[z216,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z4,z1000,z6]),(0,[z1,z2,z3,z4,z1001,z6]),(0,[z1,z2,z78,z758,z4,z6]),(0,[z1,z11,z2,z3,z340,z34])],[(0,[z1,z1002,z2,z3,z4,z6]),(0,[z1,z2,z3,z1003,z4,z6]),(0,[z1,z2,z3,z4,z1004,z6]),(0,[z89,z2,z3,z39,z106,z6]),(0,[z1,z2,z3,z4,z291,z6]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z1,z2,z3,z4,z293,z6]),(0,[z1,z2,z3,z4,z1006,z6])],[(0,[z1,z2,z3,z4,z1007,z6]),(0,[z1,z2,z3,z1008,z5,z6]),(0,[z297,z2,z3,z4,z5,z6]),(0,[z400,z2,z3,z4,z113,z6]),(0,[z1,z1009,z2,z3,z4,z6]),(0,[z1,z2,z3,z55,z4,z751])],[(0,[z1,z2,z1010,z4,z5,z6]),(0,[z1,z86,z3,z4,z5,z166]),(0,[z1,z2,z3,z4,z816,z6]),(0,[z1,z183,z2,z3,z57,z6]),(0,[z67,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z168,z2,z3,z30,z6]),(0,[z1,z2,z3,z111,z5,z97]),(0,[z1,z46,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z1013,z3,z5,z6]),(0,[z1,z2,z3,z4,z34,z229]),(0,[z1,z2,z4,z30,z6,z337]),(0,[z1,z11,z2,z3,z340,z145])]],
   [[(0,[z1,z2,z3,z1014,z5,z6]),(0,[z1,z54,z2,z3,z5,z294]),(0,[z20,z2,z3,z5,z97,z122]),(0,[z1,z2,z3,z53,z5,z6]),(0,[z1015,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1016,z6])],[(0,[z1,z2,z3,z4,z308,z6]),(0,[z165,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z4,z1017,z6]),(0,[z1,z11,z2,z21,z4,z6]),(0,[z1,z2,z3,z5,z57,z6]),(0,[z1,z556,z2,z3,z30,z6]),(0,[z1,z2,z4,z5,z809,z117]),(0,[z1,z2,z3,z160,z1018,z6])],[(0,[z1,z2,z3,z4,z1019,z6]),(0,[z20,z86,z3,z105,z5,z6]),(0,[z1,z74,z3,z4,z220,z6]),(0,[z1,z2,z186,z4,z338,z123]),(0,[z1,z725,z2,z3,z4,z6])],[(0,[z20,z1,z2,z3,z30,z6]),(0,[z271,z1,z100,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1,z12,z3,z351,z81,z6]),(0,[z1,z2,z3,z4,z1021,z6]),(0,[z1,z3,z4,z30,z6,z226]),(0,[z1,z1022,z2,z3,z4,z6]),(0,[z1,z2,z3,z353,z30,z125])],[(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z1024,z4,z6]),(0,[z1025,z1,z2,z3,z4,z6]),(0,[z1,z168,z2,z3,z4,z64])],[(0,[z1,z2,z3,z4,z1026,z6]),(0,[z1,z2,z3,z5,z97,z294]),(0,[z1,z2,z3,z4,z1027,z6]),(1,[z1,z130,z2,z3,z125]),(0,[z1,z11,z2,z3,z839,z6])],[(0,[z89,z2,z3,z39,z30,z6]),(0,[z1,z954,z2,z3,z4,z229]),(0,[z290,z1,z11,z2,z4,z6]),(0,[z1,z2,z3,z580,z30,z6]),(1,[z1,z2,z3,z5,z846]),(0,[z1,z2,z1028,z3,z160,z6])]],
   [[(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z1030,z2,z3,z4,z6]),(0,[z1,z2,z3,z1031,z4,z6])],[(0,[z1,z2,z1032,z4,z5,z6]),(0,[z1,z2,z1033,z4,z5,z6]),(1,[z1,z3,z4,z5,z720])],[(0,[z1,z1034,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1035,z6]),(0,[z1,z32,z2,z266,z4,z6]),(0,[z1,z2,z3,z68,z34,z6]),(0,[z941,z2,z3,z4,z5,z6]),(0,[z517,z2,z3,z4,z522,z6])],[(0,[z1,z2,z3,z4,z1036,z6]),(0,[z1,z2,z1037,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1038]),(0,[z1,z2,z3,z4,z1039,z6])],[(0,[z1,z86,z266,z4,z5,z6]),(0,[z1,z1040,z3,z4,z5,z6]),(0,[z1,z2,z3,z1041,z5,z6]),(0,[z1,z2,z4,z5,z123,z609]),(0,[z1,z3,z771,z4,z93,z6]),(0,[z1,z2,z199,z4,z103,z6]),(0,[z1,z2,z3,z4,z34,z94])],[(0,[z1,z2,z3,z1042,z5,z6]),(0,[z1,z2,z3,z4,z1043,z6]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z1,z1045,z2,z3,z4,z6]),(0,[z1,z251,z3,z4,z93,z6]),(0,[z1,z2,z3,z1046,z5,z6]),(0,[z1,z2,z78,z3,z160,z6]),(0,[z1,z11,z2,z3,z4,z34])],[(0,[z1,z2,z3,z4,z1047,z6]),(0,[z1,z2,z266,z4,z5,z166]),(0,[z1,z2,z3,z1048,z4,z6]),(0,[z1,z2,z3,z4,z1049,z6]),(0,[z1,z2,z3,z269,z30,z6]),(0,[z1,z2,z3,z108,z30,z6])],[(0,[z1,z1050,z2,z3,z4,z6]),(0,[z298,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z67,z2,z3,z4,z34,z122]),(0,[z275,z1,z2,z78,z4,z6]),(0,[z129,z1,z11,z3,z4,z25]),(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z2,z186,z4,z30,z123]),(0,[z1,z2,z3,z4,z1053,z6]),(1,[z1,z725,z2,z3,z6]),(0,[z1,z914,z2,z3,z4,z30])]],
   [[(0,[z101,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z32,z2,z4,z6,z337])],[(0,[z1,z74,z21,z4,z5,z6]),(0,[z1,z11,z2,z3,z1046,z6]),(0,[z1,z11,z2,z3,z4,z145])],[(0,[z1055,z1,z3,z4,z5,z6]),(0,[z1,z2,z1056,z3,z4,z6]),(0,[z20,z2,z266,z105,z5,z6]),(0,[z1,z2,z3,z4,z1057,z6]),(0,[z1,z2,z3,z1058,z5,z6]),(0,[z1,z2,z3,z4,z1059,z6]),(0,[z129,z290,z1,z4,z5,z25]),(0,[z1,z3,z4,z5,z6,z720]),(0,[z1,z11,z2,z35,z236,z6])],[(0,[z721,z71,z3,z4,z5,z6]),(0,[z1,z11,z86,z3,z4,z6]),(0,[z33,z54,z2,z3,z5,z6]),(0,[z1,z54,z2,z3,z1060,z6]),(0,[z1,z2,z3,z1061,z4,z6])],[(0,[z1,z590,z11,z2,z3,z4]),(0,[z196,z2,z3,z4,z228,z6]),(0,[z1,z725,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z1062,z6]),(0,[z50,z2,z51,z4,z30,z6]),(0,[z1,z2,z3,z4,z220,z6]),(0,[z1,z2,z3,z4,z1063,z294]),(0,[z1,z2,z3,z4,z1064,z6]),(0,[z1,z2,z3,z293,z6,z125])],[(0,[z1,z1065,z2,z3,z4,z6]),(0,[z1,z11,z2,z3,z376,z4]),(0,[z89,z1,z2,z3,z293,z6]),(0,[z240,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1066,z6]),(0,[z1067,z1,z3,z4,z5,z6]),(0,[z139,z1,z2,z223,z4,z6])],[(0,[z1,z2,z3,z4,z1068,z6]),(0,[z1,z2,z3,z4,z1069,z6]),(0,[z99,z29,z1,z4,z5,z117]),(0,[z1,z46,z2,z3,z461,z125]),(0,[z1,z11,z1070,z3,z4,z6])]],
   [[(0,[z118,z2,z3,z4,z9,z6]),(0,[z150,z2,z3,z4,z34,z6]),(0,[z1,z2,z3,z111,z5,z846])],[(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1,z2,z3,z68,z5,z273]),(0,[z1,z2,z4,z5,z123,z273]),(0,[z1,z2,z537,z236,z5,z6]),(0,[z1,z2,z3,z180,z4,z6]),(0,[z1,z2,z3,z479,z4,z34]),(0,[z1,z1072,z3,z4,z5,z6]),(0,[z1,z2,z199,z4,z480,z6])],[(0,[z1,z2,z3,z4,z30,z294]),(0,[z1,z2,z3,z4,z6,z1073]),(0,[z1,z2,z3,z4,z1074,z6]),(0,[z1,z11,z2,z1075,z4,z6])],[(0,[z1,z2,z3,z4,z1076,z6]),(0,[z216,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1077,z5,z6]),(0,[z20,z2,z3,z730,z5,z6]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z2,z3,z160,z81,z6]),(0,[z1,z315,z2,z3,z30,z6]),(0,[z1,z11,z2,z3,z4,z263])],[(0,[z1,z2,z3,z4,z5,z1079]),(0,[z165,z71,z3,z4,z30,z6]),(0,[z558,z2,z3,z4,z113,z6]),(0,[z298,z1,z11,z2,z3,z6])],[(0,[z20,z1,z2,z3,z30,z166]),(0,[z1,z2,z3,z53,z103,z6]),(0,[z1,z2,z3,z4,z1080,z6]),(0,[z1,z2,z3,z1081,z4,z6]),(0,[z1,z1082,z2,z3,z4,z6]),(0,[z1,z2,z3,z156,z30,z6]),(0,[z1,z2,z3,z1083,z4,z6]),(0,[z467,z1,z2,z3,z30,z6]),(0,[z1,z2,z3,z111,z293,z6]),(0,[z1084,z11,z2,z3,z4,z6])],[(0,[z1,z130,z2,z3,z4,z97])],[(0,[z1,z1085,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1086,z6]),(0,[z297,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z160,z6]),(0,[z1,z2,z3,z160,z5,z6])]],
   [[(0,[z1,z1087,z3,z4,z5,z6]),(0,[z1,z2,z3,z565,z30,z6]),(0,[z1,z2,z3,z4,z6,z1088]),(0,[z1,z2,z362,z4,z300,z6]),(0,[z1,z46,z2,z3,z301,z125])],[(0,[z1,z2,z4,z5,z6,z1089]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z101,z2,z3,z4,z816,z6]),(0,[z1,z32,z2,z3,z53,z6]),(0,[z99,z1,z3,z4,z5,z273]),(0,[z845,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z368,z6]),(0,[z1,z2,z3,z111,z319,z97])],[(0,[z72,z11,z188,z3,z4,z6]),(0,[z1,z2,z3,z1091,z4,z6]),(0,[z1,z2,z173,z3,z160,z6])],[(0,[z1,z46,z2,z3,z6,z182]),(0,[z395,z1,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z1092,z6]),(0,[z1,z2,z21,z4,z5,z6]),(0,[z1,z2,z739,z35,z5,z6]),(0,[z1,z2,z186,z3,z160,z6]),(0,[z1,z284,z3,z4,z109,z6]),(0,[z240,z1,z2,z3,z30,z6]),(0,[z375,z1,z2,z339,z4,z6]),(0,[z1,z11,z2,z3,z1058,z6])],[(0,[z2,z3,z4,z5,z122,z294]),(0,[z20,z1,z2,z3,z319,z6]),(0,[z2,z3,z4,z816,z113,z6]),(0,[z429,z2,z3,z4,z5,z122]),(0,[z311,z1,z3,z8,z4,z6]),(0,[z290,z1,z2,z4,z34,z6]),(0,[z1,z2,z739,z236,z5,z6]),(0,[z1,z2,z3,z1093,z4,z6]),(0,[z1,z2,z3,z95,z30,z6])],[(0,[z1,z3,z4,z5,z6,z1094]),(0,[z1,z2,z1095,z3,z4,z6]),(0,[z1,z2,z44,z339,z4,z6]),(0,[z1,z11,z718,z3,z4,z6]),(0,[z1,z2,z3,z282,z319,z6])],[(0,[z644,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z1096,z4,z6]),(0,[z1,z2,z692,z4,z103,z6]),(0,[z1,z2,z3,z4,z30,z229]),(0,[z1,z2,z152,z4,z103,z6]),(0,[z1,z2,z3,z4,z1097,z6]),(0,[z17,z1,z2,z3,z160,z6])]],
   [[(0,[z1,z2,z1098,z4,z5,z6]),(0,[z1,z11,z2,z3,z1099,z6])],[(0,[z1,z719,z2,z3,z214,z6]),(0,[z1,z888,z2,z3,z4,z273]),(0,[z1,z2,z3,z4,z1100,z6]),(0,[z1,z1070,z3,z4,z5,z6])],[(0,[z1,z1101,z2,z3,z4,z6]),(0,[z1,z2,z1102,z3,z5,z6]),(0,[z1,z32,z2,z3,z402,z6]),(0,[z290,z1,z2,z4,z5,z117]),(0,[z1,z1103,z2,z3,z4,z6]),(0,[z1,z32,z60,z3,z4,z61]),(0,[z1,z1104,z2,z3,z4,z6]),(0,[z750,z32,z2,z3,z4,z6])],[(0,[z1,z2,z3,z1105,z5,z6]),(0,[z1,z2,z1075,z4,z5,z6]),(0,[z1,z2,z3,z4,z1106,z6])],[(0,[z1,z2,z3,z1107,z4,z6])],[(0,[z1,z2,z3,z4,z1108,z6]),(0,[z1,z86,z3,z4,z220,z6]),(0,[z1,z1109,z2,z3,z4,z6]),(0,[z96,z1,z2,z3,z5,z294]),(0,[z1,z2,z3,z730,z5,z6]),(0,[z1110,z2,z3,z4,z5,z6]),(0,[z1,z2,z256,z4,z5,z123])],[(0,[z1,z2,z1111,z3,z4,z6]),(0,[z1,z2,z3,z4,z1112,z6]),(0,[z1,z2,z3,z4,z5,z273]),(0,[z149,z1,z881,z4,z5,z6]),(0,[z1,z1113,z3,z4,z5,z6]),(0,[z1,z130,z2,z3,z30,z125]),(0,[z1,z32,z2,z3,z111,z97]),(0,[z395,z1,z173,z3,z4,z6])],[(0,[z50,z2,z51,z4,z370,z6]),(0,[z1,z2,z3,z4,z220,z166]),(0,[z2,z3,z4,z5,z6,z258]),(1,[z1,z2,z3,z160,z6]),(0,[z1,z130,z2,z3,z160,z6]),(0,[z1,z2,z3,z223,z160,z6]),(0,[z1,z2,z3,z4,z34,z751])]],
   [[(0,[z1,z2,z3,z4,z1114,z6]),(0,[z1,z2,z3,z340,z5,z6])],[(0,[z1,z2,z3,z4,z1115,z6]),(0,[z1,z1116,z2,z3,z4,z6]),(0,[z50,z2,z769,z4,z5,z6]),(0,[z216,z2,z3,z214,z5,z6]),(0,[z1,z2,z3,z4,z459,z6]),(0,[z1,z2,z3,z4,z1117,z6]),(0,[z1,z2,z3,z4,z6,z1118]),(0,[z1119,z1,z2,z3,z160,z6])],[(0,[z1,z2,z3,z1120,z4,z6]),(0,[z1,z11,z2,z266,z4,z6]),(0,[z1,z32,z2,z3,z4,z294]),(0,[z1,z2,z3,z4,z1121,z6]),(0,[z1,z2,z3,z4,z336,z6]),(0,[z1122,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1123,z5,z6]),(0,[z1,z2,z3,z4,z5,z1124]),(0,[z1,z1125,z2,z3,z4,z6])],[(0,[z20,z2,z3,z105,z220,z6]),(0,[z1,z2,z3,z4,z6,z1126]),(0,[z745,z1,z2,z3,z5,z6]),(0,[z1127,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1128,z6]),(0,[z43,z1,z2,z3,z160,z6])],[(0,[z1,z74,z3,z4,z30,z6]),(0,[z1,z1129,z3,z4,z5,z6]),(0,[z1,z1130,z2,z3,z4,z294]),(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z3,z1131,z4,z6]),(0,[z1,z2,z3,z1132,z4,z6]),(0,[z1,z2,z3,z4,z1133,z6])],[(0,[z1,z12,z3,z81,z30,z6]),(0,[z1,z130,z2,z3,z4,z181]),(0,[z114,z1,z2,z3,z160,z6])],[(0,[z1,z2,z3,z4,z1134,z6]),(0,[z1,z12,z3,z81,z393,z6]),(0,[z1,z3,z4,z5,z720,z25]),(0,[z99,z1,z32,z3,z4,z6]),(0,[z1135,z11,z2,z3,z4,z6])],[(0,[z1,z86,z3,z4,z34,z6]),(0,[z1,z2,z3,z4,z1136,z6]),(0,[z1,z2,z3,z4,z1137,z6]),(0,[z1,z2,z3,z4,z5,z1138]),(0,[z149,z1,z208,z4,z34,z6])]],
   [[(0,[z20,z2,z3,z5,z303,z6]),(0,[z1,z2,z3,z4,z357,z6]),(0,[z1135,z2,z3,z4,z5,z6]),(0,[z1,z2,z1139,z4,z5,z6]),(0,[z1,z11,z2,z4,z6,z337])],[(0,[z1,z2,z3,z1140,z4,z6]),(0,[z89,z1,z130,z2,z3,z6]),(0,[z89,z1,z2,z3,z160,z6]),(0,[z1,z1141,z2,z3,z4,z6]),(0,[z1,z2,z1142,z3,z4,z6]),(0,[z1,z1143,z2,z3,z4,z6])],[(0,[z1,z1144,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1145,z6]),(0,[z1,z2,z3,z30,z57,z6]),(0,[z149,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z1146,z4,z6]),(0,[z1,z2,z3,z4,z1147,z6]),(0,[z1,z2,z3,z4,z338,z6]),(0,[z99,z1,z3,z4,z30,z6]),(0,[z1,z11,z2,z3,z4,z397]),(0,[z96,z297,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z1148,z6]),(0,[z33,z2,z3,z4,z5,z40]),(0,[z1,z2,z3,z4,z1149,z6]),(0,[z1,z2,z3,z4,z1150,z6])],[(0,[z1,z86,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z106,z6]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z1,z2,z35,z236,z34,z6]),(0,[z1,z2,z3,z160,z103,z6]),(0,[z29,z1,z4,z5,z226,z117]),(0,[z1,z251,z3,z4,z77,z6])],[(0,[z1,z1151,z3,z4,z5,z6]),(0,[z1,z2,z266,z4,z220,z6]),(0,[z1,z54,z2,z3,z34,z6]),(0,[z1,z2,z3,z4,z1152,z6]),(0,[z1,z2,z3,z4,z1153,z6]),(0,[z1,z2,z3,z1154,z160,z6])],[(0,[z1,z2,z3,z1155,z5,z6]),(0,[z1,z74,z3,z4,z396,z6]),(0,[z1,z2,z21,z4,z5,z166]),(0,[z1,z54,z2,z3,z5,z97]),(0,[z1,z2,z3,z4,z1156,z6])],[(0,[z1,z2,z3,z4,z1157,z6]),(0,[z1,z2,z3,z783,z57,z6]),(0,[z1,z2,z3,z4,z779,z6]),(0,[z1,z32,z2,z3,z4,z229]),(0,[z1,z2,z3,z111,z30,z125])]],
   [[(0,[z31,z2,z607,z4,z5,z6]),(0,[z1,z2,z3,z1158,z5,z6]),(0,[z187,z1,z2,z3,z30,z6]),(1,[z2,z3,z4,z816,z6]),(0,[z1,z2,z3,z1159,z4,z6]),(0,[z1,z2,z3,z931,z5,z6]),(0,[z1,z46,z2,z3,z30,z125]),(0,[z1,z2,z3,z111,z160,z6])],[(0,[z1,z1160,z2,z3,z4,z6]),(0,[z1,z2,z3,z1060,z4,z6]),(0,[z1,z2,z3,z160,z6,z117])],[(0,[z1161,z1,z2,z3,z4,z6]),(0,[z20,z2,z21,z105,z5,z6]),(0,[z1,z2,z3,z4,z1063,z6]),(0,[z1,z2,z3,z4,z1162,z6]),(0,[z129,z1,z3,z4,z34,z25]),(0,[z1163,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z160,z319,z6])],[(0,[z297,z2,z3,z4,z5,z40]),(0,[z1,z2,z1164,z4,z5,z6]),(0,[z29,z1,z2,z4,z5,z809])],[(0,[z1,z11,z2,z3,z4,z6]),(0,[z67,z1,z130,z2,z3,z4]),(0,[z1,z2,z3,z214,z5,z273]),(0,[z1,z725,z2,z3,z108,z6]),(0,[z1,z2,z3,z4,z6,z182])],[(0,[z1,z2,z3,z220,z30,z6]),(0,[z1,z3,z4,z5,z61,z273]),(0,[z1,z11,z2,z3,z452,z4]),(0,[z1,z130,z2,z3,z111,z6])],[(0,[z1,z1165,z2,z3,z4,z6]),(0,[z149,z1,z208,z4,z5,z273]),(0,[z1,z2,z155,z3,z160,z6])],[(0,[z1,z2,z3,z4,z30,z6]),(0,[z1,z1166,z2,z3,z4,z6]),(0,[z1,z2,z266,z4,z34,z6]),(0,[z170,z1,z2,z3,z30,z6]),(0,[z1,z7,z3,z4,z93,z6]),(0,[z1,z2,z3,z214,z459,z6]),(0,[z1,z1167,z2,z3,z4,z6]),(0,[z1,z2,z1168,z3,z4,z6]),(0,[z1,z2,z3,z584,z30,z6])]],
   [[(0,[z1,z1169,z2,z3,z4,z6]),(0,[z1,z1170,z2,z3,z5,z6]),(0,[z33,z183,z2,z3,z4,z40]),(0,[z1,z1171,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z393,z6]),(0,[z1,z2,z3,z292,z30,z6]),(0,[z1,z2,z3,z1172,z4,z6]),(0,[z1,z2,z227,z186,z4,z123]),(0,[z2,z3,z4,z34,z6,z258])],[(0,[z1,z1173,z2,z3,z4,z6]),(0,[z1,z2,z1174,z3,z4,z6]),(0,[z89,z2,z3,z39,z5,z6]),(0,[z1,z74,z3,z4,z5,z294]),(0,[z1,z11,z2,z3,z53,z6]),(0,[z216,z2,z3,z68,z5,z6])],[(0,[z1,z2,z3,z4,z1175,z6]),(0,[z1,z2,z3,z4,z1176,z6]),(0,[z1,z2,z3,z4,z1177,z6]),(0,[z1,z2,z3,z160,z236,z6])],[(0,[z1,z2,z1178,z4,z5,z6]),(0,[z1,z2,z3,z1179,z5,z6]),(0,[z1,z2,z3,z4,z1180,z6])],[(0,[z1,z2,z3,z4,z5,z1181]),(0,[z89,z483,z2,z3,z39,z6]),(0,[z1,z910,z2,z3,z111,z6]),(0,[z1,z2,z3,z97,z6,z182])],[(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z2,z3,z4,z212,z6]),(0,[z1,z2,z3,z4,z1183,z6]),(0,[z1,z32,z2,z3,z340,z6])],[(0,[z1,z2,z3,z4,z5,z1184]),(0,[z1,z2,z3,z4,z143,z6])],[(0,[z1,z2,z3,z4,z1185,z6]),(0,[z1,z2,z3,z4,z411,z6]),(0,[z1,z2,z3,z111,z5,z70])]],
   [[(0,[z1,z2,z3,z478,z30,z6]),(0,[z1,z2,z3,z39,z160,z6]),(0,[z1,z2,z3,z4,z6,z1186]),(0,[z1,z130,z2,z3,z4,z34]),(0,[z297,z2,z3,z4,z34,z6])],[(0,[z1,z1187,z2,z3,z4,z6]),(0,[z1,z1188,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1136,z166]),(0,[z1,z2,z3,z4,z1189,z6]),(0,[z1190,z1,z2,z3,z4,z6]),(0,[z1,z60,z3,z4,z291,z61])],[(0,[z1,z2,z3,z1191,z4,z6]),(0,[z1,z11,z60,z3,z4,z61]),(0,[z1,z2,z3,z55,z160,z6])],[(0,[z48,z2,z51,z4,z5,z6]),(0,[z1,z2,z3,z53,z34,z6]),(0,[z1,z2,z3,z4,z1192,z6]),(0,[z1,z12,z3,z709,z5,z6]),(0,[z1,z2,z3,z508,z4,z6]),(0,[z1,z2,z3,z4,z6,z1193]),(0,[z1194,z2,z3,z4,z5,z6])],[(0,[z1,z1195,z3,z4,z5,z6]),(0,[z2,z3,z730,z105,z5,z6]),(0,[z89,z11,z2,z3,z39,z6]),(0,[z101,z285,z2,z3,z4,z6]),(0,[z1,z2,z3,z481,z4,z34]),(0,[z54,z2,z3,z5,z122,z6]),(0,[z1,z2,z3,z4,z1196,z6]),(0,[z1,z2,z3,z4,z459,z229]),(0,[z1,z2,z3,z4,z1197,z6]),(0,[z1,z130,z2,z3,z4,z145])],[(0,[z1,z2,z3,z734,z4,z5]),(0,[z1,z2,z3,z4,z336,z229]),(0,[z149,z1,z4,z5,z217,z6]),(0,[z75,z1,z3,z76,z30,z6]),(0,[z1,z2,z3,z4,z1198,z6]),(0,[z1,z11,z1199,z3,z4,z6])],[(0,[z1,z2,z3,z1200,z5,z6]),(0,[z1,z2,z3,z1201,z4,z6]),(0,[z1,z2,z3,z1202,z5,z6]),(0,[z149,z1,z11,z208,z4,z6]),(0,[z1,z1203,z2,z3,z4,z5]),(0,[z1,z11,z2,z3,z111,z97]),(0,[z1,z11,z796,z3,z4,z6]),(0,[z1,z11,z2,z3,z813,z6])],[(0,[z50,z2,z51,z4,z5,z6]),(0,[z31,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z4,z1204,z6]),(0,[z1,z2,z3,z215,z732,z6]),(0,[z1205,z1,z2,z4,z5,z6]),(0,[z129,z1,z24,z3,z4,z25]),(0,[z1,z2,z3,z4,z1206,z6])]],
   [[(0,[z0,z2,z3,z4,z228,z6]),(0,[z1,z2,z3,z4,z751,z145])],[(0,[z1,z2,z3,z4,z1207,z6]),(0,[z348,z1,z2,z3,z160,z6])],[(0,[z1,z11,z2,z3,z4,z294]),(0,[z617,z2,z3,z4,z9,z6]),(0,[z1,z11,z2,z3,z4,z535])],[(0,[z1,z1160,z2,z3,z4,z166]),(0,[z1,z2,z794,z4,z5,z6]),(0,[z129,z290,z1,z4,z5,z6]),(0,[z1,z11,z2,z3,z4,z468]),(0,[z829,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z294]),(0,[z33,z1,z130,z2,z3,z4]),(0,[z1,z2,z838,z4,z5,z6]),(0,[z1,z1199,z3,z4,z5,z6]),(0,[z1,z2,z362,z4,z103,z6]),(0,[z187,z285,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1208,z6]),(0,[z33,z2,z3,z4,z5,z731]),(0,[z1,z2,z3,z214,z30,z6]),(0,[z147,z1,z2,z3,z160,z6]),(0,[z1,z2,z3,z4,z1209,z6]),(0,[z1,z315,z2,z3,z111,z97])],[(0,[z165,z71,z3,z4,z5,z6]),(0,[z1,z3,z881,z4,z5,z6]),(0,[z290,z1,z32,z2,z4,z6]),(0,[z1,z910,z2,z3,z30,z6]),(0,[z1,z11,z2,z3,z4,z64]),(0,[z1,z2,z3,z5,z97,z846])],[(0,[z1,z32,z2,z3,z4,z6]),(0,[z50,z2,z51,z4,z143,z6]),(0,[z1,z2,z3,z4,z1210,z6]),(0,[z1,z86,z3,z4,z30,z6]),(0,[z20,z1,z74,z3,z30,z6]),(0,[z1,z2,z3,z68,z459,z6]),(0,[z1,z2,z3,z1211,z5,z6]),(0,[z1,z2,z3,z4,z5,z1212])]],
   [[(0,[z1,z2,z3,z4,z5,z1213]),(0,[z1,z2,z3,z4,z1214,z6]),(0,[z101,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z68,z336,z6]),(0,[z903,z32,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1215]),(0,[z1,z2,z3,z4,z370,z6]),(0,[z1,z1216,z2,z3,z4,z6]),(0,[z89,z1,z2,z3,z30,z6]),(0,[z1,z1130,z2,z3,z4,z6]),(0,[z1,z1217,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z166]),(0,[z196,z2,z3,z4,z9,z6]),(0,[z196,z1,z2,z3,z53,z6]),(0,[z1,z2,z3,z4,z1218,z6]),(0,[z1,z1219,z2,z3,z4,z6]),(0,[z29,z1,z2,z4,z30,z117]),(0,[z1,z2,z3,z4,z461,z6])],[(0,[z72,z188,z3,z4,z34,z6]),(0,[z298,z1,z2,z3,z34,z6]),(0,[z1,z1220,z2,z3,z4,z6]),(0,[z1,z1221,z2,z3,z4,z6]),(0,[z1084,z2,z3,z4,z5,z6])],[(0,[z1,z1222,z3,z4,z5,z6]),(0,[z1,z2,z881,z4,z5,z6]),(0,[z1,z2,z3,z520,z30,z6]),(0,[z32,z2,z3,z4,z6,z258])],[(0,[z1,z2,z1223,z3,z4,z6]),(0,[z1,z2,z3,z4,z1224,z6]),(0,[z1,z2,z3,z30,z6,z671]),(0,[z298,z196,z2,z3,z9,z6]),(0,[z1,z54,z183,z2,z3,z6]),(0,[z1225,z2,z3,z4,z5,z6]),(0,[z75,z1,z11,z3,z76,z6]),(0,[z1,z382,z2,z3,z4,z34]),(0,[z1,z32,z3,z4,z6,z226]),(0,[z1,z2,z1226,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1227,z6]),(0,[z20,z2,z3,z105,z30,z6]),(0,[z1,z2,z3,z4,z1228,z6]),(0,[z1,z107,z2,z3,z160,z6]),(0,[z1,z2,z4,z411,z6,z337])],[(0,[z1,z2,z3,z4,z34,z47]),(0,[z129,z1,z32,z3,z4,z25]),(0,[z1,z2,z3,z4,z1229,z6])],[(0,[z1,z2,z3,z4,z396,z294]),(0,[z1,z11,z2,z3,z4,z229]),(0,[z1,z2,z3,z4,z1230,z6]),(0,[z1,z2,z3,z1231,z160,z6])]],
   [[(0,[z1,z2,z3,z4,z1232,z6]),(0,[z1,z1233,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1234,z6]),(0,[z1,z284,z3,z4,z93,z6]),(0,[z1,z2,z3,z111,z30,z6]),(0,[z2,z3,z4,z30,z6,z258])],[(0,[z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z1235,z5,z6]),(0,[z1,z2,z3,z4,z1236,z6])],[(0,[z1,z2,z78,z3,z53,z6]),(0,[z150,z2,z3,z4,z5,z273]),(0,[z1,z2,z3,z4,z301,z6])],[(0,[z1,z11,z2,z3,z4,z627]),(0,[z1,z2,z1237,z3,z4,z6])],[(0,[z20,z590,z2,z3,z5,z6]),(0,[z1,z1238,z2,z3,z4,z6]),(0,[z1,z32,z54,z2,z3,z6]),(0,[z1,z2,z4,z5,z123,z809])],[(1,[z1,z2,z3,z30,z294]),(0,[z101,z1,z2,z3,z53,z6]),(0,[z1,z2,z3,z53,z93,z6]),(0,[z150,z2,z3,z4,z459,z6]),(0,[z1,z2,z3,z4,z1239,z6]),(0,[z1,z11,z2,z3,z992,z6])],[(0,[z1,z2,z3,z4,z1240,z6]),(0,[z216,z2,z3,z4,z34,z6]),(0,[z1241,z2,z3,z4,z5,z6]),(0,[z1,z2,z244,z3,z4,z6]),(0,[z1242,z1,z2,z3,z4,z6]),(0,[z309,z2,z3,z4,z495,z6])],[(0,[z1,z2,z3,z4,z1243,z6]),(0,[z1,z2,z266,z4,z30,z6]),(1,[z2,z3,z730,z5,z6]),(0,[z1,z892,z2,z3,z4,z6]),(0,[z1,z2,z1244,z3,z4,z6]),(0,[z1,z2,z4,z5,z6,z1245])]],
   [[(0,[z2,z3,z4,z5,z6,z1246]),(0,[z1,z46,z2,z3,z254,z125])],[(0,[z1,z2,z3,z4,z1247,z6]),(0,[z2,z3,z4,z816,z5,z6]),(0,[z1248,z2,z3,z4,z5,z6]),(0,[z1249,z1,z2,z4,z5,z6]),(0,[z1,z1250,z2,z3,z4,z6]),(0,[z1,z2,z3,z30,z6,z252])],[(0,[z1,z2,z3,z160,z6,z40]),(0,[z1251,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z4,z5,z123]),(0,[z762,z32,z2,z3,z4,z6]),(0,[z1,z11,z2,z3,z160,z34]),(0,[z1,z2,z3,z160,z34,z6])],[(0,[z1252,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1253,z6]),(0,[z50,z32,z2,z51,z4,z6]),(0,[z1,z2,z3,z55,z4,z34])],[(0,[z1,z2,z1254,z4,z5,z6]),(0,[z1,z2,z1255,z3,z4,z6]),(0,[z1,z3,z4,z5,z6,z1256])],[(0,[z1,z1257,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1258]),(0,[z20,z1,z2,z3,z293,z6]),(0,[z1,z2,z3,z1259,z5,z6]),(0,[z187,z1,z2,z3,z53,z6]),(0,[z1,z2,z3,z68,z30,z6]),(0,[z1,z11,z2,z3,z340,z6])],[(0,[z1,z74,z3,z4,z5,z6]),(0,[z1,z2,z3,z852,z5,z6]),(0,[z1,z2,z3,z4,z1192,z229]),(0,[z99,z1,z3,z4,z5,z25]),(0,[z1,z2,z1260,z3,z4,z6]),(0,[z1,z11,z2,z3,z160,z145])],[(0,[z1,z2,z21,z4,z34,z6]),(0,[z290,z1,z2,z4,z5,z273]),(0,[z1,z12,z3,z81,z5,z6]),(0,[z1,z2,z3,z4,z1261,z6])]],
   [[(0,[z1,z2,z1262,z3,z4,z6]),(0,[z1263,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z466,z30,z6]),(0,[z118,z1,z2,z3,z160,z6])],[(0,[z1,z2,z3,z5,z1264,z6]),(0,[z1,z1265,z2,z3,z4,z6]),(0,[z1,z32,z2,z3,z4,z166]),(0,[z89,z2,z3,z730,z5,z6]),(0,[z1,z2,z3,z4,z1266,z6]),(0,[z1,z1267,z2,z3,z4,z6]),(0,[z1,z32,z2,z3,z706,z6]),(0,[z29,z1,z2,z568,z4,z117])],[(0,[z50,z1,z2,z3,z160,z6]),(0,[z20,z2,z3,z105,z5,z294]),(0,[z1,z82,z2,z3,z30,z6]),(0,[z1268,z2,z3,z4,z5,z6]),(1,[z297,z2,z3,z30,z6]),(0,[z1,z11,z2,z3,z1259,z6])],[(0,[z1,z2,z3,z1099,z5,z6]),(0,[z290,z1,z4,z5,z61,z6])],[(0,[z99,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1269,z6]),(0,[z1,z2,z3,z461,z160,z6]),(0,[z1,z315,z2,z3,z340,z6])],[(0,[z1,z18,z2,z3,z30,z6]),(0,[z20,z1,z2,z21,z30,z6]),(0,[z1,z11,z2,z3,z4,z543]),(0,[z216,z2,z3,z4,z5,z273]),(0,[z1,z2,z3,z4,z1270,z6]),(0,[z1,z2,z3,z4,z1271,z6]),(0,[z1,z130,z2,z3,z6,z125]),(0,[z1272,z1,z2,z3,z160,z6])],[(0,[z1,z46,z2,z3,z5,z294]),(0,[z89,z2,z3,z228,z30,z6]),(0,[z1,z2,z3,z30,z40,z125]),(0,[z1,z2,z3,z214,z1234,z6]),(0,[z1,z2,z26,z35,z236,z6]),(0,[z1,z2,z3,z4,z34,z140]),(0,[z1,z2,z3,z1273,z4,z6])],[(0,[z1,z2,z1274,z4,z5,z6]),(0,[z1,z483,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z30,z294]),(0,[z1,z2,z1275,z3,z4,z6]),(0,[z1,z2,z3,z1276,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z1277,z6]),(0,[z517,z2,z3,z4,z113,z6]),(0,[z1,z54,z2,z3,z1086,z6]),(0,[z150,z11,z2,z3,z4,z6]),(0,[z1,z2,z1278,z3,z4,z6]),(0,[z99,z1,z3,z4,z153,z6])],[(0,[z1,z1279,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z34,z273]),(0,[z1,z3,z709,z4,z5,z6]),(0,[z1,z2,z3,z735,z5,z6]),(0,[z1,z2,z3,z4,z5,z809]),(0,[z1,z2,z3,z4,z34,z70]),(0,[z814,z32,z2,z3,z4,z6]),(0,[z885,z11,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1280,z6]),(0,[z2,z3,z4,z5,z6,z863]),(0,[z1,z46,z2,z3,z5,z125])],[(0,[z1,z2,z3,z51,z160,z6]),(0,[z150,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z254,z4,z6]),(0,[z1,z2,z3,z340,z34,z6])],[(0,[z1,z2,z330,z236,z5,z6]),(0,[z20,z1,z2,z3,z891,z6]),(0,[z1,z32,z2,z3,z57,z6])],[(0,[z1,z2,z3,z1281,z4,z6]),(0,[z1,z2,z1282,z3,z4,z6]),(0,[z494,z2,z52,z4,z5,z6]),(0,[z33,z2,z3,z4,z5,z294]),(0,[z1,z2,z3,z597,z30,z6]),(0,[z99,z1,z3,z4,z5,z61]),(0,[z1,z2,z3,z601,z30,z6]),(0,[z1,z2,z3,z4,z1283,z6]),(0,[z1,z2,z3,z4,z1284,z6]),(0,[z1,z2,z3,z30,z6,z125]),(0,[z1,z2,z3,z30,z6,z263])],[(0,[z1,z2,z3,z1285,z5,z6]),(0,[z1,z2,z3,z4,z1286,z6]),(0,[z1,z2,z1287,z4,z5,z6]),(0,[z558,z89,z2,z3,z30,z6]),(0,[z1,z2,z3,z8,z160,z6])],[(0,[z1,z2,z3,z4,z1288,z6]),(0,[z1,z2,z1289,z4,z5,z6]),(0,[z1,z2,z3,z1290,z5,z6]),(0,[z1,z2,z3,z4,z5,z1291]),(0,[z1,z2,z3,z4,z1292,z6]),(0,[z1,z32,z2,z3,z318,z6]),(0,[z46,z2,z3,z5,z258,z125])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 511).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1021).take 331) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1352)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [511, 510, 331] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 62).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 62).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 129).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 206).take 50).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [62, 67, 77, 50] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_41460

theorem PEqualNP.Outside.L_meta_41460 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276811904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276811904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41460.solve