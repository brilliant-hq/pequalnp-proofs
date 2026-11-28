import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39885

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
  Nat.testBit (4276677288 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000c28194c050a50#64 ++ 0x8000c28194c050a5#64 ++ 0x601c78ffdc0f1fff#64 ++ 0x6601c78ffdc0f1ff#64 : BitVec 256),
   (0x0061934481b26525#64 ++ 0x00061934481b2652#64 ++ 0xf0e39f44e7f3e73e#64 ++ 0xef0e39f44e7f3e73#64 : BitVec 256),
   (0x2702c5863058b186#64 ++ 0x02702c5863058b18#64 ++ 0xef03e787387cf9cd#64 ++ 0xfef03e787387cf9c#64 : BitVec 256),
   (0x8bb406e83e80de08#64 ++ 0x08bb406e83e80de0#64 ++ 0xbffc07f83f80fe0b#64 ++ 0xfbffc07f83f80fe0#64 : BitVec 256),
   (0x5ddf78003f6f0000#64 ++ 0x05ddf78003f6f000#64 ++ 0xdffff8003fff0007#64 ++ 0xfdffff8003fff000#64 : BitVec 256),
   (0x1efbfff7c0000000#64 ++ 0x11efbfff7c000000#64 ++ 0x1fffffffc000000f#64 ++ 0xd1fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [10, 6]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000804400 0x0000000000080440 0xa00000002780e600 0x2a00000002780e60

def z1 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x601c78ffdc0f1fff 0x6601c78ffdc0f1ff

def z2 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e39f44e7f3e73e 0xef0e39f44e7f3e73

def z3 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03e787387cf9cd 0xfef03e787387cf9c

def z4 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff8003fff0007 0xfdffff8003fff000

def z5 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xa00000003f80fe00 0x2a00000003f80fe0

def z6 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07f83f80fe0b 0xfbffc07f83f80fe0

def z7 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x001c1878c4030632 0x0001c1878c403063

def z8 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffffffc000000f 0xd1fffffffc000000

def z9 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff8ffffff1fff 0xffffff8ffffff1ff

def z10 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1ffc07f80000000b 0xd1ffc07f80000000

def z11 : W := mkw 0x0af197e481b26525 0x00af197e481b2652 0xffff9ffce7f3e73f 0xfffff9ffce7f3e73

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000000180c19c0 0x260000000180c19c

def z13 : W := mkw 0x0008281140050050 0x8000828114005005 0x40007807c00f01f4 0x040007807c00f01f

def z14 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe3800023f00000 0x99fe3800023f0000

def z15 : W := mkw 0x0200858600000000 0x0020085860000000 0x0000078700000008 0x0000007870000000

def z16 : W := mkw 0x1edbfd8600000000 0x01edbfd860000000 0x1fffff870000000f 0xd1fffff870000000

def z17 : W := mkw 0x144bf917c0000000 0x1144bf917c000000 0x001ff8ffc000000f 0x4001ff8ffc000000

def z18 : W := mkw 0x7ddff9063f7f2186 0x07ddff9063f7f218 0xdffff8073fff01c7 0xfdffff8073fff01c

def z19 : W := mkw 0x0000001940000a50 0x80000001940000a5 0x200000ffc0001ff8 0x0200000ffc0001ff

def z20 : W := mkw 0x0502400030480000 0x0050240003048000 0x0f006000180c0001 0x10f006000180c000

def z21 : W := mkw 0x2200048200009082 0x0220004820000908 0x00000083000018c0 0x000000083000018c

def z22 : W := mkw 0x004d38194d270a50 0x8004d38194d270a5 0xf0fff8ffffff1fff 0xef0fff8ffffff1ff

def z23 : W := mkw 0x8bf597ecbfb2ff2d 0x08bf597ecbfb2ff2 0xffff9ffcfff3ff3f 0xfffff9ffcfff3ff3

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z25 : W := mkw 0x270eed863c5db186 0x0270eed863c5db18 0xef1fff873c7ff9cf 0xfef1fff873c7ff9c

def z26 : W := mkw 0x0061934480000000 0x0006193448000000 0x10e39f44c000000e 0xc10e39f44c000000

def z27 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xffffffffe7f3e73f 0xfffffffffe7f3e73

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x60001844c403073e 0x660001844c403073

def z29 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x90e3870023f0e000 0x890e3870023f0e00

def z30 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c60bb00000001 0x10f1c60bb0000000

def z31 : W := mkw 0x0041100001220000 0x0004110000122000 0x10e0180007830002 0x010e018000783000

def z32 : W := mkw 0x0000000001b26525 0x00000000001b2652 0xe000000027f3e730 0x2e000000027f3e73

def z33 : W := mkw 0x2702448230489082 0x0270244823048908 0x0f006083180c18c1 0x10f006083180c18c

def z34 : W := mkw 0x822087ec8090ff2d 0x0822087ec8090ff2 0x200007fcc000ff38 0x0200007fcc000ff3

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001840c4030632 0x000001840c403063

def z36 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0x9fe007002380e000 0x99fe007002380e00

def z37 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff844ffff073f 0xffffff844ffff073

def z38 : W := mkw 0x0ab006e000804400 0x00ab006e00080440 0xbffc07f82780e60b 0xfbffc07f82780e60

def z39 : W := mkw 0x2763d7c6b1faf5a7 0x02763d7c6b1faf5a 0xffe3ffc7ffffffff 0xfffe3ffc7fffffff

def z40 : W := mkw 0x59dd38003f270000 0x059dd38003f27000 0x9ffc18003f830003 0xf9ffc18003f83000

def z41 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0xbfe007402780e60a 0xfbfe007402780e60

def z42 : W := mkw 0x000400080c050a50 0x8000400080c050a5 0x600000001c0f1ff0 0x2600000001c0f1ff

def z43 : W := mkw 0x410400003f6f0000 0x0410400003f6f000 0xc00000003fff0000 0x2c00000003fff000

def z44 : W := mkw 0x0041910481322125 0x0004191048132212 0x40039804c0730134 0x040039804c073013

def z45 : W := mkw 0x0061124081a24421 0x00061124081a2442 0x10e01840c7830632 0x010e01840c783063

def z46 : W := mkw 0x9ffffffffe80de08 0x19ffffffffe80de0 0xbfffffffff80fe0f 0xfbfffffffff80fe0

def z47 : W := mkw 0x5ddff917ff6f0000 0x15ddff917ff6f000 0xdffff807ffff0007 0xfdffff807ffff000

def z48 : W := mkw 0x000400000c050000 0x0000400000c05000 0x400000001c0f0000 0x2400000001c0f000

def z49 : W := mkw 0xa22087ee0090ff8e 0x0a22087ee0090ff8 0x200007ff0000ffc8 0x0200007ff0000ffc

def z50 : W := mkw 0xafb6c7ee3ed8ff8e 0x0afb6c7ee3ed8ff8 0xffffe7ff3ffcffcf 0xfffffe7ff3ffcffc

def z51 : W := mkw 0x58d1100003220000 0x058d110000322000 0x10e0000003800000 0x010e000000380000

def z52 : W := mkw 0x0000000001322125 0x0000000000132212 0x4000000000730130 0x0400000000073013

def z53 : W := mkw 0x589c28000e050000 0x0589c28000e05000 0x001c000000000000 0x0001c00000000000

def z54 : W := mkw 0x7fdf7c823f6f9082 0x07fdf7c823f6f908 0xdffff8833fff18c7 0xfdffff8833fff18c

def z55 : W := mkw 0x1ef3d7e681b26525 0x11ef3d7e681b2652 0xffe39f44e7f3e73e 0xfffe39f44e7f3e73

def z56 : W := mkw 0x554f78003f6f0000 0x0554f78003f6f000 0xc003f8003fff0004 0x2c003f8003fff000

def z57 : W := mkw 0xdff356e033ead408 0x0dff356e033ead40 0x9fe3870023f0e000 0x99fe3870023f0e00

def z58 : W := mkw 0x270eed9f7c5dbbd6 0x8270eed9f7c5dbbd 0xef1ffffffc7fffff 0xfef1ffffffc7ffff

def z59 : W := mkw 0x8b9c2cb97e059a58 0x88b9c2cb97e059a5 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z60 : W := mkw 0x002402480c804e00 0x0002402480c804e0 0xb0fc07f83f80fe0b 0xeb0fc07f83f80fe0

def z61 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff878ffff0637 0xfdffff878ffff063

def z62 : W := mkw 0x5d9e68003e4d0000 0x05d9e68003e4d000 0x0f1c6000180c0001 0x10f1c6000180c000

def z63 : W := mkw 0x2743d586317ab186 0x02743d586317ab18 0xffe3ff873ffff9cf 0xfffe3ff873ffff9c

def z64 : W := mkw 0x0008281140050050 0x8000828114005005 0x401c78ffc00f01ff 0x4401c78ffc00f01f

def z65 : W := mkw 0x026197f7c0000000 0x1026197f7c000000 0x10e39fffc000000e 0xc10e39fffc000000

def z66 : W := mkw 0x0020834480906525 0x0002083448090652 0x000007000000e000 0x0000007000000e00

def z67 : W := mkw 0x1effffffcc000a00 0x11effffffcc000a0 0x3fffffffdc001e0f 0xf3fffffffdc001e0

def z68 : W := mkw 0x1efbfff7c1322125 0x11efbfff7c132212 0x5fffffffc073013f 0xd5fffffffc073013

def z69 : W := mkw 0x5ddff904bf7f2125 0x05ddff904bf7f212 0xdffff804ffff0137 0xfdffff804ffff013

def z70 : W := mkw 0x410c28003f6f0000 0x0410c28003f6f000 0xc01c78003fff0007 0x6c01c78003fff000

def z71 : W := mkw 0x006dbb448db76525 0x0006dbb448db7652 0xf0ffff44ffffe73f 0xef0ffff44ffffe73

def z72 : W := mkw 0x0000001140000050 0x8000000114000005 0x00000007c00001f0 0x000000007c00001f

def z73 : W := mkw 0x0300048030009000 0x0030004803000900 0xaf0007803800f809 0xfaf0007803800f80

def z74 : W := mkw 0x5df3d344b3fa6525 0x05df3d344b3fa652 0x9fe3870023f0e000 0x99fe3870023f0e00

def z75 : W := mkw 0x8bb406f97e80de58 0x88bb406f97e80de5 0xbffc07ffff80fffb 0xfbffc07ffff80fff

def z76 : W := mkw 0x5dfffb44bfff6525 0x05dfffb44bfff652 0xffffff44ffffe73f 0xfffffff44ffffe73

def z77 : W := mkw 0x2763d7c6b1faf5a7 0x02763d7c6b1faf5a 0x9fe3870023f0e000 0x99fe3870023f0e00

def z78 : W := mkw 0x8bf197e4b3b2f52d 0x08bf197e4b3b2f52 0x9fe3870023f0e000 0x99fe3870023f0e00

def z79 : W := mkw 0x1ddb780030480000 0x01ddb78003048000 0xdffff800387c0007 0xfdffff800387c000

def z80 : W := mkw 0x822006e80080de08 0x0822006e80080de0 0x200007f80000fe08 0x0200007f80000fe0

def z81 : W := mkw 0xabb487ee3e90ff8e 0x0abb487ee3e90ff8 0xbffc07ff3f80ffcb 0xfbffc07ff3f80ffc

def z82 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9fff980027f30002 0x99fff980027f3000

def z83 : W := mkw 0x7fdffd863f7fb186 0x07fdffd863f7fb18 0xffffff873ffff9cf 0xfffffff873ffff9c

def z84 : W := mkw 0x8b9404a83e009a08 0x08b9404a83e009a0 0x0f1c00b818001801 0x10f1c00b81800180

def z85 : W := mkw 0x0041100001220000 0x0004110000122000 0xd0e3980027f30006 0xed0e3980027f3000

def z86 : W := mkw 0x5d9e68003e4d0000 0x05d9e68003e4d000 0x9ffc60003f8c0003 0xf9ffc60003f8c000

def z87 : W := mkw 0x8bbc2ef97e85de58 0x88bbc2ef97e85de5 0xfffc7fffff8fffff 0xffffc7fffff8ffff

def z88 : W := mkw 0x410400003fff6525 0x0410400003fff652 0xe00000003fffe730 0x2e00000003fffe73

def z89 : W := mkw 0x0000001940000a50 0x80000001940000a5 0x600060ffd80c1ffd 0x6600060ffd80c1ff

def z90 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fff9f78c0000002 0x91fff9f78c000000

def z91 : W := mkw 0x0990000032000000 0x0099000003200000 0x9fe0000023800000 0x99fe000002380000

def z92 : W := mkw 0x0020024000804400 0x0002002400080440 0xb0e007402780e60a 0xeb0e007402780e60

def z93 : W := mkw 0x9ffffffffe009a08 0x19ffffffffe009a0 0x1fffffffd800180f 0xd1fffffffd800180

def z94 : W := mkw 0x5cdf78000f270000 0x05cdf78000f27000 0x1ffff80007830007 0xd1ffff8000783000

def z95 : W := mkw 0xdfff7ee03fefd408 0x0dfff7ee03fefd40 0xdfffff003fffe007 0xfdfffff003fffe00

def z96 : W := mkw 0x0702448030489000 0x0070244803048900 0xef03e780387cf80d 0xfef03e780387cf80

def z97 : W := mkw 0x58fd3a71cf270000 0x158fd3a71cf27000 0x10fc1878c7830002 0x010fc1878c783000

def z98 : W := mkw 0x220085860010b186 0x0220085860010b18 0x200007870000f9c8 0x0200007870000f9c

def z99 : W := mkw 0x3efbfff7c010b186 0x13efbfff7c010b18 0x3fffffffc000f9cf 0xd3fffffffc000f9c

def z100 : W := mkw 0x030085843010b104 0x0030085843010b10 0xef0387843870f90d 0xfef0387843870f90

def z101 : W := mkw 0xc10400083fefde08 0x0c10400083fefde0 0xe00000003ffffe00 0x2e00000003ffffe0

def z102 : W := mkw 0x1ef3d7e681b26525 0x11ef3d7e681b2652 0x9fe3870023f0e000 0x99fe3870023f0e00

def z103 : W := mkw 0x7ddf78003f7fb186 0x07ddf78003f7fb18 0xfffff8003ffff9c7 0xffffff8003ffff9c

def z104 : W := mkw 0x0061124001a24400 0x00061124001a2440 0xf0e39f4027f3e60e 0xef0e39f4027f3e60

def z105 : W := mkw 0x5ddf78083f6f0a50 0x85ddf78083f6f0a5 0xfffff8003fff1ff7 0xffffff8003fff1ff

def z106 : W := mkw 0x0008281140000000 0x0000828114000000 0x001c78ffc000000f 0x4001c78ffc000000

def z107 : W := mkw 0x022087f7c0000000 0x1022087f7c000000 0x000007ffc0000008 0x0000007ffc000000

def z108 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xd0e39f04e3f3e134 0x8d0e39f04e3f3e13

def z109 : W := mkw 0x544b7800016f0000 0x0544b7800016f000 0x4003f800007f0004 0x04003f800007f000

def z110 : W := mkw 0x144bf917c1322125 0x1144bf917c132212 0x4003f807c0730134 0x04003f807c073013

def z111 : W := mkw 0x0d9640003e480000 0x00d9640003e48000 0xdfffe0003ffc0007 0xfdfffe0003ffc000

def z112 : W := mkw 0x5dfffb44bfff6525 0x05dfffb44bfff652 0xdfffff003fffe007 0xfdfffff003fffe00

def z113 : W := mkw 0x1e9244a200000000 0x11e9244a20000000 0x0f00000000000000 0x10f0000000000000

def z114 : W := mkw 0x3ffbfff7f058b186 0x13ffbfff7f058b18 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z115 : W := mkw 0x0061124081a24421 0x00061124081a2442 0xd0e39840e7f30636 0xed0e39840e7f3063

def z116 : W := mkw 0x1e9e6cbb4c050a50 0x91e9e6cbb4c050a5 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z117 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fe3870000000000 0x91fe387000000000

def z118 : W := mkw 0x0000810400102104 0x0000081040010210 0xe00387042070e10c 0xee00387042070e10

def z119 : W := mkw 0x400400000f270000 0x0400400000f27000 0x0000000007830000 0x0000000000783000

def z120 : W := mkw 0x0602448200000000 0x0060244820000000 0x0f00608300000001 0x10f0060830000000

def z121 : W := mkw 0xdfffffffffefde08 0x1dfffffffffefde0 0xfffffffffffffe0f 0xffffffffffffffe0

def z122 : W := mkw 0x1cdb781140000000 0x01cdb78114000000 0x1ffff8ffc000000f 0xd1ffff8ffc000000

def z123 : W := mkw 0x18f93a71c0000000 0x118f93a71c000000 0x10fc1878c0000002 0x010fc1878c000000

def z124 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1fe0070000000000 0x91fe007000000000

def z125 : W := mkw 0x0ab087f7c0000000 0x10ab087f7c000000 0x1ffc07ffc000000b 0xd1ffc07ffc000000

def z126 : W := mkw 0x2402c10600582186 0x02402c1060058218 0x0003800000700000 0x0000380000070000

def z127 : W := mkw 0x9ff3d7e6b280d408 0x19ff3d7e6b280d40 0x9fe387002380e000 0x99fe387002380e00

def z128 : W := mkw 0x0602c58600000000 0x00602c5860000000 0x0f03870000000000 0x90f0387000000000

def z129 : W := mkw 0x3ffbfff7f1faf5a7 0x13ffbfff7f1faf5a 0xffffffffffffffff 0xffffffffffffffff

def z130 : W := mkw 0x0020834480906525 0x0002083448090652 0x20000744c000e738 0x020000744c000e73

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000040000010c 0x6600000040000010

def z132 : W := mkw 0x006d3a59cda74e71 0x8006d3a59cda74e7 0x10fc1878c7830632 0x010fc1878c783063

def z133 : W := mkw 0x8bb406e83e85de58 0x88bb406e83e85de5 0xfffc07f83f8ffffb 0xffffc07f83f8ffff

def z134 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x8f0387002070e000 0x98f0387002070e00

def z135 : W := mkw 0x2100000030489082 0x0210000003048908 0x00000000180c18c0 0x000000000180c18c

def z136 : W := mkw 0x004d38000d270000 0x0004d38000d27000 0xd0fff8003fff0007 0xed0fff8003fff000

def z137 : W := mkw 0x2763d7c6b1faf5a7 0x02763d7c6b1faf5a 0xffe3e7873bfcf9cd 0xfffe3e7873bfcf9c

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x60006087180c19cd 0x660006087180c19c

def z139 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff8bb3fff18c7 0xfdffff8bb3fff18c

def z140 : W := mkw 0x1cdb780000000000 0x01cdb78000000000 0x1ffff80000000007 0xd1ffff8000000000

def z141 : W := mkw 0x000c28000c050000 0x0000c28000c05000 0x401c78001c0f0007 0x6401c78001c0f000

def z142 : W := mkw 0x144bf917c0000000 0x1144bf917c000000 0x0003f807c0000004 0x00003f807c000000

def z143 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x201c18ffc4031ffa 0x0201c18ffc4031ff

def z144 : W := mkw 0x0563d344b1fa6525 0x00563d344b1fa652 0xffe3ff44ffffe73f 0xfffe3ff44ffffe73

def z145 : W := mkw 0x2443d106817a21a7 0x02443d106817a21a 0x4003f807c07f01f4 0x04003f807c07f01f

def z146 : W := mkw 0x09d510003f220000 0x009d510003f22000 0xdfff98003ff30007 0xfdfff98003ff3000

def z147 : W := mkw 0x000ca91d4c152b54 0x8000ca91d4c152b5 0xe01ffffffc7fffff 0xee01ffffffc7ffff

def z148 : W := mkw 0x5d9e68003e4d0000 0x05d9e68003e4d000 0x4f1c78001c0f0007 0x74f1c78001c0f000

def z149 : W := mkw 0x7f9eed863e5db186 0x07f9eed863e5db18 0xef1fe787387cf9cd 0xfef1fe787387cf9c

def z150 : W := mkw 0x88b402680e804e08 0x088b402680e804e0 0x10fc007807800602 0x010fc00780780060

def z151 : W := mkw 0x000400080c050a50 0x8000400080c050a5 0x00000000180c18c0 0x000000000180c18c

def z152 : W := mkw 0x0602c58600102104 0x00602c5860010210 0xef03e7872070e10d 0xfef03e7872070e10

def z153 : W := mkw 0x089400000e000000 0x0089400000e00000 0x10fc000007800002 0x010fc00000780000

def z154 : W := mkw 0x774bfd86317fb186 0x0774bfd86317fb18 0xef03ff87387ff9cd 0xfef03ff87387ff9c

def z155 : W := mkw 0x5d9e68197e4d0a50 0x85d9e68197e4d0a5 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z156 : W := mkw 0x0020024000804400 0x0002002400080440 0xf0e01f44e783e73e 0xef0e01f44e783e73

def z157 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x601c60bb1c0f1ff1 0x2601c60bb1c0f1ff

def z158 : W := mkw 0x2702c58631faf5a7 0x02702c58631faf5a 0xef03e7873ffffffd 0xfef03e7873ffffff

def z159 : W := mkw 0x0041100001220000 0x0004110000122000 0x4003980000730004 0x0400398000073000

def z160 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x601c18fcdc031f3f 0x6601c18fcdc031f3

def z161 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x60007807dc0f1ff4 0x260007807dc0f1ff

def z162 : W := mkw 0x022087f7c0906525 0x1022087f7c090652 0x200007ffc000e738 0x0200007ffc000e73

def z163 : W := mkw 0x0200048000000000 0x0020004800000000 0x0f00078000000009 0xd0f0007800000000

def z164 : W := mkw 0x0000000001b26525 0x00000000001b2652 0x8000000023f0e000 0x08000000023f0e00

def z165 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x201c00f81c001e0b 0x6201c00f81c001e0

def z166 : W := mkw 0xdfff7ee83fefde08 0x0dfff7ee83fefde0 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z167 : W := mkw 0x5ffffff7ff6f0000 0x15ffffff7ff6f000 0xdfffffffffff000f 0xfdfffffffffff000

def z168 : W := mkw 0xafb2c7e632d8f58e 0x0afb2c7e632d8f58 0x9fe3870023f0e000 0x99fe3870023f0e00

def z169 : W := mkw 0x0a9004a000000000 0x00a9004a00000000 0x0f1c00b800000001 0x10f1c00b80000000

def z170 : W := mkw 0x0061934481a24421 0x00061934481a2442 0x10e39f44c783063e 0xc10e39f44c783063

def z171 : W := mkw 0x0020024001b26525 0x00020024001b2652 0xf0e0074027f3e73a 0xef0e0074027f3e73

def z172 : W := mkw 0x0000810400102104 0x0000081040010210 0xe003e787387cf9cd 0xee003e787387cf9c

def z173 : W := mkw 0x1efbfff7c0906525 0x11efbfff7c090652 0x3fffffffc000e73f 0xd3fffffffc000e73

def z174 : W := mkw 0x810400083e009a08 0x0810400083e009a0 0x0000000018001800 0x0000000001800180

def z175 : W := mkw 0x1effffffcc050a50 0x91effffffcc050a5 0x7fffffffdc0f1fff 0xf7fffffffdc0f1ff

def z176 : W := mkw 0x8bf597ecbe80de08 0x08bf597ecbe80de0 0xbfff9ffcff80fe0f 0xfbfff9ffcff80fe0

def z177 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc1ffcff83ff3f 0xffffc1ffcff83ff3

def z178 : W := mkw 0x58dd38000f270000 0x058dd38000f27000 0x10fc180007830002 0x010fc18000783000

def z179 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x50e39844c7f30736 0x050e39844c7f3073

def z180 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x201c18f8dc031e3b 0x6201c18f8dc031e3

def z181 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x90e39f44e3f0e00e 0xc90e39f44e3f0e00

def z182 : W := mkw 0x0502400030480000 0x0050240003048000 0xef03e087387c19cd 0xfef03e087387c19c

def z183 : W := mkw 0x002cab5dcc956f75 0x8002cab5dcc956f7 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z184 : W := mkw 0x8ab406e80e804e08 0x08ab406e80e804e0 0x1ffc07f80780060b 0xd1ffc07f80780060

def z185 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc67ff3f8cffcf 0xffffc67ff3f8cffc

def z186 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x7fffffffc403073f 0xf7fffffffc403073

def z187 : W := mkw 0x0049b915c1372175 0x80049b915c137217 0x4003f807c07f01f4 0x04003f807c07f01f

def z188 : W := mkw 0x8bbc2ef97e80de08 0x08bbc2ef97e80de0 0xbffc7fffff80fe0f 0xfbffc7fffff80fe0

def z189 : W := mkw 0x140a681340000000 0x1140a68134000000 0x0000600300000000 0x0000060030000000

def z190 : W := mkw 0x099400003e000000 0x0099400003e00000 0x9ffc00003f800003 0xf9ffc00003f80000

def z191 : W := mkw 0x0008281140000000 0x0000828114000000 0x001c60bb00000001 0x0001c60bb0000000

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x000060870000000d 0x4000060870000000

def z193 : W := mkw 0x800400080e804e08 0x0800400080e804e0 0x0000000007800600 0x0000000000780060

def z194 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x7fffffffd80c19cf 0xf7fffffffd80c19c

def z195 : W := mkw 0x0502400030480000 0x0050240003048000 0xcf03e000387c0005 0xfcf03e000387c000

def z196 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0x9ffc07f82380e00b 0xd9ffc07f82380e00

def z197 : W := mkw 0x58fd3a408fa74421 0x058fd3a408fa7442 0x10fc1840c7830632 0x010fc1840c783063

def z198 : W := mkw 0x0041100001220000 0x0004110000122000 0x90e3800023f00000 0x890e3800023f0000

def z199 : W := mkw 0x8ab006e80080de08 0x08ab006e80080de0 0x3ffc07f80000fe0b 0xd3ffc07f80000fe0

def z200 : W := mkw 0x0061124080000000 0x0006112408000000 0x10e01840c0000002 0x010e01840c000000

def z201 : W := mkw 0x270244823058b186 0x0270244823058b18 0xef006083387cf9c1 0x3ef006083387cf9c

def z202 : W := mkw 0x810000003280d408 0x0810000003280d40 0x800000002380e000 0x0800000002380e00

def z203 : W := mkw 0x832006e83080de08 0x0832006e83080de0 0xaf0007f83800fe09 0xfaf0007f83800fe0

def z204 : W := mkw 0x0008281940050a50 0x80008281940050a5 0x600078ffc00f1ffc 0x0600078ffc00f1ff

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x40001804c0030134 0x040001804c003013

def z206 : W := mkw 0x8bb006e83280de08 0x08bb006e83280de0 0xbfe007f82380fe08 0x9bfe007f82380fe0

def z207 : W := mkw 0x800000080080de08 0x0800000080080de0 0x200000000000fe00 0x0200000000000fe0

def z208 : W := mkw 0x0eb2c7e600000000 0x00eb2c7e60000000 0x1fffe7ff0000000f 0xd1fffe7ff0000000

def z209 : W := mkw 0x0020024000804400 0x0002002400080440 0x200007400000e608 0x0200007400000e60

def z210 : W := mkw 0x0008281140000000 0x0000828114000000 0x601c78ffc403073f 0x6601c78ffc403073

def z211 : W := mkw 0x18f93a71c1a24421 0x118f93a71c1a2442 0x10fc1878c7830632 0x010fc1878c783063

def z212 : W := mkw 0xdfffffecbfffff2d 0x0dfffffecbfffff2 0xfffffffcffffff3f 0xffffffffcffffff3

def z213 : W := mkw 0x0300048030009000 0x0030004803000900 0xef006787380cf9cd 0xfef006787380cf9c

def z214 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x001c60bb180c18c1 0x0001c60bb180c18c

def z215 : W := mkw 0x8020026800804e08 0x08020026800804e0 0x0000007800000600 0x0000000780000060

def z216 : W := mkw 0x8bb487fffe80de08 0x18bb487fffe80de0 0xbffc07ffff80fe0b 0xfbffc07ffff80fe0

def z217 : W := mkw 0x270eed9f7c5dbbd6 0x8270eed9f7c5dbbd 0xef1fe7bf387cf9cd 0xfef1fe7bf387cf9c

def z218 : W := mkw 0x0020024080804421 0x0002002408080442 0x00000040c0000630 0x000000040c000063

def z219 : W := mkw 0x1898283140000000 0x1189828314000000 0x001c003800000000 0x0001c00380000000

def z220 : W := mkw 0x0abc2ef94c050a50 0x80abc2ef94c050a5 0x7ffc7fffdc0f1fff 0xf7ffc7fffdc0f1ff

def z221 : W := mkw 0x230085863058b186 0x0230085863058b18 0xe0000787387cf9c8 0x2e0000787387cf9c

def z222 : W := mkw 0x0008281140050050 0x8000828114005005 0x00001800c0030030 0x000001800c003003

def z223 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x401c78bb1c0f18c7 0x6401c78bb1c0f18c

def z224 : W := mkw 0x0100000030480000 0x0010000003048000 0xc0000000387c0000 0x2c0000000387c000

def z225 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fff87f80000000b 0xd1fff87f80000000

def z226 : W := mkw 0x0041910481b26525 0x00041910481b2652 0xe0039804e7f3e734 0x2e0039804e7f3e73

def z227 : W := mkw 0x0100000030000000 0x0010000003000000 0x8f00000038000001 0xf8f0000003800000

def z228 : W := mkw 0x0061934481220000 0x0006193448122000 0xd0e39f44e7f3000e 0xed0e39f44e7f3000

def z229 : W := mkw 0x230004803058b186 0x0230004803058b18 0xef000780387cf9c9 0xfef000780387cf9c

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x00006083180c18c1 0x000006083180c18c

def z231 : W := mkw 0x0ab82ef140000000 0x00ab82ef14000000 0x1ffc7fffc000000f 0xd1ffc7fffc000000

def z232 : W := mkw 0x1efbfff7c1a24421 0x11efbfff7c1a2442 0x1fffffffc783063f 0xd1fffffffc783063

def z233 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03ffc7fc7fffff 0xfef03ffc7fc7ffff

def z234 : W := mkw 0x0228aff7c0000000 0x10228aff7c000000 0x001c7fffc000000f 0x4001c7fffc000000

def z235 : W := mkw 0x210000003058b186 0x0210000003058b18 0xe0000000387cf9c0 0x2e0000000387cf9c

def z236 : W := mkw 0x5d9e68003f6f0000 0x05d9e68003f6f000 0xcf1c60003fff0001 0x3cf1c60003fff000

def z237 : W := mkw 0x414510003f6f0000 0x0414510003f6f000 0xd0e398003fff0006 0xed0e398003fff000

def z238 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xd0e39f0027f3e006 0xed0e39f0027f3e00

def z239 : W := mkw 0x1af9bff7c0000000 0x11af9bff7c000000 0x10fc1fffc000000a 0x010fc1fffc000000

def z240 : W := mkw 0x7fdffd9f7f7fbbd6 0x87fdffd9f7f7fbbd 0xffffffffffffffff 0xffffffffffffffff

def z241 : W := mkw 0x0000000000906525 0x0000000000090652 0x200000000000e730 0x0200000000000e73

def z242 : W := mkw 0x8fb6c7ee3e80de08 0x08fb6c7ee3e80de0 0xbfffe7ff3f80fe0f 0xfbfffe7ff3f80fe0

def z243 : W := mkw 0x0061124081a24421 0x00061124081a2442 0x10e0000003800000 0x010e000000380000

def z244 : W := mkw 0x1cfbfb4480000000 0x01cfbfb448000000 0x1fffff44c000000f 0xd1fffff44c000000

def z245 : W := mkw 0x18f1126080000000 0x118f112608000000 0x10e0000000000000 0x010e000000000000

def z246 : W := mkw 0x000400080c050a50 0x8000400080c050a5 0x0000000004030630 0x0000000000403063

def z247 : W := mkw 0x544b7811416f0050 0x8544b7811416f005 0x4003f807c07f01f4 0x04003f807c07f01f

def z248 : W := mkw 0x0020835dc0906f75 0x80020835dc0906f7 0x200007ffc000fff8 0x0200007ffc000fff

def z249 : W := mkw 0x5ddf78117f6f0000 0x05ddf78117f6f000 0xdffff8ffffff000f 0xfdffff8ffffff000

def z250 : W := mkw 0x5cdb7800016f0000 0x05cdb7800016f000 0x5ffff800007f0007 0xd5ffff800007f000

def z251 : W := mkw 0x5dd750003f6f0000 0x05dd750003f6f000 0xdfe380003fff0000 0xbdfe380003fff000

def z252 : W := mkw 0x5dff7a71ff6f0000 0x15dff7a71ff6f000 0xdffff878ffff0007 0xfdffff878ffff000

def z253 : W := mkw 0x006dbb5dcdb76f75 0x8006dbb5dcdb76f7 0xf0ffffffffffffff 0xef0fffffffffffff

def z254 : W := mkw 0x2402c10600582186 0x02402c1060058218 0x4003e007007c01c4 0x04003e007007c01c

def z255 : W := mkw 0x2702448230489082 0x0270244823048908 0xaf006783380cf8c9 0xfaf006783380cf8c

def z256 : W := mkw 0x88bc2a794e854e58 0x888bc2a794e854e5 0x70fc78ffdf8f1fff 0x670fc78ffdf8f1ff

def z257 : W := mkw 0xafb2c7e632d8f58e 0x0afb2c7e632d8f58 0xffe3e7873bfcf9cd 0xfffe3e7873bfcf9c

def z258 : W := mkw 0x0041100000000000 0x0004110000000000 0x10e3980000000006 0xc10e398000000000

def z259 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x201c60ffd80c1ff9 0x0201c60ffd80c1ff

def z260 : W := mkw 0x88f512688fa24e29 0x088f512688fa24e2 0x10fc1878c7830632 0x010fc1878c783063

def z261 : W := mkw 0x0000001940000a50 0x80000001940000a5 0x000000bb000018c0 0x0000000bb000018c

def z262 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8873fff19cf 0xffffff8873fff19c

def z263 : W := mkw 0x220cad9f4c15bbd6 0x8220cad9f4c15bbd 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z264 : W := mkw 0x544f78194d6f0a50 0x8544f78194d6f0a5 0x601ff8ffdc7f1fff 0x6601ff8ffdc7f1ff

def z265 : W := mkw 0xaf96c5ae3e58bb8e 0x0af96c5ae3e58bb8 0xef1fe7bf387cf9cd 0xfef1fe7bf387cf9c

def z266 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x401c787fc40f07f6 0x0401c787fc40f07f

def z267 : W := mkw 0x0602c58600000000 0x00602c5860000000 0x0f03e7870000000d 0xd0f03e7870000000

def z268 : W := mkw 0xaf9644aa3e489a8a 0x0af9644aa3e489a8 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z269 : W := mkw 0x5fffffffff6f0a50 0x95fffffffff6f0a5 0xffffffffffff1fff 0xfffffffffffff1ff

def z270 : W := mkw 0x0061934481322125 0x0006193448132212 0x50e39f44c073013e 0xc50e39f44c073013

def z271 : W := mkw 0x58dd38194f270a50 0x858dd38194f270a5 0x10fc1878c7830632 0x010fc1878c783063

def z272 : W := mkw 0x220085860010b186 0x0220085860010b18 0x60006787180cf9cd 0x660006787180cf9c

def z273 : W := mkw 0x8bb487ecbe90ff2d 0x08bb487ecbe90ff2 0xbffc07fcff80ff3b 0xfbffc07fcff80ff3

def z274 : W := mkw 0x744bf906017f2186 0x0744bf906017f218 0x4003f807007f01c4 0x04003f807007f01c

def z275 : W := mkw 0x88b402680e804e08 0x088b402680e804e0 0x30fc00f81f801e0b 0x630fc00f81f801e0

def z276 : W := mkw 0x08b0026000000000 0x008b002600000000 0x10fc007800000002 0x010fc00780000000

def z277 : W := mkw 0x8bf516e8bfa2de29 0x08bf516e8bfa2de2 0xbffc1ff8ff83fe3b 0xfbffc1ff8ff83fe3

def z278 : W := mkw 0x0702c58630009000 0x00702c5863000900 0xaf03e7873800f80d 0xfaf03e7873800f80

def z279 : W := mkw 0x210c28197c5dbbd6 0x8210c28197c5dbbd 0xe01c78fffc7fffff 0x6e01c78fffc7ffff

def z280 : W := mkw 0x1efb7ee000000000 0x01efb7ee00000000 0x1ffffff80000000f 0xd1ffffff80000000

def z281 : W := mkw 0x0000810400102104 0x0000081040010210 0x800387002070e000 0x8800387002070e00

def z282 : W := mkw 0x0300048030009000 0x0030004803000900 0x8f0007002000e000 0x98f0007002000e00

def z283 : W := mkw 0x000c28194c000a00 0x0000c28194c000a0 0x201c78ffdc001e0f 0x6201c78ffdc001e0

def z284 : W := mkw 0x1cdb780001220000 0x01cdb78000122000 0xdffff80027f30007 0xfdffff80027f3000

def z285 : W := mkw 0x000c28080c050a50 0x8000c28080c050a5 0x601c78001c0f1ff7 0x6601c78001c0f1ff

def z286 : W := mkw 0x1efbfff7c0102104 0x11efbfff7c010210 0xffffffffe070e10f 0xfffffffffe070e10

def z287 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x401c7878dc0f0637 0x6401c7878dc0f063

def z288 : W := mkw 0x0008281140050050 0x8000828114005005 0x60007847c40f07fe 0x660007847c40f07f

def z289 : W := mkw 0x410400083f6f0a50 0x8410400083f6f0a5 0xe00000003fff1ff0 0x2e00000003fff1ff

def z290 : W := mkw 0x41000000336a0000 0x041000000336a000 0x8000000023f00000 0x08000000023f0000

def z291 : W := mkw 0x0020834480000000 0x0002083448000000 0x00000744c0000008 0x000000744c000000

def z292 : W := mkw 0x5ddb7800336a0000 0x05ddb7800336a000 0x9ffff80023f00007 0xd9ffff80023f0000

def z293 : W := mkw 0x276fffdffdfffff7 0x8276fffdffdfffff 0xffffffffffffffff 0xffffffffffffffff

def z294 : W := mkw 0x1ef3d7f7c0000000 0x11ef3d7f7c000000 0x1fe387ffc0000008 0x91fe387ffc000000

def z295 : W := mkw 0x2763d7c6b1faf5a7 0x02763d7c6b1faf5a 0xffe39f44e7f3e73e 0xfffe39f44e7f3e73

def z296 : W := mkw 0x98fd3a79ce804e08 0x198fd3a79ce804e0 0x10fc1878c7800602 0x010fc1878c780060

def z297 : W := mkw 0x610400003f7fb186 0x0610400003f7fb18 0xe00000003ffff9c0 0x2e00000003ffff9c

def z298 : W := mkw 0x05435000316a0000 0x005435000316a000 0xdfe3f8003fff0007 0xfdfe3f8003fff000

def z299 : W := mkw 0x58dd38194f270a50 0x858dd38194f270a5 0x70fc78ffdf8f1fff 0x670fc78ffdf8f1ff

def z300 : W := mkw 0x540a6800004d0000 0x0540a6800004d000 0x00006000000c0000 0x000006000000c000

def z301 : W := mkw 0x0041910481322125 0x0004191048132212 0xe0039f04e073e13c 0xee0039f04e073e13

def z302 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0xbfe007803b80f809 0xfbfe007803b80f80

def z303 : W := mkw 0x0af197e480000000 0x00af197e48000000 0x1fff9ffcc000000f 0xd1fff9ffcc000000

def z304 : W := mkw 0x18f9bb75c1b26525 0x118f9bb75c1b2652 0xf0ff9f7ce7f3e73e 0xef0ff9f7ce7f3e73

def z305 : W := mkw 0x3ffffffffc5dbbd6 0x93ffffffffc5dbbd 0xfffffffffc7fffff 0xffffffffffc7ffff

def z306 : W := mkw 0x0ab406e80c000a00 0x00ab406e80c000a0 0x3ffc07f81c001e0b 0xf3ffc07f81c001e0

def z307 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e3ffc7ffffffff 0xef0e3ffc7fffffff

def z308 : W := mkw 0x5ddf78117f6f0050 0x85ddf78117f6f005 0xdffff807ffff01f7 0xfdffff807ffff01f

def z309 : W := mkw 0x0000000001220000 0x0000000000122000 0xc000000027f30000 0x2c000000027f3000

def z310 : W := mkw 0x0622c7f7c0000000 0x10622c7f7c000000 0x0f03e7ffc000000d 0xd0f03e7ffc000000

def z311 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x200000001c001e00 0x2200000001c001e0

def z312 : W := mkw 0xd8fd3a680fa74e08 0x0d8fd3a680fa74e0 0x10fc187807830602 0x010fc18780783060

def z313 : W := mkw 0x0008281140000000 0x0000828114000000 0x00007807c0000004 0x000007807c000000

def z314 : W := mkw 0x5ffbfff7f36a0000 0x15ffbfff7f36a000 0x9fffffffe3f0000f 0xd9fffffffe3f0000

def z315 : W := mkw 0x1cfb7a71c0000000 0x11cfb7a71c000000 0x1ffff878c0000007 0xd1ffff878c000000

def z316 : W := mkw 0x5dfffb5dffff6f75 0x85dfffb5dffff6f7 0xffffffffffffffff 0xffffffffffffffff

def z317 : W := mkw 0x2463d34681fa65a7 0x02463d34681fa65a 0xf0e3ff47e7ffe7fe 0xef0e3ff47e7ffe7f

def z318 : W := mkw 0x0000000800000a50 0x80000000800000a5 0x2000000000001ff0 0x02000000000001ff

def z319 : W := mkw 0x5ddf78003fff6525 0x05ddf78003fff652 0xfffff8003fffe737 0xffffff8003fffe73

def z320 : W := mkw 0x1edbfdb7c0000000 0x11edbfdb7c000000 0x0f1ff8bfc0000005 0x10f1ff8bfc000000

def z321 : W := mkw 0x2706c58e3c5dbbd6 0x82706c58e3c5dbbd 0xef03e7873c7ffffd 0xfef03e7873c7ffff

def z322 : W := mkw 0x0000001940000a50 0x80000001940000a5 0x00000078c0000630 0x000000078c000063

def z323 : W := mkw 0x099400083e000a00 0x0099400083e000a0 0xbffc00f83f801e0b 0xfbffc00f83f801e0

def z324 : W := mkw 0xdfff7ef97fefde58 0x8dfff7ef97fefde5 0xffffffffffffffff 0xffffffffffffffff

def z325 : W := mkw 0x499400003f6f0000 0x0499400003f6f000 0xdffc00003fff0003 0xfdffc00003fff000

def z326 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x8f03e7872070e00d 0xd8f03e7872070e00

def z327 : W := mkw 0xafb646ea3ec8de8a 0x0afb646ea3ec8de8 0xbffc67fb3f8cfecb 0xfbffc67fb3f8cfec

def z328 : W := mkw 0x000400080c050a50 0x8000400080c050a5 0x60001844dc0f1ffe 0x660001844dc0f1ff

def z329 : W := mkw 0x1e9e6cbb4c050a50 0x91e9e6cbb4c050a5 0x6f1c78ffdc0f1fff 0x76f1c78ffdc0f1ff

def z330 : W := mkw 0x5efbfff7c16f0000 0x15efbfff7c16f000 0x5fffffffc07f000f 0xd5fffffffc07f000

def z331 : W := mkw 0x2722c7c630d8f586 0x02722c7c630d8f58 0xffe3e7c73ffcffcf 0xfffe3e7c73ffcffc

def z332 : W := mkw 0x5d92400032480000 0x05d9240003248000 0x0f00000000000000 0x10f0000000000000

def z333 : W := mkw 0x0bb406e03e000000 0x00bb406e03e00000 0x9ffc07f83f80000b 0xf9ffc07f83f80000

def z334 : W := mkw 0x0061935dc1b26f75 0x80061935dc1b26f7 0xf0e39fffe7f3fffe 0xef0e39fffe7f3fff

def z335 : W := mkw 0x2706c58e3c58bb86 0x02706c58e3c58bb8 0xef1fe7ff3c7cffcf 0xfef1fe7ff3c7cffc

def z336 : W := mkw 0x099400003e000000 0x0099400003e00000 0x0f1c000018000001 0x10f1c00001800000

def z337 : W := mkw 0x0663d7c681b26525 0x00663d7c681b2652 0xffe3ffc7e7f3e73f 0xfffe3ffc7e7f3e73

def z338 : W := mkw 0x1eba6ef340000000 0x11eba6ef34000000 0x1ffc67fb0000000b 0xd1ffc67fb0000000

def z339 : W := mkw 0xdfdf7ca83f6f9a08 0x0dfdf7ca83f6f9a0 0xdffff8b83fff1807 0xfdffff8b83fff180

def z340 : W := mkw 0x060eed9f4c050a50 0x8060eed9f4c050a5 0x6f1fffffdc0f1fff 0xf6f1fffffdc0f1ff

def z341 : W := mkw 0x5ffffff7ffff6525 0x15ffffff7ffff652 0xffffffffffffe73f 0xfffffffffffffe73

def z342 : W := mkw 0x000400194c050a50 0x8000400194c050a5 0x600000ffdc0f1ff8 0x2600000ffdc0f1ff

def z343 : W := mkw 0x1af93ef1c0000000 0x11af93ef1c000000 0x1ffc1ff8c000000b 0xd1ffc1ff8c000000

def z344 : W := mkw 0x2702448230489082 0x0270244823048908 0x6f006087180c19cd 0x76f006087180c19c

def z345 : W := mkw 0x0041910481322125 0x0004191048132212 0x60039844c473073e 0x660039844c473073

def z346 : W := mkw 0x374bfd97f058b186 0x1374bfd97f058b18 0xef03ff87f87cf9cd 0xfef03ff87f87cf9c

def z347 : W := mkw 0x220085860010b186 0x0220085860010b18 0x000007000000e000 0x0000007000000e00

def z348 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00007002000e008 0xea00007002000e00

def z349 : W := mkw 0x09b402403e804400 0x009b402403e80440 0xbffc07403f80e60b 0xfbffc07403f80e60

def z350 : W := mkw 0x144bf917c0050050 0x9144bf917c005005 0x4003f807c00f01f4 0x04003f807c00f01f

def z351 : W := mkw 0x099c28003e050000 0x0099c28003e05000 0xdffc78003f8f0007 0xfdffc78003f8f000

def z352 : W := mkw 0x1efb7ef3c0000000 0x11efb7ef3c000000 0x1ffc78fbc0000003 0x11ffc78fbc000000

def z353 : W := mkw 0x2100000031faf5a7 0x02100000031faf5a 0xe00000003ffffff0 0x2e00000003ffffff

def z354 : W := mkw 0x000400080c050a50 0x8000400080c050a5 0x601c00f81c0f1ffb 0x6601c00f81c0f1ff

def z355 : W := mkw 0x5ddf78083f6f0a00 0x05ddf78083f6f0a0 0xfffff8f83fff1e0f 0xffffff8f83fff1e0

def z356 : W := mkw 0x022006e000000000 0x0022006e00000000 0x000007f800000008 0x0000007f80000000

def z357 : W := mkw 0x0100000030009000 0x0010000003000900 0xa00000003800f800 0x2a00000003800f80

def z358 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fe39f44c000000e 0xd1fe39f44c000000

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000004030730 0x2600000000403073

def z360 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffe7bb00000001 0x91fffe7bb0000000

def z361 : W := mkw 0x146bfb57c1b26525 0x1146bfb57c1b2652 0xf0e3ff47e7f3e73e 0xef0e3ff47e7f3e73

def z362 : W := mkw 0x5049380001270000 0x0504938000127000 0x0000180000030000 0x0000018000003000

def z363 : W := mkw 0x222087f7c010b186 0x1222087f7c010b18 0x200007ffc000f9c8 0x0200007ffc000f9c

def z364 : W := mkw 0x2fb2c7e63058b186 0x02fb2c7e63058b18 0xffffe7ff387cf9cf 0xfffffe7ff387cf9c

def z365 : W := mkw 0x6706c5863f7fb186 0x06706c5863f7fb18 0xef03e7873ffff9cd 0xfef03e7873ffff9c

def z366 : W := mkw 0x1efbfff7c1220000 0x11efbfff7c122000 0xdfffffffe7f3000f 0xfdfffffffe7f3000

def z367 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x90e39f40e7f3e632 0x890e39f40e7f3e63

def z368 : W := mkw 0x3f9a6cb370489082 0x13f9a6cb37048908 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z369 : W := mkw 0x5fdffd863f6f0000 0x05fdffd863f6f000 0xdfffff873fff000f 0xfdfffff873fff000

def z370 : W := mkw 0x0061934480000000 0x0006193448000000 0x10e3870000000000 0x810e387000000000

def z371 : W := mkw 0x0bb006e030009000 0x00bb006e03000900 0xbffc07f83800f80b 0xfbffc07f83800f80

def z372 : W := mkw 0x822087ffc080de08 0x1822087ffc080de0 0x200007ffc000fe08 0x0200007ffc000fe0

def z373 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x1ffc78001f8f0003 0x11ffc78001f8f000

def z374 : W := mkw 0x0041100001220000 0x0004110000122000 0xf0e39844e7f3073e 0xef0e39844e7f3073

def z375 : W := mkw 0x1ffbfff7f0480000 0x11ffbfff7f048000 0xdffffffff87c000f 0xfdffffffff87c000

def z376 : W := mkw 0x166bfff7c0000000 0x1166bfff7c000000 0x0003ffffc000000c 0x00003ffffc000000

def z377 : W := mkw 0x58dd38000f270000 0x058dd38000f27000 0xd0ff980027f30006 0xed0ff980027f3000

def z378 : W := mkw 0x0000000000050050 0x8000000000005005 0x40000000000f01f0 0x040000000000f01f

def z379 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x001c78ffd80c18cf 0x4001c78ffd80c18c

def z380 : W := mkw 0x812402483e80de08 0x0812402483e80de0 0xb0e007403f80fe0a 0xeb0e007403f80fe0

def z381 : W := mkw 0x09f59344bfb26525 0x009f59344bfb2652 0xffff9f44fff3e73f 0xfffff9f44fff3e73

def z382 : W := mkw 0x210000003058b186 0x0210000003058b18 0xe0006087387cf9cd 0x6e0006087387cf9c

def z383 : W := mkw 0x1edb7cb340000000 0x11edb7cb34000000 0x1ffff8bb00000007 0xd1ffff8bb0000000

def z384 : W := mkw 0x5ffffff7fe4d0000 0x15ffffff7fe4d000 0x1fffffffd80c000f 0xd1fffffffd80c000

def z385 : W := mkw 0x5ddff9043f7f2104 0x05ddff9043f7f210 0xffffff043fffe10f 0xfffffff043fffe10

def z386 : W := mkw 0x002c2a594c854e50 0x8002c2a594c854e5 0xf0fc7fffff8fffff 0xef0fc7fffff8ffff

def z387 : W := mkw 0x0000810401b26525 0x00000810401b2652 0xe003870427f3e73c 0xee003870427f3e73

def z388 : W := mkw 0x010400003e000000 0x0010400003e00000 0x800000003f800000 0x2800000003f80000

def z389 : W := mkw 0x9fbe6efb7e80de08 0x19fbe6efb7e80de0 0xbffc67fb3f80fe0b 0xfbffc67fb3f80fe0

def z390 : W := mkw 0x099c28197e050a50 0x8099c28197e050a5 0xfffc78ffff8f1fff 0xffffc78ffff8f1ff

def z391 : W := mkw 0x88b0026002804408 0x088b002600280440 0x10e0000003800000 0x010e000000380000

def z392 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3e0003bfc0005 0xfdfe3e0003bfc000

def z393 : W := mkw 0x7fd3d586337ab186 0x07fd3d586337ab18 0xffe3e7873bfcf9cd 0xfffe3e7873bfcf9c

def z394 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07782780e602 0x99ffc07782780e60

def z395 : W := mkw 0x822006e00080d408 0x0822006e00080d40 0x000007000000e000 0x0000007000000e00

def z396 : W := mkw 0x0020834400906504 0x0002083440090650 0xf0e3874427f0e70e 0xef0e3874427f0e70

def z397 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xcf03e700387ce005 0xfcf03e700387ce00

def z398 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xaf0387803870f809 0xfaf0387803870f80

def z399 : W := mkw 0x7ffffff7ff7fb186 0x17ffffff7ff7fb18 0xfffffffffffff9cf 0xffffffffffffff9c

def z400 : W := mkw 0x0502400030480000 0x0050240003048000 0x8f03800020700000 0x98f0380002070000

def z401 : W := mkw 0x0000810400102104 0x0000081040010210 0x200007040000e108 0x0200007040000e10

def z402 : W := mkw 0x000c28000c050000 0x0000c28000c05000 0x601c7844dc0f073f 0x6601c7844dc0f073

def z403 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef0387042070e10c 0xfef0387042070e10

def z404 : W := mkw 0x060aed9740000000 0x0060aed974000000 0x0f1fffffc000000f 0xd0f1fffffc000000

def z405 : W := mkw 0x18fd3a79cc050a50 0x918fd3a79cc050a5 0x70fc78ffdc0f1fff 0x670fc78ffdc0f1ff

def z406 : W := mkw 0xa10400083ed8ff8e 0x0a10400083ed8ff8 0xe00000003ffcffc0 0x2e00000003ffcffc

def z407 : W := mkw 0x022087e680000000 0x1022087e68000000 0x0000070000000000 0x0000007000000000

def z408 : W := mkw 0x1ebaeff7c0000000 0x11ebaeff7c000000 0x0f1c67ffc0000009 0x10f1c67ffc000000

def z409 : W := mkw 0x0008280000000000 0x0000828000000000 0x001c780000000007 0x4001c78000000000

def z410 : W := mkw 0x8b9404a83e009a08 0x08b9404a83e009a0 0x9ffc00b83f801803 0xf9ffc00b83f80180

def z411 : W := mkw 0x226197c681b2f5a7 0x0226197c681b2f5a 0xf0e39fc7e7f3fffe 0xef0e39fc7e7f3fff

def z412 : W := mkw 0x41659344bfff6525 0x041659344bfff652 0xf0e39f44ffffe73e 0xef0e39f44ffffe73

def z413 : W := mkw 0x0000810400000000 0x0000081040000000 0x000387040000000c 0xc000387040000000

def z414 : W := mkw 0x1e9aedb740000000 0x11e9aedb74000000 0x0f1fe7bf0000000d 0xd0f1fe7bf0000000

def z415 : W := mkw 0x0200048000009000 0x0020004800000900 0x200007800000f808 0x0200007800000f80

def z416 : W := mkw 0x000c28000c050000 0x0000c28000c05000 0x601c78871c0f19cf 0x6601c78871c0f19c

def z417 : W := mkw 0x0300048030009000 0x0030004803000900 0x0f00008018001801 0x10f0000801800180

def z418 : W := mkw 0x2602c58600582186 0x02602c5860058218 0x4f03e787007c01cd 0xd4f03e787007c01c

def z419 : W := mkw 0x0890000000000000 0x0089000000000000 0x1ffc000000000003 0xd1ffc00000000000

def z420 : W := mkw 0xaff7d7eebffaffaf 0x0aff7d7eebffaffa 0xffffffffffffffff 0xffffffffffffffff

def z421 : W := mkw 0x000c28114c050000 0x0000c28114c05000 0x401c78ffdc0f000f 0x6401c78ffdc0f000

def z422 : W := mkw 0x1443d10680000000 0x11443d1068000000 0x0003800000000000 0x0000380000000000

def z423 : W := mkw 0x1efbfff7c0050050 0x91efbfff7c005005 0x5fffffffc00f01ff 0xd5fffffffc00f01f

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x90e0000027800002 0xe90e000002780000

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000044c0000738 0x020000044c000073

def z426 : W := mkw 0x0041100081220021 0x0004110008122002 0x00001800c0030030 0x000001800c003003

def z427 : W := mkw 0x5dff7a40bfef4421 0x05dff7a40bfef442 0xdffff840ffff0637 0xfdffff840ffff063

def z428 : W := mkw 0x030c2c997c059a50 0x8030c2c997c059a5 0xef1c7ffffc0fffff 0xfef1c7ffffc0ffff

def z429 : W := mkw 0x032006c03080d400 0x0032006c03080d40 0xbfe007c03f80fe0b 0xfbfe007c03f80fe0

def z430 : W := mkw 0xa706c58e3ed8ff8e 0x0a706c58e3ed8ff8 0xef03e7873ffcffcd 0xfef03e7873ffcffc

def z431 : W := mkw 0x1cdbf917c0000000 0x11cdbf917c000000 0x1ffff807c0000007 0xd1ffff807c000000

def z432 : W := mkw 0xddff7a683fef4e08 0x0ddff7a683fef4e0 0xdffff8783fff0607 0xfdffff8783fff060

def z433 : W := mkw 0x0020024000804400 0x0002002400080440 0x10e0004007800602 0x010e000400780060

def z434 : W := mkw 0x810400083fb2ff2d 0x0810400083fb2ff2 0xe00000003ff3ff30 0x2e00000003ff3ff3

def z435 : W := mkw 0x410c28197f6f0a50 0x8410c28197f6f0a5 0xe01c78ffffff1fff 0x6e01c78ffffff1ff

def z436 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3980027f30006 0xfdfe3980027f3000

def z437 : W := mkw 0x020004b340000000 0x1020004b34000000 0x000000bb00000000 0x0000000bb0000000

def z438 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x001c00b818001801 0x0001c00b81800180

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000087000019c8 0x020000087000019c

def z440 : W := mkw 0x5d9e68003e4d0000 0x05d9e68003e4d000 0xcf1fe000387c0005 0xfcf1fe000387c000

def z441 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x601c1878dc0f1ff2 0x2601c1878dc0f1ff

def z442 : W := mkw 0x21619344b1faf5a7 0x021619344b1faf5a 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z443 : W := mkw 0x89b402683e80de08 0x089b402683e80de0 0xb0fc00783f80fe02 0x2b0fc00783f80fe0

def z444 : W := mkw 0x0000001140000000 0x0000000114000000 0x000000ffc0000008 0x0000000ffc000000

def z445 : W := mkw 0x5efffff7cf270000 0x15efffff7cf27000 0x1fffffffc783000f 0xd1fffffffc783000

def z446 : W := mkw 0x18fd3a79cc050a50 0x918fd3a79cc050a5 0x10fc1878c4030632 0x010fc1878c403063

def z447 : W := mkw 0x8b9404a83e009a08 0x08b9404a83e009a0 0xaf1c07b83800f809 0xfaf1c07b83800f80

def z448 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x8f03e783387cf8c1 0x98f03e783387cf8c

def z449 : W := mkw 0x004db91dcd372b75 0x8004db91dcd372b7 0x601ff8ffdc7f1fff 0x6601ff8ffdc7f1ff

def z450 : W := mkw 0x88bc2a794e854e58 0x888bc2a794e854e5 0x10fc1878c7830632 0x010fc1878c783063

def z451 : W := mkw 0x410400003e4d0000 0x0410400003e4d000 0x00000000180c0000 0x000000000180c000

def z452 : W := mkw 0x0702c58630480000 0x00702c5863048000 0xcf03e787387c000d 0xfcf03e787387c000

def z453 : W := mkw 0x0502c10430582104 0x00502c1043058210 0xef03e704387ce10d 0xfef03e704387ce10

def z454 : W := mkw 0x40000000016f0000 0x040000000016f000 0x40000000007f0000 0x040000000007f000

def z455 : W := mkw 0x0b9404803e009000 0x00b9404803e00900 0xbffc07803f80f80b 0xfbffc07803f80f80

def z456 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c78ffc000000f 0x50f1c78ffc000000

def z457 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xaf0387872070f9c8 0x9af0387872070f9c

def z458 : W := mkw 0x0663d7c680000000 0x00663d7c68000000 0x1fe3ffc7c000000f 0xd1fe3ffc7c000000

def z459 : W := mkw 0x5fff7ee03f6f0000 0x05fff7ee03f6f000 0xdffffff83fff000f 0xfdffffff83fff000

def z460 : W := mkw 0x10493811c0000000 0x110493811c000000 0x00001800c0000000 0x000001800c000000

def z461 : W := mkw 0x8b9404a83e009a08 0x08b9404a83e009a0 0x2f1c00f81c001e0b 0x72f1c00f81c001e0

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000008018001809 0x6200000801800180

def z463 : W := mkw 0xdbfd3ee83fa7de08 0x0dbfd3ee83fa7de0 0xbffc1ff83f83fe0b 0xfbffc1ff83f83fe0

def z464 : W := mkw 0x5ddb7800336f0000 0x05ddb7800336f000 0xdfe3f80023ff0004 0x9dfe3f80023ff000

def z465 : W := mkw 0x8bf597ecbfb2ff2d 0x08bf597ecbfb2ff2 0xbfff87f83ff0fe0b 0xfbfff87f83ff0fe0

def z466 : W := mkw 0x810400083e85de58 0x8810400083e85de5 0xe00000003f8ffff0 0x2e00000003f8ffff

def z467 : W := mkw 0x036197c4b1b2f525 0x0036197c4b1b2f52 0xffe39fc4fff3ff3f 0xfffe39fc4fff3ff3

def z468 : W := mkw 0x1efbffe680000000 0x11efbffe68000000 0x1fffff0000000007 0xd1fffff000000000

def z469 : W := mkw 0x8bb487ec3e90ff0c 0x08bb487ec3e90ff0 0xffff87fc3ff0ff0f 0xfffff87fc3ff0ff0

def z470 : W := mkw 0x0402400000480000 0x0040240000048000 0x4003e000007c0004 0x04003e000007c000

def z471 : W := mkw 0x2743d586b17ab1a7 0x02743d586b17ab1a 0xef03ff87f87ff9fd 0xfef03ff87f87ff9f

def z472 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000180004030006 0x6400018000403000

def z473 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fe3e7870000000d 0xd1fe3e7870000000

def z474 : W := mkw 0x8bf516e83fa2de08 0x08bf516e83fa2de0 0xffff9ff83ff3fe0f 0xfffff9ff83ff3fe0

def z475 : W := mkw 0x1ffbfff7f0009000 0x11ffbfff7f000900 0xbffffffff800f80f 0xfbffffffff800f80

def z476 : W := mkw 0x5fdf7c803f6f9000 0x05fdf7c803f6f900 0xffffff803ffff80f 0xfffffff803ffff80

def z477 : W := mkw 0x2502c10630582186 0x02502c1063058218 0xcf03e007387c01c5 0xfcf03e007387c01c

def z478 : W := mkw 0x5f9e6cb37e4d0000 0x15f9e6cb37e4d000 0x0f1c60bb180c0001 0x10f1c60bb180c000

def z479 : W := mkw 0x8165934cbfb2ff2d 0x08165934cbfb2ff2 0xf0e39f44fff3ff3e 0xef0e39f44fff3ff3

def z480 : W := mkw 0x5d9e68197e4d0a50 0x85d9e68197e4d0a5 0x6f1c78ffdc0f1fff 0x76f1c78ffdc0f1ff

def z481 : W := mkw 0x450640003f6f0000 0x0450640003f6f000 0xcf03e0003fff0005 0xfcf03e0003fff000

def z482 : W := mkw 0x0061124081a24421 0x00061124081a2442 0xb0e01f40e783e63a 0xeb0e01f40e783e63

def z483 : W := mkw 0x0020024000804400 0x0002002400080440 0x90e007002380e000 0x890e007002380e00

def z484 : W := mkw 0x270e6c9b7c4d9ad2 0x8270e6c9b7c4d9ad 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z485 : W := mkw 0x006dbb5dcc050a50 0x8006dbb5dcc050a5 0x70ffffffdc0f1fff 0xe70ffffffdc0f1ff

def z486 : W := mkw 0x0061124081b26525 0x00061124081b2652 0xf0e01840e7f3e732 0x2f0e01840e7f3e73

def z487 : W := mkw 0x18d9380000000000 0x018d938000000000 0x10fc180000000002 0x010fc18000000000

def z488 : W := mkw 0x222087c68090f5a7 0x0222087c68090f5a 0x200007c7c000fff8 0x0200007c7c000fff

def z489 : W := mkw 0x0008281140000000 0x0000828114000000 0x601c78ffd80c19cf 0x6601c78ffd80c19c

def z490 : W := mkw 0x0069bb55c1b26525 0x00069bb55c1b2652 0xf0ffffffe7f3e73f 0xef0ffffffe7f3e73

def z491 : W := mkw 0x344bf917c0582186 0x1344bf917c058218 0x4003f807c07c01c4 0x04003f807c07c01c

def z492 : W := mkw 0x1efbfff7c0804400 0x11efbfff7c080440 0xbfffffffe780e60f 0xfbfffffffe780e60

def z493 : W := mkw 0x8bb406e83e009a08 0x08bb406e83e009a0 0x1ffc07f81800180b 0xd1ffc07f81800180

def z494 : W := mkw 0x1ffffff7fe000000 0x11ffffff7fe00000 0x9fffffffff80000f 0xf9fffffffff80000

def z495 : W := mkw 0x146bfb57c0000000 0x1146bfb57c000000 0x10e3ff47c000000e 0xc10e3ff47c000000

def z496 : W := mkw 0x2000810600102186 0x0200081060010218 0x00000007000001c0 0x000000007000001c

def z497 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x601c187cc403073e 0x6601c187cc403073

def z498 : W := mkw 0x0000000001a24421 0x00000000001a2442 0x0000000007830630 0x0000000000783063

def z499 : W := mkw 0x7f9e6c823e4d9082 0x07f9e6c823e4d908 0x0f1c6083180c18c1 0x10f1c6083180c18c

def z500 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x601c60ff1c0c1fcf 0x6601c60ff1c0c1fc

def z501 : W := mkw 0x210000003058b186 0x0210000003058b18 0x800000002070e000 0x0800000002070e00

def z502 : W := mkw 0x240ae917405d21d6 0x8240ae917405d21d 0x4003f807c07f01f4 0x04003f807c07f01f

def z503 : W := mkw 0x006dbb5dcdb76f75 0x8006dbb5dcdb76f7 0xf0ff9f7ce7f3e73e 0xef0ff9f7ce7f3e73

def z504 : W := mkw 0x1effffffcc050a50 0x91effffffcc050a5 0x1fffffffd80c18cf 0xd1fffffffd80c18c

def z505 : W := mkw 0x1efbffffc0000a50 0x91efbffffc0000a5 0x3fffffffc0001fff 0xd3fffffffc0001ff

def z506 : W := mkw 0x3f9aedb77058b186 0x13f9aedb77058b18 0xef1fe7bf387cf9cd 0xfef1fe7bf387cf9c

def z507 : W := mkw 0x00200271c0000000 0x100200271c000000 0x00000078c0000000 0x000000078c000000

def z508 : W := mkw 0x030404883c009a00 0x0030404883c009a0 0xaf1c07f83c00fe0b 0xfaf1c07f83c00fe0

def z509 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x30e01f44c783e73a 0x030e01f44c783e73

def z510 : W := mkw 0x022087ffc0000a50 0x9022087ffc0000a5 0x200007ffc0001ff8 0x0200007ffc0001ff

def z511 : W := mkw 0x210081043058b186 0x0210081043058b18 0xe0038704387cf9cc 0xee0038704387cf9c

def z512 : W := mkw 0x8bbc2ef97e85de58 0x88bbc2ef97e85de5 0xbffc1ff8ff83fe3b 0xfbffc1ff8ff83fe3

def z513 : W := mkw 0x2200859f4010bbd6 0x82200859f4010bbd 0x200007ffc000fff8 0x0200007ffc000fff

def z514 : W := mkw 0x18f9bb75c0000000 0x118f9bb75c000000 0x10ff9f7cc000000e 0xc10ff9f7cc000000

def z515 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x201c60fb1c0c1ecb 0x6201c60fb1c0c1ec

def z516 : W := mkw 0x8bbc2ef97e85de58 0x88bbc2ef97e85de5 0xbffc67fb3f8cfecb 0xfbffc67fb3f8cfec

def z517 : W := mkw 0x2f96c5863e58b186 0x02f96c5863e58b18 0xffffe7873ffcf9cf 0xfffffe7873ffcf9c

def z518 : W := mkw 0x000400000c000000 0x0000400000c00000 0x001c00001c000003 0x6001c00001c00000

def z519 : W := mkw 0x5fdf7cb37f6f0000 0x15fdf7cb37f6f000 0xdffff8bb3fff0007 0xfdffff8bb3fff000

def z520 : W := mkw 0x0000000001b26525 0x00000000001b2652 0xe0001844e7f3e73e 0x6e0001844e7f3e73

def z521 : W := mkw 0x050e68003c4d0000 0x0050e68003c4d000 0xcf1ff8003c7f0007 0xfcf1ff8003c7f000

def z522 : W := mkw 0x2602c5860010b186 0x02602c5860010b18 0x2f03e7870000f9cd 0xd2f03e7870000f9c

def z523 : W := mkw 0x9f9e6cbb7e009a08 0x19f9e6cbb7e009a0 0x0f1c60bb18001801 0x10f1c60bb1800180

def z524 : W := mkw 0x1cd3500000000000 0x01cd350000000000 0x1fe3800000000000 0x91fe380000000000

def z525 : W := mkw 0x8b9c2cb97e059a58 0x88b9c2cb97e059a5 0x6f1c78ffdc0f1fff 0x76f1c78ffdc0f1ff

def z526 : W := mkw 0x5dd750003f6a0000 0x05dd750003f6a000 0x9fff80003ff00003 0xf9fff80003ff0000

def z527 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x001c78ffc403063f 0x4001c78ffc403063

def z528 : W := mkw 0x0041100001b26525 0x00041100001b2652 0xf0e3980027f3e736 0xef0e3980027f3e73

def z529 : W := mkw 0x5df3d344b3fa6525 0x05df3d344b3fa652 0xffe39f44e7f3e73e 0xfffe39f44e7f3e73

def z530 : W := mkw 0x544b7800016f0000 0x0544b7800016f000 0xd0e3f80027ff0006 0xed0e3f80027ff000

def z531 : W := mkw 0x88f5936c8fb26f2d 0x088f5936c8fb26f2 0xf0ff9f7ce7f3e73e 0xef0ff9f7ce7f3e73

def z532 : W := mkw 0x9bfd3ef9fe80de08 0x19bfd3ef9fe80de0 0xbffc1ff8ff80fe0b 0xfbffc1ff8ff80fe0

def z533 : W := mkw 0x5cdf78000f6f0000 0x05cdf78000f6f000 0x50fff80007ff0006 0x050fff80007ff000

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x40006007000c01c4 0x040006007000c01c

def z535 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef038700387cf9c0 0xbef038700387cf9c

def z536 : W := mkw 0x240ee91f4c5d2bd6 0x8240ee91f4c5d2bd 0x601ff8ffdc7f1fff 0x6601ff8ffdc7f1ff

def z537 : W := mkw 0x822006f94080de58 0x8822006f94080de5 0x200007ffc000fff8 0x0200007ffc000fff

def z538 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x4f03e087187c19c5 0x14f03e087187c19c

def z539 : W := mkw 0x2702448230489082 0x0270244823048908 0x0f00000000000000 0x10f0000000000000

def z540 : W := mkw 0x0061124081a24421 0x00061124081a2442 0x70e01844c783073e 0x670e01844c783073

def z541 : W := mkw 0xdff756e83feade08 0x0dff756e83feade0 0xbfff87f83ff0fe0b 0xfbfff87f83ff0fe0

def z542 : W := mkw 0x0065934c8db26f25 0x00065934c8db26f2 0xf0ff9ffcfff3ff3f 0xef0ff9ffcfff3ff3

def z543 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xcf03e707207ce1c4 0x9cf03e707207ce1c

def z544 : W := mkw 0x9fffffffffb2ff2d 0x19fffffffffb2ff2 0xfffffffffff3ff3f 0xffffffffffff3ff3

def z545 : W := mkw 0x1c9a680000000000 0x01c9a68000000000 0x0f1c600000000001 0x10f1c60000000000

def z546 : W := mkw 0x889400280e000a08 0x0889400280e000a0 0x001c003800000000 0x0001c00380000000

def z547 : W := mkw 0x58fdbb448fb76525 0x058fdbb448fb7652 0xf0ff9f44e7f3e73e 0xef0ff9f44e7f3e73

def z548 : W := mkw 0x8bb406e03e80d408 0x08bb406e03e80d40 0x9ffc07003f80e003 0xf9ffc07003f80e00

def z549 : W := mkw 0x1effffffcdb76f75 0x91effffffcdb76f7 0xffffffffffffffff 0xffffffffffffffff

def z550 : W := mkw 0x820004a800009a08 0x0820004a800009a0 0x000000b800001800 0x0000000b80000180

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001844c000000e 0x400001844c000000

def z552 : W := mkw 0x0008281140050050 0x8000828114005005 0x00006003000c00c0 0x000006003000c00c

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x001c00f80000000b 0x4001c00f80000000

def z554 : W := mkw 0x8bb406e83fb2ff2d 0x08bb406e83fb2ff2 0xfffc07f83ff3ff3b 0xffffc07f83ff3ff3

def z555 : W := mkw 0xabb406e83ed8ff8e 0x0abb406e83ed8ff8 0xfffc07f83ffcffcb 0xffffc07f83ffcffc

def z556 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbfe007003f80fe00 0xbbfe007003f80fe0

def z557 : W := mkw 0x9fff7ee83e80de08 0x09fff7ee83e80de0 0xbffffff83f80fe0f 0xfbffffff83f80fe0

def z558 : W := mkw 0x0402400000000000 0x0040240000000000 0x0f03e00000000005 0xd0f03e0000000000

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0x40006000180c0005 0x640006000180c000

def z560 : W := mkw 0x822c2ef94c85de58 0x8822c2ef94c85de5 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z561 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07b83b80f801 0x99ffc07b83b80f80

def z562 : W := mkw 0x9ffbfff7f280d408 0x19ffbfff7f280d40 0x9fffffffe380e00f 0xd9fffffffe380e00

def z563 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x001c78fbdc0f1ef3 0x0001c78fbdc0f1ef

def z564 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9fffe0003bfc0001 0x99fffe0003bfc000

def z565 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x9fffffffe3f0e00f 0xd9fffffffe3f0e00

def z566 : W := mkw 0x0020834481b26525 0x00020834481b2652 0xe0000744e7f3e738 0x2e0000744e7f3e73

def z567 : W := mkw 0x050e68197c4d0a50 0x8050e68197c4d0a5 0xef1ff8fffc7f1fff 0xfef1ff8fffc7f1ff

def z568 : W := mkw 0x2402c10600582186 0x02402c1060058218 0xe003e707207ce1cc 0xee003e707207ce1c

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x600078c7dc0f1fff 0x6600078c7dc0f1ff

def z570 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e3870027f3e730 0xaf0e3870027f3e73

def z571 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x60039f44c073e73c 0x060039f44c073e73

def z572 : W := mkw 0x7fffffc6bffff5a7 0x07fffffc6bffff5a 0xffffffc7ffffffff 0xfffffffc7fffffff

def z573 : W := mkw 0x9ff7d7eebe80de08 0x19ff7d7eebe80de0 0xbfff87f83f80fe0b 0xfbfff87f83f80fe0

def z574 : W := mkw 0x822406e80c80de08 0x0822406e80c80de0 0x201c07f81c00fe0b 0x6201c07f81c00fe0

def z575 : W := mkw 0x8ab406e80e80de08 0x08ab406e80e80de0 0x30fc07f80780fe0a 0x030fc07f80780fe0

def z576 : W := mkw 0x832406e83e80de08 0x0832406e83e80de0 0xa00007f83f80fe08 0x2a00007f83f80fe0

def z577 : W := mkw 0x144ff91fcc050a50 0x9144ff91fcc050a5 0x601ff8ffdc0f1fff 0x6601ff8ffdc0f1ff

def z578 : W := mkw 0x0065934c8db76f75 0x80065934c8db76f7 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z579 : W := mkw 0x000c28000c050000 0x0000c28000c05000 0x001c180004030002 0x0001c18000403000

def z580 : W := mkw 0x0020834480906525 0x0002083448090652 0x60001f44c403e73e 0x660001f44c403e73

def z581 : W := mkw 0x220085860010b186 0x0220085860010b18 0xe00387872070f9cc 0xee00387872070f9c

def z582 : W := mkw 0x5dfffb44bf6f0000 0x05dfffb44bf6f000 0xdfffff44ffff000f 0xfdfffff44ffff000

def z583 : W := mkw 0x5ddf78003e4d0000 0x05ddf78003e4d000 0x1ffff800180c0007 0xd1ffff800180c000

def z584 : W := mkw 0x000c28080c050a00 0x0000c28080c050a0 0x601c78f81c0f1e0f 0x6601c78f81c0f1e0

def z585 : W := mkw 0xafb6c7ee3ed8ff8e 0x0afb6c7ee3ed8ff8 0xbfff87f83ff0fe0b 0xfbfff87f83ff0fe0

def z586 : W := mkw 0x0020024000000000 0x0002002400000000 0x10e007400000000a 0xc10e007400000000

def z587 : W := mkw 0x1ddf78003e000000 0x01ddf78003e00000 0x9ffff8003f800007 0xf9ffff8003f80000

def z588 : W := mkw 0x59dd38003f6f0000 0x059dd38003f6f000 0xd0fc18003fff0002 0x2d0fc18003fff000

def z589 : W := mkw 0x0402c10600000000 0x00402c1060000000 0x0003e00700000004 0x00003e0070000000

def z590 : W := mkw 0x58dd38000f270000 0x058dd38000f27000 0x50fc78001f8f0007 0x650fc78001f8f000

def z591 : W := mkw 0x270aed97705db1d6 0x8270aed97705db1d 0xef03ff87f87ff9fd 0xfef03ff87f87ff9f

def z592 : W := mkw 0x0008281940000a50 0x80008281940000a5 0x201c78ffc0001fff 0x4201c78ffc0001ff

def z593 : W := mkw 0x0041910401322104 0x0004191040132210 0xf0e39f0427f3e10e 0xef0e39f0427f3e10

def z594 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x601c60bf180c19cd 0x6601c60bf180c19c

def z595 : W := mkw 0x2722c7f7f058b186 0x12722c7f7f058b18 0xef03e7fff87cf9cd 0xfef03e7fff87cf9c

def z596 : W := mkw 0x0061934480804400 0x0006193448080440 0xb0e39f44e780e60e 0xeb0e39f44e780e60

def z597 : W := mkw 0x026197f7c1b26525 0x1026197f7c1b2652 0xf0e39fffe7f3e73e 0xef0e39fffe7f3e73

def z598 : W := mkw 0x0041910481322125 0x0004191048132212 0xd0e39804e7f30136 0xed0e39804e7f3013

def z599 : W := mkw 0x270aed977058b186 0x0270aed977058b18 0xef1ffffff87cf9cf 0xfef1ffffff87cf9c

def z600 : W := mkw 0x1effffffcc050a50 0x91effffffcc050a5 0x1fffffffc403063f 0xd1fffffffc403063

def z601 : W := mkw 0x0069bb55c1b76575 0x80069bb55c1b7657 0xf0e3ff47e7ffe7fe 0xef0e3ff47e7ffe7f

def z602 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xb0e38744e3f0e738 0x8b0e38744e3f0e73

def z603 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xb0e3874027f0e60a 0xeb0e3874027f0e60

def z604 : W := mkw 0x3efbfff7c0582186 0x13efbfff7c058218 0x5fffffffc07c01cf 0xd5fffffffc07c01c

def z605 : W := mkw 0x2000000000582186 0x0200000000058218 0x40000000007c01c0 0x040000000007c01c

def z606 : W := mkw 0x2763d7c6b058b186 0x02763d7c6b058b18 0xffe3ffc7f87cf9cf 0xfffe3ffc7f87cf9c

def z607 : W := mkw 0x7fdffd863f7fb186 0x07fdffd863f7fb18 0xdfffff003fffe007 0xfdfffff003fffe00

def z608 : W := mkw 0x88b402680e804e08 0x088b402680e804e0 0xb0fc07782780e60a 0xeb0fc07782780e60

def z609 : W := mkw 0x0008280000050000 0x0000828000005000 0x40007800000f0004 0x040007800000f000

def z610 : W := mkw 0x826197ec81b2ff2d 0x0826197ec81b2ff2 0xf0e39ffce7f3ff3e 0xef0e39ffce7f3ff3

def z611 : W := mkw 0x0000000800000a00 0x00000000800000a0 0x200000f800001e08 0x0200000f800001e0

def z612 : W := mkw 0x18f93a71c0000000 0x118f93a71c000000 0x10fc78ffc000000f 0x410fc78ffc000000

def z613 : W := mkw 0x3ffbfff7f0489082 0x13ffbfff7f048908 0x1fffffffd80c18cf 0xd1fffffffd80c18c

def z614 : W := mkw 0x144b780000000000 0x0144b78000000000 0x0003f80000000004 0x00003f8000000000

def z615 : W := mkw 0x164bfd97c0000000 0x1164bfd97c000000 0x0f03ff87c000000d 0xd0f03ff87c000000

def z616 : W := mkw 0x8bfdbffdffb7ff7d 0x88bfdbffdffb7ff7 0xffffffffffffffff 0xffffffffffffffff

def z617 : W := mkw 0x0069bb55c0000000 0x00069bb55c000000 0x10ffffffc000000f 0xc10ffffffc000000

def z618 : W := mkw 0x210400083c5dbbd6 0x8210400083c5dbbd 0xe00000003c7ffff0 0x2e00000003c7ffff

def z619 : W := mkw 0x0041910480000000 0x0004191048000000 0x00039804c0000004 0x000039804c000000

def z620 : W := mkw 0x2602c5860058b186 0x02602c5860058b18 0x6003e787007cf9cc 0x06003e787007cf9c

def z621 : W := mkw 0x2402400200480082 0x0240240020048008 0x00006003000c00c0 0x000006003000c00c

def z622 : W := mkw 0x544bf904817f2125 0x0544bf904817f212 0x4003f804c07f0134 0x04003f804c07f013

def z623 : W := mkw 0x0041910481322125 0x0004191048132212 0x0003800000700000 0x0000380000070000

def z624 : W := mkw 0x0020834480906525 0x0002083448090652 0xb0e00744e780e73a 0xeb0e00744e780e73

def z625 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x1ffc00f81f801e03 0x11ffc00f81f801e0

def z626 : W := mkw 0xcbb406e83fefde08 0x0cbb406e83fefde0 0xfffc07f83ffffe0b 0xffffc07f83ffffe0

def z627 : W := mkw 0x0000000000102104 0x0000000000010210 0xe00000002070e100 0x2e00000002070e10

def z628 : W := mkw 0x0061934480906525 0x0006193448090652 0x30e39f44c000e73e 0xc30e39f44c000e73

def z629 : W := mkw 0x544f78000d6f0000 0x0544f78000d6f000 0x401ff8001c7f0007 0x6401ff8001c7f000

def z630 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x401c78bfd80f19f5 0x0401c78bfd80f19f

def z631 : W := mkw 0x8bf197e4b3b2f52d 0x08bf197e4b3b2f52 0xffe39f44e7f3e73e 0xfffe39f44e7f3e73

def z632 : W := mkw 0x2402c10600582186 0x02402c1060058218 0x6003e087187c19cd 0x66003e087187c19c

def z633 : W := mkw 0x8fb646e83ec8de08 0x08fb646e83ec8de0 0xffffe7f83ffcfe0f 0xfffffe7f83ffcfe0

def z634 : W := mkw 0x9ffffffffe85de58 0x99ffffffffe85de5 0xffffffffff8fffff 0xfffffffffff8ffff

def z635 : W := mkw 0x8bbc2ee83e85de08 0x08bbc2ee83e85de0 0xfffc7ff83f8ffe0f 0xffffc7ff83f8ffe0

def z636 : W := mkw 0x000c28194db76f75 0x8000c28194db76f7 0xe01c78ffffffffff 0x6e01c78fffffffff

def z637 : W := mkw 0x0008281140000000 0x0000828114000000 0x001c1878c0000002 0x0001c1878c000000

def z638 : W := mkw 0x2722c7c6b0d8f5a7 0x02722c7c6b0d8f5a 0xef03e7c7f87cfffd 0xfef03e7c7f87cfff

def z639 : W := mkw 0x1cdf78000c050000 0x01cdf78000c05000 0x5ffff8001c0f0007 0xf5ffff8001c0f000

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0xc003800020700004 0xec00380002070000

def z641 : W := mkw 0x000c28000c050000 0x0000c28000c05000 0x001c6000180c0001 0x0001c6000180c000

def z642 : W := mkw 0xdf9e6ca83e4d9a08 0x0df9e6ca83e4d9a0 0x0f1c60b8180c1801 0x10f1c60b8180c180

def z643 : W := mkw 0x2702c58630489082 0x02702c5863048908 0x0f03e787180c18cd 0xd0f03e787180c18c

def z644 : W := mkw 0x0008281140050050 0x8000828114005005 0x60007887d80f19fd 0x660007887d80f19f

def z645 : W := mkw 0x000400080db76f75 0x8000400080db76f7 0xe00000003ffffff0 0x2e00000003ffffff

def z646 : W := mkw 0x8b9004a032009008 0x08b9004a03200900 0x0f00000000000000 0x10f0000000000000

def z647 : W := mkw 0xafbeefff7eddffde 0x8afbeefff7eddffd 0xffffffffffffffff 0xffffffffffffffff

def z648 : W := mkw 0x899400083e80de08 0x0899400083e80de0 0xbffc00003f80fe03 0xfbffc00003f80fe0

def z649 : W := mkw 0x810c28197e85de58 0x8810c28197e85de5 0xe01c78ffff8fffff 0x6e01c78ffff8ffff

def z650 : W := mkw 0x9effffffce804e08 0x19effffffce804e0 0x1fffffffc780060f 0xd1fffffffc780060

def z651 : W := mkw 0x00008117c0000000 0x100008117c000000 0x00000007c0000000 0x000000007c000000

def z652 : W := mkw 0x2502c1063058b186 0x02502c1063058b18 0xe003e007387cf9c4 0x2e003e007387cf9c

def z653 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x001c007804000602 0x0001c00780400060

def z654 : W := mkw 0x5dff7a403fef4400 0x05dff7a403fef440 0xffffff403fffe60f 0xfffffff403fffe60

def z655 : W := mkw 0x0061934480000000 0x0006193448000000 0x70e39f44c403073e 0xe70e39f44c403073

def z656 : W := mkw 0x1efffff7cc050000 0x11efffff7cc05000 0x5fffffffdc0f000f 0xf5fffffffdc0f000

def z657 : W := mkw 0x0000001940000a50 0x80000001940000a5 0x600018ffc4031ffe 0x6600018ffc4031ff

def z658 : W := mkw 0x554b7800316f0000 0x0554b7800316f000 0xcf03f800387f0005 0xfcf03f800387f000

def z659 : W := mkw 0x9efbffffc080de08 0x19efbffffc080de0 0x3fffffffc000fe0f 0xd3fffffffc000fe0

def z660 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x4f1ff800187f0005 0x14f1ff800187f000

def z661 : W := mkw 0x89b402683e804e08 0x089b402683e804e0 0x9ffc00783f800603 0xf9ffc00783f80060

def z662 : W := mkw 0x7fd3d586337ab186 0x07fd3d586337ab18 0x9fe3870023f0e000 0x99fe3870023f0e00

def z663 : W := mkw 0x8b9404a83e80de08 0x08b9404a83e80de0 0xaf1c00b83f80fe01 0x3af1c00b83f80fe0

def z664 : W := mkw 0x0061934480102104 0x0006193448010210 0xf0e39f44e070e10e 0xef0e39f44e070e10

def z665 : W := mkw 0x000400080c050a50 0x8000400080c050a5 0x600060871c0f1ffd 0x6600060871c0f1ff

def z666 : W := mkw 0x3ff3d7e6b058b186 0x13ff3d7e6b058b18 0x9fe387002070e000 0x99fe387002070e00

def z667 : W := mkw 0xbffffffffed8ff8e 0x1bffffffffed8ff8 0xfffffffffffcffcf 0xffffffffffffcffc

def z668 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x001c003800000000 0x0001c00380000000

def z669 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fe3ff07c0000004 0x91fe3ff07c000000

def z670 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x2f006787180cf9c9 0x12f006787180cf9c

def z671 : W := mkw 0x3ffbfff7f058b186 0x13ffbfff7f058b18 0x9fffffffe070e00f 0xd9fffffffe070e00

def z672 : W := mkw 0x544bf917c16f0000 0x1544bf917c16f000 0x4003f807c07f0004 0x04003f807c07f000

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000400400060a 0x6200000400400060

def z674 : W := mkw 0x0000810400102104 0x0000081040010210 0xe0039f44e473e73e 0xee0039f44e473e73

def z675 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x2f1c07f81800fe09 0x12f1c07f81800fe0

def z676 : W := mkw 0x0020834480906525 0x0002083448090652 0xe0038744e070e73c 0xee0038744e070e73

def z677 : W := mkw 0x250240003058b186 0x0250240003058b18 0xef03e000387cf9c5 0xfef03e000387cf9c

def z678 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xa01c00f83f80fe0b 0x6a01c00f83f80fe0

def z679 : W := mkw 0xffffffee3fffff8e 0x0ffffffee3fffff8 0xffffffff3fffffcf 0xfffffffff3fffffc

def z680 : W := mkw 0xa722c7ee30d8ff8e 0x0a722c7ee30d8ff8 0xef03e7ff387cffcd 0xfef03e7ff387cffc

def z681 : W := mkw 0x822006e80080de08 0x0822006e80080de0 0xb0e007f82780fe0a 0xeb0e007f82780fe0

def z682 : W := mkw 0x1cdf78194c050a50 0x81cdf78194c050a5 0x7ffff8ffdc0f1fff 0xf7ffff8ffdc0f1ff

def z683 : W := mkw 0x1cfbfb4481b26525 0x01cfbfb4481b2652 0xffffff44e7f3e73f 0xfffffff44e7f3e73

def z684 : W := mkw 0x54435000016a0000 0x054435000016a000 0x0003800000700000 0x0000380000070000

def z685 : W := mkw 0x5ff3d7e6b36a0000 0x15ff3d7e6b36a000 0x9fe3870023f00000 0x99fe3870023f0000

def z686 : W := mkw 0x2702448230489082 0x0270244823048908 0xcf03e083387c18c5 0xfcf03e083387c18c

def z687 : W := mkw 0x546bfb4481ff6525 0x0546bfb4481ff652 0xf0e3ff44e7ffe73e 0xef0e3ff44e7ffe73

def z688 : W := mkw 0x270e6c9b7c4d9ad2 0x8270e6c9b7c4d9ad 0x6f1c78ffdc0f1fff 0x76f1c78ffdc0f1ff

def z689 : W := mkw 0x022cafffcc050a50 0x9022cafffcc050a5 0x601c7fffdc0f1fff 0x6601c7fffdc0f1ff

def z690 : W := mkw 0x0000810400102104 0x0000081040010210 0x4003800400700104 0x0400380040070010

def z691 : W := mkw 0x3ff3d7e6b058b186 0x13ff3d7e6b058b18 0xffe3e787387cf9cd 0xfffe3e787387cf9c

def z692 : W := mkw 0xdddf78083fefde08 0x0dddf78083fefde0 0xfffff8003ffffe07 0xffffff8003ffffe0

def z693 : W := mkw 0x1cfbfb77c0000000 0x11cfbfb77c000000 0x10fff87fc0000006 0x010fff87fc000000

def z694 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e3870423f0e10c 0xef0e3870423f0e10

def z695 : W := mkw 0x0602c58600000000 0x00602c5860000000 0x6f03e787180c19cd 0xf6f03e787180c19c

def z696 : W := mkw 0xdfbe6ee83ecdde08 0x0dfbe6ee83ecdde0 0xbffc67f83f8cfe0b 0xfbffc67f83f8cfe0

def z697 : W := mkw 0x3fdbfd863058b186 0x03fdbfd863058b18 0xffffff87387cf9cf 0xfffffff87387cf9c

def z698 : W := mkw 0x006d3a59cda74e71 0x8006d3a59cda74e7 0x70fc78ffdf8f1fff 0x670fc78ffdf8f1ff

def z699 : W := mkw 0x0000810480102125 0x0000081048010212 0x00000004c0000130 0x000000004c000013

def z700 : W := mkw 0x200000000010b186 0x0200000000010b18 0x200000000000f9c0 0x0200000000000f9c

def z701 : W := mkw 0x000c28114c050050 0x8000c28114c05005 0x401c7807dc0f01f7 0x6401c7807dc0f01f

def z702 : W := mkw 0x2702c59f7058bbd6 0x82702c59f7058bbd 0xef03e7fff87cfffd 0xfef03e7fff87cfff

def z703 : W := mkw 0x830404883e80de08 0x0830404883e80de0 0xaf0007803f80fe09 0xfaf0007803f80fe0

def z704 : W := mkw 0x000400194c000a50 0x8000400194c000a5 0x201c00ffdc001ffb 0x6201c00ffdc001ff

def z705 : W := mkw 0x5fffffe6bf6f0000 0x15fffffe6bf6f000 0xdfffff003fff0007 0xfdfffff003fff000

def z706 : W := mkw 0x230085863010b186 0x0230085863010b18 0xaf0007873800f9c9 0xfaf0007873800f9c

def z707 : W := mkw 0x1a982cb140000000 0x11a982cb14000000 0x0f1c00b800000001 0x10f1c00b80000000

def z708 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc67fb3f8cfecb 0xfbffc67fb3f8cfec

def z709 : W := mkw 0x010400083c4d0a50 0x8010400083c4d0a5 0xe00000003c7f1ff0 0x2e00000003c7f1ff

def z710 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xbfffffffe3f0e73f 0xdbfffffffe3f0e73

def z711 : W := mkw 0x5dd750003f6a0000 0x05dd750003f6a000 0x9fff80003bf00001 0x99fff80003bf0000

def z712 : W := mkw 0x1cfb7a71c0000000 0x11cfb7a71c000000 0x1fff9878c0000002 0x91fff9878c000000

def z713 : W := mkw 0x066bffd7c1b26525 0x0066bffd7c1b2652 0xffffffffe7f3e73f 0xfffffffffe7f3e73

def z714 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff8bf3fff19cf 0xffffff8bf3fff19c

def z715 : W := mkw 0x0eb2c7e600000000 0x00eb2c7e60000000 0x1fff87f80000000b 0xd1fff87f80000000

def z716 : W := mkw 0x954ff91ffe80de08 0x1954ff91ffe80de0 0xa003f807ff80fe04 0x2a003f807ff80fe0

def z717 : W := mkw 0x1e9aedb740000000 0x11e9aedb74000000 0x0f1fffffc000000f 0xd0f1fffffc000000

def z718 : W := mkw 0x8bb82ef17285d458 0x88bb82ef17285d45 0xdfe07f07e38fe1f4 0x9dfe07f07e38fe1f

def z719 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1ffc67ff0000000f 0xd1ffc67ff0000000

def z720 : W := mkw 0xdddf78083f6f9a08 0x0dddf78083f6f9a0 0xdffff8003fff1807 0xfdffff8003fff180

def z721 : W := mkw 0x1efbfff7c0906525 0x11efbfff7c090652 0x1fffffffc000e00f 0xd1fffffffc000e00

def z722 : W := mkw 0x5ddb7811736a0000 0x05ddb7811736a000 0x9ffff8ffe3f0000f 0xd9ffff8ffe3f0000

def z723 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xe00000003f8cffc0 0x2e00000003f8cffc

def z724 : W := mkw 0x0d9640003e480000 0x00d9640003e48000 0x9fff80003ff00003 0xf9fff80003ff0000

def z725 : W := mkw 0x1cd3500001220000 0x01cd350000122000 0x9fe3800023f00000 0x99fe3800023f0000

def z726 : W := mkw 0x5dbeeb44bedd6525 0x05dbeeb44bedd652 0x2f1c6744d80ce739 0x12f1c6744d80ce73

def z727 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0ff9ffce7f3e73f 0xef0ff9ffce7f3e73

def z728 : W := mkw 0x5cdb7800016f0000 0x05cdb7800016f000 0xdffff80027ff0007 0xfdffff80027ff000

def z729 : W := mkw 0x410400083f6f0a00 0x0410400083f6f0a0 0xe00000003fff1e00 0x2e00000003fff1e0

def z730 : W := mkw 0x054f78197d6f0a50 0x8054f78197d6f0a5 0xfffff8ffffff1fff 0xffffff8ffffff1ff

def z731 : W := mkw 0x02082c9140000000 0x002082c914000000 0x0f1c7fffc000000f 0xd0f1c7fffc000000

def z732 : W := mkw 0x1ebaeff7c0000000 0x11ebaeff7c000000 0x0f1c7fffc000000f 0x50f1c7fffc000000

def z733 : W := mkw 0x8bb006e83280de08 0x08bb006e83280de0 0xbffc07f82380fe0b 0xdbffc07f82380fe0

def z734 : W := mkw 0x414510083f6f0a50 0x8414510083f6f0a5 0xf0e39844ffff1ffe 0xef0e39844ffff1ff

def z735 : W := mkw 0x814510083fa2de08 0x0814510083fa2de0 0xf0e398003ff3fe06 0xef0e398003ff3fe0

def z736 : W := mkw 0x5dd35019736a0a50 0x85dd35019736a0a5 0xbfe380ffe3f01ff8 0x9bfe380ffe3f01ff

def z737 : W := mkw 0xa22cafff4c95ffde 0x8a22cafff4c95ffd 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z738 : W := mkw 0x0af9bff5c0000000 0x00af9bff5c000000 0x1fffffffc000000f 0xd1fffffffc000000

def z739 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff8f83fff000f 0xfdffff8f83fff000

def z740 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e3ff44ffffe73f 0xef0e3ff44ffffe73

def z741 : W := mkw 0x5ddf78083f6f0a00 0x05ddf78083f6f0a0 0xfffff8003fff1e07 0xffffff8003fff1e0

def z742 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07fcff80ff3b 0xfbffc07fcff80ff3

def z743 : W := mkw 0x554f78003f6f0000 0x0554f78003f6f000 0x4003f800187f0004 0x04003f800187f000

def z744 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x9fffffffe780000f 0xf9fffffffe780000

def z745 : W := mkw 0x5efbfff7c16a0000 0x15efbfff7c16a000 0x1fffffffc070000f 0xd1fffffffc070000

def z746 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff8383fff0007 0xfdffff8383fff000

def z747 : W := mkw 0x1edb7cb340000000 0x11edb7cb34000000 0x1ffff8ffc000000f 0xd1ffff8ffc000000

def z748 : W := mkw 0x1e9a6cb341b26525 0x11e9a6cb341b2652 0xef1c60bb27f3e731 0x3ef1c60bb27f3e73

def z749 : W := mkw 0xacb6c36e0ed86f8e 0x0acb6c36e0ed86f8 0x50ffe07f07fc07c6 0x050ffe07f07fc07c

def z750 : W := mkw 0x1efbfff7c1220000 0x11efbfff7c122000 0x9fffffffe3f0000f 0xd9fffffffe3f0000

def z751 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xffff9f7ce7f3e73e 0xfffff9f7ce7f3e73

def z752 : W := mkw 0x432487f7ff6f0000 0x1432487f7ff6f000 0xc00007ffffff0008 0x2c00007ffffff000

def z753 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x7ffc1ffcc403073f 0xf7ffc1ffcc403073

def z754 : W := mkw 0x5ddf78117f6f0050 0x85ddf78117f6f005 0xdffff8ffffff01ff 0xfdffff8ffffff01f

def z755 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07b83f80f803 0xf9ffc07b83f80f80

def z756 : W := mkw 0x1efb7ef340000000 0x11efb7ef34000000 0x1ffffffb0000000f 0xd1ffffffb0000000

def z757 : W := mkw 0x0702448030489000 0x0070244803048900 0xef03e787387cf9cd 0xfef03e787387cf9c

def z758 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xffffff003fffe00f 0xfffffff003fffe00

def z759 : W := mkw 0xa22087e60090f58e 0x0a22087e60090f58 0x200007870000f9c8 0x0200007870000f9c

def z760 : W := mkw 0x0d92400032480000 0x00d9240003248000 0xdfe3e0003bfc0005 0xfdfe3e0003bfc000

def z761 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fff9ffcc000000f 0xd1fff9ffcc000000

def z762 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xa00007003f80fe08 0xea00007003f80fe0

def z763 : W := mkw 0x0602c58600102104 0x00602c5860010210 0xef03e787387cf9cd 0xfef03e787387cf9c

def z764 : W := mkw 0x1efbfff7c1372175 0x91efbfff7c137217 0x5fffffffc07f01ff 0xd5fffffffc07f01f

def z765 : W := mkw 0x1ebaeff7c0000000 0x11ebaeff7c000000 0x0f1c67bb00000001 0x10f1c67bb0000000

def z766 : W := mkw 0x1ef3d7e681b26525 0x11ef3d7e681b2652 0xbfff87f827f0e60b 0xfbfff87f827f0e60

def z767 : W := mkw 0x1efbfff7c1220021 0x11efbfff7c122002 0x1fffffffc003003f 0xd1fffffffc003003

def z768 : W := mkw 0x5efbfff7c3220000 0x15efbfff7c322000 0x1fffffffc380000f 0xd1fffffffc380000

def z769 : W := mkw 0x3efbfff7c1fa65a7 0x13efbfff7c1fa65a 0xffffffffe7ffe7ff 0xfffffffffe7ffe7f

def z770 : W := mkw 0x5ddb7800336f0000 0x05ddb7800336f000 0x9fe3e00023fc0000 0x99fe3e00023fc000

def z771 : W := mkw 0x08d1100001220000 0x008d110000122000 0xdfff980027f30007 0xfdfff980027f3000

def z772 : W := mkw 0x222087f7c090f5a7 0x1222087f7c090f5a 0x200007ffc000fff8 0x0200007ffc000fff

def z773 : W := mkw 0x0af116e080000000 0x00af116e08000000 0x1ffc1ff8c000000b 0xd1ffc1ff8c000000

def z774 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffffffd80c18cf 0xd1fffffffd80c18c

def z775 : W := mkw 0x1efbfff7c0050050 0x91efbfff7c005005 0x7fffffffc40f07ff 0xf7fffffffc40f07f

def z776 : W := mkw 0x0061124001a24400 0x00061124001a2440 0xf0e39f44e7f3e73e 0xef0e39f44e7f3e73

def z777 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x40007807d80f19f4 0x040007807d80f19f

def z778 : W := mkw 0x0141100031220000 0x0014110003122000 0xdfe398003ff30007 0xfdfe398003ff3000

def z779 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0x800000003b80f800 0x0800000003b80f80

def z780 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9ffff80027f30007 0xd9ffff80027f3000

def z781 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e39fc4fff3ff3f 0xef0e39fc4fff3ff3

def z782 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x601c78ffd80f1ffd 0x0601c78ffd80f1ff

def z783 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c60fb0000000b 0x50f1c60fb0000000

def z784 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x5ffff8001fff0007 0x15ffff8001fff000

def z785 : W := mkw 0x0ef3d7e681b26525 0x00ef3d7e681b2652 0xffffffffe7f3e73f 0xfffffffffe7f3e73

def z786 : W := mkw 0x5ddb7800336a0000 0x05ddb7800336a000 0xdffff80027f30007 0xfdffff80027f3000

def z787 : W := mkw 0x1efb7ef3c0000000 0x11efb7ef3c000000 0x1ffc78ffc000000f 0x51ffc78ffc000000

def z788 : W := mkw 0x022cafffcc956f75 0x9022cafffcc956f7 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z789 : W := mkw 0x1cfb7a71c0000000 0x11cfb7a71c000000 0x1ffff8ffc000000f 0xd1ffff8ffc000000

def z790 : W := mkw 0x39f93a71f058b186 0x139f93a71f058b18 0xf0fc1878f87cf9c2 0x2f0fc1878f87cf9c

def z791 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03e707387cf9c4 0xbef03e707387cf9c

def z792 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0x000000001f801e00 0x0000000001f801e0

def z793 : W := mkw 0x062aeff7c0000000 0x1062aeff7c000000 0x0f1fffffc000000f 0xd0f1fffffc000000

def z794 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc07f83f83ff3b 0xffffc07f83f83ff3

def z795 : W := mkw 0x1ef3d7f7c0000000 0x11ef3d7f7c000000 0x1fff87ffc000000b 0xd1fff87ffc000000

def z796 : W := mkw 0x3efbfff7c0009082 0x13efbfff7c000908 0x1fffffffc00018cf 0xd1fffffffc00018c

def z797 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x0f1fffffc000000d 0x10f1fffffc000000

def z798 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdfe3f8003fff0004 0xbdfe3f8003fff000

def z799 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c67bb00000009 0xd0f1c67bb0000000

def z800 : W := mkw 0x1ebaeff7c0000000 0x11ebaeff7c000000 0x1ffc67ffc000000b 0xd1ffc67ffc000000

def z801 : W := mkw 0x0ebaeff740000000 0x00ebaeff74000000 0x1fffffffc000000f 0xd1fffffffc000000

def z802 : W := mkw 0x0ab406e80c804e00 0x00ab406e80c804e0 0xbffc07f83f80fe0b 0xfbffc07f83f80fe0

def z803 : W := mkw 0x5ddf78117f6f0050 0x85ddf78117f6f005 0xfffff847ffff07ff 0xffffff847ffff07f

def z804 : W := mkw 0x0ab087f7c0000000 0x10ab087f7c000000 0x0f1c07ffc0000009 0x10f1c07ffc000000

def z805 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xdfffffffe3f3e13f 0xddfffffffe3f3e13

def z806 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07382380e000 0x99ffc07382380e00

def z807 : W := mkw 0x8165934cbfb2ff2d 0x08165934cbfb2ff2 0xb0e387003ff0fe00 0xab0e387003ff0fe0

def z808 : W := mkw 0x1efb7ef3c1a24421 0x11efb7ef3c1a2442 0x1ffc78fbc7830633 0x11ffc78fbc783063

def z809 : W := mkw 0x822087e48090f52d 0x0822087e48090f52 0x20000744c000e738 0x020000744c000e73

def z810 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe3980023f00006 0xd9fe3980023f0000

def z811 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffe7bf0000000d 0xd1fffe7bf0000000

def z812 : W := mkw 0x544bf917c17f2125 0x1544bf917c17f212 0x4003f807c07f0134 0x04003f807c07f013

def z813 : W := mkw 0x810400083fb2ff2d 0x0810400083fb2ff2 0xa00000003ff0fe00 0x2a00000003ff0fe0

def z814 : W := mkw 0x010400083e000a00 0x0010400083e000a0 0xa00000003f801e00 0x2a00000003f801e0

def z815 : W := mkw 0x006dbb5dcdb76f75 0x8006dbb5dcdb76f7 0x90ffe7bb3bfcf8c1 0x890ffe7bb3bfcf8c

def z816 : W := mkw 0xa10400083ffaffaf 0x0a10400083ffaffa 0xe00000003ffffff0 0x2e00000003ffffff

def z817 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3e00023fc0004 0x9dfe3e00023fc000

def z818 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0x800000002780e600 0x0800000002780e60

def z819 : W := mkw 0x89b402683e80de08 0x089b402683e80de0 0xb0e000003f80fe00 0x2b0e000003f80fe0

def z820 : W := mkw 0x210400083dfffff7 0x8210400083dfffff 0xe00000003ffffff0 0x2e00000003ffffff

def z821 : W := mkw 0x0bb406e03e804400 0x00bb406e03e80440 0xbffc07f83f80e60b 0xfbffc07f83f80e60

def z822 : W := mkw 0x0af197e481322125 0x00af197e48132212 0x5fff9ffcc073013f 0xd5fff9ffcc073013

def z823 : W := mkw 0x270eed9f7c5dbbd6 0x8270eed9f7c5dbbd 0x8f1f9f78e473e632 0x98f1f9f78e473e63

def z824 : W := mkw 0xd66b7ee801efde08 0x0d66b7ee801efde0 0x6003fff8007ffe0c 0x06003fff8007ffe0

def z825 : W := mkw 0x5fff7ee03fef4400 0x05fff7ee03fef440 0xfffffff83fffe60f 0xffffffff83fffe60

def z826 : W := mkw 0x09dd38197f270a50 0x809dd38197f270a5 0xfffff8ffffff1fff 0xffffff8ffffff1ff

def z827 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc1ff8ff83fe3b 0xfbffc1ff8ff83fe3

def z828 : W := mkw 0x744bf917417f21d6 0x8744bf917417f21d 0x4003f807c07f01f4 0x04003f807c07f01f

def z829 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fff877800000002 0x91fff87780000000

def z830 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff844ffff000f 0xfdffff844ffff000

def z831 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x6f1c78ffc403073f 0x76f1c78ffc403073

def z832 : W := mkw 0x5efbfff7c1ff6525 0x15efbfff7c1ff652 0xffffffffe7ffe73f 0xfffffffffe7ffe73

def z833 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffe7ffc0000009 0x91fffe7ffc000000

def z834 : W := mkw 0x3e9aedb740582186 0x13e9aedb74058218 0x4f1fe0bf007c01c5 0x14f1fe0bf007c01c

def z835 : W := mkw 0x022087e680906525 0x1022087e68090652 0x20000744c000e738 0x020000744c000e73

def z836 : W := mkw 0xa22087ff4090ffde 0x8a22087ff4090ffd 0x200007ffc000fff8 0x0200007ffc000fff

def z837 : W := mkw 0x4165934cbfff6f75 0x84165934cbfff6f7 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z838 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1ffff8ffc0000007 0x11ffff8ffc000000

def z839 : W := mkw 0x000400080c000a00 0x0000400080c000a0 0x601c78ffdc0f1fff 0x6601c78ffdc0f1ff

def z840 : W := mkw 0x5ddb7800336a0000 0x05ddb7800336a000 0x9fff980023f00002 0x99fff980023f0000

def z841 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x1ffc60bb00000003 0xd1ffc60bb0000000

def z842 : W := mkw 0x8bb406e83e85de58 0x88bb406e83e85de5 0xbffc07f83f8cfecb 0xfbffc07f83f8cfec

def z843 : W := mkw 0x0a9004b340000000 0x10a9004b34000000 0x0f1c00bb00000001 0x10f1c00bb0000000

def z844 : W := mkw 0x0ab006e000804400 0x00ab006e00080440 0x9ffc07f82380e00b 0xd9ffc07f82380e00

def z845 : W := mkw 0x3efbfff7c010b186 0x13efbfff7c010b18 0xffffffffe070f9cf 0xfffffffffe070f9c

def z846 : W := mkw 0x0502c10430582104 0x00502c1043058210 0xef03e787387cf9cd 0xfef03e787387cf9c

def z847 : W := mkw 0x5e9a6cb3404d0000 0x15e9a6cb3404d000 0x0f1c60bb000c0001 0x10f1c60bb000c000

def z848 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xbfffffffe7f0e60f 0xfbfffffffe7f0e60

def z849 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe3980027f30002 0x99fe3980027f3000

def z850 : W := mkw 0x5d9e68003e4d0000 0x05d9e68003e4d000 0xdfffe0003ffc0007 0xfdfffe0003ffc000

def z851 : W := mkw 0x210828117058b186 0x0210828117058b18 0xe01c78fff87cf9cf 0x6e01c78fff87cf9c

def z852 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0xf0fc78ffff8f1fff 0xef0fc78ffff8f1ff

def z853 : W := mkw 0x8ab406e80e80de08 0x08ab406e80e80de0 0x3ffc07f80780fe0b 0xd3ffc07f80780fe0

def z854 : W := mkw 0xa10400083eddffde 0x8a10400083eddffd 0xe00000003ffffff0 0x2e00000003ffffff

def z855 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x3fffffffc783e73f 0xd3fffffffc783e73

def z856 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff8bb3fff1ff7 0xffffff8bb3fff1ff

def z857 : W := mkw 0x5ddb7800336a0000 0x05ddb7800336a000 0x9fe3f80023f00004 0x99fe3f80023f0000

def z858 : W := mkw 0x8ab406e80e804e08 0x08ab406e80e804e0 0xbffc07f82780e60b 0xfbffc07f82780e60

def z859 : W := mkw 0x410400083f6f0a50 0x8410400083f6f0a5 0xc00000003fff0630 0x2c00000003fff063

def z860 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xffe3e7873ffcf9cf 0xfffe3e7873ffcf9c

def z861 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe3800027f00002 0xf9fe3800027f0000

def z862 : W := mkw 0x2165934cbdfffff7 0x82165934cbdfffff 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z863 : W := mkw 0x1cdb781141220000 0x01cdb78114122000 0xfffff8ffe7f3073f 0xffffff8ffe7f3073

def z864 : W := mkw 0x1e9a6cb340050050 0x91e9a6cb34005005 0x0f1c60bb000c00c1 0x10f1c60bb000c00c

def z865 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0x9ffc07782380e002 0x99ffc07782380e00

def z866 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0xbffc07f82780e60b 0xfbffc07f82780e60

def z867 : W := mkw 0x1ef7d7ee8c050a50 0x91ef7d7ee8c050a5 0x7fe387001c0f1ff0 0xb7fe387001c0f1ff

def z868 : W := mkw 0x7addbd860f37b186 0x07addbd860f37b18 0x30fc1f870783f9ca 0x030fc1f870783f9c

def z869 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc67f83f8cfe0f 0xffffc67f83f8cfe0

def z870 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0x9ffc07b82380e001 0x99ffc07b82380e00

def z871 : W := mkw 0x1af9bff5c0000000 0x11af9bff5c000000 0x1fff9ffcc000000f 0xd1fff9ffcc000000

def z872 : W := mkw 0x3efbfff7c0102186 0x13efbfff7c010218 0x1fffffffc00001cf 0xd1fffffffc00001c

def z873 : W := mkw 0x1edb7cb340000000 0x11edb7cb34000000 0x1fffe0bb00000001 0x91fffe0bb0000000

def z874 : W := mkw 0x5ddf78117f6f0000 0x05ddf78117f6f000 0xdffff8bb3fff0007 0xfdffff8bb3fff000

def z875 : W := mkw 0x8ab006e80080de08 0x08ab006e80080de0 0xbffc07f82780fe0b 0xfbffc07f82780fe0

def z876 : W := mkw 0x8bb406e03e80d408 0x08bb406e03e80d40 0x9ffc07f83f80e00b 0xf9ffc07f83f80e00

def z877 : W := mkw 0x5ddf78083f6f0a00 0x05ddf78083f6f0a0 0xdffff8b83fff1807 0xfdffff8b83fff180

def z878 : W := mkw 0x1efbfff7c1a24421 0x11efbfff7c1a2442 0x7fffffffc783073f 0xf7fffffffc783073

def z879 : W := mkw 0x1ddf78003f220000 0x01ddf78003f22000 0xdffff8003ff30007 0xfdffff8003ff3000

def z880 : W := mkw 0x0ab087e400000000 0x00ab087e40000000 0x1fff87fc0000000f 0xd1fff87fc0000000

def z881 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fff87b800000001 0x91fff87b80000000

def z882 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x8f03e787387cf8cd 0xd8f03e787387cf8c

def z883 : W := mkw 0x8ab006e002804408 0x08ab006e00280440 0x1ffc07f80380000b 0xd1ffc07f80380000

def z884 : W := mkw 0x1efbfff7c0102104 0x11efbfff7c010210 0x5fffffffc070010f 0xd5fffffffc070010

def z885 : W := mkw 0x0061124081a24421 0x00061124081a2442 0xf0e39f40e7f3e63e 0xef0e39f40e7f3e63

def z886 : W := mkw 0x09d1100033220000 0x009d110003322000 0xdfe3980027f30006 0xfdfe3980027f3000

def z887 : W := mkw 0x8165934cbe80de08 0x08165934cbe80de0 0xb0e39f44ff80fe0e 0xeb0e39f44ff80fe0

def z888 : W := mkw 0x0ab087e400102104 0x00ab087e40010210 0xffff87fc2070e10f 0xfffff87fc2070e10

def z889 : W := mkw 0x222cafdfcc95fff7 0x8222cafdfcc95fff 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z890 : W := mkw 0x1efbfff7c1322125 0x11efbfff7c132212 0xffffffffe073e13f 0xfffffffffe073e13

def z891 : W := mkw 0xa22487ee0c90ff8e 0x0a22487ee0c90ff8 0x601c67ff1c0cffcf 0x6601c67ff1c0cffc

def z892 : W := mkw 0xa124834c3ed8ff8e 0x0a124834c3ed8ff8 0xf0e387443ffcffce 0xef0e387443ffcffc

def z893 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07f83b80f80b 0xd9ffc07f83b80f80

def z894 : W := mkw 0x410400083e4d0a50 0x8410400083e4d0a5 0x00000000180c18c0 0x000000000180c18c

def z895 : W := mkw 0x0000000000000000 0x0000000000000000 0x201c00f80400060b 0x6201c00f80400060

def z896 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x9ffc07f82780000b 0xf9ffc07f82780000

def z897 : W := mkw 0x1efbfff7c0102104 0x11efbfff7c010210 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z898 : W := mkw 0x344bf917c17a21a7 0x1344bf917c17a21a 0x4003f807c07f01f4 0x04003f807c07f01f

def z899 : W := mkw 0x0020834400906504 0x0002083440090650 0xf0e39f44e7f3e73e 0xef0e39f44e7f3e73

def z900 : W := mkw 0x1efb7ef3c0000000 0x11efb7ef3c000000 0x1ffc60bb00000001 0x11ffc60bb0000000

def z901 : W := mkw 0x3efbfff7c05d21d6 0x93efbfff7c05d21d 0x5fffffffc07f01ff 0xd5fffffffc07f01f

def z902 : W := mkw 0x0ab006f1c0000000 0x10ab006f1c000000 0x1ffc07f8c000000b 0xd1ffc07f8c000000

def z903 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xb0e39f44e7f3e73a 0x8b0e39f44e7f3e73

def z904 : W := mkw 0x022087e680906525 0x1022087e68090652 0x000007000000e000 0x0000007000000e00

def z905 : W := mkw 0x822487ec8c90ff2d 0x0822487ec8c90ff2 0x601c1ffcdc03ff3f 0x6601c1ffcdc03ff3

def z906 : W := mkw 0x1efbfff7c1220000 0x11efbfff7c122000 0x1fffffffc783000f 0xd1fffffffc783000

def z907 : W := mkw 0x810400083e85de08 0x0810400083e85de0 0xe00000003f8ffe00 0x2e00000003f8ffe0

def z908 : W := mkw 0x8145910cbfb2ff2d 0x08145910cbfb2ff2 0xe0039804fff3ff34 0x2e0039804fff3ff3

def z909 : W := mkw 0x1efbfff7c1322104 0x11efbfff7c132210 0xffffffffe7f3e10f 0xfffffffffe7f3e10

def z910 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c78bb00000007 0x50f1c78bb0000000

def z911 : W := mkw 0x1efbffe680000000 0x11efbffe68000000 0x1ffffff80000000f 0xd1ffffff80000000

def z912 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffffffc403063f 0xd1fffffffc403063

def z913 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdfffe0003bfc0005 0xfdfffe0003bfc000

def z914 : W := mkw 0xa10400083e489a8a 0x0a10400083e489a8 0x00000000180c18c0 0x000000000180c18c

def z915 : W := mkw 0xa10400083ec8de8a 0x0a10400083ec8de8 0xa00000003f8cfec0 0x2a00000003f8cfec

def z916 : W := mkw 0x0ab006e000804400 0x00ab006e00080440 0x3ffc07f80000e60b 0xd3ffc07f80000e60

def z917 : W := mkw 0x410400083f6f0a50 0x8410400083f6f0a5 0xc00000003fff18c0 0x2c00000003fff18c

def z918 : W := mkw 0x0ab087e680000000 0x10ab087e68000000 0x1ffc07f80000000b 0xd1ffc07f80000000

def z919 : W := mkw 0x1cdbf917c0000000 0x11cdbf917c000000 0x1ffff8ffc000000f 0xd1ffff8ffc000000

def z920 : W := mkw 0x1edb7cb341220000 0x11edb7cb34122000 0xdffff8bb27f30007 0xfdffff8bb27f3000

def z921 : W := mkw 0x1ddb7800316a0000 0x01ddb7800316a000 0xdffff8003fff0007 0xfdffff8003fff000

def z922 : W := mkw 0x276356c2b1ead4a3 0x0276356c2b1ead4a 0x1fe078c3df8f1ef3 0x11fe078c3df8f1ef

def z923 : W := mkw 0xa22087e60090f58e 0x0a22087e60090f58 0x000007000000e000 0x0000007000000e00

def z924 : W := mkw 0x810400083e80de58 0x8810400083e80de5 0xa00000003f80fff0 0x2a00000003f80fff

def z925 : W := mkw 0x0eb246e000000000 0x00eb246e00000000 0x1fffe7f80000000f 0xd1fffe7f80000000

def z926 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07f82780e60b 0xd9ffc07f82780e60

def z927 : W := mkw 0x222087c68090f5a7 0x0222087c68090f5a 0x200007870000f9c8 0x0200007870000f9c

def z928 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x6f1c60bf180c19cd 0x76f1c60bf180c19c

def z929 : W := mkw 0x5dd750003f6a0000 0x05dd750003f6a000 0x9fff800027f00002 0x99fff800027f0000

def z930 : W := mkw 0x1efbfff7c0804400 0x11efbfff7c080440 0x9fffffffe380e00f 0xd9fffffffe380e00

def z931 : W := mkw 0x5dd750083f6f0a50 0x85dd750083f6f0a5 0xffe380003fff1ff0 0xbffe380003fff1ff

def z932 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8c7ffff1fff 0xffffff8c7ffff1ff

def z933 : W := mkw 0x1cfbfb77c0000000 0x11cfbfb77c000000 0x1ffff87fc0000007 0xd1ffff87fc000000

def z934 : W := mkw 0x1cdb781140000000 0x01cdb78114000000 0x1ffff8bb00000007 0xd1ffff8bb0000000

def z935 : W := mkw 0x022087e480906525 0x0022087e48090652 0x200007fcc000e738 0x0200007fcc000e73

def z936 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff807ffff1ff7 0xffffff807ffff1ff

def z937 : W := mkw 0x610400083f7fbbd6 0x8610400083f7fbbd 0xe00000003ffffff0 0x2e00000003ffffff

def z938 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xe0001844ff83ff3e 0x6e0001844ff83ff3

def z939 : W := mkw 0x18fd3a79cda74e71 0x918fd3a79cda74e7 0x10fc1878c7830632 0x010fc1878c783063

def z940 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c78fbc0000003 0x10f1c78fbc000000

def z941 : W := mkw 0x222087c68090f5a7 0x0222087c68090f5a 0x20000744c000e738 0x020000744c000e73

def z942 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xffff87f83ff0fe0f 0xfffff87f83ff0fe0

def z943 : W := mkw 0x022087ffc0906f75 0x9022087ffc0906f7 0x200007ffc000fff8 0x0200007ffc000fff

def z944 : W := mkw 0x3efbfff7c0582186 0x13efbfff7c058218 0x7fffffffd87c19cf 0xf7fffffffd87c19c

def z945 : W := mkw 0x7ddf78003f6f9082 0x07ddf78003f6f908 0xdffff8003fff18c7 0xfdffff8003fff18c

def z946 : W := mkw 0x1edb7cb340000000 0x11edb7cb34000000 0x0f1ff8bb00000005 0x10f1ff8bb0000000

def z947 : W := mkw 0x5ddb7800336f0000 0x05ddb7800336f000 0xdfe3f8003bff0005 0xfdfe3f8003bff000

def z948 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xd0e39f44e7f3e736 0x8d0e39f44e7f3e73

def z949 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff840ffff0637 0xfdffff840ffff063

def z950 : W := mkw 0x0890000000000000 0x0089000000000000 0x9ffc000027800003 0xf9ffc00002780000

def z951 : W := mkw 0x1e9aedb740000000 0x11e9aedb74000000 0x0f1fe7bb00000001 0x90f1fe7bb0000000

def z952 : W := mkw 0x810400083fa2de08 0x0810400083fa2de0 0xe00000003ff3fe00 0x2e00000003ff3fe0

def z953 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffffbfc0000005 0x91fffffbfc000000

def z954 : W := mkw 0x5efbfff7c16f0050 0x95efbfff7c16f005 0x5fffffffc07f01ff 0xd5fffffffc07f01f

def z955 : W := mkw 0x554b7800316f0000 0x0554b7800316f000 0xdfe3f8003fff0007 0xfdfe3f8003fff000

def z956 : W := mkw 0x022087c680906525 0x0022087c68090652 0x200007c7c000e738 0x0200007c7c000e73

def z957 : W := mkw 0x0890000000000000 0x0089000000000000 0x1ffc00f80000000b 0xd1ffc00f80000000

def z958 : W := mkw 0x05435000316a0000 0x005435000316a000 0x9fe3800023f00000 0x99fe3800023f0000

def z959 : W := mkw 0x060a6c9340000000 0x0060a6c934000000 0x0f1c78ffc000000f 0x50f1c78ffc000000

def z960 : W := mkw 0x5dd750003f6a0000 0x05dd750003f6a000 0x9fe380003ff00000 0xb9fe380003ff0000

def z961 : W := mkw 0x810400083e009a08 0x0810400083e009a0 0xa00000003800f800 0x2a00000003800f80

def z962 : W := mkw 0xdf9e6cb97e4d9a58 0x8df9e6cb97e4d9a5 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z963 : W := mkw 0x9efbfff7c080d408 0x19efbfff7c080d40 0x1fffffffc000e00f 0xd1fffffffc000e00

def z964 : W := mkw 0x1efbfff7c1a24400 0x11efbfff7c1a2440 0xffffffffe7f3e60f 0xfffffffffe7f3e60

def z965 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x5fffffffd80c000f 0xf5fffffffd80c000

def z966 : W := mkw 0x0ab006e001b26525 0x00ab006e001b2652 0xfffc07f827f3e73b 0xffffc07f827f3e73

def z967 : W := mkw 0x1e9aedb740000000 0x11e9aedb74000000 0x0f1c67bf00000009 0x10f1c67bf0000000

def z968 : W := mkw 0x0d9e68003e4d0000 0x00d9e68003e4d000 0xdffff8003fff0007 0xfdffff8003fff000

def z969 : W := mkw 0x0ab8aff7c0000000 0x10ab8aff7c000000 0x1ffc7fffc000000f 0xd1ffc7fffc000000

def z970 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x7ffc67ff180c19cf 0xf7ffc67ff180c19c

def z971 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x201c78ffdc0f1ffb 0x0201c78ffdc0f1ff

def z972 : W := mkw 0xe10400083fffff8e 0x0e10400083fffff8 0xe00000003fffffc0 0x2e00000003fffffc

def z973 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe380003bfc0000 0xbdfe380003bfc000

def z974 : W := mkw 0x060aed9740000000 0x0060aed974000000 0x0f1fe7bf0000000d 0xd0f1fe7bf0000000

def z975 : W := mkw 0x4d9640003f6f0000 0x04d9640003f6f000 0xdfffe0003fff0007 0xfdfffe0003fff000

def z976 : W := mkw 0x1e9aedb7c0000000 0x11e9aedb7c000000 0x0f1c60bfc0000001 0x10f1c60bfc000000

def z977 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xaf03e783387cf8c9 0xfaf03e783387cf8c

def z978 : W := mkw 0x144bf917c1322125 0x1144bf917c132212 0x0003f807c0700004 0x00003f807c070000

def z979 : W := mkw 0x1efbfff7c0050050 0x91efbfff7c005005 0x1fffffffc003003f 0xd1fffffffc003003

def z980 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1ffc1ffcc000000f 0xd1ffc1ffcc000000

def z981 : W := mkw 0x0af197f7c0000000 0x10af197f7c000000 0x1fff9fffc000000f 0xd1fff9fffc000000

def z982 : W := mkw 0x1e9a6cb340050050 0x91e9a6cb34005005 0x4f1c78bfc00f01f5 0x14f1c78bfc00f01f

def z983 : W := mkw 0x0af9bff5c1b26525 0x00af9bff5c1b2652 0xffffffffe7f3e73f 0xfffffffffe7f3e73

def z984 : W := mkw 0x222087dfc090fff7 0x8222087dfc090fff 0x200007ffc000fff8 0x0200007ffc000fff

def z985 : W := mkw 0xa10400083ed8ff8e 0x0a10400083ed8ff8 0xa00000003ff0fe00 0x2a00000003ff0fe0

def z986 : W := mkw 0x05435000316a0000 0x005435000316a000 0xffe3f8c7ffff1fff 0xfffe3f8c7ffff1ff

def z987 : W := mkw 0x810c28197e85de58 0x8810c28197e85de5 0xe0007807ff8ffff4 0x2e0007807ff8ffff

def z988 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xffe3e0873bfc19cd 0xfffe3e0873bfc19c

def z989 : W := mkw 0x3efbfff7c0582186 0x13efbfff7c058218 0x1fffffffc070000f 0xd1fffffffc070000

def z990 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0xe01ff8fffc7f1fff 0xee01ff8fffc7f1ff

def z991 : W := mkw 0x1ef3d7e680000000 0x11ef3d7e68000000 0x1fffe7ff0000000f 0xd1fffe7ff0000000

def z992 : W := mkw 0x1efbfff7c0050050 0x91efbfff7c005005 0x1fffffffc00c00cf 0xd1fffffffc00c00c

def z993 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffff7fc0000006 0x91fffff7fc000000

def z994 : W := mkw 0x1c9a683140000000 0x11c9a68314000000 0x0f1c603800000001 0x10f1c60380000000

def z995 : W := mkw 0x0d9e68197e4d0a50 0x80d9e68197e4d0a5 0xfffff8ffffff1fff 0xffffff8ffffff1ff

def z996 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8403fff060f 0xffffff8403fff060

def z997 : W := mkw 0x1edbfdb7c0000000 0x11edbfdb7c000000 0x0f1ff8ffc000000f 0x50f1ff8ffc000000

def z998 : W := mkw 0x3efbfff7c1b2f5a7 0x13efbfff7c1b2f5a 0xffffffffe7f3ffff 0xfffffffffe7f3fff

def z999 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0xbfffffffe000e00f 0xfbfffffffe000e00

def z1000 : W := mkw 0x1efb7ef1c0000000 0x11efb7ef1c000000 0x1ffffff8c000000f 0xd1ffffff8c000000

def z1001 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff8003bff0005 0x9dffff8003bff000

def z1002 : W := mkw 0x1ef3d7e681b26525 0x11ef3d7e681b2652 0xffff9ffce7f3e73f 0xfffff9ffce7f3e73

def z1003 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x5fffffffc7f3073f 0xd5fffffffc7f3073

def z1004 : W := mkw 0x1efb7ef140000000 0x01efb7ef14000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1005 : W := mkw 0x1cdb783140000000 0x11cdb78314000000 0x1ffff83800000007 0xd1ffff8380000000

def z1006 : W := mkw 0x5dd750003f6f0000 0x05dd750003f6f000 0xdfff80003fff0003 0xfdfff80003fff000

def z1007 : W := mkw 0x1c9a681140000000 0x01c9a68114000000 0x0f1c78ffc000000f 0x50f1c78ffc000000

def z1008 : W := mkw 0x0502400030480000 0x0050240003048000 0xdfe3e0003ffc0007 0xfdfe3e0003ffc000

def z1009 : W := mkw 0x0af116e081a24421 0x00af116e081a2442 0x1ffc1ff8c783063b 0xd1ffc1ff8c783063

def z1010 : W := mkw 0xd8fd3a794fa74e58 0x8d8fd3a794fa74e5 0x10fc1878c7830632 0x010fc1878c783063

def z1011 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xffffffffffffffff 0xffffffffffffffff

def z1012 : W := mkw 0x0d9640083e480a00 0x00d9640083e480a0 0xffffe0ff3ffc1fcf 0xfffffe0ff3ffc1fc

def z1013 : W := mkw 0x0ab82ef140804400 0x00ab82ef14080440 0xfffc7fffe783e73f 0xffffc7fffe783e73

def z1014 : W := mkw 0x0ab087e600000000 0x00ab087e60000000 0x1ffc07ff0000000b 0xd1ffc07ff0000000

def z1015 : W := mkw 0x1efbfff7c0050000 0x11efbfff7c005000 0x5fffffffc00f000f 0xd5fffffffc00f000

def z1016 : W := mkw 0x1c9a681140000000 0x01c9a68114000000 0x0f1c60bb00000001 0x10f1c60bb0000000

def z1017 : W := mkw 0x0228aff7c0906525 0x10228aff7c090652 0x601c7fffc403e73f 0x6601c7fffc403e73

def z1018 : W := mkw 0x1efbfff7c0102104 0x11efbfff7c010210 0xffffffffe473e73f 0xfffffffffe473e73

def z1019 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffff78c0000007 0xd1fffff78c000000

def z1020 : W := mkw 0x8ab006e00080d408 0x08ab006e00080d40 0x1ffc07f80000e00b 0xd1ffc07f80000e00

def z1021 : W := mkw 0x1edbfd9740000000 0x01edbfd974000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1022 : W := mkw 0x810400083e90ff2d 0x0810400083e90ff2 0xa00000003f80ff30 0x2a00000003f80ff3

def z1023 : W := mkw 0x5dd750003f6f0000 0x05dd750003f6f000 0xdfe3e0003fff0005 0xfdfe3e0003fff000

def z1024 : W := mkw 0x0ab82ef140000000 0x00ab82ef14000000 0x1ffc1ff8c000000b 0xd1ffc1ff8c000000

def z1025 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xdfffffffe7f3e00f 0xfdfffffffe7f3e00

def z1026 : W := mkw 0x5ddb7800336f0000 0x05ddb7800336f000 0xdfe3f80027ff0006 0xfdfe3f80027ff000

def z1027 : W := mkw 0x0041910401322104 0x0004191040132210 0xf0e39f44e7f3e73e 0xef0e39f44e7f3e73

def z1028 : W := mkw 0x1efbfff7c0480000 0x11efbfff7c048000 0x5fffffffc07c000f 0xd5fffffffc07c000

def z1029 : W := mkw 0x5efbfff7c1270000 0x15efbfff7c127000 0x1fffffffc003000f 0xd1fffffffc003000

def z1030 : W := mkw 0x09d1100033220000 0x009d110003322000 0x9fe3800023f00000 0x99fe3800023f0000

def z1031 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff87cffff073f 0xffffff87cffff073

def z1032 : W := mkw 0xabb406e83ec8de8a 0x0abb406e83ec8de8 0xbffc07f83f8cfecb 0xfbffc07f83f8cfec

def z1033 : W := mkw 0xa304858e3e90ff8e 0x0a304858e3e90ff8 0xa00007873f80ffc8 0x2a00007873f80ffc

def z1034 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x9fffe7bb23f0e001 0x99fffe7bb23f0e00

def z1035 : W := mkw 0x1cdb780001220000 0x01cdb78000122000 0x9ffff80023f00007 0xd9ffff80023f0000

def z1036 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xa00000803f80fe09 0x6a00000803f80fe0

def z1037 : W := mkw 0x1ef356e000000000 0x01ef356e00000000 0x1fff87f80000000b 0xd1fff87f80000000

def z1038 : W := mkw 0x8bb406e83e85de58 0x88bb406e83e85de5 0xfffc1ffcff8fffff 0xffffc1ffcff8ffff

def z1039 : W := mkw 0x3e9a6cb340480082 0x13e9a6cb34048008 0x0f1c60bb000c00c1 0x10f1c60bb000c00c

def z1040 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffe7fb0000000b 0xd1fffe7fb0000000

def z1041 : W := mkw 0x1eba6ee000000000 0x01eba6ee00000000 0x1ffc67f80000000b 0xd1ffc67f80000000

def z1042 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x0f1c07f800000009 0x10f1c07f80000000

def z1043 : W := mkw 0x0200048000000000 0x0020004800000000 0xaf0007802000e009 0xfaf0007802000e00

def z1044 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9fff98003ff30003 0xf9fff98003ff3000

def z1045 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe3e0003bfc0001 0x99fe3e0003bfc000

def z1046 : W := mkw 0xc16512483fefde08 0x0c16512483fefde0 0xf0e39f403ffffe0e 0xef0e39f403ffffe0

def z1047 : W := mkw 0x0dd750003f6a0000 0x00dd750003f6a000 0xdffff8003fff0007 0xfdffff8003fff000

def z1048 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff804ffff0137 0xfdffff804ffff013

def z1049 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0x6f03e787187cf9cd 0x16f03e787187cf9c

def z1050 : W := mkw 0xa10400083e90ff8e 0x0a10400083e90ff8 0xa00000003f80ffc0 0x2a00000003f80ffc

def z1051 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xb0e39f40e7f3e63a 0xeb0e39f40e7f3e63

def z1052 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdfffe0003fff0001 0xbdfffe0003fff000

def z1053 : W := mkw 0x1cfbfb55c0000000 0x01cfbfb55c000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1054 : W := mkw 0x554f78197f6f0a50 0x8554f78197f6f0a5 0xe003f807ffff1ff4 0x2e003f807ffff1ff

def z1055 : W := mkw 0x49d510003f6f0000 0x049d510003f6f000 0xdfff98003fff0007 0xfdfff98003fff000

def z1056 : W := mkw 0x08b0026000000000 0x008b002600000000 0x1ffc007800000003 0xd1ffc00780000000

def z1057 : W := mkw 0x1ebaeff7c0906525 0x11ebaeff7c090652 0x2f1c67ffc000e739 0x12f1c67ffc000e73

def z1058 : W := mkw 0x1af93ef1c0000000 0x11af93ef1c000000 0x1ffc18f8c0000003 0x11ffc18f8c000000

def z1059 : W := mkw 0x040a681140000000 0x0040a68114000000 0x0f1ff8ffc000000f 0xd0f1ff8ffc000000

def z1060 : W := mkw 0xc10400083fa7de08 0x0c10400083fa7de0 0xa00000003f83fe00 0x2a00000003f83fe0

def z1061 : W := mkw 0x032406c83c80de00 0x0032406c83c80de0 0xbffc07f83f80fe0b 0xfbffc07f83f80fe0

def z1062 : W := mkw 0x1e9aedb740102104 0x11e9aedb74010210 0xef1fe7bf2070e10d 0xfef1fe7bf2070e10

def z1063 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc7fffff8fffff 0xffffc7fffff8ffff

def z1064 : W := mkw 0x8bb406e83e85de58 0x88bb406e83e85de5 0xbffc07f83f83fe3b 0xfbffc07f83f83fe3

def z1065 : W := mkw 0x830404883e80de08 0x0830404883e80de0 0xa00007803f80fe08 0x2a00007803f80fe0

def z1066 : W := mkw 0x5dd750003f6f0000 0x05dd750003f6f000 0x9fe380003bfc0000 0x99fe380003bfc000

def z1067 : W := mkw 0x812402483e80de08 0x0812402483e80de0 0xb0e000403f80fe02 0x2b0e000403f80fe0

def z1068 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff87fffff07f7 0xfdffff87fffff07f

def z1069 : W := mkw 0xc10400083fffff2d 0x0c10400083fffff2 0xe00000003fffff30 0x2e00000003fffff3

def z1070 : W := mkw 0x5efb7ee0016f0000 0x05efb7ee0016f000 0x5ffffff8007f000f 0xd5ffffff8007f000

def z1071 : W := mkw 0x0ab82ef140050050 0x80ab82ef14005005 0x5ffc7fffc00f01ff 0xd5ffc7fffc00f01f

def z1072 : W := mkw 0x3efbfff7c090f5a7 0x13efbfff7c090f5a 0x3fffffffc000ffff 0xd3fffffffc000fff

def z1073 : W := mkw 0xdddf78283f6f0a08 0x0dddf78283f6f0a0 0xdffff8383fff0007 0xfdffff8383fff000

def z1074 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1ffc00f800000003 0x11ffc00f80000000

def z1075 : W := mkw 0x5dd750003f6a0000 0x05dd750003f6a000 0xdfff98003ff30007 0xfdfff98003ff3000

def z1076 : W := mkw 0x010400083c009a00 0x0010400083c009a0 0xa00000003c00fe00 0x2a00000003c00fe0

def z1077 : W := mkw 0x832406e83e80de08 0x0832406e83e80de0 0xa00007003f80fe00 0x2a00007003f80fe0

def z1078 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1ffc07b800000001 0x91ffc07b80000000

def z1079 : W := mkw 0x5ddf78117f6f0000 0x05ddf78117f6f000 0xdffff807ffff0007 0xfdffff807ffff000

def z1080 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x3fffffffc000073f 0xd3fffffffc000073

def z1081 : W := mkw 0x1cdb781140000000 0x01cdb78114000000 0x1ffff878c0000007 0xd1ffff878c000000

def z1082 : W := mkw 0x1efbfff7c1322125 0x11efbfff7c132212 0x7fffffffc473073f 0xf7fffffffc473073

def z1083 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xffe39844e7f3073e 0xfffe39844e7f3073

def z1084 : W := mkw 0x1cdf78000d270000 0x01cdf78000d27000 0xdffff8003fff0007 0xfdffff8003fff000

def z1085 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff80027ff0006 0x9dffff80027ff000

def z1086 : W := mkw 0x1efbfff7c1a24421 0x11efbfff7c1a2442 0x1fffffffc380000f 0xd1fffffffc380000

def z1087 : W := mkw 0x250ee91f7c5dbbd6 0x8250ee91f7c5dbbd 0xe003f807fc7ffff4 0x2e003f807fc7ffff

def z1088 : W := mkw 0x8124834cbe90ff2d 0x08124834cbe90ff2 0xa0000744ff80ff38 0x2a0000744ff80ff3

def z1089 : W := mkw 0x410400083fff6f75 0x8410400083fff6f7 0xe00000003ffffff0 0x2e00000003ffffff

def z1090 : W := mkw 0x1af9bff5c1b26525 0x11af9bff5c1b2652 0xffff9ffce7f3e73f 0xfffff9ffce7f3e73

def z1091 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xd0e39f40e7f3e636 0xed0e39f40e7f3e63

def z1092 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0xffffffffe3f0e10f 0xfffffffffe3f0e10

def z1093 : W := mkw 0xd54f78083fefde08 0x0d54f78083fefde0 0xe003f8003ffffe04 0x2e003f8003ffffe0

def z1094 : W := mkw 0x1efbfff7c0804421 0x11efbfff7c080442 0x1fffffffc000063f 0xd1fffffffc000063

def z1095 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff878ffff1ff7 0xffffff878ffff1ff

def z1096 : W := mkw 0x1af9bff7c0000000 0x11af9bff7c000000 0x1ffc1fffc000000b 0xd1ffc1fffc000000

def z1097 : W := mkw 0x1ebaeff7c0000000 0x11ebaeff7c000000 0x0f1fe7ffc000000d 0xd0f1fe7ffc000000

def z1098 : W := mkw 0x0ab006f140000000 0x00ab006f14000000 0x1ffc07ffc000000b 0xd1ffc07ffc000000

def z1099 : W := mkw 0x0008281140000000 0x0000828114000000 0x601c78ffdc0f1fff 0x6601c78ffdc0f1ff

def z1100 : W := mkw 0x222087c60090f586 0x0222087c60090f58 0x200007c70000ffc8 0x0200007c70000ffc

def z1101 : W := mkw 0x5ddf78117f6f0050 0x85ddf78117f6f005 0xfffff887ffff19ff 0xffffff887ffff19f

def z1102 : W := mkw 0x5dd750083f6a0a00 0x05dd750083f6a0a0 0xbfff80f83ff01e0b 0xfbfff80f83ff01e0

def z1103 : W := mkw 0x1edbfdb7c0000000 0x11edbfdb7c000000 0x0f1fffbfc000000d 0xd0f1fffbfc000000

def z1104 : W := mkw 0x2061934681b265a7 0x02061934681b265a 0xf0e39f47e7f3e7fe 0xef0e39f47e7f3e7f

def z1105 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07783f80fe02 0xbbffc07783f80fe0

def z1106 : W := mkw 0x1af93ef1c0000000 0x11af93ef1c000000 0x1ffc1f78c0000002 0x91ffc1f78c000000

def z1107 : W := mkw 0x0898281140000000 0x0089828114000000 0x1ffc78ffc000000f 0xd1ffc78ffc000000

def z1108 : W := mkw 0x7f9e6c9b7e4d9ad2 0x87f9e6c9b7e4d9ad 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z1109 : W := mkw 0x7ddf78023f6f0082 0x07ddf78023f6f008 0xdffff8033fff00c7 0xfdffff8033fff00c

def z1110 : W := mkw 0x1efbffe600000000 0x01efbffe60000000 0x1fffffff0000000f 0xd1fffffff0000000

def z1111 : W := mkw 0x3efbfff7c17a21a7 0x13efbfff7c17a21a 0x5fffffffc07f01ff 0xd5fffffffc07f01f

def z1112 : W := mkw 0x5efbfff7c16f0000 0x15efbfff7c16f000 0xdfffffffe7ff000f 0xfdfffffffe7ff000

def z1113 : W := mkw 0xa165934cbffaffaf 0x0a165934cbffaffa 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z1114 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e3ff47e7ffe7fe 0xef0e3ff47e7ffe7f

def z1115 : W := mkw 0x0af197e481b26525 0x00af197e481b2652 0x9fff87f823f0e00b 0xd9fff87f823f0e00

def z1116 : W := mkw 0x0e92c5a600000000 0x00e92c5a60000000 0x0f1fe7bf0000000d 0xd0f1fe7bf0000000

def z1117 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03ff873c7ff9cf 0xfef03ff873c7ff9c

def z1118 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x1ffc077800000002 0x91ffc07780000000

def z1119 : W := mkw 0x822087fdc090ff7d 0x8822087fdc090ff7 0x200007ffc000fff8 0x0200007ffc000fff

def z1120 : W := mkw 0x1efb7ef3c0000000 0x11efb7ef3c000000 0x1ffc7ffbc000000b 0xd1ffc7ffbc000000

def z1121 : W := mkw 0x5ddf78117f6f0050 0x85ddf78117f6f005 0xdffff800ffff0037 0xfdffff800ffff003

def z1122 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0xbffc07f82000e00b 0xfbffc07f82000e00

def z1123 : W := mkw 0x5ddf7811ff6f0000 0x15ddf7811ff6f000 0xdffff800ffff0007 0xfdffff800ffff000

def z1124 : W := mkw 0x810400083e804e08 0x0810400083e804e0 0x800000003f800600 0x2800000003f80060

def z1125 : W := mkw 0x1cfbfb75c0000000 0x11cfbfb75c000000 0x1fffff7cc000000f 0xd1fffff7cc000000

def z1126 : W := mkw 0x1efbfff7c0000050 0x91efbfff7c000005 0x1fffffffc00001ff 0xd1fffffffc00001f

def z1127 : W := mkw 0x18f93a71c0000000 0x118f93a71c000000 0x1ffc1878c0000003 0xd1ffc1878c000000

def z1128 : W := mkw 0x5edb7cb3416f0000 0x15edb7cb3416f000 0x4f1ff8bb007f0005 0x14f1ff8bb007f000

def z1129 : W := mkw 0x0443500001220000 0x0044350000122000 0xdfe3f80027f30007 0xfdfe3f80027f3000

def z1130 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xb0e000003f80fe02 0xeb0e000003f80fe0

def z1131 : W := mkw 0x5ddf7800bf6f0021 0x05ddf7800bf6f002 0xdffff800ffff0037 0xfdffff800ffff003

def z1132 : W := mkw 0x5ddf78083f6f0a00 0x05ddf78083f6f0a0 0xfffff8fcffff1f3f 0xffffff8fcffff1f3

def z1133 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xcf03e783387cf8c5 0xfcf03e783387cf8c

def z1134 : W := mkw 0x1edbfdb7c0000000 0x11edbfdb7c000000 0x1ffff8bfc0000007 0xd1ffff8bfc000000

def z1135 : W := mkw 0x1cdb780000000000 0x01cdb78000000000 0x1ffff8f80000000f 0xd1ffff8f80000000

def z1136 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03ff87f87ff9fd 0xfef03ff87f87ff9f

def z1137 : W := mkw 0x0eb246e200000000 0x00eb246e20000000 0x1ffc67fb0000000b 0xd1ffc67fb0000000

def z1138 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fffffbb00000007 0xd1fffffbb0000000

def z1139 : W := mkw 0x1efbfff7c0102125 0x11efbfff7c010212 0x1fffffffc000013f 0xd1fffffffc000013

def z1140 : W := mkw 0x822caffdcc95ff7d 0x8822caffdcc95ff7 0x601c7fffdc0fffff 0x6601c7fffdc0ffff

def z1141 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xe00000003f83ff30 0x2e00000003f83ff3

def z1142 : W := mkw 0x1cfb7a6000000000 0x01cfb7a600000000 0x1ffff87800000007 0xd1ffff8780000000

def z1143 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x3fffffffd800180f 0xf3fffffffd800180

def z1144 : W := mkw 0x88fd3a79cfa74e79 0x888fd3a79cfa74e7 0x10fc1878c7830632 0x010fc1878c783063

def z1145 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x5fffffffc003013f 0xd5fffffffc003013

def z1146 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e39fc7e7f3fffe 0xef0e39fc7e7f3fff

def z1147 : W := mkw 0x060a6c9340000000 0x0060a6c934000000 0x0f1c60bb00000001 0x10f1c60bb0000000

def z1148 : W := mkw 0x5ddf78003f6f9000 0x05ddf78003f6f900 0xfffff8003ffff807 0xffffff8003ffff80

def z1149 : W := mkw 0xc10400083e4d9a08 0x0c10400083e4d9a0 0x00000000180c1800 0x000000000180c180

def z1150 : W := mkw 0x8104810c3e90ff0c 0x08104810c3e90ff0 0xe00387043ff0ff0c 0xee00387043ff0ff0

def z1151 : W := mkw 0xc10400083ecdde08 0x0c10400083ecdde0 0xa00000003f8cfe00 0x2a00000003f8cfe0

def z1152 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0xe01c7ffffc0fffff 0xee01c7ffffc0ffff

def z1153 : W := mkw 0x1efbfff7c0009000 0x11efbfff7c000900 0x3fffffffc000f80f 0xd3fffffffc000f80

def z1154 : W := mkw 0x244bf917c17f21f7 0x8244bf917c17f21f 0x4003f807c07f01f4 0x04003f807c07f01f

def z1155 : W := mkw 0x1efbfff7c1220000 0x11efbfff7c122000 0xffffffffe7f3073f 0xfffffffffe7f3073

def z1156 : W := mkw 0x5dd750003f6f0000 0x05dd750003f6f000 0xdfe398003fff0006 0xfdfe398003fff000

def z1157 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xaf03e787387cf9c9 0x9af03e787387cf9c

def z1158 : W := mkw 0x5ddf78117f6f0000 0x05ddf78117f6f000 0xfffff8ffffff073f 0xffffff8ffffff073

def z1159 : W := mkw 0x5ddb7800336f0000 0x05ddb7800336f000 0xdffff80023ff0007 0xddffff80023ff000

def z1160 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1ffffffbc0000003 0x91ffffffbc000000

def z1161 : W := mkw 0x060aed9740102104 0x0060aed974010210 0xef1fffffe473e73f 0xfef1fffffe473e73

def z1162 : W := mkw 0x210400083c4d9ad2 0x8210400083c4d9ad 0x600000001c0f1ff0 0x2600000001c0f1ff

def z1163 : W := mkw 0x7efbfff7c17f2186 0x17efbfff7c17f218 0x5fffffffc07f01cf 0xd5fffffffc07f01c

def z1164 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x5fffffffc00c01cf 0xd5fffffffc00c01c

def z1165 : W := mkw 0x9efbfff7c2804408 0x19efbfff7c280440 0x1fffffffc380000f 0xd1fffffffc380000

def z1166 : W := mkw 0x5ddf78197f6f0a00 0x05ddf78197f6f0a0 0xfffff8ffffff1e0f 0xffffff8ffffff1e0

def z1167 : W := mkw 0x822087ffc090ff2d 0x1822087ffc090ff2 0x200007ffc000ff38 0x0200007ffc000ff3

def z1168 : W := mkw 0x1efb7ee001a24400 0x01efb7ee001a2440 0xfffffff827f3e60f 0xffffffff827f3e60

def z1169 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c003800000000 0x10f1c00380000000

def z1170 : W := mkw 0x0ab087e480906525 0x00ab087e48090652 0x3ffc07fcc000e73b 0xd3ffc07fcc000e73

def z1171 : W := mkw 0xc10400083fefde58 0x8c10400083fefde5 0xe00000003ffffff0 0x2e00000003ffffff

def z1172 : W := mkw 0x8b9404a83e009a08 0x08b9404a83e009a0 0xbffc07b83f80f80b 0xfbffc07b83f80f80

def z1173 : W := mkw 0x010400083e050a50 0x8010400083e050a5 0xe00000003f8f1ff0 0x2e00000003f8f1ff

def z1174 : W := mkw 0x5ddf78083f6f0a50 0x85ddf78083f6f0a5 0xdffff8003fff18c7 0xfdffff8003fff18c

def z1175 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fff800023f00003 0xd9fff800023f0000

def z1176 : W := mkw 0x5cdf78000f270000 0x05cdf78000f27000 0xdffff80027f30007 0xfdffff80027f3000

def z1177 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x3fffffffc400060f 0xf3fffffffc400060

def z1178 : W := mkw 0x454750003f6f0000 0x0454750003f6f000 0xdfe3f8003fff0007 0xfdfe3f8003fff000

def z1179 : W := mkw 0x1ddf78003e480000 0x01ddf78003e48000 0xdffff8003ffc0007 0xfdffff8003ffc000

def z1180 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8043fff010f 0xffffff8043fff010

def z1181 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff8ffffff063f 0xfdffff8ffffff063

def z1182 : W := mkw 0x022087f7c0906525 0x1022087f7c090652 0x000007ffc000e008 0x0000007ffc000e00

def z1183 : W := mkw 0x5ddb7800336a0000 0x05ddb7800336a000 0x9fffe00023f00001 0x99fffe00023f0000

def z1184 : W := mkw 0x1efbfff7c0906525 0x11efbfff7c090652 0xffffffffe070e73f 0xfffffffffe070e73

def z1185 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xa00000403f80fe0a 0x6a00000403f80fe0

def z1186 : W := mkw 0x0b9404883e009a00 0x00b9404883e009a0 0xbffc07f83f80fe0b 0xfbffc07f83f80fe0

def z1187 : W := mkw 0x0af197f7c1b26525 0x10af197f7c1b2652 0xffff9fffe7f3e73f 0xfffff9fffe7f3e73

def z1188 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef1fe7ff387cf9cf 0xfef1fe7ff387cf9c

def z1189 : W := mkw 0x1edbfdb7c0000000 0x11edbfdb7c000000 0x0f1fe0bb00000001 0x10f1fe0bb0000000

def z1190 : W := mkw 0x1e9a6ca000000000 0x01e9a6ca00000000 0x0f1c60b800000001 0x10f1c60b80000000

def z1191 : W := mkw 0x812402483e85de58 0x8812402483e85de5 0xf0e01f44ff8ffffe 0xef0e01f44ff8ffff

def z1192 : W := mkw 0x1af116e080000000 0x11af116e08000000 0x1ffc07f80000000b 0xd1ffc07f80000000

def z1193 : W := mkw 0x08b0026000804400 0x008b002600080440 0x10fc007807800602 0x010fc00780780060

def z1194 : W := mkw 0x0af116e000000000 0x00af116e00000000 0x1fff9ff80000000f 0xd1fff9ff80000000

def z1195 : W := mkw 0x05435000316a0000 0x005435000316a000 0xdfe3e0003bfc0005 0xfdfe3e0003bfc000

def z1196 : W := mkw 0x0ab82ee000000000 0x00ab82ee00000000 0x1ffc7ff80000000f 0xd1ffc7ff80000000

def z1197 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8003fff0737 0xffffff8003fff073

def z1198 : W := mkw 0x0e9244a200000000 0x00e9244a20000000 0x0f1c60bb00000001 0x10f1c60bb0000000

def z1199 : W := mkw 0x5ddf78083f6f0a50 0x85ddf78083f6f0a5 0xfffff8873fff1fff 0xffffff8873fff1ff

def z1200 : W := mkw 0x1efbfff7c0804400 0x11efbfff7c080440 0x1fffffffc780060f 0xd1fffffffc780060

def z1201 : W := mkw 0x1efbfff7c1b76575 0x91efbfff7c1b7657 0xffffffffe7ffe7ff 0xfffffffffe7ffe7f

def z1202 : W := mkw 0x1efbfff7c1a24421 0x11efbfff7c1a2442 0xbfffffffe783e63f 0xfbfffffffe783e63

def z1203 : W := mkw 0x1efbfff7c0906504 0x11efbfff7c090650 0xffffffffe7f0e70f 0xfffffffffe7f0e70

def z1204 : W := mkw 0xc10400083feade08 0x0c10400083feade0 0xa00000003ff0fe00 0x2a00000003ff0fe0

def z1205 : W := mkw 0x1cdf78194d270a50 0x81cdf78194d270a5 0xfffff8ffffff1fff 0xffffff8ffffff1ff

def z1206 : W := mkw 0x1efbfff7c0102104 0x11efbfff7c010210 0x9fffffffe070e00f 0xd9fffffffe070e00

def z1207 : W := mkw 0x5ddf78117f6f0000 0x05ddf78117f6f000 0xfffff8ffffff19cf 0xffffff8ffffff19c

def z1208 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e3ffc7e7f3e73f 0xef0e3ffc7e7f3e73

def z1209 : W := mkw 0x5cdb7811416f0050 0x85cdb7811416f005 0x5ffff8ffc07f01ff 0xd5ffff8ffc07f01f

def z1210 : W := mkw 0x822087ec0090ff0c 0x0822087ec0090ff0 0x200007fc0000ff08 0x0200007fc0000ff0

def z1211 : W := mkw 0x1ebaeff740000000 0x11ebaeff74000000 0x1fffe7ff0000000f 0xd1fffe7ff0000000

def z1212 : W := mkw 0x810400083e059a58 0x8810400083e059a5 0x600000001c0f1ff0 0x2600000001c0f1ff

def z1213 : W := mkw 0x8bd595acbf32bb2d 0x08bd595acbf32bb2 0x4f1f98bcd8731935 0x14f1f98bcd873193

def z1214 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff8f8ffff1e3f 0xffffff8f8ffff1e3

def z1215 : W := mkw 0x164bfd97c0000000 0x1164bfd97c000000 0x0f1fffffc000000f 0xd0f1fffffc000000

def z1216 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0x200000001800fe00 0x0200000001800fe0

def z1217 : W := mkw 0x0a9004a000000000 0x00a9004a00000000 0x0f1c00f80000000b 0x50f1c00f80000000

def z1218 : W := mkw 0x1edbfdb740000000 0x11edbfdb74000000 0x1fffffbf0000000f 0xd1fffffbf0000000

def z1219 : W := mkw 0x0ab82ef140000000 0x00ab82ef14000000 0x1ffc67fb0000000b 0xd1ffc67fb0000000

def z1220 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3800023f00004 0xfdfe3800023f0000

def z1221 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff8073fff01c7 0xfdffff8073fff01c

def z1222 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e39f04e7f3e734 0xaf0e39f04e7f3e73

def z1223 : W := mkw 0x8bb406e83e85de08 0x08bb406e83e85de0 0xfffc07f83f8ffe0b 0xffffc07f83f8ffe0

def z1224 : W := mkw 0x5ddf78137f6f0000 0x15ddf78137f6f000 0xdffff8033fff0007 0xfdffff8033fff000

def z1225 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1fe0bb00000005 0xd0f1fe0bb0000000

def z1226 : W := mkw 0x5ddf78083f6f0a50 0x85ddf78083f6f0a5 0xdffff8003fff0637 0xfdffff8003fff063

def z1227 : W := mkw 0x544bf915c17f2175 0x8544bf915c17f217 0x4003f807c07f01f4 0x04003f807c07f01f

def z1228 : W := mkw 0x0eb2c7e600906504 0x00eb2c7e60090650 0xffffe7ff27f0e70f 0xfffffe7ff27f0e70

def z1229 : W := mkw 0x58fd3a59cfa74e71 0x858fd3a59cfa74e7 0x10fc1878c7830632 0x010fc1878c783063

def z1230 : W := mkw 0x0ab087e480000000 0x00ab087e48000000 0x1ffc07fcc000000b 0xd1ffc07fcc000000

def z1231 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07ff3f80ffcb 0xfbffc07ff3f80ffc

def z1232 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c60bf0000000d 0x50f1c60bf0000000

def z1233 : W := mkw 0x0602c58600000000 0x00602c5860000000 0x0f1fe7ff0000000f 0xd0f1fe7ff0000000

def z1234 : W := mkw 0x0abc2ef94c854e50 0x80abc2ef94c854e5 0xfffc7fffff8fffff 0xffffc7fffff8ffff

def z1235 : W := mkw 0x3e9a6cb340009082 0x13e9a6cb34000908 0x0f1c60bb000018c1 0x10f1c60bb000018c

def z1236 : W := mkw 0x5ddf78117f6f0000 0x05ddf78117f6f000 0xdffff878ffff0007 0xfdffff878ffff000

def z1237 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff8ffffff18cf 0xfdffff8ffffff18c

def z1238 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07b83f80fe01 0xbbffc07b83f80fe0

def z1239 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0xdfffffffe070000f 0xfdfffffffe070000

def z1240 : W := mkw 0x1eb246e200000000 0x11eb246e20000000 0x1ffc07f80000000b 0xd1ffc07f80000000

def z1241 : W := mkw 0x09d510003f220000 0x009d510003f22000 0x9fff80003ff00003 0xf9fff80003ff0000

def z1242 : W := mkw 0x5dd35000336f0000 0x05dd35000336f000 0xdfe3800023ff0000 0x9dfe3800023ff000

def z1243 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9fff800023f00000 0x99fff800023f0000

def z1244 : W := mkw 0x3ff3d7e6b1faf5a7 0x13ff3d7e6b1faf5a 0x9fe3870023f0e000 0x99fe3870023f0e00

def z1245 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8003fff19c7 0xffffff8003fff19c

def z1246 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff8fbffff1ef7 0xfdffff8fbffff1ef

def z1247 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03ffc7f87cf9cf 0xfef03ffc7f87cf9c

def z1248 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9ffff8003bfc0007 0xd9ffff8003bfc000

def z1249 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x3fffffffc00019cf 0xd3fffffffc00019c

def z1250 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3800027f30000 0xbdfe3800027f3000

def z1251 : W := mkw 0x5ddb7800336a0000 0x05ddb7800336a000 0xdffff8003bfc0007 0xfdffff8003bfc000

def z1252 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c60ffc0000009 0x10f1c60ffc000000

def z1253 : W := mkw 0x1af93ef1c0000000 0x11af93ef1c000000 0x1ffc7fffc000000f 0xd1ffc7fffc000000

def z1254 : W := mkw 0x1cfbfb55c1b26525 0x01cfbfb55c1b2652 0xffffffffe7f3e73f 0xfffffffffe7f3e73

def z1255 : W := mkw 0x1eba6ef340000000 0x11eba6ef34000000 0x0f1c67fb00000009 0x10f1c67fb0000000

def z1256 : W := mkw 0xcbb406e83ecdde08 0x0cbb406e83ecdde0 0xbffc07f83f8cfe0b 0xfbffc07f83f8cfe0

def z1257 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc07fc3f80ff0f 0xffffc07fc3f80ff0

def z1258 : W := mkw 0x1cd3500001220000 0x01cd350000122000 0xdfe3980027f30006 0xfdfe3980027f3000

def z1259 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x9fff9f78e7f3e632 0x99fff9f78e7f3e63

def z1260 : W := mkw 0x810400083e059a58 0x8810400083e059a5 0x00000000180c18c0 0x000000000180c18c

def z1261 : W := mkw 0x5ddf78003f6f0050 0x85ddf78003f6f005 0xdffff8003fff01f7 0xfdffff8003fff01f

def z1262 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x3ffc07f81800180b 0xf3ffc07f81800180

def z1263 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1ffc7fffc000000b 0x11ffc7fffc000000

def z1264 : W := mkw 0x8bb406e83e80de58 0x88bb406e83e80de5 0xbffc07f83f80fffb 0xfbffc07f83f80fff

def z1265 : W := mkw 0x1efbfff7c1322125 0x11efbfff7c132212 0x1fffffffc070000f 0xd1fffffffc070000

def z1266 : W := mkw 0x5ddb7800336f0000 0x05ddb7800336f000 0x9fe3980023f30000 0x99fe3980023f3000

def z1267 : W := mkw 0x1eba6ef3c0000000 0x11eba6ef3c000000 0x0f1c60fbc0000001 0x10f1c60fbc000000

def z1268 : W := mkw 0x8bb406e83e85de58 0x88bb406e83e85de5 0xfffc67ff3f8fffff 0xffffc67ff3f8ffff

def z1269 : W := mkw 0x066bffd7c0000000 0x0066bffd7c000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1270 : W := mkw 0x0ab006e000009000 0x00ab006e00000900 0x3ffc07f80000f80b 0xd3ffc07f80000f80

def z1271 : W := mkw 0xabb406ea3e80de8a 0x0abb406ea3e80de8 0xbffc07fb3f80fecb 0xfbffc07fb3f80fec

def z1272 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e39f40e7f3e732 0xaf0e39f40e7f3e73

def z1273 : W := mkw 0x1efbfff7c0906525 0x11efbfff7c090652 0x7fffffffc403e73f 0xf7fffffffc403e73

def z1274 : W := mkw 0x810400083e90ff0c 0x0810400083e90ff0 0xe00000003ff0ff00 0x2e00000003ff0ff0

def z1275 : W := mkw 0x0a982cb140000000 0x00a982cb14000000 0x0f1c78ffc000000f 0x50f1c78ffc000000

def z1276 : W := mkw 0x1edb7cb3c0000000 0x11edb7cb3c000000 0x0f1c78bbc0000001 0x10f1c78bbc000000

def z1277 : W := mkw 0x0d92400032480000 0x00d9240003248000 0x9fe3800023f00000 0x99fe3800023f0000

def z1278 : W := mkw 0x022006e000804400 0x0022006e00080440 0x200007f80000e608 0x0200007f80000e60

def z1279 : W := mkw 0xa22087ffc090ff8e 0x1a22087ffc090ff8 0x200007ffc000ffc8 0x0200007ffc000ffc

def z1280 : W := mkw 0x810400083e009a08 0x0810400083e009a0 0x800000003f801800 0x2800000003f80180

def z1281 : W := mkw 0x09b402483e804e00 0x009b402483e804e0 0xbffc07f83f80fe0b 0xfbffc07f83f80fe0

def z1282 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc1ffcff80fe0f 0xfbffc1ffcff80fe0

def z1283 : W := mkw 0x810400083e85de58 0x8810400083e85de5 0xa00000003f83fe30 0x2a00000003f83fe3

def z1284 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe3e00023f00005 0xd9fe3e00023f0000

def z1285 : W := mkw 0x0bb406e03e009000 0x00bb406e03e00900 0xbffc07f83f80f80b 0xfbffc07f83f80f80

def z1286 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x3ffc07f81f80fe0b 0x13ffc07f81f80fe0

def z1287 : W := mkw 0xa10400083e58bb8e 0x0a10400083e58bb8 0xe0000000387cf9c0 0x2e0000000387cf9c

def z1288 : W := mkw 0x1eba6ef340000000 0x11eba6ef34000000 0x1ffc60fb00000003 0x11ffc60fb0000000

def z1289 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9fffe0003ffc0003 0xf9fffe0003ffc000

def z1290 : W := mkw 0x5ddf78083f6f0a50 0x85ddf78083f6f0a5 0xfffff844ffff1fff 0xffffff844ffff1ff

def z1291 : W := mkw 0x1eba6ef340000000 0x11eba6ef34000000 0x1ffc7fffc000000f 0xd1ffc7fffc000000

def z1292 : W := mkw 0x210400083c58bb86 0x0210400083c58bb8 0xe00000003c7cffc0 0x2e00000003c7cffc

def z1293 : W := mkw 0x5ddf78117f6f0050 0x85ddf78117f6f005 0xdffff8033fff00c7 0xfdffff8033fff00c

def z1294 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07782780e60a 0xfbffc07782780e60

def z1295 : W := mkw 0x1cfb7a71c0000000 0x11cfb7a71c000000 0x1ffc7878c0000003 0x11ffc7878c000000

def z1296 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fff9f7cc000000e 0xd1fff9f7cc000000

def z1297 : W := mkw 0x810400083e009a08 0x0810400083e009a0 0x200000001c001e00 0x2200000001c001e0

def z1298 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3980023f30004 0x9dfe3980023f3000

def z1299 : W := mkw 0x1efbfff7c1322125 0x11efbfff7c132212 0xdfffffffe7f3013f 0xfdfffffffe7f3013

def z1300 : W := mkw 0x822087e48090f52d 0x0822087e48090f52 0x000007000000e000 0x0000007000000e00

def z1301 : W := mkw 0x5ddf78317f6f0000 0x15ddf78317f6f000 0xdffff8383fff0007 0xfdffff8383fff000

def z1302 : W := mkw 0x3efbfff7c010b186 0x13efbfff7c010b18 0x1fffffffc000e00f 0xd1fffffffc000e00

def z1303 : W := mkw 0x1af93ee000000000 0x01af93ee00000000 0x1ffc1ff80000000b 0xd1ffc1ff80000000

def z1304 : W := mkw 0x810400083e80de08 0x0810400083e80de0 0xe00060873f8cffcd 0x6e00060873f8cffc

def z1305 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdfff98003fff0002 0xbdfff98003fff000

def z1306 : W := mkw 0x5ddf78083f6f0a00 0x05ddf78083f6f0a0 0xfffff8ff3fff1fcf 0xffffff8ff3fff1fc

def z1307 : W := mkw 0x1edbfdb7c1322125 0x11edbfdb7c132212 0x4f1ff8bfc0730135 0x14f1ff8bfc073013

def z1308 : W := mkw 0x1af93ef1c1a24421 0x11af93ef1c1a2442 0xbffc1ff8e783e63b 0xfbffc1ff8e783e63

def z1309 : W := mkw 0x89b402683e804e08 0x089b402683e804e0 0xbffc07783f80e60b 0xfbffc07783f80e60

def z1310 : W := mkw 0x5ddb7811736f0050 0x85ddb7811736f005 0xdfe3f807e3ff01f4 0x9dfe3f807e3ff01f

def z1311 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03e7873c7ffffd 0xfef03e7873c7ffff

def z1312 : W := mkw 0x0bb006e03080d400 0x00bb006e03080d40 0xbffc07f83f80fe0b 0xfbffc07f83f80fe0

def z1313 : W := mkw 0x1efbffe480000000 0x01efbffe48000000 0x1ffffffcc000000f 0xd1ffffffcc000000

def z1314 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xcf03e787387cf9c5 0x9cf03e787387cf9c

def z1315 : W := mkw 0x0a9004a000000000 0x00a9004a00000000 0x0f1c07b800000009 0xd0f1c07b80000000

def z1316 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x9fffffffe7f3e63f 0xd9fffffffe7f3e63

def z1317 : W := mkw 0x1efbfff7c1b26525 0x11efbfff7c1b2652 0x7fffffffc073e73f 0xd7fffffffc073e73

def z1318 : W := mkw 0x144bf917c1372175 0x9144bf917c137217 0x4003f807c07f01f4 0x04003f807c07f01f

def z1319 : W := mkw 0xaf9e6cbb7e4d9ada 0x8af9e6cbb7e4d9ad 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z1320 : W := mkw 0x2702448230489082 0x0270244823048908 0xef03e783387cf8cd 0xfef03e783387cf8c

def z1321 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc1ff83f83fe0f 0xffffc1ff83f83fe0

def z1322 : W := mkw 0x5dd750003f6a0000 0x05dd750003f6a000 0xdfffe0003ffc0007 0xfdfffe0003ffc000

def z1323 : W := mkw 0x0ef3d7e680000000 0x00ef3d7e68000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1324 : W := mkw 0x0ab006e000804400 0x00ab006e00080440 0x1ffc07f80780060b 0xd1ffc07f80780060

def z1325 : W := mkw 0x3efbfff7c010b186 0x13efbfff7c010b18 0x7fffffffd80cf9cf 0xf7fffffffd80cf9c

def z1326 : W := mkw 0x1cfbfb75c1b26525 0x11cfbfb75c1b2652 0xffffff7ce7f3e73f 0xfffffff7ce7f3e73

def z1327 : W := mkw 0x5ddf78083f6f0a00 0x05ddf78083f6f0a0 0xdffff8783fff0607 0xfdffff8783fff060

def z1328 : W := mkw 0x81651248bfa2de29 0x081651248bfa2de2 0xb0e01840ff83fe32 0x2b0e01840ff83fe3

def z1329 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x7fffffffdc0f1fff 0xf7fffffffdc0f1ff

def z1330 : W := mkw 0x0200048000000000 0x0020004800000000 0x0f1c07f80000000b 0xd0f1c07f80000000

def z1331 : W := mkw 0xc165934cbfffff2d 0x0c165934cbfffff2 0xf0e39f44ffffff3e 0xef0e39f44ffffff3

def z1332 : W := mkw 0x3efbfff7c0480082 0x13efbfff7c048008 0x1fffffffc00c00cf 0xd1fffffffc00c00c

def z1333 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff8873fff000f 0xfdffff8873fff000

def z1334 : W := mkw 0x5dd750003f6f0000 0x05dd750003f6f000 0x9fe3800027f30000 0x99fe3800027f3000

def z1335 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x5fffffffc403000f 0xf5fffffffc403000

def z1336 : W := mkw 0x8165934cbfb7ff7d 0x88165934cbfb7ff7 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z1337 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07f83b80fe09 0x9bffc07f83b80fe0

def z1338 : W := mkw 0x1efbfff7c1a24421 0x11efbfff7c1a2442 0xdfffffffe7f3063f 0xfdfffffffe7f3063

def z1339 : W := mkw 0x1edb7ca000000000 0x01edb7ca00000000 0x1ffff8b800000007 0xd1ffff8b80000000

def z1340 : W := mkw 0x222087c68090f5a7 0x0222087c68090f5a 0x000007000000e000 0x0000007000000e00

def z1341 : W := mkw 0x0a9004a000000000 0x00a9004a00000000 0x1ffc00b800000003 0xd1ffc00b80000000

def z1342 : W := mkw 0x210400083c4d9ad2 0x8210400083c4d9ad 0x00000000180c18c0 0x000000000180c18c

def z1343 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0xdfe3f8003fff0007 0xfdfe3f8003fff000

def z1344 : W := mkw 0x210400083c5dbbd6 0x8210400083c5dbbd 0xe0000000387cf9c0 0x2e0000000387cf9c

def z1345 : W := mkw 0xaff3d7e6b3faf5af 0x0aff3d7e6b3faf5a 0x9fe3870023f0e000 0x99fe3870023f0e00

def z1346 : W := mkw 0x5ddf78083f6f0a50 0x85ddf78083f6f0a5 0xfffff8f83fff1fff 0xffffff8f83fff1ff

def z1347 : W := mkw 0x5ddf78003f6a0000 0x05ddf78003f6a000 0x9ffff8003ff00007 0xf9ffff8003ff0000

def z1348 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07783f80e603 0xf9ffc07783f80e60

def z1349 : W := mkw 0x0ab087f7c0906525 0x10ab087f7c090652 0xbffc07ffe780e73b 0xfbffc07ffe780e73

def z1350 : W := mkw 0x5cdf78000f6f0000 0x05cdf78000f6f000 0x5ffff80007ff0007 0xd5ffff80007ff000

def z1351 : W := mkw 0x8bb006e03280d408 0x08bb006e03280d40 0xbffc07f83b80f80b 0xfbffc07f83b80f80

def z1352 : W := mkw 0x09d510083f220a00 0x009d510083f220a0 0xffff98fcfff31f3f 0xfffff98fcfff31f3

def z1353 : W := mkw 0x054f78003d6f0000 0x0054f78003d6f000 0xdffff8003fff0007 0xfdffff8003fff000

def z1354 : W := mkw 0x2702c586b058b1a7 0x02702c586b058b1a 0xef03e787f87cf9fd 0xfef03e787f87cf9f

def z1355 : W := mkw 0x810400083fb7ff7d 0x8810400083fb7ff7 0xe00000003ffffff0 0x2e00000003ffffff

def z1356 : W := mkw 0x1e9aedb740000000 0x11e9aedb74000000 0x0f1fe0bf00000005 0x10f1fe0bf0000000

def z1357 : W := mkw 0x2104810c3c5dbbd6 0x82104810c3c5dbbd 0xe0039f44fc7ffffe 0xee0039f44fc7ffff

def z1358 : W := mkw 0x1efbfff7c1220000 0x11efbfff7c122000 0x5fffffffc073000f 0xd5fffffffc073000

def z1359 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xfffff8803fff180f 0xffffff8803fff180

def z1360 : W := mkw 0x0a982cb140000000 0x00a982cb14000000 0x0f1c60bb00000001 0x10f1c60bb0000000

def z1361 : W := mkw 0x000c28194c050a50 0x8000c28194c050a5 0x401c78ffdc0f1ff7 0x0401c78ffdc0f1ff

def z1362 : W := mkw 0x8bb406e83ec8de08 0x08bb406e83ec8de0 0xfffc07f83ffcfe0b 0xffffc07f83ffcfe0

def z1363 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0x9ffff8003fff0003 0x99ffff8003fff000

def z1364 : W := mkw 0x3efbfff7c0582186 0x13efbfff7c058218 0xffffffffe07ce1cf 0xfffffffffe07ce1c

def z1365 : W := mkw 0x1cfb7a71c1a24421 0x11cfb7a71c1a2442 0xdffff878e7f30637 0xfdffff878e7f3063

def z1366 : W := mkw 0x1efbfff7c0102104 0x11efbfff7c010210 0x3fffffffc000e10f 0xd3fffffffc000e10

def z1367 : W := mkw 0x1efb7ef3c0000000 0x11efb7ef3c000000 0x1ffc1878c0000002 0x11ffc1878c000000

def z1368 : W := mkw 0x1eba6ef340804400 0x11eba6ef34080440 0xbffc67fb2780e60b 0xfbffc67fb2780e60

def z1369 : W := mkw 0x2eb2c7e600582186 0x02eb2c7e60058218 0x5fffe7ff007c01cf 0xd5fffe7ff007c01c

def z1370 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xfffff8fb3fff1ecf 0xffffff8fb3fff1ec

def z1371 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07f82780fe0a 0x9bffc07f82780fe0

def z1372 : W := mkw 0x810400083ec8de08 0x0810400083ec8de0 0xe00000003ffcfe00 0x2e00000003ffcfe0

def z1373 : W := mkw 0x812402483e80de08 0x0812402483e80de0 0xb0e007003f80fe00 0xab0e007003f80fe0

def z1374 : W := mkw 0x1e9244a200000000 0x11e9244a20000000 0x0f1c00b800000001 0x10f1c00b80000000

def z1375 : W := mkw 0x1edb7cb340000000 0x11edb7cb34000000 0x1ffc78bb00000003 0x11ffc78bb0000000

def z1376 : W := mkw 0x822087ec8090ff2d 0x0822087ec8090ff2 0x200007f80000fe08 0x0200007f80000fe0

def z1377 : W := mkw 0x1eba6ef340000000 0x11eba6ef34000000 0x1ffc67bb00000001 0x91ffc67bb0000000

def z1378 : W := mkw 0x1efbfff7c0050050 0x91efbfff7c005005 0x7fffffffd80f19ff 0xf7fffffffd80f19f

def z1379 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc67ff3f80fe0f 0xfbffc67ff3f80fe0

def z1380 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fff873800000000 0x91fff87380000000

def z1381 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03e783387cf9c1 0xbef03e783387cf9c

def z1382 : W := mkw 0x0ab006e000000000 0x00ab006e00000000 0x3ffc07f80400060b 0xf3ffc07f80400060

def z1383 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c60bb180c18c1 0x10f1c60bb180c18c

def z1384 : W := mkw 0x0606c58e0c050a50 0x80606c58e0c050a5 0x6f03e7871c0f1ffd 0xf6f03e7871c0f1ff

def z1385 : W := mkw 0xc10400083f6f9a08 0x0c10400083f6f9a0 0xc00000003fff1800 0x2c00000003fff180

def z1386 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdffff8833fff18c7 0xfdffff8833fff18c

def z1387 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x7fffffffc000010f 0xf7fffffffc000010

def z1388 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xbffc07b83b80f809 0xfbffc07b83b80f80

def z1389 : W := mkw 0x410400083e4d0a50 0x8410400083e4d0a5 0x600000001c0f1ff0 0x2600000001c0f1ff

def z1390 : W := mkw 0x1ab82ef140000000 0x11ab82ef14000000 0x1ffc07f80000000b 0xd1ffc07f80000000

def z1391 : W := mkw 0x5efbfff7c17f2125 0x15efbfff7c17f212 0x5fffffffc07f013f 0xd5fffffffc07f013

def z1392 : W := mkw 0x810400083fa2de29 0x0810400083fa2de2 0xa00000003f83fe30 0x2a00000003f83fe3

def z1393 : W := mkw 0x810400083e85de58 0x8810400083e85de5 0xa00000003f8cfec0 0x2a00000003f8cfec

def z1394 : W := mkw 0x010400083c059a50 0x8010400083c059a5 0xe00000003c0ffff0 0x2e00000003c0ffff

def z1395 : W := mkw 0x0ab006f340000000 0x10ab006f34000000 0x1ffc07fb0000000b 0xd1ffc07fb0000000

def z1396 : W := mkw 0x5dd35000336a0000 0x05dd35000336a000 0x9fe380003bf00001 0xf9fe380003bf0000

def z1397 : W := mkw 0xa22087ee0090ff8e 0x0a22087ee0090ff8 0x200007f80000fe08 0x0200007f80000fe0

def z1398 : W := mkw 0x8bb406e8be80de29 0x08bb406e8be80de2 0xbffc07f8ff80fe3b 0xfbffc07f8ff80fe3

def z1399 : W := mkw 0xa506c10e3ed8ff8e 0x0a506c10e3ed8ff8 0xe003e0073ffcffc4 0x2e003e0073ffcffc

def z1400 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0x9fff9878e7f30632 0x99fff9878e7f3063

def z1401 : W := mkw 0x3efbfff7c058b186 0x13efbfff7c058b18 0x7fffffffc07cf9cf 0xd7fffffffc07cf9c

def z1402 : W := mkw 0x1efbfff7c0804400 0x11efbfff7c080440 0x3fffffffc000e60f 0xd3fffffffc000e60

def z1403 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03e7c73c7cffcf 0xfef03e7c73c7cffc

def z1404 : W := mkw 0x222087c68090f5a7 0x0222087c68090f5a 0x60007fc7dc0fffff 0x660007fc7dc0ffff

def z1405 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0x9fffe0bb3bfc18c1 0x99fffe0bb3bfc18c

def z1406 : W := mkw 0x1efbffe481b26525 0x01efbffe481b2652 0xfffffffce7f3e73f 0xffffffffce7f3e73

def z1407 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0xfffc07f83f8cffcb 0xffffc07f83f8cffc

def z1408 : W := mkw 0x1efb7ef3c0000000 0x11efb7ef3c000000 0x1ffff8fbc0000007 0xd1ffff8fbc000000

def z1409 : W := mkw 0x0eb2c7f7c0000000 0x10eb2c7f7c000000 0x1fffe7ffc000000f 0xd1fffe7ffc000000

def z1410 : W := mkw 0x2fb2c7e630d8f586 0x02fb2c7e630d8f58 0xffffe7ff3ffcffcf 0xfffffe7ff3ffcffc

def z1411 : W := mkw 0x5ddf78197f6f0a50 0x85ddf78197f6f0a5 0xdffff8bfffff19f7 0xfdffff8bfffff19f

def z1412 : W := mkw 0x2ab087e60010b186 0x02ab087e60010b18 0x3ffc07ff0000f9cb 0xd3ffc07ff0000f9c

def z1413 : W := mkw 0x09dd38003f270000 0x009dd38003f27000 0xdffff8003fff0007 0xfdffff8003fff000

def z1414 : W := mkw 0x0061934481b26525 0x00061934481b2652 0xf0e39f44fffffffe 0xef0e39f44fffffff

def z1415 : W := mkw 0x2502c1063058b186 0x02502c1063058b18 0x4003e007187c19c4 0x04003e007187c19c

def z1416 : W := mkw 0x030085843010b104 0x0030085843010b10 0xef03e787387cf9cd 0xfef03e787387cf9c

def z1417 : W := mkw 0x0af197e480000000 0x00af197e48000000 0x1fff87f80000000b 0xd1fff87f80000000

def z1418 : W := mkw 0x0061934481b26525 0x00061934481b2652 0x90e39f44e7f3e63e 0xc90e39f44e7f3e63

def z1419 : W := mkw 0x260aed97405d21d6 0x8260aed97405d21d 0x4f1fffffc07f01ff 0xd4f1fffffc07f01f

def z1420 : W := mkw 0x2702c5863058b186 0x02702c5863058b18 0xef03e7c7f87cfffd 0xfef03e7c7f87cfff

def z1421 : W := mkw 0x59dd38003f270000 0x059dd38003f27000 0xdfff98003ff30007 0xfdfff98003ff3000

def z1422 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fff9fffc000000a 0x91fff9fffc000000

def z1423 : W := mkw 0x022087c48090f525 0x0022087c48090f52 0x200007c4c000ff38 0x0200007c4c000ff3

def z1424 : W := mkw 0x8bb406e83e80de08 0x08bb406e83e80de0 0x9ffc07f83f80fe03 0x99ffc07f83f80fe0

def z1425 : W := mkw 0x3e9aedb74010b186 0x13e9aedb74010b18 0x2f1c67bf0000f9c9 0x12f1c67bf0000f9c

def z1426 : W := mkw 0x812402483e80de08 0x0812402483e80de0 0xa00007403f80fe08 0x2a00007403f80fe0

def z1427 : W := mkw 0x0af116e001220000 0x00af116e00122000 0xdfff9ff827f3000f 0xfdfff9ff827f3000

def z1428 : W := mkw 0x744bf917c17f2186 0x1744bf917c17f218 0x4003f807c07f01c4 0x04003f807c07f01c

def z1429 : W := mkw 0x1efbfff7c0906525 0x11efbfff7c090652 0xbfffffffe780e73f 0xfbfffffffe780e73

def z1430 : W := mkw 0x05435000316a0000 0x005435000316a000 0xdfe3980027f30006 0xfdfe3980027f3000

def z1431 : W := mkw 0x1e9a6cb340000000 0x11e9a6cb34000000 0x0f1c78bfc0000005 0x10f1c78bfc000000

def z1432 : W := mkw 0x1efbfff7c0804400 0x11efbfff7c080440 0xffffffffe783e73f 0xfffffffffe783e73

def z1433 : W := mkw 0xa22087ee8090ffaf 0x0a22087ee8090ffa 0x200007ffc000fff8 0x0200007ffc000fff

def z1434 : W := mkw 0x5ddf78003f6f0000 0x05ddf78003f6f000 0xdfff980027f30006 0xfdfff980027f3000

def z1435 : W := mkw 0x5efbfff7c04d0000 0x15efbfff7c04d000 0x1fffffffc00c000f 0xd1fffffffc00c000

def z1436 : W := mkw 0xc10400083fef4e08 0x0c10400083fef4e0 0xc00000003fff0600 0x2c00000003fff060

def z1437 : W := mkw 0x1efbfff7c0000000 0x11efbfff7c000000 0x1fff9ff8c000000b 0xd1fff9ff8c000000

def z1438 : W := mkw 0x099400003e000000 0x0099400003e00000 0xdfff80003ff00007 0xfdfff80003ff0000

def z1439 : W := mkw 0x0ab006e000804400 0x00ab006e00080440 0x9fe007002380e000 0x99fe007002380e00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z7,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z10,z11,z3,z4,z6])],[(0,[z12,z1,z2,z8,z3,z4,z6]),(0,[z13,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z15,z8,z3,z4,z6]),(0,[z1,z2,z16,z8,z3,z4,z6])],[(0,[z1,z2,z17,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z18,z6])],[(0,[z19,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z20,z8,z3,z4,z6]),(0,[z1,z2,z8,z21,z3,z4,z6]),(0,[z1,z22,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z23]),(0,[z24,z1,z2,z10,z3,z4,z6])],[(0,[z1,z2,z8,z3,z25,z4,z6]),(1,[z1,z2,z8,z3,z9,z6]),(0,[z1,z26,z8,z27,z3,z4,z6])],[(0,[z28,z1,z29,z8,z3,z4,z6]),(0,[z1,z29,z2,z30,z3,z4,z6]),(0,[z1,z31,z2,z8,z3,z4,z6])],[(1,[z32,z1,z30,z3,z4,z6]),(0,[z1,z2,z8,z33,z3,z4,z6])],[(1,[z1,z2,z8,z3,z34,z6])],[(0,[z35,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z36,z6])],[(0,[z1,z2,z8,z3,z4,z37,z6]),(0,[z1,z2,z38,z8,z27,z3,z4]),(0,[z1,z2,z8,z3,z39,z4,z6]),(0,[z1,z2,z8,z3,z40,z4,z6])],[(0,[z1,z2,z8,z3,z4,z41,z6]),(0,[z42,z1,z2,z3,z43,z4,z6]),(0,[z1,z44,z2,z27,z3,z4,z6]),(0,[z1,z45,z2,z8,z39,z4,z6]),(0,[z1,z2,z10,z3,z4,z6,z46]),(0,[z1,z2,z8,z3,z4,z47,z6])],[(0,[z48,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z6,z49,z50])],[(0,[z32,z1,z26,z8,z3,z4,z6])],[(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z51,z14,z6]),(0,[z52,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z53,z4,z6]),(0,[z1,z2,z8,z3,z4,z54,z6])],[(0,[z1,z2,z55,z8,z3,z4,z6]),(0,[z13,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z36,z6])]],
   [[(0,[z1,z2,z10,z3,z56,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z57])],[(0,[z1,z2,z3,z58,z4,z5,z6]),(0,[z19,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z59,z6])],[(0,[z1,z60,z2,z8,z3,z4,z6]),(0,[z7,z1,z2,z8,z3,z61,z6]),(0,[z1,z2,z8,z3,z62,z9,z6]),(0,[z1,z2,z8,z3,z63,z4,z6]),(0,[z64,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z65,z8,z3,z4,z6])],[(0,[z1,z66,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z67,z3,z4,z6])],[(0,[z1,z2,z8,z68,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z5,z6,z46])],[(0,[z1,z2,z8,z3,z70,z4,z6]),(1,[z1,z2,z8,z3,z61,z6]),(0,[z1,z2,z71,z8,z3,z4,z6]),(0,[z72,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z73,z8,z3,z14,z6]),(0,[z1,z2,z8,z3,z4,z74,z6])],[(0,[z1,z2,z8,z3,z4,z6,z75]),(0,[z1,z2,z27,z3,z4,z76,z6]),(0,[z1,z2,z8,z3,z77,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z78]),(0,[z1,z2,z79,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z80,z6]),(0,[z1,z2,z8,z3,z4,z6,z81])],[(0,[z1,z2,z8,z3,z82,z4,z6]),(1,[z1,z2,z3,z14,z5,z6]),(0,[z1,z2,z8,z3,z14,z83,z6]),(0,[z1,z2,z8,z3,z4,z84,z36]),(0,[z1,z85,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z86,z4,z6])],[(0,[z1,z2,z8,z3,z4,z87,z50]),(0,[z1,z2,z10,z3,z4,z6,z50]),(1,[z1,z2,z73,z8,z4,z50])],[(0,[z1,z26,z2,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z88,z4,z6]),(0,[z89,z1,z2,z8,z3,z4,z6])],[(1,[z1,z2,z90,z3,z4,z6]),(0,[z1,z2,z91,z8,z3,z4,z6]),(0,[z1,z92,z2,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z93]),(0,[z1,z2,z8,z3,z94,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z46])],[(0,[z1,z2,z8,z3,z4,z6,z95]),(0,[z1,z2,z96,z8,z3,z4,z6])],[(0,[z1,z2,z27,z3,z62,z4,z6]),(0,[z1,z2,z8,z3,z97,z4,z6]),(0,[z1,z2,z98,z3,z99,z4,z6])],[(0,[z1,z2,z100,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z101])],[(1,[z1,z2,z30,z3,z14,z6]),(0,[z1,z2,z102,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z103,z6]),(0,[z1,z104,z2,z8,z3,z4,z6])]],
   [[(1,[z1,z2,z8,z3,z105,z6]),(0,[z1,z2,z8,z3,z56,z4,z6])],[(0,[z106,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z107,z8,z3,z9,z6]),(0,[z1,z108,z2,z8,z3,z4,z6]),(0,[z1,z2,z3,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z6])],[(0,[z1,z2,z10,z3,z58,z4,z6]),(0,[z1,z2,z110,z8,z27,z3,z4]),(0,[z1,z2,z111,z8,z3,z6,z50])],[(0,[z1,z2,z8,z3,z4,z112,z6]),(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z1,z2,z73,z8,z3,z4,z6])],[],[(0,[z1,z2,z113,z8,z3,z4,z6]),(0,[z1,z2,z3,z114,z43,z4,z6]),(0,[z1,z115,z2,z8,z3,z4,z6])],[],[(0,[z1,z2,z116,z8,z3,z4,z6]),(0,[z42,z2,z117,z8,z3,z4,z6]),(0,[z118,z1,z2,z8,z33,z4,z6]),(0,[z1,z45,z2,z10,z3,z4,z6]),(0,[z1,z2,z8,z3,z119,z4,z6]),(0,[z1,z2,z8,z3,z4,z80,z6])],[(0,[z7,z1,z2,z30,z3,z4,z6]),(0,[z13,z2,z8,z3,z4,z36,z6]),(0,[z1,z2,z120,z30,z3,z4,z6]),(0,[z118,z1,z45,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z121])],[(0,[z1,z2,z122,z8,z3,z9,z6]),(0,[z1,z2,z123,z27,z3,z4,z6]),(1,[z1,z44,z2,z10,z3,z4]),(0,[z1,z2,z8,z3,z4,z6,z50])],[(0,[z1,z2,z124,z10,z3,z4,z6]),(0,[z1,z2,z125,z8,z3,z4,z6])],[(0,[z1,z2,z8,z126,z3,z4,z6]),(0,[z1,z2,z8,z3,z9,z84,z6]),(0,[z1,z2,z8,z3,z4,z6,z127])],[(0,[z1,z2,z128,z8,z3,z4,z6]),(0,[z1,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z3,z14,z4,z5,z6]),(1,[z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z129,z4,z6]),(0,[z1,z130,z2,z10,z3,z4,z6])],[(0,[z131,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z132,z8,z3,z4,z6]),(1,[z1,z2,z8,z3,z4,z133]),(0,[z1,z2,z10,z134,z3,z4,z6]),(0,[z1,z2,z8,z135,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z76,z6])],[(0,[z1,z136,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z137,z4,z6]),(0,[z138,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z3,z4,z139,z6]),(0,[z42,z1,z2,z117,z3,z4,z6]),(0,[z42,z1,z2,z140,z3,z4,z6]),(1,[z141,z2,z8,z3,z9,z6])]],
   [[(0,[z1,z2,z142,z8,z3,z4,z36]),(0,[z143,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z144,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z58,z4,z6]),(0,[z1,z2,z8,z145,z3,z4,z6]),(0,[z1,z2,z146,z8,z3,z6,z23])],[(0,[z1,z147,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z148,z4,z6]),(0,[z1,z2,z8,z3,z4,z149,z6])],[(0,[z141,z2,z8,z3,z4,z9,z6]),(0,[z1,z2,z8,z3,z4,z150,z87]),(0,[z151,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z152,z27,z3,z4,z6]),(0,[z1,z2,z153,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z154,z6])],[(0,[z1,z26,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z155,z9,z6]),(0,[z1,z156,z2,z8,z3,z4,z6]),(0,[z157,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z158,z4,z6]),(0,[z1,z159,z2,z8,z3,z4,z6]),(0,[z160,z1,z2,z8,z3,z4,z6]),(0,[z161,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z14,z150,z6]),(1,[z1,z2,z162,z8,z3,z6]),(0,[z1,z2,z163,z10,z3,z4,z6])],[(0,[z164,z1,z2,z8,z3,z4,z6]),(1,[z1,z2,z11,z3,z4,z6])],[(0,[z1,z2,z30,z3,z4,z9,z6]),(1,[z165,z2,z8,z3,z4,z87])],[(0,[z1,z2,z8,z3,z9,z6,z166]),(1,[z1,z2,z140,z3,z167,z6]),(0,[z1,z2,z8,z3,z4,z6,z168])],[(0,[z19,z141,z2,z8,z3,z4,z6]),(0,[z1,z2,z169,z30,z3,z4,z6]),(0,[z1,z170,z2,z8,z3,z4,z6]),(0,[z1,z171,z2,z8,z3,z4,z6])],[(0,[z172,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z173,z3,z4,z6]),(1,[z1,z2,z68,z3,z4,z6])],[(0,[z1,z2,z8,z134,z3,z4,z6]),(0,[z165,z1,z2,z8,z3,z4,z36])],[],[(0,[z1,z2,z3,z4,z174,z5,z6])]],
   [[(0,[z1,z2,z123,z175,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z176])],[(0,[z1,z2,z8,z3,z4,z6,z177]),(0,[z1,z2,z140,z3,z4,z5,z6]),(0,[z1,z2,z10,z3,z178,z4,z6]),(0,[z1,z179,z2,z8,z3,z4,z6]),(0,[z180,z1,z2,z8,z3,z4,z6])],[(0,[z1,z181,z2,z8,z3,z4,z6]),(0,[z1,z2,z182,z8,z3,z9,z6]),(0,[z1,z2,z10,z8,z3,z14,z6]),(0,[z1,z183,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z184,z6])],[(0,[z1,z2,z8,z3,z4,z6,z185])],[(0,[z28,z1,z2,z186,z3,z4,z6]),(0,[z1,z187,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z188]),(0,[z1,z2,z8,z3,z178,z14,z6]),(0,[z1,z2,z189,z30,z3,z4,z6]),(1,[z1,z2,z190,z8,z3,z166])],[(0,[z191,z1,z2,z30,z3,z4,z6]),(1,[z1,z45,z8,z33,z4,z6]),(1,[z1,z2,z3,z4,z6,z101]),(1,[z1,z2,z125,z3,z4,z6])],[(0,[z192,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z14,z6,z23]),(0,[z1,z85,z2,z190,z8,z3,z6]),(0,[z1,z2,z8,z3,z4,z193,z6])],[],[(0,[z106,z1,z2,z30,z3,z4,z6]),(0,[z138,z1,z2,z194,z3,z4,z6]),(0,[z1,z2,z195,z8,z3,z14,z6]),(0,[z1,z2,z107,z30,z3,z4,z6]),(0,[z1,z92,z2,z8,z3,z4,z84])],[(0,[z1,z2,z8,z3,z4,z196,z6]),(0,[z1,z2,z8,z3,z197,z4,z6])],[(0,[z1,z198,z2,z8,z3,z14,z6])],[(0,[z28,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z199,z6])],[(0,[z1,z2,z3,z4,z9,z5,z6]),(0,[z1,z200,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z201,z3,z4,z6])],[(0,[z2,z117,z8,z175,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z202,z6]),(0,[z1,z2,z8,z3,z4,z203,z6]),(0,[z204,z1,z2,z8,z3,z4,z6])],[(0,[z1,z85,z2,z8,z3,z14,z6])],[(0,[z205,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z206,z6]),(0,[z1,z2,z30,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z207,z6]),(0,[z1,z2,z10,z8,z3,z4,z6]),(1,[z1,z2,z208,z3,z4,z6])]],
   [[(0,[z1,z2,z27,z175,z3,z4,z6]),(0,[z1,z209,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z4,z150,z6,z50]),(0,[z1,z2,z3,z4,z6,z101,z166])],[(0,[z1,z2,z91,z8,z3,z14,z6]),(0,[z210,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z211,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z178,z4,z6])],[(1,[z13,z2,z8,z3,z4,z36]),(0,[z1,z2,z169,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z212])],[(0,[z1,z29,z2,z8,z3,z14,z6]),(0,[z1,z2,z213,z8,z3,z4,z6])],[(0,[z214,z1,z29,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z215,z6])],[(0,[z118,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z6,z216]),(0,[z1,z2,z195,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z217,z4,z6]),(0,[z214,z1,z2,z8,z3,z9,z6]),(0,[z1,z218,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z98,z3,z178,z6])],[(0,[z1,z198,z2,z8,z3,z4,z6]),(0,[z1,z2,z219,z30,z3,z4,z6])],[(0,[z1,z2,z220,z8,z3,z4,z6])],[(0,[z1,z2,z8,z221,z3,z4,z6])],[(0,[z222,z1,z2,z8,z3,z4,z6]),(0,[z223,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z224,z8,z3,z4,z6]),(0,[z1,z2,z8,z98,z3,z83,z6])],[(1,[z1,z2,z225,z3,z4,z6])],[(0,[z42,z1,z2,z8,z3,z4,z196]),(0,[z1,z226,z2,z8,z3,z4,z6]),(0,[z1,z2,z227,z8,z3,z4,z6]),(0,[z1,z2,z195,z8,z4,z83,z6])],[(0,[z1,z2,z8,z3,z14,z6,z46]),(1,[z1,z92,z2,z10,z3,z4]),(0,[z1,z228,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z229,z3,z4,z6])],[(0,[z230,z1,z2,z8,z3,z4,z6]),(1,[z138,z2,z8,z58,z4,z6])],[(0,[z1,z2,z8,z8,z3,z4,z6]),(0,[z1,z2,z231,z3,z4,z6,z87])]],
   [[(0,[z1,z29,z2,z8,z3,z4,z6])],[(0,[z1,z45,z2,z232,z3,z4,z6])],[(1,[z1,z2,z8,z233,z4,z6]),(0,[z1,z2,z234,z8,z3,z14,z6]),(0,[z1,z2,z10,z235,z3,z4,z6])],[(0,[z1,z2,z8,z3,z236,z4,z6]),(0,[z1,z45,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z237,z4,z6]),(1,[z1,z2,z173,z3,z4,z6]),(0,[z1,z2,z8,z98,z178,z4,z6]),(1,[z1,z2,z8,z3,z109,z80])],[(0,[z1,z238,z2,z8,z3,z4,z6]),(0,[z1,z2,z239,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z240,z6]),(0,[z1,z2,z8,z235,z3,z14,z6]),(0,[z241,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z242])],[(0,[z1,z243,z2,z8,z3,z4,z6]),(0,[z1,z2,z30,z175,z3,z4,z6]),(0,[z1,z2,z27,z3,z4,z9,z6]),(0,[z1,z2,z244,z8,z3,z4,z6]),(0,[z1,z92,z44,z8,z3,z4,z6])],[(0,[z1,z2,z245,z8,z3,z4,z6]),(0,[z1,z2,z122,z8,z3,z4,z6]),(0,[z1,z8,z33,z3,z39,z4,z6])],[(0,[z1,z2,z8,z3,z58,z14,z6]),(0,[z1,z92,z2,z8,z3,z14,z6]),(0,[z1,z2,z8,z3,z14,z167,z6]),(0,[z1,z2,z8,z3,z4,z36,z23]),(0,[z1,z130,z2,z27,z3,z4,z6])],[(0,[z246,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z247,z4,z6]),(0,[z1,z2,z8,z3,z14,z80,z6])],[(0,[z1,z2,z190,z3,z4,z5,z6])],[(0,[z1,z248,z2,z8,z3,z4,z6]),(1,[z1,z2,z8,z3,z249,z6]),(0,[z7,z1,z2,z8,z134,z4,z6]),(0,[z1,z2,z8,z3,z14,z6,z50]),(0,[z1,z2,z3,z114,z4,z5,z6])],[(0,[z1,z2,z117,z3,z4,z5,z6]),(0,[z1,z2,z3,z250,z4,z5,z6])],[(0,[z1,z2,z8,z3,z251,z4,z6])],[(1,[z1,z2,z107,z3,z43,z6])],[(0,[z1,z2,z234,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z252,z6])]],
   [[(0,[z1,z2,z253,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z14,z6,z87]),(0,[z1,z2,z30,z254,z3,z4,z6]),(0,[z1,z2,z8,z255,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z256,z6])],[(0,[z1,z2,z8,z27,z3,z9,z6])],[(0,[z28,z1,z2,z30,z3,z4,z6]),(0,[z106,z1,z2,z235,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z257]),(0,[z1,z258,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z235,z3,z4,z6])],[(0,[z1,z2,z8,z134,z3,z14,z6]),(0,[z259,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z260,z6])],[(0,[z165,z13,z2,z8,z3,z4,z6]),(0,[z1,z26,z2,z8,z3,z4,z6])],[(0,[z261,z1,z2,z8,z3,z4,z6]),(1,[z1,z2,z8,z3,z262,z6]),(0,[z7,z1,z2,z8,z3,z14,z6]),(1,[z1,z2,z162,z27,z3,z6]),(0,[z1,z92,z2,z8,z3,z4,z6]),(0,[z1,z2,z3,z4,z202,z5,z6]),(0,[z1,z2,z8,z263,z3,z4,z6])],[(0,[z1,z45,z8,z33,z3,z4,z6])],[],[(0,[z1,z2,z8,z134,z39,z4,z6]),(0,[z1,z2,z8,z3,z264,z4,z6])],[(1,[z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z208,z3,z4,z6,z50])],[(0,[z1,z2,z8,z3,z4,z6,z265]),(0,[z1,z2,z73,z10,z3,z4,z6]),(0,[z266,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z80,z6,z166])],[(1,[z1,z2,z267,z114,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z268])],[(0,[z1,z2,z8,z3,z9,z269,z6]),(0,[z1,z2,z27,z27,z3,z4,z6])],[(0,[z214,z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z162,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z76,z6]),(0,[z1,z270,z2,z8,z3,z4,z6]),(0,[z1,z2,z73,z8,z4,z6,z50])],[(0,[z1,z2,z8,z3,z271,z4,z6]),(0,[z1,z2,z8,z272,z3,z14,z6]),(1,[z1,z2,z8,z254,z4,z150])],[(0,[z1,z2,z8,z3,z4,z6,z273]),(0,[z1,z2,z11,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z274,z6])]],
   [[(0,[z42,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z275,z6]),(0,[z1,z2,z3,z4,z167,z5,z6]),(0,[z1,z2,z276,z10,z3,z4,z6])],[],[(0,[z1,z2,z117,z3,z114,z4,z6]),(0,[z7,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z120,z8,z3,z4,z6]),(0,[z1,z130,z2,z195,z8,z3,z6])],[(0,[z1,z2,z8,z3,z4,z6,z277]),(0,[z1,z2,z10,z3,z62,z4,z6]),(0,[z1,z2,z278,z8,z3,z4,z6]),(0,[z1,z2,z195,z190,z8,z3,z6]),(0,[z1,z2,z8,z3,z99,z4,z6])],[(0,[z1,z2,z8,z279,z3,z4,z6]),(0,[z1,z2,z280,z8,z3,z4,z6])],[(0,[z281,z1,z2,z8,z3,z4,z6]),(0,[z1,z130,z85,z8,z3,z4,z6]),(0,[z1,z44,z2,z3,z4,z5,z6]),(1,[z1,z2,z111,z8,z3,z6])],[(1,[z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z282,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z62,z14,z6]),(0,[z283,z1,z2,z8,z3,z4,z6])],[(0,[z106,z1,z2,z8,z3,z249,z6]),(1,[z1,z2,z284,z8,z3,z6]),(0,[z285,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z175,z3,z9,z6]),(0,[z2,z8,z134,z3,z58,z4,z6]),(0,[z1,z2,z27,z3,z4,z174,z6]),(1,[z1,z2,z286,z3,z4,z6]),(0,[z1,z2,z8,z254,z3,z4,z150])],[],[],[(0,[z28,z1,z253,z8,z3,z4,z6]),(0,[z1,z2,z8,z272,z3,z4,z6]),(0,[z287,z1,z2,z8,z3,z4,z6])],[(0,[z288,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z36,z50]),(0,[z161,z1,z2,z10,z3,z4,z6])],[(0,[z1,z2,z90,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z289,z9,z6]),(0,[z1,z2,z8,z3,z290,z14,z6]),(0,[z1,z291,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z292,z4,z6])]],
   [[(0,[z1,z2,z267,z27,z3,z4,z6])],[(0,[z1,z2,z8,z3,z293,z4,z6])],[(0,[z1,z2,z294,z8,z3,z4,z6]),(1,[z1,z2,z3,z9,z5,z6]),(0,[z13,z1,z2,z8,z3,z4,z87])],[(0,[z1,z2,z8,z3,z295,z4,z6]),(0,[z1,z2,z8,z3,z62,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z296]),(0,[z1,z2,z8,z3,z4,z297,z6])],[(0,[z1,z2,z8,z3,z14,z36,z6]),(0,[z1,z2,z298,z8,z3,z39,z6]),(0,[z1,z2,z142,z3,z4,z5,z6])],[(0,[z1,z66,z2,z8,z3,z4,z6]),(0,[z106,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z107,z8,z3,z14,z6]),(0,[z1,z2,z8,z3,z299,z4,z6])],[(0,[z1,z2,z8,z3,z300,z4,z6])],[(0,[z1,z2,z267,z10,z3,z4,z6])],[(1,[z1,z2,z27,z3,z9,z6]),(0,[z1,z301,z2,z8,z3,z4,z6])],[],[(0,[z1,z2,z8,z3,z4,z302,z6]),(0,[z1,z2,z303,z3,z4,z6,z23]),(0,[z1,z2,z140,z3,z114,z4,z6]),(0,[z1,z2,z10,z142,z3,z4,z6])],[(0,[z1,z2,z8,z3,z290,z4,z6]),(0,[z42,z1,z2,z8,z3,z105,z6]),(0,[z1,z2,z304,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z305,z4,z6]),(0,[z1,z2,z306,z8,z3,z4,z6]),(1,[z1,z307,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z308,z6]),(0,[z309,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z134,z3,z4,z5,z6]),(0,[z1,z2,z27,z254,z3,z4,z6]),(0,[z1,z2,z310,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z150,z36]),(0,[z1,z2,z189,z8,z3,z4,z6]),(0,[z311,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z6,z312])],[(0,[z191,z1,z2,z8,z3,z4,z6]),(0,[z313,z1,z2,z8,z3,z4,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z122,z3,z9,z6]),(1,[z1,z2,z10,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z314,z6]),(0,[z1,z130,z2,z8,z3,z80,z6]),(1,[z1,z2,z315,z3,z4,z6])]],
   [[(0,[z138,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z284,z8,z3,z4,z6]),(0,[z1,z2,z267,z123,z3,z4,z6]),(0,[z1,z2,z123,z3,z43,z4,z6])],[(0,[z106,z1,z2,z267,z3,z4,z6]),(0,[z1,z2,z8,z3,z9,z316,z6]),(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z73,z8,z3,z4,z50]),(1,[z1,z2,z8,z3,z6,z49]),(0,[z1,z2,z8,z317,z3,z4,z6])],[(0,[z106,z1,z2,z8,z3,z4,z6]),(0,[z318,z1,z2,z8,z3,z4,z6]),(1,[z19,z2,z8,z3,z14,z6]),(0,[z13,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z107,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z319,z6])],[(0,[z19,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z38,z8,z3,z4,z6]),(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z286,z3,z4,z6])],[(0,[z1,z2,z320,z8,z3,z4,z6]),(0,[z1,z8,z3,z4,z84,z6,z23]),(0,[z1,z2,z8,z3,z109,z80,z6])],[(0,[z1,z2,z8,z3,z321,z4,z6]),(0,[z322,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z323,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z9,z6,z324]),(0,[z1,z2,z8,z3,z325,z4,z6]),(0,[z1,z2,z73,z8,z254,z4,z6])],[(0,[z42,z1,z2,z30,z3,z4,z6])],[(0,[z28,z1,z2,z8,z233,z4,z6]),(0,[z1,z2,z8,z326,z3,z4,z6]),(0,[z42,z1,z2,z8,z3,z4,z133]),(0,[z1,z2,z8,z3,z4,z6,z327]),(0,[z1,z44,z2,z142,z8,z3,z4]),(0,[z1,z2,z123,z8,z235,z4,z6])],[(0,[z13,z1,z2,z10,z3,z4,z6]),(1,[z1,z85,z8,z3,z76,z6])],[(0,[z1,z26,z2,z8,z3,z14,z6]),(0,[z328,z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z329,z8,z3,z4,z6]),(1,[z1,z2,z3,z99,z4,z6]),(1,[z1,z2,z3,z4,z330,z6])],[(0,[z19,z1,z2,z10,z3,z4,z6]),(0,[z1,z85,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z331,z4,z6]),(0,[z1,z2,z8,z98,z3,z80,z6])],[(0,[z1,z2,z8,z3,z332,z14,z6])],[(0,[z1,z2,z8,z33,z58,z4,z6]),(0,[z1,z2,z333,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z5,z6]),(0,[z1,z2,z334,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z335,z4,z6]),(0,[z1,z2,z336,z8,z3,z4,z6])],[(0,[z1,z45,z2,z8,z33,z4,z6]),(0,[z1,z2,z337,z8,z3,z4,z6]),(0,[z1,z2,z208,z8,z3,z4,z6])]],
   [[(0,[z1,z44,z2,z338,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z150,z6]),(0,[z1,z2,z219,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z339]),(0,[z1,z2,z340,z8,z3,z4,z6])],[(1,[z1,z2,z298,z8,z3,z6]),(0,[z1,z85,z2,z10,z3,z4,z6])],[(0,[z1,z2,z140,z8,z3,z9,z6]),(0,[z1,z2,z27,z3,z4,z341,z6]),(0,[z342,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z343,z254,z3,z4,z6])],[],[(1,[z1,z2,z3,z289,z9,z6])],[(0,[z1,z253,z8,z3,z39,z4,z6]),(0,[z1,z2,z8,z344,z3,z4,z6]),(0,[z1,z2,z10,z175,z3,z4,z6]),(0,[z138,z1,z2,z90,z3,z4,z6]),(0,[z1,z2,z27,z3,z4,z84,z6]),(0,[z1,z2,z73,z27,z3,z4,z6])],[(0,[z1,z2,z8,z3,z155,z4,z6]),(0,[z1,z2,z190,z8,z98,z3,z6])],[(0,[z1,z345,z2,z8,z3,z4,z6]),(0,[z1,z2,z140,z3,z4,z167,z6]),(0,[z1,z2,z8,z3,z346,z4,z6])],[(0,[z1,z2,z8,z3,z332,z4,z6])],[(0,[z24,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z347,z3,z9,z6])],[(0,[z1,z2,z110,z8,z3,z4,z6])],[(0,[z348,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z349,z8,z3,z4,z6])],[(0,[z1,z2,z190,z8,z3,z4,z80])],[(0,[z28,z1,z2,z8,z3,z14,z6]),(1,[z214,z29,z8,z3,z4,z6]),(0,[z1,z2,z350,z8,z3,z4,z6]),(0,[z1,z2,z351,z8,z3,z4,z6]),(0,[z1,z2,z10,z8,z3,z4,z46])]],
   [[(1,[z1,z2,z352,z3,z4,z6]),(0,[z1,z2,z8,z353,z3,z4,z6])],[(1,[z1,z92,z8,z3,z4,z23]),(0,[z1,z2,z3,z43,z4,z5,z6]),(0,[z354,z1,z2,z8,z3,z4,z6])],[],[(0,[z1,z2,z182,z8,z3,z4,z6])],[(0,[z1,z2,z123,z117,z3,z4,z6]),(0,[z1,z130,z8,z3,z62,z4,z6])],[(0,[z1,z2,z27,z3,z4,z6,z166])],[(0,[z1,z2,z8,z175,z3,z4,z6]),(1,[z1,z2,z8,z3,z355,z6]),(0,[z1,z2,z30,z3,z43,z4,z6]),(0,[z1,z2,z8,z3,z4,z330,z6])],[(0,[z138,z1,z2,z8,z134,z4,z6]),(0,[z138,z1,z2,z30,z3,z4,z6]),(0,[z118,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z356,z8,z3,z4,z6]),(0,[z1,z2,z357,z3,z4,z5,z6])],[(0,[z1,z2,z358,z8,z3,z4,z6])],[(0,[z359,z1,z2,z8,z3,z4,z6]),(0,[z7,z2,z8,z134,z3,z4,z6])],[(1,[z1,z2,z360,z3,z4,z6]),(0,[z214,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z195,z8,z3,z178,z6])],[(0,[z1,z2,z361,z8,z3,z4,z6]),(0,[z1,z2,z8,z178,z4,z83,z6]),(0,[z1,z2,z8,z3,z362,z4,z6])],[(0,[z28,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z9,z6]),(0,[z1,z2,z30,z3,z4,z84,z6]),(0,[z1,z92,z2,z10,z3,z4,z6]),(0,[z1,z2,z267,z8,z235,z4,z6]),(0,[z1,z2,z8,z363,z3,z4,z6]),(0,[z1,z2,z10,z3,z364,z4,z6])],[(0,[z1,z2,z8,z3,z4,z365,z6])],[(0,[z1,z85,z2,z366,z3,z4,z6]),(0,[z1,z92,z2,z8,z3,z4,z23]),(0,[z1,z2,z195,z8,z3,z83,z6])],[(1,[z1,z367,z8,z3,z4,z6])]],
   [[(1,[z1,z2,z10,z3,z14,z6]),(0,[z1,z2,z8,z3,z4,z76,z6]),(0,[z1,z2,z8,z3,z368,z4,z6])],[(0,[z1,z2,z8,z3,z4,z369,z6])],[(0,[z1,z2,z10,z8,z3,z4,z87])],[(0,[z1,z2,z231,z8,z3,z4,z6])],[(1,[z1,z2,z232,z3,z4,z6])],[(0,[z1,z370,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z254,z3,z9,z6]),(0,[z1,z2,z8,z3,z9,z83,z6]),(0,[z1,z2,z371,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z372,z6])],[(0,[z1,z2,z8,z3,z373,z4,z6])],[(0,[z214,z1,z2,z8,z3,z4,z6]),(0,[z1,z374,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z375,z3,z4,z6]),(0,[z1,z2,z376,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z377,z4,z6])],[(0,[z214,z1,z253,z8,z3,z4,z6]),(0,[z7,z1,z2,z10,z3,z4,z6])],[(0,[z378,z1,z2,z8,z3,z4,z6]),(0,[z379,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z380,z6]),(0,[z1,z2,z140,z30,z3,z4,z6])],[(0,[z1,z2,z30,z3,z4,z6,z166]),(0,[z1,z2,z381,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z9,z6]),(0,[z1,z2,z190,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z364,z4,z6])],[(0,[z1,z2,z8,z382,z3,z4,z6]),(1,[z1,z2,z122,z3,z4,z6]),(0,[z1,z2,z3,z289,z4,z9,z6]),(0,[z1,z45,z2,z3,z4,z5,z6]),(1,[z1,z2,z10,z3,z4,z6])],[(0,[z1,z2,z117,z8,z3,z9,z6])],[(0,[z1,z2,z8,z3,z4,z34,z6])]],
   [[(1,[z1,z2,z383,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z384,z6])],[(0,[z1,z2,z298,z8,z3,z4,z6])],[(0,[z1,z2,z253,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z9,z167,z6]),(0,[z1,z2,z10,z27,z3,z4,z6]),(1,[z1,z2,z38,z8,z3,z4]),(0,[z1,z2,z8,z3,z4,z385,z6]),(0,[z1,z85,z2,z8,z3,z80,z6]),(1,[z1,z130,z8,z3,z62,z6]),(0,[z1,z130,z2,z3,z4,z5,z6]),(0,[z1,z386,z2,z8,z3,z4,z6]),(0,[z387,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z388,z3,z4,z5,z6])],[(0,[z1,z2,z30,z3,z4,z6,z389]),(0,[z1,z92,z2,z320,z3,z4,z6]),(0,[z1,z2,z390,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z391,z6]),(0,[z1,z2,z8,z3,z392,z4,z6]),(0,[z1,z2,z122,z3,z4,z9,z6]),(0,[z1,z2,z323,z8,z3,z4,z6]),(0,[z1,z2,z352,z8,z3,z4,z6])],[(0,[z1,z2,z8,z27,z3,z14,z6]),(0,[z1,z2,z8,z3,z4,z393,z6])],[(1,[z1,z2,z8,z3,z4,z394]),(0,[z1,z2,z8,z3,z9,z395,z6]),(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z1,z396,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z397,z3,z4,z6]),(0,[z1,z2,z8,z398,z3,z4,z6])],[(0,[z1,z2,z8,z3,z43,z9,z6]),(0,[z1,z2,z195,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z399,z6])],[(0,[z1,z2,z400,z8,z3,z14,z6]),(0,[z1,z2,z10,z10,z3,z4,z6])],[(0,[z29,z2,z253,z8,z3,z4,z6]),(0,[z1,z2,z30,z117,z3,z4,z6]),(0,[z1,z2,z8,z3,z9,z6,z87]),(0,[z401,z1,z2,z8,z3,z4,z6])],[(0,[z402,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z403,z3,z4,z6]),(1,[z1,z2,z404,z3,z4,z6]),(0,[z1,z2,z405,z8,z3,z4,z6]),(0,[z1,z2,z169,z10,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z61,z6]),(0,[z1,z2,z3,z4,z6,z406,z50]),(0,[z1,z2,z190,z8,z3,z4,z166])],[(0,[z1,z2,z407,z8,z3,z9,z6]),(0,[z118,z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z408,z8,z3,z4,z6])],[(0,[z1,z2,z195,z10,z3,z4,z6])]],
   [[(0,[z409,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z232,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z410,z6])],[(0,[z1,z2,z175,z3,z4,z5,z6]),(0,[z1,z2,z8,z411,z3,z4,z6])],[(0,[z1,z2,z8,z27,z3,z4,z6]),(0,[z1,z2,z10,z123,z3,z4,z6])],[(0,[z1,z29,z2,z27,z3,z4,z6]),(0,[z1,z2,z27,z3,z43,z4,z6]),(0,[z0,z1,z2,z8,z3,z4,z6])],[(0,[z42,z1,z2,z8,z3,z14,z6]),(1,[z1,z2,z320,z3,z4,z6])],[(0,[z141,z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z303,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z412,z4,z6])],[(0,[z1,z2,z360,z8,z3,z4,z6]),(0,[z1,z2,z400,z8,z3,z4,z6]),(0,[z1,z2,z27,z3,z4,z5,z6]),(0,[z1,z226,z2,z10,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z105,z6]),(0,[z1,z44,z2,z8,z3,z9,z6]),(0,[z165,z1,z2,z30,z3,z4,z6]),(0,[z1,z44,z2,z10,z8,z3,z4])],[(0,[z413,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z8,z3,z4,z5])],[(0,[z106,z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z8,z347,z3,z4,z6]),(0,[z1,z45,z2,z414,z3,z4,z6]),(1,[z1,z2,z366,z3,z4,z6]),(0,[z1,z2,z107,z10,z3,z4,z6])],[(0,[z1,z29,z2,z10,z3,z4,z6]),(0,[z32,z1,z2,z30,z3,z4,z6])],[(0,[z13,z1,z2,z8,z3,z4,z36]),(0,[z1,z2,z415,z8,z3,z4,z6])],[(0,[z1,z2,z8,z175,z3,z14,z6]),(0,[z1,z2,z30,z3,z14,z4,z6])],[(0,[z416,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z174,z6]),(0,[z1,z2,z417,z8,z3,z4,z6]),(0,[z1,z2,z8,z418,z3,z4,z6])],[(0,[z1,z2,z419,z8,z3,z4,z6])]],
   [[(0,[z42,z1,z2,z267,z3,z4,z6])],[(0,[z42,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z420]),(0,[z421,z1,z2,z8,z3,z4,z6])],[],[(0,[z1,z2,z422,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z9,z6,z23]),(0,[z1,z2,z190,z30,z3,z4,z6]),(0,[z1,z2,z10,z254,z3,z4,z6])],[(0,[z2,z8,z3,z14,z4,z9,z6]),(0,[z13,z1,z2,z423,z3,z4,z6]),(0,[z328,z1,z2,z8,z3,z4,z6]),(0,[z424,z1,z2,z8,z3,z4,z6])],[(0,[z1,z130,z2,z8,z3,z76,z6])],[(0,[z425,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z142,z8,z3,z9,z6]),(0,[z1,z2,z8,z254,z3,z14,z6])],[(0,[z1,z26,z2,z27,z3,z4,z6]),(0,[z1,z2,z2,z30,z3,z4,z6]),(0,[z1,z426,z2,z8,z3,z4,z6]),(0,[z1,z2,z123,z140,z3,z4,z6])],[(1,[z1,z2,z231,z3,z4,z6]),(0,[z1,z92,z2,z27,z3,z4,z6]),(1,[z1,z2,z284,z27,z3,z6]),(0,[z1,z2,z8,z3,z4,z427,z6]),(0,[z1,z85,z2,z195,z8,z3,z6])],[(0,[z1,z2,z253,z30,z3,z4,z6]),(0,[z1,z29,z8,z3,z39,z4,z6]),(0,[z106,z1,z2,z175,z3,z4,z6])],[],[(0,[z1,z2,z428,z8,z3,z4,z6])],[(1,[z1,z2,z27,z3,z14,z6]),(0,[z1,z2,z30,z3,z4,z5,z6])],[(0,[z1,z2,z429,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z36,z6]),(0,[z1,z26,z2,z10,z3,z4,z6]),(0,[z1,z130,z2,z8,z3,z62,z6])],[(0,[z1,z2,z8,z3,z289,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z430]),(0,[z1,z2,z431,z8,z3,z4,z6])]],
   [[(0,[z28,z1,z2,z360,z3,z4,z6]),(0,[z138,z1,z2,z8,z3,z262,z6]),(0,[z1,z2,z162,z27,z3,z4,z6]),(0,[z24,z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z432])],[(0,[z141,z1,z2,z8,z3,z9,z6])],[(0,[z1,z2,z8,z3,z14,z76,z6]),(0,[z1,z433,z2,z8,z3,z4,z6])],[(0,[z165,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z315,z98,z3,z4,z6]),(0,[z1,z2,z8,z254,z3,z4,z6])],[(0,[z42,z1,z2,z235,z3,z4,z6]),(0,[z138,z1,z2,z8,z3,z14,z6]),(1,[z1,z2,z343,z3,z4,z6])],[(0,[z7,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z366,z3,z4,z6]),(0,[z1,z2,z3,z4,z434,z6,z23]),(0,[z1,z2,z8,z3,z435,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z430])],[(1,[z1,z2,z8,z3,z436,z6]),(0,[z32,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z437,z30,z3,z4,z6]),(0,[z1,z2,z107,z8,z3,z43,z6])],[(0,[z438,z1,z2,z8,z3,z4,z6])],[(0,[z439,z1,z2,z8,z3,z4,z6]),(0,[z1,z92,z8,z3,z4,z6,z23]),(0,[z1,z2,z8,z3,z250,z4,z6])],[(1,[z1,z2,z27,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z6,z46]),(0,[z1,z2,z8,z3,z440,z4,z6]),(0,[z441,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z442,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z443,z6])],[(1,[z1,z2,z8,z3,z4,z177]),(0,[z444,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z84,z6])],[(0,[z1,z2,z8,z3,z34,z6,z23])],[(1,[z1,z2,z8,z3,z4,z185]),(0,[z1,z2,z8,z3,z14,z9,z6]),(0,[z1,z44,z2,z30,z3,z4,z6]),(0,[z1,z2,z356,z10,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z445,z6]),(1,[z1,z2,z280,z3,z4,z6])],[(0,[z1,z2,z446,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z447,z6]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z195,z8,z3,z80,z6])]],
   [[(0,[z1,z2,z8,z448,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z394,z6]),(0,[z1,z130,z2,z140,z8,z3,z6])],[(0,[z138,z1,z2,z8,z3,z4,z6]),(0,[z1,z449,z2,z8,z3,z4,z6]),(0,[z1,z2,z3,z4,z207,z5,z6])],[(0,[z1,z2,z8,z3,z4,z450,z6]),(0,[z1,z2,z30,z3,z114,z4,z6])],[(0,[z28,z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z27,z3,z451,z4,z6]),(0,[z1,z2,z452,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z14,z314,z6]),(0,[z1,z2,z453,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z454,z4,z6]),(0,[z1,z2,z455,z8,z3,z4,z6])],[(0,[z1,z2,z456,z8,z3,z4,z6]),(0,[z1,z2,z8,z457,z3,z4,z6]),(1,[z1,z2,z3,z4,z174,z6]),(0,[z1,z2,z458,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z459,z6])],[(0,[z1,z2,z8,z3,z9,z80,z6]),(0,[z1,z2,z3,z4,z5,z84,z6])],[(1,[z1,z2,z8,z3,z82,z6]),(0,[z1,z2,z140,z8,z3,z14,z6]),(0,[z1,z2,z460,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z461,z6]),(0,[z7,z1,z2,z8,z58,z4,z6]),(0,[z1,z2,z8,z3,z9,z6,z50]),(0,[z1,z2,z107,z8,z3,z167,z6])],[(0,[z462,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z27,z3,z14,z4,z6]),(0,[z1,z2,z8,z3,z4,z341,z6]),(0,[z1,z2,z8,z3,z4,z6,z463])],[(1,[z1,z2,z8,z3,z464,z6])],[(0,[z1,z2,z8,z3,z4,z6,z465]),(0,[z1,z2,z8,z3,z4,z466,z6]),(0,[z1,z2,z10,z3,z4,z6,z166]),(0,[z1,z2,z467,z8,z3,z4,z6])],[(0,[z1,z2,z407,z8,z3,z4,z6]),(0,[z1,z2,z404,z8,z3,z4,z6]),(0,[z24,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z468,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z469]),(0,[z1,z2,z8,z3,z4,z84,z6])],[(0,[z1,z2,z142,z30,z3,z4,z6]),(0,[z1,z2,z383,z8,z3,z4,z6]),(0,[z1,z2,z470,z8,z3,z4,z6])],[(0,[z214,z1,z2,z10,z3,z4,z6]),(0,[z1,z44,z2,z68,z3,z4,z6]),(0,[z1,z2,z8,z3,z471,z4,z6])],[(0,[z1,z130,z2,z8,z98,z3,z6])]],
   [[(0,[z472,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z473,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z474]),(0,[z1,z2,z73,z3,z4,z5,z6]),(0,[z1,z2,z8,z475,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z476,z6]),(0,[z1,z2,z8,z477,z3,z4,z6])],[],[(0,[z1,z2,z8,z3,z4,z478,z6]),(0,[z1,z2,z3,z4,z5,z479,z6])],[(1,[z1,z2,z8,z3,z37,z6]),(0,[z1,z2,z284,z27,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z83,z6]),(0,[z1,z2,z8,z3,z480,z4,z6]),(0,[z1,z2,z8,z3,z481,z4,z6]),(0,[z1,z482,z2,z8,z3,z4,z6])],[(0,[z1,z2,z140,z8,z3,z4,z6])],[(0,[z1,z483,z2,z8,z3,z4,z6]),(0,[z106,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z484,z4,z6]),(0,[z1,z2,z107,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z459,z6]),(0,[z1,z2,z3,z4,z5,z6,z166])],[(0,[z28,z1,z2,z8,z3,z37,z6]),(1,[z1,z2,z3,z289,z4,z6]),(0,[z1,z2,z485,z8,z3,z4,z6])],[(0,[z138,z1,z307,z8,z3,z4,z6]),(0,[z1,z2,z38,z27,z3,z4,z6]),(0,[z1,z2,z414,z8,z3,z4,z6]),(1,[z1,z2,z142,z3,z4,z5])],[(1,[z1,z2,z423,z3,z4,z6]),(0,[z1,z2,z30,z3,z109,z4,z6]),(0,[z1,z2,z3,z43,z4,z167,z6]),(0,[z1,z2,z8,z3,z4,z479,z6]),(0,[z1,z2,z3,z109,z4,z330,z6])],[(0,[z1,z486,z2,z8,z3,z4,z6]),(0,[z1,z2,z487,z8,z3,z4,z6]),(0,[z1,z2,z8,z254,z4,z150,z6])],[(0,[z1,z2,z8,z488,z3,z39,z6]),(0,[z489,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z490,z8,z3,z4,z6]),(0,[z118,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z10,z8,z3,z4,z36]),(0,[z1,z2,z8,z3,z491,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z166])],[(0,[z1,z2,z27,z3,z4,z150,z6]),(0,[z1,z2,z8,z492,z3,z4,z6]),(0,[z1,z2,z8,z3,z109,z4,z80])],[(0,[z1,z2,z8,z3,z4,z493,z6])],[(0,[z1,z2,z30,z98,z3,z4,z6])],[]],
   [[(1,[z118,z1,z8,z39,z4,z6]),(0,[z1,z2,z8,z494,z3,z4,z6])],[(0,[z214,z29,z2,z8,z3,z4,z6]),(0,[z1,z2,z495,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z249,z6]),(1,[z1,z2,z8,z3,z292,z6]),(0,[z1,z2,z404,z3,z58,z4,z6]),(0,[z1,z2,z8,z496,z3,z4,z6])],[(0,[z1,z44,z8,z3,z4,z84,z6])],[(0,[z1,z2,z8,z3,z114,z9,z6])],[(0,[z497,z1,z2,z8,z3,z4,z6])],[(1,[z1,z2,z195,z8,z83,z6])],[(0,[z498,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z499,z6])],[(0,[z118,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z98,z3,z4,z5,z6]),(0,[z1,z2,z195,z8,z98,z4,z6]),(0,[z500,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z175,z3,z114,z4,z6]),(0,[z118,z1,z2,z286,z3,z4,z6]),(0,[z1,z2,z33,z3,z4,z5,z6])],[(0,[z1,z2,z8,z501,z3,z4,z6]),(0,[z1,z2,z8,z502,z3,z4,z6]),(1,[z1,z2,z169,z3,z4,z6]),(0,[z1,z44,z2,z8,z3,z4,z84])],[(0,[z1,z2,z8,z3,z4,z262,z6])],[(0,[z1,z45,z29,z8,z3,z4,z6]),(0,[z1,z2,z503,z8,z3,z4,z6]),(1,[z7,z2,z8,z134,z4,z6]),(0,[z1,z2,z267,z3,z4,z5,z6]),(1,[z1,z2,z10,z3,z4,z46])],[(0,[z1,z2,z8,z504,z3,z4,z6]),(0,[z1,z2,z8,z505,z3,z4,z6]),(0,[z1,z2,z30,z3,z506,z4,z6]),(0,[z1,z507,z2,z8,z3,z4,z6])],[(0,[z1,z2,z508,z8,z3,z4,z6]),(0,[z141,z1,z2,z8,z3,z4,z6]),(0,[z1,z45,z2,z8,z3,z9,z6]),(0,[z1,z2,z110,z27,z3,z4,z6]),(0,[z1,z2,z27,z3,z114,z4,z6]),(0,[z1,z509,z2,z8,z3,z4,z6])]],
   [[(0,[z1,z2,z510,z8,z3,z4,z6]),(0,[z1,z2,z190,z8,z3,z14,z6])],[(0,[z165,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6,z133]),(0,[z1,z2,z117,z8,z3,z14,z6]),(1,[z1,z2,z3,z4,z466,z6]),(0,[z1,z2,z30,z511,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z150,z6]),(0,[z1,z92,z2,z492,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6,z512])],[(0,[z1,z2,z8,z513,z3,z4,z6]),(0,[z1,z130,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z423,z3,z4,z6]),(0,[z32,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z514,z8,z3,z4,z6]),(0,[z515,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6,z516]),(0,[z1,z2,z73,z8,z3,z4,z150]),(0,[z1,z2,z8,z3,z517,z4,z6])],[(0,[z1,z2,z253,z8,z3,z14,z6]),(0,[z518,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z519,z6]),(0,[z1,z2,z419,z10,z3,z4,z6]),(0,[z1,z2,z111,z8,z3,z4,z6])],[(0,[z520,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z521,z8,z3,z4,z6]),(0,[z1,z2,z8,z522,z3,z4,z6])],[(1,[z1,z2,z8,z3,z139,z6]),(0,[z42,z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z123,z8,z3,z9,z6]),(0,[z1,z374,z2,z8,z3,z4,z6])],[(0,[z1,z2,z10,z3,z43,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z523])],[(0,[z1,z2,z8,z3,z109,z9,z6]),(0,[z1,z2,z524,z8,z3,z14,z6])],[(0,[z1,z2,z8,z3,z4,z525,z6])],[(0,[z1,z2,z8,z3,z43,z14,z6])],[(0,[z138,z2,z8,z3,z58,z4,z6]),(0,[z1,z2,z8,z3,z4,z4,z6]),(0,[z1,z2,z190,z8,z3,z4,z6])],[(0,[z13,z1,z2,z8,z3,z526,z6]),(0,[z1,z2,z162,z8,z27,z3,z6]),(0,[z527,z1,z2,z8,z3,z4,z6])],[(0,[z28,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z117,z8,z3,z4,z6]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z528,z2,z8,z3,z4,z6]),(1,[z1,z2,z3,z4,z479,z6]),(0,[z1,z2,z3,z178,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z98,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z529,z6]),(1,[z1,z2,z10,z3,z4,z87]),(0,[z1,z2,z27,z3,z4,z83,z6]),(0,[z1,z2,z8,z3,z530,z4,z6]),(0,[z1,z2,z8,z3,z4,z531,z6]),(0,[z1,z2,z280,z3,z4,z6,z166])],[(0,[z1,z2,z2,z8,z3,z4,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z30,z3,z4,z6,z23]),(0,[z1,z2,z8,z3,z4,z6,z532]),(0,[z1,z2,z8,z3,z533,z4,z6])],[(0,[z28,z1,z2,z8,z3,z4,z177]),(0,[z534,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z30,z30,z3,z4,z6]),(0,[z1,z2,z169,z3,z4,z84,z6])],[(0,[z1,z2,z253,z8,z3,z4,z6]),(1,[z1,z2,z38,z27,z3,z4]),(1,[z1,z2,z492,z3,z4,z6]),(0,[z1,z2,z267,z3,z114,z4,z6])],[(0,[z1,z2,z8,z535,z3,z4,z6]),(1,[z106,z2,z175,z3,z4,z6]),(0,[z1,z2,z30,z33,z3,z4,z6]),(0,[z1,z2,z8,z536,z3,z4,z6])],[(0,[z1,z2,z27,z3,z109,z4,z6])],[(0,[z1,z2,z8,z3,z4,z240,z6]),(0,[z1,z2,z8,z3,z4,z537,z6]),(0,[z1,z130,z2,z107,z8,z3,z6]),(0,[z1,z2,z8,z538,z3,z4,z6])],[(0,[z1,z2,z8,z539,z3,z4,z6]),(0,[z1,z2,z524,z8,z3,z4,z6]),(0,[z1,z540,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z541]),(0,[z1,z2,z30,z3,z39,z4,z6])],[(0,[z42,z1,z2,z175,z3,z4,z6]),(0,[z1,z2,z542,z8,z3,z4,z6]),(0,[z1,z2,z8,z543,z3,z4,z6]),(0,[z1,z85,z2,z3,z4,z5,z6])],[(0,[z106,z1,z2,z3,z43,z4,z6]),(0,[z1,z2,z27,z3,z4,z6,z544]),(0,[z1,z2,z545,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z546,z6]),(0,[z1,z2,z8,z3,z43,z4,z6]),(0,[z1,z2,z107,z3,z43,z4,z6])],[(0,[z24,z1,z2,z8,z3,z4,z6]),(0,[z214,z1,z2,z27,z3,z4,z6]),(0,[z138,z1,z367,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z14,z393,z6]),(0,[z1,z2,z8,z3,z547,z4,z6])],[(0,[z1,z2,z8,z3,z4,z548,z6]),(0,[z1,z44,z2,z8,z3,z14,z6]),(0,[z1,z2,z27,z549,z3,z4,z6]),(0,[z1,z2,z27,z98,z3,z4,z6]),(0,[z1,z2,z8,z3,z109,z4,z166])],[(0,[z1,z2,z30,z3,z4,z36,z6]),(1,[z1,z2,z110,z8,z3,z4]),(0,[z1,z2,z8,z3,z4,z550,z6])],[(0,[z551,z1,z2,z8,z3,z4,z6]),(0,[z552,z1,z2,z8,z3,z4,z6]),(0,[z553,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z27,z3,z4,z167,z6])],[(1,[z1,z2,z3,z4,z434,z6]),(0,[z1,z2,z3,z4,z83,z5,z6])],[(0,[z1,z2,z8,z3,z4,z6,z554]),(0,[z1,z2,z8,z3,z4,z6,z555])]],
   [[(0,[z1,z2,z437,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z556,z6]),(0,[z138,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z557])],[(0,[z106,z2,z8,z175,z3,z4,z6]),(0,[z1,z2,z558,z8,z3,z4,z6])],[(0,[z559,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z560,z6])],[(1,[z1,z30,z27,z3,z4,z6])],[(0,[z1,z2,z27,z3,z4,z6,z87])],[(1,[z1,z2,z8,z3,z4,z561]),(0,[z1,z2,z8,z3,z4,z6,z562]),(0,[z1,z45,z2,z30,z3,z4,z6]),(0,[z563,z1,z2,z8,z3,z4,z6])],[],[(0,[z42,z106,z2,z8,z3,z4,z6]),(0,[z138,z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z6,z46]),(0,[z1,z44,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z49])],[(0,[z1,z2,z8,z3,z564,z4,z6]),(0,[z28,z1,z2,z8,z3,z4,z561])],[(0,[z1,z2,z8,z565,z3,z4,z6]),(0,[z1,z2,z142,z8,z3,z14,z6])],[(0,[z1,z29,z2,z565,z3,z4,z6]),(0,[z1,z130,z2,z30,z3,z4,z6]),(0,[z1,z566,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z220,z3,z4,z6]),(0,[z1,z2,z254,z3,z4,z5,z6]),(0,[z1,z2,z567,z8,z3,z4,z6])],[(0,[z1,z2,z267,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z464,z4,z6]),(0,[z1,z2,z8,z568,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z269,z6]),(0,[z1,z2,z10,z117,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z380,z6]),(0,[z569,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z140,z3,z4,z6])],[(0,[z1,z2,z30,z8,z3,z9,z6]),(0,[z1,z2,z190,z8,z3,z6,z166])],[(0,[z1,z570,z2,z8,z3,z4,z6]),(0,[z1,z2,z123,z30,z3,z4,z6]),(0,[z1,z571,z2,z8,z3,z4,z6])]],
   [[(0,[z1,z2,z8,z3,z526,z4,z6])],[(0,[z138,z1,z2,z8,z3,z4,z394]),(0,[z1,z2,z284,z8,z27,z3,z6]),(0,[z1,z2,z8,z3,z4,z572,z6])],[(0,[z1,z2,z8,z3,z4,z6,z573]),(0,[z1,z92,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z3,z436,z4,z6]),(0,[z1,z2,z8,z3,z4,z574,z6]),(0,[z1,z2,z30,z3,z4,z167,z6]),(0,[z118,z1,z2,z8,z39,z4,z6])],[(0,[z138,z1,z2,z8,z58,z4,z6]),(0,[z1,z2,z30,z3,z4,z80,z6]),(0,[z1,z2,z3,z4,z193,z5,z6])],[(0,[z141,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z30,z329,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z575,z6])],[(0,[z1,z2,z8,z194,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z6,z50]),(0,[z1,z2,z8,z3,z4,z6,z389]),(1,[z1,z2,z10,z3,z4,z5])],[(0,[z165,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z8,z488,z3,z4,z6]),(0,[z1,z85,z8,z3,z4,z76,z6]),(0,[z1,z2,z8,z3,z4,z576,z6]),(0,[z1,z2,z142,z8,z3,z4,z6])],[(0,[z1,z2,z577,z8,z3,z4,z6])],[(0,[z1,z2,z578,z8,z3,z4,z6]),(0,[z579,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z39,z9,z6]),(0,[z1,z580,z2,z8,z3,z14,z6]),(0,[z165,z2,z8,z3,z4,z6,z87]),(0,[z1,z2,z8,z581,z3,z4,z6])],[(0,[z32,z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z8,z3,z4,z582,z6]),(0,[z1,z2,z8,z3,z4,z434,z6]),(0,[z1,z270,z2,z3,z4,z5,z6])],[(0,[z1,z2,z30,z3,z4,z6,z87]),(0,[z1,z85,z2,z8,z3,z76,z6]),(0,[z1,z2,z146,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z76,z6]),(0,[z1,z2,z102,z8,z3,z4,z6]),(0,[z1,z2,z123,z8,z114,z4,z6])],[(0,[z106,z1,z2,z117,z3,z4,z6]),(0,[z1,z2,z8,z3,z583,z4,z6]),(0,[z584,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z27,z3,z4,z6,z23])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z10,z3,z14,z4,z6]),(1,[z1,z26,z27,z3,z4,z6]),(0,[z1,z2,z3,z39,z4,z5,z6])]],
   [[(1,[z42,z2,z117,z3,z4,z6]),(0,[z1,z2,z124,z8,z3,z4,z6])],[(0,[z311,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z585]),(0,[z165,z1,z2,z8,z3,z355,z6]),(0,[z13,z1,z2,z8,z3,z308,z6]),(0,[z1,z586,z2,z8,z3,z4,z6]),(0,[z1,z2,z27,z33,z3,z4,z6]),(0,[z1,z2,z8,z254,z3,z4,z50])],[(0,[z1,z2,z8,z3,z14,z14,z6]),(0,[z1,z2,z587,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z588,z4,z6]),(1,[z1,z2,z3,z4,z5,z6])],[(0,[z42,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z27,z3,z39,z4,z6]),(0,[z1,z85,z2,z8,z3,z62,z6]),(0,[z1,z2,z589,z8,z3,z4,z6])],[(1,[z1,z2,z8,z3,z392,z6])],[(0,[z1,z2,z8,z3,z590,z4,z6]),(0,[z1,z580,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z591,z4,z6]),(0,[z1,z2,z123,z8,z3,z4,z6])],[(0,[z592,z1,z2,z8,z3,z4,z6]),(0,[z1,z593,z2,z8,z3,z4,z6])],[],[(0,[z1,z2,z27,z3,z4,z36,z6]),(0,[z1,z2,z8,z3,z451,z4,z6])],[(0,[z594,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z595,z4,z6]),(0,[z1,z2,z10,z3,z4,z6,z6]),(0,[z1,z596,z2,z8,z3,z4,z6])],[],[(0,[z1,z2,z8,z3,z4,z355,z6]),(0,[z1,z2,z163,z8,z3,z4,z6]),(0,[z1,z2,z597,z8,z3,z4,z6]),(0,[z1,z598,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z599,z4,z6]),(1,[z1,z2,z8,z3,z4,z196])],[(0,[z1,z2,z8,z600,z3,z4,z6]),(0,[z1,z2,z8,z3,z14,z4,z6]),(0,[z1,z2,z601,z8,z3,z4,z6]),(0,[z118,z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z5,z6])]],
   [[(0,[z1,z602,z2,z8,z3,z4,z6]),(0,[z24,z1,z2,z8,z3,z14,z6]),(0,[z1,z603,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z604,z4,z6])],[(1,[z1,z2,z565,z3,z4,z6]),(0,[z1,z2,z235,z3,z4,z5,z6]),(0,[z1,z2,z8,z605,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z316,z6]),(0,[z151,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z73,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z14,z529,z6]),(0,[z1,z2,z152,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z150,z6])],[(0,[z2,z8,z3,z4,z36,z6,z87]),(0,[z1,z2,z8,z3,z606,z4,z6]),(0,[z1,z2,z267,z30,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z607,z6]),(1,[z1,z2,z3,z4,z380,z6])],[(0,[z1,z2,z27,z3,z4,z6,z46]),(0,[z1,z2,z8,z3,z4,z608,z6]),(0,[z1,z92,z2,z142,z8,z3,z4]),(1,[z1,z2,z303,z3,z4,z6]),(0,[z1,z2,z195,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(1,[z1,z2,z8,z3,z564,z6]),(0,[z609,z1,z2,z8,z3,z4,z6]),(0,[z1,z85,z2,z140,z8,z3,z6]),(0,[z1,z2,z125,z3,z109,z4,z6]),(0,[z1,z2,z8,z3,z4,z610,z6])],[(0,[z1,z2,z8,z3,z4,z6,z324]),(0,[z1,z85,z2,z408,z3,z4,z6])],[(0,[z611,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z140,z8,z3,z43,z6])],[(0,[z1,z2,z8,z3,z14,z6,z541]),(0,[z1,z2,z123,z235,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z5,z6])],[(0,[z214,z1,z2,z8,z3,z436,z6]),(0,[z1,z2,z612,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z233,z4,z6]),(1,[z1,z2,z30,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z6,z6]),(0,[z1,z2,z3,z4,z466,z6,z87]),(0,[z1,z2,z8,z3,z613,z4,z6])],[(0,[z1,z2,z614,z8,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z150,z6])],[(1,[z1,z2,z194,z3,z4,z6]),(0,[z1,z2,z615,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6,z616]),(1,[z2,z8,z3,z14,z9,z6]),(0,[z1,z2,z30,z3,z178,z4,z6])],[(0,[z1,z2,z8,z3,z4,z561,z6]),(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z84,z87]),(1,[z1,z2,z414,z3,z4,z6]),(0,[z1,z2,z107,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z254,z3,z604,z4,z6])]],
   [[(0,[z1,z29,z2,z3,z4,z5,z6])],[(0,[z1,z2,z617,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z14,z84,z6]),(0,[z1,z2,z27,z3,z4,z80,z6])],[(0,[z1,z2,z8,z618,z3,z4,z6]),(0,[z1,z619,z2,z8,z3,z4,z6]),(0,[z1,z130,z2,z173,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z150,z6]),(0,[z1,z2,z8,z620,z3,z4,z6])],[(0,[z1,z2,z27,z3,z4,z6,z50])],[(0,[z1,z2,z8,z621,z3,z4,z6]),(0,[z1,z2,z190,z10,z3,z4,z6])],[(0,[z13,z1,z2,z30,z3,z4,z6]),(0,[z1,z85,z2,z8,z98,z3,z6]),(0,[z1,z2,z8,z3,z622,z4,z6]),(0,[z1,z2,z10,z3,z114,z4,z6])],[(0,[z1,z2,z27,z3,z129,z4,z6])],[(0,[z1,z623,z2,z8,z3,z4,z6]),(0,[z19,z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z27,z135,z3,z4,z6]),(0,[z1,z2,z235,z3,z114,z4,z6]),(0,[z1,z624,z2,z8,z3,z4,z6])],[(0,[z1,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z114,z14,z6]),(0,[z1,z2,z8,z3,z4,z625,z6]),(0,[z1,z2,z8,z3,z4,z6,z626])],[(0,[z138,z1,z2,z8,z3,z4,z185]),(0,[z1,z2,z338,z8,z3,z4,z6])],[(0,[z1,z2,z253,z10,z3,z4,z6]),(0,[z1,z2,z307,z8,z3,z4,z6]),(0,[z19,z2,z8,z3,z14,z4,z6]),(1,[z1,z2,z38,z3,z4,z6]),(0,[z627,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z357,z8,z3,z4,z6])],[(0,[z1,z628,z2,z8,z3,z4,z6])],[(0,[z1,z2,z27,z3,z58,z4,z6]),(0,[z1,z2,z8,z3,z629,z4,z6]),(0,[z1,z2,z30,z8,z3,z4,z6]),(0,[z630,z1,z2,z8,z3,z4,z6])],[(1,[z1,z2,z8,z3,z251,z6]),(0,[z42,z1,z2,z8,z3,z292,z6]),(0,[z1,z2,z8,z3,z4,z6,z631]),(0,[z1,z2,z8,z632,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z633])],[(0,[z210,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z211,z8,z3,z4,z6]),(0,[z1,z85,z2,z30,z3,z4,z6]),(1,[z1,z2,z338,z3,z4,z6])],[]],
   [[(0,[z1,z2,z8,z3,z14,z6,z166]),(0,[z1,z2,z30,z3,z237,z4,z6]),(0,[z1,z130,z2,z190,z8,z3,z6])],[],[(0,[z1,z29,z2,z456,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z634]),(0,[z138,z1,z2,z8,z3,z82,z6]),(0,[z1,z2,z8,z3,z4,z6,z635])],[(0,[z1,z45,z2,z8,z3,z14,z6]),(0,[z1,z2,z545,z8,z3,z4,z6])],[(0,[z1,z26,z2,z3,z4,z5,z6]),(0,[z1,z636,z2,z8,z3,z4,z6]),(0,[z553,z1,z2,z10,z3,z4,z6])],[(0,[z1,z2,z8,z3,z14,z574,z6]),(1,[z1,z2,z8,z3,z308,z6]),(0,[z118,z1,z2,z352,z3,z4,z6]),(0,[z1,z2,z8,z3,z114,z4,z6])],[(0,[z637,z1,z2,z8,z3,z4,z6]),(0,[z1,z8,z3,z62,z4,z76,z6]),(0,[z1,z2,z10,z3,z4,z83,z6])],[(0,[z1,z2,z27,z134,z3,z4,z6]),(0,[z1,z2,z142,z8,z3,z4,z87]),(2,[z1,z2,z38,z3,z4]),(0,[z1,z2,z140,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z638,z4,z6]),(1,[z1,z2,z3,z604,z4,z6])],[(0,[z1,z2,z639,z8,z3,z4,z6]),(0,[z1,z130,z2,z8,z3,z14,z6]),(0,[z640,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z33,z3,z9,z6]),(1,[z1,z2,z10,z3,z4,z36]),(0,[z1,z2,z73,z30,z3,z4,z6])],[(0,[z1,z367,z2,z8,z3,z4,z6])],[(0,[z28,z214,z2,z8,z3,z4,z6]),(0,[z1,z2,z113,z30,z3,z4,z6]),(0,[z1,z2,z10,z3,z109,z4,z6])],[(0,[z641,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z123,z8,z3,z14,z6]),(0,[z1,z30,z8,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z642])],[(0,[z1,z2,z8,z643,z3,z4,z6])],[(0,[z1,z2,z10,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z109,z14,z6]),(0,[z644,z1,z2,z8,z3,z4,z6])],[(0,[z645,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z646,z6]),(0,[z1,z2,z8,z3,z3,z4,z6]),(0,[z1,z2,z30,z235,z3,z4,z6]),(0,[z1,z44,z2,z10,z3,z4,z6])]],
   [[(0,[z106,z1,z2,z140,z3,z4,z6]),(0,[z1,z2,z8,z3,z178,z9,z6]),(0,[z1,z45,z2,z8,z3,z4,z6]),(0,[z1,z2,z107,z140,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6,z647]),(0,[z13,z1,z2,z8,z3,z9,z6]),(0,[z1,z44,z2,z8,z3,z4,z23]),(0,[z1,z2,z10,z98,z3,z4,z6])],[(0,[z1,z45,z253,z8,z3,z4,z6]),(0,[z1,z2,z30,z3,z58,z4,z6]),(1,[z1,z2,z408,z3,z4,z6])],[(0,[z19,z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z10,z3,z4,z167,z6]),(0,[z1,z2,z8,z3,z4,z648,z6]),(0,[z1,z2,z3,z4,z5,z649,z6]),(0,[z1,z2,z8,z3,z4,z6,z650])],[(0,[z7,z1,z2,z8,z3,z392,z6]),(0,[z1,z2,z195,z8,z3,z9,z6]),(0,[z1,z2,z8,z98,z3,z14,z6]),(0,[z165,z1,z2,z8,z3,z4,z87]),(0,[z651,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z652,z3,z4,z6]),(0,[z1,z2,z315,z8,z3,z4,z6])],[(0,[z653,z1,z2,z8,z3,z4,z6]),(1,[z1,z2,z8,z3,z526,z6]),(0,[z1,z130,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z654,z6]),(0,[z1,z2,z388,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z406])],[(0,[z1,z655,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z83,z6])],[(0,[z1,z2,z8,z186,z3,z4,z6]),(0,[z1,z2,z8,z656,z3,z4,z6]),(0,[z1,z2,z142,z27,z3,z4,z6]),(0,[z657,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z658,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z659])],[(0,[z1,z2,z8,z3,z51,z4,z6]),(1,[z1,z2,z8,z488,z3,z6]),(0,[z1,z2,z8,z3,z660,z4,z6]),(0,[z1,z2,z8,z3,z4,z661,z6])],[(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z106,z1,z2,z8,z3,z251,z6]),(1,[z1,z2,z618,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z649,z6]),(0,[z1,z2,z190,z8,z3,z109,z6])],[(0,[z1,z85,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z662,z6])],[(0,[z1,z2,z8,z3,z9,z9,z6]),(0,[z1,z2,z10,z3,z4,z6,z87]),(0,[z1,z2,z225,z8,z3,z4,z6]),(0,[z118,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z27,z3,z178,z4,z6]),(0,[z1,z2,z8,z3,z109,z4,z6])],[(1,[z28,z253,z8,z3,z4,z6])],[(0,[z1,z2,z30,z134,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z663,z6]),(0,[z1,z664,z2,z8,z3,z4,z6]),(0,[z665,z1,z2,z8,z3,z4,z6])],[],[(0,[z1,z29,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z6,z544]),(0,[z1,z2,z3,z4,z76,z5,z6]),(0,[z1,z2,z8,z3,z666,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z667])]],
   [[],[(0,[z1,z2,z8,z549,z3,z4,z6]),(0,[z1,z2,z8,z98,z3,z4,z6])],[(0,[z141,z1,z2,z27,z3,z4,z6])],[(0,[z668,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z669,z8,z3,z4,z6]),(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z167,z6])],[(0,[z214,z1,z2,z3,z4,z5,z6]),(0,[z165,z1,z2,z27,z3,z4,z6]),(0,[z13,z1,z2,z225,z3,z4,z6]),(0,[z1,z2,z8,z670,z3,z4,z6]),(0,[z1,z2,z8,z652,z3,z4,z6]),(0,[z1,z2,z418,z3,z4,z5,z6])],[(0,[z1,z2,z8,z3,z671,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z87])],[(1,[z1,z2,z8,z448,z4,z6]),(0,[z1,z2,z276,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z672,z4,z6])],[(0,[z673,z1,z2,z8,z3,z4,z6]),(0,[z674,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z395,z6]),(0,[z32,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z675,z6]),(0,[z1,z676,z2,z8,z3,z4,z6])],[(1,[z1,z2,z456,z3,z4,z6]),(0,[z1,z2,z8,z3,z247,z9,z6]),(0,[z1,z2,z8,z677,z3,z4,z6]),(0,[z1,z586,z2,z10,z3,z4,z6])],[(0,[z28,z1,z2,z8,z448,z4,z6]),(0,[z1,z2,z8,z3,z4,z678,z6]),(0,[z141,z1,z2,z10,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6,z679]),(0,[z1,z2,z8,z3,z4,z6,z680])],[(0,[z165,z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z6,z87]),(0,[z1,z2,z8,z3,z4,z681,z6])],[(0,[z28,z1,z2,z8,z3,z564,z6]),(0,[z214,z1,z2,z8,z3,z139,z6]),(0,[z1,z85,z2,z107,z8,z3,z6]),(0,[z1,z130,z2,z383,z3,z4,z6]),(0,[z1,z2,z682,z8,z3,z4,z6])],[(1,[z1,z2,z110,z27,z3,z4]),(0,[z1,z2,z142,z8,z3,z4,z5])],[(0,[z32,z1,z2,z10,z3,z4,z6])],[(1,[z1,z2,z8,z98,z178,z6])]],
   [[(0,[z1,z2,z618,z3,z58,z4,z6]),(0,[z1,z2,z8,z33,z134,z4,z6]),(0,[z1,z2,z267,z8,z3,z14,z6]),(0,[z1,z2,z190,z27,z3,z4,z6]),(0,[z1,z2,z30,z3,z62,z4,z6]),(0,[z1,z2,z683,z8,z3,z4,z6])],[(0,[z1,z2,z8,z235,z3,z9,z6]),(0,[z1,z2,z8,z3,z14,z5,z6]),(0,[z1,z2,z8,z3,z684,z14,z6]),(0,[z1,z2,z8,z3,z506,z4,z6]),(0,[z118,z1,z8,z3,z39,z4,z6]),(0,[z1,z2,z8,z3,z4,z685,z6])],[(0,[z1,z2,z117,z27,z3,z4,z6]),(0,[z1,z2,z30,z8,z3,z14,z6]),(0,[z32,z1,z30,z8,z3,z4,z6]),(0,[z1,z2,z8,z686,z3,z4,z6]),(0,[z1,z2,z8,z3,z687,z4,z6])],[(0,[z1,z2,z267,z8,z114,z4,z6])],[(0,[z1,z2,z8,z3,z58,z9,z6]),(0,[z1,z2,z8,z58,z39,z4,z6]),(0,[z1,z92,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z87,z23]),(0,[z1,z2,z2,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z688,z4,z6]),(0,[z1,z92,z2,z10,z8,z3,z4]),(0,[z1,z2,z10,z3,z4,z6,z23]),(0,[z1,z2,z689,z8,z3,z4,z6])],[(0,[z165,z1,z2,z8,z3,z464,z6]),(0,[z1,z2,z8,z511,z3,z4,z6]),(0,[z1,z2,z10,z30,z3,z4,z6]),(0,[z690,z1,z2,z8,z3,z4,z6])],[(0,[z1,z1,z2,z8,z3,z4,z6]),(0,[z28,z2,z253,z8,z3,z4,z6]),(0,[z1,z2,z253,z27,z3,z4,z6]),(0,[z1,z2,z8,z3,z691,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z692]),(0,[z1,z2,z693,z8,z3,z4,z6])],[(0,[z1,z694,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z33,z3,z4,z6]),(1,[z1,z2,z146,z8,z3,z6]),(0,[z1,z2,z142,z8,z3,z4,z46])],[(1,[z1,z2,z123,z235,z4,z6])],[(0,[z1,z2,z695,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z519,z6]),(0,[z1,z2,z8,z3,z4,z6,z696]),(0,[z1,z2,z8,z3,z697,z4,z6])],[(0,[z1,z2,z8,z33,z3,z14,z6]),(0,[z1,z2,z10,z3,z39,z4,z6]),(0,[z1,z2,z698,z8,z3,z4,z6]),(0,[z699,z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z700,z3,z4,z6])],[(0,[z1,z2,z195,z30,z3,z4,z6]),(0,[z701,z1,z2,z8,z3,z4,z6])],[(0,[z1,z2,z8,z3,z702,z4,z6]),(0,[z1,z2,z27,z235,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z703,z6]),(0,[z1,z2,z8,z3,z4,z6,z692]),(1,[z1,z2,z3,z4,z6,z406])],[(0,[z1,z2,z8,z3,z271,z9,z6]),(0,[z1,z2,z8,z3,z39,z14,z6]),(0,[z24,z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z267,z8,z3,z4,z6]),(0,[z1,z2,z140,z8,z3,z167,z6]),(0,[z704,z1,z2,z8,z3,z4,z6])],[(1,[z1,z2,z186,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z705,z6]),(0,[z1,z2,z8,z3,z684,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z23]),(0,[z1,z2,z8,z706,z3,z4,z6])],[(0,[z138,z7,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z134,z3,z9,z6]),(0,[z1,z2,z10,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z174,z84,z6]),(0,[z1,z2,z343,z8,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z30,z3,z4,z561]),(0,[z1,z2,z8,z3,z14,z394]),(0,[z1,z2,z707,z3,z4,z6]),(0,[z1,z2,z10,z3,z622,z4])],[(0,[z1,z2,z8,z3,z4,z708]),(0,[z13,z1,z2,z38,z3,z4]),(0,[z1,z2,z709,z3,z4,z6])],[(0,[z1,z2,z280,z3,z4,z6])],[(0,[z1,z29,z2,z38,z3,z4])],[(0,[z1,z2,z10,z3,z4,z6]),(0,[z1,z2,z565,z3,z9,z6]),(0,[z1,z2,z122,z3,z4,z6]),(0,[z7,z2,z8,z134,z61,z6]),(0,[z1,z2,z710,z3,z4,z6]),(0,[z1,z66,z8,z3,z155,z6]),(0,[z1,z542,z27,z3,z4,z6]),(0,[z165,z2,z8,z3,z464,z87]),(0,[z1,z2,z142,z492,z3,z4]),(0,[z1,z2,z8,z3,z711,z6])],[],[(0,[z1,z2,z404,z3,z14,z6]),(0,[z7,z2,z134,z4,z5,z6]),(0,[z1,z2,z10,z3,z9,z87]),(0,[z1,z2,z712,z3,z4,z6])],[(0,[z1,z2,z713,z3,z4,z6]),(0,[z1,z2,z8,z3,z714,z6])],[(0,[z1,z2,z715,z3,z4,z6]),(0,[z1,z2,z11,z3,z4,z36]),(0,[z1,z2,z120,z506,z4,z6]),(1,[z1,z2,z3,z4,z716])],[(0,[z1,z2,z717,z3,z4,z6]),(0,[z1,z2,z492,z3,z9,z6]),(0,[z165,z2,z8,z3,z4,z718]),(0,[z354,z2,z8,z3,z4,z87]),(0,[z1,z2,z3,z4,z174,z6])],[(0,[z106,z2,z175,z3,z9,z6]),(0,[z1,z2,z719,z3,z4,z185]),(0,[z2,z8,z3,z9,z662,z6]),(0,[z1,z2,z169,z3,z4,z389]),(0,[z1,z2,z3,z5,z6,z720])],[(0,[z1,z2,z448,z4,z5,z6]),(0,[z1,z2,z721,z3,z4,z6]),(0,[z1,z2,z8,z3,z722,z6]),(0,[z497,z2,z8,z134,z4,z6]),(0,[z1,z2,z152,z129,z4,z6])],[(0,[z1,z45,z8,z344,z4,z6]),(0,[z1,z2,z3,z4,z723,z185]),(0,[z1,z2,z724,z8,z3,z6]),(0,[z1,z2,z725,z8,z3,z6]),(1,[z1,z8,z3,z726,z6])],[(0,[z1,z727,z8,z3,z4,z6]),(0,[z1,z2,z3,z289,z14,z6]),(0,[z1,z2,z27,z3,z728,z6])],[(0,[z42,z2,z117,z3,z105,z6]),(0,[z1,z2,z3,z43,z105,z6]),(0,[z1,z2,z8,z3,z464,z6]),(0,[z1,z2,z142,z3,z14,z5]),(0,[z1,z2,z3,z729,z355,z6])],[(0,[z1,z2,z10,z3,z4,z206]),(0,[z1,z2,z730,z8,z3,z6]),(0,[z1,z2,z10,z3,z4,z696]),(0,[z1,z2,z731,z3,z4,z6]),(0,[z1,z2,z190,z3,z101,z166])]],
   [[(0,[z28,z253,z3,z4,z5,z6]),(0,[z1,z2,z732,z3,z14,z6])],[(0,[z1,z2,z8,z3,z4,z733]),(0,[z1,z2,z3,z734,z9,z6]),(0,[z1,z2,z10,z3,z4,z466]),(0,[z1,z2,z3,z4,z735,z6])],[(0,[z2,z8,z3,z736,z4,z6]),(0,[z1,z2,z122,z3,z289,z6]),(0,[z1,z345,z2,z10,z3,z4]),(0,[z1,z26,z162,z27,z3,z6]),(0,[z1,z2,z8,z3,z6,z737])],[(0,[z1,z2,z404,z3,z4,z6]),(0,[z1,z2,z366,z3,z14,z6]),(0,[z1,z2,z3,z14,z330,z6]),(0,[z1,z2,z38,z3,z4,z150]),(0,[z52,z1,z2,z10,z3,z4])],[(0,[z1,z2,z738,z3,z4,z6]),(0,[z1,z2,z8,z3,z739,z6]),(0,[z1,z740,z8,z3,z4,z6]),(0,[z1,z3,z4,z174,z479,z6]),(0,[z1,z449,z2,z10,z3,z4]),(0,[z1,z2,z3,z741,z5,z6]),(0,[z1,z2,z73,z208,z4,z50])],[(0,[z1,z2,z8,z3,z4,z742]),(0,[z1,z2,z38,z27,z3,z9]),(0,[z1,z2,z38,z3,z743,z4]),(0,[z1,z2,z744,z3,z4,z6]),(0,[z0,z1,z3,z4,z479,z6]),(0,[z1,z2,z98,z99,z178,z6])],[(0,[z1,z2,z3,z4,z745,z6]),(0,[z161,z2,z8,z3,z4,z36]),(0,[z1,z2,z8,z3,z726,z6]),(0,[z1,z2,z10,z3,z4,z633])],[(0,[z1,z2,z8,z3,z37,z6]),(0,[z1,z2,z284,z3,z167,z6]),(0,[z311,z2,z3,z4,z649,z6])],[(0,[z1,z2,z8,z3,z746,z6]),(0,[z138,z2,z27,z58,z4,z6]),(0,[z1,z664,z27,z3,z4,z6]),(0,[z1,z2,z110,z284,z8,z3])],[(0,[z1,z2,z747,z3,z4,z6]),(0,[z1,z26,z748,z3,z4,z6]),(0,[z1,z2,z8,z4,z749,z50])],[(0,[z1,z2,z3,z289,z4,z6]),(0,[z1,z307,z10,z3,z4,z6]),(0,[z7,z2,z30,z134,z4,z6]),(0,[z1,z30,z27,z3,z9,z6]),(0,[z1,z2,z750,z3,z14,z6]),(0,[z1,z2,z38,z284,z27,z3])],[(0,[z1,z2,z10,z3,z4,z634]),(0,[z1,z2,z751,z3,z4,z6]),(0,[z1,z2,z107,z3,z752,z6]),(0,[z1,z2,z142,z3,z4,z5])],[(0,[z1,z2,z27,z233,z4,z6]),(0,[z1,z2,z753,z3,z4,z6]),(0,[z2,z27,z3,z14,z9,z6]),(0,[z1,z2,z3,z754,z5,z6])],[(0,[z1,z2,z8,z3,z4,z755]),(0,[z1,z2,z732,z3,z4,z6]),(0,[z138,z2,z8,z58,z4,z185]),(0,[z1,z2,z140,z3,z314,z6]),(0,[z1,z2,z38,z3,z43,z4]),(0,[z1,z2,z756,z3,z4,z6])],[(0,[z1,z2,z110,z8,z3,z9]),(0,[z1,z2,z757,z8,z4,z6]),(0,[z1,z2,z38,z3,z178,z4]),(0,[z32,z1,z3,z4,z479,z6])],[(0,[z1,z2,z8,z233,z4,z177]),(0,[z1,z2,z306,z3,z4,z5]),(0,[z1,z2,z208,z3,z4,z36]),(0,[z1,z2,z8,z3,z758,z6]),(0,[z1,z2,z10,z3,z6,z49])]],
   [[(0,[z28,z253,z8,z448,z4,z6]),(0,[z214,z1,z2,z38,z3,z4]),(0,[z1,z2,z8,z3,z6,z759]),(0,[z1,z85,z27,z3,z76,z6]),(0,[z1,z2,z366,z3,z4,z6]),(0,[z1,z130,z383,z3,z62,z6])],[(0,[z1,z2,z760,z8,z3,z6])],[(0,[z1,z2,z761,z3,z4,z6]),(0,[z1,z2,z231,z3,z14,z6]),(0,[z2,z8,z3,z264,z14,z6]),(0,[z1,z228,z27,z3,z4,z6]),(0,[z1,z2,z73,z30,z4,z50]),(0,[z1,z2,z3,z4,z762,z6])],[(0,[z28,z253,z8,z3,z564,z6]),(0,[z1,z2,z763,z8,z4,z6]),(0,[z1,z2,z764,z3,z4,z6]),(0,[z1,z307,z8,z3,z4,z394]),(0,[z1,z2,z765,z3,z9,z6]),(0,[z1,z2,z766,z3,z4,z6]),(0,[z1,z2,z767,z3,z4,z6]),(0,[z1,z2,z357,z4,z6,z430])],[(0,[z1,z2,z3,z4,z768,z6]),(1,[z1,z2,z38,z284,z3]),(0,[z118,z1,z8,z39,z4,z6]),(0,[z1,z85,z683,z8,z3,z6])],[(0,[z1,z2,z30,z3,z139,z6]),(0,[z1,z2,z27,z3,z249,z6]),(0,[z1,z578,z27,z3,z4,z6]),(0,[z1,z2,z38,z3,z109,z4]),(0,[z1,z2,z3,z769,z4,z6])],[(0,[z1,z2,z8,z3,z292,z6]),(0,[z1,z307,z8,z58,z4,z6]),(0,[z138,z2,z8,z58,z82,z6]),(0,[z1,z2,z123,z511,z4,z6]),(0,[z1,z2,z8,z3,z770,z6]),(0,[z1,z2,z771,z10,z3,z6])],[(0,[z210,z1,z2,z284,z3,z6]),(0,[z1,z2,z8,z772,z3,z6]),(0,[z1,z2,z773,z3,z4,z6]),(0,[z1,z85,z10,z3,z76,z6])],[(0,[z1,z2,z774,z3,z4,z6]),(0,[z1,z2,z3,z9,z6,z101]),(0,[z1,z2,z213,z8,z4,z50]),(0,[z1,z2,z775,z3,z4,z6])],[(0,[z1,z776,z8,z3,z4,z6]),(0,[z777,z1,z2,z38,z3,z4]),(0,[z1,z2,z778,z8,z3,z6])],[(0,[z1,z2,z38,z3,z114,z4]),(0,[z1,z596,z2,z10,z3,z4])],[(0,[z1,z2,z3,z4,z779,z561]),(0,[z1,z2,z8,z3,z780,z6]),(0,[z1,z781,z8,z3,z4,z6]),(0,[z13,z2,z423,z3,z4,z36]),(0,[z1,z2,z225,z3,z4,z36]),(0,[z782,z2,z8,z3,z4,z6])],[(0,[z1,z2,z10,z3,z9,z36]),(0,[z1,z2,z783,z3,z4,z6]),(0,[z165,z2,z3,z4,z466,z87]),(0,[z1,z2,z162,z3,z451,z6]),(0,[z1,z2,z8,z3,z784,z6]),(1,[z1,z2,z3,z752,z6]),(0,[z1,z2,z785,z3,z4,z6])],[(0,[z1,z2,z8,z448,z564,z6]),(0,[z1,z2,z8,z3,z786,z6]),(0,[z1,z2,z787,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z75]),(0,[z1,z2,z788,z27,z3,z6]),(0,[z1,z2,z3,z752,z167,z6])],[(0,[z1,z2,z789,z3,z4,z6]),(0,[z1,z11,z30,z3,z4,z6]),(0,[z1,z2,z267,z790,z4,z6]),(0,[z1,z2,z10,z791,z4,z6])],[(0,[z1,z2,z231,z3,z4,z6]),(0,[z1,z2,z27,z3,z262,z6]),(0,[z1,z85,z2,z122,z3,z6]),(0,[z1,z2,z284,z27,z3,z6]),(0,[z1,z2,z3,z4,z792,z6]),(0,[z1,z2,z8,z790,z4,z6])]],
   [[(0,[z1,z2,z793,z3,z14,z6])],[(0,[z1,z2,z8,z3,z4,z794]),(0,[z1,z2,z795,z3,z4,z6]),(0,[z1,z2,z3,z796,z4,z6]),(0,[z1,z2,z797,z3,z4,z6]),(0,[z1,z2,z10,z3,z798,z6]),(0,[z1,z2,z799,z3,z4,z6])],[(0,[z1,z2,z140,z3,z105,z6]),(0,[z2,z30,z3,z14,z9,z6]),(0,[z1,z2,z800,z3,z4,z6])],[(0,[z1,z2,z801,z3,z4,z6]),(0,[z1,z2,z802,z27,z3,z4]),(0,[z1,z2,z8,z3,z803,z6]),(0,[z1,z2,z804,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z199])],[(0,[z1,z2,z8,z3,z262,z185]),(0,[z1,z2,z805,z3,z4,z6]),(1,[z2,z8,z3,z4,z718]),(0,[z1,z2,z8,z3,z4,z806])],[(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z26,z27,z3,z9,z6]),(0,[z1,z2,z808,z3,z4,z6])],[(0,[z1,z2,z8,z233,z4,z561]),(0,[z1,z2,z8,z3,z14,z177]),(0,[z1,z2,z3,z4,z466,z6]),(0,[z42,z2,z117,z3,z9,z6]),(0,[z1,z2,z8,z3,z809,z6]),(0,[z1,z2,z8,z3,z810,z6])],[(0,[z1,z2,z811,z3,z4,z6]),(0,[z1,z2,z10,z3,z14,z87]),(0,[z1,z2,z27,z3,z812,z4])],[(0,[z1,z2,z8,z3,z14,z185])],[(0,[z1,z2,z3,z4,z813,z6])],[(0,[z1,z2,z814,z3,z4,z6]),(0,[z1,z44,z2,z169,z3,z4])],[(0,[z1,z2,z3,z4,z5,z554]),(0,[z1,z2,z3,z4,z5,z555])],[(0,[z1,z2,z618,z3,z9,z6])],[(0,[z1,z2,z8,z3,z436,z6]),(0,[z28,z815,z8,z3,z4,z6]),(0,[z214,z29,z10,z3,z4,z6]),(0,[z1,z2,z793,z3,z4,z6]),(0,[z1,z2,z27,z3,z355,z6]),(0,[z1,z2,z3,z4,z6,z816]),(0,[z1,z2,z8,z3,z817,z6])],[(0,[z1,z2,z3,z4,z818,z6]),(0,[z1,z2,z3,z4,z819,z6])],[(0,[z815,z253,z8,z3,z4,z6]),(0,[z1,z2,z820,z3,z4,z6]),(0,[z42,z2,z3,z435,z4,z6]),(0,[z1,z2,z821,z8,z3,z4]),(0,[z1,z92,z10,z3,z4,z23]),(0,[z1,z2,z822,z3,z4,z6])]],
   [[(0,[z2,z8,z134,z823,z4,z6]),(0,[z1,z2,z162,z30,z3,z6]),(0,[z1,z2,z38,z3,z4,z83]),(1,[z1,z2,z8,z3,z824])],[(0,[z1,z2,z3,z392,z5,z6]),(0,[z1,z2,z38,z3,z4,z825]),(0,[z1,z2,z826,z8,z3,z6])],[(0,[z1,z2,z186,z448,z4,z6]),(0,[z1,z2,z8,z3,z4,z827]),(0,[z1,z2,z8,z3,z9,z828]),(0,[z1,z2,z38,z3,z4,z80]),(0,[z1,z2,z235,z790,z4,z6]),(0,[z1,z2,z829,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z177]),(0,[z1,z2,z8,z3,z830,z6]),(0,[z1,z2,z3,z4,z479,z6]),(0,[z1,z2,z146,z30,z3,z6]),(0,[z1,z85,z366,z3,z76,z6]),(0,[z1,z2,z10,z68,z3,z4]),(0,[z1,z2,z123,z221,z4,z6])],[(1,[z815,z8,z3,z4,z6]),(0,[z1,z2,z831,z3,z4,z6]),(0,[z1,z2,z8,z3,z9,z196]),(0,[z1,z2,z10,z3,z355,z6]),(0,[z1,z2,z10,z3,z4,z87]),(0,[z1,z2,z3,z4,z832,z6])],[(0,[z1,z2,z186,z3,z564,z6]),(0,[z1,z2,z8,z3,z4,z185]),(0,[z1,z580,z8,z3,z332,z6])],[(0,[z1,z2,z833,z3,z4,z6]),(0,[z1,z367,z27,z3,z4,z6]),(0,[z1,z2,z3,z834,z4,z6]),(0,[z1,z2,z3,z5,z34,z6])],[(0,[z1,z2,z835,z8,z3,z6]),(0,[z1,z2,z38,z27,z3,z4]),(0,[z1,z2,z492,z3,z4,z6])],[(0,[z106,z2,z175,z3,z4,z6])],[(0,[z1,z2,z8,z448,z9,z6]),(0,[z1,z2,z8,z3,z6,z836]),(0,[z1,z2,z3,z837,z4,z6]),(0,[z1,z2,z838,z3,z4,z6]),(0,[z839,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z840,z6]),(0,[z1,z2,z841,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z842]),(1,[z1,z2,z38,z3,z9]),(0,[z2,z390,z8,z3,z14,z6]),(0,[z1,z2,z843,z3,z4,z6])],[(0,[z569,z253,z8,z3,z4,z6]),(0,[z1,z2,z456,z3,z9,z6]),(1,[z1,z2,z844,z3,z4]),(0,[z1,z2,z303,z3,z9,z6]),(0,[z2,z8,z3,z4,z6,z718]),(0,[z1,z2,z3,z845,z4,z6]),(0,[z1,z2,z363,z3,z43,z6])],[(0,[z1,z2,z162,z110,z27,z3])],[(0,[z1,z2,z8,z3,z14,z561]),(0,[z1,z367,z10,z3,z4,z6]),(0,[z1,z2,z38,z3,z58,z4]),(0,[z1,z2,z10,z3,z4,z302]),(0,[z1,z2,z846,z8,z9,z6]),(0,[z1,z2,z190,z30,z3,z166]),(0,[z1,z2,z3,z4,z847,z6])],[(0,[z1,z2,z8,z3,z82,z6]),(0,[z1,z2,z848,z3,z4,z6]),(0,[z1,z2,z8,z3,z849,z6]),(0,[z1,z2,z8,z3,z850,z6]),(0,[z1,z2,z303,z3,z34,z6])],[(0,[z1,z2,z851,z3,z4,z6]),(0,[z1,z2,z3,z734,z4,z6]),(0,[z1,z85,z144,z8,z3,z6])]],
   [[(0,[z1,z2,z110,z8,z3,z4]),(0,[z1,z169,z11,z3,z4,z6]),(0,[z852,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z853])],[(0,[z1,z2,z3,z4,z6,z854]),(0,[z1,z2,z855,z3,z4,z6])],[(0,[z489,z2,z175,z3,z4,z6]),(0,[z1,z2,z423,z3,z14,z6])],[(0,[z1,z2,z194,z3,z9,z6]),(0,[z402,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z856,z6]),(0,[z1,z2,z10,z492,z3,z4]),(0,[z1,z2,z8,z3,z857,z6])],[(0,[z2,z815,z8,z3,z4,z6]),(0,[z1,z2,z235,z321,z4,z6]),(0,[z1,z2,z27,z3,z4,z858])],[(0,[z1,z2,z3,z859,z4,z6]),(0,[z1,z2,z414,z3,z9,z6]),(0,[z1,z2,z73,z38,z3,z4]),(0,[z1,z2,z8,z860,z4,z6]),(0,[z1,z2,z8,z3,z861,z6])],[(0,[z328,z2,z117,z3,z4,z6]),(0,[z1,z307,z27,z3,z4,z6]),(0,[z1,z367,z8,z3,z4,z394]),(0,[z1,z2,z862,z3,z4,z6]),(0,[z1,z2,z863,z8,z3,z6]),(0,[z1,z2,z864,z3,z4,z6]),(0,[z1,z92,z320,z3,z4,z23]),(0,[z1,z2,z8,z3,z4,z865])],[(0,[z1,z2,z27,z3,z4,z866]),(1,[z1,z2,z162,z38,z3])],[(0,[z2,z867,z8,z3,z4,z6]),(0,[z161,z2,z117,z3,z4,z6]),(0,[z1,z2,z3,z14,z745,z6]),(0,[z1,z30,z27,z3,z4,z6]),(0,[z1,z170,z27,z3,z4,z6]),(0,[z1,z2,z522,z114,z4,z6]),(0,[z1,z2,z8,z3,z868,z6])],[(0,[z1,z2,z3,z43,z249,z6]),(0,[z584,z2,z8,z3,z9,z6]),(0,[z1,z130,z27,z3,z62,z6]),(0,[z1,z2,z162,z10,z3,z6])],[(0,[z1,z2,z8,z3,z4,z561]),(0,[z1,z2,z8,z3,z4,z869]),(0,[z118,z1,z8,z39,z14,z6]),(0,[z1,z2,z298,z27,z3,z6]),(0,[z1,z2,z30,z3,z4,z870]),(0,[z1,z2,z871,z3,z4,z6])],[(0,[z1,z2,z360,z3,z37,z6]),(0,[z1,z307,z8,z3,z4,z185]),(0,[z1,z2,z8,z272,z178,z6]),(0,[z1,z2,z27,z3,z6,z49]),(0,[z1,z2,z3,z4,z380,z84]),(0,[z1,z2,z3,z872,z4,z6])],[(0,[z1,z2,z146,z10,z3,z6])],[(0,[z1,z2,z27,z3,z4,z394]),(0,[z1,z2,z10,z3,z14,z5]),(0,[z1,z2,z873,z3,z4,z6])],[(0,[z42,z2,z117,z3,z4,z133]),(0,[z1,z337,z30,z3,z4,z6]),(0,[z118,z1,z39,z4,z5,z6])],[(0,[z1,z2,z423,z3,z4,z6]),(0,[z1,z2,z8,z3,z105,z196]),(0,[z1,z2,z30,z3,z874,z6])]],
   [[(0,[z1,z2,z3,z105,z5,z6]),(0,[z1,z2,z38,z3,z9,z6]),(0,[z1,z85,z8,z3,z529,z6]),(0,[z1,z2,z27,z3,z4,z875]),(0,[z1,z130,z10,z3,z62,z6])],[(0,[z1,z2,z8,z3,z4,z876]),(0,[z1,z2,z3,z4,z5,z133]),(0,[z32,z1,z2,z38,z3,z4])],[(0,[z1,z2,z30,z3,z392,z6])],[(0,[z1,z2,z8,z3,z877,z6]),(0,[z1,z2,z8,z98,z271,z6]),(0,[z1,z27,z3,z368,z4,z6])],[(0,[z1,z307,z8,z3,z82,z6]),(0,[z1,z2,z10,z3,z4,z394]),(0,[z1,z2,z878,z3,z4,z6]),(0,[z1,z2,z338,z3,z9,z6]),(0,[z2,z8,z3,z9,z685,z6]),(0,[z1,z374,z8,z3,z76,z6]),(0,[z1,z2,z146,z303,z3,z6]),(0,[z1,z727,z10,z3,z4,z6])],[(0,[z1,z2,z169,z3,z14,z6]),(0,[z1,z2,z879,z27,z3,z6])],[(0,[z1,z2,z3,z14,z768,z6]),(0,[z1,z2,z880,z3,z4,z6]),(0,[z1,z2,z881,z3,z4,z6])],[(0,[z1,z2,z8,z882,z4,z6]),(0,[z1,z2,z3,z4,z883,z6]),(0,[z7,z2,z8,z134,z14,z6]),(0,[z1,z2,z122,z3,z269,z6]),(0,[z1,z2,z10,z3,z14,z46]),(0,[z1,z2,z884,z3,z4,z6]),(0,[z1,z885,z8,z3,z4,z6])],[(0,[z2,z117,z867,z3,z4,z6]),(0,[z1,z2,z886,z8,z3,z6]),(0,[z1,z2,z3,z4,z887,z6]),(0,[z1,z2,z888,z3,z4,z6]),(0,[z1,z2,z8,z889,z3,z6]),(0,[z1,z92,z3,z4,z479,z6]),(0,[z1,z2,z890,z3,z4,z6])],[(0,[z118,z1,z286,z39,z4,z6]),(0,[z1,z92,z11,z8,z3,z4])],[(0,[z32,z1,z30,z3,z9,z6]),(0,[z1,z2,z8,z3,z6,z891]),(0,[z1,z2,z3,z4,z6,z892]),(0,[z1,z171,z30,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z5])],[(0,[z1,z2,z8,z3,z4,z893]),(0,[z1,z2,z30,z3,z4,z196]),(0,[z1,z2,z107,z38,z3,z4]),(0,[z1,z2,z10,z3,z739,z6])],[(0,[z1,z2,z3,z894,z9,z6]),(0,[z895,z1,z2,z38,z3,z4]),(0,[z1,z2,z896,z3,z4,z6]),(0,[z1,z2,z349,z10,z3,z4]),(0,[z1,z2,z771,z11,z3,z6])],[(0,[z1,z2,z897,z3,z4,z6]),(0,[z42,z1,z2,z284,z3,z6]),(0,[z1,z2,z3,z604,z9,z6]),(0,[z165,z2,z3,z4,z5,z87]),(0,[z161,z2,z10,z3,z4,z36]),(0,[z1,z2,z8,z3,z898,z4]),(0,[z1,z2,z195,z8,z83,z6])],[(0,[z1,z2,z10,z3,z37,z6]),(0,[z1,z2,z38,z38,z3,z4]),(0,[z1,z92,z2,z169,z3,z4])],[(0,[z1,z44,z2,z822,z3,z4])]],
   [[(0,[z1,z2,z30,z448,z4,z6]),(0,[z106,z2,z175,z3,z249,z6]),(0,[z1,z899,z8,z3,z4,z6]),(0,[z151,z2,z102,z3,z4,z6]),(0,[z1,z2,z140,z3,z459,z6])],[(0,[z1,z2,z900,z3,z4,z6]),(0,[z1,z2,z3,z901,z4,z6]),(0,[z1,z198,z8,z3,z529,z6]),(0,[z1,z2,z38,z3,z4,z166]),(0,[z1,z2,z902,z3,z4,z6])],[(0,[z1,z903,z8,z3,z4,z6]),(0,[z1,z2,z169,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z184]),(0,[z1,z2,z419,z3,z459,z6]),(0,[z1,z2,z73,z8,z4,z749])],[(0,[z1,z2,z30,z3,z564,z6]),(0,[z1,z2,z904,z8,z3,z6]),(0,[z1,z2,z8,z3,z905,z6]),(0,[z1,z26,z27,z3,z4,z6])],[(0,[z42,z2,z117,z3,z4,z6]),(0,[z7,z2,z8,z134,z4,z6]),(0,[z1,z2,z524,z3,z314,z6]),(0,[z1,z2,z906,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z46])],[(0,[z28,z1,z2,z38,z3,z4]),(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z2,z3,z4,z908,z6]),(0,[z1,z226,z169,z3,z4,z6])],[(0,[z214,z29,z8,z3,z436,z6]),(0,[z288,z2,z8,z3,z4,z36]),(0,[z1,z2,z267,z364,z4,z6]),(0,[z1,z2,z909,z3,z4,z6])],[(0,[z1,z2,z910,z3,z4,z6]),(0,[z1,z44,z2,z38,z3,z4])],[(0,[z1,z2,z565,z3,z14,z6]),(0,[z1,z2,z408,z3,z9,z6]),(0,[z1,z2,z122,z3,z43,z6]),(0,[z1,z2,z911,z3,z4,z6])],[(0,[z1,z2,z912,z3,z4,z6]),(0,[z1,z2,z8,z3,z913,z6]),(0,[z214,z29,z27,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z914]),(0,[z1,z2,z30,z98,z178,z6]),(0,[z1,z2,z3,z4,z6,z915]),(0,[z1,z2,z916,z3,z4,z6])],[(0,[z1,z2,z3,z917,z4,z6]),(0,[z1,z2,z918,z3,z4,z6]),(0,[z1,z2,z919,z3,z4,z6]),(0,[z1,z2,z920,z3,z4,z6]),(0,[z1,z2,z921,z8,z3,z6]),(0,[z1,z361,z30,z3,z4,z6]),(1,[z1,z8,z922,z4,z6])],[(0,[z28,z253,z186,z3,z4,z6]),(0,[z1,z2,z8,z3,z6,z923]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z1,z92,z27,z3,z4,z23]),(0,[z1,z2,z925,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z926]),(0,[z2,z8,z3,z435,z14,z6])],[(0,[z1,z2,z8,z927,z3,z6]),(0,[z1,z2,z38,z175,z3,z4]),(0,[z1,z2,z10,z3,z292,z6]),(0,[z1,z2,z928,z3,z4,z6]),(0,[z1,z2,z492,z3,z14,z6]),(0,[z1,z2,z8,z3,z929,z6])],[(0,[z1,z2,z930,z3,z4,z6]),(0,[z106,z2,z175,z3,z14,z6]),(0,[z1,z2,z8,z3,z931,z6]),(0,[z1,z2,z38,z27,z3,z14]),(0,[z1,z2,z8,z3,z932,z6]),(0,[z1,z2,z73,z10,z4,z50]),(0,[z1,z2,z933,z3,z4,z6])],[(0,[z1,z2,z8,z3,z139,z6]),(0,[z1,z483,z2,z10,z3,z4])]],
   [[(0,[z1,z2,z8,z3,z4,z828]),(0,[z1,z2,z545,z3,z519,z6]),(0,[z1,z2,z418,z4,z193,z6])],[(0,[z1,z2,z934,z3,z139,z6]),(0,[z1,z2,z935,z10,z3,z6])],[(0,[z28,z253,z8,z3,z9,z6]),(0,[z2,z10,z3,z14,z9,z6]),(0,[z210,z2,z549,z3,z4,z6]),(0,[z1,z2,z8,z3,z936,z6])],[(0,[z1,z2,z3,z9,z937,z6]),(0,[z2,z8,z3,z9,z6,z57]),(0,[z1,z2,z8,z3,z4,z716])],[(0,[z1,z2,z8,z922,z4,z6]),(0,[z1,z2,z3,z4,z5,z626]),(0,[z1,z2,z10,z3,z4,z127])],[(0,[z1,z2,z565,z3,z4,z6]),(0,[z1,z2,z3,z4,z938,z6]),(0,[z1,z2,z3,z14,z479,z6])],[(0,[z1,z2,z939,z8,z4,z6]),(0,[z1,z2,z695,z114,z4,z6]),(0,[z1,z2,z940,z3,z4,z6]),(0,[z1,z2,z8,z941,z3,z6]),(0,[z13,z2,z3,z4,z5,z36]),(0,[z1,z2,z2,z38,z3,z4]),(0,[z1,z2,z8,z868,z83,z6])],[(0,[z1,z2,z360,z3,z4,z177]),(0,[z1,z2,z110,z8,z3,z14])],[(0,[z1,z2,z3,z4,z380,z6]),(0,[z1,z27,z3,z412,z4,z6])],[(0,[z2,z8,z3,z9,z74,z6]),(0,[z1,z2,z303,z3,z4,z6]),(0,[z1,z2,z190,z8,z3,z824])],[(0,[z1,z2,z30,z3,z251,z6]),(0,[z1,z2,z8,z3,z4,z942])],[(0,[z1,z2,z943,z8,z3,z6]),(0,[z1,z2,z8,z3,z684,z574]),(0,[z1,z2,z3,z944,z4,z6]),(0,[z1,z2,z27,z3,z945,z6]),(0,[z1,z2,z162,z38,z3,z4]),(0,[z1,z2,z142,z3,z4,z380]),(0,[z1,z2,z142,z3,z4,z716]),(0,[z1,z2,z946,z3,z4,z6])],[],[(0,[z281,z1,z8,z39,z4,z6]),(0,[z1,z2,z8,z3,z947,z6]),(0,[z1,z2,z725,z27,z3,z6]),(0,[z1,z304,z30,z3,z4,z6])],[(0,[z1,z367,z8,z3,z4,z185]),(0,[z1,z948,z8,z3,z4,z6]),(0,[z1,z30,z27,z3,z14,z6]),(0,[z1,z2,z3,z14,z174,z6]),(0,[z1,z2,z225,z3,z526,z6]),(0,[z1,z2,z111,z30,z3,z6])],[(0,[z1,z2,z8,z3,z949,z6]),(0,[z1,z2,z950,z38,z3,z4])]],
   [[(0,[z1,z2,z951,z3,z4,z6]),(0,[z1,z2,z284,z30,z3,z6]),(0,[z1,z2,z3,z4,z952,z6])],[(0,[z1,z2,z953,z3,z4,z6]),(0,[z1,z2,z194,z3,z4,z6]),(0,[z1,z2,z3,z9,z954,z6]),(0,[z1,z628,z27,z3,z4,z6])],[(0,[z2,z8,z3,z14,z9,z6]),(0,[z1,z2,z30,z3,z308,z6]),(0,[z1,z2,z38,z254,z3,z4]),(0,[z1,z2,z8,z3,z955,z6]),(0,[z1,z92,z10,z11,z3,z4]),(0,[z1,z2,z956,z8,z3,z6])],[(0,[z1,z2,z957,z3,z9,z6]),(0,[z1,z2,z958,z8,z3,z6]),(0,[z1,z2,z873,z3,z14,z6]),(0,[z1,z2,z959,z3,z4,z6]),(0,[z1,z2,z3,z960,z5,z6])],[(0,[z1,z2,z10,z3,z436,z6]),(0,[z165,z1,z2,z38,z3,z4]),(0,[z1,z2,z3,z4,z961,z6])],[(0,[z1,z8,z3,z9,z6,z962]),(0,[z1,z2,z3,z9,z6,z963]),(0,[z1,z2,z3,z4,z434,z6]),(0,[z1,z45,z414,z33,z4,z6]),(0,[z1,z2,z964,z3,z4,z6])],[(0,[z138,z1,z2,z38,z3,z4]),(0,[z1,z2,z8,z3,z4,z718])],[(0,[z1,z367,z8,z3,z82,z6]),(0,[z1,z2,z965,z3,z4,z6]),(0,[z1,z2,z966,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z380]),(0,[z1,z2,z967,z3,z4,z6])],[(0,[z1,z2,z968,z8,z3,z6]),(0,[z1,z2,z969,z3,z14,z6])],[(0,[z1,z29,z11,z3,z4,z6]),(0,[z1,z2,z970,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z176]),(0,[z971,z2,z8,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z274]),(0,[z1,z2,z3,z109,z5,z80])],[(0,[z1,z2,z10,z3,z4,z177]),(0,[z2,z8,z3,z480,z14,z6])],[(0,[z1,z2,z3,z139,z5,z6]),(0,[z0,z1,z2,z38,z3,z4]),(0,[z1,z2,z3,z4,z6,z972])],[(0,[z1,z2,z10,z3,z4,z185]),(0,[z1,z2,z8,z3,z973,z6])],[(0,[z1,z2,z974,z3,z4,z6]),(0,[z1,z2,z3,z436,z5,z6]),(0,[z1,z2,z10,z3,z4,z188]),(1,[z2,z867,z3,z4,z6]),(0,[z1,z2,z8,z3,z975,z6])],[(0,[z1,z2,z360,z3,z4,z561]),(0,[z1,z2,z3,z4,z818,z394]),(0,[z1,z2,z123,z235,z9,z6]),(0,[z1,z2,z8,z3,z4,z824])],[(0,[z2,z3,z14,z9,z5,z6]),(0,[z1,z2,z110,z27,z3,z9]),(0,[z1,z2,z68,z3,z9,z6]),(0,[z1,z2,z162,z3,z174,z6])]],
   [[(0,[z1,z2,z30,z3,z61,z6]),(0,[z1,z2,z10,z3,z14,z36]),(0,[z1,z2,z976,z3,z4,z6])],[(0,[z1,z2,z8,z977,z4,z6]),(0,[z1,z2,z978,z8,z3,z4]),(0,[z1,z2,z27,z3,z464,z6]),(0,[z118,z1,z352,z39,z4,z6]),(0,[z1,z8,z3,z726,z76,z6])],[(0,[z1,z2,z979,z3,z4,z6]),(0,[z1,z2,z182,z8,z240,z6]),(0,[z1,z130,z2,z122,z3,z6]),(0,[z1,z2,z10,z3,z4,z548]),(0,[z1,z2,z30,z3,z526,z6]),(0,[z1,z2,z338,z3,z4,z6]),(0,[z1,z2,z38,z3,z4,z341]),(0,[z1,z85,z2,z315,z3,z6])],[],[(0,[z1,z2,z186,z3,z9,z6]),(0,[z1,z2,z980,z3,z4,z6]),(0,[z1,z2,z765,z3,z4,z6]),(0,[z1,z2,z763,z27,z4,z6]),(0,[z1,z2,z110,z284,z27,z3]),(0,[z1,z2,z981,z3,z4,z6])],[(0,[z1,z2,z10,z3,z82,z6]),(0,[z1,z2,z969,z3,z4,z6]),(0,[z1,z2,z982,z3,z4,z6]),(0,[z1,z26,z284,z27,z3,z6]),(0,[z1,z2,z30,z488,z3,z6])],[(0,[z1,z2,z140,z3,z289,z6]),(0,[z1,z2,z38,z284,z3,z4])],[(0,[z1,z2,z983,z3,z4,z6]),(0,[z1,z2,z8,z3,z752,z6])],[(0,[z1,z2,z10,z3,z464,z6])],[(0,[z1,z2,z8,z233,z564,z6]),(0,[z28,z253,z30,z3,z4,z6]),(0,[z1,z26,z27,z3,z14,z6]),(0,[z1,z2,z3,z250,z167,z6]),(0,[z1,z2,z190,z10,z3,z166])],[(0,[z1,z2,z27,z3,z37,z6]),(0,[z1,z2,z8,z984,z3,z6]),(0,[z1,z2,z30,z3,z105,z6]),(0,[z1,z2,z3,z4,z6,z985]),(0,[z1,z2,z986,z8,z3,z6]),(0,[z1,z2,z3,z894,z4,z6]),(0,[z1,z2,z3,z4,z987,z6])],[(0,[z1,z2,z8,z3,z105,z133]),(0,[z1,z2,z8,z3,z988,z6]),(0,[z1,z2,z3,z989,z4,z6]),(0,[z1,z92,z2,z38,z3,z4]),(0,[z990,z2,z8,z3,z4,z6]),(0,[z1,z2,z3,z604,z4,z6])],[(0,[z138,z2,z194,z58,z4,z6])],[(0,[z1,z2,z8,z3,z37,z177]),(0,[z1,z2,z991,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z36]),(0,[z1,z27,z442,z3,z4,z6])],[(0,[z1,z2,z8,z3,z82,z394]),(0,[z1,z2,z10,z3,z4,z216])],[(0,[z500,z2,z8,z3,z4,z87]),(0,[z2,z8,z3,z4,z36,z718])]],
   [[(0,[z1,z2,z992,z3,z4,z6]),(0,[z1,z2,z993,z3,z4,z6]),(0,[z1,z2,z618,z3,z14,z6]),(0,[z1,z2,z994,z3,z4,z6]),(0,[z1,z2,z73,z8,z49,z50]),(0,[z1,z2,z995,z8,z3,z6])],[(0,[z1,z2,z8,z3,z996,z6]),(0,[z1,z2,z997,z3,z4,z6])],[(0,[z1,z2,z169,z3,z4,z87]),(0,[z1,z2,z3,z998,z4,z6]),(0,[z1,z2,z999,z3,z4,z6]),(0,[z1,z2,z8,z98,z638,z6]),(0,[z1,z2,z1000,z3,z4,z6])],[(0,[z1,z2,z3,z4,z202,z196]),(1,[z1,z2,z38,z3,z14])],[(0,[z1,z2,z38,z3,z4,z84]),(0,[z1,z2,z8,z3,z4,z870])],[(0,[z1,z2,z8,z3,z1001,z6]),(0,[z1,z2,z1002,z3,z4,z6]),(0,[z1,z2,z123,z652,z4,z6]),(0,[z1,z2,z1003,z3,z4,z6])],[(0,[z1,z2,z1004,z3,z9,z6]),(0,[z1,z2,z1005,z488,z3,z6])],[(0,[z1,z2,z8,z3,z1006,z6]),(0,[z1,z2,z30,z3,z4,z133]),(0,[z210,z1,z2,z38,z3,z4]),(0,[z118,z1,z27,z39,z4,z6]),(0,[z1,z2,z1007,z3,z4,z6]),(0,[z1,z2,z1008,z8,z3,z6])],[(0,[z214,z29,z8,z3,z139,z6]),(0,[z1,z2,z8,z3,z14,z196]),(0,[z13,z2,z8,z3,z308,z36]),(0,[z1,z2,z1009,z3,z4,z6])],[(0,[z1,z2,z8,z3,z874,z6]),(0,[z1,z2,z27,z3,z292,z6]),(0,[z1,z2,z8,z3,z526,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z1010]),(0,[z1,z2,z27,z772,z3,z6]),(0,[z1,z2,z3,z4,z5,z493]),(0,[z1,z2,z107,z3,z56,z6])],[(0,[z1,z2,z1011,z3,z4,z6]),(0,[z1,z2,z1012,z8,z3,z6]),(0,[z416,z2,z8,z3,z9,z6]),(0,[z1,z2,z3,z14,z466,z6]),(0,[z1,z2,z1013,z3,z4,z6]),(0,[z1,z2,z38,z110,z3,z4]),(0,[z64,z2,z3,z4,z202,z6])],[(0,[z1,z2,z8,z3,z392,z6]),(0,[z1,z2,z1014,z3,z4,z6])],[(0,[z1,z2,z8,z448,z14,z6]),(0,[z1,z2,z618,z3,z4,z6]),(0,[z1,z2,z1015,z3,z4,z6]),(1,[z2,z8,z3,z736,z6]),(0,[z1,z2,z1016,z3,z9,z6]),(0,[z1,z2,z1017,z8,z3,z6]),(0,[z1,z26,z38,z27,z3,z4])],[(0,[z1,z2,z1018,z3,z4,z6]),(0,[z1,z2,z225,z3,z9,z6]),(0,[z118,z1,z10,z39,z4,z6]),(0,[z1,z2,z10,z3,z4,z242])],[(0,[z1,z2,z456,z3,z14,z6]),(0,[z2,z867,z175,z3,z4,z6]),(0,[z1,z2,z1019,z3,z4,z6]),(0,[z1,z2,z3,z9,z1020,z6]),(0,[z1,z2,z1021,z3,z9,z6]),(0,[z1,z2,z73,z8,z9,z50]),(0,[z1,z2,z303,z3,z14,z6]),(0,[z1,z2,z91,z8,z3,z541]),(1,[z1,z2,z38,z3,z4]),(0,[z1,z2,z3,z4,z1022,z6])]],
   [[(0,[z28,z253,z8,z3,z4,z6]),(0,[z1,z2,z140,z3,z249,z6]),(0,[z1,z2,z27,z3,z786,z6]),(0,[z1,z2,z821,z27,z3,z4])],[(0,[z1,z2,z8,z3,z1023,z6]),(0,[z1,z2,z90,z3,z9,z6]),(0,[z1,z2,z1024,z3,z4,z6]),(0,[z1,z2,z1025,z3,z4,z6]),(0,[z1,z2,z225,z3,z308,z6]),(0,[z1,z2,z276,z652,z4,z6])],[],[(0,[z1,z29,z8,z233,z4,z6]),(0,[z1,z2,z8,z3,z1026,z6]),(0,[z1,z116,z27,z3,z4,z6]),(0,[z1,z2,z194,z3,z262,z6]),(0,[z1,z1027,z8,z3,z9,z6]),(0,[z1,z2,z235,z4,z6,z430]),(0,[z1,z2,z111,z208,z3,z6])],[(0,[z1,z2,z267,z3,z4,z196]),(0,[z1,z2,z1028,z3,z4,z6]),(0,[z1,z2,z3,z4,z1029,z6])],[(0,[z1,z2,z8,z3,z4,z196]),(0,[z1,z2,z110,z27,z3,z14]),(0,[z1,z2,z1030,z8,z3,z6]),(0,[z1,z27,z3,z4,z478,z6]),(0,[z1,z2,z8,z3,z1031,z6]),(0,[z1,z2,z10,z3,z4,z681]),(0,[z1,z92,z492,z3,z4,z23]),(0,[z1,z2,z10,z3,z4,z648]),(0,[z1,z2,z10,z455,z3,z4])],[],[(0,[z1,z2,z194,z3,z14,z6]),(0,[z1,z2,z8,z3,z4,z1032]),(0,[z1,z2,z935,z11,z3,z6])],[(0,[z2,z8,z3,z14,z736,z6]),(0,[z13,z2,z8,z3,z526,z36]),(0,[z1,z596,z27,z3,z4,z6]),(0,[z1,z2,z140,z366,z3,z6]),(0,[z1,z2,z3,z4,z6,z1033])],[(0,[z1,z2,z1034,z3,z4,z6]),(0,[z1,z2,z1035,z565,z3,z6]),(0,[z1,z2,z3,z4,z1036,z6]),(0,[z1,z2,z8,z3,z247,z80]),(0,[z1,z2,z414,z3,z14,z6]),(0,[z1,z2,z1037,z3,z4,z6]),(0,[z1,z2,z30,z3,z4,z1038]),(0,[z1,z2,z3,z1039,z4,z6])],[(0,[z1,z2,z8,z448,z4,z6]),(0,[z1,z2,z1040,z3,z4,z6]),(0,[z1,z2,z3,z14,z380,z6]),(0,[z1,z2,z1041,z3,z4,z6])],[(0,[z7,z2,z10,z134,z4,z6]),(0,[z1,z27,z3,z4,z479,z6]),(0,[z118,z1,z8,z488,z39,z6]),(0,[z1,z2,z1042,z3,z4,z6])],[(0,[z1,z2,z456,z3,z4,z6]),(0,[z1,z2,z1043,z38,z3,z4])],[(0,[z1,z2,z8,z3,z564,z6]),(0,[z520,z1,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z1044,z6]),(0,[z1,z2,z122,z3,z167,z6]),(0,[z1,z2,z8,z3,z1045,z6])],[(0,[z1,z2,z253,z38,z3,z4]),(0,[z1,z2,z846,z8,z4,z6]),(0,[z1,z2,z3,z4,z6,z1046]),(0,[z1,z2,z1047,z8,z3,z6])],[(0,[z1,z45,z30,z33,z4,z6])]],
   [[(0,[z1,z2,z8,z3,z1048,z6]),(0,[z1,z2,z27,z3,z436,z6]),(0,[z1,z307,z3,z4,z5,z6]),(0,[z1,z2,z3,z9,z330,z6]),(0,[z1,z2,z8,z1049,z4,z6]),(0,[z1,z92,z3,z4,z434,z23])],[(0,[z1,z2,z957,z3,z4,z6]),(0,[z1,z2,z110,z27,z3,z4]),(0,[z1,z2,z3,z4,z6,z1050])],[(0,[z1,z1051,z8,z3,z4,z6]),(0,[z1,z2,z30,z3,z9,z6]),(0,[z1,z2,z400,z8,z393,z6]),(0,[z1,z92,z44,z10,z3,z4]),(0,[z1,z2,z123,z790,z4,z6])],[(0,[z1,z2,z8,z3,z9,z133]),(0,[z1,z2,z107,z3,z237,z6]),(0,[z1,z2,z8,z98,z178,z6])],[(0,[z1,z2,z8,z3,z1052,z6]),(0,[z1,z2,z1053,z3,z9,z6]),(0,[z1,z2,z38,z3,z14,z6]),(0,[z1,z44,z30,z3,z4,z84])],[(0,[z1,z2,z3,z1054,z9,z6]),(0,[z1,z2,z8,z632,z4,z150]),(0,[z1,z2,z30,z3,z34,z6]),(0,[z1,z2,z30,z3,z1055,z6]),(0,[z1,z2,z1056,z3,z4,z6])],[(0,[z1,z2,z3,z564,z5,z6]),(0,[z1,z2,z27,z3,z4,z177]),(0,[z1,z2,z10,z3,z139,z6]),(0,[z2,z3,z289,z14,z9,z6]),(0,[z1,z2,z414,z3,z4,z6]),(0,[z1,z2,z1057,z3,z4,z6]),(0,[z1,z2,z38,z140,z3,z4]),(0,[z1,z130,z8,z3,z610,z6])],[(0,[z7,z2,z8,z823,z4,z6]),(0,[z1,z2,z863,z27,z3,z6]),(0,[z1,z2,z3,z14,z434,z6]),(0,[z1,z2,z38,z3,z451,z4]),(0,[z1,z2,z1058,z3,z4,z6]),(0,[z1,z2,z1059,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1060])],[(0,[z1,z2,z1061,z8,z3,z4]),(0,[z1,z2,z235,z3,z4,z196]),(0,[z1,z2,z27,z3,z4,z185]),(0,[z138,z2,z618,z58,z4,z6]),(0,[z1,z2,z338,z3,z14,z6]),(0,[z1,z2,z1062,z3,z4,z6]),(0,[z1,z2,z38,z123,z3,z4])],[(0,[z1,z2,z10,z3,z4,z678]),(0,[z1,z2,z3,z464,z5,z6])],[(0,[z1,z2,z8,z3,z4,z1063]),(0,[z1,z2,z10,z3,z4,z716]),(0,[z1,z2,z8,z178,z868,z6])],[(0,[z1,z2,z8,z3,z4,z1064]),(0,[z1,z44,z2,z10,z3,z9]),(0,[z1,z130,z8,z3,z155,z6])],[(0,[z13,z2,z30,z3,z4,z36]),(0,[z1,z2,z123,z235,z4,z6]),(0,[z1,z2,z3,z4,z1065,z6]),(1,[z1,z2,z8,z4,z749])],[(0,[z2,z122,z3,z14,z9,z6]),(0,[z1,z2,z3,z526,z5,z6]),(0,[z1,z2,z27,z3,z4,z842]),(0,[z1,z2,z8,z3,z1066,z6]),(0,[z1,z2,z3,z4,z1067,z6]),(0,[z1,z2,z8,z3,z1068,z6])],[(0,[z1,z2,z267,z114,z9,z6]),(0,[z1,z2,z11,z3,z9,z6]),(0,[z32,z1,z30,z3,z14,z6]),(0,[z1,z2,z38,z235,z3,z4])],[(0,[z28,z253,z8,z233,z4,z6]),(0,[z165,z2,z8,z3,z9,z87]),(0,[z1,z2,z3,z5,z6,z49])]],
   [[(0,[z1,z540,z8,z33,z4,z6]),(0,[z1,z2,z3,z4,z6,z1069]),(0,[z1,z2,z3,z4,z6,z406]),(0,[z1,z2,z3,z4,z1070,z6])],[(0,[z1,z2,z27,z3,z82,z6]),(0,[z1,z2,z3,z604,z14,z6]),(0,[z1,z2,z1071,z3,z4,z6]),(0,[z1,z2,z38,z3,z4,z6]),(0,[z1,z2,z3,z4,z380,z23])],[(0,[z1,z2,z186,z3,z4,z6]),(0,[z106,z2,z682,z3,z4,z6]),(0,[z2,z567,z8,z3,z14,z6]),(0,[z1,z2,z38,z3,z62,z4]),(0,[z1,z2,z3,z1072,z4,z6]),(0,[z1,z2,z8,z3,z6,z1073]),(0,[z1,z2,z195,z8,z868,z6])],[(0,[z1,z181,z27,z3,z4,z6]),(0,[z1,z2,z3,z174,z6,z720]),(0,[z1,z2,z1074,z3,z4,z6]),(0,[z1,z2,z8,z3,z80,z81])],[(0,[z1,z2,z8,z3,z1075,z6]),(0,[z1,z2,z8,z3,z251,z6]),(0,[z1,z2,z488,z3,z5,z6])],[(0,[z1,z2,z1076,z3,z4,z6]),(1,[z1,z2,z863,z3,z6])],[(0,[z1,z2,z8,z3,z82,z185]),(0,[z1,z2,z8,z3,z960,z6])],[(0,[z1,z2,z3,z61,z5,z6]),(0,[z1,z2,z3,z9,z1077,z6]),(0,[z2,z689,z8,z3,z9,z6])],[(0,[z1,z2,z1078,z3,z4,z6]),(0,[z1,z2,z8,z3,z1079,z6]),(0,[z1,z2,z771,z8,z3,z6])],[(0,[z1,z2,z1080,z3,z4,z6]),(0,[z1,z815,z8,z3,z4,z6]),(0,[z1,z2,z1081,z3,z61,z6]),(0,[z1,z2,z1082,z3,z4,z6])],[(0,[z1,z2,z8,z3,z1083,z6]),(0,[z1,z2,z1084,z8,z3,z6]),(0,[z1,z490,z30,z3,z4,z6]),(0,[z1,z307,z194,z3,z4,z6]),(0,[z1,z2,z3,z4,z987,z87])],[(0,[z1,z2,z8,z3,z1085,z6]),(0,[z1,z45,z8,z33,z9,z6]),(0,[z1,z2,z125,z3,z9,z6]),(0,[z32,z1,z30,z3,z4,z6]),(0,[z1,z2,z38,z30,z3,z4]),(0,[z1,z2,z146,z3,z434,z6])],[(0,[z1,z2,z1086,z3,z4,z6]),(0,[z1,z2,z1087,z3,z4,z6]),(0,[z1,z2,z107,z3,z289,z6]),(0,[z1,z2,z8,z3,z308,z6]),(0,[z1,z2,z408,z3,z14,z6]),(0,[z1,z27,z3,z4,z6,z523]),(0,[z1,z2,z3,z4,z1088,z6]),(0,[z1,z130,z8,z411,z3,z6]),(0,[z1,z586,z11,z3,z4,z6]),(0,[z1,z2,z315,z98,z178,z6]),(0,[z1,z2,z8,z3,z6,z824])],[(0,[z1,z2,z27,z3,z4,z561]),(0,[z1,z2,z3,z1089,z9,z6]),(0,[z1,z2,z10,z3,z4,z987]),(0,[z1,z2,z30,z3,z109,z80]),(0,[z1,z2,z1090,z3,z4,z6])],[(0,[z1,z1091,z8,z3,z4,z6]),(0,[z1,z2,z1092,z3,z4,z6]),(0,[z1,z2,z38,z33,z3,z4]),(0,[z1,z2,z195,z27,z83,z6])],[(0,[z569,z2,z8,z58,z4,z6]),(0,[z1,z2,z323,z8,z3,z166]),(0,[z1,z2,z3,z491,z4,z5]),(0,[z1,z2,z3,z4,z6,z1093])]],
   [[(0,[z1,z2,z10,z3,z4,z703])],[(0,[z106,z2,z340,z3,z4,z6]),(0,[z1,z2,z1094,z3,z4,z6]),(0,[z1,z2,z8,z3,z1095,z6])],[(0,[z1,z8,z3,z922,z4,z6])],[(0,[z214,z29,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z6,z720]),(0,[z1,z2,z1096,z3,z4,z6])],[(0,[z1,z2,z10,z3,z4,z561]),(0,[z1,z2,z904,z27,z3,z6]),(0,[z1,z2,z1004,z3,z4,z6])],[(0,[z1,z2,z208,z3,z9,z6]),(0,[z1,z2,z1097,z3,z4,z6]),(0,[z1,z92,z3,z4,z5,z23])],[(0,[z28,z253,z8,z3,z14,z6]),(0,[z1,z2,z1098,z3,z4,z6]),(0,[z1,z2,z267,z38,z3,z4])],[],[(0,[z13,z2,z8,z3,z9,z36]),(0,[z1099,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z1100,z3,z6]),(0,[z1,z2,z8,z3,z1101,z6])],[(0,[z1,z2,z8,z3,z1102,z6]),(0,[z1,z2,z408,z3,z4,z6]),(0,[z1,z2,z1103,z3,z4,z6])],[(0,[z1,z2,z8,z3,z61,z6]),(0,[z1,z8,z1104,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z1105]),(0,[z1,z2,z1016,z3,z4,z6]),(0,[z1,z2,z234,z3,z43,z6]),(0,[z1,z2,z1106,z3,z4,z6]),(0,[z1,z2,z921,z27,z3,z6])],[(0,[z1,z2,z3,z14,z5,z6]),(0,[z141,z2,z30,z3,z9,z6]),(0,[z1,z26,z2,z38,z3,z4]),(0,[z1,z2,z1107,z3,z4,z6])],[(0,[z42,z1,z2,z38,z3,z4]),(0,[z1,z8,z3,z9,z1108,z6]),(0,[z1,z2,z8,z3,z1109,z6]),(0,[z1,z2,z1110,z3,z4,z6]),(0,[z1,z2,z73,z8,z4,z50])],[(0,[z1,z2,z298,z30,z3,z6]),(0,[z1,z2,z3,z1111,z4,z6]),(0,[z1,z2,z3,z4,z1112,z6])],[(0,[z1,z2,z867,z3,z4,z6]),(0,[z1,z2,z1037,z3,z14,z6]),(0,[z1,z2,z8,z488,z3,z6]),(0,[z1,z2,z3,z4,z6,z1113])]],
   [[(0,[z1,z2,z27,z3,z898,z4]),(0,[z1,z2,z935,z8,z3,z6])],[(0,[z1,z2,z186,z233,z4,z6]),(0,[z214,z29,z565,z3,z4,z6]),(0,[z1,z2,z10,z284,z3,z6]),(0,[z1,z2,z10,z3,z4,z327])],[(0,[z1,z1114,z8,z3,z4,z6]),(0,[z1,z2,z315,z3,z9,z6]),(0,[z1,z156,z2,z10,z3,z4])],[(0,[z42,z2,z3,z4,z649,z6]),(0,[z1,z367,z3,z4,z5,z6]),(0,[z1,z2,z38,z98,z3,z4]),(0,[z118,z1,z8,z922,z4,z6])],[(0,[z1,z2,z1115,z3,z4,z6]),(0,[z1,z2,z8,z3,z105,z6]),(0,[z138,z2,z8,z58,z9,z6]),(0,[z1,z386,z2,z10,z3,z4]),(0,[z1,z2,z163,z364,z4,z6])],[(0,[z1,z2,z3,z308,z5,z6]),(0,[z118,z1,z2,z38,z3,z4]),(0,[z1,z2,z169,z3,z4,z380]),(0,[z1,z2,z1116,z3,z4,z6])],[(0,[z1,z374,z2,z122,z3,z6]),(0,[z165,z2,z30,z3,z4,z87])],[(0,[z1,z2,z8,z1117,z4,z6]),(0,[z1,z2,z8,z3,z37,z561]),(0,[z1,z2,z1118,z3,z4,z6]),(0,[z7,z2,z27,z134,z4,z6]),(0,[z1,z2,z939,z27,z4,z6]),(0,[z1,z2,z38,z135,z3,z4]),(0,[z1,z92,z303,z3,z4,z23])],[(0,[z1,z2,z8,z233,z9,z6]),(0,[z1,z2,z8,z3,z1119,z6]),(0,[z106,z1,z2,z284,z3,z6]),(0,[z1,z2,z3,z9,z174,z6]),(0,[z1,z2,z190,z38,z3,z4]),(0,[z1,z2,z30,z254,z4,z150]),(0,[z1,z2,z1120,z3,z4,z6]),(0,[z1,z2,z8,z3,z80,z273])],[(0,[z1,z2,z8,z3,z1121,z6]),(0,[z1,z2,z173,z3,z9,z6]),(0,[z644,z2,z8,z3,z4,z36]),(0,[z1,z2,z1122,z3,z4,z6]),(0,[z1,z85,z8,z3,z726,z6]),(0,[z1,z2,z8,z3,z1123,z6]),(0,[z1,z2,z3,z4,z1124,z6])],[(0,[z1,z2,z123,z284,z3,z6]),(0,[z1,z2,z1125,z3,z4,z6]),(0,[z1,z270,z2,z10,z3,z4])],[(0,[z13,z2,z225,z3,z4,z36])],[(0,[z1,z2,z1126,z3,z4,z6]),(0,[z1,z2,z303,z3,z4,z87]),(0,[z1,z2,z943,z27,z3,z6]),(0,[z1,z2,z1127,z3,z4,z6])],[(0,[z106,z2,z220,z3,z4,z6]),(0,[z1,z2,z3,z99,z9,z6]),(0,[z1,z162,z30,z27,z3,z6]),(0,[z1,z2,z162,z3,z5,z6]),(0,[z1,z2,z3,z4,z1128,z6]),(0,[z1,z2,z1129,z8,z3,z6])],[(0,[z1,z2,z360,z448,z4,z6]),(0,[z1,z2,z107,z366,z3,z6]),(0,[z1,z2,z3,z4,z1130,z6])],[(0,[z1,z92,z2,z10,z3,z9]),(0,[z1,z2,z8,z3,z1131,z6])]],
   [[(0,[z1,z2,z30,z3,z4,z6]),(0,[z1,z2,z350,z3,z4,z5]),(0,[z1,z2,z8,z3,z1132,z6]),(0,[z1,z2,z146,z3,z5,z6])],[(0,[z1,z2,z360,z3,z564,z6]),(0,[z1,z2,z8,z1133,z4,z6]),(0,[z1,z2,z8,z3,z4,z133]),(0,[z1,z2,z1134,z3,z4,z6])],[(0,[z1,z2,z27,z3,z139,z6]),(0,[z1,z2,z182,z8,z83,z6]),(0,[z1,z2,z123,z235,z14,z6]),(0,[z1,z2,z1135,z3,z4,z6])],[(0,[z1,z2,z8,z1136,z4,z6]),(0,[z1,z2,z10,z3,z392,z6]),(0,[z1,z2,z3,z1054,z4,z6]),(0,[z1,z2,z68,z3,z14,z6]),(0,[z1,z130,z3,z62,z5,z6])],[(0,[z1,z307,z1011,z3,z4,z6]),(0,[z1,z2,z284,z3,z129,z6]),(0,[z1,z2,z1137,z3,z4,z6])],[(0,[z1,z2,z1138,z3,z4,z6]),(0,[z1,z2,z38,z3,z4,z544]),(0,[z1,z2,z1139,z3,z4,z6]),(0,[z1,z130,z2,z315,z3,z6]),(0,[z1,z44,z2,z303,z3,z4]),(0,[z1,z2,z8,z3,z1140,z6]),(0,[z1,z2,z3,z250,z207,z6])],[(0,[z1,z2,z3,z4,z1141,z6]),(0,[z1,z2,z1142,z3,z4,z6])],[(0,[z1,z2,z1143,z3,z4,z6]),(0,[z1,z2,z38,z102,z3,z4]),(0,[z1,z2,z298,z10,z3,z6])],[(0,[z1,z2,z186,z3,z14,z6]),(0,[z1,z2,z8,z4,z1144,z6]),(0,[z1,z2,z844,z3,z4,z6])],[(0,[z1,z2,z1145,z3,z4,z6]),(0,[z1,z1146,z8,z3,z4,z6])],[(0,[z138,z2,z90,z58,z4,z6]),(0,[z1,z2,z3,z4,z5,z394]),(0,[z1,z2,z1147,z3,z4,z6]),(0,[z1,z2,z284,z3,z341,z6]),(0,[z1,z2,z8,z3,z109,z824])],[(0,[z1,z2,z169,z3,z4,z36]),(0,[z1,z2,z162,z8,z3,z6]),(0,[z1,z2,z8,z3,z1148,z6])],[(0,[z1,z2,z10,z3,z4,z196]),(0,[z1,z2,z11,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1149]),(0,[z1,z2,z3,z4,z1150,z6]),(0,[z1,z85,z408,z3,z76,z6]),(0,[z1,z2,z3,z4,z6,z1151]),(0,[z1,z2,z10,z3,z936,z6])],[(0,[z1,z367,z194,z3,z4,z6]),(0,[z1152,z2,z8,z3,z4,z6]),(0,[z1,z2,z488,z3,z1072,z6]),(0,[z1,z2,z190,z8,z3,z474]),(0,[z161,z2,z124,z3,z4,z6]),(0,[z1,z2,z1153,z3,z4,z6])],[(0,[z1,z2,z8,z1154,z3,z4]),(0,[z1,z253,z11,z3,z4,z6]),(0,[z42,z2,z867,z3,z4,z6]),(0,[z1,z2,z1155,z3,z9,z6]),(0,[z285,z2,z8,z3,z9,z6]),(0,[z1,z2,z146,z8,z3,z6])],[(0,[z1,z2,z8,z3,z736,z6])]],
   [[(0,[z1,z2,z68,z3,z4,z6]),(0,[z1,z2,z30,z3,z1156,z6])],[(0,[z1,z2,z38,z3,z4,z87]),(0,[z160,z2,z8,z3,z4,z87])],[],[(0,[z1,z2,z8,z1157,z4,z6]),(0,[z1,z2,z8,z3,z1158,z6]),(0,[z1,z2,z8,z3,z4,z1038]),(0,[z1,z2,z3,z1159,z5,z6])],[(0,[z1,z2,z1160,z3,z4,z6]),(0,[z1,z2,z10,z3,z564,z6]),(0,[z1,z2,z1161,z3,z4,z6]),(0,[z1,z2,z8,z254,z9,z150]),(0,[z1,z2,z1162,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1163,z6])],[(0,[z147,z2,z8,z3,z9,z6]),(0,[z1,z2,z73,z4,z5,z50])],[(0,[z1,z2,z1164,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1165])],[(0,[z1,z2,z8,z3,z1166,z6])],[(0,[z1,z45,z8,z33,z4,z6]),(0,[z1,z2,z3,z4,z6,z101]),(0,[z553,z2,z220,z3,z4,z6])],[(0,[z1,z2,z8,z3,z1167,z6]),(0,[z1,z8,z33,z922,z4,z6])],[(0,[z1,z2,z3,z1089,z4,z6]),(0,[z138,z2,z30,z58,z4,z6]),(0,[z1,z2,z3,z355,z5,z6])],[(0,[z1,z2,z8,z3,z9,z6]),(0,[z1,z2,z175,z3,z4,z196])],[(0,[z1,z2,z1168,z3,z4,z6]),(0,[z1,z2,z437,z3,z237,z6])],[(0,[z1,z2,z1169,z3,z4,z6]),(0,[z1,z2,z286,z3,z9,z6]),(0,[z1,z8,z3,z726,z4,z6]),(0,[z1,z2,z1170,z3,z4,z6]),(0,[z1,z2,z8,z98,z6,z680])],[(0,[z1,z2,z30,z233,z4,z6]),(0,[z1,z2,z3,z4,z6,z1171]),(0,[z1,z2,z162,z3,z43,z6]),(0,[z1,z2,z8,z3,z1055,z6]),(0,[z1,z2,z8,z3,z4,z1172]),(0,[z1,z2,z8,z3,z34,z6]),(0,[z1,z2,z1173,z3,z4,z6])]],
   [[(0,[z1,z2,z8,z3,z1174,z6]),(0,[z42,z2,z117,z3,z292,z6]),(0,[z1,z284,z30,z27,z3,z6]),(0,[z1,z2,z38,z492,z3,z4]),(0,[z1,z2,z8,z3,z1175,z6])],[(0,[z1,z2,z90,z3,z262,z6]),(0,[z0,z1,z2,z10,z3,z4])],[(0,[z1,z2,z225,z3,z14,z6]),(0,[z1,z2,z284,z3,z174,z6]),(0,[z1,z2,z8,z3,z1176,z6])],[(0,[z1,z2,z1177,z3,z4,z6]),(0,[z1,z2,z73,z8,z14,z50]),(0,[z1,z85,z30,z3,z76,z6]),(0,[z1,z2,z30,z3,z1178,z6]),(0,[z1,z2,z1179,z8,z3,z6])],[(0,[z64,z2,z175,z3,z4,z6]),(0,[z1,z2,z194,z3,z4,z394]),(0,[z1,z2,z38,z3,z4,z9]),(0,[z1,z2,z140,z3,z519,z6]),(0,[z1,z2,z429,z10,z3,z4])],[(0,[z1,z2,z8,z3,z1180,z6]),(0,[z1,z2,z90,z3,z14,z6]),(0,[z1,z2,z3,z9,z466,z6]),(0,[z183,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z1181,z6])],[(0,[z1,z2,z1182,z565,z3,z6]),(0,[z13,z2,z8,z3,z4,z36]),(0,[z1,z2,z30,z3,z1183,z6]),(0,[z1,z2,z1184,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1185,z6]),(0,[z1,z2,z1186,z8,z3,z9]),(0,[z1,z2,z1187,z3,z4,z6])],[(0,[z1,z2,z267,z599,z4,z6]),(0,[z1,z2,z30,z3,z249,z6]),(0,[z1,z2,z8,z1188,z4,z6]),(0,[z1,z2,z1189,z3,z4,z6]),(0,[z1,z2,z1190,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1191,z6]),(0,[z1,z130,z8,z3,z726,z6]),(0,[z1,z2,z8,z4,z6,z749])],[(0,[z1,z2,z38,z3,z4,z23])],[(0,[z1,z2,z3,z4,z779,z6]),(0,[z1,z2,z10,z3,z251,z6]),(0,[z1,z2,z1192,z3,z4,z6]),(0,[z1,z108,z27,z3,z4,z6]),(0,[z1,z2,z152,z38,z3,z4]),(0,[z1,z2,z1193,z38,z3,z4]),(0,[z1,z2,z371,z3,z4,z5])],[(0,[z1,z2,z8,z3,z109,z574]),(0,[z1,z2,z1194,z3,z4,z6])],[(0,[z1,z2,z1195,z8,z3,z6]),(0,[z1,z2,z1196,z3,z4,z6])],[(0,[z1,z2,z8,z3,z1197,z6]),(0,[z1,z2,z1017,z27,z3,z6])],[(0,[z1,z2,z233,z4,z5,z6]),(0,[z1,z2,z225,z3,z4,z6]),(0,[z1,z2,z38,z211,z3,z4]),(0,[z1,z2,z1198,z3,z4,z6]),(0,[z1,z2,z8,z3,z1199,z6])]],
   [[(0,[z1,z2,z1021,z3,z4,z6]),(0,[z1,z2,z3,z4,z716,z46]),(0,[z1,z2,z8,z4,z150,z749])],[(0,[z1,z92,z11,z3,z4,z6])],[(0,[z1,z2,z90,z3,z4,z6]),(0,[z1,z30,z55,z3,z4,z6]),(0,[z1,z307,z8,z3,z9,z6]),(0,[z1,z2,z30,z3,z262,z6]),(0,[z1,z2,z3,z9,z479,z6]),(0,[z1,z2,z1200,z3,z4,z6])],[(0,[z1,z2,z8,z3,z741,z6]),(0,[z1,z2,z383,z3,z9,z6]),(0,[z89,z2,z8,z3,z14,z6]),(0,[z1,z2,z1201,z3,z4,z6]),(0,[z1,z2,z10,z3,z308,z6]),(0,[z1,z2,z1202,z3,z4,z6])],[(0,[z1,z307,z1169,z3,z4,z6]),(0,[z1,z1027,z8,z3,z4,z6]),(0,[z1,z44,z2,z10,z3,z14]),(0,[z1,z2,z1203,z3,z4,z6])],[(0,[z1,z2,z3,z4,z6,z1204]),(0,[z1,z2,z1205,z8,z3,z6])],[(0,[z1,z2,z1206,z3,z4,z6]),(0,[z1,z2,z30,z3,z14,z6]),(0,[z1,z2,z8,z3,z1207,z6])],[(0,[z28,z253,z360,z3,z4,z6]),(0,[z1,z1208,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z14,z133]),(0,[z1,z2,z3,z1209,z9,z6]),(0,[z1,z26,z110,z27,z3,z4]),(0,[z1,z2,z38,z3,z4,z174]),(0,[z1,z2,z38,z3,z4,z5]),(0,[z1,z2,z8,z3,z1210,z6]),(0,[z1,z2,z1211,z3,z4,z6]),(0,[z1,z2,z3,z4,z1212,z6]),(0,[z1,z2,z8,z3,z109,z80])],[(0,[z1,z253,z8,z233,z4,z6]),(0,[z1,z60,z2,z10,z3,z4]),(0,[z214,z29,z456,z3,z4,z6]),(0,[z19,z2,z8,z3,z736,z6]),(0,[z1,z8,z3,z62,z726,z6])],[(0,[z141,z2,z8,z3,z736,z6]),(0,[z1,z8,z3,z4,z1213,z23]),(0,[z1,z92,z2,z303,z3,z4]),(0,[z1,z2,z8,z3,z1214,z6]),(0,[z1,z2,z125,z3,z109,z80])],[(0,[z1,z2,z1215,z3,z4,z6]),(0,[z19,z1,z2,z38,z3,z4]),(0,[z1,z2,z38,z3,z4,z76]),(0,[z1,z2,z3,z4,z1216,z6])],[(0,[z1,z187,z2,z10,z3,z4]),(0,[z1,z2,z1217,z3,z4,z6]),(0,[z141,z1,z2,z38,z3,z4]),(0,[z1,z2,z1218,z3,z4,z6]),(0,[z1,z2,z333,z3,z4,z5])],[(0,[z1,z2,z1219,z3,z4,z6]),(0,[z1,z2,z27,z3,z526,z6]),(0,[z1,z597,z30,z3,z4,z6]),(0,[z1,z2,z8,z3,z1220,z6]),(0,[z1,z2,z8,z98,z868,z6])],[(0,[z1,z2,z8,z3,z1221,z6])],[(0,[z1,z1222,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z1223]),(0,[z151,z1,z2,z284,z3,z6]),(0,[z1,z2,z30,z3,z1224,z6])],[(0,[z1,z2,z27,z3,z392,z6]),(0,[z1,z748,z8,z3,z4,z6]),(0,[z1,z2,z219,z511,z4,z6]),(0,[z1,z2,z195,z30,z83,z6]),(0,[z1,z2,z1225,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z177]),(0,[z1,z2,z8,z3,z1226,z6]),(0,[z1,z2,z8,z3,z1227,z9]),(0,[z1,z2,z30,z3,z355,z6]),(0,[z1,z2,z1228,z3,z4,z6]),(0,[z1,z44,z2,z10,z3,z4])],[(0,[z1,z2,z8,z1229,z9,z6]),(0,[z1,z2,z38,z3,z4,z46]),(0,[z1,z2,z1230,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z185]),(0,[z1,z2,z267,z114,z14,z6]),(0,[z1,z2,z11,z3,z14,z6]),(0,[z1,z2,z1135,z3,z355,z6]),(0,[z1,z2,z107,z3,z43,z6]),(0,[z1,z2,z356,z3,z56,z6])],[(0,[z28,z253,z27,z3,z4,z6]),(0,[z29,z815,z8,z3,z4,z6]),(0,[z165,z2,z8,z3,z14,z87]),(0,[z2,z682,z8,z3,z14,z6]),(0,[z1,z2,z10,z3,z526,z6]),(0,[z1,z2,z211,z135,z4,z6]),(0,[z1,z2,z8,z3,z754,z6])],[(1,[z2,z8,z823,z4,z6]),(0,[z1,z2,z190,z8,z3,z541])],[(0,[z1,z2,z1053,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z1231]),(0,[z1,z11,z3,z4,z84,z6])],[(0,[z1,z2,z123,z382,z4,z6]),(0,[z1,z2,z1232,z3,z4,z6]),(0,[z141,z2,z8,z3,z9,z6]),(0,[z1,z2,z1233,z3,z4,z6]),(0,[z1,z2,z38,z1234,z3,z4]),(0,[z387,z1,z30,z3,z4,z6]),(0,[z1,z226,z30,z3,z4,z6]),(0,[z1,z2,z10,z488,z3,z6]),(0,[z1,z2,z3,z43,z6,z692]),(0,[z1,z2,z3,z1235,z4,z6])],[(0,[z1,z2,z8,z3,z1236,z6]),(0,[z1,z2,z320,z3,z9,z6]),(0,[z1,z2,z10,z145,z3,z4]),(0,[z1,z2,z3,z672,z4,z5])],[(0,[z1,z2,z27,z3,z4,z196]),(0,[z1,z307,z90,z3,z4,z6]),(0,[z1,z2,z8,z3,z1237,z6])],[(0,[z1,z2,z8,z3,z4,z1238]),(0,[z1,z2,z1081,z3,z4,z6]),(0,[z1,z2,z1239,z3,z4,z6]),(0,[z1,z92,z146,z8,z3,z23])],[(0,[z28,z253,z10,z3,z4,z6]),(0,[z1,z2,z1240,z3,z4,z6]),(0,[z1,z2,z1241,z8,z3,z6]),(0,[z1,z2,z27,z3,z4,z1032])],[(0,[z1,z2,z323,z8,z3,z324]),(0,[z1,z2,z3,z728,z174,z6]),(0,[z1,z2,z8,z3,z1242,z6])],[(0,[z1,z2,z38,z3,z39,z4]),(0,[z1,z2,z10,z3,z4,z649])],[(0,[z1,z2,z27,z448,z4,z6]),(0,[z165,z2,z8,z3,z355,z87]),(0,[z1,z2,z8,z3,z1243,z6]),(0,[z1,z2,z3,z434,z34,z6]),(0,[z1,z2,z190,z3,z5,z166]),(0,[z1,z2,z8,z3,z4,z749])],[],[(0,[z1,z45,z8,z33,z14,z6]),(0,[z1,z2,z125,z3,z14,z6]),(0,[z1,z2,z38,z3,z4,z50]),(0,[z1,z2,z267,z114,z4,z6])]],
   [[(0,[z1,z2,z8,z448,z4,z177]),(0,[z1,z2,z27,z3,z564,z6]),(0,[z165,z2,z8,z3,z4,z87]),(0,[z2,z27,z3,z1244,z4,z6]),(1,[z1,z92,z11,z3,z4]),(0,[z1,z2,z190,z280,z3,z166])],[(0,[z1,z2,z8,z3,z1245,z6]),(0,[z1,z2,z8,z3,z1246,z6]),(0,[z1,z2,z140,z3,z167,z6])],[(0,[z1,z2,z8,z1247,z4,z6]),(0,[z1,z2,z8,z254,z4,z150]),(0,[z1,z2,z73,z111,z8,z50])],[(0,[z1,z2,z8,z3,z1248,z6]),(0,[z1,z2,z8,z3,z564,z177])],[(0,[z1,z2,z10,z448,z4,z6]),(0,[z1,z2,z1249,z3,z4,z6]),(0,[z421,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z1250,z6]),(0,[z1,z2,z1005,z3,z4,z6]),(0,[z1,z45,z8,z922,z4,z6]),(0,[z1,z3,z4,z479,z84,z6]),(0,[z1,z2,z254,z604,z4,z150])],[(0,[z214,z29,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z1251,z6]),(0,[z1,z2,z1252,z3,z4,z6]),(0,[z1,z2,z3,z14,z6,z406]),(0,[z1,z130,z597,z8,z3,z6])],[(0,[z1,z2,z1253,z3,z4,z6]),(0,[z1,z2,z352,z3,z9,z6]),(0,[z1,z156,z8,z3,z4,z23]),(0,[z1,z2,z27,z98,z178,z6])],[(0,[z1,z2,z1118,z3,z4,z394]),(0,[z1,z92,z8,z3,z9,z23]),(0,[z1,z2,z1254,z3,z9,z6]),(0,[z1,z2,z8,z3,z247,z395])],[(0,[z2,z8,z263,z3,z9,z6]),(0,[z1,z2,z8,z3,z80,z824])],[(0,[z1,z307,z30,z3,z4,z6]),(0,[z1,z2,z1186,z8,z3,z4]),(0,[z1,z2,z208,z3,z14,z6]),(0,[z1,z2,z1255,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z6]),(0,[z1,z2,z8,z272,z51,z6]),(0,[z1,z2,z8,z3,z4,z1256]),(0,[z1,z92,z8,z3,z34,z23])],[(0,[z1,z2,z8,z3,z4,z1257]),(0,[z22,z2,z8,z3,z14,z6]),(0,[z1,z2,z3,z14,z6,z101]),(0,[z1,z2,z1084,z27,z3,z6]),(0,[z1,z2,z190,z8,z3,z166])],[(0,[z1,z2,z1258,z8,z3,z6]),(0,[z1,z2,z194,z3,z4,z185]),(0,[z1,z2,z1259,z3,z4,z6]),(0,[z13,z2,z8,z3,z14,z36]),(0,[z1,z2,z3,z4,z1260,z6]),(0,[z1,z130,z30,z3,z62,z6]),(0,[z1,z2,z125,z3,z4,z6])],[(0,[z28,z253,z8,z3,z37,z6]),(0,[z1,z2,z211,z235,z4,z6]),(0,[z1,z2,z10,z98,z178,z6])],[(0,[z1,z2,z8,z3,z1261,z6]),(0,[z1,z2,z1262,z3,z4,z6]),(0,[z138,z2,z8,z823,z4,z6]),(0,[z1,z2,z30,z3,z6,z49]),(0,[z1,z2,z1263,z3,z4,z6]),(0,[z1,z2,z3,z43,z752,z6])],[(0,[z1,z2,z38,z3,z129,z4])]],
   [[(0,[z1,z2,z360,z3,z9,z6]),(0,[z1,z2,z8,z3,z4,z1264]),(0,[z1,z2,z27,z3,z1066,z6])],[(0,[z1,z2,z1265,z3,z4,z6]),(0,[z1,z2,z8,z3,z1266,z6])],[(0,[z1,z2,z1035,z8,z3,z6]),(0,[z1,z2,z719,z3,z4,z6]),(0,[z1,z2,z1267,z3,z4,z6])],[(0,[z1,z2,z162,z38,z8,z3]),(0,[z1,z2,z8,z3,z4,z1268]),(0,[z1,z2,z254,z4,z5,z150])],[(0,[z1,z2,z1269,z3,z4,z6]),(0,[z138,z2,z8,z58,z262,z6]),(0,[z1,z2,z3,z4,z723,z6]),(0,[z24,z1,z2,z38,z3,z4]),(0,[z1,z2,z790,z114,z4,z6]),(0,[z1,z2,z1270,z3,z4,z6])],[(0,[z1,z367,z8,z3,z9,z6]),(0,[z1,z2,z194,z3,z82,z6]),(0,[z1,z2,z3,z82,z5,z6]),(0,[z1,z2,z303,z3,z4,z36]),(0,[z1,z2,z110,z30,z3,z4]),(0,[z1,z2,z8,z3,z4,z1271])],[(0,[z1,z1272,z8,z3,z4,z6]),(0,[z106,z2,z867,z3,z4,z6]),(0,[z1,z2,z1273,z3,z14,z6]),(0,[z1,z2,z315,z3,z14,z6]),(0,[z1,z2,z3,z4,z1274,z6]),(0,[z1,z2,z1275,z3,z4,z6]),(0,[z1,z2,z208,z3,z4,z6]),(0,[z1,z2,z1276,z3,z4,z6])],[(0,[z1,z2,z8,z448,z37,z6]),(0,[z1,z2,z27,z3,z251,z6]),(0,[z1,z2,z343,z3,z9,z6]),(0,[z1,z2,z1277,z8,z3,z6]),(0,[z1,z2,z10,z3,z4,z532])],[(0,[z138,z2,z8,z58,z14,z6]),(0,[z1,z92,z2,z10,z3,z14]),(0,[z1,z2,z1278,z38,z3,z4]),(0,[z1,z2,z8,z3,z6,z1279])],[(0,[z1,z374,z8,z3,z316,z6]),(0,[z1,z85,z2,z38,z3,z4]),(0,[z1,z2,z3,z4,z1280,z6])],[(0,[z1,z2,z8,z3,z1156,z6]),(0,[z1,z2,z232,z3,z9,z6]),(0,[z1,z2,z1281,z8,z3,z9]),(0,[z1,z2,z8,z3,z728,z6])],[],[(0,[z1,z2,z8,z3,z4,z1282]),(0,[z1,z2,z8,z233,z14,z6]),(0,[z1,z2,z3,z4,z1283,z6]),(0,[z1,z2,z195,z8,z393,z6])],[(0,[z1,z2,z980,z3,z4,z177]),(0,[z594,z29,z8,z3,z4,z6]),(0,[z1,z2,z173,z3,z14,z6]),(0,[z1,z2,z8,z3,z1284,z6]),(0,[z1,z2,z1285,z8,z3,z4])],[(0,[z1,z2,z73,z27,z4,z50]),(0,[z1,z2,z284,z366,z3,z6]),(0,[z32,z1,z748,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z1286]),(0,[z1,z2,z10,z3,z4,z443])],[(0,[z1,z2,z27,z3,z308,z6]),(0,[z1,z2,z3,z4,z6,z1287])]],
   [[],[(0,[z1,z2,z8,z3,z292,z196]),(0,[z1,z2,z3,z99,z14,z6]),(0,[z1,z2,z1288,z3,z4,z6])],[(0,[z1,z2,z8,z3,z1289,z6]),(0,[z1,z2,z8,z3,z1227,z4])],[(0,[z7,z2,z8,z134,z392,z6]),(0,[z1,z2,z122,z3,z9,z6]),(0,[z1,z2,z10,z3,z9,z6]),(0,[z1,z2,z1273,z3,z4,z6]),(0,[z204,z2,z8,z3,z14,z6]),(0,[z1,z2,z30,z3,z1290,z6]),(0,[z1,z2,z315,z3,z4,z6])],[(0,[z1,z2,z3,z4,z937,z6]),(0,[z287,z2,z8,z3,z9,z6]),(0,[z1,z92,z2,z10,z3,z4])],[(0,[z1,z2,z1291,z3,z4,z6]),(0,[z138,z2,z8,z58,z4,z6]),(0,[z1,z2,z3,z1209,z4,z6]),(0,[z1,z2,z1292,z3,z4,z6]),(0,[z1,z44,z10,z3,z4,z84])],[(0,[z1,z2,z8,z3,z1293,z6]),(0,[z1,z2,z27,z3,z6,z720]),(0,[z1,z2,z10,z3,z34,z6])],[(0,[z1,z2,z8,z3,z4,z1294]),(0,[z1,z2,z3,z9,z380,z6]),(0,[z1,z2,z1295,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z557]),(0,[z1,z2,z73,z4,z406,z50])],[(0,[z1,z2,z1296,z3,z4,z6]),(0,[z1,z2,z3,z4,z1297,z6]),(0,[z1,z2,z8,z3,z1298,z6]),(0,[z1,z2,z1299,z3,z4,z6])],[(0,[z1,z2,z8,z233,z4,z6]),(0,[z1,z2,z8,z3,z1300,z6]),(0,[z1,z2,z30,z3,z1301,z6]),(0,[z1,z2,z10,z822,z3,z4])],[(0,[z1,z2,z721,z3,z9,z6]),(0,[z657,z2,z8,z3,z14,z6]),(0,[z342,z2,z8,z3,z14,z6]),(0,[z1,z2,z38,z3,z4,z36]),(0,[z1,z2,z173,z3,z4,z6])],[(0,[z1,z367,z90,z3,z4,z6]),(0,[z1,z2,z3,z1302,z9,z6]),(0,[z1099,z2,z27,z3,z4,z6]),(0,[z1,z2,z267,z506,z4,z6]),(0,[z1,z2,z1303,z3,z4,z6])],[(0,[z214,z29,z30,z3,z4,z6]),(0,[z1,z2,z3,z43,z4,z196]),(0,[z665,z2,z117,z3,z4,z6]),(0,[z1,z2,z3,z262,z5,z6]),(0,[z1,z2,z8,z3,z9,z394]),(0,[z1,z2,z3,z4,z1304,z6]),(0,[z1,z2,z10,z3,z4,z562])],[(0,[z1,z2,z8,z3,z1305,z6]),(0,[z1,z2,z27,z3,z61,z6]),(0,[z1,z2,z38,z11,z3,z4]),(0,[z1,z2,z8,z3,z1178,z6]),(0,[z1,z85,z8,z3,z76,z6]),(0,[z1,z2,z8,z3,z1306,z6])],[(0,[z674,z1,z8,z39,z4,z6]),(0,[z1,z2,z1307,z3,z4,z6]),(0,[z1,z2,z1308,z3,z4,z6]),(0,[z1,z92,z30,z3,z4,z23]),(0,[z1,z2,z8,z3,z4,z1309]),(0,[z1,z2,z3,z99,z4,z6])],[(0,[z1,z2,z186,z3,z37,z6]),(0,[z1,z2,z3,z917,z139,z6]),(0,[z1,z29,z2,z844,z3,z4]),(0,[z1,z623,z2,z10,z3,z4]),(0,[z42,z2,z102,z3,z4,z6]),(0,[z2,z8,z3,z823,z4,z6]),(0,[z1,z2,z10,z1188,z4,z6])]],
   [[(0,[z1,z2,z8,z3,z1310,z6]),(0,[z1,z2,z8,z3,z1183,z6]),(0,[z1,z2,z3,z4,z5,z716])],[(0,[z1,z2,z8,z1311,z4,z6]),(0,[z2,z8,z3,z736,z9,z6]),(0,[z1,z2,z8,z347,z271,z6]),(0,[z1,z2,z10,z38,z3,z4]),(0,[z1,z2,z208,z3,z6,z49])],[(0,[z1,z2,z8,z3,z249,z6]),(0,[z1,z2,z404,z3,z9,z6]),(0,[z1,z2,z3,z4,z954,z6]),(0,[z1,z2,z27,z488,z3,z6]),(0,[z1,z2,z38,z3,z4,z167]),(0,[z1,z2,z1312,z8,z3,z4]),(0,[z1,z2,z1313,z3,z4,z6])],[(0,[z1,z2,z8,z1314,z4,z6]),(0,[z1,z2,z1315,z3,z4,z6])],[(0,[z1,z2,z1316,z3,z4,z6]),(0,[z1,z2,z10,z3,z61,z6]),(0,[z1,z2,z38,z8,z3,z9]),(0,[z1,z2,z3,z9,z434,z6]),(0,[z1,z2,z10,z3,z4,z663]),(0,[z1,z85,z381,z8,z3,z6])],[(0,[z1,z2,z3,z37,z5,z6]),(0,[z1,z2,z10,z3,z4,z556]),(0,[z563,z2,z8,z3,z9,z6]),(0,[z1,z486,z30,z3,z4,z6]),(0,[z1,z2,z1317,z3,z4,z6])],[(0,[z1,z2,z1318,z8,z3,z4]),(0,[z1,z8,z3,z4,z6,z962]),(0,[z1,z2,z3,z4,z6,z963]),(0,[z1,z2,z8,z3,z4,z1213]),(0,[z1,z44,z2,z11,z3,z4])],[(0,[z1,z2,z844,z565,z3,z4]),(0,[z1,z2,z8,z3,z798,z6]),(0,[z1,z2,z27,z3,z105,z6]),(0,[z1,z8,z3,z4,z6,z1319]),(0,[z1,z2,z8,z1320,z4,z6])],[(0,[z1,z2,z8,z3,z4,z1321]),(0,[z106,z1,z2,z38,z3,z4]),(0,[z1,z2,z10,z3,z4,z573]),(0,[z1,z2,z747,z3,z9,z6]),(0,[z1,z2,z8,z254,z14,z150]),(0,[z2,z10,z220,z3,z4,z36])],[(0,[z28,z253,z8,z3,z4,z177]),(0,[z1,z2,z8,z3,z1322,z6]),(0,[z1,z2,z3,z289,z9,z6]),(0,[z1,z2,z1323,z3,z4,z6]),(0,[z1,z2,z1324,z3,z4,z6])],[],[(0,[z138,z307,z8,z58,z4,z6]),(0,[z1,z2,z211,z284,z3,z6])],[(0,[z1,z2,z1182,z8,z3,z6]),(0,[z1,z2,z8,z3,z262,z6]),(0,[z1,z367,z30,z3,z4,z6]),(0,[z1,z2,z3,z1325,z14,z6]),(0,[z1,z2,z38,z3,z14,z4]),(0,[z259,z2,z8,z3,z14,z6]),(0,[z592,z2,z8,z3,z14,z6]),(0,[z1,z2,z162,z27,z3,z6])],[(0,[z1,z2,z757,z8,z9,z6]),(0,[z1,z2,z1326,z3,z4,z6])],[(0,[z1,z2,z10,z3,z105,z6]),(0,[z1,z2,z8,z3,z1327,z6]),(0,[z1,z2,z423,z3,z308,z6]),(0,[z1,z2,z3,z4,z1328,z6]),(0,[z1,z2,z111,z3,z5,z6])],[(0,[z1,z367,z1232,z3,z4,z6]),(0,[z1,z2,z366,z3,z9,z6]),(0,[z1,z2,z1155,z3,z4,z6]),(0,[z1,z2,z11,z3,z4,z87]),(0,[z1,z2,z146,z27,z3,z6]),(0,[z1,z683,z30,z3,z4,z6]),(0,[z1,z566,z30,z3,z4,z6]),(0,[z1,z2,z3,z790,z4,z6])]],
   [[(0,[z1,z2,z8,z3,z14,z6]),(0,[z1,z2,z284,z3,z5,z6]),(0,[z1,z2,z1329,z3,z4,z6])],[(0,[z1,z2,z1330,z3,z4,z6])],[(0,[z1,z2,z90,z3,z4,z394]),(0,[z1,z2,z286,z3,z14,z6]),(0,[z1,z2,z3,z4,z6,z1331])],[(0,[z704,z2,z8,z3,z14,z6]),(0,[z1,z2,z748,z3,z4,z6])],[(0,[z1,z2,z27,z3,z4,z133]),(0,[z1,z2,z152,z114,z4,z6]),(0,[z1,z2,z38,z142,z3,z4]),(0,[z1,z2,z8,z3,z812,z4]),(0,[z1,z2,z3,z1332,z4,z6]),(0,[z1,z2,z10,z3,z4,z575])],[(0,[z1,z2,z8,z3,z1333,z6]),(0,[z118,z1,z298,z8,z39,z6]),(0,[z1,z2,z8,z3,z1334,z6]),(0,[z1,z1222,z10,z3,z4,z6])],[(0,[z1,z2,z1335,z3,z4,z6]),(0,[z1,z2,z3,z4,z1336,z6])],[(0,[z1,z2,z8,z3,z4,z1337]),(0,[z1,z2,z3,z752,z4,z6]),(0,[z1,z2,z1338,z3,z4,z6])],[(0,[z1,z776,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z1224,z6])],[(0,[z1,z2,z3,z1325,z4,z6]),(0,[z1,z45,z2,z38,z3,z4]),(0,[z1,z130,z2,z38,z3,z4]),(0,[z1,z2,z190,z27,z3,z166]),(0,[z1,z147,z8,z39,z4,z6]),(0,[z1,z2,z140,z173,z3,z6]),(0,[z1,z2,z1339,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z576]),(0,[z1,z2,z3,z6,z406,z49])],[(0,[z1,z2,z3,z4,z5,z561]),(0,[z106,z2,z329,z3,z4,z6]),(0,[z210,z2,z175,z3,z4,z6]),(0,[z1,z2,z8,z3,z355,z6]),(0,[z1,z2,z110,z68,z3,z4]),(0,[z1,z2,z190,z8,z3,z633])],[(0,[z1,z2,z10,z3,z4,z133]),(0,[z1,z2,z8,z1340,z3,z6]),(0,[z1,z2,z1341,z3,z4,z6]),(0,[z1,z2,z195,z10,z83,z6])],[(0,[z1,z2,z3,z4,z1141,z177]),(0,[z1,z307,z8,z134,z4,z6]),(0,[z1,z2,z1342,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z512]),(0,[z1,z2,z788,z8,z3,z6]),(0,[z1,z2,z111,z8,z3,z6])],[(0,[z1,z2,z8,z3,z1343,z6]),(0,[z141,z2,z122,z3,z9,z6]),(0,[z141,z2,z10,z3,z9,z6])],[(0,[z1,z2,z1344,z3,z4,z6]),(0,[z1,z2,z10,z3,z4,z516]),(0,[z42,z2,z279,z3,z4,z6]),(0,[z1,z2,z231,z3,z9,z6]),(0,[z1,z2,z423,z3,z526,z6]),(0,[z1,z2,z284,z8,z3,z6]),(0,[z2,z8,z3,z4,z6,z1345]),(0,[z1,z2,z8,z3,z1346,z6])],[(0,[z172,z1,z8,z39,z4,z6]),(0,[z1,z2,z934,z3,z4,z6]),(0,[z1,z2,z8,z3,z1347,z6]),(0,[z1,z2,z286,z3,z4,z6]),(0,[z1,z92,z226,z10,z3,z4])]],
   [[(0,[z28,z253,z8,z3,z4,z561]),(0,[z1,z2,z8,z3,z4,z1348]),(0,[z1,z2,z3,z109,z330,z80])],[(0,[z1,z2,z1349,z3,z4,z6])],[(0,[z1,z2,z802,z8,z3,z4]),(0,[z1,z307,z8,z3,z262,z6]),(0,[z1,z2,z8,z3,z1350,z6])],[(0,[z1,z367,z8,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z1351]),(0,[z1,z2,z30,z3,z4,z394]),(0,[z1,z2,z1352,z8,z3,z6]),(0,[z1,z8,z922,z39,z4,z6])],[(0,[z1,z2,z1353,z8,z3,z6]),(0,[z1,z2,z3,z289,z105,z6]),(0,[z1,z2,z30,z3,z464,z6]),(0,[z1,z2,z10,z3,z4,z608]),(0,[z1,z2,z8,z1354,z4,z6]),(1,[z1,z2,z790,z4,z6])],[(0,[z1,z2,z3,z4,z1355,z6]),(0,[z1,z580,z8,z3,z62,z6]),(0,[z1,z2,z1356,z3,z4,z6])],[(0,[z1,z307,z8,z3,z14,z6]),(0,[z1,z2,z1357,z3,z4,z6]),(0,[z1,z2,z208,z3,z4,z87]),(0,[z1,z2,z27,z3,z1158,z6])],[(0,[z1,z2,z234,z3,z290,z6]),(0,[z1,z2,z383,z3,z14,z6]),(0,[z165,z2,z10,z3,z4,z87])],[(0,[z1,z2,z863,z3,z9,z6]),(0,[z1,z2,z162,z284,z3,z6]),(0,[z328,z2,z113,z3,z4,z6]),(0,[z1,z2,z1358,z3,z4,z6]),(0,[z1,z2,z195,z8,z517,z6])],[(0,[z1,z2,z8,z3,z1359,z6]),(0,[z1,z2,z3,z9,z5,z6]),(0,[z1,z2,z8,z9,z6,z1010]),(0,[z13,z2,z8,z3,z4,z718]),(0,[z1,z38,z30,z27,z3,z4])],[(0,[z1,z2,z8,z448,z4,z561]),(0,[z1,z2,z1360,z3,z4,z6]),(0,[z1361,z2,z8,z3,z4,z6]),(0,[z1,z45,z232,z33,z4,z6])],[(0,[z1,z2,z186,z3,z4,z177]),(0,[z1,z92,z8,z3,z4,z1213])],[(0,[z1,z45,z27,z33,z4,z6]),(0,[z1,z2,z8,z3,z4,z1362])],[(0,[z1,z2,z30,z3,z37,z6]),(0,[z1,z2,z8,z3,z564,z561]),(0,[z1,z2,z10,z3,z4,z41]),(0,[z1,z2,z27,z3,z1167,z6])],[(0,[z1,z2,z8,z3,z1363,z6]),(0,[z1,z2,z3,z1364,z4,z6])],[(0,[z1,z2,z27,z3,z9,z6])]],
   [[(0,[z1,z2,z38,z117,z3,z4]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1,z2,z1365,z3,z4,z6]),(0,[z1,z2,z162,z110,z8,z3]),(0,[z1,z2,z1366,z3,z4,z6]),(0,[z1,z2,z98,z178,z5,z6])],[(0,[z1,z2,z8,z3,z4,z858])],[(0,[z1,z2,z8,z3,z9,z177]),(0,[z1,z2,z1367,z3,z4,z6]),(0,[z106,z2,z175,z3,z251,z6]),(0,[z1,z2,z225,z3,z4,z87]),(0,[z1,z2,z142,z3,z4,z466]),(0,[z1,z2,z27,z3,z34,z6]),(0,[z1,z2,z1368,z3,z4,z6]),(0,[z1,z2,z3,z1369,z4,z6])],[(0,[z1,z307,z8,z3,z4,z6]),(0,[z141,z2,z3,z289,z9,z6]),(0,[z1,z2,z407,z3,z289,z6]),(0,[z1,z2,z27,z3,z1174,z6]),(0,[z1,z2,z162,z38,z3,z6]),(0,[z1,z2,z189,z3,z4,z380]),(0,[z1,z45,z10,z33,z4,z6])],[(0,[z1,z2,z8,z3,z4,z866]),(0,[z1,z2,z8,z3,z9,z185]),(0,[z1,z2,z280,z3,z9,z6]),(0,[z1,z2,z383,z3,z4,z6]),(0,[z1,z2,z111,z3,z6,z406])],[(0,[z1,z2,z10,z3,z4,z202]),(0,[z1,z2,z27,z3,z1176,z6])],[(0,[z1,z2,z1205,z27,z3,z6]),(0,[z1,z2,z38,z8,z3,z4]),(0,[z1,z130,z8,z3,z62,z6]),(0,[z1,z2,z8,z3,z1370,z6])],[(0,[z1,z2,z8,z3,z4,z1371]),(0,[z1,z2,z3,z4,z1372,z6])],[(0,[z1,z2,z3,z4,z1373,z6]),(0,[z1,z2,z3,z837,z9,z6]),(0,[z1,z2,z1374,z3,z4,z6]),(0,[z191,z2,z329,z3,z4,z6]),(0,[z1,z2,z3,z1350,z5,z6]),(0,[z1,z2,z8,z3,z6,z49]),(0,[z1,z2,z1375,z3,z4,z6])],[(0,[z1,z2,z8,z3,z1376,z6]),(0,[z1,z2,z3,z1302,z4,z6]),(0,[z19,z2,z8,z3,z14,z6]),(0,[z13,z2,z27,z3,z4,z36]),(0,[z1,z2,z1377,z3,z4,z6]),(0,[z1,z2,z3,z728,z5,z6]),(0,[z1,z2,z1378,z3,z4,z6])],[(0,[z1,z2,z3,z251,z5,z6]),(0,[z1,z2,z8,z3,z4,z394]),(0,[z1,z2,z3,z14,z6,z1204]),(0,[z1,z2,z195,z38,z3,z4]),(0,[z118,z1,z30,z39,z4,z6]),(0,[z1,z92,z2,z11,z3,z4]),(0,[z1,z2,z10,z3,z1175,z6])],[(0,[z1,z66,z2,z122,z3,z6]),(0,[z1,z2,z320,z3,z14,z6]),(0,[z1,z2,z298,z3,z5,z6])],[(0,[z1,z2,z8,z3,z4,z1379]),(0,[z1,z2,z30,z3,z292,z6]),(0,[z1,z2,z162,z173,z3,z6]),(0,[z1,z2,z1380,z3,z4,z6])],[(0,[z1,z2,z8,z1381,z4,z6]),(0,[z1,z2,z1382,z3,z4,z6]),(0,[z1,z2,z360,z233,z4,z6]),(0,[z1,z2,z8,z3,z292,z133]),(0,[z1,z2,z8,z3,z4,z875])],[(0,[z138,z367,z8,z58,z4,z6]),(0,[z1,z2,z1383,z3,z4,z6]),(0,[z1,z2,z3,z729,z4,z6])],[(0,[z42,z2,z117,z3,z4,z196]),(0,[z1,z2,z284,z3,z114,z6]),(0,[z1,z2,z10,z111,z3,z6]),(0,[z1,z2,z3,z4,z6,z716]),(0,[z1,z2,z388,z3,z6,z692])]],
   [[(0,[z1,z2,z3,z249,z5,z6]),(0,[z1,z655,z27,z3,z4,z6]),(0,[z1,z2,z1384,z3,z4,z6]),(0,[z13,z2,z10,z3,z4,z36]),(0,[z1,z2,z1312,z27,z3,z4]),(0,[z1,z2,z3,z4,z6,z1385])],[(0,[z1,z2,z8,z3,z1386,z6]),(0,[z1,z110,z30,z27,z3,z4]),(0,[z1,z2,z110,z3,z4,z174]),(0,[z1,z2,z110,z3,z4,z5]),(0,[z1,z2,z38,z284,z8,z3]),(0,[z1,z2,z3,z4,z330,z6])],[(0,[z1,z2,z186,z3,z4,z561]),(0,[z1,z2,z8,z1229,z4,z6]),(0,[z1,z2,z3,z4,z5,z196]),(0,[z1,z45,z33,z4,z5,z6])],[(0,[z1,z2,z1387,z3,z4,z6])],[(0,[z1,z2,z8,z3,z4,z1388]),(0,[z1,z2,z38,z549,z3,z4]),(0,[z1,z2,z1318,z27,z3,z4]),(0,[z1,z2,z3,z1389,z4,z6])],[(0,[z386,z2,z8,z3,z9,z6]),(0,[z1,z26,z11,z3,z4,z6]),(0,[z1,z2,z1390,z3,z4,z6]),(0,[z1,z2,z140,z3,z752,z6])],[(0,[z138,z2,z58,z4,z5,z6]),(0,[z2,z8,z3,z1244,z4,z6]),(0,[z1,z2,z3,z4,z1391,z6])],[(0,[z1,z2,z8,z791,z4,z6]),(1,[z1,z2,z8,z868,z6])],[(0,[z1,z2,z1078,z3,z4,z561]),(0,[z1,z2,z10,z3,z4,z635]),(0,[z1,z2,z320,z3,z4,z6])],[(0,[z1,z2,z8,z3,z9,z561]),(0,[z214,z29,z8,z3,z14,z6]),(0,[z1,z2,z298,z8,z3,z6]),(0,[z1,z2,z3,z4,z1392,z6])],[(0,[z1,z2,z3,z4,z1393,z6]),(0,[z1,z2,z90,z3,z4,z185]),(0,[z1,z2,z352,z3,z14,z6]),(0,[z1,z2,z27,z3,z109,z80]),(0,[z1,z2,z1394,z3,z4,z6])],[(0,[z1,z92,z8,z3,z14,z23]),(0,[z1,z2,z107,z284,z3,z6])],[(0,[z138,z2,z10,z58,z4,z6]),(1,[z1,z748,z3,z4,z6]),(0,[z1,z2,z1395,z3,z4,z6]),(0,[z1,z2,z8,z3,z1396,z6])],[(0,[z1,z2,z3,z4,z466,z133]),(0,[z1,z367,z1316,z3,z4,z6]),(0,[z1,z2,z8,z3,z6,z1397]),(0,[z1,z2,z142,z3,z9,z5]),(0,[z1,z2,z8,z3,z1290,z6]),(0,[z1,z2,z8,z3,z4,z1398]),(0,[z1,z2,z3,z4,z6,z1399])],[(0,[z1,z2,z8,z3,z1400,z6]),(0,[z1,z2,z423,z3,z9,z6]),(0,[z151,z1,z2,z38,z3,z4]),(0,[z1,z2,z38,z284,z3,z6]),(0,[z1,z2,z10,z110,z3,z4]),(0,[z1,z528,z30,z3,z4,z6]),(0,[z1,z2,z3,z1401,z4,z6]),(0,[z1,z2,z8,z3,z824,z166])],[(0,[z1,z2,z3,z9,z6,z406]),(0,[z1,z2,z10,z3,z4,z389]),(0,[z1,z2,z1402,z3,z4,z6])]],
   [[(0,[z1,z2,z10,z233,z4,z6]),(0,[z1,z2,z8,z1403,z4,z6]),(0,[z1,z8,z3,z4,z6,z1213]),(0,[z1,z2,z8,z254,z4,z749])],[(0,[z1,z2,z8,z3,z1159,z6]),(0,[z1,z2,z8,z1404,z3,z6]),(0,[z1,z2,z10,z3,z109,z80])],[(0,[z1,z2,z8,z3,z1405,z6]),(0,[z165,z2,z231,z3,z4,z87]),(0,[z1,z748,z27,z3,z4,z6]),(0,[z1,z2,z1406,z3,z4,z6])],[(0,[z1,z2,z30,z3,z436,z6]),(0,[z1,z2,z8,z3,z4,z1407]),(0,[z1,z2,z90,z3,z82,z6]),(0,[z141,z2,z3,z9,z5,z6]),(0,[z143,z2,z8,z3,z14,z6]),(0,[z1,z2,z8,z3,z1301,z6]),(0,[z1,z2,z1408,z3,z4,z6]),(0,[z1,z2,z1409,z3,z4,z6])],[(0,[z1,z2,z360,z3,z14,z6]),(0,[z1,z2,z750,z3,z4,z6]),(0,[z1,z2,z38,z3,z1410,z4]),(0,[z1,z2,z879,z8,z3,z6])],[(0,[z1,z367,z8,z3,z262,z6]),(0,[z138,z2,z8,z58,z4,z394]),(0,[z1,z2,z3,z859,z61,z6]),(0,[z1,z2,z8,z3,z1411,z6]),(0,[z1,z2,z3,z1412,z4,z6])],[(0,[z214,z29,z8,z3,z4,z6]),(0,[z1,z2,z1413,z8,z3,z6]),(0,[z1,z1414,z8,z3,z4,z6]),(0,[z118,z1,z8,z39,z9,z6]),(0,[z2,z8,z3,z9,z560,z6]),(0,[z701,z2,z8,z3,z9,z6]),(0,[z1,z130,z173,z3,z62,z6]),(0,[z1,z2,z8,z4,z868,z6])],[(0,[z1,z2,z352,z3,z4,z6]),(0,[z1,z2,z38,z1415,z3,z4])],[(0,[z214,z815,z8,z3,z4,z6]),(0,[z1,z2,z1254,z3,z4,z6]),(0,[z1,z2,z3,z4,z1077,z6]),(0,[z1,z2,z162,z140,z3,z6]),(0,[z1,z92,z8,z3,z4,z23])],[(0,[z1,z2,z30,z3,z4,z177]),(0,[z1,z2,z1416,z8,z4,z6]),(0,[z1,z2,z1417,z3,z4,z6]),(0,[z1,z2,z122,z3,z249,z6]),(0,[z1,z2,z10,z3,z249,z6]),(0,[z1,z367,z8,z3,z14,z6]),(0,[z141,z2,z27,z3,z9,z6]),(0,[z1,z2,z10,z3,z9,z5])],[(0,[z1,z570,z30,z3,z4,z6]),(0,[z1,z1418,z8,z3,z4,z6]),(0,[z1,z2,z111,z27,z3,z6])],[(0,[z1,z2,z30,z3,z4,z185]),(0,[z138,z2,z404,z58,z4,z6]),(0,[z1,z2,z1419,z3,z4,z6]),(0,[z1,z2,z3,z9,z6,z1171]),(0,[z1,z2,z343,z3,z14,z6]),(0,[z1,z270,z27,z3,z4,z6])],[(0,[z1,z2,z8,z1420,z4,z6]),(0,[z1,z2,z3,z292,z5,z6]),(0,[z630,z2,z8,z3,z9,z6]),(0,[z223,z2,z8,z3,z9,z6]),(0,[z1,z2,z8,z3,z1421,z6])],[(0,[z1,z2,z1422,z3,z4,z6]),(0,[z1,z2,z140,z3,z252,z6]),(0,[z1,z2,z3,z1148,z5,z6])],[(0,[z1,z2,z232,z3,z14,z6])],[(0,[z1,z2,z1281,z8,z3,z4]),(0,[z1,z2,z107,z173,z3,z6]),(0,[z1,z2,z1423,z8,z3,z6])]],
   [[(0,[z1,z2,z8,z3,z4,z1424]),(0,[z1,z2,z27,z3,z14,z6]),(0,[z1,z2,z789,z3,z9,z6]),(0,[z1,z2,z3,z1425,z4,z6]),(0,[z1,z2,z343,z254,z4,z150])],[(0,[z1,z2,z360,z3,z4,z6]),(0,[z1,z2,z169,z3,z9,z6]),(0,[z1,z2,z3,z4,z1426,z6])],[(0,[z1,z2,z1427,z3,z4,z6]),(0,[z1,z2,z8,z3,z4,z1428]),(0,[z1,z2,z1429,z3,z4,z6])],[(0,[z1,z2,z8,z233,z37,z6]),(0,[z1,z2,z117,z3,z4,z196]),(0,[z1,z2,z140,z3,z4,z196]),(0,[z1,z2,z10,z3,z262,z6]),(0,[z7,z2,z8,z134,z9,z6]),(0,[z1,z2,z1430,z8,z3,z6]),(0,[z1,z2,z10,z3,z9,z46]),(0,[z165,z2,z27,z3,z4,z87]),(0,[z1,z2,z1431,z3,z4,z6])],[(0,[z1,z2,z30,z3,z82,z6]),(0,[z1,z2,z142,z68,z3,z4])],[(0,[z1,z2,z280,z3,z14,z6]),(0,[z1,z2,z27,z254,z4,z150])],[(0,[z1,z2,z863,z3,z4,z6]),(0,[z2,z8,z3,z4,z718,z87]),(0,[z2,z10,z3,z4,z36,z87]),(0,[z1,z2,z1432,z3,z4,z6])],[(0,[z1,z2,z10,z3,z14,z6]),(0,[z1,z2,z122,z3,z14,z6]),(0,[z1,z270,z3,z4,z174,z6])],[(0,[z1,z2,z978,z565,z3,z4]),(0,[z1,z2,z38,z134,z3,z4]),(0,[z1,z2,z8,z3,z945,z6]),(0,[z1,z2,z8,z3,z6,z1433]),(0,[z1,z2,z343,z3,z4,z6])],[(0,[z1,z2,z8,z823,z4,z6]),(0,[z1,z2,z918,z3,z9,z6]),(0,[z1,z2,z919,z3,z9,z6]),(0,[z1,z2,z712,z3,z14,z6])],[(0,[z1,z2,z8,z3,z1434,z6])],[(0,[z1,z2,z232,z3,z4,z6]),(0,[z1,z2,z3,z4,z1435,z6]),(0,[z1,z2,z195,z83,z5,z6]),(0,[z1,z2,z3,z4,z6,z1436])],[(0,[z1,z2,z8,z3,z262,z394]),(0,[z1,z2,z1437,z3,z4,z6]),(0,[z1,z2,z814,z3,z9,z6]),(0,[z2,z8,z3,z299,z14,z6]),(0,[z1,z2,z1438,z8,z3,z6]),(0,[z1,z2,z195,z8,z63,z6]),(0,[z1,z85,z3,z76,z5,z6]),(0,[z1,z2,z10,z254,z4,z150])],[(0,[z1,z2,z27,z3,z4,z6]),(0,[z1,z2,z844,z8,z3,z4]),(0,[z1,z2,z38,z8,z3,z14]),(0,[z1,z2,z27,z3,z4,z1256])],[(0,[z2,z8,z823,z58,z4,z6]),(0,[z1,z8,z3,z4,z1108,z6]),(0,[z1,z2,z1439,z38,z3,z4]),(0,[z1,z30,z748,z3,z4,z6])],[(0,[z7,z1,z2,z38,z3,z4]),(0,[z1,z2,z162,z38,z27,z3]),(0,[z1,z2,z169,z38,z3,z4]),(0,[z1,z2,z418,z114,z4,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 489).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 978).take 487) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1465).take 81) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1546)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [489, 489, 487, 81] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 108).take 111).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 219).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 335).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 440).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [108, 111, 116, 105, 72] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_39885

theorem PEqualNP.Outside.L_meta_39885 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39885.solve