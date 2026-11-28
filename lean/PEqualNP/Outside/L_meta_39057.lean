import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39057

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
  Nat.testBit (4276813032 * 2 ^ 32 + 4276681728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4083921b070dd984#64 ++ 0x22041c90d8386ecc#64 ++ 0xc19f923f0f1fd98b#64 ++ 0xde0cfc91f878fecc#64 : BitVec 256),
   (0x022806c51162e0a9#64 ++ 0x40114036288b1705#64 ++ 0xc6681fc731e3e1ff#64 ++ 0xb63340fe398f1f0f#64 : BitVec 256),
   (0x0850236841b46a11#64 ++ 0x8042811b420da350#64 ++ 0x7870e3f8c1fc7e1f#64 ++ 0x7bc3871fc60fe3f0#64 : BitVec 256),
   (0x1580d800aa001546#64 ++ 0x00ac06c0055000aa#64 ++ 0xbf80fc00fe007ffe#64 ++ 0xfdfc07e007f003ff#64 : BitVec 256),
   (0x9f7d0000fcdb0018#64 ++ 0x04fbe80007e6d800#64 ++ 0xdfff0000ffff8019#64 ++ 0xfefff80007fffc00#64 : BitVec 256),
   (0x3ffefdb600000000#64 ++ 0x01fff7edb0000000#64 ++ 0x3fffffff00000007#64 ++ 0xf1fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e3e1ff 0xb63340fe398f1f0f

def z1 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc7e1f 0x7bc3871fc60fe3f0

def z2 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80fc00fe007ffe 0xfdfc07e007f003ff

def z3 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff00000007 0xf1fffffff8000000

def z4 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923f0f1fd98b 0xde0cfc91f878fecc

def z5 : W := mkw 0x422b06df156fe8a9 0x62115836f8ab7f45 0xc67f1fff31ffe1ff 0xb633f8fff98fff0f

def z6 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0000ffff8019 0xfefff80007fffc00

def z7 : W := mkw 0x0080d80002001546 0x000406c0001000aa 0x2000fc0000007fe6 0x010007e0000003ff

def z8 : W := mkw 0x15000000a8000000 0x00a8000005400000 0x9f800000fe000018 0xfcfc000007f00000

def z9 : W := mkw 0x9f7c0000f8d20018 0x04fbe00007c69000 0x1e600000f0e00010 0x20f3000007870000

def z10 : W := mkw 0x0082901200000000 0x0004148090000000 0x019f923f00000003 0xd00cfc91f8000000

def z11 : W := mkw 0x3f7c6da400000000 0x01fbe36d20000000 0x3e606dc000000004 0x21f3036e00000000

def z12 : W := mkw 0x3ffffdb604090000 0x01ffffedb0204800 0xffffffff0f1f800f 0xfffffffff878fc00

def z13 : W := mkw 0x1580d80000000000 0x00ac06c000000000 0x3f80fc0000000006 0xf1fc07e000000000

def z14 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbffffffffe007fff 0xfdfffffffff003ff

def z15 : W := mkw 0x9ffdd800fedb155e 0x04ffeec007f6d8aa 0xfffffc00ffffffff 0xffffffe007ffffff

def z16 : W := mkw 0xdf7d0209ffdfd99c 0x26fbe8104ffefecc 0xdfff0000ffffd999 0xfefff80007fffecc

def z17 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0x407f000001ff8001 0x0203f800000ffc00

def z18 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xb980e000fe007ff8 0x4dcc070007f003ff

def z19 : W := mkw 0x95010000fcdb0018 0x04a8080007e6d800 0xdf800000ffff8018 0xfefc000007fffc00

def z20 : W := mkw 0x1f7c212000000000 0x00fbe10900000000 0x3fffe3f800000007 0xf1ffff1fc0000000

def z21 : W := mkw 0x4083901306099184 0x22041c8098304c8c 0x818f10070e038180 0x840c788038701c0c

def z22 : W := mkw 0x42ab96df176ff9ad 0x62155cb6f8bb7fcd 0xc7ff9fff3ffff9ff 0xfe3ffcfff9ffffcf

def z23 : W := mkw 0x0a7827ed51f6eab9 0xc053c13f6a8fb755 0xc6781fff31ffe1ff 0xb633c0fff98fff0f

def z24 : W := mkw 0x28d2fdb600000000 0x014697edb0000000 0x3870ffff00000007 0x71c387fff8000000

def z25 : W := mkw 0x80010000fcdb0018 0x0400080007e6d800 0xc0000000ffff8018 0x0e00000007fffc00

def z26 : W := mkw 0x3dd6fdb600000000 0x01eeb7edb0000000 0x3997ffff00000006 0x41ccbffff8000000

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800e000c0007e1e 0x79c00700060003f0

def z28 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x407003f801fc0001 0x0203801fc00fe000

def z29 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x87801c003e0001e0 0x843c00e001f0000f

def z30 : W := mkw 0x0082901202001104 0x0004148090100088 0x819f923f0e00598b 0xdc0cfc91f87002cc

def z31 : W := mkw 0x3f7e25b600000000 0x01fbf12db0000000 0x1fff03ff00000001 0xf0fff81ff8000000

def z32 : W := mkw 0x0228048400000000 0x0011402420000000 0x06081c0700000000 0x803040e038000000

def z33 : W := mkw 0x17280000b8420008 0x00b9400005c21000 0xdfe80000ffe38019 0xfeff400007ff1c00

def z34 : W := mkw 0x0a7827ed51f6eab9 0xc053c13f6a8fb755 0x7878e3ffc1fffe1f 0x7bc3c71ffe0ffff0

def z35 : W := mkw 0x0228048400000000 0x0011402420000000 0x06681fc700000007 0xb03340fe38000000

def z36 : W := mkw 0x0082901200000000 0x0004148090000000 0x0197803800000000 0x400cbc01c0000000

def z37 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x07ff1fff00000001 0x803ff8fff8000000

def z38 : W := mkw 0x0000236841b46a11 0x8000011b420da350 0x6000e3f8c1fc7e1e 0x0b00071fc60fe3f0

def z39 : W := mkw 0x0000000100008080 0x0000000008000404 0x8008100700038180 0x8400408038001c0c

def z40 : W := mkw 0x4083921a070d5904 0x22041c90d0386ac8 0x419782380f1c580b 0x5a0cbc11c078e2c0

def z41 : W := mkw 0x0000020801044800 0x0000001040082240 0x40108238011c580b 0x5a008411c008e2c0

def z42 : W := mkw 0x00000000a8000000 0x0000000005400000 0x80000000fe000018 0x0c00000007f00000

def z43 : W := mkw 0x3ffefdb602001546 0x01fff7edb01000aa 0x3fffffff00007fe7 0xf1fffffff80003ff

def z44 : W := mkw 0x4083da1b070dddc6 0x22041ed0d8386eee 0xe19ffe3f0f1fffef 0xdf0cfff1f878ffff

def z45 : W := mkw 0x022804c410622029 0x4011402620831101 0x06600dc030e02074 0x2033006e01870103

def z46 : W := mkw 0x0a7827ed51f6eab9 0xc053c13f6a8fb755 0xfe78fffff1ffffff 0xfff3c7ffff8fffff

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x86001c00300061fe 0xb43000e00180030f

def z48 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xbfffffff300061ff 0xf5fffffff980030f

def z49 : W := mkw 0x000006c50120e0a1 0x4000003628090705 0x00001fc7000061e6 0x000000fe3800030f

def z50 : W := mkw 0x9f7d06c5fdfbe0b9 0x44fbe8362fefdf05 0xdfff1fc7ffffe1ff 0xfefff8fe3fffff0f

def z51 : W := mkw 0x0000024841b46a11 0x80000012420da350 0x40000000c1fc7e18 0x0a000000060fe3f0

def z52 : W := mkw 0x37aedc9600000000 0x01bd76e4b0000000 0x078f1c0700000000 0x803c78e038000000

def z53 : W := mkw 0x4853237b45bdea91 0xa242991bda2def54 0x787fe3ffc1fffe1f 0x7bc3ff1ffe0ffff0

def z54 : W := mkw 0x00000485000080a0 0x4000002428000405 0x00001c07000001e0 0x000000e03800000f

def z55 : W := mkw 0x02aa949600000000 0x001554a4b0000000 0x07ff9fff00000007 0xf03ffcfff8000000

def z56 : W := mkw 0x02290000144b0008 0x0011480000a25800 0xc7ff00003fff8019 0xfe3ff80001fffc00

def z57 : W := mkw 0x9dd5d800ee991556 0x04eeaec00774c8aa 0xbf97fc00fe1c7ffe 0xfdfcbfe007f0e3ff

def z58 : W := mkw 0x9d550000ec990010 0x04eaa8000764c800 0x19970000ce1c0000 0x48ccb8000670e000

def z59 : W := mkw 0x08d0fb6843b47f57 0x804687db421da3fa 0x7870fff8c1fc7fff 0x7bc387ffc60fe3ff

def z60 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3980e000ce001e00 0x49cc0700067000f0

def z61 : W := mkw 0x0080900002001104 0x0004048000100088 0x87809c003e0079fe 0xfc3c04e001f003cf

def z62 : W := mkw 0x1dd0f928ea941f56 0x80ee87c94754a0fa 0x3990e038ce1c1e00 0x49cc8701c670e0f0

def z63 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x406803c701e3e01f 0x3203401e380f1f00

def z64 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbfffffff3e0001e7 0xf5fffffff9f0000f

def z65 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x818f923f0e03d982 0x840c7c91f8701ecc

def z66 : W := mkw 0x0001000004090000 0x0000080000204800 0xc19f00000f1f8009 0xde0cf8000078fc00

def z67 : W := mkw 0xdfff921bffdfd99c 0x26fffc90dffefecc 0xdfff923fffffd99b 0xfefffc91fffffecc

def z68 : W := mkw 0x40010209070dd984 0x2200081048386ecc 0xc00000000f1fd988 0x0e0000000078fecc

def z69 : W := mkw 0x48d3b37b47bdfb95 0xa2469d9bda3defdc 0xf9fff3ffcfffff9f 0xffcfff9ffe7ffffc

def z70 : W := mkw 0x0000024951f6eab9 0xc00000124a8fb755 0xc0000000f1fffff8 0x0e000000078fffff

def z71 : W := mkw 0x9ffddec5fffbf5ff 0x44ffeef62fffdfaf 0xffffffc7ffffffff 0xfffffffe3fffffff

def z72 : W := mkw 0x000002010100c080 0x0000001008080604 0x0000120700004182 0x000000903800020c

def z73 : W := mkw 0x1580d80000000000 0x00ac06c000000000 0x07801c0000000000 0x803c00e000000000

def z74 : W := mkw 0x0000212000000000 0x0000010900000000 0x2000e3f800000006 0x0100071fc0000000

def z75 : W := mkw 0x4083925b47bdfb95 0xa2041c92da3defdc 0xc19f923fcfffff9b 0xde0cfc91fe7ffffc

def z76 : W := mkw 0x1dd0f960eab03757 0x80ee87cb075581ba 0xbfe0fdc0fee07ffe 0xfdff07ee07f703ff

def z77 : W := mkw 0x4083901a060d1904 0x22041c80d03068c8 0x019780380e1c1800 0x480cbc01c070e0c0

def z78 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x3810e3f8c01c7e06 0x49c0871fc600e3f0

def z79 : W := mkw 0x1580da08ab045d46 0x00ac06d0455822ea 0xff90fe38ff1c7fff 0xfffc87f1c7f8e3ff

def z80 : W := mkw 0x0000236801246a01 0x8000011b40092350 0x2000e3f800007e06 0x0100071fc00003f0

def z81 : W := mkw 0x972d0000bc4b0008 0x04b9680005e25800 0x878f00003e038000 0x843c780001f01c00

def z82 : W := mkw 0x9f7d0484fcdb0018 0x04fbe82427e6d800 0xdfff1fc7ffff801f 0xfefff8fe3ffffc00

def z83 : W := mkw 0x0082921a01044800 0x00041490d0082240 0x419f923f011c580b 0xda0cfc91f808e2c0

def z84 : W := mkw 0x000002411162e0a9 0x40000012088b1705 0x4000000001e38000 0x02000000000f1c00

def z85 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x007f03ff00000001 0x0003f81ff8000000

def z86 : W := mkw 0x0228000010420008 0x0011400000821000 0x8608000030038000 0x8430400001801c00

def z87 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x406803c701e38001 0x0203401e380f1c00

def z88 : W := mkw 0x0080900002001104 0x0004048000100088 0x018080000e001800 0x480c0400007000c0

def z89 : W := mkw 0x3ffef93200000000 0x01fff7c990000000 0x3fffe03800000001 0xf1ffff01c0000000

def z90 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xfe68ffc7f1e3ffff 0xfff347fe3f8f1fff

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x38006000c0002614 0x21c0030006000130

def z92 : W := mkw 0x4083901306099184 0x22041c8098304c8c 0x819f923f0e038183 0xd40cfc91f8701c0c

def z93 : W := mkw 0x0228048410420028 0x4011402420821001 0x06000c0030000060 0x0030006001800003

def z94 : W := mkw 0x6a7f27bf050dc880 0x2353f93df8286e44 0x407f03ff011f8001 0x0203f81ff808fc00

def z95 : W := mkw 0x00000001104280a8 0x4000000008821405 0x80000000300381e0 0x0400000001801c0f

def z96 : W := mkw 0x000002010100c080 0x0000001008080604 0xc00812070103c18b 0x9600409038081e0c

def z97 : W := mkw 0x00000000aa001546 0x00000000055000aa 0xb800e000fe007ffe 0x7dc0070007f003ff

def z98 : W := mkw 0x1dd0d800ea901556 0x00ee86c0075480aa 0xfff0fc00fffc7fff 0xffff87e007ffe3ff

def z99 : W := mkw 0x9f7d2368fdff6a19 0x84fbe91b47effb50 0xffffe3f8fffffe1f 0xffffff1fc7fffff0

def z100 : W := mkw 0x4082921b0304d984 0x22041490d81826cc 0x0000923f00005982 0x00000491f80002cc

def z101 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0x401f023f011f8001 0x0200f811f808fc00

def z102 : W := mkw 0x4083b37b072dfb85 0xa2041d9bd8396fdc 0xe19ff3ff0f1fff8f 0xdf0cff9ff878fffc

def z103 : W := mkw 0x5583da1baf0dddc6 0x22ac1ed0dd786eee 0xff9ffe3fff1fffff 0xfffcfff1fff8ffff

def z104 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff1c00ffffe1ff 0xfefff8e007ffff0f

def z105 : W := mkw 0x3ffefdb610420008 0x01fff7edb0821000 0xffffffff31e3801f 0xf7fffffff98f1c00

def z106 : W := mkw 0x80010000bc4b0008 0x0400080005e25800 0x800000003e038000 0x0400000001f01c00

def z107 : W := mkw 0x15000000a8000000 0x00a8000005400000 0x1e000000f0000010 0x20f0000007800000

def z108 : W := mkw 0x02280485104280a8 0x4011402428821405 0x86081c07300381e0 0x843040e039801c0f

def z109 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x3fffffffce001e07 0xf9fffffffe7000f0

def z110 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19780380f1fd988 0x4e0cbc01c078fecc

def z111 : W := mkw 0x0850212000000000 0x0042810900000000 0x3870e3f800000007 0x71c3871fc0000000

def z112 : W := mkw 0xbffffdb654db0018 0x05ffffedb2a6d800 0x7fffffff01ff8007 0xf3fffffff80ffc00

def z113 : W := mkw 0xbffffdb6fcdb0018 0x05ffffedb7e6d800 0xffffffffffff801f 0xfffffffffffffc00

def z114 : W := mkw 0x0850024841b46a11 0x80428012420da350 0x58700000c1fc7e19 0x7ac38000060fe3f0

def z115 : W := mkw 0x3ffefff601206001 0x01fff7ffb0090300 0x7fffffff01e0601f 0xf3fffffff80f0300

def z116 : W := mkw 0x0850236001206001 0x0042811b00090300 0x7870e3f801e0601f 0x73c3871fc00f0300

def z117 : W := mkw 0x1dd0fb68ebb47f57 0x80ee87db475da3fa 0xfff0fff8fffc7fff 0xffff87ffc7ffe3ff

def z118 : W := mkw 0x3ffeffb70100c080 0x01fff7fdb8080604 0xffffffff0103c18f 0xf7fffffff8081e0c

def z119 : W := mkw 0x9f7d0248fdff6a19 0x84fbe81247effb50 0xdfff0000fffffe19 0xfefff80007fffff0

def z120 : W := mkw 0x0850216840b42a11 0x8042810b4205a150 0x3870e1f8c0fc3e14 0x69c3870fc607e1f0

def z121 : W := mkw 0x0850236041b06211 0x8042811b020d8310 0x786063c0c1e0661f 0x33c3031e060f0330

def z122 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc18f10070f1fd988 0x8e0c78803878fecc

def z123 : W := mkw 0x3ffefffe41b46a11 0x81fff7fff20da350 0x7fffffffc1fc7e1f 0xfbfffffffe0fe3f0

def z124 : W := mkw 0x00809000aa001546 0x00040480055000aa 0x81809000fe007ffa 0xdc0c048007f003ff

def z125 : W := mkw 0x2082fdb600000000 0x010417edb0000000 0x219fffff00000007 0xd10cfffff8000000

def z126 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x067f1fff00000007 0xb033f8fff8000000

def z127 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xffffe000fffffe1f 0xffffff0007fffff0

def z128 : W := mkw 0x9ffdfb68ffff7f5f 0x84ffefdb47fffbfa 0xfffffff8ffffffff 0xffffffffc7ffffff

def z129 : W := mkw 0x9ffd9000fedb111c 0x04ffec8007f6d888 0xdfff9000ffffd99b 0xfefffc8007fffecc

def z130 : W := mkw 0x0080900002001104 0x0004048000100088 0x818090000e00598a 0xdc0c0480007002cc

def z131 : W := mkw 0x5583d81aae0d1d46 0x22ac1ec0d57068ea 0x3997e038ce1c1e00 0x49ccbf01c670e0f0

def z132 : W := mkw 0x08502368ebb47f57 0x8042811b475da3fa 0xf870e3f8fffc7fff 0x7fc3871fc7ffe3ff

def z133 : W := mkw 0x2a7e27f71162e0a9 0x4153f13fb88b1705 0xc67f1fff31e3e1ff 0xb633f8fff98f1f0f

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x019f000000000001 0xd00cf80000000000

def z135 : W := mkw 0x0850212840940a10 0x804281094204a050 0x3810e038c01c1e00 0x49c08701c600e0f0

def z136 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0xc01f123f011fc18b 0x9600f891f808fe0c

def z137 : W := mkw 0x000002410120e0a1 0x4000001208090705 0x00000000000061e0 0x000000000000030f

def z138 : W := mkw 0x6affb7bf070dd984 0x2357fdbdf8386ecc 0xc1ff93ff0f1fd98b 0xde0ffc9ff878fecc

def z139 : W := mkw 0x022804c410622029 0x4011402620831101 0x06681fc730e02077 0xb03340fe39870103

def z140 : W := mkw 0x15004800a8000442 0x00a8024005400022 0x38006000c0000600 0x01c0030006000030

def z141 : W := mkw 0x40010249176ff9ad 0x6200081248bb7fcd 0xc00000003ffff9f8 0x0e00000001ffffcf

def z142 : W := mkw 0x0a7825e450f22239 0xc053c12f22879111 0x3e606dc0f0e02674 0x21f3036e07870133

def z143 : W := mkw 0x8855000044990010 0x0442a8000224c800 0x00170000001c0000 0x0000b8000000e000

def z144 : W := mkw 0x15000000a8000000 0x00a8000005400000 0x878000003e000000 0x843c000001f00000

def z145 : W := mkw 0x0851000044990010 0x004288000224c800 0xd9ff0000cfff8019 0xfecff800067ffc00

def z146 : W := mkw 0x2856213200000000 0x0142b10990000000 0x0017003800000000 0x0000b801c0000000

def z147 : W := mkw 0x0000024841b46a11 0x80000012420da350 0x40108238c1fc7e1b 0x5a008411c60fe3f0

def z148 : W := mkw 0x4851236947bdfb95 0xa242891b4a3defdc 0xf870e3f8cfffff9f 0x7fc3871fc67ffffc

def z149 : W := mkw 0x9f7d0240fdfb6019 0x04fbe81207efdb00 0xdfff03c0ffffe01f 0xfefff81e07ffff00

def z150 : W := mkw 0x3dd6f93200000000 0x01eeb7c990000000 0x39f7e3f800000007 0x71cfbf1fc0000000

def z151 : W := mkw 0x972d0000bc4b0008 0x04b9680005e25800 0xc7ef00003fe38019 0xb63f780001ff1c00

def z152 : W := mkw 0x4083901a060d1904 0x22041c80d03068c8 0x019f923f0e1c1803 0xd80cfc91f870e0c0

def z153 : W := mkw 0x4083901306099184 0x22041c8098304c8c 0xc19f10070f1f8189 0xde0cf8803878fc0c

def z154 : W := mkw 0x1f7c0000a8000000 0x00fbe00005400000 0x9fff0000fe000019 0xfcfff80007f00000

def z155 : W := mkw 0x4083921baf0dddc6 0x22041c90dd786eee 0xc19f923fff1ffffb 0xde0cfc91fff8ffff

def z156 : W := mkw 0x0a7c000000000000 0x0053e00000000000 0x007f000000000001 0x0003f80000000000

def z157 : W := mkw 0x0850000040900010 0x0042800002048000 0x7870e000c1fc7e1f 0x7bc38700060fe3f0

def z158 : W := mkw 0x9f7d2120fcdb0018 0x04fbe90907e6d800 0xffffe3f8ffff801f 0xffffff1fc7fffc00

def z159 : W := mkw 0x40010209070dd984 0x2200081048386ecc 0xc01082380f1fd98b 0x5e008411c078fecc

def z160 : W := mkw 0x3f7c6fec41b46a11 0x81fbe37f620da350 0x7e70eff8c1fc7e1f 0x7bf3877fc60fe3f0

def z161 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x87809c003e0059ea 0xdc3c04e001f002cf

def z162 : W := mkw 0x0850000040900010 0x0042800002048000 0x58700000c1fc0019 0x7ac38000060fe000

def z163 : W := mkw 0x42ab921b174fd98c 0x22155c90d8ba7ecc 0xc7ff923f3fffd99b 0xfe3ffc91f9fffecc

def z164 : W := mkw 0x200225b600000000 0x0100112db0000000 0x000003ff00000000 0x0000001ff8000000

def z165 : W := mkw 0x2a7c25a400000000 0x0153e12d20000000 0x006001c000000000 0x0003000e00000000

def z166 : W := mkw 0x0000024841b46a11 0x80000012420da350 0x7800e000c1fc7e1e 0x7bc00700060fe3f0

def z167 : W := mkw 0x00000000aa001546 0x00000000055000aa 0x86001c00fe007ffe 0xbc3000e007f003ff

def z168 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x787063f8c1fc2615 0x23c3831fc60fe130

def z169 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x587003f8c1fc0019 0x7ac3801fc60fe000

def z170 : W := mkw 0xbf7d6da4fcdb0018 0x05fbeb6d27e6d800 0xffff6dc0ffff801d 0xfffffb6e07fffc00

def z171 : W := mkw 0xbffefdb6f8d20018 0x05fff7edb7c69000 0x3ffffffff0e00017 0xf1ffffffff870000

def z172 : W := mkw 0x1580da01ab00d5c6 0x00ac06d00d5806ae 0xff88fe07ff03ffff 0xfffc47f03ff81fff

def z173 : W := mkw 0x0228000010420008 0x0011400000821000 0xc668000031e38019 0xb6334000018f1c00

def z174 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010823800000003 0x50008411c0000000

def z175 : W := mkw 0x3ffeffbe01044800 0x01fff7fdf0082240 0x7fffffff011c580f 0xfbfffffff808e2c0

def z176 : W := mkw 0x0228048400000000 0x0011402420000000 0x86681fc7300061ff 0xb43340fe3980030f

def z177 : W := mkw 0x15004800a8000442 0x00a8024005400022 0x3e006c00f0002674 0x21f0036007800133

def z178 : W := mkw 0xbffffff7fdfbe0b9 0x45ffffffbfefdf05 0xffffffffffffe1ff 0xffffffffffffff0f

def z179 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0x401f823f011fd80b 0x5a00fc11f808fec0

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060000001e00019 0x32030000000f0000

def z181 : W := mkw 0x9d550000ec990010 0x04eaa8000764c800 0x9f970000fe1c0018 0xfcfcb80007f0e000

def z182 : W := mkw 0x9f7d0208fddf4818 0x04fbe81047eefa40 0xdfff8238ffffd81b 0xfefffc11c7fffec0

def z183 : W := mkw 0x000002010100c080 0x0000001008080604 0x4008020701038001 0x0200401038081c00

def z184 : W := mkw 0x9ffdd800fedb155e 0x04ffeec007f6d8aa 0xdfff1c00ffff81f9 0xfefff8e007fffc0f

def z185 : W := mkw 0x37aeded71162e0a9 0x41bd76f6b88b1705 0xc7ef1fc731e3e1ff 0xb63f78fe398f1f0f

def z186 : W := mkw 0x40010209050dc880 0x2200081048286e44 0x40000000011f8000 0x020000000008fc00

def z187 : W := mkw 0x00000000aa001546 0x00000000055000aa 0x00000000ce001e00 0x08000000067000f0

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800e00000000006 0x71c0070000000000

def z189 : W := mkw 0x2afeb5b600000000 0x0157f5adb0000000 0x01ff93ff00000003 0xd00ffc9ff8000000

def z190 : W := mkw 0x02aa96d71162e0a9 0x401554b6b88b1705 0xc7ff9fff31e3e1ff 0xf63ffcfff98f1f0f

def z191 : W := mkw 0x22aafff71162e0a9 0x411557ffb88b1705 0xe668ffff31e3e1ff 0xb73347fff98f1f0f

def z192 : W := mkw 0x000006c50120e0a1 0x4000003628090705 0xc0081fc70103e1ef 0x960040fe38081f0f

def z193 : W := mkw 0x0000236801246a01 0x8000011b40092350 0x6010e3f8011c7e0f 0x5b00871fc008e3f0

def z194 : W := mkw 0x0a7827ec51f66a39 0xc053c13f628fb351 0x7e70eff8f1fc7e7f 0x7bf3877fc78fe3f3

def z195 : W := mkw 0x7fffffff47bdfb95 0xa3fffffffa3defdc 0xffffffffcfffff9f 0xfffffffffe7ffffc

def z196 : W := mkw 0x1dd0f928ea941f56 0x80ee87c94754a0fa 0xbf90fc38fe1c7ffe 0xfdfc87e1c7f0e3ff

def z197 : W := mkw 0x2a7e27fe41b46a11 0x8153f13ff20da350 0x787fe3ffc1fc7e1f 0x7bc3ff1ffe0fe3f0

def z198 : W := mkw 0x172806c5b962e0a9 0x40b940362dcb1705 0xdfe81fc7ffe3e1ff 0xfeff40fe3fff1f0f

def z199 : W := mkw 0x0001000004090000 0x0000080000204800 0x019700000e1c0000 0x480cb8000070e000

def z200 : W := mkw 0x0a78236851f66a19 0x8053c11b428fb350 0xfe78e3f8f1fffe1f 0xfff3c71fc78ffff0

def z201 : W := mkw 0x4083901b060d9984 0x22041c80d8306ccc 0x819f903f0e1f9980 0xcc0cfc81f870fccc

def z202 : W := mkw 0x77afdc9706099184 0x23bd7ee4b8304c8c 0x878f1c070e038180 0x843c78e038701c0c

def z203 : W := mkw 0x2082fdb600000000 0x010417edb0000000 0x2000ffff00000006 0x010007fff8000000

def z204 : W := mkw 0x5fff921b070dd984 0x22fffc90d8386ecc 0xdfff923f0f1fd98b 0xfefffc91f878fecc

def z205 : W := mkw 0x0850212040900010 0x0042810902048000 0x7870e3f8c1fc001f 0x7bc3871fc60fe000

def z206 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x3860e3f8c0e07e16 0x21c3071fc60703f0

def z207 : W := mkw 0x0228048400000000 0x0011402420000000 0x006803c700000001 0x0003401e38000000

def z208 : W := mkw 0x000002411162e0a9 0x40000012088b1705 0xc000000031e3e1f8 0x06000000018f1f0f

def z209 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3980fc00ce007fe6 0x49cc07e0067003ff

def z210 : W := mkw 0x0850000040900010 0x0042800002048000 0x4070000001fc0001 0x02038000000fe000

def z211 : W := mkw 0x3f7c6da400000000 0x01fbe36d20000000 0x3fff6dc000000005 0xf1fffb6e00000000

def z212 : W := mkw 0x0850212840940a10 0x804281094204a050 0x00100038001c0000 0x00008001c000e000

def z213 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x419f823f0f1f9801 0x4a0cfc11f878fcc0

def z214 : W := mkw 0x0080900000000000 0x0004048000000000 0x0180900000000002 0xd00c048000000000

def z215 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x46681fc701e38007 0xb23340fe380f1c00

def z216 : W := mkw 0x9f7d27edfdffeab9 0xc4fbe93f6fefff55 0xffffffffffffffff 0xffffffffffffffff

def z217 : W := mkw 0x7dd7fb3b070dd984 0x23eebfd9d8386ecc 0xf99ff23f0f1fd98b 0xdfccff91f878fecc

def z218 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3ff7edf800000004 0x61ffbf6fc0000000

def z219 : W := mkw 0x9d552368edbd6a11 0x84eaa91b476deb50 0x79f7e3f8cffc7e1f 0x7bcfbf1fc67fe3f0

def z220 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffffc0007e1f 0xf9fffffffe0003f0

def z221 : W := mkw 0x88510000fcdb0018 0x0442880007e6d800 0xd8700000ffff8019 0x7ec3800007fffc00

def z222 : W := mkw 0x0080d800aa001546 0x000406c0055000aa 0xa000fc00fe007ffe 0x0d0007e007f003ff

def z223 : W := mkw 0x022906c5156be0a9 0x4011483628ab5f05 0xc7ff1fc73fffe1ff 0xfe3ff8fe39ffff0f

def z224 : W := mkw 0x3dd6f93200000000 0x01eeb7c990000000 0x3997e03800000000 0x41ccbf01c0000000

def z225 : W := mkw 0x00000000aa001546 0x00000000055000aa 0x800000003e0001e0 0x0400000001f0000f

def z226 : W := mkw 0x8a7d06c555fbe0b9 0x4453e8362aafdf05 0xc67f1fc731ffe1ff 0xb633f8fe398fff0f

def z227 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x87801c00fe007ff8 0x8c3c00e007f003ff

def z228 : W := mkw 0x15004800aa001546 0x00a80240055000aa 0xbe006c00fe007ffc 0x2df0036007f003ff

def z229 : W := mkw 0x0000024001206001 0x0000001200090300 0x406003c001e0601f 0x3203001e000f0300

def z230 : W := mkw 0x4083925b072df985 0x22041c92d8396fcc 0xc1ff93ff0ffff99f 0xfe0ffc9ff87fffcc

def z231 : W := mkw 0x95050000ac090000 0x04a8280005604800 0x018700000e000000 0x000c380000700000

def z232 : W := mkw 0x4082da1b0304ddc6 0x220416d0d81826ee 0x2000fe3f00007fe6 0x010007f1f80003ff

def z233 : W := mkw 0x0000020801044800 0x0000001040082240 0x40000000011c5808 0x0a0000000008e2c0

def z234 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0xc1ff00000fff8009 0xde0ff800007ffc00

def z235 : W := mkw 0xffffffbfffdfd99c 0x27fffffdfffefecc 0xffffffffffffd99f 0xfffffffffffffecc

def z236 : W := mkw 0x0000000010420008 0x0000000000821000 0xc000000031e38018 0x06000000018f1c00

def z237 : W := mkw 0x02280485104280a8 0x4011402428821405 0xc6681c0731e381f9 0xb63340e0398f1c0f

def z238 : W := mkw 0x42aa96df1366f9ad 0x621554b6f89b37cd 0xc6689fff31e3f9ff 0xb63344fff98f1fcf

def z239 : W := mkw 0x0000004000202001 0x0000000200010100 0x006001c000e02014 0x2003000e00070100

def z240 : W := mkw 0x3ffefffe41b46a11 0x81fff7fff20da350 0x7fffffff01fc0007 0xf3fffffff80fe000

def z241 : W := mkw 0x3ffefffeebb47f57 0x81fff7fff75da3fa 0xfffffffffffc7fff 0xffffffffffffe3ff

def z242 : W := mkw 0x3ffefff71162e0a9 0x41fff7ffb88b1705 0x7fffffff01e38007 0xf3fffffff80f1c00

def z243 : W := mkw 0x15000000a8000000 0x00a8000005400000 0x9f801c00fe0061fe 0xfcfc00e007f0030f

def z244 : W := mkw 0x4082921b0304d984 0x22041490d81826cc 0x019f923f00005983 0xd00cfc91f80002cc

def z245 : W := mkw 0x00010208050d4800 0x0000081040286a40 0xc19f82380f1fd80b 0xde0cfc11c078fec0

def z246 : W := mkw 0x3ffcfda400000000 0x01ffe7ed20000000 0x3fe0fdc000000006 0xf1ff07ee00000000

def z247 : W := mkw 0x022802011142c088 0x00114010088a1604 0xc668120731e3c19b 0xb6334090398f1e0c

def z248 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f123f0f1f8181 0x860cf891f878fc0c

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x06001c0000000006 0xb03000e000000000

def z250 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x5e7f0000f1ff8011 0x22f3f800078ffc00

def z251 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc1e01 0x4bc3871fc60fe0f0

def z252 : W := mkw 0x3ffefdf640b02211 0x81fff7efb2058110 0x3fffffffc0e02617 0xf1fffffffe070130

def z253 : W := mkw 0x17284ec5b962e4eb 0x40b942762dcb1727 0xfe687fc7f1e3e7ff 0xb7f343fe3f8f1f3f

def z254 : W := mkw 0xbf7c6da4f8d20018 0x05fbe36d27c69000 0x3e606dc0f0e00014 0x21f3036e07870000

def z255 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x59ff0000cfff8001 0x4acff800067ffc00

def z256 : W := mkw 0x9d552128ec9d0a10 0x84eaa9094764e850 0x3997e038ce1c1e00 0x49ccbf01c670e0f0

def z257 : W := mkw 0x4082921b0304d984 0x22041490d81826cc 0x4010923f011c598b 0x5a008491f808e2cc

def z258 : W := mkw 0x0000024001206001 0x0000001200090300 0x4000000001e06018 0x02000000000f0300

def z259 : W := mkw 0x9f7d0485fcdb80b8 0x44fbe8242fe6dc05 0xdfff1c07ffff81f9 0xfefff8e03ffffc0f

def z260 : W := mkw 0x4001024947bdfb95 0xa20008124a3defdc 0xc0000000cfffff98 0x0e000000067ffffc

def z261 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc06813c701e3c18b 0x9603409e380f1e0c

def z262 : W := mkw 0x022806cd1166e8a9 0x40114036688b3745 0xc6789fff31fff9ff 0xfe33c4fff98fffcf

def z263 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc66803c731e38019 0xb633401e398f1c00

def z264 : W := mkw 0x3f7c6fe51162e0a9 0x41fbe37f288b1705 0xfe687fc731e3e1ff 0xb7f343fe398f1f0f

def z265 : W := mkw 0x0000024841b46a11 0x80000012420da350 0x4000000001fc0000 0x02000000000fe000

def z266 : W := mkw 0x3ffefdb6a8000000 0x01fff7edb5400000 0xbffffffffe00001f 0xfdfffffffff00000

def z267 : W := mkw 0xc0010209ffdfd99c 0x260008104ffefecc 0xc0000000ffffd998 0x0e00000007fffecc

def z268 : W := mkw 0x0a7825a400000000 0x0053c12d20000000 0x3e78ffff00000007 0xf1f3c7fff8000000

def z269 : W := mkw 0x422b06df156fe8a9 0x62115836f8ab7f45 0x407f03ff01ff8001 0x0203f81ff80ffc00

def z270 : W := mkw 0x1d54000000000000 0x00eaa00000000000 0x1997000000000000 0x40ccb80000000000

def z271 : W := mkw 0x022804c51062a0a9 0x4011402628831505 0x86681dc730e3a1f4 0xa43340ee39871d0f

def z272 : W := mkw 0x1582d812aa001546 0x00ac16c0955000aa 0xbf9ffe3ffe007fff 0xfdfcfff1fff003ff

def z273 : W := mkw 0x3ffefdf610622029 0x41fff7efb0831101 0x3fffffff30e02077 0xf1fffffff9870103

def z274 : W := mkw 0x9f7c2368f9f66a19 0x84fbe11b47cfb350 0x7e70e3f8f1fc7e1f 0x7bf3871fc78fe3f0

def z275 : W := mkw 0x3ffefdb7104280a8 0x41fff7edb8821405 0xbfffffff300381e7 0xf5fffffff9801c0f

def z276 : W := mkw 0x0000000040900010 0x0000000002048000 0x40000000c1fc0018 0x0a000000060fe000

def z277 : W := mkw 0x0850212000000000 0x0042810900000000 0x007003f800000001 0x0003801fc0000000

def z278 : W := mkw 0x0000024001206001 0x0000001200090300 0xc6601fc031e061ff 0xb63300fe018f030f

def z279 : W := mkw 0x2082fdb602001546 0x010417edb01000aa 0x2000ffff00007fe6 0x010007fff80003ff

def z280 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3e00fc00f0007ff6 0x21f007e0078003ff

def z281 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x39ffe3ff00000001 0x41cfff1ff8000000

def z282 : W := mkw 0x3ffefff70120e0a1 0x41fff7ffb8090705 0x3fffffff000061e7 0xf1fffffff800030f

def z283 : W := mkw 0x0850216040b02211 0x8042810b02058110 0x386061c0c0e02614 0x21c3030e06070130

def z284 : W := mkw 0x972c0000b8420008 0x04b9600005c21000 0x0600000030000000 0x0030000001800000

def z285 : W := mkw 0x48d3b37a47bd7b15 0xa2469d9bd23debd8 0x79f7e3f8cffc7e1f 0x7bcfbf1fc67fe3f0

def z286 : W := mkw 0x1580d80000000000 0x00ac06c000000000 0x3f80fc00c0007e1e 0xf9fc07e0060003f0

def z287 : W := mkw 0x1580fb68ab247f47 0x80ac07db455923fa 0xbf80fff8fe007ffe 0xfdfc07ffc7f003ff

def z288 : W := mkw 0x022802411162e0a9 0x40114012088b1705 0xc668000031e3e1f9 0xb6334000018f1f0f

def z289 : W := mkw 0x00000000aa001546 0x00000000055000aa 0x80000000fe007ff8 0x0c00000007f003ff

def z290 : W := mkw 0x1580d800a8000000 0x00ac06c005400000 0xbf80fc00fe00001e 0xfdfc07e007f00000

def z291 : W := mkw 0x2a7e27fe41b46a11 0x8153f13ff20da350 0x407f03ff01fc0001 0x0203f81ff80fe000

def z292 : W := mkw 0x9f7d2128fcdf0a18 0x84fbe90947e6f850 0xffffe038ffff9e19 0xffffff01c7fffcf0

def z293 : W := mkw 0x17a8dec5bb62f5ef 0x40bd46f62ddb17af 0xffe8ffc7ffe3ffff 0xffff47fe3fff1fff

def z294 : W := mkw 0xbffffffefdff6a19 0x85fffffff7effb50 0xfffffffffffffe1f 0xfffffffffffffff0

def z295 : W := mkw 0x9ffcd800fad2155e 0x04ffe6c007d690aa 0xbfe0fc00fee07ffe 0xfdff07e007f703ff

def z296 : W := mkw 0x3ffefdbe40940a10 0x81fff7edf204a050 0x3fffffffc01c1e07 0xf9fffffffe00e0f0

def z297 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3f80fc00ce001e06 0xf9fc07e0067000f0

def z298 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6081c0731e3e1f8 0x863040e0398f1f0f

def z299 : W := mkw 0x1d502368e9b46a11 0x80ea811b474da350 0xfff0e3f8fffc7e1f 0xffff871fc7ffe3f0

def z300 : W := mkw 0x48d2b37b43b4fb95 0xa246959bda1da7dc 0x7870f3ffc1fc7f9f 0x7bc3879ffe0fe3fc

def z301 : W := mkw 0x42ab96df176ff9ad 0x62155cb6f8bb7fcd 0xc1ff93ff0fffd98b 0xde0ffc9ff87ffecc

def z302 : W := mkw 0x7fffffbf070dd984 0x23fffffdf8386ecc 0xffffffff0f1fd98f 0xfffffffff878fecc

def z303 : W := mkw 0x000006c50120e0a1 0x4000003628090705 0x86001fc7300061fe 0xb43000fe3980030f

def z304 : W := mkw 0x9d550000ec990010 0x04eaa8000764c800 0x59f70000cffc0019 0x7acfb800067fe000

def z305 : W := mkw 0x0850212840940a10 0x804281094204a050 0x7870e038c1fc1e19 0x7bc38701c60fe0f0

def z306 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xa780fc003e007fe6 0x853c07e001f003ff

def z307 : W := mkw 0x0000480000000442 0x0000024000000022 0x20006c0000002664 0x0100036000000133

def z308 : W := mkw 0x37aedc96aa001546 0x01bd76e4b55000aa 0xbf8ffc07fe007ffe 0xfdfc7fe03ff003ff

def z309 : W := mkw 0x40819209070dd984 0x22040c9048386ecc 0xc18090000f1fd98a 0xde0c04800078fecc

def z310 : W := mkw 0x02a896c51362f1ad 0x401544b6289b178d 0xc7e89fc73fe3f9ff 0xfe3f44fe39ff1fcf

def z311 : W := mkw 0x8a7c000050d20018 0x0453e00002869000 0x0060000000e00000 0x0003000000070000

def z312 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc000923f0f1fd98a 0x0e000491f878fecc

def z313 : W := mkw 0x88512368fdff6a19 0x8442891b47effb50 0xf870e3f8fffffe1f 0x7fc3871fc7fffff0

def z314 : W := mkw 0x9f7c2160f8f22219 0x84fbe10b07c79110 0x3e6061c0f0e02614 0x21f3030e07870130

def z315 : W := mkw 0x0083901204090000 0x00041c8090204800 0xc19f923f0f1f800b 0xde0cfc91f878fc00

def z316 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x018000000e000000 0x000c000000700000

def z317 : W := mkw 0x000006c50120e0a1 0x4000003628090705 0x000003c700000000 0x0000001e38000000

def z318 : W := mkw 0x3ffefff71162e0a9 0x41fff7ffb88b1705 0xffffffff31e3e1ff 0xf7fffffff98f1f0f

def z319 : W := mkw 0x0a7806c551f2e0b9 0x4053c0362a8f9705 0xde781fc7f1ffe1ff 0xfef3c0fe3f8fff0f

def z320 : W := mkw 0x97add800be4b154e 0x04bd6ec005f258aa 0x878f1c003e0381e0 0x843c78e001f01c0f

def z321 : W := mkw 0x1f7c000000000000 0x00fbe00000000000 0x1fff000000000001 0xf0fff80000000000

def z322 : W := mkw 0x000002090104c880 0x0000001048082644 0xc018923f011fd98b 0xde00c491f808fecc

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000601e 0x3000000000000300

def z324 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x387fe3ff00000007 0x71c3ff1ff8000000

def z325 : W := mkw 0x48d3b13a469d1b14 0xa2469d89d234e8d8 0x3997e038ce1c1e00 0x49ccbf01c670e0f0

def z326 : W := mkw 0x0080920803045904 0x00040490401822c8 0xc19092380f1c598b 0xde0c8491c078e2cc

def z327 : W := mkw 0x0a78000050d20018 0x0053c00002869000 0xde780000f1ff8019 0xfef3c000078ffc00

def z328 : W := mkw 0x0850236941b4ea91 0x8042811b4a0da754 0xf878f3ffc1ffff9f 0xffc3c79ffe0ffffc

def z329 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3f80ec00fe003e74 0x69fc076007f001f3

def z330 : W := mkw 0x15004800a8000442 0x00a8024005400022 0xbe007c00f00067fe 0xb5f003e00780033f

def z331 : W := mkw 0x3ffefdb6a8000442 0x01fff7edb5400022 0x3ffffffff0002677 0xf1ffffffff800133

def z332 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x1ff70000fefc0010 0x68ffb80007f7e000

def z333 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e381e1 0x863340fe398f1c0f

def z334 : W := mkw 0x08d2b13200000000 0x0046958990000000 0x39fff3ff00000007 0xf1cfff9ff8000000

def z335 : W := mkw 0xbfffdc96fcdb0018 0x05fffee4b7e6d800 0xdfff1c07ffff8019 0xfefff8e03ffffc00

def z336 : W := mkw 0x15000000a8000000 0x00a8000005400000 0xbf80e000fe007e1e 0xfdfc070007f003f0

def z337 : W := mkw 0x0228000010420008 0x0011400000821000 0xc6681c0031e3e1ff 0xb63340e0018f1f0f

def z338 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc79f9e3f3f1ff9ff 0xfe3cfcf1f9f8ffcf

def z339 : W := mkw 0x0000024841b46a11 0x80000012420da350 0x406003c0c1fc7e1f 0x3a03001e060fe3f0

def z340 : W := mkw 0x42ab969f174fd9ac 0x62155cb4f8ba7ecd 0xc79f9e3f3f1fd9eb 0xde3cfcf1f9f8fecf

def z341 : W := mkw 0x7ffeffbf0304d984 0x23fff7fdf81826cc 0x3fffffff00005987 0xf1fffffff80002cc

def z342 : W := mkw 0x408296df0324f9a5 0x620414b6f81927cd 0x00009fff000079e6 0x000004fff80003cf

def z343 : W := mkw 0x1581d800ae091546 0x00ac0ec0057048aa 0xff9ffc00ff1fffff 0xfffcffe007f8ffff

def z344 : W := mkw 0x5583da1baf0dddc6 0x22ac1ed0dd786eee 0xc79f9e3f3f1fd9eb 0xde3cfcf1f9f8fecf

def z345 : W := mkw 0x37aefdb600000000 0x01bd77edb0000000 0x278fffff00000006 0x813c7ffff8000000

def z346 : W := mkw 0x15010000ac090000 0x00a8080005604800 0xdf9f0000ff1f8019 0xfefcf80007f8fc00

def z347 : W := mkw 0x42ab969f070dd984 0x22155cb4f8386ecc 0xc7ff9fff0f1fd98f 0xfe3ffcfff878fecc

def z348 : W := mkw 0xbffffdb6ec990010 0x05ffffedb764c800 0x3fffffffce1c0007 0xf9fffffffe70e000

def z349 : W := mkw 0x9f7d4800fcdb045a 0x04fbea4007e6d822 0xffff6c00ffffa67d 0xfffffb6007fffd33

def z350 : W := mkw 0x3f7e6db600000000 0x01fbf36db0000000 0x3e7f6fff00000005 0x21f3fb7ff8000000

def z351 : W := mkw 0x5583921baf0dd984 0x22ac1c90dd786ecc 0xdf9f923fff1fd99b 0xfefcfc91fff8fecc

def z352 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x401f923f011fd983 0x0200fc91f808fecc

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x006003c000000007 0x3003001e00000000

def z354 : W := mkw 0x40010209070dd984 0x2200081048386ecc 0xc00812070f1fd98b 0x9e0040903878fecc

def z355 : W := mkw 0x02280485104280a8 0x4011402428821405 0x86081c073003e1fe 0xb43040e039801f0f

def z356 : W := mkw 0x9f7c0000f8d20018 0x04fbe00007c69000 0x5e700000f1fc0019 0x7af38000078fe000

def z357 : W := mkw 0x9f7c0000f8d20018 0x04fbe00007c69000 0x1fff0000f0e00011 0xf0fff80007870000

def z358 : W := mkw 0x3dd6f932aa001546 0x01eeb7c9955000aa 0x3997e038ce001e00 0x49ccbf01c67000f0

def z359 : W := mkw 0x4083921b050dc880 0x22041c90d8286e44 0x419f923f011f8003 0xd20cfc91f808fc00

def z360 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x40681fc701e3e1e7 0x020340fe380f1f0f

def z361 : W := mkw 0x6083ffbf070dd984 0x23041ffdf8386ecc 0xe19fffff0f1fd98f 0xdf0cfffff878fecc

def z362 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7810e038c1fc7e18 0x4bc08701c60fe3f0

def z363 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x46680fc731e3a075 0x2233407e398f1d03

def z364 : W := mkw 0x80010000fcdb0018 0x0400080007e6d800 0xc19f0000ffff8019 0xde0cf80007fffc00

def z365 : W := mkw 0x9f7d0000ec990010 0x04fbe8000764c800 0x1fff0000ce1c0001 0xf8fff8000670e000

def z366 : W := mkw 0x17a8dcc4ba62356f 0x40bd46e625d311ab 0xbfe0fdc0fee07ffe 0xfdff07ee07f703ff

def z367 : W := mkw 0x4083901a060d1904 0x22041c80d03068c8 0xc19f80380f1f9809 0xde0cfc01c078fcc0

def z368 : W := mkw 0x8a7d236855ff6a19 0x8453e91b42affb50 0x407f03f801ff8001 0x0203f81fc00ffc00

def z369 : W := mkw 0x40010209af0dddc6 0x220008104d786eee 0xc0000000ff1ffff8 0x0e00000007f8ffff

def z370 : W := mkw 0x000002411162e0a9 0x40000012088b1705 0xc008120731e3e1fb 0x96004090398f1f0f

def z371 : W := mkw 0x9ffdd800fedb155e 0x04ffeec007f6d8aa 0xffffe000ffff9e19 0xffffff0007fffcf0

def z372 : W := mkw 0x9d550000fcdb0018 0x04eaa80007e6d800 0xd9970000ffff8018 0x4eccb80007fffc00

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0xc008000001038009 0x9600400000081c00

def z374 : W := mkw 0x02280485104280a8 0x4011402428821405 0x0008000700038000 0x0000400038001c00

def z375 : W := mkw 0x0000236801246a01 0x8000011b40092350 0x3800e3f8c0007e1e 0x79c0071fc60003f0

def z376 : W := mkw 0x15004800a8000442 0x00a8024005400022 0xbf806c00fe00267c 0xfdfc036007f00133

def z377 : W := mkw 0x1dd0f92000000000 0x00ee87c900000000 0x3ff0fff800000007 0xf1ff87ffc0000000

def z378 : W := mkw 0x0000000002001104 0x0000000000100088 0x800000000e005988 0x0c000000007002cc

def z379 : W := mkw 0x0000020001004000 0x0000001000080200 0x400002000100400b 0x1200001000080200

def z380 : W := mkw 0x9f7c04c4f8f22039 0x44fbe02627c79101 0x1e600dc0f0e02074 0x20f3006e07870103

def z381 : W := mkw 0x48d3921b479dd994 0x22469c90da3ceecc 0xd9ff923fcfffd99b 0xfecffc91fe7ffecc

def z382 : W := mkw 0x0002001200000000 0x0000100090000000 0x001f023f00000001 0x0000f811f8000000

def z383 : W := mkw 0x372c4c8400000000 0x01b9626420000000 0x06000c0000000000 0x0030006000000000

def z384 : W := mkw 0x0081900006091104 0x00040c8000304888 0xc19f90000f1fd98b 0xde0cfc800078fecc

def z385 : W := mkw 0x9fff9012fcdb0018 0x04fffc8097e6d800 0xdfff923fffff801b 0xfefffc91fffffc00

def z386 : W := mkw 0x0000024001206001 0x0000001200090300 0x7860e3c0c1e07e1f 0x7bc3071e060f03f0

def z387 : W := mkw 0x57abdedfbf6ffdef 0x62bd5ef6fdfb7fef 0xffffffffffffffff 0xffffffffffffffff

def z388 : W := mkw 0x008292130100c080 0x0004149098080604 0xc19f923f0103c18b 0xd60cfc91f8081e0c

def z389 : W := mkw 0x1580da48ebb47f57 0x80ac06d2475da3fa 0xff80fc00fffc7ffe 0xfffc07e007ffe3ff

def z390 : W := mkw 0x2082fffe01246a01 0x810417fff0092350 0x2000ffff00007e06 0x010007fff80003f0

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001c00000061e6 0x000000e00000030f

def z392 : W := mkw 0x00000241bb62f5ef 0x400000120ddb17af 0xc0000000ffe3fff8 0x0e00000007ff1fff

def z393 : W := mkw 0x37aedc96aa001546 0x01bd76e4b55000aa 0x878f1c073e0001e0 0x843c78e039f0000f

def z394 : W := mkw 0x0850216040b02211 0x8042810b02058110 0x3870e3f8c0e02617 0x71c3871fc6070130

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000c0030002074 0x2030006001800103

def z396 : W := mkw 0x02280485104280a8 0x4011402428821405 0x86681fc7300381e7 0xb43340fe39801c0f

def z397 : W := mkw 0x8001000054db0018 0x0400080002a6d800 0x4000000001ff8000 0x02000000000ffc00

def z398 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x9f801c00fe0001f8 0xfcfc00e007f0000f

def z399 : W := mkw 0x3f7c6da4a8000442 0x01fbe36d25400022 0x3e606dc0f0002674 0x21f3036e07800133

def z400 : W := mkw 0x9f7c4800f8d2045a 0x04fbe24007c69022 0x3e606c00f0e02674 0x21f3036007870133

def z401 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xc7ff00003fff8001 0x863ff80001fffc00

def z402 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xde600000ffff8018 0x2ef3000007fffc00

def z403 : W := mkw 0xd7af9013be4b918c 0x26bd7c809df25c8c 0x878f10073e038180 0x843c788039f01c0c

def z404 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80fc00fe001fe0 0xcdfc07e007f000ff

def z405 : W := mkw 0x3ffefff7bb62f5ef 0x41fff7ffbddb17af 0xffffffffffe3ffff 0xffffffffffff1fff

def z406 : W := mkw 0x82290000fcdb0018 0x0411480007e6d800 0xc6680000ffff8019 0xbe33400007fffc00

def z407 : W := mkw 0x9d550000ec990010 0x04eaa8000764c800 0xd99f0000cf1f8009 0xdeccf8000678fc00

def z408 : W := mkw 0x0080d80002001546 0x000406c0001000aa 0xa600fc0030007ffe 0xb53007e0018003ff

def z409 : W := mkw 0x0000024801246a01 0x8000001240092350 0x0000000000007e00 0x00000000000003f0

def z410 : W := mkw 0x37aedc9600000000 0x01bd76e4b0000000 0x079f9e3f00000003 0xd03cfcf1f8000000

def z411 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc06803c731e3e1f9 0x0603401e398f1f0f

def z412 : W := mkw 0x8a7d06c555fbe0b9 0x4453e8362aafdf05 0x407f03c701ff8001 0x0203f81e380ffc00

def z413 : W := mkw 0x5583da1b070dd984 0x22ac1ed0d8386ecc 0xff9ffe3f0f1fd98f 0xfffcfff1f878fecc

def z414 : W := mkw 0xc083921bffdfd99c 0x26041c90dffefecc 0xc19f923fffffd99b 0xde0cfc91fffffecc

def z415 : W := mkw 0x3f7c6da400000000 0x01fbe36d20000000 0x3e687fc700000007 0xb1f343fe38000000

def z416 : W := mkw 0x0082901200000000 0x0004148090000000 0x018f100700000000 0x800c788038000000

def z417 : W := mkw 0x1f7c000000000000 0x00fbe00000000000 0x1e60000000000000 0x20f3000000000000

def z418 : W := mkw 0xdfffb37bfffffb9d 0xa6fffd9bdfffffdc 0xfffff3ffffffff9f 0xffffff9ffffffffc

def z419 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x786061c0c1fc7e1c 0x2bc3030e060fe3f0

def z420 : W := mkw 0x222e049600000000 0x01117024b0000000 0x000f000700000000 0x0000780038000000

def z421 : W := mkw 0x022806c5bb62f5ef 0x401140362ddb17af 0xc6681fc7ffe3ffff 0xbe3340fe3fff1fff

def z422 : W := mkw 0x0001000004090000 0x0000080000204800 0xc00000000f1f8008 0x0e0000000078fc00

def z423 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3e60ffff00000006 0x21f307fff8000000

def z424 : W := mkw 0x022806851142c0a8 0x40114034288a1605 0xc6081e073103c1eb 0x963040f039881e0f

def z425 : W := mkw 0x0850216040b02211 0x8042810b02058110 0x787061c0c1fc261d 0x7bc3830e060fe130

def z426 : W := mkw 0x4082901a02041904 0x22041480d01020c8 0x0000803800001800 0x00000401c00000c0

def z427 : W := mkw 0x022827ed1166eaa9 0xc011413f688b3755 0xe668ffff31e3ffff 0xb73347fff98f1fff

def z428 : W := mkw 0x022806c50120e0a1 0x4011403628090705 0x06681fc7000061e7 0xb03340fe3800030f

def z429 : W := mkw 0x0000000840940a10 0x800000004204a050 0x00000000c01c1e00 0x080000000600e0f0

def z430 : W := mkw 0x3ffefdb640900010 0x01fff7edb2048000 0x7fffffffc1fc001f 0xfbfffffffe0fe000

def z431 : W := mkw 0x0080dec50320f5e7 0x400406f6281907af 0x2000ffc700007fe6 0x010007fe380003ff

def z432 : W := mkw 0x9f7c0000f8d20018 0x04fbe00007c69000 0xde680000f1e38019 0xb6f34000078f1c00

def z433 : W := mkw 0x1d500000e8900010 0x00ea800007448000 0xdff00000fffc0019 0xfeff800007ffe000

def z434 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x9f9f0000fe1f8000 0xccfcf80007f0fc00

def z435 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f801fc0007 0x73c3871fc00fe000

def z436 : W := mkw 0x00000000a8000442 0x0000000005400022 0x00000000f0002670 0x0000000007800133

def z437 : W := mkw 0x4082b37b0324fb85 0xa204159bd81927dc 0x2000f3ff00007f86 0x0100079ff80003fc

def z438 : W := mkw 0x4853237b45bdea91 0xa242991bda2def54 0x407f03ff01ff8001 0x0203f81ff80ffc00

def z439 : W := mkw 0x6082ffbf0304d984 0x230417fdf81826cc 0x2000ffff00005986 0x010007fff80002cc

def z440 : W := mkw 0x1f7c000010420008 0x00fbe00000821000 0xdfff000031e38019 0xf6fff800018f1c00

def z441 : W := mkw 0xbffff932fcdb0018 0x05ffffc997e6d800 0xffffe038ffff8019 0xffffff01c7fffc00

def z442 : W := mkw 0xca7f021b55dfc898 0x2653f810daaefe44 0x407f023f01ff8001 0x0203f811f80ffc00

def z443 : W := mkw 0x17a8dec5bb62f5ef 0x40bd46f62ddb17af 0xc7e81fc73fe3e1ff 0xb63f40fe39ff1f0f

def z444 : W := mkw 0x9f7d2160fcfb2219 0x84fbe90b07e7d910 0xffff61c0ffffa61d 0xfffffb0e07fffd30

def z445 : W := mkw 0x7ffffdb706099184 0x23ffffedb8304c8c 0xbfffffff0e038187 0xf5fffffff8701c0c

def z446 : W := mkw 0x0850216040b02211 0x8042810b02058110 0x3860e1c0c0e07e1e 0x79c3070e060703f0

def z447 : W := mkw 0x0850232841944a10 0x80428119420ca250 0x7810e238c11c5e0b 0x5bc08711c608e2f0

def z448 : W := mkw 0x0850212000000000 0x0042810900000000 0x3870e3f8c0007e1f 0x79c3871fc60003f0

def z449 : W := mkw 0x3dd6f932aa001546 0x01eeb7c9955000aa 0xbf97fc38fe007ffe 0xfdfcbfe1c7f003ff

def z450 : W := mkw 0x0228000010420008 0x0011400000821000 0x0660000030e00010 0x2033000001870000

def z451 : W := mkw 0x0000004040b02211 0x8000000202058110 0x00000000c0e02610 0x0000000006070130

def z452 : W := mkw 0xdfff9013fedb919c 0x26fffc809ff6dc8c 0xdfff1007ffff8199 0xfefff8803ffffc0c

def z453 : W := mkw 0x80000000f8d20018 0x0400000007c69000 0x00000000f0e00010 0x0000000007870000

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe00fc00f0007ffe 0xfdf007e0078003ff

def z455 : W := mkw 0x3f7c6da400000000 0x01fbe36d20000000 0x3e70eff800000007 0x71f3877fc0000000

def z456 : W := mkw 0x972d06c5bd6be0a9 0x44b968362deb5f05 0xc7ef1fc73fe3e1ff 0xb63f78fe39ff1f0f

def z457 : W := mkw 0xbdd7f932ec990010 0x05eebfc99764c800 0x3997e038ce1c0000 0x49ccbf01c670e000

def z458 : W := mkw 0xb7afdc96bc4b0008 0x05bd7ee4b5e25800 0x878f1c073e038000 0x843c78e039f01c00

def z459 : W := mkw 0x0850000040900010 0x0042800002048000 0x18100000c01c0000 0x48c080000600e000

def z460 : W := mkw 0x0000236801246a01 0x8000011b40092350 0x000003f800000000 0x0000001fc0000000

def z461 : W := mkw 0x15004800a8000442 0x00a8024005400022 0x06000c0030000060 0x0030006001800003

def z462 : W := mkw 0x0080d80000000000 0x000406c000000000 0x2000fc0000000006 0x010007e000000000

def z463 : W := mkw 0x80010000ec990010 0x040008000764c800 0x00000000ce1c0000 0x080000000670e000

def z464 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x06601fc730e061f6 0x203300fe3987030f

def z465 : W := mkw 0x0228048400000000 0x0011402420000000 0x06600dc000000004 0x2033006e00000000

def z466 : W := mkw 0x3582fdb6aa001546 0x01ac17edb55000aa 0xbf80fffffe007ffe 0xfdfc07fffff003ff

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x800010000000418a 0x940000800000020c

def z468 : W := mkw 0x9f7d0201fddbc098 0x04fbe8100feede04 0xdfff1207ffffc19b 0xfefff8903ffffe0c

def z469 : W := mkw 0x3ffefdb602001104 0x01fff7edb0100088 0xbfffffff0e00598f 0xfdfffffff87002cc

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x8600000030000018 0xb430000001800000

def z471 : W := mkw 0x48d3b37b47bdfb95 0xa2469d9bda3defdc 0xc1ff93ff0fffd98b 0xde0ffc9ff87ffecc

def z472 : W := mkw 0x9f7d000054db0018 0x04fbe80002a6d800 0x5fff000001ff8001 0xf2fff800000ffc00

def z473 : W := mkw 0x1580d80002001104 0x00ac06c000100088 0xbf80fc000e00598e 0xfdfc07e0007002cc

def z474 : W := mkw 0x0000024001206001 0x0000001200090300 0x406003c001e00001 0x0203001e000f0000

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800e000c0001e00 0x49c00700060000f0

def z476 : W := mkw 0x1580d800a8000442 0x00ac06c005400022 0x3f80fc00f0002676 0xf1fc07e007800133

def z477 : W := mkw 0x9dd5d800ee991556 0x04eeaec00774c8aa 0x3997e000ce1c1e00 0x49ccbf000670e0f0

def z478 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x87801c003e0061fe 0xb43c00e001f0030f

def z479 : W := mkw 0x37aedc9600000000 0x01bd76e4b0000000 0x3f8ffc0700000006 0xf1fc7fe038000000

def z480 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x407003f8c1fc7e19 0x0a03801fc60fe3f0

def z481 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3980e000ce007e1e 0x79cc0700067003f0

def z482 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x407003f801fc601f 0x3203801fc00fe300

def z483 : W := mkw 0x9d540000e8900010 0x04eaa00007448000 0x18000000c0000000 0x00c0000006000000

def z484 : W := mkw 0x17a8d800ba42154e 0x00bd46c005d210aa 0xffe8fc00ffe3ffff 0xffff47e007ff1fff

def z485 : W := mkw 0x1f7c236841b46a11 0x80fbe11b420da350 0x7fffe3f8c1fc7e1f 0xfbffff1fc60fe3f0

def z486 : W := mkw 0x5583da1baf0dddc6 0x22ac1ed0dd786eee 0xf99ff23fcf1fdf8b 0xdfccff91fe78fefc

def z487 : W := mkw 0x000002010100c080 0x0000001008080604 0xc00000000103c188 0x0600000000081e0c

def z488 : W := mkw 0xdf7f021bfddfc898 0x26fbf810dfeefe44 0xdfff023fffff8019 0xfefff811fffffc00

def z489 : W := mkw 0x2afefdb600000000 0x0157f7edb0000000 0x207fffff00000007 0x0103fffff8000000

def z490 : W := mkw 0x0228048410420008 0x0011402420821000 0xc6681fc731e3801f 0xb63340fe398f1c00

def z491 : W := mkw 0x28d2fffe41b46a11 0x814697fff20da350 0x7870ffffc1fc7e1f 0x7bc387fffe0fe3f0

def z492 : W := mkw 0x972d0485bc4b80a8 0x44b968242de25c05 0x878f1c073e0381e0 0x843c78e039f01c0f

def z493 : W := mkw 0x000102010509c080 0x0000081008284e04 0xc19f12070f1fc18b 0xde0cf8903878fe0c

def z494 : W := mkw 0x0850232801044800 0x0042811940082240 0x7870e3f8011c580f 0x7bc3871fc008e2c0

def z495 : W := mkw 0x0a7827e51162e0a9 0x4053c13f288b1705 0xfe78ffff31e3e1ff 0xf7f3c7fff98f1f0f

def z496 : W := mkw 0x972d0000fcdb0018 0x04b9680007e6d800 0xc78f0000ffff8018 0x8e3c780007fffc00

def z497 : W := mkw 0xbffffdb6fedb155e 0x05ffffedb7f6d8aa 0xffffffffffffffff 0xffffffffffffffff

def z498 : W := mkw 0x022806cd51f6eab9 0xc01140366a8fb755 0xc6681fc7f1ffffff 0xbe3340fe3f8fffff

def z499 : W := mkw 0x5582da1bab04ddc6 0x22ac16d0dd5826ee 0xbf80fe3ffe007ffe 0xfdfc07f1fff003ff

def z500 : W := mkw 0x0850000000000000 0x0042800000000000 0x1870000000000001 0x70c3800000000000

def z501 : W := mkw 0x9f7c0000f8d20018 0x04fbe00007c69000 0x9fe00000fee00018 0xfcff000007f70000

def z502 : W := mkw 0x17a8dc85ba4295ee 0x40bd46e42dd214af 0xbf88fc07fe03fffe 0xfdfc47e03ff01fff

def z503 : W := mkw 0x422906cd176ff9ad 0x6211483668bb7fcd 0xc6681fc73ffff9ff 0xbe3340fe39ffffcf

def z504 : W := mkw 0x822906c5fdfbe0b9 0x441148362fefdf05 0xc6681fc7ffffe1ff 0xbe3340fe3fffff0f

def z505 : W := mkw 0x022806c401206001 0x0011403620090300 0x46681fc701e0601f 0xb23340fe380f0300

def z506 : W := mkw 0x1500000000000000 0x00a8000000000000 0x1f80000000000000 0xf0fc000000000000

def z507 : W := mkw 0x0000236801246a01 0x8000011b40092350 0x6060e3f801e07e1f 0x3303071fc00f03f0

def z508 : W := mkw 0x000002410120e081 0x0000001208090704 0xc06813c701e3e19f 0xb603409e380f1f0c

def z509 : W := mkw 0x37aedc9600000000 0x01bd76e4b0000000 0x07ef1fc700000007 0xb03f78fe38000000

def z510 : W := mkw 0x80010241fdfbe0b9 0x440008120fefdf05 0xc0000000ffffe1f8 0x0e00000007ffff0f

def z511 : W := mkw 0x172c000000000000 0x00b9600000000000 0x078f000000000000 0x803c780000000000

def z512 : W := mkw 0x42ab96d7176bf1ad 0x62155cb6b8bb5f8d 0xc7ef1fc73fe3e1ff 0xb63f78fe39ff1f0f

def z513 : W := mkw 0x0000020801044800 0x0000001040082240 0x7810e238c11c7e1f 0x7bc08711c608e3f0

def z514 : W := mkw 0x22aafdb600000000 0x011557edb0000000 0x2668ffff00000007 0xb13347fff8000000

def z515 : W := mkw 0x2082dc9600000000 0x010416e4b0000000 0x00001c0700000000 0x000000e038000000

def z516 : W := mkw 0x0080900002001104 0x0004048000100088 0xb980f000ce007f9e 0xfdcc0780067003fc

def z517 : W := mkw 0xbf7f25b6fcdb0018 0x05fbf92db7e6d800 0xdfff03ffffff8019 0xfefff81ffffffc00

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z519 : W := mkw 0x37aedc97104280a8 0x41bd76e4b8821405 0x878f1c07300381e0 0x843c78e039801c0f

def z520 : W := mkw 0x9f7d0000fedb155e 0x04fbe80007f6d8aa 0xdfff0000fffffff9 0xfefff80007ffffff

def z521 : W := mkw 0x0228000010420008 0x0011400000821000 0x4068000001e38001 0x02034000000f1c00

def z522 : W := mkw 0x4083925b176ff9ad 0x62041c92d8bb7fcd 0xc19f923f3ffff9fb 0xde0cfc91f9ffffcf

def z523 : W := mkw 0x085027ed41b4eab1 0xc042813f6a0da755 0x7870ffffc1fc7fff 0x7bc387fffe0fe3ff

def z524 : W := mkw 0xddd7921bef9dd994 0x26eebc90df7ceecc 0xd99f923fcf1fd98b 0xdeccfc91fe78fecc

def z525 : W := mkw 0x0000000002001546 0x00000000001000aa 0x0000000000007fe0 0x00000000000003ff

def z526 : W := mkw 0x15809000aa001104 0x00ac048005500088 0x9f809000fe00599a 0xfcfc048007f002cc

def z527 : W := mkw 0x022804c410622029 0x4011402620831101 0xc6680dc031e3a07d 0xb633406e018f1d03

def z528 : W := mkw 0xaa7f25b654db0018 0x0553f92db2a6d800 0x407f03ff01ff8001 0x0203f81ff80ffc00

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x86001c00300001e0 0x843000e00180000f

def z530 : W := mkw 0x822d0000144b0008 0x0411680000a25800 0x000f000000038000 0x0000780000001c00

def z531 : W := mkw 0x0000020801044800 0x0000001040082240 0x0000823800005802 0x00000411c00002c0

def z532 : W := mkw 0x0228024011626009 0x00114012008b1300 0xc66803c031e3e01f 0xb633401e018f1f00

def z533 : W := mkw 0x0000048400000000 0x0000002420000000 0x00001fc700000006 0x000000fe38000000

def z534 : W := mkw 0x0850000040900010 0x0042800002048000 0x18600000c0e00010 0x20c3000006070000

def z535 : W := mkw 0x1f7c06c51162e0a9 0x40fbe036288b1705 0xdfff1fc731e3e1ff 0xf6fff8fe398f1f0f

def z536 : W := mkw 0x4afbb7ff57fffbbd 0xe257ddbffabfffdd 0xffffffffffffffff 0xffffffffffffffff

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x40100000011c0009 0x5a0080000008e000

def z538 : W := mkw 0x0850212000000000 0x0042810900000000 0x3810e03800000000 0x41c08701c0000000

def z539 : W := mkw 0x7ffffdbe060d1904 0x23ffffedf03068c8 0x3fffffff0e1c1807 0xf9fffffff870e0c0

def z540 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x407083f801fc580b 0x5a03841fc00fe2c0

def z541 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x6070e3f801fc7e07 0x0303871fc00fe3f0

def z542 : W := mkw 0x1ffcd800aa001546 0x00ffe6c0055000aa 0xbffffc00fe007fff 0xfdffffe007f003ff

def z543 : W := mkw 0x0850212040900210 0x8042810902048010 0x38006000c0000600 0x01c0030006000030

def z544 : W := mkw 0x42ab9497164b91ac 0x62155ca4b8b25c8d 0x878f1c073e0381e0 0x843c78e039f01c0f

def z545 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xb980f000ce005f8a 0xddcc0780067002fc

def z546 : W := mkw 0x5dd3fb7befbdffd7 0xa2ee9fdbdf7deffe 0xffffffffffffffff 0xffffffffffffffff

def z547 : W := mkw 0x7dd7f93a060d1904 0x23eebfc9d03068c8 0x3997e0380e1c1800 0x49ccbf01c070e0c0

def z548 : W := mkw 0x1ff8ffedfbf6ffff 0xc0ffc7ff6fdfb7ff 0xfff8ffffffffffff 0xffffc7ffffffffff

def z549 : W := mkw 0x17a8dc84aa001546 0x00bd46e4255000aa 0xbfe8ffc7fe007fff 0xfdff47fe3ff003ff

def z550 : W := mkw 0x3dd6fb7a41b46a11 0x81eeb7dbd20da350 0x79f7e3f8c1fc7e1f 0x7bcfbf1fc60fe3f0

def z551 : W := mkw 0x3ffeffff51f6eab9 0xc1fff7fffa8fb755 0xfffffffff1ffffff 0xffffffffff8fffff

def z552 : W := mkw 0x5583d813ae0995c6 0x22ac1ec09d704cae 0x878f1c073e0381e0 0x843c78e039f01c0f

def z553 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xf99ff23fcf1fff9f 0xffccff91fe78fffc

def z554 : W := mkw 0x0080fb6803247f47 0x800407db401923fa 0x2000fff800007fe6 0x010007ffc00003ff

def z555 : W := mkw 0x4083901206091104 0x22041c8090304888 0x018700000e000000 0x000c380000700000

def z556 : W := mkw 0xdfffda1bffdfddde 0x26fffed0dffefeee 0xfffffe3fffffffff 0xfffffff1ffffffff

def z557 : W := mkw 0x48d3b33b070dd984 0x22469d99d8386ecc 0xf9fff3ff0f1fd98f 0xffcfff9ff878fecc

def z558 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x9fef0000fee38010 0xa4ff780007f71c00

def z559 : W := mkw 0x4002021b0104c880 0x22001010d8082644 0x0000023f00000000 0x00000011f8000000

def z560 : W := mkw 0x0000004010622029 0x4000000200831101 0x0000000030e02070 0x0000000001870103

def z561 : W := mkw 0x80010000fedb155e 0x0400080007f6d8aa 0xc0000000fffffff8 0x0e00000007ffffff

def z562 : W := mkw 0x7fffffbfaf0dddc6 0x23fffffdfd786eee 0xffffffffff1fffff 0xfffffffffff8ffff

def z563 : W := mkw 0x17a8dec51162e0a9 0x40bd46f6288b1705 0xffe8ffc731e3e1ff 0xf7ff47fe398f1f0f

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x818000000e000008 0xdc0c000000700000

def z565 : W := mkw 0x08d2b37a41b46a11 0x8046959bd20da350 0x79fff3ffc1fc7e1f 0xfbcfff9ffe0fe3f0

def z566 : W := mkw 0x5581da09af0dddc6 0x22ac0ed04d786eee 0xff80fc00ff1ffffe 0xfffc07e007f8ffff

def z567 : W := mkw 0x1f7d000004090000 0x00fbe80000204800 0xdfff00000f1f8009 0xfefff8000078fc00

def z568 : W := mkw 0x008092010300d184 0x000404900818068c 0xc18892070f03d98b 0xde0c449038781ecc

def z569 : W := mkw 0x0228000000000000 0x0011400000000000 0x0668000000000001 0xb033400000000000

def z570 : W := mkw 0x000004c400202021 0x4000002620010101 0x00000dc000002064 0x0000006e00000103

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000c0007e18 0x08000000060003f0

def z572 : W := mkw 0x4082921b0304d984 0x22041490d81826cc 0xc008923f0103d98b 0x96004491f8081ecc

def z573 : W := mkw 0x4083901306099184 0x22041c8098304c8c 0x818f90070e03d98a 0xdc0c7c8038701ecc

def z574 : W := mkw 0x1dd0fb6841b46a11 0x80ee87db420da350 0x7ff0fff8c1fc7e1f 0xfbff87ffc60fe3f0

def z575 : W := mkw 0x02a8dec51362f5ef 0x401546f6289b17af 0xe668ffc731e3ffff 0xb73347fe398f1fff

def z576 : W := mkw 0x0000024001206001 0x0000001200090300 0x000003c000006006 0x0000001e00000300

def z577 : W := mkw 0x3586d81200000000 0x01ac36c090000000 0x0187000000000000 0x000c380000000000

def z578 : W := mkw 0x17a8dc85ba4295ee 0x40bd46e42dd214af 0x87881c073e0381e0 0x843c40e039f01c0f

def z579 : W := mkw 0x4083901a060d1904 0x22041c80d03068c8 0x819790380e1c598a 0xdc0cbc81c070e2cc

def z580 : W := mkw 0x0080d80002001546 0x000406c0001000aa 0x2000e00000001e00 0x01000700000000f0

def z581 : W := mkw 0x2082f93200000000 0x010417c990000000 0x2000e03800000000 0x01000701c0000000

def z582 : W := mkw 0x0000212800040a00 0x8000010940002050 0x2000e03800001e00 0x01000701c00000f0

def z583 : W := mkw 0x0850212000000000 0x0042810900000000 0x386061c000000004 0x21c3030e00000000

def z584 : W := mkw 0x1d506b68e9b46e53 0x80ea835b474da372 0x7e70eff8f1fc7e7f 0x7bf3877fc78fe3f3

def z585 : W := mkw 0xdfff96dffffff9bd 0x66fffcb6ffffffcd 0xdfff9ffffffff9ff 0xfefffcffffffffcf

def z586 : W := mkw 0x0000020801044800 0x0000001040082240 0x40100238011c0001 0x02008011c008e000

def z587 : W := mkw 0x0080900002001104 0x0004048000100088 0x818010000e000180 0x840c00800070000c

def z588 : W := mkw 0x1ffe901200000000 0x00fff48090000000 0x1fff923f00000003 0xf0fffc91f8000000

def z589 : W := mkw 0x0a7827ed51f6eab9 0xc053c13f6a8fb755 0x407803ff01ff8001 0x0203c01ff80ffc00

def z590 : W := mkw 0x000027ed0124eaa1 0xc000013f68092755 0x2000ffff00007fe6 0x010007fff80003ff

def z591 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0xc67f000031ff8019 0xb633f800018ffc00

def z592 : W := mkw 0x0850020841944810 0x00428010420ca240 0x58708238c1fc581b 0x7ac38411c60fe2c0

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000300061f8 0x040000000180030f

def z594 : W := mkw 0x7fffffff176ff9ad 0x63fffffff8bb7fcd 0xffffffff3ffff9ff 0xfffffffff9ffffcf

def z595 : W := mkw 0x0082901200000000 0x0004148090000000 0x0000923f00000002 0x00000491f8000000

def z596 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0x587f0000c1ff8019 0x7ac3f800060ffc00

def z597 : W := mkw 0x000002411162e0a9 0x40000012088b1705 0xc6001c0031e3e1fe 0xb63000e0018f1f0f

def z598 : W := mkw 0x1582d81200000000 0x00ac16c090000000 0x3f9ffe3f00000007 0xf1fcfff1f8000000

def z599 : W := mkw 0x3dd6f93200000000 0x01eeb7c990000000 0x3f97fc3800000006 0xf1fcbfe1c0000000

def z600 : W := mkw 0x1f7c000040900010 0x00fbe00002048000 0x5fff0000c1fc0019 0xfafff800060fe000

def z601 : W := mkw 0x15000000aa001546 0x00a80000055000aa 0x9f800000fe007ff8 0xfcfc000007f003ff

def z602 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0xfe70fff8f1fc7fff 0xfff387ffc78fe3ff

def z603 : W := mkw 0x0000024801246801 0x0000001240092340 0x407083f801fc781f 0x7a03841fc00fe3c0

def z604 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x0197923f0e1c5982 0x480cbc91f870e2cc

def z605 : W := mkw 0x1d506960e8b02653 0x80ea834b07458132 0x3e606dc0f0e02674 0x21f3036e07870133

def z606 : W := mkw 0x15004800a8000442 0x00a8024005400022 0x3e00ec00f0007e7e 0x79f00760078003f3

def z607 : W := mkw 0x0a7827e551f2e2b9 0xc053c13f2a8f9715 0xfe687fc7f1e3e7ff 0xb7f343fe3f8f1f3f

def z608 : W := mkw 0x022804c410622029 0x4011402620831101 0x86601dc030e061fe 0xb43300ee0187030f

def z609 : W := mkw 0x3582fdb600000000 0x01ac17edb0000000 0x3f80ffff00000006 0xf1fc07fff8000000

def z610 : W := mkw 0x1dd0fb68ebb47f57 0x80ee87db475da3fa 0x79f0e3f8cffc7e1f 0x7bcf871fc67fe3f0

def z611 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x86081fc73003e1e6 0x843040fe39801f0f

def z612 : W := mkw 0x9f7d04c4fcfb2039 0x44fbe82627e7d901 0xdfff0dc0ffffa07d 0xfefff86e07fffd03

def z613 : W := mkw 0x4001000106099184 0x2200080008304c8c 0x800000000e038180 0x0400000000701c0c

def z614 : W := mkw 0x1580d80000000000 0x00ac06c000000000 0xbf80fc00300061fe 0xf5fc07e00180030f

def z615 : W := mkw 0x5583d81aae0d1d46 0x22ac1ec0d57068ea 0xbf97fc38fe1c7ffe 0xfdfcbfe1c7f0e3ff

def z616 : W := mkw 0x022804c410622029 0x4011402620831101 0x006001c000e00000 0x0003000e00070000

def z617 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0xc19f023f0f1f8009 0xde0cf811f878fc00

def z618 : W := mkw 0x48d3b33b479ddb94 0xa2469d99da3ceedc 0xf99ff23fcf1fdf8b 0xdfccff91fe78fefc

def z619 : W := mkw 0xcaff921b57dfd99c 0x2657fc90dabefecc 0xc1ff923f0fffd98b 0xde0ffc91f87ffecc

def z620 : W := mkw 0x1580d80002001546 0x00ac06c0001000aa 0x3f80fc0000007fe6 0xf1fc07e0000003ff

def z621 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80fc003e0001e6 0xf5fc07e001f0000f

def z622 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6600dc031e3e1fc 0x2633006e018f1f0f

def z623 : W := mkw 0x97add800be4b154e 0x04bd6ec005f258aa 0xbf8ffc00fe03fffe 0xfdfc7fe007f01fff

def z624 : W := mkw 0x1580d80000000000 0x00ac06c000000000 0x3980e00000000000 0x41cc070000000000

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x000080000000580a 0x58000400000002c0

def z626 : W := mkw 0x4003001304098080 0x2200180098204c04 0x000f000700038000 0x0000780038001c00

def z627 : W := mkw 0x0000216000202201 0x8000010b00010110 0x200061c000002604 0x0100030e00000130

def z628 : W := mkw 0x0080d80002001546 0x000406c0001000aa 0x3800fc00c0007ffe 0x79c007e0060003ff

def z629 : W := mkw 0xd7af921bbf4fd98c 0x26bd7c90ddfa7ecc 0xc79f923f3f1fd98b 0xde3cfc91f9f8fecc

def z630 : W := mkw 0x4003001a040d0800 0x22001800d0206840 0x00170038001c0000 0x0000b801c000e000

def z631 : W := mkw 0x1580da41bb62f5ef 0x40ac06d20ddb17af 0xff80fc00ffe3fffe 0xfffc07e007ff1fff

def z632 : W := mkw 0x3d54692000000000 0x01eaa34900000000 0x3800600000000000 0x01c0030000000000

def z633 : W := mkw 0x0850216040b02211 0x8042810b02058110 0x006001c000e00000 0x0003000e00070000

def z634 : W := mkw 0x0001000004090000 0x0000080000204800 0x401f0000011f8001 0x0200f8000008fc00

def z635 : W := mkw 0x77afde9f070dd984 0x23bd7ef4f8386ecc 0xc79f9e3f0f1fd98b 0xde3cfcf1f878fecc

def z636 : W := mkw 0x0850212840940a10 0x804281094204a050 0x3810e038c01c7e1e 0x79c08701c600e3f0

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008120700000003 0x9000409038000000

def z638 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80e000fe001e18 0xfdfc070007f000f0

def z639 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fef7dc700000004 0xa1ff7bee38000000

def z640 : W := mkw 0x08d0b36843b47b15 0x8046859b421da3d8 0xf9f0f3f8cffc7f9f 0xffcf879fc67fe3fc

def z641 : W := mkw 0x0850236801246a01 0x8042811b40092350 0x3870e3f800007e07 0x71c3871fc00003f0

def z642 : W := mkw 0xdfff901afedf191c 0x26fffc80d7f6f8c8 0xdfff8038ffff9819 0xfefffc01c7fffcc0

def z643 : W := mkw 0x000002010100c080 0x0000001008080604 0xc6081e073103e1ff 0xb63040f039881f0f

def z644 : W := mkw 0x40010008060d1904 0x22000800403068c8 0x000000000e1c1800 0x080000000070e0c0

def z645 : W := mkw 0x8a7d0000fcdb0018 0x0453e80007e6d800 0xc07f0000ffff8019 0x0e03f80007fffc00

def z646 : W := mkw 0x9581d800fedb155e 0x04ac0ec007f6d8aa 0xff80fc00fffffffe 0xfffc07e007ffffff

def z647 : W := mkw 0x3dd6f93200000000 0x01eeb7c990000000 0x399ff23f00000003 0xd1ccff91f8000000

def z648 : W := mkw 0x0080900002001104 0x0004048000100088 0x0000900000005982 0x00000480000002cc

def z649 : W := mkw 0x20006da400000000 0x0100036d20000000 0x20006dc000000004 0x0100036e00000000

def z650 : W := mkw 0x4082921b0304d984 0x22041490d81826cc 0x8180923f0e00598a 0xdc0c0491f87002cc

def z651 : W := mkw 0xbffffdb6bc4b0008 0x05ffffedb5e25800 0xbfffffff3e038007 0xf5fffffff9f01c00

def z652 : W := mkw 0x17284cc4b862246b 0x40b9426625c31123 0x3e606dc0f0e02674 0x21f3036e07870133

def z653 : W := mkw 0x1f7c048400000000 0x00fbe02420000000 0x1fff1fc700000007 0xf0fff8fe38000000

def z654 : W := mkw 0x3f7c6de440b02211 0x81fbe36f22058110 0x3e606dc0c0e02614 0x21f3036e06070130

def z655 : W := mkw 0x3ffefffe01246a01 0x81fff7fff0092350 0x3fffffff00007e07 0xf1fffffff80003f0

def z656 : W := mkw 0x4003021b070dd984 0x22001810d8386ecc 0xc01f023f0f1fd989 0x0e00f811f878fecc

def z657 : W := mkw 0x40010209070dd984 0x2200081048386ecc 0xc19f00000f1fd989 0xde0cf8000078fecc

def z658 : W := mkw 0xddd7901aee9d1914 0x26eebc80d774e8c8 0x19978038ce1c1800 0x48ccbc01c670e0c0

def z659 : W := mkw 0x0080d80002001546 0x000406c0001000aa 0xa180fc000e007fee 0xdd0c07e0007003ff

def z660 : W := mkw 0x0a7827ec41b46a11 0x8053c13f620da350 0x7e78ffffc1fc7e1f 0xfbf3c7fffe0fe3f0

def z661 : W := mkw 0x00000248ebb47f57 0x80000012475da3fa 0xc0000000fffc7ff8 0x0e00000007ffe3ff

def z662 : W := mkw 0x972d0000bc4b0008 0x04b9680005e25800 0xc79f00003f1f8009 0xde3cf80001f8fc00

def z663 : W := mkw 0x0001000004090000 0x0000080000204800 0x818f00000e038000 0x840c780000701c00

def z664 : W := mkw 0x000006c50120e0a1 0x4000003628090705 0x40601fc701e061ff 0x320300fe380f030f

def z665 : W := mkw 0x3f7c6de410622029 0x41fbe36f20831101 0x3e606dc030e02074 0x21f3036e01870103

def z666 : W := mkw 0x2082fff70120e0a1 0x410417ffb8090705 0x2000ffff000061e6 0x010007fff800030f

def z667 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf807c00fe0027f4 0xa5fc03e007f0013f

def z668 : W := mkw 0x408396df072df9a5 0x62041cb6f8396fcd 0xc19f9fff0f1ff9ef 0xde0cfcfff878ffcf

def z669 : W := mkw 0x0000000800040800 0x0000000040002040 0x00108038001c1800 0x48008401c000e0c0

def z670 : W := mkw 0x9f7d06c5fdfbe0b9 0x44fbe8362fefdf05 0xdfff03c7ffff8019 0xfefff81e3ffffc00

def z671 : W := mkw 0x1dd0f920aa001546 0x00ee87c9055000aa 0xbff0fff8fe007fff 0xfdff87ffc7f003ff

def z672 : W := mkw 0x8a7d236855ff6a19 0x8453e91b42affb50 0x787fe3f8c1fffe1f 0x7bc3ff1fc60ffff0

def z673 : W := mkw 0x1580da40ab207547 0x00ac06d2055903aa 0xffe0ffc0ffe07fff 0xffff07fe07ff03ff

def z674 : W := mkw 0x0850236951f6eab9 0xc042811b4a8fb755 0xf870e3f8f1ffffff 0x7fc3871fc78fffff

def z675 : W := mkw 0x9f7c06c5f9f2e0b9 0x44fbe0362fcf9705 0xde681fc7f1e3e1ff 0xb6f340fe3f8f1f0f

def z676 : W := mkw 0x3dd6f93a40940a10 0x81eeb7c9d204a050 0x3997e038c01c1e00 0x49ccbf01c600e0f0

def z677 : W := mkw 0x9f7d0000bc4b0008 0x04fbe80005e25800 0x9fff00003e038001 0xf4fff80001f01c00

def z678 : W := mkw 0x1ffcd80000000000 0x00ffe6c000000000 0x3ffffc0000000007 0xf1ffffe000000000

def z679 : W := mkw 0x9f7d0241fdfbe0b9 0x44fbe8120fefdf05 0xdfff0000ffffe1f9 0xfefff80007ffff0f

def z680 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000c0000018 0x78c0000006000000

def z681 : W := mkw 0x022806c411626029 0x40114036208b1301 0x46600fc031e0607f 0x3233007e018f0303

def z682 : W := mkw 0x4082901302009184 0x220414809810048c 0x0000100700000180 0x000000803800000c

def z683 : W := mkw 0x0851236845bd6a11 0x8042891b422deb50 0xf9ffe3f8cffffe1f 0xffcfff1fc67ffff0

def z684 : W := mkw 0x0850024041b06011 0x00428012020d8300 0x587003c0c1fc601f 0x7ac3801e060fe300

def z685 : W := mkw 0x000002411162e0a9 0x40000012088b1705 0xc06003c031e3e1ff 0x3603001e018f1f0f

def z686 : W := mkw 0x3ffedc9600000000 0x01fff6e4b0000000 0x1fff1c0700000001 0xf0fff8e038000000

def z687 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3f9ffc3f00000000 0xc1fcffe1f8000000

def z688 : W := mkw 0x17a8dc8400000000 0x00bd46e420000000 0x3fe8ffc700000007 0xf1ff47fe38000000

def z689 : W := mkw 0x5583d813ae0995c6 0x22ac1ec09d704cae 0xbf8ffc07fe03fffe 0xfdfc7fe03ff01fff

def z690 : W := mkw 0x9ffdd800fcdb0018 0x04ffeec007e6d800 0xfffffc00ffff801f 0xffffffe007fffc00

def z691 : W := mkw 0x7fffffbf050dc880 0x23fffffdf8286e44 0x7fffffff011f8007 0xf3fffffff808fc00

def z692 : W := mkw 0x0850212840940a10 0x804281094204a050 0x3870e3f8c01c1e07 0x79c3871fc600e0f0

def z693 : W := mkw 0x000006c51162e0a9 0x40000036288b1705 0xc0001fc731e3e1fe 0x060000fe398f1f0f

def z694 : W := mkw 0x2a7e27f71162e0a9 0x4153f13fb88b1705 0x407f03ff01e38001 0x0203f81ff80f1c00

def z695 : W := mkw 0x1580dec5ab20f5e7 0x40ac06f62d5907af 0xbf80ffc7fe007ffe 0xfdfc07fe3ff003ff

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000e00000007e06 0x01000700000003f0

def z697 : W := mkw 0x972d0000bc4b0008 0x04b9680005e25800 0x9f8f0000fe038018 0xfcfc780007f01c00

def z698 : W := mkw 0x0080d80002001546 0x000406c0001000aa 0x00001c00000001e0 0x000000e00000000f

def z699 : W := mkw 0x3ffcfda4aa001546 0x01ffe7ed255000aa 0xbfe0fdc0fe007ffe 0xfdff07ee07f003ff

def z700 : W := mkw 0x408392130709d184 0x22041c9098384e8c 0xc18f12070f03c18b 0x960c789038781e0c

def z701 : W := mkw 0x9f7d2368fdff6a19 0x84fbe91b47effb50 0xdfff03f8ffff8019 0xfefff81fc7fffc00

def z702 : W := mkw 0x022806850100c080 0x0011403428080604 0xc6681fc70103c18f 0xb63340fe38081e0c

def z703 : W := mkw 0x400002090304d984 0x22000010481826cc 0x0000000000005980 0x00000000000002cc

def z704 : W := mkw 0x15000000a8000000 0x00a8000005400000 0x19800000ce000000 0x48cc000006700000

def z705 : W := mkw 0x80010248fdff6a19 0x8400081247effb50 0xc0000000fffffe18 0x0e00000007fffff0

def z706 : W := mkw 0x1500480000000000 0x00a8024000000000 0x3e006c0000000004 0x21f0036000000000

def z707 : W := mkw 0x008392130509c080 0x00041c9098284e04 0xc19f923f0f1fc18b 0xde0cfc91f878fe0c

def z708 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923f0f1fd983 0x860cfc91f878fecc

def z709 : W := mkw 0x3f7e25b600000000 0x01fbf12db0000000 0x07ff03ff00000001 0x803ff81ff8000000

def z710 : W := mkw 0x7f7d6fad070dd984 0x23fbeb7d68386ecc 0xfe606dc00f1fd98c 0x2ff3036e0078fecc

def z711 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdff70000ffff8018 0x6effb80007fffc00

def z712 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf90fe38fe007fff 0xfdfc87f1c7f003ff

def z713 : W := mkw 0x9f7d000054db0018 0x04fbe80002a6d800 0xdfff00000fff8009 0xfefff800007ffc00

def z714 : W := mkw 0x2082fdb600000000 0x010417edb0000000 0x2197ffff00000006 0x410cbffff8000000

def z715 : W := mkw 0x80010000fcdb0018 0x0400080007e6d800 0xc18f0000ffff8018 0x8e0c780007fffc00

def z716 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc7e81fc73fe3e1ff 0xfe3f40fe39ff1f0f

def z717 : W := mkw 0x00010209050dc880 0x0000081048286e44 0xc19f923f0f1fd98b 0xde0cfc91f878fecc

def z718 : W := mkw 0x40010249156fe8a9 0x6200081248ab7f45 0x4000000001ff8000 0x02000000000ffc00

def z719 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e1f8c1fc7e1c 0x6bc3870fc60fe3f0

def z720 : W := mkw 0xbf7c25a4f8d20018 0x05fbe12d27c69000 0x1e6001c0f0e00010 0x20f3000e07870000

def z721 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xff88fc00ff03ffff 0xfffc47e007f81fff

def z722 : W := mkw 0x3ffefdb602001104 0x01fff7edb0100088 0x3fffffff00005987 0xf1fffffff80002cc

def z723 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc7e19 0x4bc3871fc60fe3f0

def z724 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff1c00ffff81f9 0xfefff8e007fffc0f

def z725 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7e70eff8f1fc7e7f 0x7bf3877fc78fe3f3

def z726 : W := mkw 0x22aafdb600000000 0x011557edb0000000 0x27ffffff00000007 0xf13ffffff8000000

def z727 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0000fffffe19 0xfefff80007fffff0

def z728 : W := mkw 0xbf7c6de4f8f22219 0x85fbe36f27c79110 0x3e606dc0f0e02614 0x21f3036e07870130

def z729 : W := mkw 0x2afefdb602001546 0x0157f7edb01000aa 0x207fffff00007fe7 0x0103fffff80003ff

def z730 : W := mkw 0xdffe921bfbd6d99c 0x26fff490dfdeb6cc 0x1e60923ff0e05992 0x20f30491ff8702cc

def z731 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xbffffffff0007fff 0xfdffffffff8003ff

def z732 : W := mkw 0x0850216840b42a11 0x8042810b4205a150 0x7870e1f8c1fc3e1d 0x7bc3870fc60fe1f0

def z733 : W := mkw 0xbf7e25b6f8d20018 0x05fbf12db7c69000 0x1e7f03fff0e00011 0x20f3f81fff870000

def z734 : W := mkw 0x55034a1bad0dccc2 0x22a81a50dd686e66 0x7e1f6e3ff11fa675 0x23f0fb71ff88fd33

def z735 : W := mkw 0xa083fdb6fcdb0018 0x05041fedb7e6d800 0xe000ffffffff801e 0x0f0007fffffffc00

def z736 : W := mkw 0x3ffefdb610420008 0x01fff7edb0821000 0x3fffffff30e00017 0xf1fffffff9870000

def z737 : W := mkw 0x2afefdb600000000 0x0157f7edb0000000 0x007f1fff00000001 0x0003f8fff8000000

def z738 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x41ff00000fff8001 0x020ff800007ffc00

def z739 : W := mkw 0x17a8dec5bb62f5ef 0x40bd46f62ddb17af 0x79e8e3c7cfe39e01 0x4bcf471e3e7f1cf0

def z740 : W := mkw 0x0082901200000000 0x0004148090000000 0x01ff93ff00000007 0xf00ffc9ff8000000

def z741 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x86681fc730e3e1f6 0xa43340fe39871f0f

def z742 : W := mkw 0x95010000fcdb0018 0x04a8080007e6d800 0xdf9f0000ffff8019 0xfefcf80007fffc00

def z743 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xc7ff0000ffff8019 0x8e3ff80007fffc00

def z744 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xe19ff23f0f1fff8f 0xdf0cff91f878fffc

def z745 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3f9fffff00000006 0xc1fcfffff8000000

def z746 : W := mkw 0x4083901306099184 0x22041c8098304c8c 0xc19f923f0f1f818b 0xde0cfc91f878fc0c

def z747 : W := mkw 0x37aefdb6aa001546 0x01bd77edb55000aa 0xa78fffff3e007fe6 0x853c7ffff9f003ff

def z748 : W := mkw 0x2a7e25b6aa001546 0x0153f12db55000aa 0x807f03fffe007ff9 0x0c03f81ffff003ff

def z749 : W := mkw 0x8afdd80056db155e 0x0457eec002b6d8aa 0x607ffc0001ffffe7 0x0303ffe0000fffff

def z750 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0x41ff00000fff8001 0x4a0ff800007ffc00

def z751 : W := mkw 0xc0010249fffffb9d 0xa60008124fffffdc 0xc0000000ffffff98 0x0e00000007fffffc

def z752 : W := mkw 0x972d0000fcdb0018 0x04b9680007e6d800 0xc79f0000ffff8019 0xde3cf80007fffc00

def z753 : W := mkw 0x972d0000fcdb0018 0x04b9680007e6d800 0xc78f00003fff8000 0x863c780001fffc00

def z754 : W := mkw 0x17aadc96aa001546 0x00bd56e4b55000aa 0xbffffffffe007fff 0xfdfffffffff003ff

def z755 : W := mkw 0x9f7d2120fcdb0018 0x04fbe90907e6d800 0xdfff03f8ffff8019 0xfefff81fc7fffc00

def z756 : W := mkw 0x9d550000fcdb0018 0x04eaa80007e6d800 0xdf970000ffff8018 0xfefcb80007fffc00

def z757 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff1207ffff801b 0xfefff8903ffffc00

def z758 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x59ff0000cfff8019 0x7acff800067ffc00

def z759 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f9e3f0f1ff9ef 0xde0cfcf1f878ffcf

def z760 : W := mkw 0x022806cd1166e8a9 0x40114036688b3745 0xc6689fff31e3f9ff 0xb63344fff98f1fcf

def z761 : W := mkw 0x1ffe949600000000 0x00fff4a4b0000000 0x1fff9fff00000007 0xf0fffcfff8000000

def z762 : W := mkw 0x022806cd1166eaa9 0xc0114036688b3755 0xc6681fc731e3ffff 0xb63340fe398f1fff

def z763 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0xc1ff00000fff8001 0x860ff800007ffc00

def z764 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff8238ffff801b 0xfefffc11c7fffc00

def z765 : W := mkw 0x972d2368bd6f6a09 0x84b9691b45eb7b50 0xa78fe3f83e03fe06 0x853c7f1fc1f01ff0

def z766 : W := mkw 0x9f7d0484fcdb0018 0x04fbe82427e6d800 0xdfff03c7ffff8019 0xfefff81e3ffffc00

def z767 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfef0000ffff8018 0xaeff780007fffc00

def z768 : W := mkw 0x3ffefdb602001546 0x01fff7edb01000aa 0xbfffffff0e007fef 0xfdfffffff87003ff

def z769 : W := mkw 0x3ffefdb640900210 0x81fff7edb2048010 0x3fffffffc0000607 0xf1fffffffe000030

def z770 : W := mkw 0x2a7e25b610420008 0x0153f12db0821000 0x407f03ff01e38001 0x0203f81ff80f1c00

def z771 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x3ffffffffe003e77 0xf9fffffffff001f3

def z772 : W := mkw 0x3ffefdb602001104 0x01fff7edb0100088 0xbfffffff3e0079ff 0xfdfffffff9f003cf

def z773 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0x419f023f0f1f8001 0x4a0cf811f878fc00

def z774 : W := mkw 0x972d0000fcdb0018 0x04b9680007e6d800 0xdf8f0000ffff8018 0xfefc780007fffc00

def z775 : W := mkw 0x3ffefdb6a8000442 0x01fff7edb5400022 0x3ffffffff0007e7f 0xf9ffffffff8003f3

def z776 : W := mkw 0x4083da1b070dd984 0x22041ed0d8386ecc 0xe19ffe3f0f1fd98f 0xdf0cfff1f878fecc

def z777 : W := mkw 0x3ffefdb610420008 0x01fff7edb0821000 0xbfffffff30038007 0xf5fffffff9801c00

def z778 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xffff6000ffffa61d 0xfffffb0007fffd30

def z779 : W := mkw 0x022804c51062a0a9 0x4011402628831505 0x86681dc730e3e1fe 0xb43340ee39871f0f

def z780 : W := mkw 0x3ffeb5b600000000 0x01fff5adb0000000 0x1fff93ff00000003 0xf0fffc9ff8000000

def z781 : W := mkw 0x9f7d2120fcdb0018 0x04fbe90907e6d800 0xffffe038ffff8019 0xffffff01c7fffc00

def z782 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0000ffffe1f9 0xfefff80007ffff0f

def z783 : W := mkw 0x3dd6fb731162e0a9 0x41eeb7db988b1705 0xf997e03831e3e1f8 0x47ccbf01c18f1f0f

def z784 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbffffffffe0027f7 0xf5fffffffff0013f

def z785 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80fc00fe007fe6 0xcdfc07e007f003ff

def z786 : W := mkw 0x0850216840b42a11 0x8042810b4205a150 0x3870e1f8c0fc7e1e 0x79c3870fc607e3f0

def z787 : W := mkw 0x3ffefdb6a8000442 0x01fff7edb5400022 0xbffffffff00067ff 0xf5ffffffff80033f

def z788 : W := mkw 0x3ffefdb650d20018 0x01fff7edb2869000 0xfffffffff1ff801f 0xffffffffff8ffc00

def z789 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc79f9e3f3f1fd9eb 0xde3cfcf1f9f8fecf

def z790 : W := mkw 0x15004800aa001546 0x00a80240055000aa 0xbe007c00fe007ffe 0xbdf003e007f003ff

def z791 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0xfe70e3f8f1fc7e1f 0xfff3871fc78fe3f0

def z792 : W := mkw 0x1582d812aa001546 0x00ac16c0955000aa 0xbf97fc38fe007ffe 0xfdfcbfe1c7f003ff

def z793 : W := mkw 0x42ab94de166f392d 0x62155ca6f0b379c9 0x07f78df83efc3874 0x683fbc6fc1f7e1c3

def z794 : W := mkw 0x37aedede41b46a11 0x81bd76f6f20da350 0x478f1c07c1fc7e18 0x8a3c78e03e0fe3f0

def z795 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xd9ff0000cfff8009 0xdecff800067ffc00

def z796 : W := mkw 0x9d5506c5edb9e0b1 0x44eaa8362f6dcf05 0x19971fc7ce1c61e6 0x48ccb8fe3e70e30f

def z797 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f123f0f1fd989 0x8e0cf891f878fecc

def z798 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffffc000001f 0xf9fffffffe000000

def z799 : W := mkw 0x0a7825ad50d68ab8 0xc053c12d6a86b455 0xbe18fc3ff01f9fe0 0xcdf0c7e1ff80fcff

def z800 : W := mkw 0x9f7d4800fcdb045a 0x04fbea4007e6d822 0xffff6000ffff8619 0xfffffb0007fffc30

def z801 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x01ff03ff00000001 0x000ff81ff8000000

def z802 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbfffffff3e007fe7 0xf5fffffff9f003ff

def z803 : W := mkw 0x4001024957fffbbd 0xe20008124abfffdd 0xc0000000fffffff8 0x0e00000007ffffff

def z804 : W := mkw 0x00010000144b0008 0x0000080000a25800 0xc19f00003fff8019 0xde0cf80001fffc00

def z805 : W := mkw 0x8001000054db0018 0x0400080002a6d800 0xc19f00000fff8009 0xde0cf800007ffc00

def z806 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xc7ff00003fff8019 0xb63ff80001fffc00

def z807 : W := mkw 0xbf7d6920fcdb0018 0x05fbeb4907e6d800 0xffff6000ffff8019 0xfffffb0007fffc00

def z808 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xffe0fc00ffe07fff 0xffff07e007ff03ff

def z809 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc1ff923f0fffd99b 0xfe0ffc91f87ffecc

def z810 : W := mkw 0x4082b37b0324fb85 0xa204159bd81927dc 0x000093ff00005982 0x0000049ff80002cc

def z811 : W := mkw 0x3ffefdb602001104 0x01fff7edb0100088 0x3fffffff0e001807 0xf9fffffff87000c0

def z812 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf88fe07fe007fff 0xfdfc47f03ff003ff

def z813 : W := mkw 0x40010249efbdffd7 0xa20008124f7deffe 0xc0000000fffffff8 0x0e00000007ffffff

def z814 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x01ff03ff00000001 0xd00ff81ff8000000

def z815 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0xc7ff00003fff8019 0xfe3ff80001fffc00

def z816 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff0000580f 0xf9fffffff80002c0

def z817 : W := mkw 0x3ffefdb640900010 0x01fff7edb2048000 0x7fffffff01fc0007 0xf3fffffff80fe000

def z818 : W := mkw 0x48d3b17346b9b395 0xa2469d8b9a35cd9c 0xb9ef71c7cee3a794 0xa5cf7b8e3e771d3c

def z819 : W := mkw 0x3f7e6db600000000 0x01fbf36db0000000 0x067f0fff00000001 0x0033f87ff8000000

def z820 : W := mkw 0x3f7e6db600000000 0x01fbf36db0000000 0x3fff6fff00000005 0xf1fffb7ff8000000

def z821 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0xf870e3f8f1fc7fff 0x7fc3871fc78fe3ff

def z822 : W := mkw 0x3ffefdb6a8000442 0x01fff7edb5400022 0x3fffffffc0000607 0xf1fffffffe000030

def z823 : W := mkw 0x3ffefdb602001104 0x01fff7edb0100088 0xbfffffff0e000187 0xf5fffffff870000c

def z824 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xbfffffff0000418f 0xf5fffffff800020c

def z825 : W := mkw 0x82290000fcdb0018 0x0411480007e6d800 0xc7ff0000ffff8019 0xfe3ff80007fffc00

def z826 : W := mkw 0x4083da1b070dddc6 0x22041ed0d8386eee 0xc19f9e3f0f1fd9eb 0xde0cfcf1f878fecf

def z827 : W := mkw 0xbdd7f932ee991556 0x05eebfc99774c8aa 0x3997e038ce1c1e00 0x49ccbf01c670e0f0

def z828 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc1e19 0x7bc3871fc60fe0f0

def z829 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xc7ff00003fff8009 0xde3ff80001fffc00

def z830 : W := mkw 0x9f7d4800fcdb0018 0x04fbea4007e6d800 0xffff6c00ffff801d 0xfffffb6007fffc00

def z831 : W := mkw 0xbf7c6de4f8f22039 0x45fbe36f27c79101 0x3e606dc0f0e02074 0x21f3036e07870103

def z832 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xd99f923fcf1fd99b 0xfeccfc91fe78fecc

def z833 : W := mkw 0x3ffefdb6a8000000 0x01fff7edb5400000 0x3ffffffff0000017 0xf1ffffffff800000

def z834 : W := mkw 0x37aefdb600000000 0x01bd77edb0000000 0x3f8fffff00000006 0xf1fc7ffff8000000

def z835 : W := mkw 0x9d550000fcdb0018 0x04eaa80007e6d800 0x59970000cfff8000 0x4accb800067ffc00

def z836 : W := mkw 0xbffefdb6f8d2045a 0x05fff7edb7c69022 0x3ffffffff0e02677 0xf1ffffffff870133

def z837 : W := mkw 0x0850212040900010 0x0042810902048000 0x7870e3f8c1fc7e1f 0x7bc3871fc60fe3f0

def z838 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80fc00fe007ff8 0xcdfc07e007f003ff

def z839 : W := mkw 0x15004800aa001546 0x00a80240055000aa 0xbf806c00fe007ffc 0xfdfc036007f003ff

def z840 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc1e07 0x7bc3871fc60fe0f0

def z841 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xf99ff23f0f1fd98f 0xffccff91f878fecc

def z842 : W := mkw 0x4083901b060d9984 0x22041c80d8306ccc 0xc19f903f0f1f9989 0xde0cfc81f878fccc

def z843 : W := mkw 0x022804c51062a0a9 0x4011402628831505 0x86681dc730e381e0 0x843340ee39871c0f

def z844 : W := mkw 0x1dd2f932aa001546 0x00ee97c9955000aa 0xbffffffffe007fff 0xfdfffffffff003ff

def z845 : W := mkw 0xc0010249fffff9bd 0x660008124fffffcd 0xc0000000fffff9f8 0x0e00000007ffffcf

def z846 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e3e1f9 0x863340fe398f1f0f

def z847 : W := mkw 0x4083901b060d9984 0x22041c80d8306ccc 0x019f803f0e1f9800 0x480cfc01f870fcc0

def z848 : W := mkw 0xbffefdb6fad2155e 0x05fff7edb7d690aa 0xbffffffffee07fff 0xfdfffffffff703ff

def z849 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x5fff0000cfff8001 0xfafff800067ffc00

def z850 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xff90fc00ff1c7fff 0xfffc87e007f8e3ff

def z851 : W := mkw 0x40010249bf6ffdef 0x620008124dfb7fef 0xc0000000fffffff8 0x0e00000007ffffff

def z852 : W := mkw 0x28d6fdb600000000 0x0146b7edb0000000 0x2017ffff00000006 0x0100bffff8000000

def z853 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6781fc731ffe1ff 0xfe33c0fe398fff0f

def z854 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x3fffffff0e000007 0xf1fffffff8700000

def z855 : W := mkw 0xbf7d4c84fcdb0018 0x05fbea6427e6d800 0xdfff0c00ffff8019 0xfefff86007fffc00

def z856 : W := mkw 0x2afeb5b602001104 0x0157f5adb0100088 0x81ff93ff0e00598b 0xdc0ffc9ff87002cc

def z857 : W := mkw 0x9f7c25e4f8f22239 0xc4fbe12f27c79111 0x3e606dc0f0e02674 0x21f3036e07870133

def z858 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xffffe000ffff9e19 0xffffff0007fffcf0

def z859 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7878f3ffc1fc7e1f 0xfbc3c79ffe0fe3f0

def z860 : W := mkw 0x022a049600000000 0x00115024b0000000 0x007f03ff00000001 0x0003f81ff8000000

def z861 : W := mkw 0x2afeb5b600000000 0x0157f5adb0000000 0x39fff3ff00000007 0xf1cfff9ff8000000

def z862 : W := mkw 0x2afeb5b600000000 0x0157f5adb0000000 0x007f93ff00000003 0x0003fc9ff8000000

def z863 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x79ffe3f8c1fc7e1f 0xfbcfff1fc60fe3f0

def z864 : W := mkw 0x3ffefdb6a8000442 0x01fff7edb5400022 0xbffffffffe00267f 0xfdfffffffff00133

def z865 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7e70fff8c1fc7e1f 0xfbf387ffc60fe3f0

def z866 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3e7fffff00000007 0x21f3fffff8000000

def z867 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923fcf1fff9b 0xde0cfc91fe78fffc

def z868 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc7e07 0x4bc3871fc60fe3f0

def z869 : W := mkw 0x3dd6fdb6aa001546 0x01eeb7edb55000aa 0x3997ffffce007fe6 0x49ccbffffe7003ff

def z870 : W := mkw 0x0852213200000000 0x0042910990000000 0x007f03ff00000001 0x0003f81ff8000000

def z871 : W := mkw 0x1582d812aa001546 0x00ac16c0955000aa 0xbf8ffc07fe007ffe 0xfdfc7fe03ff003ff

def z872 : W := mkw 0x0850236941b4ea91 0x8042811b4a0da754 0xf870e3f8c1ffff9f 0x7fc3871fc60ffffc

def z873 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xfe68ffc731e3e1ff 0xf7f347fe398f1f0f

def z874 : W := mkw 0x0850216840b42a11 0x8042810b4205a150 0x3870e1f8c0fc1e00 0x49c3870fc607e0f0

def z875 : W := mkw 0xaa7e25b650d20018 0x0553f12db2869000 0x007f03ff00e00001 0x0003f81ff8070000

def z876 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x3e7fffff00000007 0xf1f3fffff8000000

def z877 : W := mkw 0x4083925b072df985 0x22041c92d8396fcc 0xc1ff93ff0fffd98b 0xde0ffc9ff87ffecc

def z878 : W := mkw 0x1dd0fb68ebb47f57 0x80ee87db475da3fa 0xc7f01ff83ffc01e1 0x863f80ffc1ffe00f

def z879 : W := mkw 0x8a7d0000fcdb0018 0x0453e80007e6d800 0xc1ff0000ffff8019 0xde0ff80007fffc00

def z880 : W := mkw 0x9f7d2120fcdb0218 0x84fbe90907e6d810 0xffff6000ffff8619 0xfffffb0007fffc30

def z881 : W := mkw 0x4083925b072df985 0x22041c92d8396fcc 0xc7ff9fff3ffff9ff 0xfe3ffcfff9ffffcf

def z882 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x3fffffffce007fe7 0xf9fffffffe7003ff

def z883 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xde681fc7f1e3e1ff 0xfef340fe3f8f1f0f

def z884 : W := mkw 0x972d0000fcdb0018 0x04b9680007e6d800 0xc7ef0000ffff8019 0xbe3f780007fffc00

def z885 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x39ffe3ffce001e01 0x49cfff1ffe7000f0

def z886 : W := mkw 0x40010249176ff9ad 0x6200081248bb7fcd 0xc00000000fffd988 0x0e000000007ffecc

def z887 : W := mkw 0x08d2b13200000000 0x0046958990000000 0x01ff93ff00000003 0xd00ffc9ff8000000

def z888 : W := mkw 0x2a7e25b640900010 0x0153f12db2048000 0x407f03ff01fc0001 0x0203f81ff80fe000

def z889 : W := mkw 0x3ffefdb610420008 0x01fff7edb0821000 0xffffffff31e3e1ff 0xf7fffffff98f1f0f

def z890 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923f0f1f9981 0xce0cfc91f878fccc

def z891 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870fff8c1fc7fff 0x7bc387ffc60fe3ff

def z892 : W := mkw 0x3dd6fdb600000000 0x01eeb7edb0000000 0x3f97ffff00000006 0xf1fcbffff8000000

def z893 : W := mkw 0x2a7e6db600000000 0x0153f36db0000000 0x207f6fff00000005 0x0103fb7ff8000000

def z894 : W := mkw 0x3586d812aa001546 0x01ac36c0955000aa 0xbf87fc00fe007ffe 0xfdfc3fe007f003ff

def z895 : W := mkw 0x4082925b0324f9a5 0x62041492d81927cd 0x0000923f000079e2 0x00000491f80003cf

def z896 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff0000601f 0xf1fffffff8000300

def z897 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6689fc731e3f9ff 0xfe3344fe398f1fcf

def z898 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffffc0001e07 0xf9fffffffe0000f0

def z899 : W := mkw 0x0083901206091104 0x00041c8090304888 0xc19f923f0f1fd98b 0xde0cfc91f878fecc

def z900 : W := mkw 0x22aefdb600000000 0x011577edb0000000 0x200fffff00000006 0x01007ffff8000000

def z901 : W := mkw 0x0003001204090000 0x0000180090204800 0xc19f023f0f1f8009 0xde0cf811f878fc00

def z902 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x867f1fff300061ff 0xb433f8fff980030f

def z903 : W := mkw 0x4082fb7b0324ffc7 0xa20417dbd81927fe 0x2000ffff00007fe6 0x010007fff80003ff

def z904 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf807c00fe007ffc 0xadfc03e007f003ff

def z905 : W := mkw 0x3ffefdb6a8000000 0x01fff7edb5400000 0xbffffffffe007e1f 0xfdfffffffff003f0

def z906 : W := mkw 0xbf7d6da4fcdb045a 0x05fbeb6d27e6d822 0xffff6dc0ffffa67d 0xfffffb6e07fffd33

def z907 : W := mkw 0x3ffefdb610420028 0x41fff7edb0821001 0x3fffffff30000067 0xf1fffffff9800003

def z908 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e3a1f5 0xa63340fe398f1d0f

def z909 : W := mkw 0x2a7e25b610420008 0x0153f12db0821000 0xc67f03ff31e38019 0xb633f81ff98f1c00

def z910 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0xf9f0e3f8cffc7e1f 0xffcf871fc67fe3f0

def z911 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x419f923f0f1f9803 0xda0cfc91f878fcc0

def z912 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3ff7ffff00000006 0x61ffbffff8000000

def z913 : W := mkw 0x3ffefdb6a8000442 0x01fff7edb5400022 0x3fffffff30000067 0xf1fffffff9800003

def z914 : W := mkw 0x3ffefdb640900010 0x01fff7edb2048000 0x3fffffffc0e00017 0xf1fffffffe070000

def z915 : W := mkw 0x40010249072dfb85 0xa200081248396fdc 0xc00000000f1fff88 0x0e0000000078fffc

def z916 : W := mkw 0x4083921b070dddc6 0x22041c90d8386eee 0xc19f923f0f1fffeb 0xde0cfc91f878ffff

def z917 : W := mkw 0x02aa949600000000 0x001554a4b0000000 0x01ff93ff00000003 0xd00ffc9ff8000000

def z918 : W := mkw 0x9f7d2120fcdb0018 0x04fbe90907e6d800 0xffff61c0ffff801d 0xfffffb0e07fffc00

def z919 : W := mkw 0x00000000aa001546 0x00000000055000aa 0xbe00fc00fe007ffe 0xfdf007e007f003ff

def z920 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0xf878e3f8c1fffe1f 0xffc3c71fc60ffff0

def z921 : W := mkw 0x3f7e25b600000000 0x01fbf12db0000000 0x3fffe3ff00000007 0xf1ffff1ff8000000

def z922 : W := mkw 0x3f7e25b6a8000000 0x01fbf12db5400000 0x9fff03fffe000019 0xfcfff81ffff00000

def z923 : W := mkw 0x0080900002001104 0x0004048000100088 0xbf80fc00fe007ffe 0xfdfc07e007f003ff

def z924 : W := mkw 0x2082fdb602001546 0x010417edb01000aa 0xa19fffff0e007fef 0xdd0cfffff87003ff

def z925 : W := mkw 0x3ffefdb6ea901556 0x01fff7edb75480aa 0xfffffffffffc7fff 0xffffffffffffe3ff

def z926 : W := mkw 0x4083da1b070dddc6 0x22041ed0d8386eee 0xe19ff23f0f1fdf8b 0xdf0cff91f878fefc

def z927 : W := mkw 0x3ffefdb602001546 0x01fff7edb01000aa 0xbfffffff30007fff 0xf5fffffff98003ff

def z928 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc1ff93ff0f1fd98f 0xfe0ffc9ff878fecc

def z929 : W := mkw 0x02aa949602001104 0x001554a4b0100088 0x87ff9fff3e0079ff 0xfc3ffcfff9f003cf

def z930 : W := mkw 0x4083da1b070dddc6 0x22041ed0d8386eee 0xe79ffe3f3f1fffff 0xff3cfff1f9f8ffff

def z931 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0xf870f3f8c1fc7f9f 0xffc3879fc60fe3fc

def z932 : W := mkw 0x022804c51062a0a9 0x4011402628831505 0xc6681dc731e3a1fd 0xb63340ee398f1d0f

def z933 : W := mkw 0x4082dedf0324fde7 0x620416f6f81927ef 0x2000ffff00007fe6 0x010007fff80003ff

def z934 : W := mkw 0x3ffefdb6b8420008 0x01fff7edb5c21000 0xffffffffffe3801f 0xffffffffffff1c00

def z935 : W := mkw 0x37aefdb6aa001546 0x01bd77edb55000aa 0xbf8ffffffe007ffe 0xfdfc7ffffff003ff

def z936 : W := mkw 0x0850236941b4eab1 0xc042811b4a0da755 0x7870e3f8c1fc7fff 0x7bc3871fc60fe3ff

def z937 : W := mkw 0x0851000044990010 0x004288000224c800 0xc1ff00000fff8009 0xde0ff800007ffc00

def z938 : W := mkw 0xbffefdb650d20018 0x05fff7edb2869000 0x3fffffff00e00007 0xf1fffffff8070000

def z939 : W := mkw 0xbffefdb6f8d20018 0x05fff7edb7c69000 0xbffffffffee0001f 0xfdfffffffff70000

def z940 : W := mkw 0x2afefdb600000000 0x0157f7edb0000000 0x387fffff00000007 0x71c3fffff8000000

def z941 : W := mkw 0xbffefdb6b8420008 0x05fff7edb5c21000 0x3fffffff30000007 0xf1fffffff9800000

def z942 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xfe687fc7f1e3e7ff 0xb7f343fe3f8f1f3f

def z943 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0x46681fc731e3e1f7 0x223340fe398f1f0f

def z944 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc79f9e3f0f1fd98f 0xfe3cfcf1f878fecc

def z945 : W := mkw 0xbf7c6da4f8d2045a 0x05fbe36d27c69022 0x3e606dc0f0e02674 0x21f3036e07870133

def z946 : W := mkw 0x0000024801246801 0x0000001240092340 0x7870e3f8c1fc7e1f 0x7bc3871fc60fe3f0

def z947 : W := mkw 0x9f7d2120fcdb0018 0x04fbe90907e6d800 0xffffe3f8fffffe1f 0xffffff1fc7fffff0

def z948 : W := mkw 0xbf7d25a4fcdb0018 0x05fbe92d27e6d800 0xdfff01c0ffff8019 0xfefff80e07fffc00

def z949 : W := mkw 0x9d550000fcdb0018 0x04eaa80007e6d800 0xd99f0000ffff8019 0xdeccf80007fffc00

def z950 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0x3f80fc00fe007ff6 0x69fc07e007f003ff

def z951 : W := mkw 0x08d2b13202001104 0x0046958990100088 0xb9fff3ffce007f9f 0xfdcfff9ffe7003fc

def z952 : W := mkw 0x1f7d0000144b0008 0x00fbe80000a25800 0xdfff00003fff8019 0xfefff80001fffc00

def z953 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff1c00ffff801f 0xfefff8e007fffc00

def z954 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff30002077 0xf1fffffff9800103

def z955 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xe668ffc731e3ffff 0xb73347fe398f1fff

def z956 : W := mkw 0x1582d812aa001546 0x00ac16c0955000aa 0xbf80fe3ffe007ffe 0xfdfc07f1fff003ff

def z957 : W := mkw 0x4001024947bdfb95 0xa20008124a3defdc 0xc00000000fffd988 0x0e000000007ffecc

def z958 : W := mkw 0x37aefdb600000000 0x01bd77edb0000000 0x078f1fff00000000 0x803c78fff8000000

def z959 : W := mkw 0x3ffefdb640900010 0x01fff7edb2048000 0x3fffffffc01c0007 0xf9fffffffe00e000

def z960 : W := mkw 0x4083925b072df9a5 0x62041c92d8396fcd 0xc19f923f0f1ff9eb 0xde0cfc91f878ffcf

def z961 : W := mkw 0x3ffefdb6a8000000 0x01fff7edb5400000 0xbffffffffe0061ff 0xfdfffffffff0030f

def z962 : W := mkw 0x9f7d0484fcdb0018 0x04fbe82427e6d800 0xdfff0dc0ffff801d 0xfefff86e07fffc00

def z963 : W := mkw 0x4083925b072df985 0x22041c92d8396fcc 0xf9fff3ffcfffff9f 0xffcfff9ffe7ffffc

def z964 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc7f1e3ffff 0xbe3340fe3f8f1fff

def z965 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e381f9 0xb63340fe398f1c0f

def z966 : W := mkw 0x3ffefdb6aa001104 0x01fff7edb5500088 0xbffffffffe00599f 0xfdfffffffff002cc

def z967 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x7fffffff01e0001f 0xf3fffffff80f0000

def z968 : W := mkw 0x3f7e25b600000000 0x01fbf12db0000000 0x1e7f03ff00000001 0x20f3f81ff8000000

def z969 : W := mkw 0xbffefdb6f8d20018 0x05fff7edb7c69000 0xfffffffff1e3801f 0xf7ffffffff8f1c00

def z970 : W := mkw 0x2afefdb600000000 0x0157f7edb0000000 0x267fffff00000007 0xb133fffff8000000

def z971 : W := mkw 0x4083925b072df985 0x22041c92d8396fcc 0xc19f923f0ffff99b 0xde0cfc91f87fffcc

def z972 : W := mkw 0x022a049600000000 0x00115024b0000000 0x067f1fff00000007 0xb033f8fff8000000

def z973 : W := mkw 0x2afeb5b600000000 0x0157f5adb0000000 0x07ff9fff00000007 0xf03ffcfff8000000

def z974 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbffffffffe001e1f 0xfdfffffffff000f0

def z975 : W := mkw 0x3f7e6db600000000 0x01fbf36db0000000 0x3e7f7fff00000007 0xb1f3fbfff8000000

def z976 : W := mkw 0x2082fdb600000000 0x010417edb0000000 0x218fffff00000006 0x810c7ffff8000000

def z977 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f823f0f1f9809 0xde0cfc11f878fcc0

def z978 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffffc0002617 0xf1fffffffe000130

def z979 : W := mkw 0x3f7e25b600000000 0x01fbf12db0000000 0x1fff1fff00000007 0xf0fff8fff8000000

def z980 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923f3f1ff9fb 0xde0cfc91f9f8ffcf

def z981 : W := mkw 0x0850236941b4ea91 0x8042811b4a0da754 0xfe78fffff1ffffff 0xfff3c7ffff8fffff

def z982 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x39ffe3ff00000007 0x71cfff1ff8000000

def z983 : W := mkw 0x5581da49efbdffd7 0xa2ac0ed24f7deffe 0xff80fc00fffffffe 0xfffc07e007ffffff

def z984 : W := mkw 0x4082925b0324f985 0x22041492d81927cc 0x000093ff00007986 0x0000049ff80003cc

def z985 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0xc19f023f0f1f8001 0x860cf811f878fc00

def z986 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xf99ff23fcf1fdf8b 0xdfccff91fe78fefc

def z987 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x207fe3ff00000007 0x0103ff1ff8000000

def z988 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fff7fff00000005 0xa1fffbfff8000000

def z989 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xff9ffe3fff1fffff 0xfffcfff1fff8ffff

def z990 : W := mkw 0x4082b7ff0324fba5 0xe20415bff81927dd 0x2000ffff00007fe6 0x010007fff80003ff

def z991 : W := mkw 0x3dd6fdb6aa001546 0x01eeb7edb55000aa 0xbf97fffffe007ffe 0xfdfcbffffff003ff

def z992 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff00007e07 0xf1fffffff80003f0

def z993 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0000ffffe01f 0xfefff80007ffff00

def z994 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xbfffffff300001e7 0xf5fffffff980000f

def z995 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xffffffff0103800f 0xf7fffffff8081c00

def z996 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x3870e3f8c0fc7e16 0x69c3871fc607e3f0

def z997 : W := mkw 0x5dd3f93aee9d1f56 0xa2ee9fc9d774e8fa 0x3997e038ce1c1e00 0x49ccbf01c670e0f0

def z998 : W := mkw 0x4082925b0324fb85 0xa2041492d81927dc 0x0000923f00007f82 0x00000491f80003fc

def z999 : W := mkw 0x4083901b060d9984 0x22041c80d8306ccc 0x819f923f0e1f9983 0xdc0cfc91f870fccc

def z1000 : W := mkw 0x9f7d0484fcdb0038 0x44fbe82427e6d801 0xdfff0c00ffff8079 0xfefff86007fffc03

def z1001 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923f0f1f8183 0xd60cfc91f878fc0c

def z1002 : W := mkw 0x1f7d000044990010 0x00fbe8000224c800 0xdfff0000cfff8019 0xfefff800067ffc00

def z1003 : W := mkw 0x6082ffff0324fb85 0xa30417fff81927dc 0x2000ffff00007f86 0x010007fff80003fc

def z1004 : W := mkw 0x3ffefdb602001546 0x01fff7edb01000aa 0x3fffffffc0007fff 0xf9fffffffe0003ff

def z1005 : W := mkw 0x3dd6fdb600000000 0x01eeb7edb0000000 0x399fffff00000007 0xd1ccfffff8000000

def z1006 : W := mkw 0x3f7e6db600000000 0x01fbf36db0000000 0x3e7fefff00000007 0x71f3ff7ff8000000

def z1007 : W := mkw 0x1ffeb13200000000 0x00fff58990000000 0x3ffff3ff00000007 0xf1ffff9ff8000000

def z1008 : W := mkw 0x3ffefdb640900010 0x01fff7edb2048000 0x7fffffffc1fc7e1f 0xfbfffffffe0fe3f0

def z1009 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0xc19f823f0f1fd80b 0xde0cfc11f878fec0

def z1010 : W := mkw 0x3dd6f93200000000 0x01eeb7c990000000 0x39fff3ff00000007 0xf1cfff9ff8000000

def z1011 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xbfffffff0e00000f 0xfdfffffff8700000

def z1012 : W := mkw 0x4001024945bdea91 0xa20008124a2def54 0x40000000c1fffe18 0x0a000000060ffff0

def z1013 : W := mkw 0x2082fdb600000000 0x010417edb0000000 0x201fffff00000007 0x0100fffff8000000

def z1014 : W := mkw 0x972d0000bc4b0008 0x04b9680005e25800 0xc7ff00003fff8019 0xfe3ff80001fffc00

def z1015 : W := mkw 0x222e25b600000000 0x0111712db0000000 0x000f03ff00000000 0x0000781ff8000000

def z1016 : W := mkw 0x57abdc97be4b95ee 0x62bd5ee4bdf25caf 0x878f1c073e0381e0 0x843c78e039f01c0f

def z1017 : W := mkw 0x15004800aa001546 0x00a80240055000aa 0xbe00ec00fe007ffe 0x7df0076007f003ff

def z1018 : W := mkw 0x0850212840940a10 0x804281094204a050 0x7870e3f8c1fc1e1f 0x7bc3871fc60fe0f0

def z1019 : W := mkw 0x0082949600000000 0x000414a4b0000000 0x019f9fff00000007 0xd00cfcfff8000000

def z1020 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e3e1e7 0x863340fe398f1f0f

def z1021 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x007f03ff00000007 0x3003f81ff8000000

def z1022 : W := mkw 0x000002410120e081 0x0000001208090704 0xc6681fc731e3e1ff 0xb63340fe398f1f0f

def z1023 : W := mkw 0x28d2fdb600000000 0x014697edb0000000 0x39ffffff00000007 0xf1cffffff8000000

def z1024 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff03c0ffff801f 0xfefff81e07fffc00

def z1025 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffefff00000005 0x61ffff7ff8000000

def z1026 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x7fffffff011c000f 0xfbfffffff808e000

def z1027 : W := mkw 0x40010249072df985 0x2200081248396fcc 0xc00000000ffff998 0x0e000000007fffcc

def z1028 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e381e7 0xb63340fe398f1c0f

def z1029 : W := mkw 0xbffefdb6f8d20018 0x05fff7edb7c69000 0x7ffffffff1fc001f 0xfbffffffff8fe000

def z1030 : W := mkw 0x4083901b060d9984 0x22041c80d8306ccc 0x819f103f0e1f8180 0x840cf881f870fc0c

def z1031 : W := mkw 0x022806cd1166e8a9 0x40114036688b3745 0xc6681fc731fff9ff 0xbe3340fe398fffcf

def z1032 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc7e17 0x23c3871fc60fe3f0

def z1033 : W := mkw 0x9d550000fcdb0018 0x04eaa80007e6d800 0xd9f70000ffff8019 0x7ecfb80007fffc00

def z1034 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f123f0f1fc18b 0x960cf891f878fe0c

def z1035 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x387fe3ff00000001 0x41c3ff1ff8000000

def z1036 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x39ffffff00000007 0x41cffffff8000000

def z1037 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6789fff31e3e1ff 0xf633c4fff98f1f0f

def z1038 : W := mkw 0x9f7d4800fcdb045a 0x04fbea4007e6d822 0xffffec00fffffe7f 0xffffff6007fffff3

def z1039 : W := mkw 0x40010249156fe8a9 0x6200081248ab7f45 0xc000000031ffe1f8 0x06000000018fff0f

def z1040 : W := mkw 0x9f7d25a4fcdb0018 0x04fbe92d27e6d800 0xffffffffffff801f 0xfffffffffffffc00

def z1041 : W := mkw 0x4083da1b070dddc6 0x22041ed0d8386eee 0xf99ffe3fcf1fffff 0xffccfff1fe78ffff

def z1042 : W := mkw 0x9f7d0484fcdb0018 0x04fbe82427e6d800 0xdfff1fc7ffffe1ff 0xfefff8fe3fffff0f

def z1043 : W := mkw 0x0a79000054db0018 0x0053c80002a6d800 0xdfff0000ffff8019 0xfefff80007fffc00

def z1044 : W := mkw 0x3ffefdb610420008 0x01fff7edb0821000 0x7fffffff01e38007 0xf3fffffff80f1c00

def z1045 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xd9ff0000ffff8019 0x4ecff80007fffc00

def z1046 : W := mkw 0x3ffefdb6a8000000 0x01fff7edb5400000 0xbfffffff3e000007 0xf5fffffff9f00000

def z1047 : W := mkw 0x0228048410420008 0x0011402420821000 0xc6681fc731e3e1ff 0xb63340fe398f1f0f

def z1048 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f903f0f1fd988 0xce0cfc81f878fecc

def z1049 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x3fffffffce007e1f 0xf9fffffffe7003f0

def z1050 : W := mkw 0x4083901b060d9984 0x22041c80d8306ccc 0x819f903f0e1fd98a 0xdc0cfc81f870fecc

def z1051 : W := mkw 0x9d550000ec990010 0x04eaa8000764c800 0xd9ff0000cfff8019 0xfecff800067ffc00

def z1052 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbffffffffe0001ff 0xfdfffffffff0000f

def z1053 : W := mkw 0x4083921b050dc880 0x22041c90d8286e44 0xc19f923f0f1f800b 0xde0cfc91f878fc00

def z1054 : W := mkw 0x1f7c25a400000000 0x00fbe12d20000000 0x3fffffff00000007 0xf1fffffff8000000

def z1055 : W := mkw 0x3ffefdb6e8900010 0x01fff7edb7448000 0xfffffffffffc001f 0xffffffffffffe000

def z1056 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x387f63ff00000005 0x21c3fb1ff8000000

def z1057 : W := mkw 0xb7afdc96be4b154e 0x05bd7ee4b5f258aa 0x878f1c073e0381e0 0x843c78e039f01c0f

def z1058 : W := mkw 0x3dd6fdb600000000 0x01eeb7edb0000000 0x3997e3ff00000000 0x41ccbf1ff8000000

def z1059 : W := mkw 0x2082b5b600000000 0x010415adb0000000 0x019f93ff00000003 0xd00cfc9ff8000000

def z1060 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc5e0b 0x5bc3871fc60fe2f0

def z1061 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x067f0fff00000005 0x2033f87ff8000000

def z1062 : W := mkw 0x3582fdb600000000 0x01ac17edb0000000 0x3f9fffff00000007 0xf1fcfffff8000000

def z1063 : W := mkw 0xbf7d6da4fcdb0018 0x05fbeb6d27e6d800 0xffff7fc7ffff801f 0xfffffbfe3ffffc00

def z1064 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x187f03ff00000001 0x70c3f81ff8000000

def z1065 : W := mkw 0x80010249fdffeab9 0xc40008124fefff55 0xc0000000fffffff8 0x0e00000007ffffff

def z1066 : W := mkw 0x0001000004090000 0x0000080000204800 0xc1ff00000fff8019 0xfe0ff800007ffc00

def z1067 : W := mkw 0x9f7d4800fcdb045a 0x04fbea4007e6d822 0xffff7c00ffffe7ff 0xfffffbe007ffff3f

def z1068 : W := mkw 0x37aedc9600000000 0x01bd76e4b0000000 0x07ff9fff00000007 0xf03ffcfff8000000

def z1069 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffe3ff00000001 0xf1ffff1ff8000000

def z1070 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x007f1fff00000007 0x0003f8fff8000000

def z1071 : W := mkw 0x022804c51062a0a9 0x4011402628831505 0x86681fc730e3a1f7 0xb43340fe39871d0f

def z1072 : W := mkw 0x37aefdb600000000 0x01bd77edb0000000 0x279fffff00000007 0xd13cfffff8000000

def z1073 : W := mkw 0xbf7d6da4fcdb0018 0x05fbeb6d27e6d800 0xffffeff8ffff801f 0xffffff7fc7fffc00

def z1074 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbfffffff3e0059ef 0xfdfffffff9f002cf

def z1075 : W := mkw 0x2a7e25b640900010 0x0153f12db2048000 0x587f03ffc1fc0019 0x7ac3f81ffe0fe000

def z1076 : W := mkw 0x3f7e6db6a8000442 0x01fbf36db5400022 0x3e7f6ffff0002675 0x21f3fb7fff800133

def z1077 : W := mkw 0x9f7d0000fcdb045a 0x04fbe80007e6d822 0xdfff0000ffffa679 0xfefff80007fffd33

def z1078 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbfe0ffc0fe007fff 0xfdff07fe07f003ff

def z1079 : W := mkw 0x15000000a8000000 0x00a8000005400000 0xbf80fc00fe007ffe 0xfdfc07e007f003ff

def z1080 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff000061e7 0xf1fffffff800030f

def z1081 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x27ffffff00000007 0x813ffffff8000000

def z1082 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x39fff3ff00000003 0xd1cfff9ff8000000

def z1083 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x07ff9fff00000003 0xd03ffcfff8000000

def z1084 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f123f0f1f8189 0xde0cf891f878fc0c

def z1085 : W := mkw 0x022806cd1166e8a9 0x40114036688b3745 0xfe78fffff1ffffff 0xfff3c7ffff8fffff

def z1086 : W := mkw 0x3ffefdb600000442 0x01fff7edb0000022 0x3fffffff00002667 0xf1fffffff8000133

def z1087 : W := mkw 0x0852213200000000 0x0042910990000000 0x387fe3ff00000007 0x71c3ff1ff8000000

def z1088 : W := mkw 0x285625b600000000 0x0142b12db0000000 0x001703ff00000000 0x0000b81ff8000000

def z1089 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681dc731e3e1fc 0xa63340ee398f1f0f

def z1090 : W := mkw 0x4083925b072dfb85 0xa2041c92d8396fdc 0xc19f923f0f1fff8b 0xde0cfc91f878fffc

def z1091 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x419f923f0f1fd983 0x4a0cfc91f878fecc

def z1092 : W := mkw 0x3ffefdb602001546 0x01fff7edb01000aa 0x3fffffff00001e07 0xf1fffffff80000f0

def z1093 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff8000ffffd81b 0xfefffc0007fffec0

def z1094 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6681fc731e3c1eb 0x963340fe398f1e0f

def z1095 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x87ff1fff3e0001e1 0x843ff8fff9f0000f

def z1096 : W := mkw 0x95050000fcdb0018 0x04a8280007e6d800 0xc1870000ffff8018 0x0e0c380007fffc00

def z1097 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbfffffffce005f8f 0xfdfffffffe7002fc

def z1098 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7870e3f8c1fc3e15 0x6bc3871fc60fe1f0

def z1099 : W := mkw 0x6082ffff0324f9a5 0x630417fff81927cd 0x2000ffff000079e6 0x010007fff80003cf

def z1100 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0x5fff0000ffff8011 0x6afff80007fffc00

def z1101 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf9ffc00fe007fff 0xfdfcffe007f003ff

def z1102 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x07ff1fff00000007 0xb03ff8fff8000000

def z1103 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0c00ffffa07d 0xfefff86007fffd03

def z1104 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x067f03ff00000001 0xb033f81ff8000000

def z1105 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbe00fc00fe007ffe 0x2df007e007f003ff

def z1106 : W := mkw 0x40010249072df9a5 0x6200081248396fcd 0xc00000000f1ff9e8 0x0e0000000078ffcf

def z1107 : W := mkw 0x0083921a050d4800 0x00041c90d0286a40 0xc19f923f0f1fd80b 0xde0cfc91f878fec0

def z1108 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x819f923f0e1fd982 0xcc0cfc91f870fecc

def z1109 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x007f13ff00000003 0x9003f89ff8000000

def z1110 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0000ffff8011 0xa6fff80007fffc00

def z1111 : W := mkw 0x4083925b072df985 0x22041c92d8396fcc 0xc19f93ff0f1ff98f 0xde0cfc9ff878ffcc

def z1112 : W := mkw 0x4a7b27ff55ffeab9 0xe253d93ffaafff55 0x407f03ff01ff8001 0x0203f81ff80ffc00

def z1113 : W := mkw 0x4003021b050dc880 0x22001810d8286e44 0xc19f123f0f1fc18b 0xde0cf891f878fe0c

def z1114 : W := mkw 0x0082b13200000000 0x0004158990000000 0x219ff3ff00000007 0xd10cff9ff8000000

def z1115 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fffffff00000001 0xc1fffffff8000000

def z1116 : W := mkw 0x17aadc9600000000 0x00bd56e4b0000000 0x3fffffff00000007 0xf1fffffff8000000

def z1117 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdf9f0000ffff8018 0xcefcf80007fffc00

def z1118 : W := mkw 0x17290000bc4b0008 0x00b9480005e25800 0xdfff0000ffff8019 0xfefff80007fffc00

def z1119 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc7ff1fc731e3e1ff 0xf63ff8fe398f1f0f

def z1120 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff1000ffffc19b 0xfefff88007fffe0c

def z1121 : W := mkw 0x9f7d4800fcdb045a 0x04fbea4007e6d822 0xdfff0c00ffff8079 0xfefff86007fffc03

def z1122 : W := mkw 0x0001000044990010 0x000008000224c800 0xc19f0000cfff8019 0xde0cf800067ffc00

def z1123 : W := mkw 0x0850236841b46a11 0x8042811b420da350 0x7860e3f8c1fc7e1e 0x2bc3071fc60fe3f0

def z1124 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff0000ffff8001 0xcefff80007fffc00

def z1125 : W := mkw 0xbffefdb6e8900010 0x05fff7edb7448000 0x3fffffffc0000007 0xf1fffffffe000000

def z1126 : W := mkw 0x2afeb5b600000000 0x0157f5adb0000000 0x01ff13ff00000001 0x800ff89ff8000000

def z1127 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xffffe000ffff801f 0xffffff0007fffc00

def z1128 : W := mkw 0x8a7d000054db0018 0x0453e80002a6d800 0xd9ff0000cfff8019 0xfecff800067ffc00

def z1129 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xfffffc00ffffffff 0xffffffe007ffffff

def z1130 : W := mkw 0x3ffefdb6a8000000 0x01fff7edb5400000 0x3fffffffce000007 0xf9fffffffe700000

def z1131 : W := mkw 0x3586fdb600000000 0x01ac37edb0000000 0x2187ffff00000006 0x010c3ffff8000000

def z1132 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x007f83ff00000003 0x5003fc1ff8000000

def z1133 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x1fff1fff00000001 0xf0fff8fff8000000

def z1134 : W := mkw 0x200225b600000000 0x0100112db0000000 0x001f03ff00000001 0x0000f81ff8000000

def z1135 : W := mkw 0x0850236941b4ea91 0x8042811b4a0da754 0x7878e3ffc1fffe1f 0x7bc3c71ffe0ffff0

def z1136 : W := mkw 0x02280485104280a8 0x4011402428821405 0xc6681fc731e381ff 0xb63340fe398f1c0f

def z1137 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x067f1fff00000001 0x8033f8fff8000000

def z1138 : W := mkw 0x1d510000ec990010 0x00ea88000764c800 0xdfff0000ffff8019 0xfefff80007fffc00

def z1139 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80ec00fe007ffc 0x6dfc076007f003ff

def z1140 : W := mkw 0x88510000fcdb0018 0x0442880007e6d800 0xd9ff0000ffff8019 0xfecff80007fffc00

def z1141 : W := mkw 0x3ffefdb602001104 0x01fff7edb0100088 0xbfffffffce007f9f 0xfdfffffffe7003fc

def z1142 : W := mkw 0x37aefdb600000000 0x01bd77edb0000000 0x27efffff00000007 0xb13f7ffff8000000

def z1143 : W := mkw 0x4081924947bdfb95 0xa2040c924a3defdc 0xf980f000cfffff9e 0xffcc0780067ffffc

def z1144 : W := mkw 0x0850216840b42a11 0x8042810b4205a150 0x3870e3f8c0fc3e17 0x79c3871fc607e1f0

def z1145 : W := mkw 0x4083901a060d1904 0x22041c80d03068c8 0xc19f923f0f1f980b 0xde0cfc91f878fcc0

def z1146 : W := mkw 0x2afefdb600000000 0x0157f7edb0000000 0x207fe3ff00000001 0x0103ff1ff8000000

def z1147 : W := mkw 0x022806c51162e0a9 0x40114036288b1705 0xc6601fc731e3e1fe 0x263300fe398f1f0f

def z1148 : W := mkw 0x0850236941b4ea91 0x8042811b4a0da754 0x7870f3ffc1fc7f9f 0x7bc3879ffe0fe3fc

def z1149 : W := mkw 0x2afeb5b600000000 0x0157f5adb0000000 0x01ff83ff00000001 0x400ffc1ff8000000

def z1150 : W := mkw 0x80010000fcdb0018 0x0400080007e6d800 0xc1970000ffff8018 0x4e0cb80007fffc00

def z1151 : W := mkw 0x3f7e6db600000000 0x01fbf36db0000000 0x387f63ff00000001 0x01c3fb1ff8000000

def z1152 : W := mkw 0x1580d800aa001546 0x00ac06c0055000aa 0xbf80fc00fe007ff6 0xa5fc07e007f003ff

def z1153 : W := mkw 0x5581da49bf6ffdef 0x62ac0ed24dfb7fef 0xff80fc00fffffffe 0xfffc07e007ffffff

def z1154 : W := mkw 0x3ffefdb602001546 0x01fff7edb01000aa 0x3fffffff000001e7 0xf1fffffff800000f

def z1155 : W := mkw 0x3f7e25b600000000 0x01fbf12db0000000 0x19ff03ff00000001 0x40cff81ff8000000

def z1156 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbfffffff3e0061ff 0xf5fffffff9f0030f

def z1157 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0xbffffffffe001fe7 0xfdfffffffff000ff

def z1158 : W := mkw 0x02290000144b0008 0x0011480000a25800 0xc1ff00000fff8009 0xde0ff800007ffc00

def z1159 : W := mkw 0x3ffefdb6ba42154e 0x01fff7edb5d210aa 0xffffffffffe3ffff 0xffffffffffff1fff

def z1160 : W := mkw 0x4001024945bdea91 0xa20008124a2def54 0x4000000001ff8000 0x02000000000ffc00

def z1161 : W := mkw 0x2afefdb600000000 0x0157f7edb0000000 0x21ffffff00000007 0xd10ffffff8000000

def z1162 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f923f0f1ff99f 0xfe0cfc91f878ffcc

def z1163 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc19f823f0f1fd989 0x4e0cfc11f878fecc

def z1164 : W := mkw 0x40819249176ff9ad 0x62040c9248bb7fcd 0xc7809c003ffff9fe 0xfe3c04e001ffffcf

def z1165 : W := mkw 0x2a7e25b600000000 0x0153f12db0000000 0x387fe3ffc0007e1f 0x79c3ff1ffe0003f0

def z1166 : W := mkw 0x3ffefdb6aa001546 0x01fff7edb55000aa 0x3ffffffff0007ff7 0xf1ffffffff8003ff

def z1167 : W := mkw 0x8a7d27ed55ffeab9 0xc453e93f6aafff55 0x407f03ff01ff8001 0x0203f81ff80ffc00

def z1168 : W := mkw 0x4003021b070dd984 0x22001810d8386ecc 0xc19f023f0f1fd989 0xde0cf811f878fecc

def z1169 : W := mkw 0x0afab5b600000000 0x0057d5adb0000000 0x3fffffff00000007 0xf1fffffff8000000

def z1170 : W := mkw 0x9f7d0484fcdb0018 0x04fbe82427e6d800 0xdfff1c07ffff8019 0xfefff8e03ffffc00

def z1171 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x419f023f0f1f8001 0x020cf811f878fc00

def z1172 : W := mkw 0x9f7d0000fcdb0018 0x04fbe80007e6d800 0xdfff00003fff8001 0xf6fff80001fffc00

def z1173 : W := mkw 0x3dd6fdb600000000 0x01eeb7edb0000000 0x39f7ffff00000007 0x71cfbffff8000000

def z1174 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0x3fefffff00000006 0xa1ff7ffff8000000

def z1175 : W := mkw 0x3ffefdb600000000 0x01fff7edb0000000 0xbfffffff3000001f 0xf5fffffff9800000

def z1176 : W := mkw 0x022806cd1166e8a9 0x40114036688b3745 0xc6781fff31ffe1ff 0xb633c0fff98fff0f

def z1177 : W := mkw 0x3582fdb6aa001546 0x01ac17edb55000aa 0xbf9ffffffe007fff 0xfdfcfffffff003ff

def z1178 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0xc79f923f3f1fd99b 0xfe3cfc91f9f8fecc

def z1179 : W := mkw 0x4083921b070dd984 0x22041c90d8386ecc 0x419f823f0f1fd80b 0x5a0cfc11f878fec0

def z1180 : W := mkw 0x1dd2f93200000000 0x00ee97c990000000 0x3fffffff00000007 0xf1fffffff8000000

def z1181 : W := mkw 0x408296df0324f9a5 0x620414b6f81927cd 0x000093ff00005982 0x0000049ff80002cc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z8,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z6])],[(0,[z10,z0,z1,z2,z11,z4,z6]),(0,[z0,z1,z2,z3,z12,z4,z6])],[(1,[z0,z1,z13,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z15]),(0,[z0,z1,z2,z3,z4,z6,z16])],[(0,[z0,z1,z8,z2,z3,z4,z17])],[(0,[z0,z1,z18,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z19,z6])],[(0,[z0,z1,z2,z20,z3,z4,z6])],[(0,[z0,z1,z2,z3,z21,z22,z6]),(0,[z0,z1,z23,z2,z3,z4,z6]),(0,[z0,z1,z2,z24,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z6])],[(0,[z0,z1,z2,z26,z3,z4,z6]),(0,[z27,z0,z28,z2,z3,z4,z6]),(0,[z0,z1,z29,z2,z14,z4,z6]),(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z31,z3,z4,z6])]],
   [[(0,[z32,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z33,z3,z4,z6]),(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z35,z0,z1,z2,z14,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z37,z3,z4,z6]),(0,[z38,z0,z1,z2,z3,z4,z6])],[(0,[z39,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z4,z6]),(0,[z41,z0,z1,z2,z3,z21,z6]),(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z43,z4,z6]),(0,[z7,z0,z1,z2,z3,z44,z6])],[(0,[z45,z1,z46,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z48,z4,z6]),(0,[z49,z0,z1,z2,z3,z4,z50]),(1,[z51,z0,z2,z52,z4,z6]),(0,[z0,z1,z2,z3,z4,z53,z6])],[(0,[z54,z0,z1,z2,z3,z4,z6]),(0,[z0,z55,z1,z2,z3,z4,z6]),(0,[z0,z56,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z57,z6]),(0,[z0,z1,z2,z3,z4,z25,z58]),(0,[z0,z1,z59,z2,z3,z4,z6])],[(0,[z0,z1,z60,z2,z3,z4,z6]),(0,[z61,z0,z1,z2,z3,z4,z6]),(0,[z49,z1,z2,z3,z4,z58,z6]),(0,[z0,z1,z2,z62,z3,z4,z6]),(0,[z63,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z64,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z6]),(0,[z66,z0,z1,z2,z3,z6,z67])],[(0,[z35,z0,z1,z2,z68,z4,z6]),(0,[z0,z1,z2,z3,z4,z69,z6])],[(0,[z70,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z71]),(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z73,z2,z3,z4,z6])],[(0,[z74,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z6]),(0,[z0,z1,z2,z76,z3,z4,z6])]],
   [[(0,[z45,z1,z2,z3,z77,z4,z6]),(0,[z0,z78,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z64,z4,z6]),(0,[z0,z1,z2,z79,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z81])],[(1,[z0,z1,z2,z3,z4,z82]),(0,[z83,z0,z1,z2,z3,z4,z6]),(0,[z84,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z85,z3,z14,z4,z6]),(1,[z0,z1,z8,z3,z4,z15])],[(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z87,z1,z60,z2,z3,z4,z6]),(0,[z88,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z3,z4,z6]),(0,[z27,z90,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z14,z4,z6])],[(0,[z91,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z92,z4,z6])],[(0,[z93,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z22,z6]),(1,[z0,z1,z2,z37,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z15]),(0,[z0,z1,z2,z3,z4,z94,z6])],[(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z96,z1,z2,z3,z4,z22,z6]),(0,[z97,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z98,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z99]),(0,[z0,z1,z2,z3,z100,z9,z6])],[(0,[z0,z1,z2,z3,z101,z77,z6]),(0,[z0,z1,z2,z3,z4,z102,z6]),(0,[z66,z0,z1,z2,z3,z103,z6])],[(1,[z0,z1,z2,z3,z4,z104]),(0,[z0,z1,z2,z3,z105,z4,z6]),(1,[z49,z1,z2,z3,z4,z58]),(0,[z0,z1,z2,z3,z4,z58,z15]),(0,[z0,z1,z2,z3,z4,z106,z6]),(0,[z0,z1,z107,z2,z3,z4,z6])]],
   [[(0,[z108,z45,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z109,z4,z6]),(0,[z0,z1,z2,z3,z110,z4,z6]),(0,[z0,z111,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z112]),(0,[z0,z1,z2,z3,z4,z6,z113]),(0,[z0,z114,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z115,z4,z6]),(0,[z0,z116,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z117,z3,z4,z6]),(0,[z0,z1,z2,z3,z101,z9,z6])],[(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z28,z29,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z119]),(0,[z51,z0,z2,z52,z3,z4,z6])],[(1,[z0,z120,z2,z3,z4,z6]),(0,[z0,z121,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z105,z4,z6]),(0,[z0,z1,z2,z3,z122,z4,z6]),(0,[z0,z111,z1,z2,z123,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z125,z4,z6])],[(0,[z0,z1,z60,z2,z126,z4,z6]),(0,[z27,z0,z1,z2,z3,z4,z127])],[(0,[z0,z1,z2,z3,z4,z6,z128]),(0,[z0,z1,z2,z3,z4,z6,z129]),(0,[z130,z0,z1,z2,z3,z103,z6]),(0,[z0,z1,z2,z3,z4,z131,z6])],[(1,[z96,z1,z2,z3,z22,z6]),(0,[z51,z0,z1,z2,z52,z4,z6]),(0,[z0,z1,z13,z2,z14,z4,z6]),(0,[z0,z1,z132,z2,z3,z4,z6]),(0,[z0,z1,z2,z133,z3,z4,z6]),(0,[z134,z0,z1,z2,z3,z4,z6])],[(0,[z108,z135,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z136,z4,z6]),(0,[z137,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z138,z6]),(0,[z139,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z140,z2,z3,z4,z6]),(0,[z0,z1,z2,z141,z4,z22,z6]),(0,[z0,z90,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z52,z3,z4,z6]),(0,[z7,z0,z1,z3,z4,z17,z6])],[(0,[z0,z1,z142,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z143,z6]),(0,[z0,z1,z144,z2,z3,z4,z6]),(0,[z0,z1,z145,z2,z3,z4,z6]),(0,[z0,z1,z2,z146,z85,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z148,z6])],[(0,[z0,z1,z2,z3,z4,z6,z149]),(0,[z0,z1,z2,z150,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z151,z6]),(0,[z0,z1,z2,z3,z152,z4,z6]),(0,[z0,z1,z2,z3,z22,z103,z6]),(0,[z0,z1,z2,z85,z77,z4,z6]),(0,[z0,z1,z2,z3,z153,z4,z6]),(0,[z0,z1,z2,z154,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z155,z6]),(0,[z0,z1,z156,z2,z3,z4,z6]),(0,[z0,z157,z1,z2,z3,z4,z6])],[(0,[z0,z111,z1,z2,z3,z4,z158]),(0,[z0,z1,z2,z3,z159,z4,z6]),(0,[z0,z1,z2,z160,z3,z4,z6])],[(0,[z108,z0,z135,z2,z3,z4,z6]),(0,[z0,z55,z1,z2,z4,z22,z6]),(0,[z0,z1,z161,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z6]),(0,[z0,z162,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z85,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z163,z6]),(0,[z0,z1,z2,z164,z85,z4,z6]),(0,[z0,z1,z2,z165,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z17])],[(0,[z166,z0,z1,z2,z3,z4,z6])],[(0,[z167,z0,z1,z2,z3,z4,z6]),(0,[z0,z168,z1,z2,z3,z4,z6]),(0,[z0,z169,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z170]),(0,[z0,z1,z2,z4,z9,z6,z171])]],
   [[(0,[z0,z1,z2,z3,z48,z4,z6]),(0,[z0,z1,z2,z172,z3,z4,z6]),(0,[z45,z0,z1,z2,z14,z4,z6]),(0,[z173,z0,z1,z2,z3,z100,z4]),(0,[z174,z0,z1,z2,z3,z4,z6])],[(0,[z0,z111,z1,z2,z52,z4,z6]),(0,[z0,z1,z2,z3,z175,z4,z6]),(0,[z176,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z177,z3,z14,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z178]),(0,[z0,z1,z2,z3,z179,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z113])],[(0,[z180,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z181,z6]),(0,[z0,z1,z2,z3,z4,z50,z15]),(0,[z0,z1,z2,z3,z4,z6,z182]),(0,[z0,z2,z3,z21,z4,z69,z6]),(0,[z0,z1,z2,z68,z4,z6,z113])],[(1,[z0,z1,z2,z48,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z184]),(0,[z0,z1,z2,z185,z3,z4,z6]),(0,[z0,z1,z2,z3,z186,z4,z6])],[(0,[z187,z0,z1,z2,z3,z4,z6]),(0,[z173,z0,z1,z2,z105,z4,z6]),(0,[z0,z1,z2,z3,z4,z58,z113]),(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z189,z3,z4,z6]),(0,[z0,z190,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z191,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z9]),(0,[z192,z0,z1,z2,z3,z4,z6]),(0,[z193,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z194,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z195,z6])],[(0,[z0,z1,z2,z196,z3,z4,z6]),(0,[z0,z1,z2,z197,z3,z4,z6]),(0,[z0,z1,z2,z198,z3,z4,z6])]],
   [[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z200,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z21,z4,z6]),(0,[z0,z1,z2,z125,z3,z4,z6])],[(0,[z0,z1,z2,z3,z201,z4,z6]),(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z0,z1,z2,z203,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z204,z6]),(0,[z0,z205,z1,z2,z3,z4,z6]),(0,[z0,z206,z1,z2,z3,z4,z6])],[(0,[z207,z0,z1,z2,z3,z4,z6]),(0,[z208,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z209,z2,z3,z4,z6]),(0,[z0,z210,z1,z2,z3,z4,z6]),(0,[z0,z1,z29,z2,z85,z4,z6]),(0,[z0,z1,z2,z203,z3,z4,z25]),(0,[z0,z1,z2,z211,z3,z4,z6])],[(0,[z0,z212,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z213,z4,z6]),(0,[z35,z0,z1,z2,z85,z4,z6]),(0,[z214,z0,z1,z2,z3,z4,z6]),(0,[z215,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z11,z3,z4,z6]),(0,[z0,z1,z2,z203,z68,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z216]),(0,[z0,z1,z2,z3,z4,z217,z6]),(0,[z0,z1,z2,z218,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z219,z6]),(1,[z0,z1,z2,z220,z4,z6]),(0,[z0,z111,z2,z3,z123,z4,z6]),(0,[z0,z1,z2,z3,z4,z221,z6]),(0,[z66,z0,z1,z2,z14,z4,z6]),(0,[z222,z0,z1,z2,z3,z4,z6]),(0,[z0,z223,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z224,z4,z6,z113]),(0,[z173,z0,z1,z2,z3,z4,z50]),(0,[z225,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z226,z6]),(0,[z0,z1,z2,z11,z68,z4,z6])],[(0,[z0,z1,z227,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z44,z6]),(0,[z10,z0,z1,z228,z3,z4,z6])],[(0,[z229,z0,z1,z2,z3,z230,z6]),(0,[z0,z1,z2,z3,z4,z231,z6]),(0,[z87,z0,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z232,z4,z6])]],
   [[(0,[z233,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z234,z6]),(0,[z0,z1,z2,z3,z4,z6,z235]),(0,[z66,z0,z1,z2,z3,z4,z25])],[(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z208,z1,z2,z224,z3,z4,z6]),(0,[z0,z1,z145,z2,z3,z4,z69]),(0,[z237,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z238,z6])],[(0,[z239,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z240,z4,z6]),(0,[z41,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z14,z241,z4,z6])],[(0,[z0,z1,z2,z3,z242,z4,z6]),(0,[z0,z1,z243,z2,z3,z4,z6]),(0,[z130,z0,z1,z2,z14,z4,z6]),(0,[z10,z0,z1,z2,z3,z68,z6]),(0,[z0,z1,z2,z3,z244,z4,z6])],[(0,[z0,z1,z2,z14,z77,z4,z6]),(0,[z245,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z246,z3,z4,z6]),(0,[z247,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z22,z6]),(0,[z27,z0,z2,z117,z3,z4,z6]),(0,[z0,z1,z8,z2,z85,z4,z6]),(0,[z0,z1,z3,z101,z4,z103,z6])],[(0,[z27,z0,z1,z2,z3,z248,z6]),(1,[z0,z1,z177,z14,z4,z6])],[(0,[z0,z135,z1,z2,z14,z4,z6]),(0,[z249,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z250,z6]),(0,[z10,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z46,z2,z3,z4,z69,z6]),(0,[z49,z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z68,z4,z6])],[(0,[z0,z251,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z50,z113]),(0,[z0,z1,z2,z3,z69,z103,z6]),(0,[z0,z1,z2,z3,z252,z4,z6]),(0,[z0,z1,z2,z253,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z254])],[(0,[z47,z0,z1,z2,z3,z4,z255]),(0,[z0,z1,z2,z3,z4,z256,z6]),(0,[z0,z1,z2,z3,z257,z4,z6])],[(0,[z258,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z259]),(0,[z0,z1,z2,z14,z4,z6,z50]),(0,[z0,z1,z2,z3,z260,z4,z6]),(1,[z80,z0,z2,z3,z4,z81]),(0,[z261,z0,z1,z2,z3,z4,z6])],[(0,[z41,z262,z1,z2,z3,z4,z6]),(0,[z263,z0,z1,z2,z3,z4,z6])],[(0,[z229,z0,z1,z2,z3,z201,z6]),(0,[z0,z1,z2,z264,z3,z4,z6])],[(0,[z229,z0,z1,z2,z3,z4,z6]),(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z265,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z266,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z267])],[(0,[z0,z1,z268,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6]),(0,[z30,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z3,z4,z17,z6,z15])]],
   [[(0,[z0,z1,z2,z270,z3,z4,z6]),(0,[z66,z173,z0,z1,z2,z3,z4]),(0,[z271,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z272,z3,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z273,z4,z6]),(0,[z41,z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z13,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z274,z6])],[(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z173,z0,z1,z2,z26,z4,z6]),(0,[z276,z0,z1,z2,z3,z4,z6]),(0,[z0,z277,z1,z2,z85,z4,z6]),(1,[z0,z1,z2,z266,z4,z6])],[(0,[z0,z1,z2,z3,z141,z4,z6]),(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z279,z3,z4,z6]),(0,[z0,z1,z280,z2,z3,z4,z6])],[(0,[z0,z1,z2,z281,z3,z4,z6]),(0,[z0,z1,z60,z2,z14,z4,z6]),(0,[z1,z2,z3,z4,z58,z6,z50]),(0,[z0,z1,z2,z3,z282,z4,z6]),(1,[z0,z111,z2,z123,z4,z6]),(0,[z0,z283,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z284,z6])],[(0,[z0,z1,z2,z3,z4,z285,z6]),(0,[z0,z1,z286,z2,z3,z4,z6]),(0,[z0,z1,z2,z287,z3,z4,z6]),(0,[z0,z1,z2,z165,z85,z4,z6]),(0,[z288,z0,z1,z2,z3,z4,z6])],[(1,[z90,z1,z2,z3,z4,z6]),(0,[z289,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z290,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z22,z69,z6]),(0,[z0,z1,z2,z291,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z103,z6]),(0,[z0,z162,z1,z2,z85,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z292]),(0,[z1,z60,z2,z293,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z294]),(0,[z0,z1,z2,z14,z4,z6,z99]),(0,[z0,z1,z2,z14,z100,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z295])],[(0,[z0,z1,z2,z3,z296,z4,z6]),(0,[z0,z1,z297,z2,z3,z4,z6]),(0,[z298,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z162,z2,z3,z4,z6]),(0,[z0,z1,z2,z299,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z300,z6])],[(0,[z0,z1,z2,z3,z4,z301,z6]),(0,[z0,z162,z2,z3,z4,z6,z99]),(0,[z0,z1,z2,z11,z3,z302,z6])],[(0,[z45,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z14,z4,z6,z67]),(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z66,z10,z0,z1,z2,z3,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z304,z6]),(0,[z0,z1,z2,z3,z4,z22,z6]),(0,[z0,z305,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z101,z4,z6])],[(0,[z96,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z306,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z17,z6]),(0,[z307,z0,z1,z2,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z100,z6])],[(0,[z0,z1,z2,z126,z3,z4,z6]),(0,[z0,z1,z2,z308,z3,z4,z6]),(0,[z0,z1,z2,z3,z309,z4,z6]),(0,[z0,z310,z1,z2,z3,z4,z6]),(1,[z130,z0,z1,z3,z103,z6]),(0,[z0,z1,z2,z3,z4,z311,z6]),(0,[z0,z1,z2,z3,z312,z4,z6])],[(0,[z229,z0,z46,z2,z3,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z82]),(0,[z10,z35,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z313,z6])]],
   [[(1,[z0,z1,z2,z3,z4,z127]),(0,[z0,z1,z2,z3,z4,z6,z158]),(0,[z0,z1,z2,z3,z4,z314,z6]),(0,[z315,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z316,z2,z3,z4,z6]),(0,[z317,z0,z1,z2,z3,z4,z6]),(0,[z35,z1,z2,z3,z318,z4,z6]),(0,[z208,z0,z1,z2,z318,z4,z6]),(0,[z27,z0,z1,z117,z3,z4,z6]),(0,[z0,z1,z2,z117,z14,z4,z6]),(0,[z0,z1,z2,z85,z21,z4,z6]),(0,[z0,z1,z319,z2,z3,z4,z6]),(0,[z0,z1,z2,z203,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z320,z6]),(0,[z0,z1,z2,z321,z4,z6,z113])],[(0,[z322,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z4,z6])],[(0,[z323,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z77,z103,z6]),(1,[z0,z1,z2,z324,z4,z6]),(0,[z0,z1,z2,z3,z4,z325,z6])],[(0,[z326,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z327,z2,z3,z4,z6]),(0,[z208,z0,z1,z2,z85,z4,z6]),(0,[z96,z0,z328,z2,z3,z4,z6]),(0,[z0,z1,z329,z2,z3,z4,z6]),(0,[z0,z1,z330,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z103,z6]),(0,[z0,z1,z177,z2,z331,z4,z6])],[(0,[z0,z1,z2,z3,z4,z332,z6]),(1,[z333,z1,z2,z3,z4,z6]),(0,[z0,z1,z334,z2,z3,z4,z6]),(0,[z10,z0,z1,z2,z3,z302,z6])],[(0,[z1,z2,z224,z3,z318,z4,z6]),(0,[z51,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z335]),(0,[z66,z0,z1,z2,z85,z4,z6])]],
   [[(1,[z229,z46,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z52,z14,z4,z6]),(0,[z0,z1,z336,z2,z3,z4,z6])],[(0,[z51,z0,z1,z2,z68,z4,z6]),(0,[z337,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z1,z2,z3,z338,z6]),(0,[z339,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z154,z14,z4,z6])],[(0,[z0,z1,z2,z3,z4,z340,z6]),(0,[z1,z2,z3,z77,z4,z22,z6])],[(1,[z0,z1,z2,z3,z4,z255]),(0,[z80,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z85,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z342,z4,z6]),(1,[z45,z1,z2,z3,z77,z6]),(0,[z27,z333,z1,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z4,z25,z6,z113]),(0,[z0,z1,z2,z343,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z344,z6]),(0,[z0,z1,z2,z345,z3,z4,z6]),(0,[z130,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z346,z2,z3,z4,z6]),(0,[z0,z1,z177,z2,z3,z101,z6])],[(0,[z0,z1,z2,z3,z4,z347,z6]),(0,[z0,z1,z2,z3,z4,z6,z348]),(1,[z0,z1,z2,z3,z4,z349]),(0,[z0,z1,z2,z203,z3,z4,z113])]],
   [[(0,[z229,z1,z46,z2,z3,z4,z6]),(0,[z35,z0,z1,z2,z224,z4,z6]),(1,[z208,z1,z2,z224,z4,z6]),(0,[z130,z0,z1,z2,z350,z4,z6]),(0,[z0,z1,z2,z3,z4,z351,z6]),(0,[z0,z1,z2,z3,z352,z4,z6])],[(0,[z353,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z354,z4,z6]),(0,[z49,z0,z1,z2,z3,z4,z6]),(0,[z355,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z356,z6]),(0,[z0,z1,z2,z85,z68,z4,z6]),(0,[z0,z1,z228,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z357,z6]),(1,[z66,z0,z1,z2,z3,z67])],[(0,[z0,z135,z1,z2,z85,z4,z6]),(0,[z45,z0,z1,z2,z3,z77,z6]),(0,[z0,z1,z2,z123,z4,z6,z113]),(1,[z0,z1,z2,z345,z4,z6]),(0,[z0,z1,z2,z358,z3,z4,z6]),(0,[z0,z1,z2,z3,z359,z4,z6]),(0,[z0,z1,z2,z3,z331,z4,z6]),(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z361,z6])],[(0,[z0,z362,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z248,z4,z6]),(0,[z363,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z364])],[(0,[z0,z1,z2,z3,z4,z365,z6]),(1,[z0,z55,z1,z2,z4,z6]),(0,[z0,z1,z2,z366,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z6,z50]),(0,[z0,z1,z2,z3,z367,z4,z6]),(0,[z0,z1,z2,z3,z4,z368,z6]),(0,[z289,z0,z1,z85,z3,z4,z6]),(0,[z0,z1,z2,z3,z369,z4,z6]),(0,[z370,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z371]),(0,[z0,z1,z2,z3,z4,z372,z6]),(0,[z373,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z101,z22,z6])],[(0,[z49,z0,z1,z2,z3,z4,z58]),(0,[z41,z271,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z331,z4,z6])],[(0,[z374,z0,z1,z2,z3,z4,z6]),(0,[z375,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z364,z6]),(0,[z315,z0,z1,z2,z3,z6,z113]),(0,[z0,z1,z376,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z21,z4,z6]),(0,[z10,z0,z1,z2,z203,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z82]),(0,[z0,z1,z2,z377,z3,z4,z6]),(0,[z0,z1,z2,z203,z14,z4,z6]),(0,[z378,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z85,z4,z6])],[(0,[z379,z0,z1,z2,z3,z4,z6]),(0,[z35,z0,z1,z2,z318,z4,z6]),(0,[z0,z1,z2,z3,z4,z380,z6]),(0,[z0,z1,z2,z3,z4,z381,z6]),(0,[z382,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z230,z6]),(0,[z0,z1,z2,z383,z3,z4,z6]),(0,[z0,z1,z2,z11,z14,z4,z6]),(0,[z384,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z385])],[(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z387,z6]),(0,[z388,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z389,z3,z4,z6])],[(0,[z0,z28,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z127]),(0,[z0,z1,z2,z390,z3,z4,z6]),(0,[z0,z1,z2,z350,z3,z4,z6]),(0,[z0,z1,z2,z11,z3,z9,z6])],[(0,[z0,z1,z46,z2,z3,z4,z6]),(0,[z391,z0,z1,z2,z3,z4,z6]),(0,[z392,z0,z1,z2,z3,z4,z6]),(0,[z96,z45,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z393,z3,z4,z6]),(0,[z0,z394,z1,z2,z3,z4,z6])],[(0,[z395,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z104]),(0,[z0,z1,z60,z2,z85,z4,z6]),(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z397,z6])]],
   [[(0,[z0,z1,z398,z2,z3,z4,z6]),(0,[z0,z1,z2,z399,z3,z4,z6]),(1,[z289,z0,z1,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z400,z6])],[(0,[z0,z1,z2,z3,z4,z17,z50]),(1,[z0,z1,z2,z3,z4,z401]),(0,[z0,z1,z2,z85,z4,z6,z99]),(0,[z0,z1,z2,z85,z100,z4,z6]),(1,[z0,z1,z228,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z402,z6]),(1,[z315,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z403])],[(0,[z0,z1,z404,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z248,z6]),(0,[z0,z1,z2,z3,z241,z4,z6])],[(0,[z0,z1,z2,z3,z405,z4,z6]),(0,[z0,z1,z2,z3,z4,z406,z6]),(0,[z0,z1,z2,z3,z4,z407,z6]),(1,[z0,z1,z2,z26,z4,z6]),(0,[z408,z0,z1,z2,z3,z4,z6]),(0,[z409,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z410,z3,z4,z6]),(0,[z411,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z77,z4,z6]),(0,[z0,z1,z2,z3,z4,z412,z6]),(0,[z0,z1,z2,z3,z4,z413,z6]),(0,[z0,z1,z2,z85,z4,z6,z67]),(0,[z0,z1,z2,z3,z4,z6,z414])],[(0,[z0,z1,z2,z415,z3,z4,z6]),(0,[z416,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z101,z4,z6]),(0,[z0,z1,z2,z417,z3,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z372]),(0,[z45,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z418]),(0,[z0,z1,z2,z14,z14,z4,z6]),(0,[z0,z1,z2,z85,z4,z17,z6]),(0,[z0,z419,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z420,z3,z4,z6]),(0,[z10,z0,z1,z2,z14,z4,z6]),(0,[z0,z421,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z4,z17]),(0,[z422,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z423,z3,z4,z6])]],
   [[(0,[z96,z0,z1,z2,z85,z4,z6]),(0,[z27,z0,z1,z2,z3,z4,z401]),(0,[z424,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z68,z4,z6]),(0,[z0,z425,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z201,z6]),(0,[z0,z1,z2,z3,z426,z4,z6]),(0,[z0,z427,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z272,z3,z4,z6]),(0,[z10,z0,z1,z2,z3,z9,z6]),(0,[z428,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z429,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z430,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z50]),(0,[z0,z1,z2,z85,z4,z302,z6])],[(1,[z0,z1,z2,z3,z338,z6]),(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z208,z10,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z432,z6]),(0,[z0,z1,z2,z117,z85,z4,z6]),(0,[z0,z1,z2,z433,z3,z4,z6]),(1,[z0,z283,z2,z3,z21,z6]),(0,[z80,z0,z2,z3,z4,z81,z6]),(0,[z0,z1,z2,z3,z100,z4,z67])],[(0,[z0,z1,z2,z3,z4,z434,z6]),(0,[z0,z1,z2,z14,z4,z81,z6])],[(0,[z229,z0,z1,z2,z14,z4,z6]),(0,[z27,z0,z1,z2,z14,z4,z6]),(1,[z0,z1,z2,z430,z4,z6]),(0,[z0,z1,z2,z3,z4,z17,z99]),(0,[z265,z0,z1,z2,z14,z4,z6]),(0,[z0,z435,z1,z2,z3,z4,z6]),(0,[z436,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z103,z6])],[(0,[z0,z1,z2,z3,z437,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z170])]],
   [[(1,[z0,z1,z2,z3,z342,z4]),(0,[z0,z1,z2,z3,z77,z69,z6]),(0,[z0,z28,z1,z117,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z438,z6]),(0,[z0,z1,z2,z3,z4,z439,z6])],[(1,[z108,z135,z2,z3,z4,z6]),(0,[z0,z1,z2,z440,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z441]),(0,[z0,z1,z2,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z442])],[(0,[z0,z1,z2,z443,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z69,z6]),(1,[z0,z1,z2,z260,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z444]),(0,[z0,z1,z2,z3,z4,z445,z6]),(0,[z0,z446,z1,z2,z3,z4,z6])],[(0,[z0,z447,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z279,z14,z4,z6]),(0,[z0,z1,z8,z3,z4,z6,z15])],[(0,[z0,z283,z1,z2,z14,z4,z6]),(0,[z0,z448,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z449,z3,z4,z6]),(0,[z450,z0,z1,z2,z3,z4,z6]),(0,[z451,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z452]),(0,[z80,z66,z0,z1,z2,z3,z4]),(0,[z0,z1,z156,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z453,z6])],[(0,[z454,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z293,z3,z4,z6]),(0,[z0,z1,z2,z455,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z456,z6]),(0,[z289,z0,z1,z13,z3,z4,z6]),(0,[z289,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z457]),(0,[z0,z1,z2,z3,z4,z6,z458])],[(0,[z0,z46,z2,z117,z3,z4,z6]),(0,[z0,z459,z1,z2,z3,z4,z6]),(0,[z460,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z461,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z85,z4,z6]),(0,[z462,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z85,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z463,z6]),(0,[z464,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z100,z4,z6])],[(0,[z465,z0,z1,z2,z3,z4,z6]),(0,[z166,z0,z1,z2,z85,z4,z6]),(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z466,z3,z4,z6])],[(0,[z467,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z126,z4,z6]),(0,[z208,z0,z1,z2,z224,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z468]),(1,[z0,z1,z2,z141,z4,z6]),(0,[z0,z1,z2,z85,z123,z4,z6]),(0,[z130,z0,z1,z2,z469,z4,z6]),(0,[z130,z0,z1,z3,z4,z103,z6])],[(0,[z470,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z471,z6]),(0,[z0,z1,z2,z3,z4,z472,z6]),(0,[z0,z1,z177,z2,z3,z103,z6]),(0,[z0,z1,z473,z2,z3,z4,z6])],[(0,[z474,z0,z1,z2,z3,z4,z6]),(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z173,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z101,z4,z6]),(0,[z0,z1,z476,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z17,z6]),(0,[z0,z1,z2,z3,z4,z477,z6])],[(0,[z1,z46,z2,z3,z4,z22,z6]),(0,[z0,z1,z478,z2,z3,z4,z6]),(1,[z27,z0,z117,z3,z4,z6]),(0,[z0,z1,z2,z479,z3,z4,z6]),(0,[z0,z1,z13,z3,z14,z4,z6])],[(0,[z96,z0,z1,z2,z3,z77,z6]),(0,[z0,z480,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z481,z2,z3,z4,z6]),(0,[z0,z1,z2,z203,z318,z4,z6]),(0,[z0,z1,z29,z2,z64,z4,z6])],[(0,[z0,z482,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z483,z6]),(0,[z0,z1,z2,z484,z3,z4,z6]),(0,[z173,z0,z1,z2,z3,z4,z58]),(0,[z0,z1,z177,z2,z3,z4,z349])],[(0,[z47,z1,z2,z293,z3,z4,z6]),(0,[z87,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z17,z58]),(0,[z0,z1,z2,z324,z3,z4,z6]),(0,[z0,z283,z2,z3,z21,z4,z6]),(0,[z0,z1,z8,z2,z266,z4,z6]),(0,[z0,z1,z2,z485,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z486,z6]),(0,[z0,z1,z2,z224,z3,z4,z6]),(0,[z487,z0,z1,z2,z3,z4,z6]),(0,[z0,z283,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z85,z133,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z488]),(0,[z0,z1,z2,z489,z3,z4,z6]),(0,[z490,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z491,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z492,z6]),(0,[z493,z0,z1,z2,z3,z4,z6]),(0,[z0,z494,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z318,z4,z6,z113]),(0,[z0,z56,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z14,z4,z302,z6]),(0,[z207,z0,z1,z2,z85,z4,z6])],[(0,[z0,z1,z495,z2,z3,z4,z6]),(0,[z0,z262,z1,z2,z3,z4,z6]),(0,[z0,z283,z1,z2,z3,z21,z6]),(0,[z10,z0,z1,z2,z4,z302,z6])],[(0,[z87,z0,z1,z293,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z496]),(0,[z0,z1,z2,z203,z123,z4,z6]),(0,[z51,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z437,z4,z69]),(0,[z0,z1,z2,z14,z4,z6,z497])]],
   [[(0,[z0,z283,z46,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z14,z4,z6]),(0,[z0,z498,z1,z2,z3,z4,z6]),(1,[z0,z162,z2,z3,z4,z99])],[(0,[z0,z1,z2,z3,z4,z499,z6])],[(0,[z0,z1,z60,z2,z109,z4,z6]),(0,[z333,z0,z1,z2,z3,z4,z6]),(0,[z41,z0,z2,z3,z4,z69,z6])],[(0,[z0,z500,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z501,z6])],[(0,[z0,z1,z2,z502,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z503,z6]),(0,[z0,z1,z2,z3,z4,z504,z6])],[(0,[z135,z1,z46,z2,z3,z4,z6]),(0,[z47,z0,z1,z293,z3,z4,z6]),(0,[z0,z1,z2,z14,z318,z4,z6]),(0,[z10,z0,z111,z1,z2,z4,z6]),(0,[z505,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z506,z2,z3,z4,z6])],[(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z508,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z509,z3,z4,z6]),(0,[z0,z135,z2,z3,z4,z69,z6]),(0,[z0,z1,z2,z3,z4,z25,z50]),(0,[z0,z1,z2,z3,z4,z510,z6]),(0,[z0,z1,z2,z511,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z512,z6]),(0,[z0,z1,z2,z420,z85,z4,z6]),(0,[z513,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z514,z3,z4,z6]),(0,[z0,z1,z2,z515,z3,z4,z6]),(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z6,z15]),(0,[z0,z1,z2,z85,z4,z6,z517])],[(0,[z518,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z519,z3,z4,z6]),(0,[z49,z0,z1,z2,z14,z4,z6]),(0,[z27,z0,z1,z29,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z520]),(0,[z0,z1,z2,z3,z9,z6,z67])],[(0,[z521,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z358,z14,z4,z6]),(0,[z0,z1,z2,z85,z4,z19,z6]),(0,[z10,z0,z1,z2,z85,z4,z6])],[(0,[z0,z1,z2,z3,z4,z522,z6]),(0,[z96,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z523,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z524]),(0,[z525,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z401,z6]),(0,[z0,z1,z2,z14,z123,z4,z6]),(1,[z0,z1,z2,z350,z4,z6]),(0,[z0,z1,z526,z2,z3,z4,z6]),(0,[z527,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z328,z2,z3,z4,z6]),(0,[z0,z111,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z203,z52,z4,z6]),(1,[z0,z1,z2,z489,z4,z6]),(0,[z0,z1,z2,z321,z203,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z528])],[(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z108,z1,z2,z293,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z255,z6]),(0,[z96,z0,z120,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z530,z6]),(0,[z531,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z81,z6]),(0,[z0,z1,z2,z85,z197,z4,z6])],[(0,[z0,z1,z2,z3,z4,z230,z6]),(0,[z0,z111,z1,z2,z68,z4,z6]),(0,[z532,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z47,z1,z293,z3,z4,z6]),(0,[z533,z0,z1,z2,z3,z4,z6]),(0,[z0,z534,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z100,z4,z15]),(0,[z0,z1,z2,z535,z3,z4,z6])],[(0,[z229,z0,z1,z2,z85,z4,z6]),(0,[z27,z0,z1,z2,z85,z4,z6]),(1,[z0,z1,z2,z3,z437,z4]),(0,[z66,z0,z162,z1,z2,z3,z4]),(0,[z7,z0,z1,z2,z3,z4,z15])],[(0,[z0,z1,z2,z3,z4,z536,z6]),(0,[z537,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z177,z2,z189,z4,z6]),(0,[z0,z1,z2,z125,z4,z9,z6])],[(0,[z229,z0,z135,z2,z3,z4,z6]),(0,[z0,z538,z1,z2,z3,z4,z6]),(0,[z0,z135,z2,z117,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z539,z6]),(0,[z0,z1,z2,z85,z4,z69,z6]),(0,[z0,z540,z1,z2,z3,z4,z6]),(0,[z0,z541,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z542,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z496,z6]),(0,[z0,z1,z177,z2,z3,z4,z6]),(1,[z0,z1,z2,z203,z4,z25])],[(0,[z0,z543,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z544,z6]),(0,[z0,z1,z545,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z546,z6]),(0,[z0,z28,z1,z2,z14,z4,z6])],[(0,[z0,z1,z46,z2,z14,z4,z6]),(0,[z0,z1,z2,z146,z3,z4,z6]),(0,[z0,z1,z2,z393,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z547,z6])],[(0,[z108,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z548,z3,z4,z6]),(0,[z108,z1,z2,z3,z4,z22,z6]),(0,[z0,z1,z2,z549,z3,z4,z6]),(0,[z0,z1,z2,z550,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z58,z6]),(0,[z0,z283,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z397,z6]),(0,[z0,z1,z177,z2,z3,z4,z234])]],
   [[(0,[z0,z1,z2,z3,z551,z4,z6]),(0,[z80,z0,z1,z2,z3,z100,z4]),(0,[z0,z1,z2,z399,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z552,z6])],[(1,[z0,z1,z2,z3,z553,z6]),(0,[z289,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z203,z4,z25,z6])],[(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z52,z4,z6,z113]),(0,[z0,z1,z2,z164,z3,z4,z6]),(0,[z130,z0,z1,z177,z3,z4,z6])],[(0,[z0,z1,z2,z3,z555,z4,z6]),(0,[z47,z0,z1,z2,z281,z4,z6]),(0,[z0,z162,z1,z2,z3,z100,z4]),(0,[z0,z1,z2,z3,z4,z6,z556])],[(0,[z0,z1,z2,z3,z4,z557,z6]),(0,[z0,z1,z2,z3,z4,z558,z6]),(0,[z0,z1,z2,z3,z559,z4,z6])],[(0,[z560,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z561,z6])],[(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z14,z4,z562,z6]),(0,[z0,z1,z2,z3,z14,z4,z6]),(0,[z0,z1,z2,z85,z4,z6,z113])],[(0,[z87,z1,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z563,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z517]),(0,[z564,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z565,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(0,[z0,z1,z2,z321,z3,z4,z6])]],
   [[(0,[z0,z135,z28,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z338,z6]),(0,[z27,z0,z1,z2,z3,z553,z6]),(0,[z0,z1,z2,z14,z4,z9,z6]),(0,[z0,z1,z2,z567,z3,z4,z6]),(0,[z0,z1,z2,z321,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z6,z254])],[(0,[z568,z0,z1,z2,z3,z4,z6]),(0,[z569,z0,z1,z2,z3,z4,z6]),(0,[z570,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z100,z4,z17])],[(0,[z571,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z14,z4,z6,z15]),(1,[z0,z1,z2,z31,z4,z6])],[(0,[z173,z1,z2,z3,z4,z6,z50]),(0,[z0,z1,z2,z3,z572,z4,z6]),(0,[z0,z1,z2,z3,z573,z4,z6]),(0,[z0,z1,z2,z574,z3,z4,z6]),(1,[z0,z1,z2,z189,z4,z6]),(0,[z0,z575,z1,z2,z3,z4,z6])],[(0,[z576,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z577,z3,z4,z6]),(0,[z0,z1,z2,z578,z3,z4,z6]),(0,[z0,z1,z2,z3,z579,z4,z6]),(0,[z580,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z224,z4,z6]),(1,[z0,z56,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z17,z81]),(1,[z0,z1,z272,z3,z4,z6])],[(0,[z87,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z581,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z81,z6]),(0,[z0,z1,z2,z85,z4,z138,z6])],[(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z583,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z25,z6]),(0,[z0,z1,z2,z584,z3,z4,z6]),(0,[z66,z0,z1,z2,z11,z3,z6]),(0,[z0,z1,z2,z3,z100,z4,z113])],[(1,[z35,z1,z2,z318,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z585]),(0,[z0,z1,z29,z2,z3,z4,z6]),(0,[z586,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z349])]],
   [[(0,[z108,z0,z46,z2,z3,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z6]),(0,[z587,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z234]),(0,[z0,z1,z2,z588,z3,z4,z6])],[(0,[z0,z28,z46,z2,z3,z4,z6]),(0,[z0,z1,z589,z2,z3,z4,z6]),(0,[z590,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z591,z6]),(0,[z0,z592,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z100,z4,z9])],[(0,[z593,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z594,z6]),(1,[z0,z328,z2,z3,z4,z6]),(0,[z0,z111,z1,z2,z3,z4,z496]),(0,[z51,z0,z1,z2,z85,z4,z6]),(0,[z289,z0,z1,z177,z3,z4,z6]),(1,[z7,z0,z1,z3,z4,z17]),(0,[z595,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z213,z6]),(0,[z47,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z596,z6]),(0,[z597,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z598,z3,z4,z6])],[(1,[z262,z1,z2,z3,z4,z6]),(0,[z0,z162,z1,z2,z345,z4,z6]),(0,[z0,z448,z1,z2,z14,z4,z6])],[(0,[z0,z1,z2,z599,z3,z4,z6]),(0,[z51,z0,z1,z2,z123,z4,z6]),(0,[z0,z1,z2,z600,z3,z4,z6]),(0,[z0,z1,z601,z2,z3,z4,z6])],[(0,[z47,z0,z602,z2,z3,z4,z6]),(0,[z0,z1,z2,z293,z14,z4,z6]),(0,[z0,z1,z2,z85,z318,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z604,z4,z6]),(0,[z0,z1,z2,z605,z3,z4,z6]),(0,[z0,z1,z606,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z81,z6,z99])],[]],
   [[(0,[z1,z46,z2,z293,z3,z4,z6]),(0,[z208,z35,z1,z2,z3,z4,z6]),(0,[z0,z1,z607,z2,z3,z4,z6]),(0,[z0,z162,z1,z2,z3,z4,z81])],[(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z6]),(0,[z0,z1,z2,z203,z224,z4,z6]),(0,[z7,z0,z1,z2,z14,z4,z6]),(0,[z518,z0,z1,z2,z85,z4,z6]),(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z31,z4,z6]),(0,[z0,z1,z2,z609,z3,z4,z6])],[(0,[z0,z1,z2,z610,z3,z4,z6]),(0,[z49,z66,z0,z1,z2,z3,z4]),(0,[z611,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z469,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z6])],[(0,[z0,z1,z602,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z612]),(0,[z0,z1,z2,z3,z4,z6,z99])],[(0,[z47,z0,z251,z2,z3,z4,z6]),(0,[z173,z0,z1,z2,z14,z4,z6]),(0,[z49,z0,z1,z2,z85,z4,z6]),(0,[z0,z2,z52,z3,z123,z4,z6]),(0,[z0,z1,z2,z3,z100,z4,z25])],[(0,[z0,z1,z2,z3,z613,z4,z6]),(0,[z0,z1,z2,z260,z4,z69,z6]),(0,[z0,z162,z1,z2,z3,z4,z99])],[(0,[z0,z1,z614,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z615,z6]),(1,[z0,z1,z2,z469,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z67])],[(0,[z616,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z617,z6])]],
   [[(0,[z27,z0,z1,z2,z37,z4,z6]),(0,[z0,z28,z1,z29,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z6,z113]),(0,[z0,z1,z2,z11,z3,z4,z170])],[(0,[z0,z1,z2,z3,z4,z618,z6]),(0,[z0,z120,z1,z2,z3,z4,z6]),(1,[z0,z1,z14,z4,z103,z6]),(0,[z0,z1,z2,z3,z4,z6,z619]),(0,[z10,z0,z1,z2,z4,z6,z113]),(0,[z0,z1,z2,z11,z3,z4,z364]),(0,[z0,z1,z620,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z100,z9])],[(0,[z0,z1,z621,z2,z3,z4,z6]),(0,[z622,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z224,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z623,z6])],[(0,[z0,z1,z624,z2,z3,z4,z6]),(0,[z625,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z626,z4,z6]),(0,[z627,z0,z1,z2,z3,z4,z6]),(0,[z628,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z629]),(0,[z0,z1,z177,z2,z85,z4,z6])],[(1,[z0,z1,z2,z281,z4,z6]),(0,[z0,z1,z2,z3,z630,z4,z6]),(0,[z0,z1,z2,z631,z3,z4,z6]),(0,[z0,z1,z2,z632,z3,z4,z6]),(0,[z0,z633,z1,z2,z3,z4,z6]),(0,[z382,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z4,z302,z6])],[(0,[z47,z87,z1,z2,z3,z4,z6]),(0,[z0,z1,z13,z2,z3,z4,z6]),(0,[z634,z0,z1,z2,z3,z4,z6])],[(0,[z108,z0,z1,z2,z85,z4,z6]),(0,[z0,z277,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z635,z6]),(0,[z0,z1,z2,z3,z4,z6,z497])]],
   [[(0,[z229,z108,z1,z2,z3,z4,z6]),(0,[z0,z636,z1,z2,z3,z4,z6]),(0,[z637,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z638,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z58,z6]),(0,[z0,z28,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z639,z3,z4,z6]),(1,[z0,z1,z85,z14,z4,z6]),(0,[z0,z1,z3,z14,z4,z103,z6]),(0,[z0,z1,z640,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z103,z6])],[(0,[z0,z1,z46,z2,z85,z4,z6]),(0,[z0,z641,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z4,z99,z15])],[(0,[z0,z1,z2,z3,z4,z6,z642]),(0,[z0,z1,z29,z2,z324,z4,z6]),(0,[z0,z1,z2,z85,z52,z4,z6]),(0,[z0,z1,z2,z3,z101,z69,z6]),(0,[z643,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z321,z4,z113]),(0,[z0,z1,z2,z3,z6,z254,z113])],[(0,[z0,z1,z2,z3,z644,z4,z6]),(0,[z0,z29,z2,z117,z3,z4,z6]),(0,[z0,z162,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z645,z6]),(0,[z0,z1,z2,z3,z4,z646,z6])],[(0,[z0,z1,z2,z3,z318,z4,z6]),(0,[z0,z1,z2,z647,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z81,z15]),(0,[z289,z0,z1,z3,z4,z103,z6]),(0,[z648,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z649,z3,z4,z6])],[(0,[z0,z1,z2,z3,z101,z21,z6]),(0,[z0,z1,z2,z85,z11,z4,z6]),(0,[z7,z0,z1,z2,z3,z617,z6]),(0,[z0,z1,z2,z3,z650,z4,z6])],[(1,[z0,z1,z334,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z651]),(0,[z0,z1,z2,z321,z85,z4,z6])]],
   [[(0,[z0,z1,z2,z652,z3,z4,z6]),(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z653,z3,z4,z6]),(0,[z0,z1,z2,z654,z3,z4,z6]),(0,[z0,z162,z1,z2,z430,z4,z6]),(0,[z0,z1,z2,z3,z655,z4,z6]),(0,[z0,z1,z2,z3,z656,z4,z6]),(0,[z0,z1,z2,z3,z657,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z4,z6,z658])],[(0,[z518,z0,z1,z2,z14,z4,z6]),(0,[z176,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z9,z6]),(0,[z66,z0,z1,z2,z3,z101,z6])],[(0,[z0,z1,z2,z3,z617,z4,z6]),(0,[z659,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z660,z2,z3,z4,z6]),(0,[z661,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z662,z6]),(0,[z663,z0,z1,z2,z3,z4,z6]),(0,[z664,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z1,z2,z3,z213,z6]),(0,[z0,z1,z2,z665,z3,z4,z6]),(0,[z0,z1,z2,z666,z3,z4,z6]),(0,[z0,z1,z2,z3,z123,z4,z6]),(0,[z0,z1,z667,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z186,z4,z6]),(0,[z0,z1,z2,z11,z3,z68,z6])],[(0,[z0,z1,z2,z3,z4,z668,z6]),(0,[z0,z1,z2,z3,z220,z4,z6]),(0,[z0,z111,z1,z2,z14,z4,z6]),(0,[z41,z0,z283,z2,z3,z4,z6]),(0,[z0,z1,z334,z2,z4,z69,z6]),(1,[z0,z1,z2,z85,z4,z6])],[(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z670]),(0,[z0,z1,z2,z671,z3,z4,z6]),(1,[z0,z1,z145,z2,z3,z4]),(0,[z0,z1,z2,z3,z103,z9,z6]),(0,[z0,z1,z2,z3,z4,z672,z6])],[(0,[z0,z1,z2,z85,z4,z25,z6])]],
   [[(0,[z0,z1,z2,z673,z3,z4,z6]),(1,[z0,z602,z2,z3,z4,z6]),(0,[z0,z1,z674,z2,z3,z4,z6]),(0,[z130,z0,z1,z2,z3,z101,z6]),(1,[z10,z0,z1,z2,z302,z6]),(0,[z0,z1,z2,z68,z4,z302,z6]),(0,[z0,z1,z2,z3,z4,z675,z6])],[(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z51,z10,z0,z1,z2,z4,z6])],[(0,[z108,z87,z1,z2,z3,z4,z6]),(0,[z0,z135,z283,z2,z3,z4,z6]),(0,[z208,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z77,z6]),(0,[z0,z1,z2,z3,z4,z25,z81]),(0,[z0,z1,z8,z2,z3,z4,z15])],[(0,[z0,z1,z2,z3,z4,z677,z6]),(0,[z597,z0,z1,z2,z85,z4,z6]),(1,[z0,z1,z177,z3,z101,z6]),(0,[z0,z1,z2,z678,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z679]),(0,[z208,z0,z1,z2,z68,z4,z6]),(0,[z680,z0,z1,z2,z3,z4,z6]),(0,[z681,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z682,z4,z6]),(0,[z0,z1,z177,z2,z14,z4,z6]),(0,[z0,z1,z683,z2,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z6])],[(0,[z47,z0,z1,z2,z3,z4,z104]),(1,[z0,z1,z2,z3,z4,z372]),(0,[z0,z684,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z553,z6]),(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z686,z3,z4,z6]),(0,[z0,z1,z2,z321,z3,z4,z113])],[(1,[z0,z251,z2,z3,z4,z6]),(1,[z271,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z171])],[(0,[z0,z1,z2,z687,z3,z4,z6]),(0,[z108,z0,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z688,z3,z4,z6]),(0,[z0,z1,z2,z3,z342,z4,z22]),(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z0,z1,z2,z3,z4,z689,z6]),(0,[z0,z1,z2,z3,z4,z25,z99])]],
   [[(0,[z27,z0,z1,z2,z220,z4,z6]),(1,[z0,z1,z2,z3,z4,z158]),(0,[z0,z1,z2,z3,z4,z99,z113]),(0,[z0,z1,z2,z3,z4,z6,z690]),(0,[z0,z1,z2,z14,z405,z4,z6]),(0,[z0,z1,z2,z3,z4,z691,z6])],[(0,[z0,z1,z2,z293,z85,z4,z6]),(0,[z0,z692,z1,z2,z3,z4,z6]),(0,[z693,z0,z1,z2,z3,z4,z6])],[(1,[z173,z1,z2,z3,z4,z50]),(0,[z41,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z43,z4,z6]),(1,[z0,z1,z2,z3,z44,z6]),(1,[z0,z1,z2,z4,z6,z171])],[(0,[z0,z1,z2,z694,z3,z4,z6]),(0,[z0,z1,z2,z695,z3,z4,z6]),(0,[z696,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z697,z6]),(1,[z41,z0,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z4,z81,z113]),(0,[z130,z0,z1,z2,z3,z4,z6])],[(0,[z698,z0,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z85,z309,z4,z6]),(0,[z0,z1,z2,z699,z3,z4,z6])],[(0,[z0,z1,z2,z3,z700,z4,z6]),(0,[z49,z0,z1,z2,z3,z100,z4]),(0,[z0,z1,z2,z3,z4,z6,z701]),(0,[z0,z1,z8,z2,z489,z4,z6]),(0,[z702,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z11,z68,z6]),(0,[z0,z1,z2,z3,z703,z4,z6])],[(0,[z0,z1,z704,z2,z3,z4,z6]),(0,[z51,z0,z111,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z705,z6]),(0,[z0,z1,z706,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z562,z6])],[(0,[z0,z135,z1,z2,z3,z4,z6]),(0,[z173,z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z321,z14,z4,z6]),(0,[z0,z1,z177,z3,z101,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z0,z1,z2,z85,z437,z4]),(0,[z0,z1,z2,z709,z4,z6]),(0,[z0,z1,z8,z266,z4,z15]),(0,[z0,z1,z2,z11,z710,z6]),(0,[z0,z1,z2,z3,z100,z9])],[(0,[z87,z1,z60,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z711]),(0,[z0,z1,z712,z3,z4,z6]),(0,[z0,z1,z336,z3,z4,z15]),(0,[z0,z1,z2,z3,z4,z713])],[(0,[z96,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z714,z4,z6]),(0,[z262,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z716,z1,z2,z3,z4,z6])],[(0,[z717,z0,z1,z2,z3,z6]),(0,[z288,z1,z2,z224,z4,z6]),(0,[z0,z1,z2,z718,z4,z6])],[(0,[z0,z1,z2,z281,z4,z6]),(0,[z0,z719,z2,z3,z4,z6]),(0,[z0,z1,z2,z105,z4,z58]),(0,[z0,z1,z14,z4,z646,z6]),(0,[z0,z1,z2,z85,z6,z720]),(0,[z66,z0,z1,z272,z3,z6])],[(0,[z0,z1,z2,z85,z230,z6]),(0,[z0,z1,z721,z3,z4,z6]),(0,[z0,z1,z343,z14,z4,z6]),(0,[z0,z1,z280,z14,z4,z6]),(0,[z0,z1,z2,z722,z4,z6])],[(0,[z0,z723,z2,z3,z4,z6]),(0,[z0,z1,z2,z281,z338,z6]),(0,[z0,z1,z2,z14,z4,z496]),(0,[z0,z1,z177,z331,z101,z6])],[(0,[z0,z135,z2,z3,z230,z6]),(0,[z0,z162,z2,z14,z4,z99]),(0,[z0,z1,z272,z4,z302,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z724]),(0,[z47,z251,z293,z3,z4,z6]),(0,[z90,z1,z2,z3,z4,z127])],[(0,[z0,z725,z2,z3,z4,z6]),(0,[z0,z1,z85,z449,z4,z6]),(0,[z0,z1,z2,z726,z4,z6]),(0,[z0,z1,z2,z3,z4,z727]),(0,[z0,z1,z2,z3,z6,z728]),(0,[z0,z1,z2,z729,z4,z6]),(0,[z0,z1,z2,z211,z4,z113]),(1,[z0,z1,z2,z3,z730])],[(0,[z0,z1,z2,z321,z4,z113])],[(0,[z0,z1,z2,z731,z4,z6]),(0,[z0,z732,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z401]),(0,[z30,z0,z1,z3,z103,z6]),(0,[z0,z1,z2,z4,z6,z733]),(0,[z0,z1,z3,z101,z734,z6]),(0,[z0,z1,z2,z3,z4,z170]),(0,[z0,z1,z2,z321,z4,z735])],[(0,[z0,z1,z2,z736,z4,z6]),(0,[z66,z0,z1,z2,z3,z381]),(0,[z0,z1,z2,z737,z4,z6])],[(0,[z0,z1,z404,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z738]),(0,[z1,z739,z293,z3,z4,z6])],[(0,[z0,z1,z2,z600,z4,z113])],[(0,[z740,z0,z1,z2,z4,z6]),(0,[z608,z1,z2,z3,z77,z6]),(0,[z0,z1,z2,z220,z4,z401]),(0,[z741,z1,z2,z3,z4,z6]),(0,[z0,z1,z145,z2,z260,z4]),(0,[z0,z1,z2,z85,z4,z742])]],
   [[(0,[z386,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z743]),(0,[z0,z1,z2,z220,z248,z6]),(0,[z0,z1,z2,z3,z744,z6]),(0,[z0,z1,z2,z399,z68,z6])],[(0,[z0,z1,z2,z745,z4,z6]),(0,[z0,z1,z2,z3,z746,z6]),(0,[z0,z1,z2,z747,z4,z6]),(0,[z0,z1,z2,z748,z4,z6]),(0,[z222,z0,z1,z85,z4,z6]),(0,[z7,z0,z1,z3,z4,z749]),(0,[z0,z1,z2,z203,z4,z735]),(0,[z0,z1,z2,z100,z9,z171])],[(0,[z96,z1,z2,z141,z22,z6]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z0,z1,z2,z4,z6,z751]),(0,[z66,z0,z1,z2,z3,z488])],[(0,[z0,z1,z2,z85,z201,z6]),(0,[z0,z1,z2,z3,z4,z752]),(0,[z0,z1,z2,z3,z4,z753]),(0,[z0,z1,z272,z85,z4,z6])],[(0,[z0,z1,z2,z754,z4,z6]),(0,[z0,z1,z389,z14,z4,z6]),(0,[z0,z1,z2,z85,z4,z755])],[(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z208,z1,z2,z4,z503,z6])],[(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z2,z3,z759,z6]),(0,[z760,z1,z2,z3,z4,z6]),(0,[z0,z283,z2,z85,z21,z6])],[(0,[z0,z602,z2,z3,z4,z6]),(0,[z47,z1,z293,z14,z4,z6]),(0,[z0,z1,z2,z761,z4,z6]),(0,[z333,z1,z2,z37,z4,z6]),(0,[z762,z1,z2,z3,z4,z6]),(0,[z0,z1,z14,z4,z689,z6]),(0,[z0,z1,z2,z3,z4,z763]),(0,[z0,z1,z2,z85,z4,z234]),(0,[z10,z0,z1,z2,z302,z6])]],
   [[(0,[z681,z1,z2,z3,z77,z6]),(0,[z0,z1,z2,z220,z4,z6]),(0,[z0,z1,z2,z3,z4,z764]),(0,[z80,z0,z2,z3,z4,z765]),(0,[z0,z1,z177,z189,z101,z6]),(0,[z0,z1,z3,z4,z749,z6])],[(0,[z0,z602,z2,z3,z338,z6]),(0,[z0,z1,z2,z3,z4,z766]),(0,[z0,z1,z2,z3,z4,z767]),(0,[z7,z0,z1,z85,z4,z17]),(0,[z0,z1,z2,z768,z4,z6])],[(1,[z46,z2,z3,z230,z6]),(0,[z0,z1,z2,z769,z4,z6]),(0,[z0,z251,z2,z14,z4,z6]),(0,[z0,z1,z614,z14,z4,z6]),(0,[z0,z1,z2,z770,z4,z6]),(0,[z173,z1,z2,z26,z4,z50]),(0,[z271,z1,z2,z14,z4,z6]),(0,[z0,z1,z177,z3,z101,z6])],[(0,[z108,z135,z2,z85,z4,z6]),(0,[z0,z1,z2,z771,z4,z6])],[(0,[z0,z1,z2,z3,z4,z372]),(0,[z0,z1,z2,z772,z4,z6]),(0,[z0,z1,z2,z3,z773,z6]),(0,[z0,z1,z2,z3,z4,z774]),(0,[z0,z1,z2,z775,z4,z6]),(0,[z375,z0,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z776,z6])],[(0,[z0,z1,z2,z777,z4,z6]),(0,[z0,z1,z2,z3,z4,z778]),(0,[z0,z1,z177,z3,z101,z234])],[(0,[z779,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z44,z6]),(0,[z0,z1,z2,z780,z4,z6]),(0,[z0,z1,z2,z3,z617,z15]),(0,[z0,z1,z2,z31,z44,z6])],[(0,[z0,z1,z2,z3,z4,z781]),(0,[z0,z1,z2,z3,z4,z782]),(1,[z1,z2,z783,z4,z6]),(0,[z1,z2,z783,z318,z4,z6]),(0,[z0,z1,z2,z3,z4,z158]),(0,[z0,z1,z2,z784,z4,z6])]],
   [[(0,[z0,z1,z785,z3,z4,z6]),(0,[z47,z1,z293,z3,z213,z6]),(0,[z0,z786,z2,z3,z4,z6]),(0,[z0,z1,z2,z787,z4,z6]),(0,[z0,z1,z2,z653,z4,z113]),(0,[z0,z1,z2,z14,z553,z6]),(0,[z0,z1,z706,z14,z4,z6])],[(0,[z0,z1,z2,z788,z4,z6]),(0,[z0,z1,z2,z3,z789,z6]),(0,[z176,z1,z2,z318,z4,z6]),(0,[z597,z1,z2,z224,z4,z6]),(0,[z0,z1,z790,z3,z4,z6]),(0,[z173,z1,z2,z3,z4,z50]),(0,[z0,z1,z2,z68,z4,z158]),(0,[z0,z1,z2,z43,z4,z6])],[(0,[z0,z791,z2,z3,z4,z6]),(0,[z0,z1,z792,z3,z4,z6]),(0,[z45,z1,z2,z3,z793,z6]),(0,[z41,z0,z2,z3,z69,z6]),(0,[z0,z205,z2,z3,z4,z99])],[(0,[z0,z251,z2,z3,z213,z6])],[(0,[z490,z1,z2,z3,z4,z50]),(0,[z0,z2,z794,z123,z4,z6]),(0,[z0,z1,z2,z11,z68,z6])],[(0,[z0,z1,z2,z3,z4,z795]),(0,[z208,z1,z2,z358,z4,z6]),(0,[z0,z1,z2,z203,z4,z406]),(0,[z659,z0,z1,z3,z103,z6])],[(0,[z173,z1,z2,z3,z4,z796]),(0,[z0,z1,z2,z3,z797,z6]),(0,[z0,z1,z2,z798,z4,z6]),(0,[z0,z641,z2,z3,z4,z81]),(0,[z0,z1,z8,z3,z4,z749]),(0,[z7,z0,z1,z3,z44,z17])],[(0,[z0,z799,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z800]),(0,[z51,z0,z1,z272,z4,z6])]],
   [[(0,[z278,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z801,z4,z6]),(0,[z27,z0,z117,z85,z4,z6])],[(0,[z35,z0,z1,z272,z4,z6]),(0,[z90,z2,z117,z3,z4,z6]),(0,[z0,z1,z2,z802,z4,z6]),(0,[z0,z1,z13,z14,z4,z6]),(0,[z0,z1,z376,z3,z4,z15])],[(0,[z0,z1,z2,z803,z4,z6]),(0,[z804,z0,z1,z2,z3,z4]),(0,[z90,z1,z2,z3,z248,z6]),(0,[z0,z1,z2,z14,z4,z805]),(0,[z134,z0,z1,z2,z4,z113])],[(0,[z0,z1,z2,z3,z4,z806]),(0,[z0,z1,z2,z3,z4,z807]),(0,[z1,z2,z3,z4,z793,z6]),(0,[z0,z1,z2,z399,z186,z6])],[],[(0,[z0,z1,z272,z3,z9,z6]),(0,[z66,z0,z1,z2,z3,z385])],[(0,[z0,z1,z808,z3,z4,z6]),(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z1,z2,z3,z100,z668]),(0,[z0,z1,z2,z3,z810,z4]),(0,[z0,z1,z2,z266,z4,z6])],[(0,[z0,z1,z2,z811,z4,z6]),(0,[z0,z1,z812,z3,z4,z6]),(0,[z0,z1,z2,z813,z4,z6]),(0,[z0,z1,z85,z748,z4,z6]),(0,[z130,z0,z1,z3,z734,z6]),(1,[z0,z1,z3,z4,z749]),(0,[z0,z1,z2,z814,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z815]),(1,[z1,z2,z3,z793,z6]),(0,[z0,z1,z2,z816,z4,z6]),(0,[z0,z1,z2,z817,z4,z6]),(0,[z0,z1,z2,z710,z302,z6])],[(0,[z167,z0,z1,z85,z4,z6]),(0,[z0,z328,z2,z14,z4,z6]),(0,[z51,z0,z2,z52,z4,z6]),(0,[z0,z1,z2,z85,z4,z496]),(0,[z41,z0,z2,z3,z818,z6]),(0,[z0,z1,z2,z819,z4,z6]),(0,[z7,z0,z1,z14,z4,z17]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z7,z0,z1,z31,z4,z17])],[(0,[z90,z1,z2,z3,z4,z6]),(0,[z0,z821,z2,z3,z4,z6]),(0,[z47,z1,z293,z281,z4,z6]),(0,[z0,z1,z2,z14,z213,z6]),(0,[z66,z0,z1,z2,z3,z556])],[(0,[z0,z1,z2,z822,z4,z6]),(0,[z0,z1,z2,z823,z4,z6]),(0,[z262,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z20,z4,z113])],[(0,[z108,z1,z2,z3,z230,z6]),(0,[z0,z1,z2,z824,z4,z6]),(0,[z0,z1,z2,z3,z4,z825]),(0,[z0,z1,z2,z3,z248,z127]),(0,[z0,z1,z2,z3,z826,z6]),(0,[z1,z2,z3,z4,z6,z827])],[(0,[z0,z251,z2,z281,z4,z6]),(0,[z0,z1,z2,z48,z4,z255]),(0,[z0,z828,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z82]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z1,z2,z3,z4,z830])],[(0,[z0,z1,z2,z3,z6,z831]),(0,[z0,z1,z2,z3,z832,z6]),(0,[z0,z1,z2,z833,z4,z6]),(0,[z66,z0,z1,z2,z3,z414])],[(0,[z46,z2,z3,z4,z230,z6]),(0,[z333,z1,z2,z220,z4,z6]),(0,[z0,z1,z2,z64,z4,z6]),(0,[z0,z1,z2,z834,z4,z6]),(0,[z0,z1,z2,z14,z4,z835]),(0,[z0,z1,z2,z331,z4,z349]),(0,[z0,z1,z2,z4,z6,z836]),(0,[z66,z0,z1,z2,z3,z254])]],
   [[(0,[z1,z799,z2,z3,z4,z6]),(0,[z0,z837,z2,z14,z4,z6]),(0,[z0,z1,z8,z3,z4,z15]),(0,[z0,z1,z3,z4,z749,z15])],[(0,[z0,z1,z838,z3,z4,z6]),(0,[z30,z0,z1,z2,z302,z6]),(0,[z0,z1,z839,z3,z4,z6])],[(0,[z0,z840,z2,z3,z4,z6]),(0,[z0,z1,z2,z68,z4,z82]),(0,[z0,z1,z399,z14,z103,z6]),(0,[z130,z0,z1,z3,z103,z6])],[(0,[z0,z1,z2,z14,z4,z104]),(0,[z49,z1,z2,z14,z4,z58])],[(0,[z108,z636,z2,z3,z4,z6]),(0,[z424,z135,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z127]),(0,[z0,z1,z2,z3,z841,z6])],[(0,[z0,z1,z2,z3,z842,z6]),(0,[z0,z1,z589,z14,z4,z6]),(0,[z843,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z844,z4,z6]),(0,[z0,z1,z2,z14,z617,z6]),(0,[z0,z1,z2,z31,z617,z6]),(0,[z10,z0,z1,z2,z12,z6])],[(0,[z0,z1,z2,z4,z6,z845]),(0,[z0,z1,z14,z4,z138,z6])]],
   [[(0,[z0,z1,z2,z3,z338,z104]),(0,[z846,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z847,z6]),(0,[z0,z1,z2,z14,z100,z9]),(0,[z0,z1,z2,z4,z6,z848]),(0,[z0,z1,z177,z3,z359,z6])],[(0,[z602,z2,z293,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z2,z430,z100,z4]),(0,[z10,z0,z1,z228,z302,z6])],[(0,[z0,z120,z2,z3,z4,z6]),(0,[z47,z1,z293,z85,z4,z6]),(0,[z0,z1,z2,z105,z4,z6]),(0,[z96,z1,z2,z14,z22,z6]),(0,[z0,z1,z14,z22,z103,z6]),(0,[z0,z1,z850,z3,z4,z6]),(0,[z0,z1,z272,z4,z6,z113]),(0,[z0,z1,z2,z423,z4,z25])],[(0,[z740,z0,z1,z2,z230,z6]),(0,[z0,z1,z2,z851,z4,z6]),(0,[z0,z1,z2,z852,z4,z6]),(0,[z853,z1,z2,z3,z4,z6]),(0,[z0,z1,z620,z14,z4,z6]),(0,[z66,z0,z1,z2,z3,z442])],[(0,[z0,z1,z2,z854,z4,z6]),(0,[z643,z1,z2,z3,z22,z6]),(0,[z41,z0,z334,z2,z69,z6]),(0,[z0,z1,z748,z3,z4,z6]),(0,[z0,z1,z177,z14,z103,z6]),(0,[z0,z1,z2,z4,z6,z735])],[(0,[z47,z602,z293,z3,z4,z6]),(0,[z0,z251,z2,z85,z4,z6]),(0,[z303,z1,z2,z3,z4,z58]),(0,[z271,z1,z2,z85,z4,z6])],[(0,[z7,z0,z1,z3,z617,z17]),(0,[z0,z1,z3,z4,z17,z749])],[(0,[z0,z1,z2,z3,z4,z855])]],
   [[(0,[z0,z1,z2,z3,z4,z255]),(0,[z0,z1,z856,z14,z4,z6])],[(0,[z0,z1,z2,z3,z857,z6]),(0,[z0,z1,z2,z3,z4,z858]),(0,[z0,z859,z2,z3,z4,z6]),(0,[z0,z860,z1,z2,z4,z6]),(0,[z0,z1,z2,z861,z4,z6]),(0,[z0,z1,z376,z14,z4,z6]),(0,[z0,z1,z2,z85,z44,z6]),(0,[z0,z1,z2,z862,z4,z6])],[(0,[z0,z1,z2,z3,z338,z255]),(0,[z96,z328,z2,z3,z22,z6]),(0,[z0,z1,z177,z14,z4,z349]),(0,[z0,z1,z156,z2,z4,z517]),(0,[z0,z1,z2,z11,z309,z6]),(0,[z0,z863,z2,z3,z4,z6]),(0,[z0,z1,z2,z864,z4,z6])],[(0,[z0,z865,z2,z3,z4,z6]),(0,[z96,z1,z2,z3,z342,z22]),(0,[z0,z1,z2,z85,z553,z6]),(0,[z0,z1,z606,z3,z101,z6]),(0,[z30,z0,z1,z14,z103,z6]),(0,[z0,z1,z2,z14,z4,z170]),(0,[z0,z1,z2,z3,z4,z349]),(0,[z0,z1,z2,z866,z4,z6])],[(0,[z322,z1,z2,z3,z22,z6]),(0,[z0,z111,z2,z197,z4,z6]),(0,[z315,z0,z1,z2,z321,z113])],[(0,[z0,z1,z2,z281,z213,z6]),(0,[z0,z1,z2,z3,z867,z6]),(0,[z66,z0,z1,z2,z3,z67])],[(0,[z0,z868,z2,z3,z4,z6]),(0,[z0,z1,z2,z345,z4,z6]),(0,[z0,z2,z52,z794,z4,z6])],[(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z1,z2,z869,z4,z6]),(0,[z0,z1,z2,z220,z553,z6]),(0,[z27,z0,z117,z37,z4,z6]),(0,[z0,z1,z870,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z364])]],
   [[(0,[z0,z55,z1,z2,z4,z6]),(0,[z0,z1,z286,z14,z4,z6]),(0,[z0,z1,z871,z3,z4,z6]),(0,[z0,z1,z2,z68,z4,z170])],[(0,[z0,z872,z2,z3,z4,z6]),(0,[z0,z1,z330,z3,z101,z6]),(0,[z873,z1,z2,z3,z4,z6]),(0,[z0,z874,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z875])],[(0,[z0,z1,z2,z876,z4,z6]),(0,[z87,z602,z2,z3,z4,z6]),(0,[z45,z328,z2,z3,z4,z6]),(0,[z0,z1,z2,z331,z4,z6])],[(0,[z0,z1,z2,z3,z877,z6]),(0,[z669,z0,z2,z3,z69,z6]),(0,[z0,z1,z2,z48,z4,z6]),(0,[z0,z878,z117,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z753]),(0,[z0,z1,z2,z279,z4,z397]),(0,[z66,z0,z1,z2,z14,z67]),(0,[z0,z1,z2,z279,z4,z25]),(0,[z0,z1,z2,z3,z730,z67])],[(0,[z0,z1,z2,z3,z4,z879])],[(0,[z0,z1,z2,z3,z4,z880]),(0,[z0,z1,z2,z48,z338,z6]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z0,z157,z2,z3,z4,z99])],[(0,[z0,z1,z2,z882,z4,z6]),(0,[z883,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z43,z44,z6])],[(0,[z508,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z602,z2,z14,z4,z6]),(0,[z0,z1,z2,z885,z4,z6]),(0,[z0,z1,z2,z886,z4,z6])]],
   [[(0,[z0,z56,z1,z2,z3,z101]),(0,[z0,z1,z887,z2,z4,z6]),(0,[z51,z0,z2,z4,z148,z6]),(0,[z262,z2,z3,z4,z69,z6]),(0,[z0,z1,z2,z888,z4,z6])],[(0,[z1,z2,z3,z4,z796,z50]),(0,[z10,z0,z1,z2,z138,z6]),(0,[z0,z1,z2,z889,z4,z6])],[(0,[z0,z1,z2,z3,z890,z6]),(0,[z0,z1,z177,z14,z101,z6])],[(0,[z0,z891,z2,z3,z4,z6]),(0,[z0,z1,z2,z892,z4,z6]),(0,[z333,z1,z2,z3,z4,z127]),(0,[z0,z1,z227,z85,z4,z6])],[(0,[z0,z1,z2,z14,z4,z372]),(0,[z0,z328,z2,z85,z4,z6]),(0,[z0,z1,z85,z699,z4,z6]),(0,[z0,z1,z2,z893,z4,z6])],[(0,[z0,z1,z2,z85,z213,z6]),(0,[z0,z1,z228,z3,z4,z6]),(0,[z315,z0,z1,z2,z3,z6])],[(0,[z454,z0,z117,z3,z4,z6]),(0,[z0,z1,z2,z3,z248,z6]),(0,[z262,z1,z2,z85,z4,z6])],[(0,[z0,z1,z894,z3,z4,z6]),(0,[z0,z1,z2,z26,z4,z6]),(0,[z0,z1,z2,z3,z895,z4]),(0,[z0,z1,z2,z14,z4,z158])]],
   [[(0,[z0,z1,z2,z896,z4,z6]),(0,[z0,z602,z2,z3,z213,z6]),(0,[z0,z1,z2,z85,z4,z82]),(0,[z897,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z818,z6]),(0,[z0,z1,z2,z11,z6,z171])],[(0,[z0,z1,z2,z898,z4,z6]),(0,[z35,z1,z2,z318,z4,z372]),(0,[z173,z1,z2,z14,z4,z50]),(0,[z0,z1,z14,z69,z103,z6]),(0,[z0,z1,z473,z14,z4,z6]),(0,[z899,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z900,z4,z6]),(0,[z41,z0,z2,z14,z69,z6]),(0,[z901,z0,z1,z2,z3,z6])],[(0,[z474,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z902,z4,z6]),(0,[z0,z1,z2,z3,z903,z4]),(0,[z0,z1,z904,z3,z4,z6]),(1,[z0,z2,z3,z818,z6]),(0,[z0,z1,z2,z905,z4,z6]),(0,[z315,z0,z1,z2,z14,z6]),(0,[z0,z1,z8,z489,z4,z15])],[(0,[z0,z2,z3,z818,z69,z6]),(0,[z0,z1,z2,z3,z4,z906])],[(0,[z0,z1,z2,z907,z4,z6]),(0,[z908,z1,z2,z3,z4,z6]),(0,[z0,z1,z177,z14,z4,z6])],[(0,[z0,z1,z2,z85,z4,z104]),(0,[z0,z1,z2,z909,z4,z6]),(0,[z49,z1,z2,z85,z4,z58])],[(0,[z0,z910,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z3,z6,z254]),(0,[z0,z1,z2,z4,z25,z735])],[(0,[z0,z1,z2,z912,z4,z6]),(0,[z0,z1,z2,z85,z617,z6]),(0,[z66,z0,z1,z2,z85,z67]),(0,[z7,z0,z1,z43,z4,z17])],[(0,[z0,z1,z243,z3,z4,z15]),(0,[z0,z1,z2,z913,z4,z6]),(0,[z0,z1,z2,z914,z4,z6]),(0,[z80,z0,z2,z3,z4,z81]),(0,[z0,z1,z2,z915,z4,z6]),(0,[z0,z1,z272,z11,z4,z6]),(0,[z0,z1,z2,z68,z6,z254])],[(0,[z0,z1,z598,z14,z4,z6]),(0,[z0,z1,z2,z3,z916,z6]),(0,[z0,z1,z2,z85,z100,z9])],[(0,[z47,z1,z293,z3,z4,z104]),(0,[z0,z917,z1,z2,z4,z6]),(0,[z90,z1,z2,z3,z4,z401]),(0,[z0,z162,z2,z345,z4,z99]),(0,[z207,z1,z2,z133,z4,z6])],[(0,[z96,z1,z2,z85,z22,z6]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z97,z0,z1,z85,z4,z6])],[(0,[z919,z0,z1,z3,z4,z6]),(0,[z0,z920,z2,z3,z4,z6]),(0,[z0,z1,z2,z921,z4,z6]),(0,[z10,z0,z1,z2,z4,z158]),(0,[z0,z1,z2,z260,z4,z6]),(0,[z0,z1,z2,z922,z4,z6]),(0,[z0,z1,z476,z14,z4,z6])],[(0,[z923,z0,z1,z3,z4,z6]),(0,[z0,z251,z2,z3,z4,z104]),(0,[z428,z1,z2,z3,z4,z58]),(0,[z27,z0,z117,z220,z4,z6]),(0,[z0,z1,z14,z21,z103,z6]),(0,[z0,z1,z2,z924,z4,z6])]],
   [[(0,[z27,z90,z117,z3,z4,z6]),(0,[z0,z1,z2,z925,z4,z6]),(0,[z0,z448,z2,z241,z4,z6])],[(0,[z0,z1,z2,z3,z926,z6]),(0,[z0,z1,z2,z927,z4,z6])],[(0,[z0,z1,z2,z3,z928,z6]),(0,[z0,z602,z2,z281,z4,z6]),(0,[z0,z929,z1,z2,z4,z6]),(0,[z90,z1,z2,z14,z4,z6]),(0,[z0,z1,z2,z37,z553,z6])],[(0,[z0,z328,z2,z3,z77,z6]),(0,[z0,z1,z2,z3,z930,z6]),(0,[z0,z111,z2,z123,z4,z6])],[(0,[z0,z931,z2,z3,z4,z6]),(0,[z932,z1,z2,z3,z4,z6]),(0,[z176,z1,z2,z405,z4,z6]),(0,[z0,z1,z2,z312,z4,z113])],[(0,[z1,z2,z3,z4,z796,z6]),(0,[z289,z0,z1,z189,z4,z6])],[(0,[z39,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z126,z4,z6]),(0,[z0,z1,z2,z141,z4,z6]),(0,[z0,z1,z2,z85,z4,z170]),(0,[z0,z1,z2,z43,z617,z6])],[(0,[z0,z1,z2,z3,z933,z4]),(0,[z0,z1,z2,z934,z4,z6]),(0,[z0,z111,z1,z272,z4,z6]),(0,[z0,z1,z2,z935,z4,z6])]],
   [[(0,[z46,z2,z673,z3,z4,z6]),(0,[z229,z46,z2,z3,z230,z6]),(0,[z0,z1,z8,z14,z4,z15]),(0,[z0,z1,z469,z4,z103,z6]),(0,[z0,z1,z2,z3,z232,z9])],[(0,[z0,z936,z2,z3,z4,z6]),(0,[z0,z1,z937,z2,z3,z4]),(0,[z315,z0,z1,z2,z85,z6]),(0,[z0,z1,z177,z469,z4,z6]),(0,[z0,z1,z2,z4,z6,z938]),(0,[z0,z1,z2,z4,z6,z939])],[(0,[z0,z1,z2,z940,z4,z6]),(0,[z0,z1,z2,z4,z6,z941]),(0,[z130,z0,z1,z14,z103,z6])],[(0,[z0,z1,z14,z77,z103,z6]),(0,[z173,z223,z1,z2,z3,z4]),(0,[z942,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z203,z4,z221])],[(0,[z61,z0,z1,z3,z103,z6]),(0,[z0,z1,z2,z141,z342,z4]),(0,[z333,z1,z2,z3,z4,z401]),(0,[z0,z1,z2,z14,z4,z127]),(0,[z0,z277,z2,z197,z4,z6]),(0,[z943,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z944,z6]),(0,[z1,z2,z739,z3,z4,z6]),(0,[z35,z1,z2,z318,z4,z82]),(0,[z0,z1,z631,z14,z4,z6]),(0,[z0,z56,z55,z1,z2,z4]),(0,[z333,z1,z2,z3,z248,z6]),(0,[z0,z2,z878,z3,z4,z6]),(0,[z0,z1,z2,z3,z734,z6])],[(0,[z0,z1,z14,z4,z499,z6]),(0,[z0,z1,z2,z3,z6,z945]),(0,[z0,z1,z542,z85,z4,z6]),(0,[z901,z0,z1,z2,z85,z6])],[(0,[z946,z0,z2,z3,z4,z6]),(0,[z0,z1,z621,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z947]),(0,[z0,z1,z2,z3,z4,z948]),(0,[z10,z0,z1,z272,z302,z6])]],
   [[(0,[z0,z1,z2,z85,z4,z756])],[(0,[z47,z1,z293,z48,z4,z6]),(0,[z0,z1,z2,z3,z4,z949]),(0,[z0,z56,z1,z2,z141,z4]),(0,[z0,z1,z2,z3,z710,z6])],[(0,[z0,z602,z2,z85,z4,z6]),(0,[z0,z1,z549,z85,z4,z6]),(0,[z0,z120,z2,z14,z4,z6]),(0,[z0,z1,z950,z3,z4,z6]),(0,[z0,z1,z2,z324,z4,z6]),(0,[z0,z1,z951,z2,z4,z6]),(0,[z0,z1,z145,z2,z3,z101])],[(0,[z0,z1,z2,z952,z3,z4]),(0,[z0,z1,z2,z68,z710,z6])],[(0,[z0,z251,z2,z48,z4,z6]),(0,[z96,z1,z2,z3,z793,z6]),(0,[z0,z1,z748,z14,z4,z6]),(0,[z0,z1,z2,z85,z4,z766])],[(0,[z333,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z953]),(0,[z0,z1,z2,z954,z4,z6]),(0,[z35,z190,z1,z2,z4,z6]),(0,[z955,z1,z2,z3,z4,z6]),(0,[z0,z1,z177,z85,z101,z6]),(0,[z0,z1,z956,z3,z4,z6])],[(0,[z229,z46,z2,z3,z201,z6]),(0,[z0,z1,z2,z957,z4,z6]),(0,[z0,z1,z2,z3,z4,z765]),(0,[z0,z1,z2,z958,z4,z6]),(0,[z66,z0,z1,z2,z3,z730])],[(0,[z229,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z213,z104]),(0,[z10,z0,z1,z2,z4,z82]),(0,[z0,z1,z2,z85,z4,z372]),(0,[z0,z328,z2,z3,z22,z6]),(0,[z96,z56,z1,z2,z3,z22]),(0,[z0,z114,z2,z52,z4,z6]),(0,[z0,z1,z2,z85,z4,z774]),(0,[z0,z1,z2,z535,z4,z113])]],
   [[(0,[z0,z1,z2,z959,z4,z6]),(0,[z0,z1,z2,z14,z4,z255]),(0,[z0,z1,z2,z3,z960,z6]),(0,[z66,z0,z1,z2,z105,z4]),(0,[z0,z1,z2,z961,z4,z6])],[(0,[z0,z1,z2,z3,z4,z962]),(1,[z0,z1,z748,z4,z6]),(1,[z0,z1,z2,z4,z735])],[(0,[z0,z1,z2,z3,z963,z6]),(0,[z0,z56,z1,z2,z3,z103]),(0,[z964,z1,z2,z3,z4,z6]),(0,[z965,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z4,z158]),(0,[z0,z1,z2,z966,z4,z6])],[(0,[z0,z1,z2,z967,z4,z6]),(0,[z0,z262,z2,z3,z69,z6]),(0,[z0,z1,z2,z14,z4,z349]),(0,[z0,z1,z2,z165,z309,z6]),(0,[z0,z1,z2,z968,z4,z6])],[(0,[z45,z1,z2,z3,z77,z6]),(0,[z0,z1,z2,z4,z6,z969]),(0,[z173,z1,z2,z85,z4,z50]),(0,[z0,z1,z290,z14,z4,z6]),(0,[z0,z1,z2,z189,z4,z349])],[(0,[z45,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z970,z4,z6]),(0,[z0,z1,z2,z123,z4,z158]),(0,[z41,z0,z2,z85,z69,z6])],[(0,[z0,z1,z2,z3,z971,z6]),(0,[z35,z1,z2,z783,z4,z6]),(0,[z0,z972,z1,z2,z4,z6])],[(0,[z0,z1,z2,z973,z4,z6]),(0,[z208,z1,z2,z224,z4,z6]),(0,[z0,z1,z2,z974,z4,z6]),(0,[z0,z1,z2,z14,z4,z364]),(0,[z0,z1,z2,z154,z4,z113])]],
   [[(0,[z0,z1,z673,z14,z4,z6]),(0,[z0,z1,z2,z975,z4,z6]),(0,[z0,z111,z2,z123,z4,z496]),(0,[z0,z1,z2,z976,z4,z6]),(0,[z0,z1,z2,z3,z9,z170])],[(0,[z355,z135,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z977,z6]),(0,[z208,z0,z1,z272,z4,z6]),(0,[z49,z1,z2,z3,z4,z238]),(0,[z0,z1,z2,z978,z4,z6]),(0,[z513,z0,z2,z3,z69,z6]),(0,[z0,z1,z2,z489,z4,z6])],[(0,[z0,z1,z2,z979,z4,z6]),(0,[z80,z0,z2,z85,z4,z81])],[(0,[z27,z0,z117,z3,z4,z127]),(0,[z0,z1,z2,z794,z4,z6]),(0,[z66,z0,z1,z2,z3,z619]),(0,[z0,z1,z2,z3,z4,z730])],[(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z13,z748,z4,z6]),(0,[z0,z981,z2,z3,z4,z6])],[(0,[z0,z1,z2,z224,z4,z82]),(0,[z0,z1,z2,z3,z437,z4])],[(1,[z799,z2,z3,z4,z6]),(0,[z0,z1,z2,z982,z4,z6]),(0,[z0,z1,z606,z14,z4,z6])],[(0,[z0,z1,z2,z4,z983,z6])]],
   [[(0,[z0,z1,z2,z3,z984,z230]),(0,[z799,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z68,z522,z6]),(0,[z1,z328,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z248,z401]),(0,[z0,z1,z2,z3,z985,z6]),(0,[z0,z1,z2,z331,z4,z234])],[(0,[z0,z1,z2,z3,z986,z6]),(0,[z0,z1,z2,z281,z4,z104]),(0,[z0,z55,z1,z2,z342,z4]),(0,[z0,z1,z2,z430,z4,z81]),(0,[z0,z1,z2,z987,z4,z6]),(0,[z0,z1,z2,z154,z4,z497]),(0,[z0,z1,z2,z3,z6,z720]),(0,[z0,z1,z2,z125,z100,z9])],[(0,[z0,z1,z2,z3,z230,z6]),(0,[z0,z1,z2,z988,z4,z6])],[(0,[z0,z1,z2,z3,z989,z6]),(0,[z0,z1,z2,z3,z990,z4]),(0,[z0,z1,z694,z14,z4,z6]),(0,[z0,z1,z2,z991,z4,z6]),(0,[z0,z1,z2,z992,z4,z6]),(0,[z0,z1,z2,z52,z4,z158])],[(0,[z0,z1,z2,z3,z4,z993]),(0,[z0,z1,z2,z994,z4,z6]),(0,[z0,z1,z2,z48,z213,z6]),(0,[z0,z1,z2,z995,z4,z6]),(0,[z0,z1,z330,z14,z4,z6]),(0,[z337,z1,z2,z3,z4,z50]),(0,[z0,z1,z14,z4,z413,z6])],[(0,[z87,z1,z481,z3,z4,z6]),(0,[z0,z996,z2,z3,z4,z6]),(0,[z90,z1,z2,z85,z4,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z0,z1,z2,z3,z998,z4]),(0,[z0,z1,z2,z260,z437,z4]),(0,[z30,z0,z1,z2,z562,z6]),(0,[z0,z1,z228,z14,z4,z6]),(0,[z0,z1,z601,z85,z4,z6]),(0,[z10,z0,z1,z2,z4,z170])],[(0,[z0,z1,z2,z3,z999,z6]),(0,[z0,z1,z2,z3,z4,z1000]),(0,[z0,z1,z2,z3,z1001,z6]),(0,[z0,z1,z2,z14,z248,z6]),(0,[z0,z1,z2,z1002,z3,z4]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z2,z430,z4,z99]),(0,[z0,z1,z2,z1004,z4,z6]),(0,[z0,z1,z228,z189,z4,z6])],[(0,[z0,z1,z18,z85,z4,z6]),(0,[z0,z1,z2,z318,z4,z82]),(0,[z0,z1,z2,z1005,z4,z6]),(0,[z0,z1,z2,z1006,z4,z6]),(0,[z0,z205,z2,z123,z4,z6]),(0,[z51,z0,z2,z794,z4,z6]),(0,[z0,z1,z2,z1007,z4,z6]),(0,[z289,z0,z1,z85,z4,z6]),(0,[z0,z1,z2,z1008,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z401]),(0,[z0,z1,z2,z3,z1009,z6]),(0,[z66,z0,z1,z2,z4,z171])],[(0,[z0,z1,z2,z1010,z4,z6]),(0,[z10,z0,z1,z2,z347,z6]),(0,[z0,z1,z2,z1011,z4,z6]),(0,[z0,z1,z2,z3,z101,z234]),(0,[z0,z1,z2,z1012,z4,z6]),(0,[z0,z1,z2,z1013,z4,z6]),(0,[z0,z1,z2,z485,z4,z113])],[(0,[z0,z1,z2,z3,z4,z1014]),(0,[z0,z1,z2,z1015,z4,z6])],[(0,[z454,z1,z293,z3,z4,z6]),(0,[z0,z1,z2,z281,z4,z255]),(0,[z0,z2,z3,z4,z1016,z6]),(0,[z0,z1,z2,z440,z4,z113]),(0,[z0,z1,z1017,z3,z4,z6]),(0,[z628,z0,z1,z3,z4,z17]),(0,[z0,z1,z8,z85,z4,z15])],[(0,[z0,z1018,z2,z3,z4,z6]),(0,[z1019,z0,z1,z2,z4,z6]),(0,[z1020,z1,z2,z3,z4,z6]),(0,[z41,z0,z2,z3,z437,z69]),(0,[z0,z1,z2,z14,z4,z906]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z10,z0,z1,z2,z361,z6])],[(0,[z130,z0,z1,z85,z103,z6]),(0,[z0,z1,z2,z3,z100,z254])],[(0,[z0,z1,z2,z1021,z4,z6]),(0,[z80,z0,z2,z3,z4,z300])],[(0,[z454,z0,z1,z14,z4,z6]),(0,[z0,z1,z2,z85,z4,z127]),(0,[z0,z1,z2,z189,z4,z6]),(0,[z130,z0,z1,z350,z103,z6])]],
   [[(0,[z0,z1,z2,z3,z201,z6]),(0,[z0,z56,z1,z2,z3,z4]),(0,[z1022,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1023,z4,z6]),(0,[z0,z1,z272,z3,z4,z6]),(0,[z0,z1,z2,z14,z6,z254])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1024]),(0,[z0,z1,z2,z3,z984,z4]),(0,[z0,z1,z2,z1025,z4,z6]),(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z1,z2,z1026,z4,z6])],[(0,[z80,z0,z2,z14,z4,z81]),(0,[z899,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z203,z4,z19])],[(0,[z0,z46,z2,z3,z230,z6]),(0,[z0,z1,z2,z1027,z230,z6]),(0,[z0,z1,z2,z3,z338,z6]),(0,[z1028,z1,z2,z3,z4,z6]),(0,[z0,z283,z2,z3,z21,z6]),(0,[z0,z1,z2,z4,z6,z1029]),(0,[z0,z1,z177,z14,z4,z234]),(0,[z0,z1,z272,z165,z4,z6])],[(0,[z0,z283,z2,z3,z700,z6]),(0,[z0,z602,z2,z3,z4,z104]),(0,[z0,z1,z2,z3,z1030,z6]),(0,[z90,z1,z2,z3,z553,z6]),(0,[z1031,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z234]),(0,[z0,z1032,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z2,z1035,z4,z6]),(0,[z0,z1,z2,z1036,z4,z6]),(0,[z0,z120,z2,z85,z4,z6]),(0,[z1037,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z430,z4,z6]),(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z2,z1039,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1040]),(0,[z0,z56,z1,z2,z14,z4]),(0,[z0,z1,z2,z3,z1041,z6]),(0,[z0,z1,z2,z3,z4,z1042]),(0,[z0,z1,z2,z4,z735,z113])],[(0,[z229,z46,z2,z85,z4,z6]),(0,[z0,z1,z1043,z2,z3,z4]),(0,[z0,z1,z2,z1044,z4,z6]),(0,[z0,z1,z2,z3,z342,z4]),(0,[z0,z1,z2,z511,z4,z113])]],
   [[(0,[z108,z135,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z0,z1,z2,z783,z4,z6]),(0,[z0,z1,z79,z14,z4,z6])],[(0,[z0,z1,z2,z1046,z4,z6]),(0,[z1,z2,z14,z4,z6,z827]),(0,[z1047,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z321,z4,z517])],[(0,[z0,z1,z329,z14,z4,z6])],[(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z1,z2,z1049,z4,z6]),(0,[z0,z1,z2,z85,z4,z255]),(0,[z0,z162,z2,z3,z4,z765]),(0,[z0,z1,z280,z3,z4,z17])],[(0,[z0,z1,z2,z3,z1050,z6]),(0,[z0,z1,z2,z3,z4,z1051]),(0,[z47,z1,z739,z3,z4,z6]),(0,[z27,z0,z117,z3,z4,z401]),(0,[z0,z1,z145,z2,z3,z103]),(0,[z0,z1,z2,z1052,z4,z6]),(0,[z0,z1,z2,z3,z1053,z6])],[(0,[z0,z1,z2,z1054,z4,z6]),(0,[z0,z1,z297,z14,z4,z6]),(0,[z27,z0,z117,z3,z248,z6]),(0,[z0,z1,z2,z1055,z4,z6])],[(0,[z0,z602,z2,z3,z4,z255]),(0,[z0,z1,z2,z3,z553,z127]),(0,[z0,z2,z794,z3,z4,z6]),(0,[z0,z1,z2,z1056,z4,z6]),(0,[z0,z2,z14,z4,z6,z1057]),(0,[z0,z1,z2,z85,z4,z349]),(0,[z0,z1,z2,z1058,z4,z6])],[(0,[z0,z283,z2,z3,z818,z6]),(0,[z0,z1,z2,z3,z4,z749]),(0,[z0,z1,z2,z1059,z4,z6]),(0,[z0,z1,z2,z3,z6,z730])]],
   [[(0,[z239,z46,z2,z3,z4,z6]),(0,[z0,z1060,z2,z3,z4,z6]),(0,[z1,z2,z783,z3,z4,z6]),(0,[z0,z1,z667,z14,z4,z6])],[(0,[z47,z1,z293,z3,z4,z255]),(0,[z603,z0,z2,z3,z69,z6]),(0,[z0,z1,z2,z1061,z4,z6]),(0,[z0,z1,z671,z85,z4,z6]),(0,[z0,z1,z2,z1062,z4,z6])],[(0,[z0,z1,z2,z1027,z4,z6]),(0,[z0,z1,z2,z3,z4,z1063]),(0,[z173,z1,z2,z105,z4,z50]),(0,[z0,z1,z2,z1064,z4,z6]),(0,[z0,z1,z177,z856,z4,z6]),(0,[z0,z1,z2,z85,z4,z364]),(0,[z0,z1,z280,z3,z101,z6])],[(0,[z0,z1,z2,z4,z1065,z6]),(0,[z41,z271,z2,z3,z69,z6])],[(0,[z1,z46,z2,z3,z230,z6]),(0,[z1066,z0,z1,z2,z3,z230]),(0,[z0,z251,z2,z3,z4,z255]),(0,[z328,z2,z3,z4,z22,z6]),(0,[z0,z1,z2,z3,z4,z1067]),(0,[z333,z1,z2,z3,z553,z6]),(0,[z0,z111,z565,z2,z4,z6])],[(0,[z0,z1,z2,z1068,z4,z6]),(0,[z0,z1,z2,z1069,z4,z6]),(0,[z0,z1,z2,z1070,z4,z6]),(0,[z27,z0,z117,z3,z4,z6]),(0,[z1071,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1072,z4,z6]),(0,[z0,z1,z2,z3,z4,z1073]),(0,[z0,z1,z14,z4,z103,z6]),(0,[z66,z0,z1,z14,z103,z6])],[(1,[z1,z2,z3,z4,z796]),(0,[z0,z1,z2,z1074,z4,z6]),(0,[z66,z0,z1,z2,z430,z4]),(0,[z0,z1,z2,z1075,z4,z6]),(0,[z0,z1,z2,z14,z6,z945])],[(0,[z51,z0,z2,z393,z4,z6]),(0,[z0,z1,z2,z14,z4,z947]),(0,[z0,z1,z2,z1076,z4,z6]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z124,z0,z1,z85,z4,z6])]],
   [[(0,[z0,z1,z1078,z3,z4,z6]),(0,[z0,z1,z1079,z3,z4,z6]),(0,[z0,z1,z2,z1080,z4,z6]),(0,[z0,z1,z2,z270,z4,z113]),(0,[z0,z1,z2,z1081,z4,z6])],[(0,[z108,z799,z2,z3,z4,z6]),(0,[z0,z602,z2,z48,z4,z6]),(0,[z0,z1,z2,z1082,z4,z6]),(0,[z0,z1,z2,z3,z793,z6]),(0,[z0,z1,z3,z734,z103,z6]),(0,[z0,z1,z2,z4,z710,z6])],[],[],[(0,[z0,z56,z1,z2,z85,z4]),(0,[z90,z1,z2,z37,z4,z6]),(0,[z0,z1,z2,z1083,z4,z6]),(0,[z0,z1,z2,z3,z1084,z6]),(0,[z0,z1,z2,z3,z818,z6]),(0,[z0,z1,z85,z14,z4,z6])],[(0,[z333,z1,z2,z14,z4,z6]),(0,[z0,z446,z2,z3,z21,z6]),(0,[z0,z1,z165,z14,z4,z6]),(0,[z1085,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1086,z4,z6]),(0,[z0,z1,z1087,z2,z4,z6])],[(0,[z0,z1,z2,z1088,z4,z6]),(0,[z0,z1,z2,z3,z4,z496]),(0,[z1089,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1090,z6])],[(0,[z229,z46,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z1091,z6]),(0,[z0,z1,z2,z1092,z4,z6]),(0,[z0,z162,z2,z3,z4,z99])]],
   [[(0,[z0,z1,z172,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z41,z262,z2,z3,z69,z6]),(0,[z0,z1,z228,z85,z4,z6])],[(0,[z1094,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z248,z6]),(0,[z0,z1,z2,z1095,z4,z6]),(0,[z0,z1,z2,z11,z68,z170])],[(0,[z0,z1,z2,z3,z4,z1096]),(0,[z0,z1,z2,z1097,z4,z6]),(0,[z0,z1,z85,z466,z4,z6]),(0,[z0,z1,z2,z11,z68,z364]),(0,[z0,z1,z2,z4,z357,z113])],[(0,[z0,z1098,z2,z3,z4,z6]),(0,[z0,z1,z739,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1099]),(0,[z0,z1,z334,z2,z4,z6]),(0,[z0,z162,z2,z430,z4,z99]),(0,[z0,z1,z14,z103,z9,z6])],[(0,[z0,z1,z2,z3,z4,z1100]),(0,[z45,z1,z2,z14,z77,z6]),(0,[z0,z162,z683,z2,z3,z4]),(0,[z0,z1,z1101,z3,z4,z6])],[(0,[z1066,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1102,z4,z6]),(0,[z0,z1,z2,z3,z4,z1103]),(0,[z0,z1,z2,z1104,z4,z6]),(0,[z0,z1,z14,z4,z6,z528]),(0,[z0,z1,z189,z14,z4,z6]),(0,[z0,z1,z1105,z3,z4,z6])],[(0,[z0,z1,z2,z37,z4,z127]),(0,[z0,z1,z2,z3,z103,z234])],[(0,[z0,z121,z2,z3,z21,z6]),(0,[z0,z2,z3,z21,z818,z6]),(0,[z0,z1,z2,z100,z4,z171])]],
   [[(0,[z0,z1,z2,z1106,z4,z6]),(0,[z1107,z0,z1,z2,z3,z6]),(0,[z10,z0,z1,z2,z710,z6])],[(0,[z0,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z3,z1108,z6]),(0,[z603,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z1109,z4,z6]),(0,[z0,z1,z2,z3,z4,z1110]),(0,[z130,z0,z1,z469,z103,z6])],[(0,[z0,z1,z2,z3,z1111,z6]),(0,[z0,z1,z3,z4,z1112,z6]),(0,[z135,z799,z2,z3,z4,z6]),(0,[z0,z1,z145,z2,z3,z4])],[(0,[z0,z1,z2,z85,z338,z6]),(0,[z0,z1,z2,z3,z1113,z6]),(0,[z1114,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z350,z4,z6]),(0,[z0,z1,z2,z85,z6,z254]),(0,[z66,z10,z0,z1,z2,z113])],[(0,[z0,z1,z2,z1115,z4,z6]),(0,[z108,z447,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z213,z255]),(0,[z0,z1,z2,z1116,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1117]),(0,[z0,z1,z2,z1118,z3,z4]),(0,[z0,z1,z2,z14,z437,z4]),(0,[z1119,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z9,z730])],[(0,[z0,z1,z2,z105,z100,z4])],[(0,[z46,z2,z3,z22,z69,z6]),(0,[z47,z1,z293,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1120]),(0,[z0,z1,z2,z85,z342,z4]),(0,[z0,z1,z2,z3,z553,z401]),(0,[z0,z1,z2,z3,z4,z1121]),(0,[z1122,z0,z1,z2,z3,z4]),(0,[z0,z1123,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z145,z2,z14,z4]),(0,[z166,z0,z2,z420,z4,z6])],[(0,[z47,z1,z293,z3,z338,z6]),(0,[z0,z1,z272,z203,z4,z6])],[(0,[z0,z251,z2,z3,z4,z6]),(0,[z271,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z230,z6]),(0,[z0,z2,z3,z4,z765,z99])],[(0,[z0,z1,z2,z3,z4,z1124]),(0,[z0,z1,z2,z4,z6,z1125]),(0,[z0,z1,z2,z1126,z4,z6]),(0,[z0,z1,z2,z203,z4,z25])],[(0,[z0,z251,z2,z3,z338,z6]),(0,[z508,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z1127]),(0,[z0,z1,z878,z3,z4,z6])],[(0,[z27,z0,z878,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1128])],[(0,[z0,z1,z2,z3,z4,z1129]),(0,[z0,z1,z2,z1130,z4,z6]),(0,[z96,z120,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z4,z6,z171])],[(0,[z0,z1,z2,z1131,z4,z6]),(0,[z49,z1,z2,z3,z4,z796]),(0,[z0,z1,z14,z4,z566,z6]),(0,[z289,z0,z1,z748,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z553,z6]),(0,[z0,z1,z2,z14,z4,z401]),(0,[z0,z1,z2,z1132,z4,z6]),(0,[z265,z0,z2,z393,z4,z6]),(0,[z0,z1,z2,z3,z4,z735])],[(0,[z0,z1,z2,z1133,z4,z6]),(0,[z41,z0,z145,z2,z3,z69]),(0,[z0,z1,z2,z1134,z4,z6])],[(0,[z0,z1,z2,z514,z4,z25]),(0,[z0,z448,z2,z123,z4,z6]),(1,[z0,z2,z3,z4,z765])],[(0,[z0,z1135,z2,z3,z4,z6]),(0,[z0,z1,z2,z105,z4,z50]),(0,[z1136,z1,z2,z3,z4,z6]),(0,[z0,z1,z145,z334,z2,z4])],[(0,[z0,z1,z2,z1137,z4,z6]),(0,[z90,z1,z2,z220,z4,z6]),(0,[z0,z1,z2,z1138,z3,z4])],[(0,[z0,z1,z1139,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1140]),(0,[z0,z1,z2,z1141,z4,z6]),(0,[z0,z1,z2,z3,z100,z102]),(0,[z0,z1,z2,z3,z100,z400])],[(0,[z0,z1,z2,z1142,z4,z6]),(0,[z262,z283,z2,z3,z4,z6]),(0,[z0,z1,z2,z1143,z4,z6]),(0,[z0,z2,z3,z4,z81,z765])],[(0,[z0,z1144,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1145,z6]),(0,[z41,z0,z2,z260,z69,z6]),(1,[z0,z1,z2,z710,z6])]],
   [[(0,[z0,z1,z2,z14,z201,z6]),(0,[z0,z1,z2,z48,z4,z104]),(0,[z0,z1,z2,z1146,z4,z6]),(0,[z0,z1,z272,z14,z4,z6]),(0,[z1147,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z14,z4,z6]),(0,[z0,z1148,z2,z3,z4,z6]),(0,[z1,z2,z3,z77,z793,z6]),(0,[z0,z111,z2,z123,z4,z158]),(0,[z0,z2,z3,z4,z765,z6]),(0,[z0,z1,z2,z31,z4,z6])],[(0,[z490,z1,z2,z318,z4,z6]),(0,[z0,z1,z2,z1149,z4,z6]),(0,[z0,z1,z2,z3,z4,z1150]),(0,[z0,z1,z2,z3,z4,z805]),(0,[z0,z1,z2,z85,z4,z948]),(0,[z0,z1,z2,z164,z4,z19])],[(0,[z0,z1,z2,z14,z338,z6]),(0,[z0,z1,z2,z1151,z4,z6]),(0,[z0,z1,z1152,z3,z4,z6]),(0,[z0,z283,z2,z14,z21,z6])],[(0,[z1,z2,z3,z793,z22,z6]),(0,[z96,z55,z1,z2,z22,z6]),(0,[z0,z1,z2,z4,z1153,z6]),(0,[z0,z1,z2,z1154,z4,z6]),(0,[z516,z0,z1,z3,z103,z6]),(0,[z0,z1,z2,z14,z4,z234]),(0,[z0,z1,z2,z3,z617,z17]),(0,[z0,z1,z2,z6,z254,z171])],[(0,[z0,z1,z2,z1155,z4,z6]),(0,[z0,z1,z2,z189,z4,z234]),(0,[z10,z0,z1,z2,z6,z171])],[(0,[z0,z1,z2,z1156,z4,z6]),(0,[z35,z1,z2,z318,z4,z6]),(0,[z27,z333,z117,z3,z4,z6]),(0,[z0,z1,z2,z220,z4,z127]),(0,[z0,z1,z145,z2,z85,z4]),(0,[z0,z1,z2,z14,z4,z1042]),(0,[z597,z1,z2,z146,z4,z6])],[(0,[z0,z1,z2,z1157,z4,z6]),(0,[z0,z1158,z1,z2,z3,z4]),(0,[z0,z1,z2,z14,z342,z4]),(0,[z0,z1,z2,z1159,z4,z6]),(0,[z0,z1,z2,z37,z4,z401]),(1,[z0,z2,z794,z4,z6]),(0,[z0,z111,z2,z794,z4,z6]),(0,[z0,z1,z291,z14,z4,z6]),(0,[z0,z1,z2,z1160,z4,z6]),(0,[z0,z162,z2,z85,z4,z99]),(0,[z0,z1,z2,z1161,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z1162,z6]),(0,[z108,z135,z2,z14,z4,z6]),(0,[z0,z1,z2,z3,z1163,z6]),(0,[z333,z1,z2,z85,z4,z6]),(0,[z0,z1,z2,z37,z248,z6])],[(0,[z0,z328,z2,z3,z4,z6]),(0,[z0,z1,z2,z1164,z4,z6]),(0,[z0,z1,z2,z1165,z4,z6]),(0,[z0,z1,z85,z308,z4,z6]),(0,[z0,z1,z14,z4,z94,z6]),(0,[z1047,z1,z2,z14,z4,z6]),(0,[z7,z0,z1,z3,z4,z17]),(0,[z0,z1,z2,z1166,z4,z6])],[(0,[z322,z0,z2,z3,z69,z6]),(0,[z0,z1,z3,z4,z1167,z6]),(0,[z0,z1,z2,z3,z213,z6]),(0,[z1,z2,z3,z4,z58,z796]),(0,[z84,z1,z2,z358,z4,z6]),(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z1,z2,z203,z4,z402])],[(0,[z262,z1,z2,z3,z4,z6]),(0,[z90,z28,z2,z3,z4,z6]),(0,[z0,z1,z2,z24,z4,z25]),(0,[z0,z1,z2,z3,z1168,z6])],[(0,[z229,z799,z2,z3,z4,z6]),(0,[z27,z0,z117,z3,z553,z6]),(0,[z0,z1,z2,z3,z100,z730])],[(0,[z0,z1,z1169,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1170]),(0,[z0,z1,z2,z3,z4,z82]),(0,[z0,z28,z29,z85,z4,z6]),(1,[z0,z1,z3,z734,z6])],[(0,[z0,z1,z2,z3,z1171,z6]),(0,[z208,z1,z2,z783,z4,z6]),(1,[z328,z2,z3,z22,z6]),(0,[z0,z1,z14,z4,z615,z6]),(0,[z0,z1,z2,z3,z4,z1172]),(0,[z10,z0,z1,z2,z557,z6]),(0,[z0,z2,z3,z4,z6,z1057]),(0,[z382,z0,z1,z2,z138,z6])],[(0,[z0,z1,z2,z1173,z4,z6]),(0,[z1,z2,z224,z783,z4,z6]),(0,[z45,z1,z2,z85,z77,z6]),(0,[z0,z1,z2,z1174,z4,z6]),(0,[z0,z1,z2,z3,z4,z835])]],
   [[(0,[z408,z0,z1,z3,z4,z17]),(0,[z0,z1,z2,z37,z4,z6]),(0,[z0,z837,z2,z3,z4,z6]),(0,[z0,z1,z2,z321,z254,z113])],[(0,[z0,z1,z2,z1175,z4,z6]),(0,[z1176,z1,z2,z3,z4,z6]),(0,[z0,z1,z177,z3,z734,z6]),(0,[z0,z1,z2,z3,z254,z170]),(0,[z0,z1,z2,z1177,z4,z6])],[(0,[z66,z0,z1,z2,z3,z163]),(1,[z262,z2,z3,z69,z6]),(0,[z0,z1,z334,z2,z437,z4]),(0,[z10,z0,z1,z2,z6,z254])],[(0,[z0,z1,z2,z3,z4,z104]),(0,[z0,z1,z2,z3,z1178,z6]),(0,[z49,z1,z2,z3,z4,z58]),(0,[z0,z1,z2,z856,z4,z6])],[(0,[z0,z1,z2,z109,z4,z6]),(0,[z0,z1,z2,z68,z75,z6])],[(0,[z27,z0,z117,z14,z4,z6]),(0,[z0,z1,z2,z469,z4,z6])],[(0,[z0,z1,z2,z3,z1179,z6]),(0,[z35,z1,z2,z133,z4,z6]),(0,[z0,z1,z2,z1180,z4,z6]),(0,[z0,z1,z2,z3,z617,z6]),(0,[z66,z0,z1,z2,z3,z170])],[(0,[z0,z1,z2,z3,z1181,z4]),(0,[z166,z0,z2,z52,z4,z6]),(0,[z262,z1,z2,z3,z69,z6]),(0,[z0,z1,z177,z3,z101,z349]),(0,[z0,z1,z2,z125,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1058).take 170) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1228)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 525, 170] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 110).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 217).take 39).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [110, 107, 39] = true :=
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

end PEqualNP.Outside.L_meta_39057

theorem PEqualNP.Outside.L_meta_39057 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276681728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276681728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39057.solve