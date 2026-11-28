import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38587

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
  Nat.testBit (4276677352 * 2 ^ 32 + 4004031144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4000850214025094#64 ++ 0x1000214085009425#64 ++ 0xaa018f1e3c47ffff#64 ++ 0xea8063c78f11ffff#64 : BitVec 256),
   (0x80063268c9992a49#64 ++ 0x60018c9a32664a92#64 ++ 0x7f0e73e9cfb93a4f#64 ++ 0xdfc39cfa73ee4e93#64 : BitVec 256),
   (0x007058b163c18c62#64 ++ 0x401c162c58f06318#64 ++ 0xfcf07cf1f3c1cc73#64 ++ 0xbf3c1f3c7cf0731c#64 : BitVec 256),
   (0x02bb00fc02ec0f03#64 ++ 0x80aec03f00bb03c0#64 ++ 0xf7ff80fe03fe0f83#64 ++ 0x7dffe03f80ff83e0#64 : BitVec 256),
   (0x05ddff000377f000#64 ++ 0x01777fc000ddfc00#64 ++ 0xe7ffff0003fff002#64 ++ 0xf9ffffc000fffc00#64 : BitVec 256),
   (0x09efefdfbc000000#64 ++ 0x027bfbf7ef000000#64 ++ 0xf9fffffffc000001#64 ++ 0xfe7fffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0060489120000000 0x0018122448000000 0x50f070e1c0000000 0x143c1c3870000000

def z1 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f0000001 0xbe3c1f3c7c000000

def z2 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07cf1f3c1cc73 0xbf3c1f3c7cf0731c

def z3 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80fe03fe0f83 0x7dffe03f80ff83e0

def z4 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z5 : W := mkw 0x4000850214025094 0x1000214085009425 0xaa018f1e3c47ffff 0xea8063c78f11ffff

def z6 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73e9cfb93a4f 0xdfc39cfa73ee4e93

def z7 : W := mkw 0x0944ef03bc000000 0x02513bc0ef000000 0x08007f01fc000000 0x82001fc07f000000

def z8 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003c1cc72 0x0100000000f0731c

def z9 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff800003fe0002 0x79ffe00000ff8000

def z10 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000fe00000f81 0x0400003f800003e0

def z11 : W := mkw 0x098fa74e9c000000 0x0263e9d3a7000000 0x010f830e0c000000 0x4043e0c383000000

def z12 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc000001 0xfe7fffffff000000

def z13 : W := mkw 0x0070489122408422 0x001c122448902108 0x80f00c103040c430 0x203c03040c10310c

def z14 : W := mkw 0x8006224888182209 0x2001889222060882 0x030e03080c38320c 0x40c380c2030e0c83

def z15 : W := mkw 0x4000850214025094 0x1000214085009425 0x0201830e0c06338c 0x408060c383018ce3

def z16 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x51fe70e1c0000000 0x147f9c3870000000

def z17 : W := mkw 0x8000102041992a49 0x6000040810664a92 0x0600000003b93a4e 0x0180000000ee4e93

def z18 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000000013a4e 0x0080000000004e93

def z19 : W := mkw 0x07fffffc03ffff03 0x81ffffff00ffffc0 0xf7fffffe03ffff83 0xfdffffff80ffffe0

def z20 : W := mkw 0x0050580003418000 0x0014160000d06000 0xe4f07c0003c1c002 0xb93c1f0000f07000

def z21 : W := mkw 0x80020068c8880a49 0x6000801a32220292 0x180000e9cc000a4d 0x0600003a73000293

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z23 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff1e3fffffff 0xfbffffc78fffffff

def z24 : W := mkw 0x4010952257c3dcf6 0x5004254895f0f73d 0xae018f1e3fc7ffff 0xeb8063c78ff1ffff

def z25 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x54f070e1c3800000 0x153c1c3870e00000

def z26 : W := mkw 0x0000850000025000 0x0000214000009400 0xa2018f000047f002 0xe88063c00011fc00

def z27 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0x59fe70fffc000001 0x167f9c3fff000000

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0xa201801e00460f83 0x68806007801183e0

def z29 : W := mkw 0x82bf32fccbfd2f4b 0xe0afccbf32ff4bd2 0xfffff3ffcfff3fcf 0xfffffcfff3ffcff3

def z30 : W := mkw 0x0010100003418000 0x0004040000d06000 0x0400000003c1c002 0x0100000000f07000

def z31 : W := mkw 0x45fdffb377f7fcf6 0x517f7fecddfdff3d 0xffffffffffffffff 0xffffffffffffffff

def z32 : W := mkw 0x4000850214025094 0x1000214085009425 0x0201830e0c47fffe 0x408060c38311ffff

def z33 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc06338d 0xfeffffffff018ce3

def z34 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x45fe700003b80000 0x117f9c0000ee0000

def z35 : W := mkw 0x01cdef0214000000 0x00737bc085000000 0xe9ffff1e3c000001 0xfa7fffc78f000000

def z36 : W := mkw 0x01cd6a0000000000 0x00735a8000000000 0x41fe700000000000 0x107f9c0000000000

def z37 : W := mkw 0x0dffffddab77f000 0x037ffff76addfc00 0xf7ffffe1c3fff002 0xfdfffff870fffc00

def z38 : W := mkw 0x0000100041010040 0x4000040010404010 0x08007001c0010040 0x82001c0070004010

def z39 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x550e70e1c3b80000 0x15439c3870ee0000

def z40 : W := mkw 0xc5dfff6adffffadd 0x7177ffdab7fffeb7 0xffffffffffffffff 0xffffffffffffffff

def z41 : W := mkw 0x89efeffffc880a49 0x627bfbffff220292 0xf9fffffffc000a4d 0xfe7fffffff000293

def z42 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc47ffff 0xfeffffffff11ffff

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8000c103041cc73 0xaa0003040c10731c

def z44 : W := mkw 0x4070ddb377c3dcf6 0x501c376cddf0f73d 0xfef1ffffffc7ffff 0xffbc7ffffff1ffff

def z45 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff0e0ffff38e 0xf9ffffc383fffce3

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x020003080c00320c 0x408000c203000c83

def z47 : W := mkw 0x4000000214000094 0x1000000085000025 0x0800001e3c000ffd 0x020000078f0003ff

def z48 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x90f180fe00460f81 0x243c603f801183e0

def z49 : W := mkw 0x09e9489520000000 0x027a522548000000 0x00f0000000000000 0x003c000000000000

def z50 : W := mkw 0x4000000000025094 0x1000000000009425 0x020000000047fffe 0x008000000011ffff

def z51 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xe7ffff0003fffffe 0xf9ffffc000ffffff

def z52 : W := mkw 0x05d9cd000266d000 0x017673400099b400 0x80f18c000046c000 0x203c63000011b000

def z53 : W := mkw 0x05d9cd000266d000 0x017673400099b400 0xe7ff8c0003fec002 0x79ffe30000ffb000

def z54 : W := mkw 0x003010b163c18c62 0x400c042c58f06318 0x1c0000f1f3c1cc73 0x0700003c7cf0731c

def z55 : W := mkw 0x01cdef0000000000 0x00737bc000000000 0xe1ffff0000000000 0xf87fffc000000000

def z56 : W := mkw 0x89effffffd992a49 0x627bffffff664a92 0xffffffffffb93a4f 0xffffffffffee4e93

def z57 : W := mkw 0x003000b002c00c02 0x000c002c00b00300 0xf4f000f003c00c03 0x3d3c003c00f00300

def z58 : W := mkw 0x02fb58fd63ed8f63 0xc0bed63f58fb63d8 0xfffffcfff3ffcff3 0xffffff3ffcfff3fc

def z59 : W := mkw 0x00d9580003658000 0x0036560000d96000 0xe7fffc0003ffc002 0xf9ffff0000fff000

def z60 : W := mkw 0x058d220000342000 0x01634880000d0800 0x010e000000380000 0x00438000000e0000

def z61 : W := mkw 0x80767af9ebd9ae6b 0x601d9ebe7af66b9a 0xfffe7ff9fff9fe7f 0xffff9ffe7ffe7f9f

def z62 : W := mkw 0x0002006800880a01 0x0000801a00220280 0x7f0e03e80fb93a4f 0xdfc380fa03ee4e93

def z63 : W := mkw 0x0000850214000000 0x0000214085000000 0xa8018f1e3c000001 0xea0063c78f000000

def z64 : W := mkw 0x0040480120000000 0x0010120048000000 0x08007c01f0000000 0x82001f007c000000

def z65 : W := mkw 0x4000850214025094 0x1000214085009425 0x80018c163046c5b0 0x200063058c11b16c

def z66 : W := mkw 0x8bfffffffffd2f4b 0xe2ffffffffff4bd2 0xffffffffffff3fcf 0xffffffffffffcff3

def z67 : W := mkw 0x0bffffffffed8f63 0xc2fffffffffb63d8 0xffffffffffffcff3 0xfffffffffffff3fc

def z68 : W := mkw 0x028b004c002c0301 0x80a2c013000b00c0 0x030f800e003e0380 0x40c3e003800f80e0

def z69 : W := mkw 0x42bb85fe16ee5f97 0x90aee17f85bb97e5 0xffff8ffe3fffffff 0xffffe3ff8fffffff

def z70 : W := mkw 0x0210002002ec0f03 0x8084000800bb03c0 0x0600000003fe0f82 0x0180000000ff83e0

def z71 : W := mkw 0x0defefdfbc367000 0x037bfbf7ef0d9c00 0xfbfffffffc3e3001 0xfeffffffff0f8c00

def z72 : W := mkw 0x498fa74e9c025094 0x1263e9d3a7009425 0xab0f8f1e3c47ffff 0xeac3e3c78f11ffff

def z73 : W := mkw 0x80447a01e911a068 0x60111e807a44681a 0x08007f01fc01f07c 0x82001fc07f007c1f

def z74 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff1633fff5b2 0xf9ffffc58cfffd6c

def z75 : W := mkw 0x02bb10fc43ed8f63 0xc0aec43f10fb63d8 0xf7ff80fe03ffcff3 0x7dffe03f80fff3fc

def z76 : W := mkw 0x4000000000025094 0x1000000000009425 0x020000000006338c 0x0080000000018ce3

def z77 : W := mkw 0x01ddef0002640000 0x00777bc000990000 0xe7ffff0003fe0002 0xf9ffffc000ff8000

def z78 : W := mkw 0x0bffefffbeec0f03 0x82fffbffefbb03c0 0xfffffffffffe0f83 0xffffffffffff83e0

def z79 : W := mkw 0x82bf22fc8afc2f0b 0xa0afc8bf22bf0bc2 0xf7ff83fe0ffe3f8f 0x7dffe0ff83ff8fe3

def z80 : W := mkw 0x0089000000240000 0x0022400000090000 0x030f8000003e0000 0x40c3e000000f8000

def z81 : W := mkw 0x058da70000367000 0x016369c0000d9c00 0x030f8300003e3000 0x40c3e0c0000f8c00

def z82 : W := mkw 0x058da70000367000 0x016369c0000d9c00 0xa30f8f00007ff002 0xe8c3e3c0001ffc00

def z83 : W := mkw 0x0002004800000000 0x0000801200000000 0x710e00e800000001 0x5c43803a00000000

def z84 : W := mkw 0x4070cd933642d4b6 0x101c3364cd90b52d 0x80f18c163046c5b0 0x203c63058c11b16c

def z85 : W := mkw 0x0544ff000113f000 0x01513fc00044fc00 0x00007f000001f000 0x80001fc000007c00

def z86 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff801e03fe0f83 0x79ffe00780ff83e0

def z87 : W := mkw 0x80063248c9112048 0x60018c9232444812 0x790e73e9cc01304d 0xde439cfa73004c13

def z88 : W := mkw 0x80020068c8880a49 0x6000801a32220292 0x3a0003e9cc013a4f 0xce8000fa73004e93

def z89 : W := mkw 0x09efffdfbd112000 0x027bfff7ef444800 0xffffffffffb93003 0xffffffffffee4c00

def z90 : W := mkw 0x00547a000351a000 0x00151e8000d46800 0xe7fe7f0003f9f002 0xf9ff9fc000fe7c00

def z91 : W := mkw 0x0004320001112000 0x00010c8000444800 0x670e730003b93002 0xd9c39cc000ee4c00

def z92 : W := mkw 0x85dfff68cbfffa49 0x6177ffda32fffe92 0xffffffe9cffffa4f 0xfffffffa73fffe93

def z93 : W := mkw 0x01cdef0000025000 0x00737bc000009400 0xe3ffff000047f002 0xf8ffffc00011fc00

def z94 : W := mkw 0x89ef7afde9992a49 0x627bdebf7a664a92 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z95 : W := mkw 0x807058b163d9ae6b 0x601c162c58f66b9a 0xfef07cf1f3f9fe7f 0xbfbc1f3c7cfe7f9f

def z96 : W := mkw 0x07fffffd63ffff63 0xc1ffffff58ffffd8 0xfffffffff3fffff3 0xfffffffffcfffffc

def z97 : W := mkw 0x00ab00dc00000000 0x002ac03700000000 0xf1ff80fe00000001 0x7c7fe03f80000000

def z98 : W := mkw 0x01fdffb163c18c62 0x407f7fec58f06318 0xfdfffff1f3c1cc73 0xff7ffffc7cf0731c

def z99 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe5fe7c0003f9c002 0xb97f9f0000fe7000

def z100 : W := mkw 0x0000102041810840 0x4000040810604210 0x7c0070e1c3810843 0x9f001c3870e04210

def z101 : W := mkw 0x0210002002ec0f03 0x8084000800bb03c0 0x0400000003b80000 0x0100000000ee0000

def z102 : W := mkw 0xc006b76add9b7add 0x7001addab766deb7 0xff0fffffffffffff 0xffc3ffffffffffff

def z103 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x54f070e1c3c1cc72 0x153c1c3870f0731c

def z104 : W := mkw 0x4000000000025094 0x1000000000009425 0x000000000046c5b0 0x000000000011b16c

def z105 : W := mkw 0x059db7000377f000 0x01676dc000ddfc00 0x070f830003fff002 0x41c3e0c000fffc00

def z106 : W := mkw 0x4544ff021513f094 0x11513fc08544fc25 0x08007f003c01f07c 0x82001fc00f007c1f

def z107 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0xb20180fe00460f83 0x6c80603f801183e0

def z108 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000e000000000 0x0400003800000000

def z109 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x55fe00e003b80000 0x157f803800ee0000

def z110 : W := mkw 0x02bf32fc03fd2f03 0x80afccbf00ff4bc0 0xf7fff3fe03ff3f83 0xfdfffcff80ffcfe0

def z111 : W := mkw 0x02fb58fd63ed8f63 0xc0bed63f58fb63d8 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z112 : W := mkw 0x002000b160800c62 0x4008002c58200318 0x100000e1c0000000 0x0400003870000000

def z113 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x47fff30003be3000 0x51fffcc000ef8c00

def z114 : W := mkw 0x422200fe14880f97 0x9088803f852203e5 0x180000fe3c000ffd 0x0600003f8f0003ff

def z115 : W := mkw 0x002000b160800c62 0x4008002c58200318 0x180000f1f0000c71 0x0600003c7c00031c

def z116 : W := mkw 0x05fdffb163f7fc62 0x417f7fec58fdff18 0xfffffff1f3fffc73 0xfffffffc7cffff1c

def z117 : W := mkw 0x8006224888182209 0x2001889222060882 0x7b0e73e9cc38320d 0xdec39cfa730e0c83

def z118 : W := mkw 0x0000102041810840 0x4000040810604210 0x7e0073e9cf813a4f 0xdf801cfa73e04e93

def z119 : W := mkw 0x4000850214025094 0x1000214085009425 0x08000f003c01f07c 0x820003c00f007c1f

def z120 : W := mkw 0x05447a000111a000 0x01511e8000446800 0x0000700000000000 0x00001c0000000000

def z121 : W := mkw 0x002000b000800c02 0x0008002c00200300 0x100000f000000c01 0x0400003c00000300

def z122 : W := mkw 0x0000000000025000 0x0000000000009400 0x020000000047f002 0x008000000011fc00

def z123 : W := mkw 0x082200dda8000000 0x020880376a000000 0x100000e1c0000000 0x0400003870000000

def z124 : W := mkw 0x082200dfbc000000 0x02088037ef000000 0x180000fffc000001 0x0600003fff000000

def z125 : W := mkw 0x09efeffffc800c62 0x427bfbffff200318 0xf9fffffffc000c71 0xfe7fffffff00031c

def z126 : W := mkw 0x05ddff2043f7fc62 0x41777fc810fdff18 0xe7ffff0003fffc72 0xf9ffffc000ffff1c

def z127 : W := mkw 0x0089000000000000 0x0022400000000000 0xe1ff800000000000 0x787fe00000000000

def z128 : W := mkw 0x09446a01a8000000 0x02511a806a000000 0x00007001c0000000 0x00001c0070000000

def z129 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf5ff80fe03b80001 0x7d7fe03f80ee0000

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a0003080c013a4f 0xca8000c203004e93

def z131 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xc5fffc0003fec000 0x317fff0000ffb000

def z132 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xd1fffcf7f0000000 0x347fff3dfc000000

def z133 : W := mkw 0x898fb76edd992a49 0x6263eddbb7664a92 0x7f0ff3efcfb93a4f 0xdfc3fcfbf3ee4e93

def z134 : W := mkw 0x0060cd9334000000 0x00183364cd000000 0xf8f1fffffc000001 0xfe3c7fffff000000

def z135 : W := mkw 0x05ffffdc0377f000 0x017ffff700ddfc00 0xf7fffffe03fff003 0xfdffffff80fffc00

def z136 : W := mkw 0x0099850002665000 0x0026614000999400 0xe7ff8f0003fff002 0xf9ffe3c000fffc00

def z137 : W := mkw 0x0050580003418000 0x0014160000d06000 0x44f0700003800000 0x113c1c0000e00000

def z138 : W := mkw 0x045058000377f000 0x0114160000ddfc00 0xe6f07c0003fff002 0xb9bc1f0000fffc00

def z139 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf1fff0ffc0000001 0x7c7ffc3ff0000000

def z140 : W := mkw 0x80467a69e999aa69 0x60119e9a7a666a9a 0x7f0e7fe9ffb9fa7f 0xdfc39ffa7fee7e9f

def z141 : W := mkw 0x09e9cd9734000000 0x027a7365cd000000 0x80f18c1630000000 0x203c63058c000000

def z142 : W := mkw 0x00b900b002e40c02 0x002e402c00b90300 0xf7ff80f003fe0c03 0x7dffe03c00ff8300

def z143 : W := mkw 0x80667af9e9992a49 0x60199ebe7a664a92 0xfffe7ff9ffb93a4f 0xffff9ffe7fee4e93

def z144 : W := mkw 0x07ff7afc03fdaf03 0x81ffdebf00ff6bc0 0x55fe70e003b80000 0x157f9c3800ee0000

def z145 : W := mkw 0x4000000214000094 0x1000000085000025 0xa8000c1e3c41cfff 0xaa0003078f1073ff

def z146 : W := mkw 0x02b900b402ec0f03 0x80ae402d00bb03c0 0x86f1801603fe0f82 0x21bc600580ff83e0

def z147 : W := mkw 0x003200f802c80e03 0x000c803e00b20380 0xf7fe00f803f80e03 0x7dff803e00fe0380

def z148 : W := mkw 0x0544ff000113f000 0x01513fc00044fc00 0xa201ff000047f002 0xe8807fc00011fc00

def z149 : W := mkw 0x49ffffffffc3dcf6 0x527ffffffff0f73d 0xffffffffffc7ffff 0xfffffffffff1ffff

def z150 : W := mkw 0x0050582163c18c62 0x4014160858f06318 0x0c007c01f3c1cc72 0x83001f007cf0731c

def z151 : W := mkw 0x029b004c026c0301 0x80a6c013009b00c0 0xe7ff800e03fe0382 0x79ffe00380ff80e0

def z152 : W := mkw 0x041010000377f000 0x0104040000ddfc00 0x0600000003fff002 0x0180000000fffc00

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001e00000f81 0x00000007800003e0

def z154 : W := mkw 0x0820009734000000 0x02080025cd000000 0x0000001630000000 0x000000058c000000

def z155 : W := mkw 0x4000000214000094 0x1000000085000025 0x2a00031e3c013fff 0xca8000c78f004fff

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa018c1e3047cff3 0xea8063078c11f3fc

def z157 : W := mkw 0x02b9009402640502 0x80ae402500990140 0x80f1801600460580 0x203c600580118160

def z158 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x770e00fe03b80f83 0x5dc3803f80ee03e0

def z159 : W := mkw 0x498fa74e9c025094 0x1263e9d3a7009425 0x030f830e0c06338c 0x40c3e0c383018ce3

def z160 : W := mkw 0x0002006800880a01 0x0000801a00220280 0x100000e800000a01 0x0400003a00000280

def z161 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0x47fe700003fff002 0x11ff9c0000fffc00

def z162 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xd4f07cf1f3c0c430 0x353c1f3c7cf0310c

def z163 : W := mkw 0x0202004c00080301 0x80808013000200c0 0x0000000e00000380 0x00000003800000e0

def z164 : W := mkw 0x07bfa7fc02fe7f03 0x81efe9ff00bf9fc0 0xf7ff83fe03fe3f83 0x7dffe0ff80ff8fe0

def z165 : W := mkw 0x07f9cd940266d502 0x81fe73650099b540 0x80f18c160046c580 0x203c63058011b160

def z166 : W := mkw 0x0070ddb163c3dc62 0x401c376c58f0f718 0xfef1fff1f3c7fc73 0xffbc7ffc7cf1ff1c

def z167 : W := mkw 0x49e9cd9734025094 0x127a7365cd009425 0xaaf18f1e3c47ffff 0xeabc63c78f11ffff

def z168 : W := mkw 0x45d9cd021666d094 0x117673408599b425 0x80f18c163046c5b0 0x203c63058c11b16c

def z169 : W := mkw 0x0946ef4bbc000000 0x0251bbd2ef000000 0x790e7fe9fc000001 0xde439ffa7f000000

def z170 : W := mkw 0x09ffffffffc18c62 0x427ffffffff06318 0xfdffffffffc1cc73 0xff7ffffffff0731c

def z171 : W := mkw 0x009d320003752000 0x00274c8000dd4800 0xe7fff30003ff3002 0xf9fffcc000ffcc00

def z172 : W := mkw 0x42bb00fc02ee5f97 0x90aec03f00bb97e5 0xf7ff80fe03ffffff 0x7dffe03f80ffffff

def z173 : W := mkw 0x89ef7afde9992a49 0x627bdebf7a664a92 0x7ffe73e9cfb93a4f 0xdfff9cfa73ee4e93

def z174 : W := mkw 0x058db70001377000 0x01636dc0004ddc00 0x670ff30003bf3002 0xd9c3fcc000efcc00

def z175 : W := mkw 0x09effffffd810840 0x427bffffff604210 0xfdffffffff810843 0xff7fffffffe04210

def z176 : W := mkw 0x89efefdfbc182209 0x227bfbf7ef060882 0xfbfffffffc38320d 0xfeffffffff0e0c83

def z177 : W := mkw 0x0defffdfbd13f000 0x037bfff7ef44fc00 0xf9fffffffc01f001 0xfe7fffffff007c00

def z178 : W := mkw 0x47fffffe17ffff97 0x91ffffff85ffffe5 0xfffffffe3fffffff 0xffffffff8fffffff

def z179 : W := mkw 0x0006224888000000 0x0001889222000000 0x790e73e9cc000001 0xde439cfa73000000

def z180 : W := mkw 0x0220009400000502 0x8088002500000140 0x0000001600000580 0x0000000580000160

def z181 : W := mkw 0x8006b76add992a49 0x6001addab7664a92 0xff0fffffffb93a4f 0xffc3ffffffee4e93

def z182 : W := mkw 0x03ffeffc02ec0f03 0x80fffbff00bb03c0 0xf7fffffe03fe0f83 0xfdffffff80ff83e0

def z183 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x79fe73e9cc000001 0xde7f9cfa73000000

def z184 : W := mkw 0x078fa74c003e7301 0x81e3e9d3000f9cc0 0x030f830e003e3380 0x40c3e0c3800f8ce0

def z185 : W := mkw 0x4210852216ee5f97 0x9084214885bb97e5 0xae018f1e3fffffff 0xeb8063c78fffffff

def z186 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc41cc73 0xfe7fffffff10731c

def z187 : W := mkw 0x0000002040800c62 0x4000000810200318 0x0000000000000c70 0x000000000000031c

def z188 : W := mkw 0x08ab00dfbc000000 0x022ac037ef000000 0xf9ff80fffc000001 0x7e7fe03fff000000

def z189 : W := mkw 0x4099850216665094 0x1026614085999425 0xefff8f1e3fffffff 0xfbffe3c78fffffff

def z190 : W := mkw 0x002200dc00000000 0x0008803700000000 0x100000fe00000001 0x0400003f80000000

def z191 : W := mkw 0x02ab00fc00880f03 0x80aac03f002203c0 0xf1ff80fe00000f81 0x7c7fe03f800003e0

def z192 : W := mkw 0x8004220088102008 0x2001088022040802 0x000003000c00300c 0x000000c003000c03

def z193 : W := mkw 0x80062268c8982a49 0x6001889a32260a92 0x1b0e03e9cc383a4d 0x46c380fa730e0e93

def z194 : W := mkw 0x40009522558358d4 0x500025489560d635 0xfe01ffffffc7ffff 0xff807ffffff1ffff

def z195 : W := mkw 0x09cfef4fbc000000 0x0273fbd3ef000000 0x090fff0ffc000000 0xc243ffc3ff000000

def z196 : W := mkw 0x003000b002c00c02 0x000c002c00b00300 0xfcf00cf033c1cc73 0xbf3c033c0cf0731c

def z197 : W := mkw 0x0070489122408422 0x001c122448902108 0xf8f07cf1f040c431 0xbe3c1f3c7c10310c

def z198 : W := mkw 0x458da70214367094 0x116369c0850d9c25 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z199 : W := mkw 0x0040580161018060 0x4010160058406018 0x08007c01f001c070 0x82001f007c00701c

def z200 : W := mkw 0x8006226888982a09 0x2001889a22260a82 0x770e03e80fb83a0f 0x5dc380fa03ee0e83

def z201 : W := mkw 0x87fffffccbffff4b 0xe1ffffff32ffffd2 0xffffffffcfffffcf 0xfffffffff3fffff3

def z202 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef07ff9ffc1fe7f 0xffbc1ffe7ff07f9f

def z203 : W := mkw 0x40ab85de14025094 0x102ae17785009425 0xfbff8ffe3c47ffff 0xfeffe3ff8f11ffff

def z204 : W := mkw 0x822200fcc8880f4b 0xe088803f322203d2 0x180000ffcc000fcd 0x0600003ff30003f3

def z205 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe7fff00003fe0002 0x79fffc0000ff8000

def z206 : W := mkw 0x80021068c9992a49 0x6000841a32664a92 0x1e0000e9cfb93a4f 0x0780003a73ee4e93

def z207 : W := mkw 0xc0063268c99b7add 0x70018c9a3266deb7 0x7f0e73e9cfffffff 0xdfc39cfa73ffffff

def z208 : W := mkw 0x00eb48dd20000000 0x003ad23748000000 0xf9fffcfff0000001 0xfe7fff3ffc000000

def z209 : W := mkw 0x0000850000025000 0x0000214000009400 0xaa018f080c47fa4f 0xea8063c20311fe93

def z210 : W := mkw 0x09ff7afdebc18c62 0x427fdebf7af06318 0xfdfe7cf1f3c1cc73 0xbf7f9f3c7cf0731c

def z211 : W := mkw 0x086248dfbc000000 0x02189237ef000000 0xf8f07cfffc000001 0xbe3c1f3fff000000

def z212 : W := mkw 0x0966efdfbc000000 0x0259bbf7ef000000 0x18007ffffc000001 0x86001fffff000000

def z213 : W := mkw 0x422285fe148a5f97 0x9088a17f852297e5 0xba018ffe3c47ffff 0xee8063ff8f11ffff

def z214 : W := mkw 0x05dfff488b77f000 0x0177ffd222ddfc00 0xffffffe9cffff003 0xfffffffa73fffc00

def z215 : W := mkw 0x028b006c00ac0b01 0x80a2c01b002b02c0 0x770f80ee03be0b83 0x5dc3e03b80ef82e0

def z216 : W := mkw 0x4000000214000094 0x1000000085000025 0x080000003c00007c 0x020000000f00001f

def z217 : W := mkw 0x06bb10fc03ffff03 0x81aec43f00ffffc0 0xf7ff80fe03ffff83 0x7dffe03f80ffffe0

def z218 : W := mkw 0x8000102041992a49 0x6000040810664a92 0x0400000003b80000 0x0100000000ee0000

def z219 : W := mkw 0x0dff7addab75a000 0x037fdeb76add6800 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z220 : W := mkw 0x4000000214000094 0x1000000085000025 0xaa01801e3c460fff 0x6a8060078f1183ff

def z221 : W := mkw 0x441010000377f094 0x1104040000ddfc25 0x0600000003fffffe 0x0180000000ffffff

def z222 : W := mkw 0x0befefdfbc2c0301 0x82fbfbf7ef0b00c0 0xfbfffffffc3e0381 0xfeffffffff0f80e0

def z223 : W := mkw 0x4000000000000094 0x1000000000000025 0x0000000000000ffc 0x00000000000003ff

def z224 : W := mkw 0x4bffefffbeee5f97 0x92fffbffefbb97e5 0xffffffffffffffff 0xffffffffffffffff

def z225 : W := mkw 0xc0001020419b7add 0x700004081066deb7 0x0600000003fffffe 0x0180000000ffffff

def z226 : W := mkw 0x403085b216c25c96 0x100c216c85b09725 0xfef18ffe3fc7ffff 0xffbc63ff8ff1ffff

def z227 : W := mkw 0x8002004888080209 0x2000801222020082 0x000000080c00020c 0x0000000203000083

def z228 : W := mkw 0x0020009000000000 0x0008002400000000 0xf0f000f000000001 0x3c3c003c00000000

def z229 : W := mkw 0x08000003bc000000 0x02000000ef000000 0x08000001fc000000 0x020000007f000000

def z230 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x67fe730003b93002 0xd9ff9cc000ee4c00

def z231 : W := mkw 0x0010000002400000 0x0004000000900000 0xe4f0000003c00002 0x393c000000f00000

def z232 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff1033fffc73 0xfbffffc40cffff1c

def z233 : W := mkw 0x441095021777f094 0x1104254085ddfc25 0xae018f1e3fffffff 0xeb8063c78fffffff

def z234 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xefffff1e3ffff003 0xfbffffc78ffffc00

def z235 : W := mkw 0x0006224888000000 0x0001889222000000 0x010e03080c000000 0x404380c203000000

def z236 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x51fff3efcc000000 0x547ffcfbf3000000

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000c103040c430 0x200003040c10310c

def z238 : W := mkw 0xc006a74a9c1a729d 0x3001a9d2a7069ca7 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z239 : W := mkw 0x05cdff000137f000 0x01737fc0004dfc00 0x030fff00003ff000 0xc0c3ffc0000ffc00

def z240 : W := mkw 0x0289000400240100 0x80a2400100090040 0x0001800600060180 0x0000600180018060

def z241 : W := mkw 0x80043200c9112048 0x60010c8032444812 0x08007301cc01304c 0x82001cc073004c13

def z242 : W := mkw 0x003000b162c00c62 0x400c002c58b00318 0xfcf000f1f3c00c73 0x3f3c003c7cf0031c

def z243 : W := mkw 0x0554ff000353f000 0x01553fc000d4fc00 0xe4f07f0003c1f002 0xb93c1fc000f07c00

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000041cc72 0x000000000010731c

def z245 : W := mkw 0x85ddff2043fffa49 0x61777fc810fffe92 0xe7ffff0003fffa4e 0xf9ffffc000fffe93

def z246 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xd5ff80f603fe0580 0x357fe03d80ff8160

def z247 : W := mkw 0x0002006800880a01 0x0000801a00220280 0x770e00e803b80a03 0x5dc3803a00ee0280

def z248 : W := mkw 0xc006b76add9b7add 0x7001addab766deb7 0x7f0ff3efcfbf3bcf 0xdfc3fcfbf3efcef3

def z249 : W := mkw 0x027058b163ed8f63 0xc09c162c58fb63d8 0xfef07cf1f3ffcff3 0xbfbc1f3c7cfff3fc

def z250 : W := mkw 0x05f9ddb163e7dc62 0x417e776c58f9f718 0xfcf1fcf1f3c7cc73 0xbf3c7f3c7cf1f31c

def z251 : W := mkw 0x05fd7ab163f5ac62 0x417f5eac58fd6b18 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z252 : W := mkw 0x0000002040800840 0x4000000810200210 0x180000e1c0000841 0x0600003870000210

def z253 : W := mkw 0x02fb48fd22ec8f23 0x80bed23f48bb23c8 0xf7ff8cfe33fecfb3 0x7dffe33f8cffb3ec

def z254 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef1fcfff3c7cff3 0xffbc7f3ffcf1f3fc

def z255 : W := mkw 0x407058b163c3dcf6 0x501c162c58f0f73d 0xfef07cf1f3c7ffff 0xbfbc1f3c7cf1ffff

def z256 : W := mkw 0x898fa74e9c182209 0x2263e9d3a7060882 0x030f830e0c38320c 0x40c3e0c3830e0c83

def z257 : W := mkw 0x040010000113f000 0x010004000044fc00 0x000000000001f000 0x0000000000007c00

def z258 : W := mkw 0x00ab00dc00000000 0x002ac03700000000 0x51fe00e000000000 0x147f803800000000

def z259 : W := mkw 0x0010002002c00c02 0x0004000800b00300 0x0400000003c00c02 0x0100000000f00300

def z260 : W := mkw 0x09e9cd9734000000 0x027a7365cd000000 0xf8f1fcf7f0000001 0xbe3c7f3dfc000000

def z261 : W := mkw 0x029b006c02ec0f03 0x80a6c01b00bb03c0 0x070f800e03fe0f82 0x41c3e00380ff83e0

def z262 : W := mkw 0x81cfff68c9992a49 0x6073ffda32664a92 0xffffffe9cfb93a4f 0xfffffffa73ee4e93

def z263 : W := mkw 0x4000850214025094 0x1000214085009425 0xa2018f0e0c47f38e 0xe88063c38311fce3

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8000c1030000001 0xaa0003040c000000

def z265 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x57ff80ee03be0380 0x55ffe03b80ef80e0

def z266 : W := mkw 0x007048b122c00c02 0x001c122c48b00300 0xfcf07cf1f3c00c03 0xbf3c1f3c7cf00300

def z267 : W := mkw 0x01cdff0001112000 0x00737fc000444800 0xe7ffff0003b93002 0xf9ffffc000ee4c00

def z268 : W := mkw 0xc002006adc880add 0x7000801ab72202b7 0x180000fffc000ffd 0x0600003fff0003ff

def z269 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x5cf07ce1f381c070 0x973c1f387ce0701c

def z270 : W := mkw 0x002000b160800c62 0x4008002c58200318 0xb8000cf1f041cc73 0xae00033c7c10731c

def z271 : W := mkw 0x027258fd63c98f63 0xc09c963f58f263d8 0xfcf07cfff3c1cff3 0xbf3c1f3ffcf073fc

def z272 : W := mkw 0x07fbcdfc02eedf03 0x81fef37f00bbb7c0 0xf7ff8cfe03fecf83 0x7dffe33f80ffb3e0

def z273 : W := mkw 0x09e9cd9734000000 0x027a7365cd000000 0xa8f18f1e3c000001 0xea3c63c78f000000

def z274 : W := mkw 0x80063248c9192249 0x60018c9232464892 0x0b0e7309cc39324c 0xc2c39cc2730e4c93

def z275 : W := mkw 0x098f224c88000000 0x0263c89322000000 0x010e000000000000 0x0043800000000000

def z276 : W := mkw 0x4040dd037503d0f4 0x50103740dd40f43d 0xaa01ff1ffc47ffff 0xea807fc7ff11ffff

def z277 : W := mkw 0x4002856a148a5a95 0x1000a15a852296a5 0xff0f8ffe3fffffff 0xffc3e3ff8fffffff

def z278 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x5d0e73e1cfb9304c 0x97439cf873ee4c13

def z279 : W := mkw 0x80163268cbd9ae6b 0x60058c9a32f66b9a 0x7f0e73e9cff9fe7f 0xdfc39cfa73fe7f9f

def z280 : W := mkw 0x4000850214025094 0x1000214085009425 0x08000f1e3c01fffd 0x820003c78f007fff

def z281 : W := mkw 0x4dffffdfbf77f094 0x137ffff7efddfc25 0xffffffffffffffff 0xffffffffffffffff

def z282 : W := mkw 0x8006324889192209 0x20018c9222464882 0x670e73080fb9320e 0xd9c39cc203ee4c83

def z283 : W := mkw 0x80043200c9112048 0x60010c8032444812 0x00007001c0000000 0x00001c0070000000

def z284 : W := mkw 0x0bfbcdff36ec0f03 0x82fef37fcdbb03c0 0xf7ff8cfe33fe0f83 0x7dffe33f8cff83e0

def z285 : W := mkw 0x00063268c9810840 0x40018c9a32604210 0x7d0e73e9cf810843 0xdf439cfa73e04210

def z286 : W := mkw 0x0000102041810840 0x4000040810604210 0xfc007cf1f3c1cc73 0xbf001f3c7cf0731c

def z287 : W := mkw 0x003010b043c18c62 0x400c042c10f06318 0xf4f000f003c1cc73 0x3d3c003c00f0731c

def z288 : W := mkw 0x4000850214025094 0x1000214085009425 0xaa018f003c47f07e 0xea8063c00f11fc1f

def z289 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff1e03ffff83 0xf9ffffc780ffffe0

def z290 : W := mkw 0x0004320001112000 0x00010c8000444800 0x6f0e73080fb93a4f 0xdbc39cc203ee4e93

def z291 : W := mkw 0x0dffffdfbf77f000 0x037ffff7efddfc00 0xfffffffffffff003 0xfffffffffffffc00

def z292 : W := mkw 0x047058b163f7fc62 0x411c162c58fdff18 0xfef07cf1f3fffc73 0xbfbc1f3c7cffff1c

def z293 : W := mkw 0x02ab00dc002c0301 0x80aac037000b00c0 0xf3ff80fe003e0381 0x7cffe03f800f80e0

def z294 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x770e70e9c3b80a03 0x5dc39c3a70ee0280

def z295 : W := mkw 0x82bf32fccbfd2f4b 0xe0afccbf32ff4bd2 0x7ffe73e9cfb93a4f 0xdfff9cfa73ee4e93

def z296 : W := mkw 0x0000102041810840 0x4000040810604210 0x0400000003810842 0x0100000000e04210

def z297 : W := mkw 0x02bb85fc02ee5f03 0x80aee17f00bb97c0 0xf7ff8ffe03ffff83 0xfdffe3ff80ffffe0

def z298 : W := mkw 0x0040480000000000 0x0010120000000000 0xe0f07c0000000000 0xb83c1f0000000000

def z299 : W := mkw 0x0540cd000002d000 0x015033400000b400 0x00000c000000c000 0x0000030000003000

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000c000041c002 0xa800030000107000

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x780070e1c0000001 0x9e001c3870000000

def z302 : W := mkw 0x809f3268cbfd2a49 0x6027cc9a32ff4a92 0xfffff3e9cfff3a4f 0xfffffcfa73ffce93

def z303 : W := mkw 0x0befefffbc880f03 0x82fbfbffef2203c0 0xf9fffffffc000f81 0xfe7fffffff0003e0

def z304 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xf4f07ce1c3c1c002 0xbd3c1f3870f07000

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001801600460580 0x2000600580118160

def z306 : W := mkw 0x05ddef000266d000 0x01777bc00099b400 0xe1ffff000046c000 0xf87fffc00011b000

def z307 : W := mkw 0x0dfffffffff7fc62 0x437ffffffffdff18 0xfffffffffffffc73 0xffffffffffffff1c

def z308 : W := mkw 0x007058b003c18c02 0x001c162c00f06300 0xf4f07cf003c1cc03 0xbd3c1f3c00f07300

def z309 : W := mkw 0x0004220088000000 0x0001088022000000 0x08007301cc000000 0x82001cc073000000

def z310 : W := mkw 0x01efefdc00000000 0x007bfbf700000000 0xf1fffffe00000001 0xfc7fffff80000000

def z311 : W := mkw 0x07fffffc03ffff03 0x81ffffff00ffffc0 0xf7ffffe003fff002 0xfdfffff800fffc00

def z312 : W := mkw 0x0020009120000422 0x0008002448000108 0x0000001030000430 0x000000040c00010c

def z313 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x5cf070f1f3800c71 0x173c1c3c7ce0031c

def z314 : W := mkw 0x4070ddb377c3dcf6 0x501c376cddf0f73d 0xfcf1fcf7f3c7cdf3 0xbf3c7f3dfcf1f37c

def z315 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0xac000c1033c1cc73 0xab0003040cf0731c

def z316 : W := mkw 0x0006224888000000 0x0001889222000000 0x510e70e1c0000000 0x14439c3870000000

def z317 : W := mkw 0x85fffff9ebfffe6b 0x617ffffe7affff9a 0xfffffff9fffffe7f 0xfffffffe7fffff9f

def z318 : W := mkw 0x822632fcc9992f4b 0xe0898cbf32664bd2 0x7f0e73ffcfb93fcf 0xdfc39cfff3ee4ff3

def z319 : W := mkw 0x007258f963c98e63 0x401c963e58f26398 0xfffe7cf9f3f9ce73 0xffff9f3e7cfe739c

def z320 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x45fe7f0003b9f000 0x917f9fc000ee7c00

def z321 : W := mkw 0x02fb58fd63ed8f63 0xc0bed63f58fb63d8 0xfdfe7cf1f3f9cc73 0xbf7f9f3c7cfe731c

def z322 : W := mkw 0x00666ad9a8000000 0x00199ab66a000000 0xf9fe7ff9fc000001 0xfe7f9ffe7f000000

def z323 : W := mkw 0x802200f9e8880e6b 0x6008803e7a22039a 0x180000f9fc000e7d 0x0600003e7f00039f

def z324 : W := mkw 0x006058b161818c62 0x4018162c58606318 0x18007cf1f001cc71 0x86001f3c7c00731c

def z325 : W := mkw 0x0070589163418462 0x401c162458d06118 0x88f07c11f041c470 0xa23c1f047c10711c

def z326 : W := mkw 0x0200002000880f03 0x80800008002203c0 0x0000000000000f80 0x00000000000003e0

def z327 : W := mkw 0x02ab00fc00ac0f03 0x80aac03f002b03c0 0x130f80fe003e0f81 0x44c3e03f800f83e0

def z328 : W := mkw 0x00af22dc88000000 0x002bc8b722000000 0xf9fff3ffcc000001 0xfe7ffcfff3000000

def z329 : W := mkw 0x803632f8cbd92e4b 0x600d8cbe32f64b92 0xfffe73f9cff93e4f 0xffff9cfe73fe4f93

def z330 : W := mkw 0x4000000000025094 0x1000000000009425 0xaa000c103047ffff 0xaa8003040c11ffff

def z331 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0xf1ffffe1c0000000 0xfc7ffff870000000

def z332 : W := mkw 0x4006a74a9c025094 0x1001a9d2a7009425 0xfb0ffffffc47ffff 0xfec3ffffff11ffff

def z333 : W := mkw 0x0144ef0000000000 0x00513bc000000000 0x00007f0000000000 0x80001fc000000000

def z334 : W := mkw 0x8002106841992a49 0x6000841a10664a92 0x770e00e803b93a4f 0x5dc3803a00ee4e93

def z335 : W := mkw 0x0002004800080201 0x0000801200020080 0x030e000800380200 0x40c38002000e0080

def z336 : W := mkw 0x0210102043ed8f63 0xc084040810fb63d8 0x0600000003ffcff2 0x0180000000fff3fc

def z337 : W := mkw 0x4040dd037503d0f4 0x50103740dd40f43d 0x08007f01fc01f07c 0x82001fc07f007c1f

def z338 : W := mkw 0x0000850000025000 0x0000214000009400 0x0201830000063000 0x408060c000018c00

def z339 : W := mkw 0x4000850214025094 0x1000214085009425 0x88018c1e3c46cffd 0x220063078f11b3ff

def z340 : W := mkw 0x4000850214025094 0x1000214085009425 0xa2018f163047f5b2 0xe88063c58c11fd6c

def z341 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x80f1ff000047f000 0xa03c7fc00011fc00

def z342 : W := mkw 0x082622dfbc000000 0x020988b7ef000000 0x790e73fffc000001 0xde439cffff000000

def z343 : W := mkw 0x4000850214025094 0x1000214085009425 0x0a01831e3c063ffd 0x428060c78f018fff

def z344 : W := mkw 0x0210002002ec0f03 0x8084000800bb03c0 0xa601801e03fe0f83 0x6980600780ff83e0

def z345 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff080ffffa4f 0xfbffffc203fffe93

def z346 : W := mkw 0x02bb85fe16ec0f03 0x80aee17f85bb03c0 0xffff8ffe3ffe0f83 0xffffe3ff8fff83e0

def z347 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xf4f070f1c3c00c03 0x3d3c1c3c70f00300

def z348 : W := mkw 0x482200dfbc000094 0x12088037ef000025 0x180000fffc000ffd 0x0600003fff0003ff

def z349 : W := mkw 0x0000100001010000 0x0000040000404000 0x6400700003810002 0x99001c0000e04000

def z350 : W := mkw 0x82bf32fccbfd2f4b 0xe0afccbf32ff4bd2 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z351 : W := mkw 0x0050582043c18c62 0x4014160810f06318 0xe4f07c0003c1cc72 0xb93c1f0000f0731c

def z352 : W := mkw 0x09edef9734000000 0x027b7be5cd000000 0xe1ffff1630000000 0xf87fffc58c000000

def z353 : W := mkw 0x0fffffffbfffff03 0x83ffffffefffffc0 0xffffffffffffff83 0xffffffffffffffe0

def z354 : W := mkw 0x4060cd9334025094 0x10183364cd009425 0xfaf1fffffc47ffff 0xfebc7fffff11ffff

def z355 : W := mkw 0x85ddff00cb77f048 0x61777fc032ddfc12 0xefffff01cffff04e 0xfbffffc073fffc13

def z356 : W := mkw 0x002010b161810c62 0x4008042c58604318 0x7c0070f1f3810c73 0x9f001c3c7ce0431c

def z357 : W := mkw 0x82ff7afdebfdaf6b 0xe0bfdebf7aff6bda 0xffffffffffffffff 0xffffffffffffffff

def z358 : W := mkw 0x0410102043f7fc62 0x4104040810fdff18 0x0600000003fffc72 0x0180000000ffff1c

def z359 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf5fe00f003f80c03 0x3d7f803c00fe0300

def z360 : W := mkw 0x09efefffbc880a01 0x027bfbffef220280 0xffffffffffb80a03 0xffffffffffee0280

def z361 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0xe5ffff0003b80000 0xf97fffc000ee0000

def z362 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff83fe0fff3fcf 0xffffe0ff83ffcff3

def z363 : W := mkw 0x022200fd60880f63 0xc088803f582203d8 0x180000fff0000ff1 0x0600003ffc0003fc

def z364 : W := mkw 0x0050480002408000 0x0014120000902000 0x80f00c000040c000 0x203c030000103000

def z365 : W := mkw 0x0060489120000000 0x0018122448000000 0x80f00c1030000000 0x203c03040c000000

def z366 : W := mkw 0x00bb00fc02c00c02 0x002ec03f00b00300 0xf5ff80fe03c00c03 0x7d7fe03f80f00300

def z367 : W := mkw 0x0000850000025000 0x0000214000009400 0xa2018f1e0047ff83 0xe88063c78011ffe0

def z368 : W := mkw 0x8dfffffffffffa49 0x637ffffffffffe92 0xfffffffffffffa4f 0xfffffffffffffe93

def z369 : W := mkw 0x82bb00fccaec0f4b 0xe0aec03f32bb03d2 0xffff80ffcffe0fcf 0x7fffe03ff3ff83f3

def z370 : W := mkw 0x0020009120000000 0x0008002448000000 0x180000f1f0000001 0x0600003c7c000000

def z371 : W := mkw 0x0abb00ffbeec0f03 0x82aec03fefbb03c0 0xffff80fffffe0f83 0x7fffe03fffff83e0

def z372 : W := mkw 0x007048b162c08c62 0x401c122c58b02318 0x98f00cf1f040cc71 0x263c033c7c10331c

def z373 : W := mkw 0x45d9cd021666d094 0x117673408599b425 0xaaf18f1e3c47ffff 0xeabc63c78f11ffff

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000c003001c070 0x820003000c00701c

def z375 : W := mkw 0x8010102043d9ae6b 0x6004040810f66b9a 0x0600000003f9fe7e 0x0180000000fe7f9f

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa000f183c41fe7f 0xea8003c60f107f9f

def z377 : W := mkw 0x0610102003ffff03 0x8184040800ffffc0 0x0600000003ffff82 0x0180000000ffffe0

def z378 : W := mkw 0x00ab00fc00880a01 0x002ac03f00220280 0xf7ff80fe03b80a03 0x7dffe03f80ee0280

def z379 : W := mkw 0x0574ffb163d3fc62 0x415d3fec58f4ff18 0xfcf07ff1f3c1fc73 0xbf3c1ffc7cf07f1c

def z380 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x7cf070e1c3810843 0x9f3c1c3870e04210

def z381 : W := mkw 0x80043220c9912848 0x60010c8832644a12 0x7c0073e1cf81384f 0x9f001cf873e04e13

def z382 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x77fe00e803b80a03 0x5dff803a00ee0280

def z383 : W := mkw 0x4000000000025094 0x1000000000009425 0x2a0003080c47ffff 0xca8000c20311ffff

def z384 : W := mkw 0x02fb48fd22ec0f03 0x80bed23f48bb03c0 0xfffffcfff3fe0f83 0xffffff3ffcff83e0

def z385 : W := mkw 0x4000000000025094 0x1000000000009425 0x000000000001f07c 0x0000000000007c1f

def z386 : W := mkw 0x0002106841890a41 0x4000841a10624290 0x7f0e70e9c3b90a43 0xdfc39c3a70ee4290

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001801e00000001 0x6800600780000000

def z388 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x070e03080fb93a4e 0x41c380c203ee4e93

def z389 : W := mkw 0x4000000000025094 0x1000000000009425 0xa201801e0047ffff 0x688060078011ffff

def z390 : W := mkw 0x0bff6afdaaec0f03 0x82ffdabf6abb03c0 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z391 : W := mkw 0x00a9009400000000 0x002a402500000000 0x80f1801600000000 0x203c600580000000

def z392 : W := mkw 0x80767af9ebd9ae6b 0x601d9ebe7af66b9a 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z393 : W := mkw 0x0004220000000000 0x0001088000000000 0x610e730000000000 0xd8439cc000000000

def z394 : W := mkw 0x041095000377f000 0x0104254000ddfc00 0xa6018f0003fff002 0xe98063c000fffc00

def z395 : W := mkw 0x02b9009402640502 0x80ae402500990140 0x00f0000000000000 0x003c000000000000

def z396 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f041cc73 0xbe3c1f3c7c10731c

def z397 : W := mkw 0x0000002000800800 0x0000000800200200 0x740000e003800803 0x1d00003800e00200

def z398 : W := mkw 0x0bff6afdaaec0f03 0x82ffdabf6abb03c0 0xf7fff0ffc3fe0f83 0x7dfffc3ff0ff83e0

def z399 : W := mkw 0x05fdffb163f7fc62 0x417f7fec58fdff18 0xf7ffffe1c3fff002 0xfdfffff870fffc00

def z400 : W := mkw 0x4000850214025094 0x1000214085009425 0x0001800600060180 0x0000600180018060

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x670e000003b80002 0x59c3800000ee0000

def z402 : W := mkw 0x80062268c8880a49 0x6001889a32220292 0x790e73e9cc000a4d 0xde439cfa73000293

def z403 : W := mkw 0x4944ef03bc025094 0x12513bc0ef009425 0xaa01ff1ffc47ffff 0xea807fc7ff11ffff

def z404 : W := mkw 0x8000102041992a49 0x6000040810664a92 0x2e0003080fb93a4f 0xcb8000c203ee4e93

def z405 : W := mkw 0x02bb00fd62ec0f63 0xc0aec03f58bb03d8 0xffff80fff3fe0ff3 0x7fffe03ffcff83fc

def z406 : W := mkw 0x0bffefdfbe640502 0x82fffbf7ef990140 0xf9fffffffc460581 0xfe7fffffff118160

def z407 : W := mkw 0x05d9480002648000 0x0176520000992000 0x00f0000000000000 0x003c000000000000

def z408 : W := mkw 0x0070ddb377c18c62 0x401c376cddf06318 0xfcf1ffffffc1cc73 0xff3c7ffffff0731c

def z409 : W := mkw 0x0050582043c18840 0x4014160810f06210 0xfcf07ce1c3c1c843 0xbf3c1f3870f07210

def z410 : W := mkw 0x0000000160000060 0x4000000058000018 0x08000001f0000070 0x020000007c00001c

def z411 : W := mkw 0x05fd7ab163f5ac62 0x417f5eac58fd6b18 0xfdfe7cf1f3f9cc73 0xbf7f9f3c7cfe731c

def z412 : W := mkw 0x85df7a68cbfdaa49 0x6177de9a32ff6a92 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800001030000c71 0x020000040c00031c

def z414 : W := mkw 0x80021068c9890a49 0x6000841a32624292 0x7c0070e9cf810a4f 0x9f001c3a73e04293

def z415 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x84f00c1033c1cc72 0x213c03040cf0731c

def z416 : W := mkw 0x0010000002408422 0x0004000000902108 0x000000000040c430 0x000000000010310c

def z417 : W := mkw 0x4070cd933642d4b6 0x101c3364cd90b52d 0xaaf18f1e3c47ffff 0xeabc63c78f11ffff

def z418 : W := mkw 0x09cdef03bc000000 0x02737bc0ef000000 0xe9ffff01fc000000 0xfa7fffc07f000000

def z419 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x570e73e9cfb8320c 0x55c39cfa73ee0c83

def z420 : W := mkw 0xc002856adc8a5add 0x7000a15ab72296b7 0xba018ffffc47ffff 0xee8063ffff11ffff

def z421 : W := mkw 0x8410102043fffa49 0x6104040810fffe92 0x0600000003fffa4e 0x0180000000fffe93

def z422 : W := mkw 0x049910000377f000 0x0126440000ddfc00 0xe7ff800003fff002 0x79ffe00000fffc00

def z423 : W := mkw 0x0000850214000000 0x0000214085000000 0xaa018f1e3c460f83 0xea8063c78f1183e0

def z424 : W := mkw 0x8000100041112048 0x6000040010444812 0x000000000001304c 0x0000000000004c13

def z425 : W := mkw 0x0070489122408422 0x001c122448902108 0x00f0000000000000 0x003c000000000000

def z426 : W := mkw 0x80747ab1ebd1ac6a 0x601d1eac7af46b1a 0xfcf07ff1ffc1fc7f 0xbf3c1ffc7ff07f1f

def z427 : W := mkw 0x807258f9ebc98e6b 0x601c963e7af2639a 0xfcf07cf9ffc1ce7f 0xbf3c1f3e7ff0739f

def z428 : W := mkw 0x0964ef93bc000000 0x02593be4ef000000 0xf8f07ff1fc000001 0xbe3c1ffc7f000000

def z429 : W := mkw 0x098fa74e9c000000 0x0263e9d3a7000000 0xa90f8f1e3c000001 0xea43e3c78f000000

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa01831e0c473fcf 0xea8060c78311cff3

def z431 : W := mkw 0x80767af9ebd9ae6b 0x601d9ebe7af66b9a 0x7ffe73e9cfb93a4f 0xdfff9cfa73ee4e93

def z432 : W := mkw 0x85df7a68cbfdaa49 0x6177de9a32ff6a92 0x7ffe73e9cfb93a4f 0xdfff9cfa73ee4e93

def z433 : W := mkw 0x09f9ddb777c18c62 0x427e776dddf06318 0xfcf1fcf7f3c1cc73 0xbf3c7f3dfcf0731c

def z434 : W := mkw 0x8000000000182209 0x2000000000060882 0x020000000038320c 0x00800000000e0c83

def z435 : W := mkw 0x0589850000265000 0x0162614000099400 0x0001800000060000 0x0000600000018000

def z436 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0ff3ffcfff3fcf 0xffc3fcfff3ffcff3

def z437 : W := mkw 0x80af32fcc9992a49 0x602bccbf32664a92 0xfffff3ffcfb93a4f 0xfffffcfff3ee4e93

def z438 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000001000400c03 0x2800000400100300

def z439 : W := mkw 0x02b9009402640502 0x80ae402500990140 0xa2f1801e00460f83 0x68bc6007801183e0

def z440 : W := mkw 0x0000100041018060 0x4000040010406018 0x000000000001c070 0x000000000000701c

def z441 : W := mkw 0x0060589161018060 0x4018162458406018 0xf8f07cf1f001c071 0xbe3c1f3c7c00701c

def z442 : W := mkw 0x00767af9ebc18c62 0x401d9ebe7af06318 0xfdfe7ff9ffc1cc73 0xff7f9ffe7ff0731c

def z443 : W := mkw 0x00747ab163d1ac62 0x401d1eac58f46b18 0xfffe7ff1f3f9fc73 0xffff9ffc7cfe7f1c

def z444 : W := mkw 0x09ffefdfbe640000 0x027ffbf7ef990000 0xfffffffffffe0003 0xffffffffffff8000

def z445 : W := mkw 0x80043200c9112048 0x60010c8032444812 0x2a007309cc013a4f 0xca801cc273004e93

def z446 : W := mkw 0x09edef97bc000000 0x027b7be5ef000000 0x88f1ff17fc000000 0xa23c7fc5ff000000

def z447 : W := mkw 0x8006224888182209 0x2001889222060882 0x010e000000380000 0x00438000000e0000

def z448 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc01f07d 0xfe7fffffff007c1f

def z449 : W := mkw 0x4944ef03bc025094 0x12513bc0ef009425 0x08007f01fc01f07c 0x82001fc07f007c1f

def z450 : W := mkw 0x0bf9cd9736640502 0x82fe7365cd990140 0x80f18c1630460580 0x203c63058c118160

def z451 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003800000 0x0100000000e00000

def z452 : W := mkw 0x0070589123418422 0x001c162448d06108 0xe4f07c1033c1c432 0xb93c1f040cf0710c

def z453 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x57fe00e003fe0f82 0x15ff803800ff83e0

def z454 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07cf1f3800001 0xbf3c1f3c7ce00000

def z455 : W := mkw 0x0040580001018000 0x0010160000406000 0x00007c000001c000 0x80001f0000007000

def z456 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc46c5b1 0xfe7fffffff11b16c

def z457 : W := mkw 0x0944ff03fd018060 0x42513fc0ff406018 0x08007f01fc01c070 0x82001fc07f00701c

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800000000010843 0x8a00000000004210

def z459 : W := mkw 0x02bb10fc43ed0f43 0xc0aec43f10fb43d0 0xfffff0ffc3ff0fc3 0xfffffc3ff0ffc3f0

def z460 : W := mkw 0x80043200c9112048 0x60010c8032444812 0x6f0e7301cfb9304e 0xdbc39cc073ee4c13

def z461 : W := mkw 0x858fb768c9bf7a49 0x6163edda326fde92 0x7f0ff3e9cfbf3a4f 0xdfc3fcfa73efce93

def z462 : W := mkw 0x00f958b163e58c62 0x403e562c58f96318 0xfffffcf1f3ffcc73 0xffffff3c7cfff31c

def z463 : W := mkw 0x4000850214025094 0x1000214085009425 0x00000c003000c030 0x000003000c00300c

def z464 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xf9fffffffc000ffd 0xfe7fffffff0003ff

def z465 : W := mkw 0xc006a74a9c1a729d 0x3001a9d2a7069ca7 0xab0f8f1e3c7fffff 0xeac3e3c78f1fffff

def z466 : W := mkw 0x4000850214025094 0x1000214085009425 0xa2018c1e3046cfb3 0x688063078c11b3ec

def z467 : W := mkw 0x0004320001112000 0x00010c8000444800 0x450e700003b80000 0x11439c0000ee0000

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x280003080c000001 0xca0000c203000000

def z469 : W := mkw 0x09ffffdfbf418000 0x027ffff7efd06000 0xfdffffffffc1c003 0xff7ffffffff07000

def z470 : W := mkw 0x0000002000880a01 0x0000000800220280 0x0600000003b80a02 0x0180000000ee0280

def z471 : W := mkw 0x041432000377f000 0x01050c8000ddfc00 0x670e730003fff002 0xd9c39cc000fffc00

def z472 : W := mkw 0x0050dd000343d000 0x0014374000d0f400 0xe6f1ff0003c7f002 0xf9bc7fc000f1fc00

def z473 : W := mkw 0x8210102043fd2f4b 0xe084040810ff4bd2 0x0600000003ff3fce 0x0180000000ffcff3

def z474 : W := mkw 0x0000850000025000 0x0000214000009400 0xaa018f103047fc73 0xea8063c40c11ff1c

def z475 : W := mkw 0x0dddff03bf77f000 0x03777fc0efddfc00 0xefffff01fffff002 0xfbffffc07ffffc00

def z476 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xfbfffffffc47f003 0xfeffffffff11fc00

def z477 : W := mkw 0x458da70214367094 0x116369c0850d9c25 0xab0f8f1e3c7fffff 0xeac3e3c78f1fffff

def z478 : W := mkw 0xc004b702dd1370dc 0x70012dc0b744dc37 0x08007f01fc01f07c 0x82001fc07f007c1f

def z479 : W := mkw 0x05d9dd000377f000 0x0176774000ddfc00 0x86f18c0003fff002 0x21bc630000fffc00

def z480 : W := mkw 0x82163268cbfd2f4b 0xe0858c9a32ff4bd2 0x7f0e73e9cfff3fcf 0xdfc39cfa73ffcff3

def z481 : W := mkw 0x087258ffffc18c62 0x421c963ffff06318 0xfcf07cffffc1cc73 0xbf3c1f3ffff0731c

def z482 : W := mkw 0x007048b122c08c22 0x001c122c48b02308 0xf4f00cf033c0cc33 0x3d3c033c0cf0330c

def z483 : W := mkw 0x05fdff912377f000 0x017f7fe448ddfc00 0xfffffff1f3fff003 0xfffffffc7cfffc00

def z484 : W := mkw 0x0b8fa74e9c2c0301 0x82e3e9d3a70b00c0 0x030f830e0c3e0380 0x40c3e0c3830f80e0

def z485 : W := mkw 0x0dffefdfbe66d000 0x037ffbf7ef99b400 0xf9fffffffc46c001 0xfe7fffffff11b000

def z486 : W := mkw 0x0040580161018060 0x4010160058406018 0x00007001c0000000 0x00001c0070000000

def z487 : W := mkw 0x01cfef4888000000 0x0073fbd222000000 0xf9ffffe9cc000001 0xfe7ffffa73000000

def z488 : W := mkw 0x8000102041992a49 0x6000040810664a92 0x7e0070e1c3b93a4f 0x9f801c3870ee4e93

def z489 : W := mkw 0x0000000214000000 0x0000000085000000 0x0800001e3c000001 0x020000078f000000

def z490 : W := mkw 0x0000850214000000 0x0000214085000000 0x80018c1630000000 0x200063058c000000

def z491 : W := mkw 0x882200fffc880a49 0x6208803fff220292 0x180000fffc000a4d 0x0600003fff000293

def z492 : W := mkw 0x82bf32fccbfd2f4b 0xe0afccbf32ff4bd2 0xf7fff0ffc3fe0f83 0x7dfffc3ff0ff83e0

def z493 : W := mkw 0x0070589123418000 0x001c162448d06000 0xfcf07cf1f3c1c003 0xbf3c1f3c7cf07000

def z494 : W := mkw 0x02b9009402640502 0x80ae402500990140 0xe7ff801603fe0582 0x79ffe00580ff8160

def z495 : W := mkw 0x428b854e142e5395 0x90a2e153850b94e5 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z496 : W := mkw 0x80567a68cbd9aa49 0x60159e9a32f66a92 0xfffe7fe9cff9fa4f 0xffff9ffa73fe7e93

def z497 : W := mkw 0x0000850214000000 0x0000214085000000 0x0001830e0c000000 0x400060c383000000

def z498 : W := mkw 0x85dfff488b7ff209 0x2177ffd222dffc82 0xe7ffff080ffff20e 0xf9ffffc203fffc83

def z499 : W := mkw 0x80767af9ebd9ae6b 0x601d9ebe7af66b9a 0xfdfe7cf1f3f9cc73 0xbf7f9f3c7cfe731c

def z500 : W := mkw 0x4000000214025094 0x1000000085009425 0x0a00001e3c47ffff 0x028000078f11ffff

def z501 : W := mkw 0x003000b002c00c02 0x000c002c00b00300 0xf6f180fe03c60f83 0x7dbc603f80f183e0

def z502 : W := mkw 0xc006b76add9b7add 0x7001addab766deb7 0x7f0e7fe9ffb9fa7f 0xdfc39ffa7fee7e9f

def z503 : W := mkw 0x0400000000367000 0x01000000000d9c00 0x02000000003e3000 0x00800000000f8c00

def z504 : W := mkw 0xc006326add992add 0x70018c9ab7664ab7 0x7f0e73ffffb93fff 0xdfc39cffffee4fff

def z505 : W := mkw 0x07ddff2003ffff03 0x81f77fc800ffffc0 0xe7ffff0003ffff82 0xf9ffffc000ffffe0

def z506 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x570e70e1c3b93a4e 0x15c39c3870ee4e93

def z507 : W := mkw 0x4050dd021743d094 0x1014374085d0f425 0xeef1ff1e3fc7ffff 0xfbbc7fc78ff1ffff

def z508 : W := mkw 0x023000b002ec0f03 0x808c002c00bb03c0 0xf6f000f003fe0f83 0x3dbc003c00ff83e0

def z509 : W := mkw 0x8006b768c99b7a49 0x6001adda3266de92 0xff0fffe9cffffa4f 0xffc3fffa73fffe93

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x2200030000013002 0xc88000c000004c00

def z511 : W := mkw 0x09ffffffffc18c62 0x427ffffffff06318 0xfdffffffff800001 0xff7fffffffe00000

def z512 : W := mkw 0x0000850000025000 0x0000214000009400 0x00000f000001f000 0x800003c000007c00

def z513 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff8cfe33ffcff3 0xffffe33f8cfff3fc

def z514 : W := mkw 0x0802004e9c000000 0x02008013a7000000 0x0000000e0c000000 0x0000000383000000

def z515 : W := mkw 0x4000850214025094 0x1000214085009425 0xaa018f1e3c06338d 0xea8063c78f018ce3

def z516 : W := mkw 0x42fbddff77efdff7 0xd0bef77fddfbf7fd 0xffffffffffffffff 0xffffffffffffffff

def z517 : W := mkw 0x09ffefdfbe408422 0x027ffbf7ef902108 0xf9fffffffc40c431 0xfe7fffffff10310c

def z518 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x5d0e70e9cfb80a4d 0x17439c3a73ee0293

def z519 : W := mkw 0x85dfff68cbfffa49 0x6177ffda32fffe92 0xf7ffffe1c3fff002 0xfdfffff870fffc00

def z520 : W := mkw 0x0050580163418060 0x4014160058d06018 0xecf07c01f3c1c072 0xbb3c1f007cf0701c

def z521 : W := mkw 0x0974ffb3ffc18c62 0x425d3fecfff06318 0xfcf07ff1ffc1cc73 0xbf3c1ffc7ff0731c

def z522 : W := mkw 0x07ff7afc03fdaf03 0x81ffdebf00ff6bc0 0xf7fff0fe03fe0f83 0x7dfffc3f80ff83e0

def z523 : W := mkw 0x0050580003418000 0x0014160000d06000 0xecf07c1033c1cc73 0xbb3c1f040cf0731c

def z524 : W := mkw 0x05d9cd000266d000 0x017673400099b400 0xa2f18f000047f002 0xe8bc63c00011fc00

def z525 : W := mkw 0x0df9cd973666d000 0x037e7365cd99b400 0x80f18c163046c000 0x203c63058c11b000

def z526 : W := mkw 0x0989850614000000 0x0262614185000000 0x0001800600000000 0x0000600180000000

def z527 : W := mkw 0x01c9cd0000000000 0x0072734000000000 0x80f18c0000000000 0x203c630000000000

def z528 : W := mkw 0x4000850214025094 0x1000214085009425 0xa8018f1e3c46c5b1 0xea0063c78f11b16c

def z529 : W := mkw 0x858fa748883e7209 0x2163e9d2220f9c82 0x030f83080c3e320c 0x40c3e0c2030f8c83

def z530 : W := mkw 0x09afa7de9c000000 0x026be9f7a7000000 0xf1ff83fe0c000001 0x7c7fe0ff83000000

def z531 : W := mkw 0x01edef9120000000 0x007b7be448000000 0xf9fffff1f0000001 0xfe7ffffc7c000000

def z532 : W := mkw 0x4010102043c3dcf6 0x5004040810f0f73d 0x0600000003c7fffe 0x0180000000f1ffff

def z533 : W := mkw 0x0944ef03bc000000 0x02513bc0ef000000 0xa801ff1ffc000001 0xea007fc7ff000000

def z534 : W := mkw 0x028b004c002c0301 0x80a2c013000b00c0 0x010e000000380000 0x00438000000e0000

def z535 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf9fe7cf1f0000001 0xbe7f9f3c7c000000

def z536 : W := mkw 0x0002006800880a01 0x0000801a00220280 0xf70f80fe03fe0f83 0x7dc3e03f80ff83e0

def z537 : W := mkw 0x0006226888880a01 0x0001889a22220280 0x7f0e73e9cfb80a03 0xdfc39cfa73ee0280

def z538 : W := mkw 0x82bb10fc43fd2f4b 0xe0aec43f10ff4bd2 0xf7ff80fe03ff3fcf 0x7dffe03f80ffcff3

def z539 : W := mkw 0x008b004c00000000 0x0022c01300000000 0x010f800e00000000 0x4043e00380000000

def z540 : W := mkw 0x0099000002640000 0x0026400000990000 0x45fe000003b80000 0x117f800000ee0000

def z541 : W := mkw 0x80020068c8880a49 0x6000801a32220292 0x100000e1c0000000 0x0400003870000000

def z542 : W := mkw 0x0bbfa7fe9eec0f03 0x82efe9ffa7bb03c0 0xf7ff83fe0ffe0f83 0x7dffe0ff83ff83e0

def z543 : W := mkw 0x0000850000000000 0x0000214000000000 0xa0018f0000000000 0xe80063c000000000

def z544 : W := mkw 0x0070489122408422 0x001c122448902108 0xa8f00c103041cc73 0xaa3c03040c10731c

def z545 : W := mkw 0x4000850214025094 0x1000214085009425 0xa8018c163047cdf3 0xaa0063058c11f37c

def z546 : W := mkw 0x42bb00fe16ec0f97 0x90aec03f85bb03e5 0xffff80fe3ffe0fff 0x7fffe03f8fff83ff

def z547 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x59fe7fe1fc000000 0x967f9ff87f000000

def z548 : W := mkw 0x0000850214025000 0x0000214085009400 0xaa018f1e3c47f003 0xea8063c78f11fc00

def z549 : W := mkw 0x4000850214025094 0x1000214085009425 0x000003000c00300c 0x000000c003000c03

def z550 : W := mkw 0x05cdff000113f000 0x01737fc00044fc00 0xe1ffff000001f000 0xf87fffc000007c00

def z551 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc460f83 0xfeffffffff1183e0

def z552 : W := mkw 0x00ab00dc00000000 0x002ac03700000000 0xf3ff80fe00460f83 0x7cffe03f801183e0

def z553 : W := mkw 0x0006a74a9c000000 0x0001a9d2a7000000 0xf90ffffffc000001 0xfe43ffffff000000

def z554 : W := mkw 0x4000850214025094 0x1000214085009425 0xa201831e0c463f8f 0x688060c783118fe3

def z555 : W := mkw 0x80043220c9992a49 0x60010c8832664a92 0x0e007301cfb93a4e 0x83801cc073ee4e93

def z556 : W := mkw 0x006048b160800c62 0x4018122c58200318 0xf8f07cf1f0000c71 0xbe3c1f3c7c00031c

def z557 : W := mkw 0x0904a7029c000000 0x024129c0a7000000 0x000003000c000000 0x000000c003000000

def z558 : W := mkw 0x828f224c883c2309 0xa0a3c893220f08c2 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z559 : W := mkw 0x09f9cd9736408422 0x027e7365cd902108 0x80f18c163040c430 0x203c63058c10310c

def z560 : W := mkw 0x0000850214000000 0x0000214085000000 0x08000f003c000000 0x820003c00f000000

def z561 : W := mkw 0xc9effffffd9b7add 0x727bffffff66deb7 0xffffffffffffffff 0xffffffffffffffff

def z562 : W := mkw 0x828f326cc9bd2b49 0xe0a3cc9b326f4ad2 0x7f0ff3efcfbf3bcf 0xdfc3fcfbf3efcef3

def z563 : W := mkw 0x0504a70000127000 0x014129c000049c00 0x0000030000003000 0x000000c000000c00

def z564 : W := mkw 0x0a2200ffbc880f03 0x8288803fef2203c0 0x180000fffc000f81 0x0600003fff0003e0

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0x080003000c01304c 0x820000c003004c13

def z566 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80e003fe0002 0x7dffe03800ff8000

def z567 : W := mkw 0x0010000002640000 0x0004000000990000 0x0600000003fe0002 0x0180000000ff8000

def z568 : W := mkw 0x0004320001112000 0x00010c8000444800 0x0000730000013000 0x80001cc000004c00

def z569 : W := mkw 0x4000850000025094 0x1000214000009425 0xa2018f000047fffe 0xe88063c00011ffff

def z570 : W := mkw 0x02bb00dc02640502 0x80aec03700990140 0xf1ff80fe00460581 0x7c7fe03f80118160

def z571 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc013a4f 0xfeffffffff004e93

def z572 : W := mkw 0x8006224888182209 0x2001889222060882 0x2b0e03080c393a4f 0xcac380c2030e4e93

def z573 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7d0e70e1c3b90843 0x9f439c3870ee4210

def z574 : W := mkw 0x028b004c002c0301 0x80a2c013000b00c0 0xa30f801e007e0f83 0x68c3e007801f83e0

def z575 : W := mkw 0x42b9859616665596 0x90ae616585999565 0x80f18c163046c5b0 0x203c63058c11b16c

def z576 : W := mkw 0x0dffffdfbf75a000 0x037ffff7efdd6800 0xfdffffffffb80001 0xff7fffffffee0000

def z577 : W := mkw 0x0212006802ec0f03 0x8084801a00bb03c0 0x770e00e803fe0f83 0x5dc3803a00ff83e0

def z578 : W := mkw 0x0000850214000000 0x0000214085000000 0xaa018f1e3c013a4f 0xea8063c78f004e93

def z579 : W := mkw 0x05dfff6803fffa01 0x0177ffda00fffe80 0xf7ffffe803fffa03 0xfdfffffa00fffe80

def z580 : W := mkw 0x42bb85fe16ee5f97 0x90aee17f85bb97e5 0xf7ff8cfe33fecfb3 0x7dffe33f8cffb3ec

def z581 : W := mkw 0x05ddff016377f060 0x41777fc058ddfc18 0xefffff01f3fff072 0xfbffffc07cfffc1c

def z582 : W := mkw 0x041010000375a000 0x0104040000dd6800 0x0400000003b80000 0x0100000000ee0000

def z583 : W := mkw 0x0210000002640502 0x8084000000990140 0x0000000000460580 0x0000000000118160

def z584 : W := mkw 0x082285dfbc000000 0x0208a177ef000000 0xb8018ffffc000001 0xee0063ffff000000

def z585 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0e7ff9fff9fe7f 0xffc39ffe7ffe7f9f

def z586 : W := mkw 0x01ddff0003418000 0x00777fc000d06000 0xe5ffff0003c1c002 0xf97fffc000f07000

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000000460f82 0x00800000001183e0

def z588 : W := mkw 0x07dfff4c037ff301 0x81f7ffd300dffcc0 0xe7ffff0e03fff382 0xf9ffffc380fffce0

def z589 : W := mkw 0x02000000002c0301 0x80800000000b00c0 0x02000000003e0380 0x00800000000f80e0

def z590 : W := mkw 0xc004b702dd1370dc 0x70012dc0b744dc37 0xaa01ff1ffc47ffff 0xea807fc7ff11ffff

def z591 : W := mkw 0x0040580161018060 0x4010160058406018 0xa8007c11f041cc73 0xaa001f047c10731c

def z592 : W := mkw 0x0040480120008020 0x0010120048002008 0x00000c003000c030 0x000003000c00300c

def z593 : W := mkw 0x402000b374800cf6 0x5008002cdd20033d 0x180000fffc000ffd 0x0600003fff0003ff

def z594 : W := mkw 0x0554ff000377f000 0x01553fc000ddfc00 0x06007f0003fff002 0x81801fc000fffc00

def z595 : W := mkw 0x0544ff016113f060 0x41513fc05844fc18 0x08007f01f001f070 0x82001fc07c007c1c

def z596 : W := mkw 0x80020068c8880a49 0x6000801a32220292 0x7f0e00e9cfb80a4f 0x5fc3803a73ee0293

def z597 : W := mkw 0x02f9489522648522 0x80be522548992148 0x80f18c163046c5b0 0x203c63058c11b16c

def z598 : W := mkw 0x00fb58fd63c18c62 0x403ed63f58f06318 0xfdfffcfff3c1cc73 0xff7fff3ffcf0731c

def z599 : W := mkw 0x02bb00dc026c0703 0x80aec037009b01c0 0x83ff801e007e0780 0x60ffe007801f81e0

def z600 : W := mkw 0x4004b70215137094 0x10012dc08544dc25 0xef0fff1e3fffffff 0xfbc3ffc78fffffff

def z601 : W := mkw 0x8944ff03fd112048 0x62513fc0ff444812 0x08007f01fc01304c 0x82001fc07f004c13

def z602 : W := mkw 0x89ffffffffd9ae6b 0x627ffffffff66b9a 0xfffffffffff9fe7f 0xfffffffffffe7f9f

def z603 : W := mkw 0x0dfdff973777f000 0x037f7fe5cdddfc00 0xe7ffff1633fff002 0xf9ffffc58cfffc00

def z604 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff003ffff07e 0xfbffffc00ffffc1f

def z605 : W := mkw 0x8000002040880a49 0x6000000810220292 0x0000000000000a4c 0x0000000000000293

def z606 : W := mkw 0x09ffefffbec00c02 0x027ffbffefb00300 0xfdffffffffc00c03 0xff7ffffffff00300

def z607 : W := mkw 0x059da70002767000 0x016769c0009d9c00 0xe7ff830003fe3002 0x79ffe0c000ff8c00

def z608 : W := mkw 0x0d8fa74e9c367000 0x0363e9d3a70d9c00 0x030f830e0c3e3000 0x40c3e0c3830f8c00

def z609 : W := mkw 0x482285dfbc025094 0x1208a177ef009425 0xba018ffffc47ffff 0xee8063ffff11ffff

def z610 : W := mkw 0x0099000002640000 0x0026400000990000 0x80f1800000460000 0x203c600000118000

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x0201800e00060380 0x40806003800180e0

def z612 : W := mkw 0x4070ddb377c3dcf6 0x501c376cddf0f73d 0xfcf07ff1ffc1fc7f 0xbf3c1ffc7ff07f1f

def z613 : W := mkw 0x41cdef0214025094 0x10737bc085009425 0xebffff1e3c47ffff 0xfaffffc78f11ffff

def z614 : W := mkw 0x02fb58fc03ed8f03 0x80bed63f00fb63c0 0xf7fffcfe03ffcf83 0xfdffff3f80fff3e0

def z615 : W := mkw 0x4000850214025094 0x1000214085009425 0x2a000f083c01fa7f 0xca8003c20f007e9f

def z616 : W := mkw 0x006058b161810840 0x4018162c58604210 0xfcf07cf1f3810843 0xbf3c1f3c7ce04210

def z617 : W := mkw 0x8946ff6bfd992a49 0x6251bfdaff664a92 0x7f0e7fe9ffb93a4f 0xdfc39ffa7fee4e93

def z618 : W := mkw 0x0040582161818860 0x4010160858606218 0x7c007ce1f381c873 0x9f001f387ce0721c

def z619 : W := mkw 0x407058b377c18cf6 0x501c162cddf0633d 0xfcf07cffffc1cfff 0xbf3c1f3ffff073ff

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0xa201800000460002 0x6880600000118000

def z621 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x81ff8f1e3c000000 0x607fe3c78f000000

def z622 : W := mkw 0x0299002002ec0f03 0x80a6400800bb03c0 0xe7ff800003fe0f82 0x79ffe00000ff83e0

def z623 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7d0e73e9cfb80001 0xdf439cfa73ee0000

def z624 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x180073e9cc013a4d 0x86001cfa73004e93

def z625 : W := mkw 0x00ab85de14000000 0x002ae17785000000 0xf9ff8ffe3c000001 0xfe7fe3ff8f000000

def z626 : W := mkw 0x4000850214025094 0x1000214085009425 0x2a01830e0c073bcf 0xca8060c38301cef3

def z627 : W := mkw 0xc2bfb7fedfff7fdf 0xf0afedffb7ffdff7 0xffffffffffffffff 0xffffffffffffffff

def z628 : W := mkw 0x4000000214000094 0x1000000085000025 0x00000016300005b0 0x000000058c00016c

def z629 : W := mkw 0x0006224888000000 0x0001889222000000 0x7b0e73e9cc013a4f 0xdec39cfa73004e93

def z630 : W := mkw 0x003000b002c00c02 0x000c002c00b00300 0x54f000e003800000 0x153c003800e00000

def z631 : W := mkw 0x8004322041992a49 0x60010c8810664a92 0x670e730003b93a4e 0xd9c39cc000ee4e93

def z632 : W := mkw 0x09cfef4e9c000000 0x0273fbd3a7000000 0xe1ffff0e0c000000 0xf87fffc383000000

def z633 : W := mkw 0x098fa74e9c000000 0x0263e9d3a7000000 0x790ff3efcc000001 0xde43fcfbf3000000

def z634 : W := mkw 0x89efffdffd112048 0x627bfff7ff444812 0xf9fffffffc01304d 0xfe7fffffff004c13

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x2200000800000a03 0x4880000200000280

def z636 : W := mkw 0x023200fc02c80f03 0x808c803f00b203c0 0xf4f000fe03c00f83 0x3d3c003f80f003e0

def z637 : W := mkw 0x05ddef000276f000 0x01777bc0009dbc00 0x83ff8f00007ef000 0x60ffe3c0001fbc00

def z638 : W := mkw 0x02f958b563e58d62 0xc0be562d58f96358 0xfcf1fcf7f3c7cdf3 0xbf3c7f3dfcf1f37c

def z639 : W := mkw 0x84163268cbfffa49 0x61058c9a32fffe92 0x7f0e73e9cffffa4f 0xdfc39cfa73fffe93

def z640 : W := mkw 0x09efffdffd018060 0x427bfff7ff406018 0xf9fffffffc01c071 0xfe7fffffff00701c

def z641 : W := mkw 0x07fdff940377f502 0x81ff7fe500ddfd40 0xe7ffff1603fff582 0xf9ffffc580fffd60

def z642 : W := mkw 0x041000000266d000 0x010400000099b400 0x000000000046c000 0x000000000011b000

def z643 : W := mkw 0x05fdff912377f422 0x017f7fe448ddfd08 0xe7ffff1033fff432 0xf9ffffc40cfffd0c

def z644 : W := mkw 0x802632f9e9992e6b 0x60098cbe7a664b9a 0x7f0e73f9ffb93e7f 0xdfc39cfe7fee4f9f

def z645 : W := mkw 0x4000000214000094 0x1000000085000025 0x0000000e0c00038c 0x00000003830000e3

def z646 : W := mkw 0x09ebcddf34000000 0x027af377cd000000 0xf1ff8cfe30000001 0x7c7fe33f8c000000

def z647 : W := mkw 0x80000000c8000048 0x6000000032000012 0x08000001cc00004c 0x0200000073000013

def z648 : W := mkw 0x4000850214000094 0x1000214085000025 0xa8018f1e3c000ffd 0xea0063c78f0003ff

def z649 : W := mkw 0xc076fffbffdbfeff 0x701dbffefff6ffbf 0xffffffffffffffff 0xffffffffffffffff

def z650 : W := mkw 0x4000850214025094 0x1000214085009425 0x82018f1e3c46f7bc 0x608063c78f11bdef

def z651 : W := mkw 0x8544ff00c913f048 0x61513fc03244fc12 0x08007f01cc01f04c 0x82001fc073007c13

def z652 : W := mkw 0x4210002002ee5f97 0x9084000800bb97e5 0x0600000003fffffe 0x0180000000ffffff

def z653 : W := mkw 0x0002006800880a01 0x0000801a00220280 0x550e00e003b80000 0x1543803800ee0000

def z654 : W := mkw 0x49e9cd9734025094 0x127a7365cd009425 0x80f18c163046c5b0 0x203c63058c11b16c

def z655 : W := mkw 0x0006324889112000 0x00018c9222444800 0x7f0e73e9cfb93003 0xdfc39cfa73ee4c00

def z656 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x55fe00fe03b80f81 0x157f803f80ee03e0

def z657 : W := mkw 0x4000850214025094 0x1000214085009425 0x0a000f003c47fffe 0x828003c00f11ffff

def z658 : W := mkw 0x05cdef0000367000 0x01737bc0000d9c00 0xe3ffff00003e3000 0xf8ffffc0000f8c00

def z659 : W := mkw 0x0030009002400402 0x000c002400900100 0x80f0001000400400 0x203c000400100100

def z660 : W := mkw 0x4000850214025094 0x1000214085009425 0x0a018f0e3c07f3fc 0xc28063c38f01fcff

def z661 : W := mkw 0x42bb85fe16ee5f97 0x90aee17f85bb97e5 0xf7ff83fe0ffe3f8f 0x7dffe0ff83ff8fe3

def z662 : W := mkw 0x4000850214025094 0x1000214085009425 0x82018c163047fffe 0x208063058c11ffff

def z663 : W := mkw 0x0000100001112000 0x0000040000444800 0x0600000003b93002 0x0180000000ee4c00

def z664 : W := mkw 0x0000850214000000 0x0000214085000000 0xa8018f1e3c41cc73 0xea0063c78f10731c

def z665 : W := mkw 0x4000850214025094 0x1000214085009425 0xa8000f103c41fc7f 0xaa0003c40f107f1f

def z666 : W := mkw 0x882632fffd992a49 0x62098cbfff664a92 0x7f0e73ffffb93a4f 0xdfc39cffffee4e93

def z667 : W := mkw 0x0006326801992a01 0x00018c9a00664a80 0x770e73e803b93a03 0xddc39cfa00ee4e80

def z668 : W := mkw 0x0940cd0334000000 0x02503340cd000000 0x00000c0030000000 0x000003000c000000

def z669 : W := mkw 0x02b900b402e40d02 0x80ae402d00b90340 0xf4f180f603c60d83 0x3d3c603d80f18360

def z670 : W := mkw 0x8546ff68c99bfa49 0x6151bfda3266fe92 0x7f0e7fe9cfb9fa4f 0xdfc39ffa73ee7e93

def z671 : W := mkw 0x4000850214025094 0x1000214085009425 0xa8018f1e3c01f07d 0xea0063c78f007c1f

def z672 : W := mkw 0x00bb00dc02640000 0x002ec03700990000 0xf7ff80fe03fe0003 0x7dffe03f80ff8000

def z673 : W := mkw 0x0ddfff4e9f77f000 0x0377ffd3a7ddfc00 0xe7ffff0e0ffff002 0xf9ffffc383fffc00

def z674 : W := mkw 0x0000102041810840 0x4000040810604210 0x540070e1c3800000 0x15001c3870e00000

def z675 : W := mkw 0x09ff7afdebc18c62 0x427fdebf7af06318 0x55fe70e1c3800000 0x157f9c3870e00000

def z676 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x770e73e1c3b93002 0xddc39cf870ee4c00

def z677 : W := mkw 0x0bffefffbeec0f03 0x82fffbffefbb03c0 0xfdffffffffb80001 0xff7fffffffee0000

def z678 : W := mkw 0x42b9859616665596 0x90ae616585999565 0xaaf18f1e3c47ffff 0xeabc63c78f11ffff

def z679 : W := mkw 0xc0009522559b7add 0x700025489566deb7 0xae018f1e3fffffff 0xeb8063c78fffffff

def z680 : W := mkw 0x02fb58fd63ed8f63 0xc0bed63f58fb63d8 0xf7fff0ffc3fe0f83 0x7dfffc3ff0ff83e0

def z681 : W := mkw 0x0004b70001137000 0x00012dc00044dc00 0xe70fff0003fff002 0xf9c3ffc000fffc00

def z682 : W := mkw 0x082200fffc800c62 0x4208803fff200318 0x180000fffc000c71 0x0600003fff00031c

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000080c000a4d 0x0200000203000293

def z684 : W := mkw 0x89effffffd992a49 0x627bffffff664a92 0xfdffffffffb80001 0xff7fffffffee0000

def z685 : W := mkw 0x05fdffb003f7fc02 0x017f7fec00fdff00 0xf7fffff003fffc03 0xfdfffffc00ffff00

def z686 : W := mkw 0x09afa7dfbc000000 0x026be9f7ef000000 0x190f83fffc000001 0x4643e0ffff000000

def z687 : W := mkw 0x0544ff000113f000 0x01513fc00044fc00 0x670e7f0003b9f002 0xd9c39fc000ee7c00

def z688 : W := mkw 0x0004220000102000 0x0001088000040800 0x030e030000383000 0x40c380c0000e0c00

def z689 : W := mkw 0x003010b043c10c42 0x400c042c10f04310 0xfcf070f1c3c10c43 0xbf3c1c3c70f04310

def z690 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x7c0070e1c3c1cc73 0x9f001c3870f0731c

def z691 : W := mkw 0x018da70000000000 0x006369c000000000 0x010f830000000000 0x4043e0c000000000

def z692 : W := mkw 0x009b006802ec0a01 0x0026c01a00bb0280 0xf7ff80e803fe0a03 0x7dffe03a00ff8280

def z693 : W := mkw 0x0002004888000000 0x0000801222000000 0x180000e9cc000001 0x0600003a73000000

def z694 : W := mkw 0x05ddff2043f7f840 0x41777fc810fdfe10 0xffffffe1c3fff843 0xfffffff870fffe10

def z695 : W := mkw 0x05d9dd000367d000 0x0176774000d9f400 0xe4f1fc0003c7c002 0xb93c7f0000f1f000

def z696 : W := mkw 0x428b854e142e5395 0x90a2e153850b94e5 0xab0f8f1e3c7fffff 0xeac3e3c78f1fffff

def z697 : W := mkw 0x402085b374825cf6 0x5008216cdd20973d 0xba018ffffc47ffff 0xee8063ffff11ffff

def z698 : W := mkw 0x05f9cd912266d422 0x017e73644899b508 0x80f18c103046c430 0x203c63040c11b10c

def z699 : W := mkw 0x09ebcddfbc000000 0x027af377ef000000 0x98f18cfffc000001 0x263c633fff000000

def z700 : W := mkw 0x4544ff021513f094 0x11513fc08544fc25 0xaa01ff1e3c47ffff 0xea807fc78f11ffff

def z701 : W := mkw 0x023200fc02ec0f03 0x808c803f00bb03c0 0x160000fe03fe0f83 0x0580003f80ff83e0

def z702 : W := mkw 0x0d44ff03bd13f000 0x03513fc0ef44fc00 0x08007f01fc01f000 0x82001fc07f007c00

def z703 : W := mkw 0x02bf22fc8aec0f03 0x80afc8bf22bb03c0 0xfffff3ffcffe0f83 0xfffffcfff3ff83e0

def z704 : W := mkw 0x4000850214025094 0x1000214085009425 0x88018f163c47f5fc 0xa20063c58f11fd7f

def z705 : W := mkw 0x0004322041912840 0x40010c8810644a10 0x7f0e73e1c3b93843 0xdfc39cf870ee4e10

def z706 : W := mkw 0x0000850000025000 0x0000214000009400 0x80018c000046c000 0x200063000011b000

def z707 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0x51fff3e1c0000000 0x547ffcf870000000

def z708 : W := mkw 0x0099850002640000 0x0026614000990000 0xe7ff8f0003fe0002 0xf9ffe3c000ff8000

def z709 : W := mkw 0x4410102043f7fcf6 0x5104040810fdff3d 0x0600000003fffffe 0x0180000000ffffff

def z710 : W := mkw 0x0dddff01ab77f000 0x03777fc06addfc00 0xe7ffff01c3fff002 0xf9ffffc070fffc00

def z711 : W := mkw 0x8410102043fdaa49 0x6104040810ff6a92 0x0600000003b93a4e 0x0180000000ee4e93

def z712 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc000a03 0xfeffffffff000280

def z713 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff8c0003ffc002 0xf9ffe30000fff000

def z714 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0x47fe700003be3000 0x11ff9c0000ef8c00

def z715 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07cfff3c1cff3 0xbf3c1f3ffcf073fc

def z716 : W := mkw 0x022200fc88880f03 0x8088803f222203c0 0x180000ffcc000f81 0x0600003ff30003e0

def z717 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0x59fe70e1fc000000 0x167f9c387f000000

def z718 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7fffc0003fec002 0x79ffff0000ffb000

def z719 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f040c431 0xbe3c1f3c7c10310c

def z720 : W := mkw 0x4070ddb377c3dcf6 0x501c376cddf0f73d 0x56f1f3efcf86338c 0x55bc7cfbf3e18ce3

def z721 : W := mkw 0x0befefdfbc240100 0x82fbfbf7ef090040 0xf9fffffffc060181 0xfe7fffffff018060

def z722 : W := mkw 0x486248dfbc000094 0x12189237ef000025 0xf8f07cfffc41cfff 0xbe3c1f3fff1073ff

def z723 : W := mkw 0x0010102043c18840 0x4004040810f06210 0x0400000003c1c842 0x0100000000f07210

def z724 : W := mkw 0x006248dd20000000 0x0018923748000000 0xf8f07cfff0000001 0xbe3c1f3ffc000000

def z725 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x57ff80ee03fe0f82 0x55ffe03b80ff83e0

def z726 : W := mkw 0x00af22dc88000000 0x002bc8b722000000 0xfbfff3ffcc473fcf 0xfefffcfff311cff3

def z727 : W := mkw 0x00af22dc88000000 0x002bc8b722000000 0x79fe73e9cc000001 0xde7f9cfa73000000

def z728 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff8cfe33fe0f83 0xffffe33f8cff83e0

def z729 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0xa4000c0003c1cc72 0xa900030000f0731c

def z730 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef1fcf1f3c7cc73 0xffbc7f3c7cf1f31c

def z731 : W := mkw 0x807058b163d9ae6b 0x601c162c58f66b9a 0xfef07ff9fff9fe7f 0xffbc1ffe7ffe7f9f

def z732 : W := mkw 0x01cfef4888000000 0x0073fbd222000000 0xf1ffffe1c0000000 0xfc7ffff870000000

def z733 : W := mkw 0x05ddff008b77f000 0x01777fc022ddfc00 0xefffff01cffff002 0xfbffffc073fffc00

def z734 : W := mkw 0x0004322041912840 0x40010c8810644a10 0x7f0e73e9cfb93a4f 0xdfc39cfa73ee4e93

def z735 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xefffff1033ffffff 0xfbffffc40cffffff

def z736 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe7fff01e03fe0f83 0x79fffc0780ff83e0

def z737 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0x45fff30003b80000 0x517ffcc000ee0000

def z738 : W := mkw 0x027058b163ed8f63 0xc09c162c58fb63d8 0xfef1fcfff3ffcff3 0xffbc7f3ffcfff3fc

def z739 : W := mkw 0x02bb00dc02640502 0x80aec03700990140 0xf7ff80fe03fe0583 0x7dffe03f80ff8160

def z740 : W := mkw 0x08eb48dfbc000000 0x023ad237ef000000 0xf9fffcfffc000001 0xfe7fff3fff000000

def z741 : W := mkw 0x822632fcc9992f4b 0xe0898cbf32664bd2 0x180073ffcc013fcd 0x86001cfff3004ff3

def z742 : W := mkw 0x8210102043fd2f4b 0xe084040810ff4bd2 0xae01831e0fff3fcf 0xeb8060c783ffcff3

def z743 : W := mkw 0x827058b163fdaf6b 0xe09c162c58ff6bda 0xfef07cf1f3ffffff 0xbfbc1f3c7cffffff

def z744 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc46cffd 0xfe7fffffff11b3ff

def z745 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x47ffff0003bff000 0xd1ffffc000effc00

def z746 : W := mkw 0x802200f9e8880e6b 0x6008803e7a22039a 0x100000e1c0000000 0x0400003870000000

def z747 : W := mkw 0x0766fffc019bff03 0x81d9bfff0066ffc0 0x10007ffe0001ff81 0x84001fff80007fe0

def z748 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff1e3ffff07f 0xfbffffc78ffffc1f

def z749 : W := mkw 0x0002106841890a41 0x4000841a10624290 0x7f0e73e9cfb93a4f 0xdfc39cfa73ee4e93

def z750 : W := mkw 0x807058b163d1ac6a 0x601c162c58f46b1a 0xfcf07cf1f3c1fc7f 0xbf3c1f3c7cf07f1f

def z751 : W := mkw 0x0060489120000000 0x0018122448000000 0xd0f07cf1f0000000 0x343c1f3c7c000000

def z752 : W := mkw 0x0210102043ed8f63 0xc084040810fb63d8 0x0600000003fe0f82 0x0180000000ff83e0

def z753 : W := mkw 0x059db72043f7fc62 0x41676dc810fdff18 0x070f830003fffc72 0x41c3e0c000ffff1c

def z754 : W := mkw 0x41edef9334025094 0x107b7be4cd009425 0xfbfffffffc47ffff 0xfeffffffff11ffff

def z755 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73e9cfff3fcf 0xdfc39cfa73ffcff3

def z756 : W := mkw 0x01efefd9a8000000 0x007bfbf66a000000 0xf9fffff9fc000001 0xfe7ffffe7f000000

def z757 : W := mkw 0x0abb00fdaaec0f03 0x82aec03f6abb03c0 0xf7ff80ffc3fe0f83 0x7dffe03ff0ff83e0

def z758 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe5fe700003f80002 0x397f9c0000fe0000

def z759 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x570e73e9cfb93a4e 0x55c39cfa73ee4e93

def z760 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07cf9ffc1ce7f 0xbf3c1f3e7ff0739f

def z761 : W := mkw 0x4010952257c3dcf6 0x5004254895f0f73d 0x0c000f003fc1fc7e 0x830003c00ff07f1f

def z762 : W := mkw 0x086248dfbc000000 0x02189237ef000000 0x58f070fffc000001 0x163c1c3fff000000

def z763 : W := mkw 0xc006b76add9b7add 0x7001addab766deb7 0xd50ffcf7f3fec5b0 0x3543ff3dfcffb16c

def z764 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0xe7fe7c0003fff002 0xb9ff9f0000fffc00

def z765 : W := mkw 0x4000850214025094 0x1000214085009425 0x88018f1e3c47fffd 0xa20063c78f11ffff

def z766 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc00c031 0xfe7fffffff00300c

def z767 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff0e0ffffffe 0xf9ffffc383ffffff

def z768 : W := mkw 0x0060589161018060 0x4018162458406018 0x58f07ce1f001c070 0x963c1f387c00701c

def z769 : W := mkw 0x0060cd9120025000 0x0018336448009400 0xfaf1fff1f047f003 0xfebc7ffc7c11fc00

def z770 : W := mkw 0x00ab00fc00880a01 0x002ac03f00220280 0xf7ff80fe03fe0f83 0x7dffe03f80ff83e0

def z771 : W := mkw 0x4d8fa74e9c367094 0x1363e9d3a70d9c25 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z772 : W := mkw 0x4befefdfbc2e5395 0x92fbfbf7ef0b94e5 0xfbfffffffc7fffff 0xfeffffffff1fffff

def z773 : W := mkw 0x0050582043c18840 0x4014160810f06210 0xfcf07cf1f3c1cc73 0xbf3c1f3c7cf0731c

def z774 : W := mkw 0x0c3210dfbf77f000 0x030c8437efddfc00 0x1e0000fffffff003 0x0780003ffffffc00

def z775 : W := mkw 0x008f224888000000 0x0023c89222000000 0xf9fff3e9cc000001 0xfe7ffcfa73000000

def z776 : W := mkw 0x0099100003650000 0x0026440000d94000 0xe7fff00003ff0002 0xf9fffc0000ffc000

def z777 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc460003 0xfeffffffff118000

def z778 : W := mkw 0x85dbcd68caeeda49 0x6176f35a32bbb692 0x98f18ce9cc46ca4d 0x263c633a7311b293

def z779 : W := mkw 0x8dddff03ff77f048 0x63777fc0ffddfc12 0xefffff01fffff04e 0xfbffffc07ffffc13

def z780 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff003ffffffe 0xfbffffc00fffffff

def z781 : W := mkw 0x049910000375a000 0x0126440000dd6800 0xe7ff800003fe0002 0x79ffe00000ff8000

def z782 : W := mkw 0x059d220002742000 0x01674880009d0800 0xe7ff800003fe0002 0x79ffe00000ff8000

def z783 : W := mkw 0x822200fc88880f0b 0xa088803f222203c2 0x100000fe0c000f8d 0x0400003f830003e3

def z784 : W := mkw 0x01cfef4a9c000000 0x0073fbd2a7000000 0xf9fffffffc000001 0xfe7fffffff000000

def z785 : W := mkw 0x0070589163418060 0x401c162458d06018 0xfcf07cf1f3c1c073 0xbf3c1f3c7cf0701c

def z786 : W := mkw 0x8a2200fffc880f4b 0xe288803fff2203d2 0x180000fffc000fcd 0x0600003fff0003f3

def z787 : W := mkw 0x0060489120008020 0x0018122448002008 0xf8f07cf1f000c031 0xbe3c1f3c7c00300c

def z788 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xf9fffffffc00007d 0xfe7fffffff00001f

def z789 : W := mkw 0x0fefefdfbc3e7301 0x83fbfbf7ef0f9cc0 0xfbfffffffc3e3381 0xfeffffffff0f8ce0

def z790 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x45fe730003b93000 0x917f9cc000ee4c00

def z791 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0xe5ffff0003f9c002 0xf97fffc000fe7000

def z792 : W := mkw 0x82bb00fccaec0f4b 0xe0aec03f32bb03d2 0xf7ff80ffc3fe0f83 0x7dffe03ff0ff83e0

def z793 : W := mkw 0x029b106c43ed8f63 0xc0a6c41b10fb63d8 0x070f800e03ffcff2 0x41c3e00380fff3fc

def z794 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff1e33fffff3 0xfbffffc78cfffffc

def z795 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff000ffff00e 0xf9ffffc003fffc03

def z796 : W := mkw 0x003200f802c80e03 0x000c803e00b20380 0xf7ff80fe03fe0f83 0x7dffe03f80ff83e0

def z797 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07cf1f3c0c431 0xbf3c1f3c7cf0310c

def z798 : W := mkw 0x0099000002640000 0x0026400000990000 0x47ff800003be0000 0x51ffe00000ef8000

def z799 : W := mkw 0x8010102043d9ae6b 0x6004040810f66b9a 0x0600000003b93a4e 0x0180000000ee4e93

def z800 : W := mkw 0x0010000002400000 0x0004000000900000 0xe4f0001003c00c03 0x393c000400f00300

def z801 : W := mkw 0x0410102043f5ac62 0x4104040810fd6b18 0x0400000003f9cc72 0x0100000000fe731c

def z802 : W := mkw 0x01ed6a9120000000 0x007b5aa448000000 0xf9fe7cf1f0000001 0xbe7f9f3c7c000000

def z803 : W := mkw 0x49ef6adda8025094 0x127bdab76a009425 0x53fe70e1c047fffe 0x14ff9c387011ffff

def z804 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80fe03ff3fcf 0x7dffe03f80ffcff3

def z805 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xf9fffffffc46c001 0xfe7fffffff11b000

def z806 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x71fe73e1c0000000 0xdc7f9cf870000000

def z807 : W := mkw 0x00547a000351a000 0x00151e8000d46800 0xe5fe7c0003f9c002 0xb97f9f0000fe7000

def z808 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff801003fe0c03 0x79ffe00400ff8300

def z809 : W := mkw 0x09edef9734000000 0x027b7be5cd000000 0xf9fffff7f0000001 0xfe7ffffdfc000000

def z810 : W := mkw 0x02cb584d612d8361 0xc0b2d613584b60d8 0x0b0ffc0ff03fc3f0 0xc2c3ff03fc0ff0fc

def z811 : W := mkw 0x027058b563c18d62 0xc09c162d58f06358 0xfcf07cf7f3c1cdf3 0xbf3c1f3dfcf0737c

def z812 : W := mkw 0x8206326cc9992b49 0xe0818c9b32664ad2 0x7f0e73efcfb93bcf 0xdfc39cfbf3ee4ef3

def z813 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x180000fe30000ff1 0x0600003f8c0003fc

def z814 : W := mkw 0x4df9cd973666d094 0x137e7365cd99b425 0x80f18c163046c5b0 0x203c63058c11b16c

def z815 : W := mkw 0x05ddef000276f000 0x01777bc0009dbc00 0xe7ff8f0003fef002 0x79ffe3c000ffbc00

def z816 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xf9fffffffc41cfff 0xfe7fffffff1073ff

def z817 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x71fe70e9c0000001 0x5c7f9c3a70000000

def z818 : W := mkw 0x007048b162c08c62 0x401c122c58b02318 0xf8f07cf1f040cc71 0xbe3c1f3c7c10331c

def z819 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc01fffd 0xfe7fffffff007fff

def z820 : W := mkw 0x026258fd61898f63 0xc098963f586263d8 0x18007cfff001cff1 0x86001f3ffc0073fc

def z821 : W := mkw 0x0bef6adda82c0301 0x82fbdab76a0b00c0 0x53fff0efc03e0380 0x54fffc3bf00f80e0

def z822 : W := mkw 0x4a2200ffbc880f97 0x9288803fef2203e5 0x180000fffc000ffd 0x0600003fff0003ff

def z823 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf1fffff7f0000000 0xfc7ffffdfc000000

def z824 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff8ffe3fffffff 0xffffe3ff8fffffff

def z825 : W := mkw 0x0099100003658000 0x0026440000d96000 0xe7ff800003ffc002 0x79ffe00000fff000

def z826 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff8cfe03ffcf83 0xfdffe33f80fff3e0

def z827 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7d0e73e1cfb9384f 0x9f439cf873ee4e13

def z828 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0600000003c7cff2 0x0180000000f1f3fc

def z829 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0x4dfe7f003fb9f07c 0x937f9fc00fee7c1f

def z830 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc47f5fd 0xfe7fffffff11fd7f

def z831 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xdcf07cf1f3c0cc71 0x373c1f3c7cf0331c

def z832 : W := mkw 0x00646a9120000000 0x00191aa448000000 0xf9fe7ff1f0000001 0xfe7f9ffc7c000000

def z833 : W := mkw 0x09efefdfbc008020 0x027bfbf7ef002008 0xf9fffffffc00c031 0xfe7fffffff00300c

def z834 : W := mkw 0x802200f9e8880e6b 0x6008803e7a22039a 0x180000e9cc000a4d 0x0600003a73000293

def z835 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf1fffcfff0000001 0x7c7fff3ffc000000

def z836 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf1fe70f1c0000001 0x3c7f9c3c70000000

def z837 : W := mkw 0x02ab00fc00ac0b01 0x80aac03f002b02c0 0xf7ff80fe03be0b83 0x7dffe03f80ef82e0

def z838 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff80fe03ff0fc3 0xffffe03f80ffc3f0

def z839 : W := mkw 0x82bb00fdeaec0f6b 0xe0aec03f7abb03da 0xffff80fffffe0fff 0x7fffe03fffff83ff

def z840 : W := mkw 0x0060cd9334000000 0x00183364cd000000 0xf8f1fcf7f0000001 0xbe3c7f3dfc000000

def z841 : W := mkw 0x006058b161810840 0x4018162c58604210 0xfcf07cf1f3c1cc73 0xbf3c1f3c7cf0731c

def z842 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73e9cff9fe7f 0xdfc39cfa73fe7f9f

def z843 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc01304d 0xfe7fffffff004c13

def z844 : W := mkw 0x007058b163d1ac62 0x401c162c58f46b18 0xfef07cf1f3f9fc73 0xbfbc1f3c7cfe7f1c

def z845 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f001c071 0xbe3c1f3c7c00701c

def z846 : W := mkw 0xc5ddff02df77f0dc 0x71777fc0b7ddfc37 0xefffff1fffffffff 0xfbffffc7ffffffff

def z847 : W := mkw 0x01cdff0215112000 0x00737fc085444800 0xefffff1e3fb93a4f 0xfbffffc78fee4e93

def z848 : W := mkw 0x029b004c026c0301 0x80a6c013009b00c0 0xe7ff801e03fe0f83 0x79ffe00780ff83e0

def z849 : W := mkw 0x0014320003512000 0x00050c8000d44800 0xe7fe730003f93002 0xf9ff9cc000fe4c00

def z850 : W := mkw 0x0befefdfbc080301 0x82fbfbf7ef0200c0 0xf9fffffffc000381 0xfe7fffffff0000e0

def z851 : W := mkw 0x00ab00dc00000000 0x002ac03700000000 0xf9fff0ffc0000001 0xfe7ffc3ff0000000

def z852 : W := mkw 0x0060589161018060 0x4018162458406018 0xf8f07cf1f041cc73 0xbe3c1f3c7c10731c

def z853 : W := mkw 0x0befefdfbc000502 0x82fbfbf7ef000140 0xf9fffffffc000581 0xfe7fffffff000160

def z854 : W := mkw 0x89e9ddb775992a49 0x627a776ddd664a92 0x86f18c1633b93a4e 0x21bc63058cee4e93

def z855 : W := mkw 0x4410952257f7fcf6 0x5104254895fdff3d 0xae018f1e3fffffff 0xeb8063c78fffffff

def z856 : W := mkw 0x01cf6a4888000000 0x0073da9222000000 0x79fe73e9cc000001 0xde7f9cfa73000000

def z857 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000f600000580 0x0400003d80000160

def z858 : W := mkw 0x0050582163c18860 0x4014160858f06218 0xfcf07ce1f3c1c873 0xbf3c1f387cf0721c

def z859 : W := mkw 0x4defefdfbc367094 0x137bfbf7ef0d9c25 0xfbfffffffc3e338d 0xfeffffffff0f8ce3

def z860 : W := mkw 0x019da70002640000 0x006769c000990000 0xe7ff830003fe0002 0x79ffe0c000ff8000

def z861 : W := mkw 0x0070489122408422 0x001c122448902108 0xf8f07cf1f041cc73 0xbe3c1f3c7c10731c

def z862 : W := mkw 0x82bd3294cb75254a 0xe0af4ca532dd4952 0x88f1f317cc4735cc 0xa23c7cc5f311cd73

def z863 : W := mkw 0x0010102043e58c62 0x4004040810f96318 0x0600000003ffcc72 0x0180000000fff31c

def z864 : W := mkw 0x4964ef93bc025094 0x12593be4ef009425 0xf8f07ff1fc41fc7f 0xbe3c1ffc7f107f1f

def z865 : W := mkw 0x82063268c9992f4b 0xe0818c9a32664bd2 0x7f0e73e9cfb93fcf 0xdfc39cfa73ee4ff3

def z866 : W := mkw 0x00666ad9a8000000 0x00199ab66a000000 0xf9fe7cf1f0000001 0xbe7f9f3c7c000000

def z867 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000e800000a01 0x0400003a00000280

def z868 : W := mkw 0x05fdff912377f000 0x017f7fe448ddfc00 0xfffffff1f3fffc73 0xfffffffc7cffff1c

def z869 : W := mkw 0x0a2200fda8880f03 0x8288803f6a2203c0 0x100000ffc0000f81 0x0400003ff00003e0

def z870 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x47fff00003be0000 0x51fffc0000ef8000

def z871 : W := mkw 0x809d3200cb752048 0x60274c8032dd4812 0xeffff301cfff304e 0xfbfffcc073ffcc13

def z872 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f1fcfff0000001 0xfe3c7f3ffc000000

def z873 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc063ffd 0xfeffffffff018fff

def z874 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80fe03ffcff3 0x7dffe03f80fff3fc

def z875 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07ff9ffc1cc73 0xff3c1ffe7ff0731c

def z876 : W := mkw 0x4010102043c3dcf6 0x5004040810f0f73d 0x0400000003c7cdf2 0x0100000000f1f37c

def z877 : W := mkw 0x80163268cbd9ae6b 0x60058c9a32f66b9a 0x070e03080ff9fe7e 0x41c380c203fe7f9f

def z878 : W := mkw 0x0b66efffbc880f03 0x82d9bbffef2203c0 0x18007ffffc000f81 0x86001fffff0003e0

def z879 : W := mkw 0x42bb85fe16ee5f97 0x90aee17f85bb97e5 0x5dfe0fe03fb9f07c 0x977f83f80fee7c1f

def z880 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf9fe7cf1f041cc73 0xbe7f9f3c7c10731c

def z881 : W := mkw 0x882200fde8880a49 0x6208803f7a220292 0x180000e9cc000a4d 0x0600003a73000293

def z882 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x47fff30003fff002 0x51fffcc000fffc00

def z883 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf9fe7ff9fc000001 0xfe7f9ffe7f000000

def z884 : W := mkw 0x49ef6adfbc000094 0x127bdab7ef000025 0x59fe70fffc000ffd 0x167f9c3fff0003ff

def z885 : W := mkw 0x8410952043fffa49 0x6104254810fffe92 0xae018f080ffffa4f 0xeb8063c203fffe93

def z886 : W := mkw 0x882200fffc880e6b 0x6208803fff22039a 0x180000fffc000e7d 0x0600003fff00039f

def z887 : W := mkw 0x047058b163f5ac62 0x411c162c58fd6b18 0xfcf07cf1f3f9cc73 0xbf3c1f3c7cfe731c

def z888 : W := mkw 0x00547a000351a000 0x00151e8000d46800 0x67fe730003b93002 0xd9ff9cc000ee4c00

def z889 : W := mkw 0x09cfef4e9c000000 0x0273fbd3a7000000 0xf9ffffefcc000001 0xfe7ffffbf3000000

def z890 : W := mkw 0x8006324889192209 0x20018c9222464882 0x7f0e73e9cfb9320f 0xdfc39cfa73ee4c83

def z891 : W := mkw 0x01ddff000351a000 0x00777fc000d46800 0xe7ffff0003f9f002 0xf9ffffc000fe7c00

def z892 : W := mkw 0x05ddff000377f422 0x01777fc000ddfd08 0xe7ffff0003fff432 0xf9ffffc000fffd0c

def z893 : W := mkw 0x007048b122c08c22 0x001c122c48b02308 0xfcf07cf1f3c0cc33 0xbf3c1f3c7cf0330c

def z894 : W := mkw 0x802200f8c8880e4b 0x6008803e32220392 0x180000f9cc000e4d 0x0600003e73000393

def z895 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x59fe7ce1f0000000 0x967f9f387c000000

def z896 : W := mkw 0x0010952043c3dc62 0x4004254810f0f718 0xa6018f0003c7fc72 0xe98063c000f1ff1c

def z897 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x79fe7fe9fc000001 0xde7f9ffa7f000000

def z898 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003c00c02 0x0100000000f00300

def z899 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x51fe70ffc0000001 0x147f9c3ff0000000

def z900 : W := mkw 0x80063248c9112048 0x60018c9232444812 0x7f0e73e9cfb9304f 0xdfc39cfa73ee4c13

def z901 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xe7ffff0003fff5b2 0xf9ffffc000fffd6c

def z902 : W := mkw 0x45dd7a021775a094 0x11775e8085dd6825 0x4dfe701e3fb80ffd 0x137f9c078fee03ff

def z903 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0e73f9cff93e4f 0xffc39cfe73fe4f93

def z904 : W := mkw 0x4000850214025094 0x1000214085009425 0xfa01fffffc47ffff 0xfe807fffff11ffff

def z905 : W := mkw 0x0554ff000353f000 0x01553fc000d4fc00 0xe7fe7f0003f9f002 0xf9ff9fc000fe7c00

def z906 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0e7ff9ffb93a4f 0xffc39ffe7fee4e93

def z907 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc41fe7f 0xfeffffffff107f9f

def z908 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0x51fe70f7f0000000 0x147f9c3dfc000000

def z909 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x55ff80e603be0180 0x157fe03980ef8060

def z910 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xfbfffffffc47ff83 0xfeffffffff11ffe0

def z911 : W := mkw 0x0099100003752000 0x0026440000dd4800 0xe7ff800003ff3002 0x79ffe00000ffcc00

def z912 : W := mkw 0x09e9489520000000 0x027a522548000000 0xf8f07cf1f0000001 0xbe3c1f3c7c000000

def z913 : W := mkw 0x4544ff021513f094 0x11513fc08544fc25 0x00007f000c01f00c 0x80001fc003007c03

def z914 : W := mkw 0x01ed6a9120000000 0x007b5aa448000000 0x51fe70e1c0000000 0x147f9c3870000000

def z915 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9ffffe1fc000000 0xfe7ffff87f000000

def z916 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff801603fe0582 0x79ffe00580ff8160

def z917 : W := mkw 0x009b006802ec0a01 0x0026c01a00bb0280 0xf7ff80fe03fe0f83 0x7dffe03f80ff83e0

def z918 : W := mkw 0x099fb76edfc18c62 0x4267eddbb7f06318 0x050f830e0fc1cc72 0x4143e0c383f0731c

def z919 : W := mkw 0x02b9009402640502 0x80ae402500990140 0xe7ff801e03fe0f83 0x79ffe00780ff83e0

def z920 : W := mkw 0x086248dda8000000 0x021892376a000000 0x50f070e1c0000000 0x143c1c3870000000

def z921 : W := mkw 0x082200ffbc880a01 0x0208803fef220280 0x180000fffc000a01 0x0600003fff000280

def z922 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe7fffc0003ffc002 0xf9ffff0000fff000

def z923 : W := mkw 0x01edef9334000000 0x007b7be4cd000000 0xf9fffffffc000001 0xfe7fffffff000000

def z924 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x6ffe73080fb93a4f 0xdbff9cc203ee4e93

def z925 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x180073e1cc01304c 0x86001cf873004c13

def z926 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff800803fe0a03 0x79ffe00200ff8280

def z927 : W := mkw 0x89ef6adda8182209 0x227bdab76a060882 0x53fe73e9cc38320c 0x54ff9cfa730e0c83

def z928 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc000a4d 0xfe7fffffff000293

def z929 : W := mkw 0x02bb00fc42ec0f63 0xc0aec03f10bb03d8 0xf7ff80fe03fe0ff3 0x7dffe03f80ff83fc

def z930 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc47f5b3 0xfeffffffff11fd6c

def z931 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf1fcf7f3c7cdf3 0xbf3c7f3dfcf1f37c

def z932 : W := mkw 0x003010b043c10c42 0x400c042c10f04310 0xfcf07cf1f3c1cc73 0xbf3c1f3c7cf0731c

def z933 : W := mkw 0x8610102043ffff4b 0xe184040810ffffd2 0x0600000003ffffce 0x0180000000fffff3

def z934 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x87ff801e03fe0f82 0x61ffe00780ff83e0

def z935 : W := mkw 0x0099000002640000 0x0026400000990000 0x80f1801600460580 0x203c600580118160

def z936 : W := mkw 0x01d9cd0002640000 0x0076734000990000 0xe7ff8c0003fe0002 0x79ffe30000ff8000

def z937 : W := mkw 0x02b9009402640502 0x80ae402500990140 0xc5ff801603fe0580 0x317fe00580ff8160

def z938 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xfbfffffffc013fff 0xfeffffffff004fff

def z939 : W := mkw 0x4060489334000094 0x10181224cd000025 0xf8f07cfffc000ffd 0xbe3c1f3fff0003ff

def z940 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73f9ffb93e7f 0xdfc39cfe7fee4f9f

def z941 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0xf9ffffe9cc000001 0xfe7ffffa73000000

def z942 : W := mkw 0x09edef97bc000000 0x027b7be5ef000000 0xf8f1fff7fc000001 0xbe3c7ffdff000000

def z943 : W := mkw 0x0966efdbbc000000 0x0259bbf6ef000000 0xf9fe7ff9fc000001 0xfe7f9ffe7f000000

def z944 : W := mkw 0x007058b163e58c62 0x401c162c58f96318 0xfef07cf1f3ffcc73 0xbfbc1f3c7cfff31c

def z945 : W := mkw 0x02fb48fd22ec0f03 0x80bed23f48bb03c0 0xfffffcfff3ffcff3 0xffffff3ffcfff3fc

def z946 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0xe7ffff0003b93002 0xf9ffffc000ee4c00

def z947 : W := mkw 0x022200fc40880f63 0xc088803f102203d8 0x100000fe00000ff1 0x0400003f800003fc

def z948 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xd1fff0f7c0000000 0x347ffc3df0000000

def z949 : W := mkw 0x029b006c02ec0f03 0x80a6c01b00bb03c0 0x070f800e03be0380 0x41c3e00380ef80e0

def z950 : W := mkw 0x006248d920000000 0x0018923648000000 0xf9fe7cf9f0000001 0xfe7f9f3e7c000000

def z951 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xf4f07cf1f3c1c432 0xbd3c1f3c7cf0710c

def z952 : W := mkw 0x422200fe14880f97 0x9088803f852203e5 0x100000fe0c000f8d 0x0400003f830003e3

def z953 : W := mkw 0x05ada7b160b67c62 0x416b69ec582d9f18 0x1b0f83f1f03e3c71 0x46c3e0fc7c0f8f1c

def z954 : W := mkw 0x0410102043f5ac62 0x4104040810fd6b18 0x0400000003b80000 0x0100000000ee0000

def z955 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73e9cfb8320d 0xdfc39cfa73ee0c83

def z956 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x47fe730003b83000 0x51ff9cc000ee0c00

def z957 : W := mkw 0x09efefdfbc102000 0x027bfbf7ef040800 0xfbfffffffc383001 0xfeffffffff0e0c00

def z958 : W := mkw 0x8010102043c98e6b 0x6004040810f2639a 0x0400000003c1ce7e 0x0100000000f0739f

def z959 : W := mkw 0x0010000002400000 0x0004000000900000 0xe7fe000003f80002 0x79ff800000fe0000

def z960 : W := mkw 0x00666ad9a8000000 0x00199ab66a000000 0x79fe73e9cc000001 0xde7f9cfa73000000

def z961 : W := mkw 0x80063268c9992e6b 0x60018c9a32664b9a 0x7f0e73e9cfb93e7f 0xdfc39cfa73ee4f9f

def z962 : W := mkw 0x822200fcc8880f4b 0xe088803f322203d2 0x100000e1c0000000 0x0400003870000000

def z963 : W := mkw 0x0610102043ffff63 0xc184040810ffffd8 0x0600000003fffff2 0x0180000000fffffc

def z964 : W := mkw 0xc944ff03fd1370dc 0x72513fc0ff44dc37 0x08007f01fc01f07c 0x82001fc07f007c1f

def z965 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x040000000381c070 0x0100000000e0701c

def z966 : W := mkw 0x80766ad9aa58a62b 0x201d9ab66a96298a 0x83fe0f183c78f63c 0x60ff83c60f1e3d8f

def z967 : W := mkw 0x85ddff01eb77f068 0x61777fc07addfc1a 0xefffff01fffff07e 0xfbffffc07ffffc1f

def z968 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc000c71 0xfe7fffffff00031c

def z969 : W := mkw 0x0010102043c98e63 0x4004040810f26398 0x0600000003f9ce72 0x0180000000fe739c

def z970 : W := mkw 0x09edef93bc000000 0x027b7be4ef000000 0xf9fffff1fc000001 0xfe7ffffc7f000000

def z971 : W := mkw 0x802200f9e8880a49 0x6008803e7a220292 0x180000f9fc000a4d 0x0600003e7f000293

def z972 : W := mkw 0x0960cd9334000000 0x02583364cd000000 0xf8f07cf1f0000001 0xbe3c1f3c7c000000

def z973 : W := mkw 0xc02200fbfc880eff 0x7008803eff2203bf 0x180000fffc000ffd 0x0600003fff0003ff

def z974 : W := mkw 0x822200fde8880f6b 0xe088803f7a2203da 0x180000fffc000ffd 0x0600003fff0003ff

def z975 : W := mkw 0x45f9cd933666d4b6 0x117e7364cd99b52d 0x80f18c163046c5b0 0x203c63058c11b16c

def z976 : W := mkw 0x0006324889112000 0x00018c9222444800 0x7f0e73e9cfb93a4f 0xdfc39cfa73ee4e93

def z977 : W := mkw 0x0964ef93bc000000 0x02593be4ef000000 0xf8f1fffffc000001 0xfe3c7fffff000000

def z978 : W := mkw 0x002200f800880e03 0x0008803e00220380 0x100000f800000e01 0x0400003e00000380

def z979 : W := mkw 0x00e9489120000000 0x003a522448000000 0xf9fffcf1f0000001 0xfe7fff3c7c000000

def z980 : W := mkw 0x0299000402640100 0x80a6400100990040 0xe7ff800603fe0182 0x79ffe00180ff8060

def z981 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x5f0e73e1cfb93a4e 0x97c39cf873ee4e93

def z982 : W := mkw 0x02bb00dc026c0703 0x80aec037009b01c0 0xe7ff801e03fe0782 0x79ffe00780ff81e0

def z983 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x45fe700003f9c002 0x117f9c0000fe7000

def z984 : W := mkw 0x05ddff012377f000 0x01777fc048ddfc00 0xefffff01f3fff002 0xfbffffc07cfffc00

def z985 : W := mkw 0x82bb00fccaec0f4b 0xe0aec03f32bb03d2 0xffff83ffcfff3fcf 0xffffe0fff3ffcff3

def z986 : W := mkw 0x027058b163ed8f63 0xc09c162c58fb63d8 0xfcf07cf1f3f9cc73 0xbf3c1f3c7cfe731c

def z987 : W := mkw 0x08666adfbc000000 0x02199ab7ef000000 0xf9fe7ffffc000001 0xfe7f9fffff000000

def z988 : W := mkw 0x822200fc40880f4b 0xe088803f102203d2 0x100000fe00000fcd 0x0400003f800003f3

def z989 : W := mkw 0x009d220002742000 0x00274880009d0800 0xe7ff830003fe3002 0x79ffe0c000ff8c00

def z990 : W := mkw 0xc98fa74e9c1a729d 0x3263e9d3a7069ca7 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z991 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07cf1f381c071 0xbf3c1f3c7ce0701c

def z992 : W := mkw 0x05ddff004377f060 0x41777fc010ddfc18 0xe7ffff0003fff072 0xf9ffffc000fffc1c

def z993 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xd4f07cf1f3c1cc72 0x353c1f3c7cf0731c

def z994 : W := mkw 0x01cdef0000000000 0x00737bc000000000 0xf9ffffe1c0000001 0xfe7ffff870000000

def z995 : W := mkw 0x09efefdfbc240000 0x027bfbf7ef090000 0xfbfffffffc3e0001 0xfeffffffff0f8000

def z996 : W := mkw 0x0060489120000000 0x0018122448000000 0xf0f07ce1c0000000 0xbc3c1f3870000000

def z997 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0xf9fff0fffc000001 0x7e7ffc3fff000000

def z998 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0ff3e9cfff3a4f 0xffc3fcfa73ffce93

def z999 : W := mkw 0x4964ef93bc025094 0x12593be4ef009425 0xfaf1fffffc47ffff 0xfebc7fffff11ffff

def z1000 : W := mkw 0x0070589123418000 0x001c162448d06000 0xfcf07cf1f3c1cc73 0xbf3c1f3c7cf0731c

def z1001 : W := mkw 0x08af22dfbc000000 0x022bc8b7ef000000 0xf9fff3fffc000001 0xfe7ffcffff000000

def z1002 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff080ffff003 0xfbffffc203fffc00

def z1003 : W := mkw 0x4060cd9334025094 0x10183364cd009425 0xf8f1fcf7f046c5b1 0xbe3c7f3dfc11b16c

def z1004 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe7fe7f0003f9f002 0xf9ff9fc000fe7c00

def z1005 : W := mkw 0xc28fa74e9c3e739d 0xb0a3e9d3a70f9ce7 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z1006 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc00320d 0xfeffffffff000c83

def z1007 : W := mkw 0x0060489120000000 0x0018122448000000 0x58f070f1f0000001 0x163c1c3c7c000000

def z1008 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe7fff30003ff3002 0xf9fffcc000ffcc00

def z1009 : W := mkw 0x422285fe148a5f97 0x9088a17f852297e5 0x120183fe0c063f8d 0x448060ff83018fe3

def z1010 : W := mkw 0x0860489734000000 0x02181225cd000000 0xf8f07cf7f0000001 0xbe3c1f3dfc000000

def z1011 : W := mkw 0x0060cd9120000000 0x0018336448000000 0xf8f1fff1f0000001 0xfe3c7ffc7c000000

def z1012 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x59ffffeffc000000 0xd67ffffbff000000

def z1013 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc010843 0xfe7fffffff004210

def z1014 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x87ff8f0003fff002 0x61ffe3c000fffc00

def z1015 : W := mkw 0x049d32000377f000 0x01274c8000ddfc00 0xe7fff30003fff002 0xf9fffcc000fffc00

def z1016 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x59fe73e1cc000000 0x967f9cf873000000

def z1017 : W := mkw 0x00bb00dc02640000 0x002ec03700990000 0xf7ff80fe03fe0f83 0x7dffe03f80ff83e0

def z1018 : W := mkw 0x02bb00fc02ec8f23 0x80aec03f00bb23c8 0xf7ff80fe03fecfb3 0x7dffe03f80ffb3ec

def z1019 : W := mkw 0x0060489334000000 0x00181224cd000000 0xf8f07cfffc000001 0xbe3c1f3fff000000

def z1020 : W := mkw 0x0060489120000422 0x0018122448000108 0xf8f07cf1f0000431 0xbe3c1f3c7c00010c

def z1021 : W := mkw 0x049910000375a000 0x0126440000dd6800 0x45fe000003b80000 0x117f800000ee0000

def z1022 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0xb8000cfe3041cff3 0xae00033f8c1073fc

def z1023 : W := mkw 0x023200fc02ec0f03 0x808c803f00bb03c0 0x100000fe00460f81 0x0400003f801183e0

def z1024 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0x47fff30e0fbe338c 0x51fffcc383ef8ce3

def z1025 : W := mkw 0x09e9cd9734000000 0x027a7365cd000000 0xf8f1fffffc000001 0xfe3c7fffff000000

def z1026 : W := mkw 0x4000850214025094 0x1000214085009425 0xef0f8f1e3fffffff 0xfbc3e3c78fffffff

def z1027 : W := mkw 0x01ddef0216640000 0x00777bc085990000 0xefffff1e3ffe0f83 0xfbffffc78fff83e0

def z1028 : W := mkw 0x89cdff03fd112048 0x62737fc0ff444812 0xefffff01ffb9304e 0xfbffffc07fee4c13

def z1029 : W := mkw 0x807058b163c98e6b 0x601c162c58f2639a 0xfcf07cf1f3c1ce7f 0xbf3c1f3c7cf0739f

def z1030 : W := mkw 0x00d9580163658060 0x4036560058d96018 0xeffffc01f3ffc072 0xfbffff007cfff01c

def z1031 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe5ffff0003b9f000 0xf97fffc000ee7c00

def z1032 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x59fe70e9cc000001 0x167f9c3a73000000

def z1033 : W := mkw 0x01cdff0001137000 0x00737fc00044dc00 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z1034 : W := mkw 0x459da70216767094 0x116769c0859d9c25 0xefff8f1e3fffffff 0xfbffe3c78fffffff

def z1035 : W := mkw 0x029b006c02ec0f03 0x80a6c01b00bb03c0 0xe7ff800e03fe0f82 0x79ffe00380ff83e0

def z1036 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xd9fffff7fc000000 0xb67ffffdff000000

def z1037 : W := mkw 0x8210102043fd2f4b 0xe084040810ff4bd2 0x0600000003b93a4e 0x0180000000ee4e93

def z1038 : W := mkw 0x02bb00fd62ec0f63 0xc0aec03f58bb03d8 0xf7ff80ffc3fe0f83 0x7dffe03ff0ff83e0

def z1039 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x770e73e9cfb83a0f 0x5dc39cfa73ee0e83

def z1040 : W := mkw 0x8410102043fffe6b 0x6104040810ffff9a 0x0600000003fffe7e 0x0180000000ffff9f

def z1041 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff1033fff003 0xfbffffc40cfffc00

def z1042 : W := mkw 0x022200fe14880f03 0x8088803f852203c0 0x180000fe3c000f81 0x0600003f8f0003e0

def z1043 : W := mkw 0x007048b122c00c02 0x001c122c48b00300 0xfcf07cf1f3c1cc73 0xbf3c1f3c7cf0731c

def z1044 : W := mkw 0x0040480000000000 0x0010120000000000 0xf8f07ce1c0000001 0xbe3c1f3870000000

def z1045 : W := mkw 0x0010102043c10c42 0x4004040810f04310 0x0400000003c10c42 0x0100000000f04310

def z1046 : W := mkw 0xc58fa74a9c3e729d 0x3163e9d2a70f9ca7 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z1047 : W := mkw 0x4099850216665094 0x1026614085999425 0xe7ff8c1633fec5b2 0x79ffe3058cffb16c

def z1048 : W := mkw 0x0040480120000000 0x0010120048000000 0x08007c01f001c070 0x82001f007c00701c

def z1049 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf1fff0e1c0000000 0x7c7ffc3870000000

def z1050 : W := mkw 0x422285fe148a5f97 0x9088a17f852297e5 0x18000ffe3c01fffd 0x860003ff8f007fff

def z1051 : W := mkw 0x0000000000000000 0x0000000000000000 0x670e000803b80a03 0x59c3800200ee0280

def z1052 : W := mkw 0x00eb48dd20000000 0x003ad23748000000 0x51fe70e1c0000000 0x147f9c3870000000

def z1053 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf5ff80fe03fe0581 0x7d7fe03f80ff8160

def z1054 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff1633fffffe 0xf9ffffc58cffffff

def z1055 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0x59fe7fe1fc01f07c 0x967f9ff87f007c1f

def z1056 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xd9fffcfffc000001 0x367fff3fff000000

def z1057 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x070e03080fb8320c 0x41c380c203ee0c83

def z1058 : W := mkw 0x882200fffc880a49 0x6208803fff220292 0x180000fffc000001 0x0600003fff000000

def z1059 : W := mkw 0x009d320003752000 0x00274c8000dd4800 0xe7fff00003fe0002 0x79fffc0000ff8000

def z1060 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xc5ffff0003fff000 0xb17fffc000fffc00

def z1061 : W := mkw 0x01cdff0001112000 0x00737fc000444800 0xe5ffff0003b80000 0xf97fffc000ee0000

def z1062 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff0e3ffff3fe 0xfbffffc38ffffcff

def z1063 : W := mkw 0x4099850216665094 0x1026614085999425 0xefff8f003ffff07e 0xfbffe3c00ffffc1f

def z1064 : W := mkw 0x009db70003777000 0x00276dc000dddc00 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z1065 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x84000c1033c1cc72 0x210003040cf0731c

def z1066 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff0003fff843 0xfbffffc000fffe10

def z1067 : W := mkw 0x49e9cd9734025094 0x127a7365cd009425 0xfaf1fffffc47ffff 0xfebc7fffff11ffff

def z1068 : W := mkw 0x01ddef0002665000 0x00777bc000999400 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z1069 : W := mkw 0x0dddff03bf75a000 0x03777fc0efdd6800 0x4dfe7f01ffb80000 0x937f9fc07fee0000

def z1070 : W := mkw 0x0299002002ec0f03 0x80a6400800bb03c0 0xe7ff801e03fe0f83 0x79ffe00780ff83e0

def z1071 : W := mkw 0x006058b161818c62 0x4018162c58606318 0x18007ce1f001c070 0x86001f387c00701c

def z1072 : W := mkw 0x0020009120000000 0x0008002448000000 0x180000f1f0000c71 0x0600003c7c00031c

def z1073 : W := mkw 0x0defefdfbc367000 0x037bfbf7ef0d9c00 0xfbfffffffc7ff003 0xfeffffffff1ffc00

def z1074 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07ff9fc000001 0xfe3c1ffe7f000000

def z1075 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003c0c430 0x0100000000f0310c

def z1076 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc47cdf3 0xfe7fffffff11f37c

def z1077 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xefffff003ffff002 0xfbffffc00ffffc00

def z1078 : W := mkw 0x0966efdfbc000000 0x0259bbf7ef000000 0x18007fe1fc000000 0x86001ff87f000000

def z1079 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff83fe0ffe3f8f 0x7dffe0ff83ff8fe3

def z1080 : W := mkw 0x02bb00fd62ec0f63 0xc0aec03f58bb03d8 0xffff8cfff3ffcff3 0xffffe33ffcfff3fc

def z1081 : W := mkw 0x4066efdbbc025094 0x1019bbf6ef009425 0xfbfffffffc47ffff 0xfeffffffff11ffff

def z1082 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x550e73e1cfb8300c 0x15439cf873ee0c03

def z1083 : W := mkw 0x498fa74e9c025094 0x1263e9d3a7009425 0x010f830e0c00300c 0x4043e0c383000c03

def z1084 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc41fc7f 0xfe7fffffff107f1f

def z1085 : W := mkw 0x00666ad9a8000000 0x00199ab66a000000 0x51fe70e1c0000000 0x147f9c3870000000

def z1086 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc000f81 0xfe7fffffff0003e0

def z1087 : W := mkw 0x0dddff029f77f000 0x03777fc0a7ddfc00 0xe7ffff000ffff002 0xf9ffffc003fffc00

def z1088 : W := mkw 0x00eb48dd20000000 0x003ad23748000000 0xf1fff0ffc0000001 0x7c7ffc3ff0000000

def z1089 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc47f38f 0xfeffffffff11fce3

def z1090 : W := mkw 0x409db70217777094 0x10276dc085dddc25 0xefffff1e3fffffff 0xfbffffc78fffffff

def z1091 : W := mkw 0x01cfef4888025000 0x0073fbd222009400 0xfbffffe9cc47fa4f 0xfefffffa7311fe93

def z1092 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003810842 0x0100000000e04210

def z1093 : W := mkw 0x41ddef0216665094 0x10777bc085999425 0xefffff1e3fffffff 0xfbffffc78fffffff

def z1094 : W := mkw 0x01efefdc88000000 0x007bfbf722000000 0xf9ffffffcc000001 0xfe7ffffff3000000

def z1095 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff800e03fe0382 0x79ffe00380ff80e0

def z1096 : W := mkw 0x0410102043f7f840 0x4104040810fdfe10 0x0600000003fff842 0x0180000000fffe10

def z1097 : W := mkw 0x422200fe14880f97 0x9088803f852203e5 0x100000fe30000fb1 0x0400003f8c0003ec

def z1098 : W := mkw 0x8010102043fd2a49 0x6004040810ff4a92 0x0600000003ff3a4e 0x0180000000ffce93

def z1099 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff000ffff04e 0xfbffffc003fffc13

def z1100 : W := mkw 0x459da70216767094 0x116769c0859d9c25 0xe7ff831e0ffe3f8f 0x79ffe0c783ff8fe3

def z1101 : W := mkw 0x022200fd60880f63 0xc088803f582203d8 0x100000ffc0000f81 0x0400003ff00003e0

def z1102 : W := mkw 0x00d9580003658000 0x0036560000d96000 0xe5fe7c0003f9c002 0xb97f9f0000fe7000

def z1103 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc473fcf 0xfeffffffff11cff3

def z1104 : W := mkw 0x05cdff000113f000 0x01737fc00044fc00 0xe7ffff0003b9f002 0xf9ffffc000ee7c00

def z1105 : W := mkw 0x4bf9cd9736665596 0x92fe7365cd999565 0x80f18c163046c5b0 0x203c63058c11b16c

def z1106 : W := mkw 0x422200fc00880f97 0x9088803f002203e5 0x100000fe00000ffd 0x0400003f800003ff

def z1107 : W := mkw 0x0410102043d3fc62 0x4104040810f4ff18 0x0400000003c1fc72 0x0100000000f07f1c

def z1108 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff83fe0ffe0f83 0xffffe0ff83ff83e0

def z1109 : W := mkw 0x0066efdbbc000000 0x0019bbf6ef000000 0xf9fffffffc000001 0xfe7fffffff000000

def z1110 : W := mkw 0xc010952257dbfeff 0x7004254895f6ffbf 0xae018f1e3fffffff 0xeb8063c78fffffff

def z1111 : W := mkw 0x80063268c999aa69 0x60018c9a32666a9a 0x7f0e73e9cfb9fa7f 0xdfc39cfa73ee7e9f

def z1112 : W := mkw 0x0defefdda8367000 0x037bfbf76a0d9c00 0x53fff3e1c03e3000 0x54fffcf8700f8c00

def z1113 : W := mkw 0x00646a91a8000000 0x00191aa46a000000 0xf8f07ff1fc000001 0xbe3c1ffc7f000000

def z1114 : W := mkw 0x0599850002665000 0x0166614000999400 0xe7ff800003fe0002 0x79ffe00000ff8000

def z1115 : W := mkw 0x00af22dc88000000 0x002bc8b722000000 0x51fe70e1c0000000 0x147f9c3870000000

def z1116 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff1e3ffff7be 0xf9ffffc78ffffdef

def z1117 : W := mkw 0x00547a000351a000 0x00151e8000d46800 0xeffe7f183ff9fe7f 0xfbff9fc60ffe7f9f

def z1118 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0xc5fffc0003b80000 0x317fff0000ee0000

def z1119 : W := mkw 0x802200fcc8880a49 0x6008803f32220292 0x180000ffcc000a4d 0x0600003ff3000293

def z1120 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff8cfe33fecfb3 0x7dffe33f8cffb3ec

def z1121 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xf4f07cf1f3c0cc33 0x3d3c1f3c7cf0330c

def z1122 : W := mkw 0x809f3268cbfd2a49 0x6027cc9a32ff4a92 0xfffff3ffcfff3fcf 0xfffffcfff3ffcff3

def z1123 : W := mkw 0x8210102043fd2f4b 0xe084040810ff4bd2 0x0600000003fe0f82 0x0180000000ff83e0

def z1124 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x900180fe00460f81 0x2400603f801183e0

def z1125 : W := mkw 0x049995000377f000 0x0126654000ddfc00 0xe7ff8f0003fff002 0xf9ffe3c000fffc00

def z1126 : W := mkw 0x00afa7de9c000000 0x002be9f7a7000000 0xf9fffffffc000001 0xfe7fffffff000000

def z1127 : W := mkw 0x85dd7a00cb75a048 0x61775e8032dd6812 0x45fe7001c3b80000 0x117f9c0070ee0000

def z1128 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e7fe9ffb9fa7f 0xdfc39ffa7fee7e9f

def z1129 : W := mkw 0x0010102043d1ac62 0x4004040810f46b18 0x0600000003f9fc72 0x0180000000fe7f1c

def z1130 : W := mkw 0x41cdff0215137094 0x10737fc08544dc25 0xefffff1e3fffffff 0xfbffffc78fffffff

def z1131 : W := mkw 0x0b54ef23beec0f03 0x82d53bc8efbb03c0 0x0e007f01fffe0f82 0x83801fc07fff83e0

def z1132 : W := mkw 0x8010102043d92e4b 0x6004040810f64b92 0x0600000003f93e4e 0x0180000000fe4f93

def z1133 : W := mkw 0x008d320001112000 0x00234c8000444800 0xe7fff30003b93002 0xf9fffcc000ee4c00

def z1134 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0x45fe7f0003b80000 0x917f9fc000ee0000

def z1135 : W := mkw 0x05cdff0001377000 0x01737fc0004ddc00 0xe7ffff0003bf3002 0xf9ffffc000efcc00

def z1136 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0xf1ffffffc0000001 0xfc7ffffff0000000

def z1137 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc41c003 0xfe7fffffff107000

def z1138 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xdcf07cf1f3c1c470 0xb73c1f3c7cf0711c

def z1139 : W := mkw 0x82bb00fc42ec0f4b 0xe0aec03f10bb03d2 0xf7ff80fe03fe0fcf 0x7dffe03f80ff83f3

def z1140 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff80fe33fe0ff3 0x7fffe03f8cff83fc

def z1141 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x5cf07ce1f3c1cc72 0x973c1f387cf0731c

def z1142 : W := mkw 0x0dddff033777f000 0x03777fc0cdddfc00 0xe7ffff0033fff002 0xf9ffffc00cfffc00

def z1143 : W := mkw 0x882285fffc880a49 0x6208a17fff220292 0xba018ffffc013a4f 0xee8063ffff004e93

def z1144 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0xf9fe7cfffc000001 0xbe7f9f3fff000000

def z1145 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x51fe73e1cc000000 0x147f9cf873000000

def z1146 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x47fe700003b93002 0x11ff9c0000ee4c00

def z1147 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff1033fff432 0xf9ffffc40cfffd0c

def z1148 : W := mkw 0x4060cd9334025094 0x10183364cd009425 0xfaf1fffffc06338d 0xfebc7fffff018ce3

def z1149 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xd1fe7cf1f0000000 0x347f9f3c7c000000

def z1150 : W := mkw 0x01dd6a0002640000 0x00775a8000990000 0x45fe700003b80000 0x117f9c0000ee0000

def z1151 : W := mkw 0x0defefdfbc342000 0x037bfbf7ef0d0800 0xf9fffffffc380001 0xfe7fffffff0e0000

def z1152 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0600000003c1fe7e 0x0180000000f07f9f

def z1153 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x5d0e73e9cfb93a4d 0x97439cfa73ee4e93

def z1154 : W := mkw 0x059db7000377f000 0x01676dc000ddfc00 0xe7ff830003fff002 0x79ffe0c000fffc00

def z1155 : W := mkw 0x449995021777f094 0x1126654085ddfc25 0xefff8f1e3fffffff 0xfbffe3c78fffffff

def z1156 : W := mkw 0x0099850002665000 0x0026614000999400 0xe7ff8c0003fec002 0x79ffe30000ffb000

def z1157 : W := mkw 0x822200fcc8880f4b 0xe088803f322203d2 0xba0183ffcc473fcf 0xee8060fff311cff3

def z1158 : W := mkw 0x0006226888880a01 0x0001889a22220280 0x7f0e73e9cfb93a4f 0xdfc39cfa73ee4e93

def z1159 : W := mkw 0x00af22dc88000000 0x002bc8b722000000 0xf1fff0ffc0000001 0x7c7ffc3ff0000000

def z1160 : W := mkw 0x01cdef0000000000 0x00737bc000000000 0xe7ffff0003b80002 0xf9ffffc000ee0000

def z1161 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe5fff00003b80000 0x797ffc0000ee0000

def z1162 : W := mkw 0x0060489120000000 0x0018122448000000 0x58f07ce1f0000000 0x963c1f387c000000

def z1163 : W := mkw 0x086248dda8000000 0x021892376a000000 0xf8f07cf1f0000001 0xbe3c1f3c7c000000

def z1164 : W := mkw 0x45d9cd021666d094 0x117673408599b425 0xefff8f1e3fffffff 0xfbffe3c78fffffff

def z1165 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07ce1f3c1c072 0xbf3c1f387cf0701c

def z1166 : W := mkw 0x0060cd9334000000 0x00183364cd000000 0xf8f07ff1fc000001 0xbe3c1ffc7f000000

def z1167 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x2e0003080fc1fe7f 0xcb8000c203f07f9f

def z1168 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0003fffc72 0xf9ffffc000ffff1c

def z1169 : W := mkw 0x80667af9e999ae6b 0x60199ebe7a666b9a 0x18007ff9fc01fe7d 0x86001ffe7f007f9f

def z1170 : W := mkw 0x003010b163c18c62 0x400c042c58f06318 0x0400001033c1cc72 0x010000040cf0731c

def z1171 : W := mkw 0x0210102043c98f63 0xc084040810f263d8 0x0400000003c1cff2 0x0100000000f073fc

def z1172 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x65fe730003b80000 0xd97f9cc000ee0000

def z1173 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf9fffcfff0000001 0xfe7fff3ffc000000

def z1174 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff1e3ffff38f 0xfbffffc78ffffce3

def z1175 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xefffff080fffffff 0xfbffffc203ffffff

def z1176 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xe5fe7c0003b80000 0xb97f9f0000ee0000

def z1177 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xefffff1e3ffffc73 0xfbffffc78fffff1c

def z1178 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xc5fe7c0003f8c000 0x317f9f0000fe3000

def z1179 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0003ffff82 0xf9ffffc000ffffe0

def z1180 : W := mkw 0x4000850214025094 0x1000214085009425 0x82018f1e3c47fffe 0x608063c78f11ffff

def z1181 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xc5fff00003fe0000 0x317ffc0000ff8000

def z1182 : W := mkw 0xc82200fffc880add 0x7208803fff2202b7 0x180000fffc000ffd 0x0600003fff0003ff

def z1183 : W := mkw 0xc5ddff02df77f0dc 0x71777fc0b7ddfc37 0xefffff01fffff07e 0xfbffffc07ffffc1f

def z1184 : W := mkw 0xc22200fedc880fdf 0xf088803fb72203f7 0x180000fffc000ffd 0x0600003fff0003ff

def z1185 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0c000c0033c1cc72 0x830003000cf0731c

def z1186 : W := mkw 0x009d320003752000 0x00274c8000dd4800 0xeffff31e0fff3fcf 0xfbfffcc783ffcff3

def z1187 : W := mkw 0x85dd7a00cb75a048 0x61775e8032dd6812 0x4dfe7301cfb9304c 0x937f9cc073ee4c13

def z1188 : W := mkw 0x49e9cd9734025094 0x127a7365cd009425 0xf8f1fcf7f047cdf3 0xbe3c7f3dfc11f37c

def z1189 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000fe00000001 0x0400003f80000000

def z1190 : W := mkw 0x8410102043fffa49 0x6104040810fffe92 0x0600000003fff002 0x0180000000fffc00

def z1191 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf5ff80f603fe0d83 0x3d7fe03d80ff8360

def z1192 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0xd1fffce1c0000000 0x347fff3870000000

def z1193 : W := mkw 0x42f9cd973666d5b6 0x90be7365cd99b56d 0x80f18c163046c5b0 0x203c63058c11b16c

def z1194 : W := mkw 0x00f958b163e58c62 0x403e562c58f96318 0xfffffcfff3ffcff3 0xffffff3ffcfff3fc

def z1195 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xf9fffffffc0005b1 0xfe7fffffff00016c

def z1196 : W := mkw 0x02bb00dc026c0301 0x80aec037009b00c0 0xf7ff80fe03fe0383 0x7dffe03f80ff80e0

def z1197 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff083ffffa7f 0xfbffffc20ffffe9f

def z1198 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f041c003 0xbe3c1f3c7c107000

def z1199 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0c00001033c1cc73 0x030000040cf0731c

def z1200 : W := mkw 0x40d9dd021767d094 0x1036774085d9f425 0xefffff1e3fffffff 0xfbffffc78fffffff

def z1201 : W := mkw 0x0099000002640000 0x0026400000990000 0x47fe000003fe0002 0x11ff800000ff8000

def z1202 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xfbfffffffc47fa4f 0xfeffffffff11fe93

def z1203 : W := mkw 0x01efefdd20000000 0x007bfbf748000000 0xf9fffffff0000001 0xfe7ffffffc000000

def z1204 : W := mkw 0x09646a91a8000000 0x02591aa46a000000 0x50f070e1c0000000 0x143c1c3870000000

def z1205 : W := mkw 0x0089000000000000 0x0022400000000000 0xe7ff800003b80002 0x79ffe00000ee0000

def z1206 : W := mkw 0x0099850216640000 0x0026614085990000 0xefff8f1e3ffe0003 0xfbffe3c78fff8000

def z1207 : W := mkw 0x8966fffffd992a49 0x6259bfffff664a92 0x18007ffffc013a4d 0x86001fffff004e93

def z1208 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0x45fe700003b9f000 0x117f9c0000ee7c00

def z1209 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xc7ffff0003fef000 0x71ffffc000ffbc00

def z1210 : W := mkw 0x09efefdfbc080201 0x027bfbf7ef020080 0xfbfffffffc380201 0xfeffffffff0e0080

def z1211 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff183ffffe7f 0xfbffffc60fffff9f

def z1212 : W := mkw 0x822200fcc8880f4b 0xe088803f322203d2 0x100000ffc0000f81 0x0400003ff00003e0

def z1213 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x180000fe0c000fcd 0x0600003f830003f3

def z1214 : W := mkw 0x4010952257c3dcf6 0x5004254895f0f73d 0x84018c1633c7cdf2 0x210063058cf1f37c

def z1215 : W := mkw 0x8010102043d9ae6b 0x6004040810f66b9a 0xae000f183ff9fe7f 0xeb8003c60ffe7f9f

def z1216 : W := mkw 0x006048b160800c62 0x4018122c58200318 0xf8f07cf1f041cc73 0xbe3c1f3c7c10731c

def z1217 : W := mkw 0x829f326ccbfd2f4b 0xe0a7cc9b32ff4bd2 0x070f830e0fff3fce 0x41c3e0c383ffcff3

def z1218 : W := mkw 0x01cf6a4888000000 0x0073da9222000000 0x51fe70e1c0000000 0x147f9c3870000000

def z1219 : W := mkw 0x85ddff008b77f008 0x21777fc022ddfc02 0xe7ffff000ffff00e 0xf9ffffc003fffc03

def z1220 : W := mkw 0x0410102043e7dc62 0x4104040810f9f718 0x0400000003c7cc72 0x0100000000f1f31c

def z1221 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x51fe73e9cc000000 0x547f9cfa73000000

def z1222 : W := mkw 0x4010952257c3dcf6 0x5004254895f0f73d 0x0601830e0fc7fffe 0x418060c383f1ffff

def z1223 : W := mkw 0x05d9480002648000 0x0176520000992000 0x45fe000003b80000 0x117f800000ee0000

def z1224 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0x53fff3efcc06338c 0x54fffcfbf3018ce3

def z1225 : W := mkw 0x0410102043f7fc62 0x4104040810fdff18 0x0600000003fff002 0x0180000000fffc00

def z1226 : W := mkw 0x4d44ff03bd13f094 0x13513fc0ef44fc25 0x08007f01fc01f07c 0x82001fc07f007c1f

def z1227 : W := mkw 0x05d9dd000367d000 0x0176774000d9f400 0xe7fffc0003ffc002 0xf9ffff0000fff000

def z1228 : W := mkw 0x02ab00fc00ac0f03 0x80aac03f002b03c0 0x100180fe00060f81 0x0400603f800183e0

def z1229 : W := mkw 0xc010102043dbfeff 0x7004040810f6ffbf 0x0600000003fffffe 0x0180000000ffffff

def z1230 : W := mkw 0x01cd7a0001112000 0x00735e8000444800 0x67fe730003b93002 0xd9ff9cc000ee4c00

def z1231 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff801e03fe0003 0x79ffe00780ff8000

def z1232 : W := mkw 0x0060489120000000 0x0018122448000000 0x80f00c103040c430 0x203c03040c10310c

def z1233 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc463f8f 0xfeffffffff118fe3

def z1234 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc47f07f 0xfeffffffff11fc1f

def z1235 : W := mkw 0x0099000002640000 0x0026400000990000 0xc5ff800003fe0000 0x317fe00000ff8000

def z1236 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xfbfffffffc47fc73 0xfeffffffff11ff1c

def z1237 : W := mkw 0x89efefdfbc080209 0x227bfbf7ef020082 0xf9fffffffc00020d 0xfe7fffffff000083

def z1238 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0e03fff382 0xf9ffffc380fffce0

def z1239 : W := mkw 0x022200fd60880f63 0xc088803f582203d8 0x100000e1c0000000 0x0400003870000000

def z1240 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xd1fffffffc000000 0x747fffffff000000

def z1241 : W := mkw 0x882200fde8880a49 0x6208803f7a220292 0x100000e1c0000000 0x0400003870000000

def z1242 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfffe7cf1f3f9cc73 0xffff9f3c7cfe731c

def z1243 : W := mkw 0x8010102043d9ae6b 0x6004040810f66b9a 0x0400000003f9cc72 0x0100000000fe731c

def z1244 : W := mkw 0x422285ff748a5ff7 0xd088a17fdd2297fd 0xba018ffffc47ffff 0xee8063ffff11ffff

def z1245 : W := mkw 0x09e9489520000000 0x027a522548000000 0x50f070e1c0000000 0x143c1c3870000000

def z1246 : W := mkw 0x449910000377f094 0x1126440000ddfc25 0xe7ff801e03ffffff 0x79ffe00780ffffff

def z1247 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff0033fff072 0xfbffffc00cfffc1c

def z1248 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0fffffffffffff 0xffc3ffffffffffff

def z1249 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc01c071 0xfe7fffffff00701c

def z1250 : W := mkw 0x002200f960880e63 0x4008803e58220398 0x180000f9f0000e71 0x0600003e7c00039c

def z1251 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf3fff0ffc0460f83 0x7cfffc3ff01183e0

def z1252 : W := mkw 0x0020009000000000 0x0008002400000000 0xf8f070f1c0000001 0xbe3c1c3c70000000

def z1253 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc400c03 0xfe7fffffff100300

def z1254 : W := mkw 0x01edef9120025000 0x007b7be448009400 0xfbfffff1f047fc73 0xfefffffc7c11ff1c

def z1255 : W := mkw 0x8010102043d1ac6a 0x6004040810f46b1a 0x0400000003c1fc7e 0x0100000000f07f1f

def z1256 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x3a0003fe0c013fcf 0xce8000ff83004ff3

def z1257 : W := mkw 0x0a2200ff34880f03 0x8288803fcd2203c0 0x100000fe30000f81 0x0400003f8c0003e0

def z1258 : W := mkw 0x09e9cd9734000000 0x027a7365cd000000 0xd0f1fcf7f0000000 0x343c7f3dfc000000

def z1259 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf1fe7ce1c0000000 0xbc7f9f3870000000

def z1260 : W := mkw 0x05ddff021775a000 0x01777fc085dd6800 0xedffff1e3fb80001 0xfb7fffc78fee0000

def z1261 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0003fffa4e 0xf9ffffc000fffe93

def z1262 : W := mkw 0x4060489120025094 0x1018122448009425 0xfaf07cf1f047ffff 0xbebc1f3c7c11ffff

def z1263 : W := mkw 0x05ddef0002767000 0x01777bc0009d9c00 0xe7ffff0003fe3002 0xf9ffffc000ff8c00

def z1264 : W := mkw 0xc22285fedc8a5fdf 0xf088a17fb72297f7 0xba018ffffc47ffff 0xee8063ffff11ffff

def z1265 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0xf9fff3ffcc000001 0xfe7ffcfff3000000

def z1266 : W := mkw 0x05ddff016377f060 0x41777fc058ddfc18 0xefffff11f3fffc73 0xfbffffc47cffff1c

def z1267 : W := mkw 0xc544ff02dd13f0dc 0x71513fc0b744fc37 0x08007f01fc01f07c 0x82001fc07f007c1f

def z1268 : W := mkw 0x4060cd9334025094 0x10183364cd009425 0xf8f07ff1fc01f07d 0xbe3c1ffc7f007c1f

def z1269 : W := mkw 0x8210102043fdaf6b 0xe084040810ff6bda 0x0600000003fffffe 0x0180000000ffffff

def z1270 : W := mkw 0x022200fd20880f03 0x8088803f482203c0 0x180000fff0000f81 0x0600003ffc0003e0

def z1271 : W := mkw 0x029b004c026c0301 0x80a6c013009b00c0 0x47ff800e03be0380 0x51ffe00380ef80e0

def z1272 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80fe03be0381 0x7dffe03f80ef80e0

def z1273 : W := mkw 0x01ddff0003752000 0x00777fc000dd4800 0xe7ffff0003ff3002 0xf9ffffc000ffcc00

def z1274 : W := mkw 0x02bb00fd22ec0f03 0x80aec03f48bb03c0 0xffff80fff3fe0f83 0x7fffe03ffcff83e0

def z1275 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0xa601801e03c7cff3 0x6980600780f1f3fc

def z1276 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x770e73e9cfb9320e 0xddc39cfa73ee4c83

def z1277 : W := mkw 0x02bb00fc42ec0f43 0xc0aec03f10bb03d0 0xffff80ffc3fe0fc3 0x7fffe03ff0ff83f0

def z1278 : W := mkw 0x422285fe148a5f97 0x9088a17f852297e5 0x90018cfe3046cfb1 0x2400633f8c11b3ec

def z1279 : W := mkw 0x049910000377f000 0x0126440000ddfc00 0x47fe000003fff002 0x11ff800000fffc00

def z1280 : W := mkw 0x0070489122408422 0x001c122448902108 0xd0f07cf1f040c430 0x343c1f3c7c10310c

def z1281 : W := mkw 0x80043220c9912848 0x60010c8832644a12 0x7f0e73e1cfb9384f 0xdfc39cf873ee4e13

def z1282 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0x51fe7fe1c0000000 0x947f9ff870000000

def z1283 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff830003ff3002 0xf9ffe0c000ffcc00

def z1284 : W := mkw 0x00466a4888000000 0x00119a9222000000 0xf9fe7fe9cc000001 0xfe7f9ffa73000000

def z1285 : W := mkw 0x4210952257efdff7 0xd084254895fbf7fd 0xae018f1e3fffffff 0xeb8063c78fffffff

def z1286 : W := mkw 0x002200fc00880a01 0x0008803f00220280 0x100000fe00000a01 0x0400003f80000280

def z1287 : W := mkw 0x4befefdfbc2e5395 0x92fbfbf7ef0b94e5 0xfbfffffffc3e338d 0xfeffffffff0f8ce3

def z1288 : W := mkw 0x8006226888982a09 0x2001889a22260a82 0x7f0e73e9cfb83a0f 0xdfc39cfa73ee0e83

def z1289 : W := mkw 0x01dd6a0002640000 0x00775a8000990000 0xe7fff00003fe0002 0x79fffc0000ff8000

def z1290 : W := mkw 0xc410102043fffadd 0x7104040810fffeb7 0x0600000003fffffe 0x0180000000ffffff

def z1291 : W := mkw 0x82ff7afdebfdaf6b 0xe0bfdebf7aff6bda 0x55fe70e1c3b80000 0x157f9c3870ee0000

def z1292 : W := mkw 0x022285fc008a5f03 0x8088a17f002297c0 0xb2018ffe0047ff83 0xec8063ff8011ffe0

def z1293 : W := mkw 0x0a2200ffbc880f03 0x8288803fef2203c0 0x180000fffc000001 0x0600003fff000000

def z1294 : W := mkw 0x00e9489520000000 0x003a522548000000 0xf8f1fcf7f0000001 0xbe3c7f3dfc000000

def z1295 : W := mkw 0x07ddff000377f502 0x81f77fc000ddfd40 0xe7ffff0003fff582 0xf9ffffc000fffd60

def z1296 : W := mkw 0x82af22dc883c2309 0xa0abc8b7220f08c2 0xfbfff3ffcc3e338d 0xfefffcfff30f8ce3

def z1297 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xd7ff80fe03fe0780 0x75ffe03f80ff81e0

def z1298 : W := mkw 0x8defefdfbc3e7209 0x237bfbf7ef0f9c82 0xfbfffffffc3e320d 0xfeffffffff0f8c83

def z1299 : W := mkw 0x0050580003418000 0x0014160000d06000 0xe7fe7c0003f9c002 0xf9ff9f0000fe7000

def z1300 : W := mkw 0x4099850216665094 0x1026614085999425 0xe7ff830e0ffe338e 0x79ffe0c383ff8ce3

def z1301 : W := mkw 0x807058b163d9ae6b 0x601c162c58f66b9a 0xfcf07cf1f3f9cc73 0xbf3c1f3c7cfe731c

def z1302 : W := mkw 0x05d9cd000266d000 0x017673400099b400 0xe7ff8f0003fff002 0xf9ffe3c000fffc00

def z1303 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000f000000c01 0x0400003c00000300

def z1304 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x65fe700003b90002 0x997f9c0000ee4000

def z1305 : W := mkw 0x05ddff000375a000 0x01777fc000dd6800 0xe7ffff0003fe0002 0xf9ffffc000ff8000

def z1306 : W := mkw 0xc210952257ff7fdf 0xf084254895ffdff7 0xae018f1e3fffffff 0xeb8063c78fffffff

def z1307 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc073bcf 0xfeffffffff01cef3

def z1308 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0xa400001003c1cc73 0x2900000400f0731c

def z1309 : W := mkw 0x0010102043c3dc62 0x4004040810f0f718 0x0600000003c7fc72 0x0180000000f1ff1c

def z1310 : W := mkw 0x0000000000000000 0x0000000000000000 0x780070e1c0010843 0x9e001c3870004210

def z1311 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0003be3000 0xf9ffffc000ef8c00

def z1312 : W := mkw 0x02b900b402e40d02 0x80ae402d00b90340 0xf7ff80f603fe0d83 0x7dffe03d80ff8360

def z1313 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xd5ff80fe03fe0f81 0x357fe03f80ff83e0

def z1314 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xf9fffffffc00038d 0xfe7fffffff0000e3

def z1315 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xfbfffffffc063001 0xfeffffffff018c00

def z1316 : W := mkw 0x0499000002767000 0x01264000009d9c00 0xe7ff800003fe3002 0x79ffe00000ff8c00

def z1317 : W := mkw 0x00d9480002648000 0x0036520000992000 0xe7ff8c0003fec002 0x79ffe30000ffb000

def z1318 : W := mkw 0x0befefdfbc2c0301 0x82fbfbf7ef0b00c0 0xf9fffffffc380001 0xfe7fffffff0e0000

def z1319 : W := mkw 0x4defefdfbc367094 0x137bfbf7ef0d9c25 0xfbfffffffc7fffff 0xfeffffffff1fffff

def z1320 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x98f1fffffc000001 0xa63c7fffff000000

def z1321 : W := mkw 0x09ddef03be640000 0x02777bc0ef990000 0xefffff01fffe0002 0xfbffffc07fff8000

def z1322 : W := mkw 0x4862cddfbc025094 0x1218b377ef009425 0xfaf1fffffc47ffff 0xfebc7fffff11ffff

def z1323 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fe7ff1fc000001 0xbe7f9ffc7f000000

def z1324 : W := mkw 0x0299000002640502 0x80a6400000990140 0xe7ff800003fe0582 0x79ffe00000ff8160

def z1325 : W := mkw 0x0089000000000000 0x0022400000000000 0xe1ff801e00000001 0x787fe00780000000

def z1326 : W := mkw 0x022200fd20880f23 0x8088803f482203c8 0x100000fe30000fb1 0x0400003f8c0003ec

def z1327 : W := mkw 0x8010102043d9ae6b 0x6004040810f66b9a 0x0400000003b80000 0x0100000000ee0000

def z1328 : W := mkw 0x022200fd60880f63 0xc088803f582203d8 0xba018cfff047cff3 0xee80633ffc11f3fc

def z1329 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff163ffff5fe 0xfbffffc58ffffd7f

def z1330 : W := mkw 0x0070589163418462 0x401c162458d06118 0xf8f07cf1f041c471 0xbe3c1f3c7c10711c

def z1331 : W := mkw 0x4b8fa74e9c2e5395 0x92e3e9d3a70b94e5 0x030f830e0c3e338c 0x40c3e0c3830f8ce3

def z1332 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x67fe7f0003b9f002 0xd9ff9fc000ee7c00

def z1333 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x67fff30003bf3002 0xd9fffcc000efcc00

def z1334 : W := mkw 0x80547a01eb51a068 0x60151e807ad4681a 0xeffe7f01fff9f07e 0xfbff9fc07ffe7c1f

def z1335 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73ffcfb93fcf 0xdfc39cfff3ee4ff3

def z1336 : W := mkw 0x4054ff021753f094 0x10153fc085d4fc25 0xefffff1e3fffffff 0xfbffffc78fffffff

def z1337 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xc7fffc0003fff002 0x31ffff0000fffc00

def z1338 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf1ffffefcc000000 0xfc7ffffbf3000000

def z1339 : W := mkw 0x0060489120000000 0x0018122448000000 0xfaf07ff9fc013a4f 0xfebc1ffe7f004e93

def z1340 : W := mkw 0x0010952257c18c62 0x4004254895f06318 0xac018f1e3fc1cc73 0xeb0063c78ff0731c

def z1341 : W := mkw 0x4dddff03bf77f094 0x13777fc0efddfc25 0xefffff01fffff07e 0xfbffffc07ffffc1f

def z1342 : W := mkw 0x45ddff037777f0f4 0x51777fc0ddddfc3d 0xefffff1fffffffff 0xfbffffc7ffffffff

def z1343 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7fff30003fe3002 0x79fffcc000ff8c00

def z1344 : W := mkw 0x09efefdda8000000 0x027bfbf76a000000 0xf9fffff1f0000001 0xfe7ffffc7c000000

def z1345 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf1fff3ffcc000001 0x7c7ffcfff3000000

def z1346 : W := mkw 0x029b006c02ec0b01 0x80a6c01b00bb02c0 0xf7ff80ee03fe0b83 0x7dffe03b80ff82e0

def z1347 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x47fe7f0003fff002 0x91ff9fc000fffc00

def z1348 : W := mkw 0x0099000002640000 0x0026400000990000 0xe5fe000003f80002 0x397f800000fe0000

def z1349 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff0603fff182 0xf9ffffc180fffc60

def z1350 : W := mkw 0x006058b161818c62 0x4018162c58606318 0xf8f07cf1f001cc71 0xbe3c1f3c7c00731c

def z1351 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff83fe03ff3f83 0xfdffe0ff80ffcfe0

def z1352 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x5f0e73e9cfb9324c 0xd7c39cfa73ee4c93

def z1353 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xd1fffcf7f046c5b0 0x347fff3dfc11b16c

def z1354 : W := mkw 0x09cfef4bbc000000 0x0273fbd2ef000000 0xf9ffffe9fc000001 0xfe7ffffa7f000000

def z1355 : W := mkw 0x0054ff000353f000 0x00153fc000d4fc00 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z1356 : W := mkw 0x09ebcddfbc000000 0x027af377ef000000 0xf8f1fcfffc000001 0xbe3c7f3fff000000

def z1357 : W := mkw 0x00d9580003658000 0x0036560000d96000 0xe7fff00003fe0002 0x79fffc0000ff8000

def z1358 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x120180fe00060f81 0x4480603f800183e0

def z1359 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x51fff0e7c0000000 0x147ffc39f0000000

def z1360 : W := mkw 0x0210102043ed0f43 0xc084040810fb43d0 0x0600000003ff0fc2 0x0180000000ffc3f0

def z1361 : W := mkw 0xc9efefdfbc1a729d 0x327bfbf7ef069ca7 0xfbfffffffc7fffff 0xfeffffffff1fffff

def z1362 : W := mkw 0x422200fc008a5f97 0x9088803f002297e5 0x120000fe0047ffff 0x0480003f8011ffff

def z1363 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe5ffff0003fec000 0xf97fffc000ffb000

def z1364 : W := mkw 0x00d9dd000367d000 0x0036774000d9f400 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z1365 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff1e33ffffb3 0xf9ffffc78cffffec

def z1366 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xe7ffff1e03ffffff 0xf9ffffc780ffffff

def z1367 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000ee00000380 0x0400003b800000e0

def z1368 : W := mkw 0x85ddff004377f048 0x61777fc010ddfc12 0xe7ffff0003fff04e 0xf9ffffc000fffc13

def z1369 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0xe7fff00003fff002 0x79fffc0000fffc00

def z1370 : W := mkw 0x00b900b002e40c02 0x002e402c00b90300 0xf7ff80fe03fe0f83 0x7dffe03f80ff83e0

def z1371 : W := mkw 0x802200f9e8880e6b 0x6008803e7a22039a 0x180000f1f0000c71 0x0600003c7c00031c

def z1372 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x7cf07ce1f381c873 0x9f3c1f387ce0721c

def z1373 : W := mkw 0x0089000000240000 0x0022400000090000 0x030f800e003e0380 0x40c3e003800f80e0

def z1374 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc46cfb3 0xfeffffffff11b3ec

def z1375 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0x67fe730003fff002 0xd9ff9cc000fffc00

def z1376 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0e73e1cfb9304e 0xdfc39cf873ee4c13

def z1377 : W := mkw 0x009d220002640000 0x0027488000990000 0xe7fff30003fe0002 0xf9fffcc000ff8000

def z1378 : W := mkw 0x09646a91a8000000 0x02591aa46a000000 0xf8f07cf1f0000001 0xbe3c1f3c7c000000

def z1379 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7f0ff3efcfbf3bcf 0xdfc3fcfbf3efcef3

def z1380 : W := mkw 0x027058b163e58d62 0xc09c162c58f96358 0xfcf07cf1f3c7cdf3 0xbf3c1f3c7cf1f37c

def z1381 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef07cf1f3c1fe7f 0xbfbc1f3c7cf07f9f

def z1382 : W := mkw 0x05d9480002648000 0x0176520000992000 0xe7ff800003fe0002 0x79ffe00000ff8000

def z1383 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xffffffe1c3fff003 0xfffffff870fffc00

def z1384 : W := mkw 0x4099000216640094 0x1026400085990025 0xefff801e3ffe0fff 0x7bffe0078fff83ff

def z1385 : W := mkw 0x0070589123418422 0x001c162448d06108 0xfcf07cf1f3c1c433 0xbf3c1f3c7cf0710c

def z1386 : W := mkw 0x0dddff03ff77f060 0x43777fc0ffddfc18 0xefffff01fffff072 0xfbffffc07ffffc1c

def z1387 : W := mkw 0x4a2285ffbc8a5f97 0x9288a17fef2297e5 0xba018ffffc47ffff 0xee8063ffff11ffff

def z1388 : W := mkw 0x0010000002640000 0x0004000000990000 0x0600000003fe0f82 0x0180000000ff83e0

def z1389 : W := mkw 0x41cfef4a9c025094 0x1073fbd2a7009425 0xfbfffffffc47ffff 0xfeffffffff11ffff

def z1390 : W := mkw 0x49efefdfbc000094 0x127bfbf7ef000025 0xfbfffffffc460fff 0xfeffffffff1183ff

def z1391 : W := mkw 0x049900000266d000 0x012640000099b400 0xe7ff800003fec002 0x79ffe00000ffb000

def z1392 : W := mkw 0x01edef9120000000 0x007b7be448000000 0xf1ffffe1c0000000 0xfc7ffff870000000

def z1393 : W := mkw 0x0210102043ed8f63 0xc084040810fb63d8 0x0400000003b80000 0x0100000000ee0000

def z1394 : W := mkw 0x0a2200fda8880f03 0x8288803f6a2203c0 0x100000e1c0000000 0x0400003870000000

def z1395 : W := mkw 0x0def6adda8342000 0x037bdab76a0d0800 0x51fe70e1c0380000 0x147f9c38700e0000

def z1396 : W := mkw 0x01e9cd9120000000 0x007a736448000000 0xf8f1fcf1f0000001 0xbe3c7f3c7c000000

def z1397 : W := mkw 0x07ddff040377f100 0x81f77fc100ddfc40 0xe7ffff0603fff182 0xf9ffffc180fffc60

def z1398 : W := mkw 0x4010102043c3dcf6 0x5004040810f0f73d 0x0400000003c1fc7e 0x0100000000f07f1f

def z1399 : W := mkw 0x05ddff012377f020 0x01777fc048ddfc08 0xe7ffff0033fff032 0xf9ffffc00cfffc0c

def z1400 : W := mkw 0x00d9580003658000 0x0036560000d96000 0x45fe700003b80000 0x117f9c0000ee0000

def z1401 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xd7ff80f603fe0f82 0x35ffe03d80ff83e0

def z1402 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x2c00000003c1cc73 0x8b00000000f0731c

def z1403 : W := mkw 0xc210102043ff7fdf 0xf084040810ffdff7 0x0600000003fffffe 0x0180000000ffffff

def z1404 : W := mkw 0x0060489120000000 0x0018122448000000 0xfaf1fcfff0460f83 0xfebc7f3ffc1183e0

def z1405 : W := mkw 0x4010102257c18cf6 0x5004040895f0633d 0x0c00001e3fc1cfff 0x030000078ff073ff

def z1406 : W := mkw 0xc410952257fffadd 0x7104254895fffeb7 0xae018f1e3fffffff 0xeb8063c78fffffff

def z1407 : W := mkw 0x09afa7de9c000000 0x026be9f7a7000000 0xf9fff3ffcc000001 0xfe7ffcfff3000000

def z1408 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0x51fe70efcc000000 0x147f9c3bf3000000

def z1409 : W := mkw 0x08604893bc000000 0x02181224ef000000 0xf8f07cf1fc000001 0xbe3c1f3c7f000000

def z1410 : W := mkw 0x0a2285ffbc880f03 0x8288a17fef2203c0 0xba018ffffc460f83 0xee8063ffff1183e0

def z1411 : W := mkw 0x04d958000377f000 0x0136560000ddfc00 0xe7fffc0003fff002 0xf9ffff0000fffc00

def z1412 : W := mkw 0x02bb00fc8aec0f03 0x80aec03f22bb03c0 0xffff80ffcffe0f83 0x7fffe03ff3ff83e0

def z1413 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x59fe70f1f0000001 0x167f9c3c7c000000

def z1414 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x7bfe73e9cc013a4f 0xdeff9cfa73004e93

def z1415 : W := mkw 0xc044ff03fd13f0fc 0x70113fc0ff44fc3f 0x08007f01fc01f07c 0x82001fc07f007c1f

def z1416 : W := mkw 0x0defefdfbc127000 0x037bfbf7ef049c00 0xf9fffffffc003001 0xfe7fffffff000c00

def z1417 : W := mkw 0x05d9cd000266d000 0x017673400099b400 0xc5ff8c0003fec000 0x317fe30000ffb000

def z1418 : W := mkw 0x45ddff037777f0f4 0x51777fc0ddddfc3d 0xefffff01fffff07e 0xfbffffc07ffffc1f

def z1419 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xe7ffff0003fff38e 0xf9ffffc000fffce3

def z1420 : W := mkw 0x006058b161818860 0x4018162c58606218 0xfcf07cf1f381c873 0xbf3c1f3c7ce0721c

def z1421 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x67fe700003b80002 0x59ff9c0000ee0000

def z1422 : W := mkw 0x027058b163c98f63 0xc09c162c58f263d8 0xfcf07cf1f3c1cff3 0xbf3c1f3c7cf073fc

def z1423 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff1003fffc03 0xf9ffffc400ffff00

def z1424 : W := mkw 0x0050582163c18c62 0x4014160858f06318 0x04000c0033c1cc72 0x010003000cf0731c

def z1425 : W := mkw 0x82bb00fc8aec0f0b 0xa0aec03f22bb03c2 0xf7ff80fe0ffe0f8f 0x7dffe03f83ff83e3

def z1426 : W := mkw 0x40afa7de9c025094 0x102be9f7a7009425 0xfbfffffffc47ffff 0xfeffffffff11ffff

def z1427 : W := mkw 0x05dd7a016375a060 0x41775e8058dd6818 0x4dfe7c01f3b9c070 0x937f9f007cee701c

def z1428 : W := mkw 0x00eb48dd20000000 0x003ad23748000000 0xf9fe7cf1f0000001 0xbe7f9f3c7c000000

def z1429 : W := mkw 0x498fa74e9c025094 0x1263e9d3a7009425 0x010f830e0c060180 0x4043e0c383018060

def z1430 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x51fff0efc0000000 0x547ffc3bf0000000

def z1431 : W := mkw 0x00d9480002640000 0x0036520000990000 0xe7fffc0003fe0002 0xf9ffff0000ff8000

def z1432 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff0033fff032 0xf9ffffc00cfffc0c

def z1433 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x120000fe00460f83 0x0480003f801183e0

def z1434 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc47cff3 0xfeffffffff11f3fc

def z1435 : W := mkw 0xc02285fbfc8a5eff 0x7008a17eff2297bf 0xba018ffffc47ffff 0xee8063ffff11ffff

def z1436 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x47fe700003fe0002 0x11ff9c0000ff8000

def z1437 : W := mkw 0x45ddff000377f094 0x11777fc000ddfc25 0xe7ffff0003fff07e 0xf9ffffc000fffc1f

def z1438 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f0400c03 0xbe3c1f3c7c100300

def z1439 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa018f1e3c47ffff 0xea8063c78f11ffff

def z1440 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0e7fe9cff9fa4f 0xffc39ffa73fe7e93

def z1441 : W := mkw 0x0040480000000000 0x0010120000000000 0xe0f07c000041c002 0xb83c1f0000107000

def z1442 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff103ffffc7f 0xfbffffc40fffff1f

def z1443 : W := mkw 0x09efefdda8025000 0x027bfbf76a009400 0xf3ffffe1c047f002 0xfcfffff87011fc00

def z1444 : W := mkw 0x80666ad9a8182209 0x20199ab66a060882 0xfbfe7ff9fc38320d 0xfeff9ffe7f0e0c83

def z1445 : W := mkw 0x85cfef48883e7209 0x2173fbd2220f9c82 0xfbffffe9cc3e320d 0xfefffffa730f8c83

def z1446 : W := mkw 0x05d9dd000377f000 0x0176774000ddfc00 0xe7ff8c0003fff002 0x79ffe30000fffc00

def z1447 : W := mkw 0xc9efefdfbc1a729d 0x327bfbf7ef069ca7 0xfbfffffffc3e338d 0xfeffffffff0f8ce3

def z1448 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc40c431 0xfe7fffffff10310c

def z1449 : W := mkw 0x05ddff004377f040 0x41777fc010ddfc10 0xefffff01c3fff042 0xfbffffc070fffc10

def z1450 : W := mkw 0x8010102043d9aa49 0x6004040810f66a92 0x0600000003f9fa4e 0x0180000000fe7e93

def z1451 : W := mkw 0x00447a0001112000 0x00111e8000444800 0xe7fe7f0003b93002 0xf9ff9fc000ee4c00

def z1452 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xffff80fe0ffe0fcf 0x7fffe03f83ff83f3

def z1453 : W := mkw 0x01cd7a0001112000 0x00735e8000444800 0x45fe700003b80000 0x117f9c0000ee0000

def z1454 : W := mkw 0x002622d888000000 0x000988b622000000 0xf9fe73f9cc000001 0xfe7f9cfe73000000

def z1455 : W := mkw 0x0966efdfbc000000 0x0259bbf7ef000000 0xf8f07ffffc000001 0xbe3c1fffff000000

def z1456 : W := mkw 0x0020009000000000 0x0008002400000000 0xf0f000f000400c03 0x3c3c003c00100300

def z1457 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x45fe7c0003b8c000 0x117f9f0000ee3000

def z1458 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc01fa7f 0xfeffffffff007e9f

def z1459 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x45fff00003be0000 0x117ffc0000ef8000

def z1460 : W := mkw 0x89efefdfbc182209 0x227bfbf7ef060882 0xf9fffffffc380001 0xfe7fffffff0e0000

def z1461 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xffffffffffb80003 0xffffffffffee0000

def z1462 : W := mkw 0x80667af9e9992a49 0x60199ebe7a664a92 0xfffe7ff9fff9fe7f 0xffff9ffe7ffe7f9f

def z1463 : W := mkw 0x89efefdfbc182209 0x227bfbf7ef060882 0xfbfffffffc393a4f 0xfeffffffff0e4e93

def z1464 : W := mkw 0x009d320003752000 0x00274c8000dd4800 0x45fe700003b80000 0x117f9c0000ee0000

def z1465 : W := mkw 0x05ddef000266d000 0x01777bc00099b400 0xe7ffff0003fec002 0xf9ffffc000ffb000

def z1466 : W := mkw 0x0ddd7a01ab75a000 0x03775e806add6800 0x45fe7001c3b80000 0x117f9c0070ee0000

def z1467 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef07ff1f3c1fc73 0xffbc1ffc7cf07f1c

def z1468 : W := mkw 0x89efefdfbc102008 0x227bfbf7ef040802 0xf9fffffffc00300d 0xfe7fffffff000c03

def z1469 : W := mkw 0xc82285fffc8a5add 0x7208a17fff2296b7 0xba018ffffc47ffff 0xee8063ffff11ffff

def z1470 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x320000fe00000f83 0x4c80003f800003e0

def z1471 : W := mkw 0x022200fc40880f43 0xc088803f102203d0 0x180000ffc0000fc1 0x0600003ff00003f0

def z1472 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0x100000e000000f80 0x04000038000003e0

def z1473 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff1603fff582 0xf9ffffc580fffd60

def z1474 : W := mkw 0x8befefdfbc3c2309 0xa2fbfbf7ef0f08c2 0xfbfffffffc3e338d 0xfeffffffff0f8ce3

def z1475 : W := mkw 0x02b900b402ec0f03 0x80ae402d00bb03c0 0xe7ff801603fe0f82 0x79ffe00580ff83e0

def z1476 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003800c70 0x0100000000e0031c

def z1477 : W := mkw 0x00666ad9a8000000 0x00199ab66a000000 0xfbfe7ff9fc41fe7f 0xfeff9ffe7f107f9f

def z1478 : W := mkw 0x0210102043e58d62 0xc084040810f96358 0x0400000003c7cdf2 0x0100000000f1f37c

def z1479 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x5cf07cf1f381cc71 0x973c1f3c7ce0731c

def z1480 : W := mkw 0x022285fe14880f03 0x8088a17f852203c0 0xb8018ffe3c000f81 0xee0063ff8f0003e0

def z1481 : W := mkw 0x0210102043ed8f63 0xc084040810fb63d8 0xae018c1e33ffcff3 0xeb8063078cfff3fc

def z1482 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0xff0ff3ffcfb93a4f 0xffc3fcfff3ee4e93

def z1483 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x98f07cf1f041cc71 0xa63c1f3c7c10731c

def z1484 : W := mkw 0x01ddff0003658000 0x00777fc000d96000 0xe7ffff0003ffc002 0xf9ffffc000fff000

def z1485 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x5f0e73e9cfb83a4d 0x57c39cfa73ee0e93

def z1486 : W := mkw 0x0099000002640000 0x0026400000990000 0xefff8c1033ffcc73 0xfbffe3040cfff31c

def z1487 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe5fffc0003ffc002 0xb97fff0000fff000

def z1488 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff1e03fff003 0xf9ffffc780fffc00

def z1489 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef07cf1f3c7cff3 0xbfbc1f3c7cf1f3fc

def z1490 : W := mkw 0x4dddff03bf77f094 0x13777fc0efddfc25 0xefffff1fffffffff 0xfbffffc7ffffffff

def z1491 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf1fcfff3c1cc73 0xff3c7f3ffcf0731c

def z1492 : W := mkw 0x0bef6adda82c0301 0x82fbdab76a0b00c0 0x51fe70e1c0380000 0x147f9c38700e0000

def z1493 : W := mkw 0x0060489120000000 0x0018122448000000 0xf0f070f1c0000001 0x3c3c1c3c70000000

def z1494 : W := mkw 0x00d9580003658000 0x0036560000d96000 0xeffffc1e33ffcff3 0xfbffff078cfff3fc

def z1495 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x51fe7ce1f0000000 0x147f9f387c000000

def z1496 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc060181 0xfe7fffffff018060

def z1497 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x59fff3fffc000001 0x567ffcffff000000

def z1498 : W := mkw 0x0dddff03bf77f000 0x03777fc0efddfc00 0xefffff1ffffff003 0xfbffffc7fffffc00

def z1499 : W := mkw 0x05dd7a000377f000 0x01775e8000ddfc00 0x45fe700003fec000 0x117f9c0000ffb000

def z1500 : W := mkw 0x059d220002742000 0x01674880009d0800 0x45fe000003b80000 0x117f800000ee0000

def z1501 : W := mkw 0x8210102043fd2f4b 0xe084040810ff4bd2 0x0400000003b80000 0x0100000000ee0000

def z1502 : W := mkw 0x0a2200fffc880f63 0xc288803fff2203d8 0x180000fffc000ff1 0x0600003fff0003fc

def z1503 : W := mkw 0x059db7000377f000 0x01676dc000ddfc00 0x070f830003be3000 0x41c3e0c000ef8c00

def z1504 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xf9fffffffc00300d 0xfe7fffffff000c03

def z1505 : W := mkw 0x0010102043c18c62 0x4004040810f06318 0x0400000003c1c002 0x0100000000f07000

def z1506 : W := mkw 0x0befefdfbc2c0301 0x82fbfbf7ef0b00c0 0xfbfffffffc7e0f83 0xfeffffffff1f83e0

def z1507 : W := mkw 0x4544ff037513f0f4 0x51513fc0dd44fc3d 0x08007f01fc01f07c 0x82001fc07f007c1f

def z1508 : W := mkw 0x859fb768cbfffa49 0x6167edda32fffe92 0x070f83080ffffa4e 0x41c3e0c203fffe93

def z1509 : W := mkw 0x009d320003752000 0x00274c8000dd4800 0x67fe730003b93002 0xd9ff9cc000ee4c00

def z1510 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0x54f07ce1f380c030 0x153c1f387ce0300c

def z1511 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0xb00180fe00000f81 0x6c00603f800003e0

def z1512 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x77ff80ee03be0b83 0x5dffe03b80ef82e0

def z1513 : W := mkw 0x45dd7a000377f094 0x11775e8000ddfc25 0x47fe700003fffffe 0x11ff9c0000ffffff

def z1514 : W := mkw 0x4210102043efdff7 0xd084040810fbf7fd 0x0600000003fffffe 0x0180000000ffffff

def z1515 : W := mkw 0x0210102043ed8f63 0xc084040810fb63d8 0x0400000003f9cc72 0x0100000000fe731c

def z1516 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80f603fe0582 0x7dffe03d80ff8160

def z1517 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f0000c71 0xbe3c1f3c7c00031c

def z1518 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc060381 0xfeffffffff0180e0

def z1519 : W := mkw 0x0862cddfbc000000 0x0218b377ef000000 0xf8f1fffffc000001 0xfe3c7fffff000000

def z1520 : W := mkw 0x0defefdfbc265000 0x037bfbf7ef099400 0xf9fffffffc060001 0xfe7fffffff018000

def z1521 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xe7ffff0e0ffff002 0xf9ffffc383fffc00

def z1522 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0xedfe7c1033f9cc73 0xbb7f9f040cfe731c

def z1523 : W := mkw 0x822200fcc8880f4b 0xe088803f322203d2 0x180000e9cc000a4d 0x0600003a73000293

def z1524 : W := mkw 0x09ef6adda8000000 0x027bdab76a000000 0x79fe70e1c0000001 0x9e7f9c3870000000

def z1525 : W := mkw 0x0410952043f7fc62 0x4104254810fdff18 0xae018f1033fffc73 0xeb8063c40cffff1c

def z1526 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xefffff1e3fffff83 0xfbffffc78fffffe0

def z1527 : W := mkw 0x0099000002640000 0x0026400000990000 0xe7ff800003fe0f82 0x79ffe00000ff83e0

def z1528 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xfffff0ffc3fe0f83 0xfffffc3ff0ff83e0

def z1529 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0x45fe730003b83000 0x117f9cc000ee0c00

def z1530 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff0803fffa03 0xf9ffffc200fffe80

def z1531 : W := mkw 0x4544ff021513f094 0x11513fc08544fc25 0x00007f003001f030 0x80001fc00c007c0c

def z1532 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x59fe7ffffc000001 0x967f9fffff000000

def z1533 : W := mkw 0x00ebcddf34000000 0x003af377cd000000 0xf9fffffffc000001 0xfe7fffffff000000

def z1534 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xc5fffc1633fec5b0 0x317fff058cffb16c

def z1535 : W := mkw 0x0dddff061777f000 0x03777fc185ddfc00 0xe7ffff0603fff002 0xf9ffffc180fffc00

def z1536 : W := mkw 0x00547a000351a000 0x00151e8000d46800 0x45fe700003b80000 0x117f9c0000ee0000

def z1537 : W := mkw 0x802200f9e8880e6b 0x6008803e7a22039a 0xba000ff9fc41fe7f 0xee8003fe7f107f9f

def z1538 : W := mkw 0x00ef6adda8000000 0x003bdab76a000000 0xf9fffffffc000001 0xfe7fffffff000000

def z1539 : W := mkw 0x45d9cd021666d094 0x117673408599b425 0xe7ff8c1e33fecfb3 0x79ffe3078cffb3ec

def z1540 : W := mkw 0x05dd7a016375a060 0x41775e8058dd6818 0x45fe7001c3b80000 0x117f9c0070ee0000

def z1541 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffcf7f0000001 0xbe7fff3dfc000000

def z1542 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef1ffffffc7ffff 0xffbc7ffffff1ffff

def z1543 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0x57ff80fe03be0f81 0x55ffe03f80ef83e0

def z1544 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc46f7bd 0xfeffffffff11bdef

def z1545 : W := mkw 0x059da70002767000 0x016769c0009d9c00 0x47ff830003be3000 0x51ffe0c000ef8c00

def z1546 : W := mkw 0x422200ff74880ff7 0xd088803fdd2203fd 0x180000fffc000ffd 0x0600003fff0003ff

def z1547 : W := mkw 0x09efefdfbc000422 0x027bfbf7ef000108 0xf9fffffffc000431 0xfe7fffffff00010c

def z1548 : W := mkw 0x05edef9120367000 0x017b7be4480d9c00 0xfbfffff1f03e3001 0xfefffffc7c0f8c00

def z1549 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xefffff1e0fffffcf 0xfbffffc783fffff3

def z1550 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xe7ffff1633fff002 0xf9ffffc58cfffc00

def z1551 : W := mkw 0x4010102043c18cf6 0x5004040810f0633d 0x0400000003c1cffe 0x0100000000f073ff

def z1552 : W := mkw 0x85ddff00cb77f048 0x61777fc032ddfc12 0xe7ffff01c3fff002 0xf9ffffc070fffc00

def z1553 : W := mkw 0x0099000002640000 0x0026400000990000 0xefff83080fff3a4f 0xfbffe0c203ffce93

def z1554 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfef07cf9f3c1ce73 0xffbc1f3e7cf0739c

def z1555 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff0e0ffffbcf 0xfbffffc383fffef3

def z1556 : W := mkw 0x022200fd60880f63 0xc088803f582203d8 0x180000f1f0000c71 0x0600003c7c00031c

def z1557 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xfbfffffffc013003 0xfeffffffff004c00

def z1558 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe7ffff080ffff20e 0xf9ffffc203fffc83

def z1559 : W := mkw 0x05ddff000377f000 0x01777fc000ddfc00 0xe5fe7f0003f9f002 0xb97f9fc000fe7c00

def z1560 : W := mkw 0x006248d9a8000000 0x001892366a000000 0xf8f07cf9fc000001 0xbe3c1f3e7f000000

def z1561 : W := mkw 0x02bb00fd22ec0f23 0x80aec03f48bb03c8 0xf7ff80fe33fe0fb3 0x7dffe03f8cff83ec

def z1562 : W := mkw 0x0a2200fe9c880f03 0x8288803fa72203c0 0x100000fe0c000f81 0x0400003f830003e0

def z1563 : W := mkw 0x89ef6adda8182209 0x227bdab76a060882 0x51fe70e1c0380000 0x147f9c38700e0000

def z1564 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff1633fffdf3 0xfbffffc58cffff7c

def z1565 : W := mkw 0x01ddef0002640000 0x00777bc000990000 0xe5ffff0003b80000 0xf97fffc000ee0000

def z1566 : W := mkw 0x09ef6adfbc000000 0x027bdab7ef000000 0x79fe73fffc000001 0xde7f9cffff000000

def z1567 : W := mkw 0x0defefdfbc02d000 0x037bfbf7ef00b400 0xf9fffffffc00c001 0xfe7fffffff003000

def z1568 : W := mkw 0x09efefdfbc025000 0x027bfbf7ef009400 0xf9fffffffc01f001 0xfe7fffffff007c00

def z1569 : W := mkw 0x007058b163c18c62 0x401c162c58f06318 0xfcf07ff1ffc1fc7f 0xbf3c1ffc7ff07f1f

def z1570 : W := mkw 0x09ffefdfbe640000 0x027ffbf7ef990000 0xfffffffffffe0f83 0xffffffffffff83e0

def z1571 : W := mkw 0x059db70003777000 0x01676dc000dddc00 0xe7fff30003ff3002 0xf9fffcc000ffcc00

def z1572 : W := mkw 0x4099000002665094 0x1026400000999425 0xe7ff800003fffffe 0x79ffe00000ffffff

def z1573 : W := mkw 0x059da70002767000 0x016769c0009d9c00 0xe7ff8f0003fff002 0xf9ffe3c000fffc00

def z1574 : W := mkw 0x0164ef9120000000 0x00593be448000000 0xf8f07ff1f0000001 0xbe3c1ffc7c000000

def z1575 : W := mkw 0x0099000002640000 0x0026400000990000 0x67fe000003b80002 0x59ff800000ee0000

def z1576 : W := mkw 0x80063268c9992a49 0x60018c9a32664a92 0x7d0e73e9cfb9304d 0xdf439cfa73ee4c13

def z1577 : W := mkw 0x02eb48dd202c0301 0x80bad237480b00c0 0xfbfffcfff03e0381 0xfeffff3ffc0f80e0

def z1578 : W := mkw 0x40ebcddf34025094 0x103af377cd009425 0xfbfffffffc47ffff 0xfeffffffff11ffff

def z1579 : W := mkw 0x00dd7a000375a000 0x00375e8000dd6800 0xe7ffff0003fff002 0xf9ffffc000fffc00

def z1580 : W := mkw 0x0060489120000000 0x0018122448000000 0xf8f07cf1f0010843 0xbe3c1f3c7c004210

def z1581 : W := mkw 0x022200fc00880f03 0x8088803f002203c0 0xb00000fe00400f83 0x2c00003f801003e0

def z1582 : W := mkw 0x0099850002665000 0x0026614000999400 0xe7ff830003fe3002 0x79ffe0c000ff8c00

def z1583 : W := mkw 0x04547a000377f000 0x01151e8000ddfc00 0xe7fe7f0003fff002 0xf9ff9fc000fffc00

def z1584 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0xf9fffffffc460581 0xfe7fffffff118160

def z1585 : W := mkw 0x09ebcddf34000000 0x027af377cd000000 0xf9fffcfff0000001 0xfe7fff3ffc000000

def z1586 : W := mkw 0x0060489120000000 0x0018122448000000 0x78f070e1c0000001 0x9e3c1c3870000000

def z1587 : W := mkw 0x0099000002665000 0x0026400000999400 0xe7ff800003fff002 0x79ffe00000fffc00

def z1588 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xe7ffff1e0fffff8f 0xf9ffffc783ffffe3

def z1589 : W := mkw 0x007058b163c98e63 0x401c162c58f26398 0xfef07cf1f3f9ce73 0xbfbc1f3c7cfe739c

def z1590 : W := mkw 0x05dd7a000375a000 0x01775e8000dd6800 0x45fe7c0003b9c000 0x917f9f0000ee7000

def z1591 : W := mkw 0x02bb00fc02ec0f03 0x80aec03f00bb03c0 0xf7ff80ee03fe0382 0x7dffe03b80ff80e0

def z1592 : W := mkw 0x05ddff016377f060 0x41777fc058ddfc18 0xe7ffff01c3fff002 0xf9ffffc070fffc00

def z1593 : W := mkw 0x0964ef93bc000000 0x02593be4ef000000 0x58f07fe1fc000000 0x963c1ff87f000000

def z1594 : W := mkw 0x85ddff00cb77f048 0x61777fc032ddfc12 0xefffff09cffffa4f 0xfbffffc273fffe93

def z1595 : W := mkw 0x05ddff021777f000 0x01777fc085ddfc00 0xefffff1e3ffffa4f 0xfbffffc78ffffe93

def z1596 : W := mkw 0x09efefdfbc000000 0x027bfbf7ef000000 0x79fff3efcc000001 0xde7ffcfbf3000000

def z1597 : W := mkw 0x8410102043fdaa49 0x6104040810ff6a92 0x0400000003b80000 0x0100000000ee0000

def z1598 : W := mkw 0x49efefdfbc025094 0x127bfbf7ef009425 0xfbfffffffc07f3fd 0xfeffffffff01fcff

def z1599 : W := mkw 0x0099000002640000 0x0026400000990000 0xe5ff800003b80000 0x797fe00000ee0000

def z1600 : W := mkw 0x45ddff021777f094 0x11777fc085ddfc25 0xefffff1e3ffff5b3 0xfbffffc78ffffd6c

def z1601 : W := mkw 0x00eb48dd20000000 0x003ad23748000000 0xfbfffcfff047cff3 0xfeffff3ffc11f3fc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z5,z6]),(0,[z8,z2,z9,z3,z4,z5,z6]),(0,[z2,z10,z3,z11,z12,z5,z6]),(0,[z13,z2,z3,z4,z12,z5,z14])],[(0,[z3,z4,z11,z12,z15,z5,z6]),(0,[z2,z3,z4,z16,z5,z17,z6]),(0,[z18,z2,z3,z4,z12,z5,z6])],[(0,[z8,z2,z3,z4,z19,z5,z6])],[(0,[z20,z2,z3,z12,z5,z21,z6]),(0,[z22,z2,z3,z12,z5,z23,z6])],[(1,[z2,z3,z4,z5,z24,z6]),(0,[z8,z25,z2,z3,z4,z5,z6]),(0,[z25,z2,z3,z12,z5,z23,z6]),(0,[z26,z2,z3,z4,z27,z5,z6])],[(0,[z28,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z16,z5,z6,z29])],[(0,[z30,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z31,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(1,[z2,z3,z4,z5,z33,z6])],[(0,[z8,z2,z3,z34,z4,z5,z6]),(1,[z2,z10,z3,z16,z5,z6]),(0,[z2,z35,z3,z12,z5,z23,z6]),(0,[z2,z36,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z16,z37,z5,z6])],[(0,[z38,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z14,z39]),(0,[z2,z3,z4,z12,z5,z6,z40]),(0,[z2,z3,z4,z12,z5,z6,z41]),(0,[z2,z3,z4,z12,z5,z42,z6])],[(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z43,z3,z4,z12,z5,z44,z6]),(1,[z2,z3,z12,z5,z45,z6]),(0,[z46,z2,z3,z4,z12,z5,z6]),(0,[z26,z2,z3,z4,z12,z23,z6]),(0,[z2,z3,z12,z47,z5,z23,z6]),(0,[z2,z48,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z49,z16,z5,z6]),(0,[z2,z3,z12,z50,z5,z51,z6])],[(0,[z2,z3,z4,z12,z5,z44,z6]),(0,[z13,z3,z4,z12,z5,z14,z6]),(0,[z2,z10,z3,z52,z12,z5,z6]),(1,[z2,z3,z53,z12,z5,z6]),(0,[z54,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z47,z5,z6])],[(1,[z25,z3,z4,z12,z15,z6]),(0,[z2,z55,z3,z4,z16,z5,z6])],[(0,[z8,z2,z3,z4,z5,z6,z56])],[(0,[z2,z3,z4,z12,z5,z45,z6])],[(0,[z57,z3,z58,z4,z12,z5,z6]),(0,[z2,z59,z3,z4,z12,z5,z6]),(0,[z2,z3,z60,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z61]),(0,[z62,z2,z3,z4,z12,z5,z6])],[]],
   [[],[(0,[z63,z2,z3,z4,z12,z50,z6])],[(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z66])],[(0,[z2,z3,z4,z12,z67,z5,z6]),(0,[z2,z68,z4,z12,z5,z69,z6]),(0,[z2,z3,z11,z12,z5,z23,z6]),(0,[z2,z3,z4,z12,z65,z5,z39])],[(0,[z63,z1,z2,z3,z4,z5,z6]),(1,[z2,z70,z4,z7,z5,z6])],[(1,[z2,z3,z4,z71,z5,z6]),(0,[z2,z3,z4,z12,z5,z72,z6]),(0,[z2,z3,z34,z4,z12,z47,z6])],[(0,[z1,z2,z68,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z73]),(1,[z2,z3,z12,z5,z74,z6])],[(0,[z8,z2,z3,z75,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z24,z6])],[(1,[z8,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z76,z5,z6]),(0,[z2,z77,z3,z12,z78,z5,z6])],[(0,[z2,z9,z3,z12,z5,z44,z6]),(0,[z2,z3,z4,z12,z5,z33,z6]),(0,[z2,z3,z4,z12,z5,z6,z79]),(0,[z2,z80,z9,z3,z12,z5,z6]),(0,[z2,z9,z3,z12,z47,z5,z6])],[(0,[z2,z3,z81,z12,z5,z23,z6]),(0,[z2,z3,z82,z4,z12,z5,z6]),(0,[z83,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z84,z6]),(0,[z2,z85,z4,z19,z12,z5,z6]),(1,[z2,z86,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z5,z39,z6]),(0,[z63,z2,z3,z4,z12,z42,z6])],[(0,[z57,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z87,z6]),(0,[z2,z3,z34,z12,z5,z88,z6]),(0,[z2,z3,z4,z12,z89,z5,z6])],[(0,[z90,z2,z3,z12,z5,z6,z61]),(0,[z91,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z21,z6,z92]),(0,[z2,z93,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z6,z94]),(0,[z3,z4,z12,z5,z17,z6,z95])],[(0,[z2,z3,z4,z15,z5,z42,z6])],[(0,[z2,z3,z4,z96,z12,z5,z6]),(0,[z2,z97,z3,z12,z5,z23,z6]),(0,[z2,z98,z3,z4,z12,z5,z6]),(0,[z22,z2,z3,z4,z16,z5,z6])]],
   [[(0,[z8,z2,z3,z4,z50,z5,z6]),(0,[z25,z2,z3,z4,z16,z5,z6]),(1,[z2,z3,z99,z12,z5,z6]),(0,[z100,z2,z3,z12,z5,z23,z6]),(0,[z2,z101,z3,z4,z5,z42,z6])],[(0,[z8,z2,z3,z4,z5,z6,z102]),(0,[z103,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z104,z5,z6])],[(0,[z2,z3,z105,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z5,z6,z61]),(0,[z2,z3,z4,z12,z5,z106,z6])],[(0,[z1,z2,z9,z3,z12,z5,z6]),(0,[z2,z107,z3,z34,z12,z5,z6])],[(0,[z2,z108,z109,z3,z12,z5,z6]),(0,[z2,z3,z110,z4,z12,z5,z6])],[(0,[z2,z3,z111,z4,z12,z5,z6]),(0,[z112,z2,z3,z4,z12,z5,z6]),(1,[z2,z3,z113,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z114,z6])],[(0,[z115,z2,z3,z116,z12,z5,z6]),(0,[z2,z10,z3,z116,z12,z5,z6]),(0,[z2,z3,z4,z12,z32,z5,z6]),(1,[z8,z2,z10,z3,z5,z6]),(0,[z2,z3,z4,z12,z5,z117,z6]),(0,[z118,z2,z3,z4,z12,z5,z6]),(0,[z2,z85,z4,z12,z119,z5,z6]),(0,[z2,z3,z120,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z65,z5,z6])],[(0,[z121,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z14,z6]),(0,[z2,z4,z12,z119,z5,z69,z6]),(0,[z122,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z123,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z39,z6])],[(0,[z2,z3,z4,z12,z71,z5,z6]),(0,[z2,z3,z34,z124,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z88,z6])],[(0,[z2,z3,z4,z12,z125,z5,z6]),(0,[z8,z2,z3,z4,z126,z5,z6]),(0,[z2,z127,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z128,z12,z5,z6]),(0,[z2,z3,z4,z47,z5,z42,z6]),(1,[z2,z3,z52,z12,z5,z21]),(0,[z2,z129,z3,z4,z12,z5,z6])],[(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z12,z5,z6])],[(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z85,z4,z12,z5,z6]),(0,[z130,z2,z3,z131,z12,z5,z6]),(0,[z2,z3,z4,z132,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z133]),(0,[z134,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z135,z12,z5,z6]),(0,[z2,z136,z3,z12,z5,z69,z6]),(0,[z137,z2,z3,z34,z12,z5,z6])],[(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z2,z3,z138,z4,z12,z5,z6]),(0,[z2,z3,z4,z139,z119,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z140]),(0,[z2,z3,z4,z12,z5,z6,z61]),(0,[z2,z3,z34,z141,z12,z5,z6])],[(0,[z2,z142,z3,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z143]),(0,[z8,z2,z109,z3,z4,z5,z6]),(0,[z2,z3,z4,z15,z5,z33,z6]),(0,[z2,z3,z4,z144,z12,z5,z6]),(0,[z2,z3,z34,z34,z12,z5,z6])]],
   [[(0,[z2,z3,z4,z12,z145,z5,z6]),(0,[z2,z55,z10,z3,z12,z5,z6]),(0,[z2,z3,z34,z4,z5,z42,z6]),(0,[z2,z146,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z5,z42,z17,z6])],[(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z147,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z148,z4,z12,z5,z6]),(0,[z2,z55,z3,z12,z5,z23,z6]),(0,[z2,z3,z4,z5,z42,z149,z6]),(0,[z2,z3,z4,z12,z65,z5,z6])],[(0,[z150,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z114,z69,z6])],[(0,[z115,z2,z151,z4,z12,z5,z6]),(0,[z8,z2,z3,z4,z47,z5,z6]),(0,[z8,z2,z3,z152,z4,z5,z6]),(0,[z2,z9,z3,z152,z12,z5,z6]),(0,[z153,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z154,z12,z5,z6]),(0,[z2,z3,z4,z12,z155,z5,z6])],[(0,[z156,z2,z3,z4,z12,z5,z6]),(0,[z63,z2,z9,z3,z12,z5,z6]),(0,[z2,z157,z85,z4,z12,z5,z6]),(0,[z91,z2,z3,z12,z5,z6,z92]),(0,[z2,z158,z3,z4,z12,z5,z6]),(0,[z3,z4,z12,z5,z159,z42,z6])],[(0,[z2,z3,z81,z4,z16,z5,z6]),(0,[z2,z9,z3,z12,z5,z39,z6]),(0,[z160,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z161,z4,z12,z5,z6]),(0,[z130,z162,z3,z4,z12,z5,z6])],[(0,[z25,z3,z58,z4,z12,z5,z6]),(0,[z2,z163,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z164,z12,z5,z6]),(0,[z2,z3,z4,z165,z12,z5,z6]),(0,[z2,z166,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z167,z6])],[(0,[z2,z3,z12,z5,z168,z23,z6])],[(0,[z2,z3,z4,z169,z12,z5,z6])],[(0,[z2,z9,z10,z4,z12,z5,z6])],[(0,[z2,z3,z12,z170,z5,z23,z6]),(0,[z2,z97,z3,z4,z16,z5,z6]),(0,[z2,z171,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z172,z6])],[(0,[z2,z3,z4,z126,z12,z5,z6]),(0,[z100,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z173])],[(0,[z2,z9,z3,z12,z5,z6,z61]),(0,[z2,z3,z174,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z175,z5,z6]),(0,[z2,z3,z4,z5,z14,z6,z176]),(0,[z2,z3,z4,z12,z177,z5,z6]),(0,[z2,z3,z4,z12,z5,z29,z102]),(0,[z2,z3,z12,z5,z23,z178,z6]),(0,[z179,z2,z3,z12,z5,z23,z6])],[(0,[z2,z180,z3,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z6,z181])]],
   [[(0,[z2,z3,z182,z4,z12,z5,z6]),(1,[z2,z3,z4,z183,z5,z6])],[(0,[z2,z9,z3,z12,z65,z5,z6]),(0,[z2,z3,z4,z184,z12,z5,z6]),(0,[z2,z4,z7,z12,z78,z5,z6]),(0,[z2,z3,z4,z12,z5,z185,z6]),(0,[z2,z3,z4,z12,z5,z6,z95]),(0,[z2,z3,z4,z12,z39,z6,z102])],[(0,[z2,z3,z4,z12,z186,z5,z6]),(0,[z2,z97,z3,z4,z5,z17,z6])],[(0,[z187,z2,z3,z4,z12,z5,z6]),(0,[z2,z9,z9,z3,z12,z5,z6]),(0,[z2,z9,z3,z124,z12,z5,z6]),(0,[z2,z3,z4,z188,z12,z5,z6]),(0,[z179,z2,z70,z3,z4,z5,z6])],[(0,[z1,z13,z3,z4,z12,z5,z6]),(0,[z90,z2,z3,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z5,z189,z6]),(0,[z22,z2,z10,z3,z12,z5,z6]),(0,[z190,z2,z3,z4,z12,z5,z6]),(0,[z2,z191,z3,z4,z12,z5,z6])],[(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z192,z6]),(0,[z25,z2,z10,z3,z12,z5,z6]),(1,[z2,z3,z4,z139,z5,z6]),(0,[z2,z3,z4,z141,z12,z5,z17])],[(0,[z2,z3,z4,z12,z5,z193,z6]),(0,[z2,z3,z4,z12,z5,z194,z6])],[(0,[z2,z3,z4,z195,z12,z5,z6]),(1,[z28,z2,z4,z12,z69,z6])],[(0,[z115,z2,z3,z81,z12,z5,z6]),(0,[z2,z3,z4,z12,z15,z5,z6]),(0,[z196,z2,z3,z4,z12,z5,z6])],[(0,[z2,z9,z3,z141,z12,z5,z6]),(0,[z197,z3,z4,z12,z5,z17,z6])],[(0,[z115,z2,z3,z12,z5,z23,z6]),(0,[z1,z2,z3,z4,z5,z14,z6]),(0,[z1,z2,z3,z4,z5,z39,z6]),(0,[z2,z9,z3,z34,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z23,z6]),(0,[z2,z3,z12,z5,z198,z23,z6]),(0,[z2,z3,z12,z5,z23,z21,z6])],[(0,[z199,z2,z3,z4,z12,z5,z6]),(0,[z91,z115,z2,z3,z12,z5,z6]),(1,[z13,z3,z4,z12,z5,z14]),(0,[z2,z9,z3,z4,z5,z42,z6])],[(0,[z2,z3,z4,z12,z5,z200,z6]),(0,[z2,z3,z4,z12,z5,z6,z201]),(0,[z130,z202,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z203,z6]),(0,[z2,z3,z12,z5,z6,z204,z29])],[(0,[z3,z58,z4,z11,z12,z5,z6]),(1,[z2,z3,z34,z12,z23,z6]),(0,[z2,z4,z12,z5,z106,z23,z6])],[(0,[z2,z58,z4,z12,z5,z69,z6]),(0,[z2,z3,z4,z12,z5,z6,z143])]],
   [[(1,[z20,z3,z116,z12,z5,z6]),(0,[z8,z2,z3,z4,z5,z117,z6]),(0,[z2,z3,z205,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z206,z6])],[(1,[z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z207])],[(0,[z2,z208,z3,z4,z12,z5,z6]),(0,[z209,z2,z3,z4,z12,z5,z6])],[(1,[z1,z2,z10,z3,z5,z6])],[(0,[z2,z3,z4,z12,z210,z5,z6])],[(0,[z2,z3,z4,z4,z12,z5,z6]),(0,[z2,z3,z81,z4,z211,z5,z6]),(0,[z2,z3,z4,z212,z12,z5,z6]),(1,[z2,z3,z12,z5,z213,z6]),(0,[z2,z55,z3,z4,z5,z17,z6]),(0,[z2,z3,z4,z214,z12,z5,z6])],[(0,[z2,z215,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z216,z5,z6]),(0,[z2,z3,z4,z217,z12,z5,z6]),(1,[z26,z2,z3,z12,z23,z6]),(0,[z2,z3,z4,z12,z5,z218,z6])],[(0,[z130,z2,z3,z12,z5,z23,z6])],[(0,[z8,z2,z3,z4,z5,z6,z61]),(0,[z2,z109,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z92])],[(1,[z8,z3,z4,z11,z5,z6]),(0,[z3,z4,z12,z5,z14,z6,z61]),(0,[z2,z3,z4,z12,z5,z213,z6]),(0,[z2,z108,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z219,z5,z6])],[(0,[z2,z9,z3,z12,z5,z42,z6]),(0,[z2,z3,z4,z12,z220,z5,z6]),(0,[z179,z2,z3,z4,z16,z5,z6])],[(0,[z2,z3,z4,z170,z5,z42,z6]),(0,[z2,z3,z12,z5,z221,z23,z6])],[(0,[z2,z68,z3,z4,z222,z5,z6]),(0,[z91,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z223,z5,z6]),(0,[z2,z3,z4,z5,z42,z224,z6]),(0,[z2,z3,z4,z12,z5,z6,z225])],[(0,[z2,z3,z4,z12,z5,z226,z6]),(0,[z2,z3,z4,z12,z5,z227,z6]),(0,[z228,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z229,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z74,z6]),(0,[z2,z3,z230,z12,z65,z5,z6])],[(0,[z231,z2,z3,z4,z12,z5,z6]),(0,[z43,z2,z3,z232,z12,z5,z6]),(0,[z2,z3,z34,z12,z5,z14,z6]),(0,[z2,z3,z4,z19,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z233,z6]),(1,[z2,z3,z234,z12,z5,z6])],[(0,[z235,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z236,z12,z5,z6]),(0,[z237,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z50,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z238])]],
   [[(0,[z2,z3,z239,z4,z12,z5,z6]),(0,[z8,z2,z68,z3,z4,z5,z6]),(0,[z2,z240,z3,z4,z12,z5,z6]),(1,[z43,z1,z3,z4,z5,z6]),(0,[z2,z97,z10,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z23,z241,z6]),(0,[z2,z3,z4,z16,z5,z6,z102]),(0,[z162,z2,z3,z4,z12,z5,z6])],[(0,[z25,z2,z3,z4,z12,z15,z6]),(0,[z100,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z131,z4,z12,z5,z6])],[(0,[z242,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z234,z12,z5,z6])],[(0,[z2,z3,z243,z4,z12,z5,z6]),(0,[z244,z2,z3,z4,z12,z5,z6]),(0,[z28,z2,z85,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z245]),(0,[z2,z246,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z12,z5,z6]),(0,[z2,z9,z3,z212,z12,z5,z6]),(0,[z247,z2,z3,z4,z12,z5,z29]),(0,[z2,z3,z4,z5,z159,z42,z6])],[(0,[z8,z57,z2,z3,z4,z5,z6]),(0,[z1,z2,z157,z3,z4,z5,z6]),(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z248]),(1,[z249,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z7,z5,z42,z6]),(0,[z2,z3,z4,z250,z12,z5,z6])],[(0,[z2,z3,z4,z251,z12,z5,z6]),(0,[z115,z2,z3,z4,z16,z5,z6]),(0,[z2,z10,z3,z4,z16,z5,z6])],[(0,[z20,z2,z3,z12,z5,z23,z6]),(0,[z252,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z253,z4,z12,z5,z6]),(1,[z254,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z255,z6])],[(0,[z2,z3,z4,z12,z5,z6,z256])],[(0,[z199,z2,z58,z4,z12,z5,z6]),(0,[z2,z3,z257,z4,z12,z5,z6]),(0,[z2,z258,z3,z4,z16,z5,z6])],[(0,[z1,z2,z3,z4,z15,z5,z6]),(0,[z259,z8,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z260,z5,z6]),(0,[z2,z3,z4,z16,z5,z6,z92])],[],[(0,[z2,z261,z3,z4,z12,z5,z6]),(0,[z8,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z262])],[(0,[z2,z3,z4,z12,z263,z5,z6]),(0,[z179,z2,z97,z3,z4,z5,z6]),(0,[z2,z86,z4,z12,z5,z23,z6])],[(0,[z264,z1,z2,z3,z4,z5,z6]),(0,[z2,z265,z3,z4,z12,z5,z6]),(0,[z266,z2,z3,z4,z12,z5,z6]),(0,[z2,z157,z3,z34,z12,z5,z6]),(1,[z2,z267,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z268])]],
   [[(0,[z2,z157,z3,z4,z5,z42,z6]),(0,[z2,z3,z34,z12,z5,z21,z6]),(1,[z2,z3,z4,z16,z50,z6])],[(0,[z269,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z5,z69,z6])],[(0,[z2,z9,z109,z3,z12,z5,z6]),(0,[z270,z2,z3,z34,z12,z5,z6])],[(0,[z2,z271,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z272,z12,z5,z6]),(0,[z130,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z273,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z274,z6]),(0,[z8,z2,z55,z3,z4,z5,z6]),(0,[z8,z2,z3,z34,z12,z5,z6]),(0,[z2,z9,z55,z3,z12,z5,z6]),(0,[z2,z3,z4,z275,z16,z5,z6]),(0,[z130,z2,z3,z4,z12,z6,z102])],[(0,[z199,z3,z4,z12,z5,z44,z6]),(0,[z8,z2,z3,z4,z5,z42,z6]),(0,[z2,z70,z3,z34,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z276,z6]),(0,[z2,z70,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z277,z6]),(0,[z179,z2,z3,z4,z12,z5,z56])],[(0,[z8,z2,z3,z4,z5,z44,z6]),(0,[z25,z2,z3,z4,z12,z44,z6]),(1,[z2,z3,z4,z12,z5,z278])],[(0,[z2,z3,z4,z12,z5,z6,z279])],[(0,[z2,z9,z3,z12,z5,z14,z6]),(0,[z2,z3,z4,z12,z280,z5,z6]),(0,[z70,z249,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z281,z6]),(0,[z2,z93,z3,z4,z12,z5,z6])],[(0,[z3,z81,z4,z116,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z282,z6]),(0,[z2,z10,z3,z16,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z283,z6]),(1,[z2,z3,z4,z16,z42,z6]),(0,[z2,z3,z4,z12,z284,z5,z6])],[(0,[z179,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z56])],[(0,[z285,z2,z3,z4,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z17,z6]),(0,[z2,z101,z3,z4,z12,z5,z6]),(0,[z2,z55,z3,z4,z124,z5,z6]),(0,[z2,z3,z4,z12,z5,z21,z6]),(0,[z286,z2,z3,z4,z12,z5,z6])],[(0,[z2,z80,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z11,z5,z42,z6]),(0,[z26,z2,z3,z12,z5,z23,z6])],[(0,[z287,z2,z3,z4,z12,z5,z6]),(0,[z247,z2,z4,z12,z5,z6,z29])],[(0,[z2,z3,z34,z12,z15,z5,z6]),(0,[z2,z10,z3,z12,z288,z5,z6]),(0,[z179,z2,z10,z3,z12,z5,z6]),(1,[z2,z3,z289,z12,z5,z6]),(0,[z290,z2,z3,z12,z5,z23,z6]),(0,[z63,z2,z3,z34,z12,z5,z6])]],
   [[(0,[z3,z4,z11,z12,z170,z5,z6]),(0,[z2,z10,z3,z12,z5,z6,z29]),(1,[z2,z55,z3,z291,z5,z6]),(0,[z2,z3,z292,z4,z12,z5,z6]),(0,[z2,z107,z3,z4,z12,z5,z6]),(0,[z63,z2,z3,z4,z5,z42,z6])],[(0,[z8,z2,z293,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z294,z6])],[(0,[z2,z3,z4,z12,z5,z278,z6]),(0,[z2,z3,z4,z12,z5,z6,z295])],[(0,[z20,z2,z3,z4,z16,z5,z6]),(0,[z22,z8,z2,z3,z4,z5,z6])],[(0,[z2,z3,z58,z34,z12,z5,z6]),(0,[z8,z2,z3,z4,z5,z24,z6]),(0,[z296,z2,z3,z4,z12,z5,z6]),(1,[z43,z3,z4,z12,z44,z6]),(0,[z2,z3,z4,z260,z5,z14,z6]),(0,[z2,z3,z297,z4,z12,z5,z6]),(0,[z130,z2,z3,z4,z132,z5,z6])],[(0,[z2,z3,z58,z4,z5,z42,z6]),(0,[z2,z3,z152,z12,z5,z23,z6])],[(0,[z20,z2,z3,z116,z12,z5,z6]),(0,[z298,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z299,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z5,z42,z6])],[(0,[z8,z20,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z6])],[(0,[z300,z2,z3,z4,z12,z5,z6]),(1,[z8,z2,z3,z5,z23,z6]),(0,[z2,z9,z3,z12,z280,z5,z6]),(0,[z2,z3,z4,z16,z12,z50,z6])],[(0,[z137,z2,z3,z4,z12,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z301,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z302]),(0,[z2,z3,z4,z12,z303,z5,z6]),(0,[z304,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z52,z4,z12,z5,z21])],[(0,[z305,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z306,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z307,z5,z6]),(0,[z115,z2,z10,z3,z12,z5,z6]),(0,[z2,z10,z3,z81,z12,z5,z6]),(0,[z2,z9,z3,z12,z5,z21,z6]),(0,[z308,z2,z3,z4,z12,z5,z6]),(0,[z2,z10,z10,z3,z12,z5,z6]),(0,[z309,z2,z3,z4,z12,z5,z6])],[(0,[z2,z310,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z311,z12,z5,z6]),(0,[z2,z3,z34,z4,z12,z5,z6])],[(0,[z312,z2,z3,z4,z12,z5,z6]),(0,[z8,z2,z3,z4,z7,z5,z6]),(1,[z2,z3,z232,z12,z5,z6]),(0,[z313,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z314,z6])],[(0,[z2,z70,z3,z4,z7,z5,z6]),(1,[z315,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z16,z5,z6,z56])],[(0,[z316,z2,z3,z4,z16,z5,z6])]],
   [[(0,[z2,z3,z4,z12,z5,z6,z317]),(0,[z2,z10,z3,z12,z5,z6,z318]),(0,[z2,z319,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z102]),(0,[z315,z2,z3,z4,z12,z5,z6])],[(0,[z13,z2,z3,z12,z5,z23,z6]),(0,[z2,z3,z320,z4,z12,z5,z6])],[(0,[z2,z3,z321,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z241,z6]),(0,[z2,z3,z4,z16,z12,z42,z6])],[(1,[z322,z2,z3,z4,z5,z6])],[(0,[z8,z2,z3,z4,z5,z14,z6]),(0,[z8,z2,z3,z4,z5,z39,z6])],[(0,[z13,z25,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z323,z61])],[(0,[z324,z2,z9,z3,z12,z5,z6]),(0,[z28,z2,z9,z3,z12,z5,z6]),(0,[z325,z2,z3,z4,z12,z5,z6])],[(0,[z2,z326,z3,z4,z12,z5,z6])],[(0,[z2,z327,z3,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z5,z6,z302]),(0,[z130,z2,z10,z3,z12,z5,z6]),(0,[z2,z328,z3,z4,z12,z5,z6]),(0,[z2,z86,z3,z12,z5,z23,z6])],[(0,[z2,z3,z4,z12,z5,z6,z329]),(0,[z2,z3,z4,z12,z330,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z6]),(0,[z26,z2,z3,z4,z16,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z2,z9,z3,z12,z15,z5,z6]),(0,[z2,z3,z4,z331,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z332,z6])],[(0,[z91,z2,z3,z4,z12,z5,z21])],[(0,[z2,z333,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z334,z6])],[(0,[z2,z10,z3,z58,z12,z5,z6]),(0,[z335,z2,z3,z4,z12,z5,z6]),(1,[z8,z2,z3,z34,z5,z6]),(0,[z28,z2,z3,z34,z12,z5,z6])],[(0,[z2,z336,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z337,z6]),(0,[z28,z2,z3,z4,z5,z42,z6]),(0,[z2,z109,z4,z12,z119,z5,z6])],[(0,[z338,z2,z3,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z8,z2,z3,z4,z65,z5,z6]),(0,[z2,z9,z4,z19,z12,z5,z6]),(0,[z2,z10,z3,z85,z12,z5,z6]),(0,[z2,z3,z52,z34,z12,z5,z6]),(0,[z2,z3,z4,z12,z339,z5,z6]),(0,[z2,z3,z4,z12,z340,z5,z6])]],
   [[(0,[z100,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z52,z4,z5,z42,z6])],[(0,[z2,z3,z341,z4,z12,z5,z6]),(0,[z2,z3,z152,z4,z16,z5,z6]),(0,[z2,z3,z4,z342,z12,z5,z6])],[],[(0,[z2,z9,z68,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z343,z5,z6]),(0,[z2,z3,z4,z116,z5,z42,z6]),(0,[z2,z10,z3,z12,z5,z6,z92]),(0,[z2,z3,z124,z12,z5,z21,z6]),(0,[z2,z3,z34,z4,z12,z23,z6]),(0,[z2,z344,z3,z4,z12,z5,z6]),(0,[z2,z202,z3,z4,z12,z5,z6]),(1,[z2,z3,z345,z12,z5,z6])],[(0,[z2,z3,z346,z4,z12,z5,z6]),(0,[z130,z2,z3,z4,z12,z5,z102])],[(0,[z1,z13,z2,z3,z4,z5,z6]),(1,[z28,z2,z9,z12,z5,z6]),(0,[z347,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z348,z42,z6])],[(0,[z349,z2,z3,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z291,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z350]),(1,[z2,z3,z4,z27,z5,z6]),(0,[z63,z2,z3,z234,z12,z5,z6])],[(0,[z1,z2,z3,z4,z170,z5,z6]),(0,[z2,z3,z75,z4,z12,z5,z6]),(0,[z2,z9,z3,z4,z12,z5,z6]),(0,[z28,z269,z3,z4,z12,z5,z6]),(0,[z351,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z352,z12,z5,z6]),(0,[z2,z3,z4,z345,z12,z5,z6])],[(0,[z20,z2,z3,z81,z12,z5,z6]),(0,[z20,z2,z10,z3,z12,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z353,z5,z6]),(0,[z2,z3,z152,z4,z5,z17,z6])],[(0,[z57,z2,z9,z3,z12,z5,z6]),(1,[z2,z3,z4,z5,z354,z6]),(0,[z2,z10,z3,z12,z5,z69,z6]),(0,[z2,z3,z12,z5,z5,z23,z6])],[(0,[z2,z9,z4,z12,z119,z5,z6]),(0,[z91,z2,z9,z3,z12,z5,z6]),(1,[z2,z3,z12,z5,z6,z355]),(0,[z91,z2,z3,z124,z12,z5,z6]),(0,[z356,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z357]),(0,[z2,z3,z358,z4,z12,z5,z6]),(0,[z2,z359,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z360,z5,z6]),(0,[z2,z3,z361,z4,z12,z5,z6]),(0,[z179,z2,z3,z4,z5,z6,z56]),(0,[z130,z2,z362,z4,z12,z5,z6])],[],[(0,[z1,z2,z3,z4,z141,z5,z6]),(0,[z43,z2,z3,z12,z5,z23,z6]),(0,[z13,z2,z3,z4,z16,z5,z6])],[(1,[z2,z363,z3,z12,z5,z6]),(0,[z364,z2,z3,z4,z12,z5,z6]),(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z2,z366,z3,z4,z12,z5,z6]),(0,[z2,z3,z34,z19,z12,z5,z6]),(0,[z367,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z355]),(0,[z2,z3,z4,z12,z5,z6,z368]),(0,[z2,z3,z12,z5,z23,z23,z6])],[(0,[z8,z2,z157,z3,z4,z5,z6]),(0,[z2,z9,z157,z3,z12,z5,z6]),(1,[z2,z3,z12,z5,z6,z204]),(0,[z2,z4,z12,z5,z21,z6,z369])]],
   [[(0,[z57,z2,z3,z34,z12,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z112,z2,z3,z12,z5,z23,z6])],[(0,[z57,z2,z3,z4,z5,z42,z6]),(0,[z370,z2,z3,z4,z12,z5,z6]),(0,[z43,z25,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z371,z5,z6]),(0,[z91,z2,z3,z34,z12,z5,z6])],[(0,[z372,z2,z3,z4,z12,z5,z6]),(0,[z91,z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z373,z6]),(1,[z3,z4,z12,z5,z6,z95])],[(0,[z374,z2,z3,z4,z12,z5,z6]),(0,[z2,z68,z3,z34,z12,z5,z6]),(1,[z2,z3,z4,z5,z6,z375]),(0,[z376,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z377,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z178,z6])],[(0,[z2,z68,z3,z4,z5,z42,z6]),(0,[z115,z1,z2,z3,z4,z5,z6]),(0,[z2,z157,z3,z4,z12,z5,z241])],[(0,[z1,z2,z3,z4,z5,z241,z6]),(1,[z1,z2,z3,z5,z23,z6]),(0,[z8,z2,z3,z4,z15,z5,z6]),(0,[z2,z3,z34,z7,z12,z5,z6]),(0,[z247,z2,z3,z12,z5,z23,z6]),(0,[z2,z378,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z16,z5,z44,z6]),(1,[z134,z2,z3,z4,z5,z6]),(0,[z2,z3,z379,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z241,z39]),(0,[z2,z3,z12,z65,z5,z23,z6]),(0,[z2,z3,z4,z16,z47,z5,z6]),(0,[z380,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z381,z6]),(0,[z2,z382,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z383,z5,z6])],[(0,[z2,z3,z4,z211,z12,z5,z6]),(0,[z2,z3,z384,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z385,z5,z6])],[(0,[z2,z109,z58,z4,z12,z5,z6]),(0,[z386,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z19,z12,z5,z6]),(0,[z2,z85,z4,z12,z5,z6,z29]),(0,[z2,z3,z34,z12,z291,z5,z6])],[(0,[z2,z3,z34,z12,z170,z5,z6]),(0,[z387,z2,z3,z4,z12,z5,z6])],[(0,[z2,z68,z85,z4,z12,z5,z6]),(0,[z13,z3,z4,z11,z12,z5,z6])],[(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z2,z3,z4,z12,z389,z5,z6])],[(1,[z2,z59,z3,z12,z5,z6]),(0,[z26,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z390,z5,z6])],[(0,[z2,z391,z3,z4,z12,z5,z6])]],
   [[(0,[z43,z2,z265,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z392]),(0,[z2,z3,z19,z12,z5,z23,z6]),(0,[z2,z3,z205,z12,z119,z5,z6]),(0,[z393,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z394,z4,z16,z5,z6])],[(0,[z1,z2,z3,z384,z4,z5,z6]),(0,[z2,z3,z4,z260,z12,z5,z6]),(0,[z2,z3,z4,z7,z12,z5,z6]),(0,[z2,z395,z3,z4,z12,z5,z6]),(2,[z396,z3,z4,z5,z6])],[(0,[z2,z3,z3,z4,z12,z5,z6]),(0,[z397,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z398,z5,z6])],[(0,[z2,z3,z4,z399,z12,z5,z6]),(0,[z2,z3,z4,z12,z400,z5,z6]),(0,[z2,z109,z3,z4,z12,z119,z6]),(0,[z2,z3,z230,z4,z12,z5,z6])],[],[(0,[z401,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z119,z5,z6]),(0,[z2,z3,z4,z12,z5,z402,z6]),(1,[z2,z3,z4,z141,z5,z17])],[(0,[z2,z9,z58,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z375]),(0,[z2,z10,z3,z12,z5,z6,z56]),(0,[z2,z3,z4,z289,z12,z5,z6]),(0,[z2,z3,z4,z12,z291,z5,z6])],[(0,[z2,z3,z4,z12,z170,z5,z6]),(0,[z2,z3,z4,z12,z5,z403,z6])],[(0,[z0,z2,z3,z4,z12,z5,z6]),(1,[z2,z3,z205,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z404,z6])],[(0,[z2,z3,z4,z12,z5,z5,z6]),(0,[z43,z2,z3,z4,z16,z5,z6]),(0,[z2,z9,z3,z19,z12,z5,z6]),(0,[z2,z3,z34,z12,z5,z241,z6])],[(0,[z115,z2,z405,z4,z12,z5,z6]),(1,[z1,z2,z3,z34,z5,z6]),(1,[z2,z328,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z406,z5,z6]),(1,[z2,z3,z5,z23,z42,z6]),(0,[z2,z3,z407,z34,z12,z5,z6]),(0,[z2,z408,z3,z4,z12,z5,z6])],[(0,[z199,z2,z68,z4,z12,z5,z6]),(0,[z409,z2,z3,z4,z12,z5,z6])],[(0,[z2,z157,z3,z4,z12,z5,z6])],[(0,[z410,z2,z3,z4,z12,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z12,z78,z5,z6]),(0,[z28,z254,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z23,z42,z6]),(0,[z2,z3,z4,z411,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z412]),(0,[z2,z3,z4,z123,z16,z5,z6]),(0,[z2,z267,z3,z12,z5,z6,z56])],[(0,[z413,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z414,z6]),(0,[z2,z3,z152,z4,z124,z5,z6]),(0,[z270,z2,z3,z4,z12,z5,z6]),(0,[z415,z2,z3,z4,z12,z5,z6])]],
   [[(0,[z416,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z417,z6]),(0,[z2,z9,z3,z7,z12,z5,z6]),(0,[z2,z3,z4,z418,z12,z5,z6]),(0,[z2,z3,z4,z128,z16,z5,z6])],[(0,[z115,z20,z3,z4,z12,z5,z6]),(0,[z8,z2,z3,z4,z12,z5,z6]),(0,[z43,z2,z3,z4,z12,z5,z419]),(0,[z22,z2,z9,z3,z12,z5,z6]),(0,[z2,z70,z4,z7,z12,z5,z6]),(0,[z247,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z420])],[(0,[z25,z2,z9,z3,z12,z5,z6]),(0,[z13,z2,z10,z3,z12,z5,z6]),(0,[z2,z70,z3,z4,z12,z5,z6])],[(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z179,z2,z3,z152,z4,z5,z6])],[(0,[z2,z3,z4,z232,z12,z5,z6]),(0,[z197,z2,z3,z4,z12,z5,z6])],[(0,[z1,z3,z4,z12,z5,z6,z61]),(0,[z2,z9,z3,z12,z291,z5,z6]),(1,[z3,z4,z5,z159,z42,z6])],[(0,[z199,z2,z3,z12,z5,z23,z6]),(0,[z2,z9,z3,z12,z170,z5,z6]),(0,[z2,z3,z4,z5,z6,z421,z92]),(0,[z2,z3,z4,z65,z5,z42,z6])],[(0,[z130,z8,z2,z3,z4,z5,z6]),(1,[z2,z9,z3,z16,z5,z6]),(0,[z2,z3,z422,z4,z12,z5,z6])],[(0,[z423,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z424,z6])],[(0,[z2,z3,z4,z11,z12,z5,z6]),(0,[z25,z2,z3,z34,z12,z5,z6])],[(0,[z64,z2,z3,z4,z12,z5,z6]),(0,[z199,z25,z3,z4,z12,z5,z6]),(0,[z25,z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z16,z5,z6,z61]),(0,[z2,z10,z3,z12,z50,z5,z6])],[(0,[z2,z10,z3,z12,z5,z6,z102]),(0,[z2,z3,z4,z124,z16,z5,z6])],[(0,[z425,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z426]),(0,[z2,z3,z4,z12,z5,z6,z427]),(0,[z63,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z388,z6]),(0,[z2,z4,z12,z5,z241,z6,z29]),(1,[z197,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z428,z12,z5,z6]),(0,[z2,z3,z4,z429,z12,z5,z6]),(0,[z430,z2,z3,z4,z12,z5,z6]),(1,[z2,z3,z34,z16,z5,z6]),(0,[z2,z3,z4,z16,z65,z5,z6])],[(0,[z1,z2,z3,z4,z5,z354,z6]),(0,[z2,z3,z4,z12,z5,z6,z431]),(0,[z2,z157,z4,z12,z5,z241,z6])]],
   [[(0,[z2,z3,z12,z5,z23,z17,z6])],[(0,[z2,z3,z58,z4,z12,z5,z6]),(1,[z8,z2,z9,z3,z5,z6]),(0,[z2,z3,z34,z12,z5,z6,z432]),(0,[z2,z3,z4,z141,z16,z5,z6]),(0,[z2,z3,z4,z12,z433,z5,z6])],[(0,[z2,z363,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z434,z6]),(0,[z2,z10,z271,z3,z12,z5,z6])],[],[(0,[z2,z3,z435,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z5,z241,z6]),(0,[z2,z3,z12,z5,z23,z6,z29]),(0,[z2,z108,z3,z12,z5,z23,z6]),(0,[z2,z3,z4,z5,z42,z42,z6])],[(0,[z8,z2,z3,z4,z5,z6,z279]),(1,[z2,z3,z4,z12,z5,z436])],[(0,[z1,z2,z3,z81,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z437]),(1,[z2,z3,z4,z331,z5,z6])],[(0,[z438,z2,z3,z4,z12,z5,z6]),(0,[z100,z2,z3,z4,z12,z5,z61]),(0,[z2,z3,z4,z12,z5,z39,z29])],[(0,[z115,z3,z81,z4,z12,z5,z6]),(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z2,z3,z4,z16,z5,z6,z173]),(0,[z2,z3,z4,z141,z5,z17,z6]),(0,[z2,z439,z3,z4,z12,z5,z6])],[(0,[z440,z2,z3,z4,z12,z5,z6]),(0,[z8,z2,z3,z4,z5,z21,z6]),(1,[z2,z86,z12,z5,z23,z6])],[(0,[z2,z3,z12,z5,z44,z23,z6]),(0,[z441,z70,z3,z4,z12,z5,z6]),(0,[z2,z442,z3,z4,z12,z5,z6])],[(0,[z2,z443,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z444,z5,z6]),(0,[z2,z3,z4,z12,z5,z445,z6]),(0,[z2,z3,z4,z446,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z447,z6]),(1,[z2,z97,z4,z78,z5,z6]),(0,[z2,z3,z4,z119,z5,z448,z6]),(0,[z2,z3,z124,z12,z291,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z432])],[(0,[z43,z2,z10,z3,z12,z5,z6]),(0,[z100,z2,z9,z3,z12,z5,z6])],[(0,[z2,z3,z81,z34,z12,z5,z6]),(0,[z1,z3,z4,z12,z15,z5,z6]),(0,[z8,z13,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z449,z6])]],
   [[(0,[z2,z3,z81,z4,z5,z42,z6]),(0,[z8,z2,z3,z4,z291,z5,z6]),(0,[z2,z3,z4,z12,z450,z5,z6])],[(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z451,z8,z2,z3,z4,z5,z6]),(0,[z2,z55,z3,z152,z12,z5,z6]),(0,[z452,z2,z3,z4,z12,z5,z6]),(0,[z2,z453,z3,z4,z12,z5,z6])],[(0,[z199,z2,z3,z4,z16,z5,z6]),(1,[z1,z3,z4,z5,z6,z61]),(0,[z247,z8,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z52,z4,z5,z6]),(0,[z2,z9,z3,z52,z12,z5,z6])],[(1,[z2,z3,z12,z5,z6,z323]),(0,[z121,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z53,z4,z12,z5,z6]),(1,[z2,z3,z131,z12,z5,z6])],[(0,[z264,z2,z3,z4,z12,z5,z6]),(0,[z2,z97,z3,z34,z12,z5,z6]),(1,[z441,z3,z4,z12,z5,z6])],[(0,[z2,z97,z3,z4,z5,z42,z6]),(0,[z454,z2,z3,z4,z12,z5,z6])],[(0,[z455,z2,z3,z4,z12,z5,z6]),(0,[z247,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z204]),(1,[z2,z3,z152,z124,z5,z6]),(1,[z2,z3,z4,z5,z456,z6])],[(0,[z2,z3,z358,z4,z116,z5,z6]),(0,[z2,z3,z4,z16,z5,z42,z6])],[(0,[z2,z58,z85,z4,z12,z5,z6]),(0,[z2,z3,z4,z457,z12,z5,z6]),(0,[z458,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z459,z4,z12,z5,z6]),(0,[z2,z10,z3,z3,z12,z5,z6]),(0,[z2,z3,z141,z12,z5,z23,z6])],[(0,[z43,z1,z3,z4,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z460,z6]),(0,[z2,z3,z85,z12,z5,z23,z6]),(0,[z247,z2,z157,z4,z12,z5,z6])],[(0,[z324,z2,z3,z4,z12,z5,z6]),(0,[z28,z2,z3,z4,z12,z5,z6])],[(0,[z20,z3,z4,z116,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z461]),(0,[z2,z9,z3,z12,z444,z5,z6])],[(0,[z2,z462,z3,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z119,z5,z6]),(0,[z2,z3,z4,z12,z463,z5,z6]),(0,[z2,z3,z52,z4,z12,z5,z6])],[(0,[z26,z8,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z464,z6]),(0,[z2,z3,z4,z141,z12,z5,z56])],[(1,[z162,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z116,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z354,z6]),(0,[z8,z2,z3,z4,z5,z241,z6]),(0,[z2,z3,z4,z12,z5,z6,z465]),(0,[z2,z136,z3,z4,z12,z5,z6])]],
   [[(0,[z2,z3,z422,z7,z12,z5,z6]),(0,[z2,z3,z4,z12,z466,z5,z6]),(0,[z2,z3,z34,z12,z5,z5,z6]),(0,[z467,z2,z3,z34,z12,z5,z6]),(0,[z468,z2,z3,z4,z12,z5,z6])],[(0,[z3,z4,z12,z5,z44,z6,z61])],[(0,[z2,z3,z4,z12,z469,z5,z6]),(0,[z160,z2,z10,z3,z12,z5,z6]),(0,[z470,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z471,z4,z12,z5,z6])],[(0,[z472,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z14,z6]),(0,[z2,z163,z10,z3,z12,z5,z6]),(0,[z2,z36,z3,z34,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z39,z6])],[(0,[z130,z1,z2,z3,z4,z5,z6]),(1,[z2,z10,z3,z5,z42,z6]),(1,[z2,z3,z4,z5,z6,z473])],[(0,[z2,z3,z34,z12,z78,z5,z6]),(0,[z2,z3,z34,z411,z12,z5,z6])],[(0,[z2,z208,z3,z58,z4,z5,z6]),(0,[z474,z2,z3,z4,z12,z5,z6]),(1,[z2,z3,z12,z475,z5,z6]),(0,[z2,z3,z4,z5,z6,z473,z29]),(0,[z26,z2,z3,z4,z476,z5,z6])],[(1,[z2,z10,z85,z12,z5,z6]),(0,[z2,z55,z3,z34,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z477,z6]),(0,[z2,z55,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z6,z478])],[(0,[z2,z3,z4,z12,z5,z456,z6])],[(0,[z43,z2,z3,z4,z12,z15,z6]),(0,[z2,z3,z4,z5,z44,z42,z6]),(0,[z2,z3,z99,z12,z15,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z61]),(0,[z2,z3,z4,z12,z475,z5,z6]),(1,[z2,z3,z161,z12,z5,z6]),(0,[z2,z3,z479,z4,z12,z5,z6])],[(1,[z2,z109,z4,z12,z119,z6]),(1,[z396,z3,z4,z5,z42,z6])],[(1,[z1,z3,z4,z15,z5,z6]),(0,[z179,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z480]),(0,[z2,z3,z4,z481,z12,z5,z6]),(0,[z130,z2,z246,z4,z12,z5,z6])],[(0,[z57,z2,z3,z4,z12,z5,z6]),(0,[z2,z97,z3,z4,z7,z5,z6]),(0,[z482,z2,z3,z4,z12,z5,z6])],[(0,[z1,z2,z3,z4,z483,z5,z6]),(1,[z1,z2,z9,z3,z5,z6]),(0,[z2,z3,z4,z12,z484,z5,z6]),(0,[z91,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z485,z5,z6])],[(0,[z2,z3,z4,z12,z5,z348,z6])]],
   [[(0,[z2,z68,z3,z4,z12,z5,z6]),(0,[z486,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z81,z4,z71,z5,z6]),(0,[z2,z3,z34,z11,z12,z5,z6]),(1,[z2,z9,z10,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z464,z6]),(0,[z2,z487,z3,z4,z12,z5,z6])],[(0,[z30,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z488,z6]),(0,[z2,z109,z3,z4,z12,z69,z6]),(0,[z489,z2,z3,z4,z12,z5,z6]),(0,[z490,z2,z3,z4,z12,z5,z6]),(1,[z2,z3,z12,z5,z6,z491])],[(0,[z1,z2,z3,z12,z5,z23,z6])],[(0,[z179,z2,z55,z3,z4,z5,z6]),(0,[z179,z2,z3,z34,z12,z5,z6])],[(0,[z20,z1,z2,z3,z4,z5,z6]),(0,[z179,z2,z3,z4,z5,z42,z6]),(1,[z202,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z492])],[(0,[z2,z3,z85,z4,z16,z5,z6]),(0,[z493,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z16,z5,z14,z6]),(0,[z396,z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z16,z5,z39,z6])],[(0,[z199,z2,z10,z3,z12,z5,z6]),(1,[z2,z3,z4,z211,z5,z6]),(0,[z2,z3,z99,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z119,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z473]),(0,[z2,z3,z34,z12,z5,z23,z6]),(1,[z2,z494,z4,z12,z5,z6]),(0,[z130,z2,z3,z4,z12,z65,z6])],[(0,[z115,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z37,z5,z6])],[(0,[z451,z25,z2,z3,z4,z5,z6]),(1,[z2,z9,z19,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z495,z6])],[(0,[z2,z3,z4,z12,z5,z6,z496]),(0,[z28,z2,z9,z4,z12,z5,z6])],[(0,[z43,z3,z4,z11,z12,z5,z6]),(0,[z22,z2,z3,z34,z12,z5,z6])],[(0,[z22,z2,z3,z4,z5,z42,z6])],[(0,[z8,z2,z3,z4,z116,z5,z6]),(0,[z497,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z498]),(0,[z2,z3,z4,z27,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z499])],[(0,[z2,z10,z3,z141,z12,z5,z6]),(0,[z2,z3,z4,z12,z500,z5,z6]),(0,[z91,z2,z55,z3,z12,z5,z6])],[(0,[z115,z2,z3,z34,z12,z5,z6]),(0,[z247,z1,z2,z3,z4,z5,z6]),(0,[z2,z10,z3,z34,z12,z5,z6]),(1,[z2,z3,z12,z5,z23,z6]),(0,[z2,z3,z4,z49,z12,z5,z6])]],
   [[(0,[z115,z2,z3,z4,z5,z42,z6]),(0,[z43,z2,z3,z4,z12,z44,z6]),(0,[z501,z2,z3,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z78,z5,z6]),(0,[z2,z10,z3,z4,z5,z42,z6]),(0,[z28,z2,z3,z4,z12,z5,z278]),(0,[z2,z3,z4,z12,z5,z6,z502])],[],[(0,[z199,z1,z3,z4,z12,z5,z6]),(0,[z28,z2,z3,z4,z12,z119,z6])],[(1,[z2,z3,z4,z428,z5,z6]),(0,[z2,z3,z4,z12,z5,z23,z6]),(0,[z2,z3,z52,z12,z5,z21,z6])],[(0,[z2,z3,z503,z4,z12,z5,z6]),(1,[z2,z9,z12,z119,z5,z6]),(1,[z2,z107,z3,z12,z5,z6])],[(0,[z228,z2,z3,z4,z12,z5,z6]),(0,[z130,z2,z9,z3,z12,z5,z6]),(0,[z2,z108,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z504])],[(0,[z2,z3,z4,z505,z12,z5,z6]),(0,[z2,z109,z3,z12,z5,z23,z6]),(0,[z2,z3,z4,z12,z5,z506,z6])],[(0,[z2,z3,z4,z12,z5,z507,z6]),(0,[z2,z508,z3,z4,z12,z5,z6]),(0,[z2,z3,z407,z4,z12,z5,z6])],[(0,[z2,z10,z85,z4,z12,z5,z6]),(0,[z28,z2,z3,z289,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z509])],[(0,[z1,z2,z10,z3,z4,z5,z6]),(0,[z401,z2,z3,z4,z12,z5,z6]),(0,[z510,z2,z3,z4,z12,z5,z6])],[(0,[z26,z1,z2,z3,z4,z5,z6])],[(0,[z2,z9,z3,z11,z12,z5,z6]),(0,[z2,z3,z12,z15,z5,z45,z6])],[(0,[z57,z2,z58,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z511,z5,z6]),(0,[z512,z2,z3,z4,z12,z5,z6]),(0,[z130,z2,z3,z34,z12,z5,z6])],[(0,[z43,z8,z2,z3,z4,z5,z6]),(0,[z43,z2,z513,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z436])],[(0,[z2,z3,z4,z514,z12,z5,z6]),(0,[z1,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z12,z515,z5,z6])],[(0,[z2,z59,z3,z58,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z516,z6]),(0,[z2,z10,z3,z12,z5,z42,z6])]],
   [[(0,[z8,z2,z3,z81,z4,z5,z6]),(0,[z2,z3,z4,z12,z517,z5,z6]),(0,[z2,z3,z53,z12,z5,z241,z6]),(0,[z2,z3,z4,z12,z5,z518,z6]),(0,[z2,z3,z4,z12,z5,z6,z519])],[(0,[z91,z20,z2,z3,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z44,z6]),(0,[z520,z2,z3,z4,z12,z5,z6]),(0,[z2,z10,z3,z12,z47,z5,z6]),(0,[z2,z3,z4,z521,z12,z5,z6]),(0,[z2,z3,z4,z522,z12,z5,z6]),(0,[z2,z3,z4,z47,z5,z464,z6])],[(0,[z8,z2,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z4,z119,z5,z6]),(1,[z2,z265,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z5,z23,z6]),(0,[z2,z109,z4,z12,z5,z6,z29]),(0,[z2,z3,z4,z5,z42,z218,z6])],[(0,[z523,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z34,z4,z16,z5,z6]),(0,[z2,z3,z524,z4,z12,z5,z6])],[(0,[z8,z2,z3,z4,z170,z5,z6]),(0,[z2,z3,z4,z12,z525,z5,z6])],[(0,[z1,z2,z3,z4,z5,z17,z6])],[(0,[z2,z3,z34,z116,z12,z5,z6]),(0,[z2,z3,z4,z526,z12,z5,z6]),(0,[z25,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z16,z15,z5,z6]),(0,[z2,z527,z3,z4,z12,z5,z6]),(0,[z315,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z12,z528,z5,z6])],[(0,[z100,z2,z3,z34,z12,z5,z6]),(0,[z322,z2,z3,z4,z5,z6,z61]),(0,[z2,z3,z4,z12,z5,z6,z529])],[(0,[z2,z3,z4,z530,z12,z5,z6]),(0,[z2,z531,z3,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z29]),(1,[z2,z3,z4,z5,z532,z6]),(0,[z100,z2,z3,z4,z5,z42,z6])],[(0,[z2,z151,z3,z4,z12,z5,z6]),(0,[z8,z2,z3,z4,z141,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z323]),(0,[z2,z3,z4,z533,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z491,z56])],[(0,[z1,z2,z3,z58,z4,z5,z6]),(0,[z8,z2,z3,z4,z78,z5,z6]),(1,[z2,z3,z4,z16,z5,z6]),(1,[z2,z3,z361,z12,z5,z6])],[(0,[z2,z534,z3,z4,z12,z5,z6]),(0,[z43,z2,z3,z4,z236,z5,z6]),(0,[z2,z3,z4,z535,z15,z5,z6]),(1,[z90,z2,z3,z12,z5,z6]),(0,[z2,z70,z3,z4,z78,z5,z6]),(0,[z536,z2,z3,z4,z12,z5,z6])],[(0,[z1,z2,z3,z85,z4,z5,z6]),(0,[z537,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z538])],[(0,[z2,z9,z4,z12,z5,z6,z29])],[(0,[z2,z539,z3,z4,z12,z5,z6]),(0,[z2,z540,z9,z3,z12,z5,z6]),(0,[z2,z171,z3,z12,z5,z6,z29]),(0,[z2,z3,z12,z5,z23,z6,z102]),(0,[z2,z494,z4,z12,z5,z21,z6])]],
   [[(0,[z2,z3,z4,z12,z5,z159,z6])],[(0,[z2,z3,z12,z5,z23,z541,z6])],[(0,[z2,z3,z4,z12,z542,z5,z6]),(0,[z2,z3,z4,z12,z5,z14,z102]),(0,[z2,z109,z3,z4,z16,z5,z6]),(0,[z2,z494,z3,z4,z12,z5,z6])],[(1,[z2,z3,z4,z12,z5,z419]),(0,[z153,z2,z10,z3,z12,z5,z6]),(0,[z543,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z210,z5,z6]),(0,[z544,z2,z3,z4,z12,z5,z6])],[(0,[z199,z3,z4,z11,z12,z5,z6]),(0,[z2,z3,z4,z12,z545,z5,z6])],[(0,[z1,z3,z58,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z546,z6])],[(1,[z2,z208,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z6]),(0,[z2,z540,z3,z34,z12,z5,z6])],[(0,[z2,z10,z109,z3,z12,z5,z6]),(1,[z2,z3,z4,z547,z5,z6]),(0,[z2,z3,z34,z16,z12,z5,z6])],[(0,[z548,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z549,z5,z6]),(0,[z2,z157,z3,z4,z12,z5,z29]),(0,[z2,z3,z34,z12,z5,z17,z6])],[(0,[z2,z3,z124,z12,z5,z23,z6]),(0,[z2,z3,z12,z5,z23,z6,z92]),(0,[z2,z344,z3,z4,z16,z5,z6])],[(0,[z26,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z550,z4,z12,z5,z6]),(1,[z2,z3,z4,z551,z5,z6]),(0,[z2,z552,z3,z4,z5,z42,z6])],[(1,[z2,z336,z3,z4,z5,z6]),(1,[z2,z151,z4,z12,z5,z6]),(0,[z2,z10,z3,z152,z12,z5,z6]),(1,[z2,z3,z4,z132,z5,z6]),(0,[z553,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z554,z5,z6]),(0,[z2,z3,z34,z12,z5,z6,z29]),(0,[z2,z3,z4,z12,z65,z5,z102])],[(0,[z298,z2,z3,z4,z12,z5,z6]),(0,[z187,z8,z2,z3,z4,z5,z6]),(0,[z2,z10,z3,z12,z5,z14,z6]),(0,[z2,z9,z3,z4,z16,z5,z6]),(0,[z2,z180,z10,z3,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z39,z6])],[]],
   [[],[(0,[z2,z9,z3,z116,z12,z5,z6]),(0,[z2,z97,z3,z4,z12,z5,z6])],[(0,[z2,z336,z3,z58,z4,z5,z6]),(0,[z100,z13,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z555,z6]),(0,[z556,z2,z3,z4,z12,z5,z6]),(0,[z26,z2,z3,z34,z12,z5,z6]),(1,[z2,z3,z230,z12,z5,z6])],[(0,[z2,z3,z4,z557,z12,z5,z6]),(0,[z1,z2,z10,z3,z12,z5,z6]),(0,[z190,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z69,z23,z6]),(0,[z2,z3,z4,z12,z5,z6,z558]),(0,[z2,z3,z152,z124,z12,z5,z6]),(0,[z26,z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z16,z12,z5,z6])],[(1,[z2,z86,z3,z12,z5,z6])],[(0,[z2,z10,z3,z12,z5,z6,z61]),(0,[z2,z3,z12,z50,z5,z23,z6]),(0,[z2,z3,z4,z12,z5,z17,z6]),(1,[z179,z2,z3,z4,z5,z56])],[(0,[z2,z3,z4,z12,z5,z149,z6]),(0,[z2,z3,z4,z12,z559,z5,z6]),(0,[z2,z3,z4,z5,z6,z375,z61]),(0,[z560,z2,z3,z4,z12,z5,z6])],[(0,[z2,z157,z3,z12,z5,z23,z6]),(0,[z2,z3,z4,z12,z5,z6,z561])],[(1,[z2,z3,z358,z4,z5,z6]),(0,[z2,z3,z4,z535,z12,z5,z6]),(0,[z13,z2,z3,z4,z12,z5,z61]),(0,[z2,z3,z4,z12,z5,z61,z102]),(0,[z2,z3,z4,z12,z288,z5,z6]),(0,[z2,z97,z70,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z21,z6]),(0,[z2,z3,z4,z12,z5,z6,z491])],[(0,[z2,z3,z4,z12,z5,z6,z562]),(0,[z2,z10,z3,z12,z65,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z29]),(0,[z91,z2,z3,z52,z12,z5,z6])],[(0,[z2,z3,z563,z4,z12,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z70,z3,z4,z5,z6]),(1,[z2,z3,z12,z564,z5,z6]),(0,[z2,z3,z152,z34,z12,z5,z6]),(0,[z2,z3,z4,z183,z65,z5,z6])],[(0,[z2,z3,z4,z483,z12,z5,z6]),(0,[z2,z10,z3,z124,z12,z5,z6]),(0,[z2,z3,z152,z4,z5,z42,z6])],[(1,[z8,z2,z3,z4,z5,z6]),(1,[z2,z513,z4,z12,z5,z6]),(0,[z565,z2,z3,z4,z12,z5,z6]),(0,[z2,z566,z3,z4,z12,z5,z6])],[(0,[z567,z2,z9,z3,z12,z5,z6]),(0,[z568,z2,z3,z4,z12,z5,z6]),(0,[z467,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z551,z5,z6]),(0,[z2,z157,z109,z4,z12,z5,z6]),(1,[z2,z3,z4,z5,z448,z6]),(0,[z2,z3,z4,z12,z569,z5,z6]),(0,[z2,z570,z3,z4,z12,z5,z6]),(0,[z130,z2,z3,z4,z571,z5,z6])],[(0,[z2,z3,z4,z12,z5,z572,z6]),(0,[z2,z3,z4,z12,z5,z573,z6]),(0,[z13,z2,z9,z3,z12,z5,z6])]],
   [[(0,[z259,z2,z3,z4,z12,z5,z6]),(1,[z451,z2,z3,z4,z5,z6]),(1,[z2,z10,z3,z12,z5,z6]),(0,[z2,z36,z3,z4,z12,z5,z6])],[(0,[z2,z3,z123,z12,z5,z23,z6])],[(0,[z2,z9,z3,z16,z12,z5,z6])],[(0,[z2,z574,z3,z4,z12,z5,z6]),(0,[z2,z326,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z575,z6]),(0,[z2,z3,z34,z12,z576,z5,z6])],[(0,[z2,z9,z3,z12,z5,z17,z6]),(0,[z2,z3,z12,z119,z5,z23,z6]),(0,[z2,z55,z3,z4,z12,z5,z6]),(0,[z2,z577,z3,z4,z12,z5,z6])],[(0,[z2,z293,z3,z4,z12,z5,z6]),(0,[z578,z2,z3,z4,z12,z5,z6])],[(0,[z13,z2,z3,z34,z12,z5,z6]),(0,[z2,z3,z4,z579,z12,z5,z6])],[(0,[z13,z2,z3,z4,z5,z42,z6]),(0,[z2,z9,z462,z3,z12,z5,z6]),(0,[z63,z2,z3,z12,z5,z23,z6]),(1,[z396,z3,z4,z12,z5,z6])],[(0,[z2,z9,z3,z12,z5,z6,z29]),(0,[z2,z3,z4,z7,z16,z5,z6]),(0,[z2,z3,z34,z522,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z318])],[(0,[z2,z9,z68,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z580,z6])],[(1,[z2,z3,z4,z236,z5,z6]),(0,[z2,z3,z12,z5,z23,z281,z6]),(0,[z2,z3,z4,z16,z5,z21,z6])],[(0,[z2,z3,z58,z12,z5,z23,z6])],[(0,[z199,z2,z3,z581,z12,z5,z6]),(0,[z2,z3,z12,z5,z23,z6,z56]),(0,[z2,z3,z582,z34,z12,z5,z6])],[(0,[z1,z3,z4,z12,z170,z5,z6]),(0,[z244,z8,z2,z3,z4,z5,z6]),(0,[z322,z2,z3,z4,z12,z5,z6]),(1,[z2,z9,z157,z12,z5,z6]),(0,[z2,z583,z3,z4,z12,z5,z6]),(0,[z2,z540,z109,z3,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z241,z6]),(0,[z2,z3,z582,z4,z5,z42,z6]),(0,[z2,z3,z4,z16,z398,z5,z6])],[(0,[z2,z10,z3,z12,z15,z5,z6]),(0,[z2,z3,z34,z584,z12,z5,z6]),(0,[z2,z3,z4,z12,z576,z5,z6])]],
   [[(0,[z2,z3,z34,z12,z5,z6,z92]),(0,[z130,z2,z3,z4,z5,z42,z6]),(0,[z179,z2,z3,z4,z12,z5,z6])],[(0,[z43,z2,z3,z4,z12,z5,z585]),(0,[z2,z3,z4,z12,z5,z448,z6])],[(0,[z2,z3,z4,z16,z291,z5,z6]),(0,[z396,z2,z3,z4,z12,z5,z6])],[(0,[z2,z9,z3,z81,z12,z5,z6]),(0,[z2,z3,z4,z16,z170,z5,z6]),(0,[z8,z2,z10,z3,z4,z5,z6]),(0,[z2,z9,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z5,z69,z42,z6]),(0,[z2,z157,z3,z4,z16,z5,z6]),(1,[z2,z362,z4,z12,z5,z6])],[(0,[z2,z586,z3,z4,z12,z5,z6]),(0,[z587,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z588,z12,z5,z6]),(0,[z2,z589,z3,z4,z12,z5,z6]),(0,[z1,z2,z261,z3,z4,z5,z6]),(1,[z2,z9,z12,z5,z6,z29]),(0,[z2,z3,z4,z50,z5,z42,z6])],[(0,[z2,z3,z116,z12,z5,z23,z6]),(0,[z365,z2,z3,z4,z12,z5,z6]),(0,[z2,z9,z157,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z590])],[(0,[z591,z2,z3,z4,z12,z5,z6])],[(0,[z22,z2,z3,z4,z12,z5,z6]),(0,[z592,z2,z3,z4,z12,z5,z6]),(0,[z2,z10,z68,z3,z12,z5,z6]),(0,[z20,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z593,z6]),(0,[z2,z3,z594,z4,z12,z5,z6])],[(0,[z2,z3,z595,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z596,z6])],[(0,[z2,z3,z597,z4,z12,z5,z6])],[(0,[z199,z68,z3,z4,z12,z5,z6]),(0,[z43,z2,z9,z3,z12,z5,z6]),(0,[z2,z598,z3,z4,z12,z5,z6]),(0,[z26,z2,z3,z4,z12,z47,z6]),(0,[z2,z3,z4,z584,z12,z5,z6]),(0,[z179,z2,z3,z4,z12,z5,z17])],[(0,[z115,z2,z3,z4,z12,z5,z6]),(0,[z2,z599,z3,z4,z12,z5,z6]),(0,[z2,z35,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z92]),(1,[z2,z4,z12,z5,z6,z369])],[(1,[z2,z3,z320,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z600,z6]),(0,[z2,z3,z4,z12,z5,z6,z601])],[(0,[z2,z3,z4,z12,z5,z6,z602])],[(0,[z3,z58,z4,z12,z5,z44,z6]),(0,[z20,z2,z3,z34,z12,z5,z6])]],
   [[(0,[z20,z2,z3,z4,z5,z42,z6]),(0,[z2,z10,z3,z12,z5,z213,z6]),(0,[z2,z258,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z224,z6]),(0,[z2,z3,z4,z12,z603,z5,z6])],[(1,[z2,z3,z12,z5,z604,z6]),(0,[z2,z3,z4,z16,z5,z241,z6]),(0,[z2,z3,z4,z12,z5,z605,z6])],[(0,[z2,z3,z4,z12,z606,z5,z6]),(0,[z43,z2,z3,z34,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z69,z6])],[(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z4,z5,z6,z29]),(0,[z43,z2,z3,z4,z5,z42,z6]),(0,[z247,z2,z9,z3,z12,z5,z6]),(0,[z2,z55,z3,z4,z291,z5,z6]),(0,[z63,z2,z3,z4,z16,z5,z6])],[(0,[z2,z3,z607,z4,z12,z5,z6]),(0,[z25,z3,z4,z12,z5,z6,z61]),(0,[z2,z3,z4,z119,z5,z42,z6]),(0,[z2,z267,z3,z4,z12,z5,z6])],[(0,[z8,z2,z3,z58,z4,z5,z6]),(0,[z2,z9,z3,z58,z12,z5,z6]),(0,[z2,z531,z3,z4,z116,z5,z6]),(0,[z1,z2,z97,z3,z4,z5,z6]),(0,[z28,z2,z3,z12,z5,z23,z6]),(0,[z2,z3,z4,z12,z5,z604,z6])],[(0,[z2,z3,z4,z12,z608,z5,z6]),(0,[z2,z3,z4,z12,z5,z609,z6])],[(0,[z8,z2,z3,z85,z4,z5,z6]),(0,[z2,z9,z3,z85,z12,z5,z6]),(0,[z2,z3,z12,z78,z5,z23,z6])],[(0,[z2,z3,z58,z4,z16,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6])],[(0,[z2,z610,z9,z3,z12,z5,z6]),(0,[z247,z2,z3,z34,z12,z5,z6]),(0,[z451,z2,z3,z4,z5,z42,z6])],[(0,[z611,z2,z3,z4,z12,z5,z6]),(1,[z1,z3,z4,z170,z5,z6]),(0,[z2,z9,z3,z12,z5,z6,z92]),(0,[z247,z2,z3,z4,z5,z42,z6]),(0,[z2,z55,z3,z12,z5,z21,z6])],[(1,[z115,z3,z81,z12,z5,z6]),(0,[z28,z2,z109,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z612,z6]),(0,[z2,z3,z4,z183,z12,z5,z6])],[(0,[z2,z328,z3,z4,z5,z6,z29])],[(1,[z2,z3,z4,z5,z6,z176]),(0,[z28,z2,z3,z4,z12,z5,z436]),(0,[z2,z3,z4,z12,z5,z613,z6])],[(0,[z2,z3,z81,z4,z12,z5,z6]),(0,[z296,z8,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z532,z6]),(0,[z100,z2,z3,z4,z12,z5,z14])]],
   [[(0,[z8,z2,z3,z4,z5,z23,z6]),(0,[z2,z3,z4,z12,z65,z39,z6])],[(1,[z2,z9,z3,z5,z42,z6])],[(1,[z2,z9,z58,z12,z5,z6]),(1,[z2,z171,z3,z12,z5,z6]),(0,[z2,z55,z3,z12,z291,z5,z6])],[(0,[z2,z3,z614,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6]),(0,[z2,z3,z4,z12,z615,z5,z6]),(0,[z2,z3,z12,z5,z23,z6,z40]),(0,[z616,z2,z3,z4,z12,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z102])],[(0,[z1,z2,z3,z105,z4,z5,z6]),(0,[z100,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z617]),(0,[z618,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z124,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z619,z6]),(0,[z63,z2,z3,z161,z12,z5,z6])],[(1,[z2,z531,z3,z4,z5,z6])],[(0,[z620,z2,z9,z3,z12,z5,z6])],[(1,[z2,z3,z34,z5,z42,z6])],[(1,[z2,z487,z3,z4,z5,z6])],[(0,[z2,z3,z4,z621,z12,z5,z6]),(0,[z2,z622,z3,z4,z12,z5,z6]),(0,[z396,z3,z4,z12,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z623,z6])],[(0,[z8,z2,z3,z4,z515,z5,z6]),(0,[z2,z3,z4,z141,z5,z42,z6])],[(0,[z2,z3,z4,z12,z5,z624,z6]),(0,[z2,z625,z3,z4,z12,z5,z6])],[(1,[z2,z3,z4,z222,z5,z6]),(0,[z2,z3,z4,z12,z626,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z627]),(0,[z2,z3,z4,z12,z5,z281,z6]),(0,[z2,z3,z4,z12,z628,z5,z6]),(0,[z629,z2,z3,z4,z5,z42,z6])],[(0,[z57,z199,z3,z4,z12,z5,z6]),(0,[z630,z2,z3,z4,z12,z5,z6]),(1,[z1,z13,z3,z4,z5,z6]),(0,[z25,z3,z4,z12,z15,z5,z6]),(0,[z2,z3,z4,z12,z5,z631,z6])],[(1,[z2,z405,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z92]),(0,[z1,z2,z3,z4,z124,z5,z6]),(0,[z8,z2,z3,z12,z5,z23,z6]),(0,[z2,z77,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z56])]],
   [[(1,[z2,z3,z4,z12,z5,z585]),(0,[z100,z3,z4,z12,z5,z6,z61]),(0,[z2,z97,z4,z12,z78,z5,z6]),(0,[z2,z70,z3,z12,z5,z23,z6]),(1,[z2,z3,z4,z5,z6,z421])],[(0,[z2,z3,z4,z632,z12,z5,z6]),(0,[z8,z115,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z564,z5,z6]),(0,[z28,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z362,z4,z12,z5,z6])],[(0,[z2,z68,z109,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z6])],[(1,[z57,z58,z4,z12,z5,z6]),(0,[z115,z2,z3,z12,z5,z21,z6]),(0,[z2,z3,z4,z633,z12,z5,z6]),(0,[z2,z540,z3,z4,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z21,z6]),(0,[z2,z3,z4,z12,z5,z6,z634])],[(0,[z199,z2,z9,z3,z12,z5,z6]),(0,[z8,z2,z70,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z419,z6]),(0,[z2,z3,z4,z19,z16,z5,z6])],[(1,[z199,z68,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z69,z6]),(0,[z635,z2,z3,z4,z12,z5,z6])],[(0,[z2,z636,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z449,z42,z6])],[(0,[z1,z2,z3,z152,z4,z5,z6]),(0,[z2,z3,z637,z4,z12,z5,z6]),(0,[z2,z3,z4,z78,z5,z42,z6]),(0,[z2,z3,z34,z12,z50,z5,z6]),(0,[z2,z552,z3,z4,z12,z5,z6])],[(0,[z8,z1,z3,z4,z12,z5,z6]),(0,[z63,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z638,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z639]),(1,[z2,z3,z4,z476,z5,z6]),(0,[z2,z3,z34,z12,z5,z6,z102])],[(0,[z2,z3,z4,z12,z640,z5,z6]),(0,[z2,z3,z4,z641,z12,z5,z6]),(0,[z2,z3,z642,z4,z12,z5,z6])],[(1,[z100,z3,z4,z12,z5,z61]),(0,[z2,z4,z12,z5,z69,z6,z29])],[(0,[z2,z9,z3,z12,z5,z624,z6])],[(0,[z2,z3,z4,z643,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z644]),(0,[z2,z3,z4,z12,z5,z241,z102]),(0,[z130,z2,z3,z4,z12,z5,z39])],[(1,[z2,z77,z3,z12,z5,z6])],[(0,[z2,z3,z4,z12,z645,z5,z6]),(0,[z26,z2,z3,z4,z12,z5,z6])]],
   [[(0,[z2,z3,z4,z12,z222,z5,z6]),(0,[z2,z10,z3,z12,z303,z5,z6])],[(0,[z68,z3,z58,z4,z12,z5,z6]),(0,[z290,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z60,z34,z12,z5,z6]),(1,[z3,z4,z12,z5,z159,z6])],[(0,[z2,z3,z4,z646,z12,z5,z6]),(0,[z0,z2,z3,z4,z16,z5,z6])],[(0,[z28,z2,z3,z4,z12,z69,z6]),(0,[z2,z3,z4,z12,z5,z6,z421]),(0,[z2,z3,z4,z12,z50,z5,z6])],[(1,[z2,z9,z68,z12,z5,z6]),(0,[z2,z3,z4,z16,z119,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z102])],[(0,[z2,z3,z4,z12,z5,z647,z6]),(0,[z2,z3,z4,z12,z648,z5,z6])],[(1,[z2,z3,z581,z12,z5,z6]),(0,[z1,z2,z9,z3,z4,z5,z6]),(1,[z2,z108,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z541,z6])],[(0,[z2,z3,z4,z12,z5,z6,z649]),(0,[z2,z3,z4,z12,z650,z5,z6]),(0,[z2,z3,z152,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z651]),(0,[z2,z3,z4,z16,z5,z404,z6])],[(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z2,z3,z4,z16,z5,z5,z6])],[(0,[z2,z3,z12,z5,z23,z6,z61]),(0,[z2,z10,z3,z12,z5,z241,z6]),(0,[z2,z3,z34,z12,z5,z69,z6]),(0,[z2,z3,z4,z12,z5,z652,z6])],[(0,[z2,z3,z4,z581,z12,z5,z6]),(0,[z1,z25,z2,z3,z4,z5,z6]),(0,[z653,z2,z3,z4,z12,z5,z6])],[(0,[z8,z2,z3,z4,z16,z5,z6]),(0,[z2,z97,z3,z4,z78,z5,z6]),(0,[z2,z3,z4,z12,z476,z5,z6]),(0,[z2,z3,z4,z5,z654,z42,z6])],[(1,[z199,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z39,z61]),(0,[z2,z70,z3,z4,z16,z5,z6]),(1,[z2,z12,z5,z106,z23,z6])],[(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z43,z2,z3,z4,z186,z5,z6]),(0,[z2,z3,z4,z16,z78,z5,z6])],[(0,[z655,z2,z3,z4,z12,z5,z6]),(0,[z2,z656,z3,z4,z12,z5,z6]),(0,[z523,z2,z3,z12,z5,z23,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z2,z10,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z657,z5,z6])]],
   [[(0,[z2,z363,z3,z58,z12,z5,z6]),(1,[z2,z3,z34,z12,z47,z6]),(1,[z2,z3,z4,z12,z65,z39])],[(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z567,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z291,z5,z23,z6])],[(0,[z1,z2,z3,z4,z5,z6,z56]),(0,[z2,z3,z658,z4,z12,z5,z6]),(0,[z8,z2,z3,z4,z5,z17,z6]),(0,[z2,z9,z3,z12,z50,z5,z6])],[(0,[z659,z2,z3,z4,z12,z5,z6]),(0,[z8,z199,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z11,z16,z5,z6]),(0,[z13,z2,z3,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z5,z6,z102]),(0,[z2,z70,z3,z4,z5,z17,z6])],[(0,[z2,z3,z4,z12,z660,z5,z6]),(0,[z2,z3,z4,z12,z5,z661,z6]),(0,[z2,z3,z4,z12,z662,z5,z6])],[(0,[z416,z2,z3,z4,z12,z5,z6]),(0,[z2,z127,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z654,z6])],[(0,[z28,z2,z10,z3,z12,z5,z6]),(0,[z2,z3,z12,z119,z5,z604,z6]),(0,[z663,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z361,z12,z50,z5,z6])],[(0,[z664,z2,z3,z4,z12,z5,z6]),(0,[z2,z10,z157,z3,z12,z5,z6])],[(0,[z199,z2,z3,z607,z12,z5,z6]),(1,[z396,z2,z3,z4,z5,z6])],[(0,[z2,z3,z120,z34,z12,z5,z6])],[(0,[z2,z3,z4,z12,z665,z5,z6]),(0,[z8,z3,z4,z11,z12,z5,z6]),(0,[z2,z3,z113,z4,z12,z5,z6]),(0,[z2,z3,z582,z4,z12,z5,z6]),(0,[z2,z86,z3,z4,z12,z5,z6]),(0,[z2,z3,z52,z12,z5,z23,z6])],[(0,[z2,z3,z4,z12,z5,z6,z666]),(1,[z2,z3,z16,z5,z23,z6])],[(0,[z667,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z668,z12,z5,z6]),(0,[z2,z3,z4,z139,z12,z5,z6]),(0,[z130,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z405,z4,z12,z5,z6]),(0,[z2,z3,z4,z275,z12,z5,z6]),(0,[z2,z3,z513,z4,z12,z5,z6])],[(1,[z2,z3,z607,z12,z5,z6]),(0,[z2,z3,z85,z34,z12,z5,z6]),(0,[z2,z3,z12,z5,z241,z6,z355])],[(0,[z8,z2,z97,z3,z4,z5,z6]),(0,[z2,z669,z3,z4,z12,z5,z6]),(0,[z2,z9,z97,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z670]),(0,[z2,z3,z85,z4,z5,z42,z6]),(0,[z2,z3,z4,z12,z671,z5,z6]),(0,[z2,z157,z4,z12,z5,z69,z6]),(0,[z247,z2,z3,z4,z12,z5,z241]),(0,[z2,z672,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z5,z23,z6])]],
   [[(0,[z57,z2,z68,z4,z12,z5,z6]),(1,[z91,z2,z3,z12,z5,z92])],[(1,[z63,z2,z3,z4,z42,z6])],[(0,[z2,z3,z4,z12,z673,z5,z6]),(0,[z134,z2,z3,z4,z5,z44,z6]),(0,[z674,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z460,z6])],[(0,[z2,z3,z4,z12,z675,z5,z6]),(0,[z2,z3,z4,z12,z5,z676,z6]),(1,[z2,z3,z12,z5,z51,z6])],[(0,[z2,z9,z3,z12,z5,z69,z6]),(0,[z2,z3,z4,z12,z677,z5,z6]),(0,[z2,z3,z12,z5,z23,z31,z6]),(1,[z2,z246,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z678,z6]),(0,[z2,z3,z4,z12,z5,z6,z679])],[(0,[z2,z3,z680,z4,z12,z5,z6]),(0,[z2,z3,z7,z12,z475,z5,z6]),(0,[z2,z3,z152,z4,z291,z5,z6]),(0,[z2,z3,z12,z5,z23,z42,z6]),(0,[z2,z3,z4,z12,z5,z221,z6]),(0,[z2,z3,z34,z12,z5,z6,z56]),(0,[z2,z3,z394,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z51,z6]),(0,[z681,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z65,z5,z456,z6])],[(0,[z2,z3,z4,z682,z12,z5,z6]),(0,[z683,z2,z3,z4,z12,z5,z6])],[(0,[z179,z2,z3,z4,z141,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z684])],[(1,[z247,z2,z4,z12,z5,z29])],[(0,[z57,z2,z3,z12,z5,z23,z6]),(0,[z130,z2,z3,z345,z12,z5,z6]),(1,[z130,z2,z3,z4,z12,z102])],[(1,[z1,z3,z58,z4,z5,z6]),(0,[z20,z2,z3,z4,z12,z5,z6]),(0,[z8,z8,z2,z3,z4,z5,z6]),(0,[z91,z2,z3,z12,z5,z23,z6])],[(0,[z2,z3,z4,z685,z12,z5,z6])],[(0,[z2,z68,z3,z12,z5,z23,z6]),(1,[z2,z3,z4,z535,z5,z6]),(1,[z2,z3,z12,z5,z114,z6])],[(0,[z2,z3,z4,z686,z12,z5,z6]),(0,[z43,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z687,z4,z12,z5,z6]),(0,[z2,z3,z52,z4,z12,z5,z92])]],
   [[(0,[z2,z2,z3,z4,z12,z5,z6]),(0,[z688,z2,z3,z4,z12,z5,z6]),(0,[z8,z2,z10,z3,z12,z5,z6]),(0,[z2,z9,z3,z3,z12,z5,z6]),(0,[z689,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z16,z12,z5,z23,z6])],[(0,[z2,z10,z3,z19,z12,z5,z6]),(0,[z2,z70,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z291,z5,z42,z6])],[(0,[z2,z68,z3,z4,z428,z5,z6]),(0,[z690,z2,z3,z4,z12,z5,z6])],[(0,[z2,z691,z3,z4,z12,z5,z6]),(0,[z28,z2,z3,z320,z12,z5,z6]),(2,[z2,z86,z12,z5,z6]),(1,[z2,z3,z4,z571,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z176]),(0,[z2,z692,z3,z4,z12,z5,z6])],[(0,[z1,z2,z109,z3,z4,z5,z6]),(0,[z693,z2,z3,z4,z12,z5,z6]),(0,[z2,z487,z3,z4,z5,z6,z92])],[(0,[z451,z2,z3,z4,z12,z5,z6]),(1,[z2,z540,z3,z12,z5,z6]),(0,[z2,z3,z52,z4,z16,z5,z6])],[(0,[z63,z8,z2,z3,z4,z5,z6]),(0,[z3,z4,z11,z12,z5,z6,z61]),(0,[z2,z9,z70,z3,z12,z5,z6]),(0,[z247,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z6,z585]),(0,[z2,z10,z3,z7,z12,z5,z6]),(0,[z316,z2,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z116,z16,z5,z6]),(0,[z370,z1,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z4,z5,z6,z92]),(0,[z8,z2,z3,z4,z124,z5,z6])],[(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z2,z3,z12,z5,z106,z23,z6])],[(0,[z2,z3,z4,z694,z12,z5,z6]),(0,[z2,z3,z4,z547,z12,z5,z6])],[(0,[z8,z2,z3,z4,z11,z5,z6]),(1,[z2,z3,z4,z186,z5,z6]),(0,[z2,z10,z3,z12,z119,z5,z6])],[(0,[z13,z3,z4,z12,z5,z44,z6]),(0,[z2,z3,z695,z4,z12,z5,z6]),(1,[z2,z9,z3,z12,z5,z6]),(0,[z2,z10,z3,z12,z291,z5,z6]),(1,[z2,z3,z422,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z6,z369]),(0,[z2,z3,z4,z5,z17,z6,z56])],[(0,[z199,z2,z3,z34,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z696,z6]),(0,[z2,z10,z3,z12,z170,z5,z6]),(1,[z2,z3,z12,z5,z189,z6]),(0,[z2,z610,z3,z4,z12,z5,z6])],[(0,[z199,z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z4,z12,z5,z697,z6]),(0,[z8,z2,z3,z4,z5,z69,z6]),(0,[z2,z3,z7,z12,z5,z23,z6])]],
   [[(0,[z28,z2,z3,z4,z547,z5,z6]),(0,[z2,z3,z4,z12,z5,z198,z6]),(0,[z2,z3,z4,z5,z42,z6,z561]),(0,[z2,z3,z12,z65,z5,z74,z6])],[(0,[z3,z4,z12,z15,z5,z44,z6]),(0,[z2,z9,z3,z12,z5,z6,z56]),(0,[z2,z3,z12,z564,z78,z5,z6]),(0,[z2,z3,z4,z124,z12,z5,z6]),(0,[z91,z2,z3,z4,z12,z5,z92])],[(0,[z2,z3,z4,z12,z5,z189,z6]),(1,[z2,z136,z3,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z29])],[],[(0,[z440,z8,z2,z3,z4,z5,z6]),(0,[z2,z249,z3,z4,z12,z5,z6]),(0,[z28,z2,z3,z4,z551,z5,z6]),(1,[z2,z3,z34,z12,z5,z6]),(1,[z2,z4,z12,z5,z106,z6])],[(0,[z2,z3,z12,z5,z23,z14,z6]),(0,[z2,z10,z3,z12,z78,z5,z6]),(0,[z2,z3,z12,z5,z23,z39,z6]),(1,[z2,z3,z4,z5,z42,z6])],[(0,[z43,z2,z3,z113,z12,z5,z6]),(0,[z2,z3,z4,z12,z571,z5,z6])],[(0,[z57,z2,z3,z4,z16,z5,z6]),(0,[z2,z3,z4,z698,z12,z5,z6]),(0,[z2,z3,z4,z5,z532,z44,z6]),(0,[z2,z10,z3,z418,z12,z5,z6]),(0,[z2,z254,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z699,z12,z5,z6]),(0,[z2,z3,z4,z141,z12,z5,z6])],[(0,[z8,z2,z3,z658,z4,z5,z6]),(0,[z441,z2,z3,z4,z12,z5,z6]),(0,[z91,z2,z3,z4,z16,z5,z6])],[(0,[z629,z2,z3,z4,z12,z5,z6])],[(0,[z2,z68,z3,z4,z16,z5,z6]),(0,[z231,z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z700,z6]),(0,[z2,z701,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z702,z5,z6]),(0,[z2,z3,z4,z16,z16,z5,z6]),(0,[z2,z3,z703,z4,z12,z5,z6])],[(0,[z0,z25,z2,z3,z4,z5,z6]),(0,[z620,z2,z3,z4,z12,z5,z6]),(0,[z2,z109,z3,z34,z12,z5,z6]),(0,[z2,z3,z4,z12,z704,z5,z6])],[(0,[z2,z109,z3,z4,z5,z42,z6])],[(0,[z705,z2,z3,z4,z12,z5,z6]),(0,[z520,z2,z10,z3,z12,z5,z6]),(0,[z28,z2,z4,z12,z5,z69,z6]),(0,[z2,z3,z4,z12,z5,z168,z6]),(0,[z2,z3,z4,z331,z47,z5,z6])],[(0,[z2,z3,z34,z12,z5,z44,z6]),(0,[z2,z3,z12,z15,z5,z23,z6]),(1,[z269,z3,z4,z12,z5,z6]),(0,[z706,z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z47,z5,z6])],[]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z3,z4,z707,z5,z6]),(0,[z3,z4,z5,z354,z6,z61])],[(0,[z2,z708,z3,z12,z5,z6])],[(0,[z2,z3,z4,z5,z709,z6]),(0,[z1,z3,z99,z15,z5,z6]),(0,[z1,z3,z4,z411,z5,z6]),(0,[z8,z197,z3,z4,z5,z6]),(0,[z2,z3,z12,z710,z5,z6])],[(0,[z2,z3,z12,z5,z23,z6]),(0,[z20,z443,z3,z12,z5,z6]),(0,[z2,z9,z494,z12,z5,z6]),(0,[z2,z108,z109,z12,z119,z6]),(0,[z2,z3,z4,z5,z6,z711])],[(0,[z197,z3,z4,z12,z5,z6]),(0,[z1,z3,z4,z5,z33,z6]),(0,[z2,z3,z4,z712,z5,z6])],[(0,[z2,z713,z3,z12,z5,z6]),(0,[z2,z9,z12,z398,z5,z6]),(0,[z2,z3,z320,z5,z42,z6])],[(0,[z2,z3,z714,z12,z5,z6]),(0,[z715,z3,z4,z12,z5,z6]),(0,[z2,z716,z3,z12,z5,z6])],[(0,[z2,z3,z4,z717,z5,z6]),(0,[z396,z3,z4,z7,z5,z6]),(0,[z2,z3,z718,z12,z5,z6]),(0,[z719,z3,z4,z5,z456,z6])],[(0,[z2,z10,z3,z71,z5,z6]),(0,[z1,z2,z3,z34,z23,z6]),(0,[z2,z9,z12,z119,z5,z6])],[(0,[z3,z4,z12,z15,z720,z6]),(0,[z26,z2,z3,z12,z189,z6])],[(0,[z2,z3,z4,z721,z5,z6]),(0,[z2,z3,z4,z5,z722,z6]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z724,z2,z10,z3,z5,z6]),(0,[z440,z441,z3,z4,z5,z6]),(0,[z2,z70,z4,z5,z449,z6])],[(0,[z1,z9,z3,z170,z5,z6])],[(0,[z8,z2,z171,z3,z5,z6])],[(0,[z2,z9,z570,z12,z5,z6]),(0,[z2,z136,z12,z119,z5,z6]),(0,[z548,z2,z3,z4,z42,z6])],[(0,[z199,z1,z384,z4,z5,z6]),(0,[z28,z8,z2,z9,z5,z6]),(0,[z2,z3,z4,z5,z42,z419])],[(0,[z1,z2,z725,z4,z5,z6])],[],[(0,[z324,z68,z4,z12,z5,z6]),(0,[z2,z85,z12,z5,z604,z6]),(0,[z2,z3,z34,z547,z5,z6])],[(0,[z244,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z16,z354,z6]),(0,[z1,z3,z34,z170,z5,z6]),(0,[z2,z726,z3,z4,z5,z6]),(0,[z112,z2,z86,z12,z5,z6])],[(0,[z523,z1,z3,z4,z5,z6]),(0,[z2,z727,z3,z4,z5,z6])],[(0,[z1,z2,z728,z4,z5,z6])],[],[(0,[z8,z2,z3,z131,z5,z6]),(0,[z729,z2,z3,z4,z5,z6])],[(0,[z1,z13,z3,z4,z5,z61]),(0,[z1,z2,z3,z564,z5,z6]),(0,[z730,z9,z3,z12,z5,z6]),(0,[z3,z4,z16,z5,z6,z731])],[(0,[z2,z732,z3,z4,z5,z6])],[(0,[z13,z3,z4,z16,z5,z14]),(0,[z2,z3,z733,z12,z5,z6]),(0,[z734,z2,z3,z12,z5,z23]),(0,[z396,z3,z4,z65,z5,z6])],[(0,[z324,z3,z81,z12,z5,z6]),(0,[z2,z171,z3,z5,z42,z6])],[(0,[z441,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z735,z6]),(0,[z269,z3,z4,z547,z5,z6])],[(0,[z365,z2,z3,z4,z5,z388]),(0,[z247,z2,z171,z12,z5,z29]),(0,[z2,z3,z34,z16,z23,z6]),(0,[z202,z3,z4,z12,z5,z39])],[(0,[z2,z9,z208,z3,z5,z6]),(0,[z396,z68,z3,z4,z5,z6]),(0,[z1,z3,z15,z5,z45,z6]),(0,[z28,z2,z9,z12,z5,z436]),(0,[z2,z3,z4,z16,z403,z6]),(0,[z2,z3,z736,z12,z5,z6]),(0,[z2,z3,z152,z124,z5,z6]),(0,[z2,z3,z4,z5,z456,z6])],[(0,[z199,z3,z4,z5,z354,z6]),(0,[z2,z3,z737,z12,z5,z6]),(0,[z2,z513,z4,z186,z5,z6]),(0,[z2,z3,z12,z5,z168,z541]),(0,[z738,z3,z4,z16,z5,z6])],[(0,[z2,z3,z4,z16,z5,z6]),(0,[z1,z2,z362,z4,z5,z6]),(0,[z2,z3,z16,z23,z42,z6])]],
   [[(0,[z57,z396,z3,z4,z5,z6]),(0,[z2,z86,z58,z12,z5,z6]),(0,[z1,z2,z86,z3,z5,z6]),(0,[z8,z2,z3,z5,z51,z6])],[(0,[z2,z9,z3,z5,z448,z6]),(0,[z2,z739,z4,z12,z5,z6])],[(0,[z2,z86,z85,z12,z5,z6])],[(0,[z2,z3,z4,z740,z5,z6]),(0,[z2,z12,z5,z6,z741,z29]),(0,[z2,z3,z4,z5,z6,z742]),(0,[z3,z4,z5,z6,z473,z743]),(0,[z2,z3,z4,z5,z744,z6]),(0,[z2,z3,z4,z65,z42,z39])],[(0,[z2,z3,z745,z12,z5,z6]),(0,[z2,z3,z4,z5,z464,z6]),(0,[z26,z2,z3,z16,z23,z6])],[(0,[z199,z1,z9,z3,z5,z6]),(0,[z2,z3,z12,z5,z6,z746])],[(0,[z2,z405,z34,z12,z5,z6]),(0,[z2,z513,z34,z12,z5,z6]),(0,[z2,z85,z747,z12,z5,z6]),(0,[z2,z3,z12,z5,z748,z6])],[(0,[z749,z2,z3,z4,z12,z5]),(0,[z2,z9,z68,z222,z5,z6]),(0,[z3,z4,z12,z5,z6,z750]),(0,[z751,z162,z3,z4,z5,z6])],[(0,[z2,z3,z16,z5,z213,z6]),(0,[z2,z3,z34,z5,z448,z6])],[(0,[z2,z752,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z23,z278]),(0,[z396,z157,z3,z4,z5,z6])],[(0,[z2,z3,z753,z4,z5,z6]),(0,[z2,z3,z4,z5,z754,z6]),(0,[z70,z249,z4,z7,z5,z6]),(0,[z2,z3,z4,z12,z5,z755]),(0,[z3,z4,z16,z159,z42,z6])],[(0,[z2,z756,z3,z4,z5,z6]),(0,[z376,z3,z4,z12,z44,z6]),(0,[z655,z2,z55,z3,z5,z6]),(0,[z2,z4,z16,z757,z5,z6])],[(0,[z2,z3,z758,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z2,z3,z12,z5,z21,z318]),(0,[z2,z3,z234,z16,z5,z6])],[(0,[z199,z68,z4,z5,z42,z6]),(0,[z43,z1,z3,z5,z23,z6]),(0,[z1,z3,z638,z4,z5,z6]),(0,[z2,z265,z113,z12,z5,z6]),(0,[z401,z2,z3,z12,z5,z302]),(0,[z760,z3,z4,z12,z5,z6])],[(0,[z664,z1,z3,z4,z5,z6]),(0,[z2,z9,z3,z236,z5,z6]),(0,[z2,z12,z5,z23,z6,z369]),(0,[z130,z2,z362,z4,z12,z102])],[(0,[z1,z197,z3,z4,z5,z6]),(0,[z396,z3,z4,z15,z5,z6])],[(0,[z2,z3,z4,z5,z761,z6]),(0,[z2,z9,z119,z5,z448,z6]),(0,[z2,z3,z4,z132,z5,z6])],[(0,[z2,z3,z4,z762,z5,z6]),(0,[z396,z2,z9,z3,z5,z6]),(0,[z2,z3,z4,z12,z5,z763])],[(0,[z2,z3,z764,z12,z5,z6]),(0,[z2,z9,z12,z5,z449,z6])],[(0,[z1,z3,z4,z15,z5,z6]),(0,[z2,z9,z3,z12,z765,z6]),(0,[z2,z10,z3,z183,z5,z6]),(0,[z3,z4,z12,z5,z6,z743])],[(0,[z115,z3,z81,z71,z5,z6]),(0,[z2,z3,z4,z5,z766,z6]),(0,[z162,z3,z345,z12,z5,z6])],[(0,[z1,z2,z3,z5,z767,z6]),(0,[z2,z3,z34,z236,z5,z6]),(0,[z3,z5,z23,z159,z42,z6]),(0,[z768,z3,z4,z12,z5,z6])],[(0,[z2,z9,z405,z12,z5,z6]),(0,[z43,z1,z3,z4,z5,z419]),(0,[z769,z2,z3,z4,z5,z6]),(0,[z2,z540,z3,z12,z189,z6]),(0,[z2,z77,z3,z5,z42,z6]),(0,[z2,z770,z4,z12,z5,z6])],[(0,[z8,z2,z3,z289,z5,z6]),(0,[z3,z4,z12,z5,z771,z6])],[(0,[z2,z3,z4,z5,z772,z6]),(0,[z773,z3,z12,z5,z23,z6]),(0,[z2,z362,z4,z12,z5,z39])],[(0,[z1,z2,z171,z3,z5,z6]),(0,[z2,z728,z4,z12,z5,z6]),(0,[z2,z9,z157,z5,z42,z6]),(0,[z2,z9,z12,z5,z6,z204]),(0,[z179,z2,z3,z4,z5,z56])],[(0,[z2,z3,z152,z212,z5,z6]),(0,[z2,z3,z289,z12,z5,z436]),(0,[z2,z3,z16,z5,z6,z355])],[(0,[z8,z2,z9,z157,z5,z6]),(0,[z202,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z65,z189,z6])],[(0,[z2,z3,z152,z774,z5,z6]),(0,[z2,z180,z494,z12,z5,z6])],[(0,[z2,z775,z9,z3,z5,z6]),(0,[z2,z3,z5,z604,z42,z6])],[(0,[z64,z2,z261,z4,z5,z6]),(0,[z3,z4,z12,z5,z488,z61]),(0,[z13,z10,z3,z12,z5,z14]),(0,[z2,z494,z4,z12,z5,z6])],[(0,[z2,z9,z384,z12,z5,z6]),(0,[z2,z776,z3,z12,z5,z6]),(0,[z2,z107,z12,z5,z69,z6]),(0,[z315,z3,z4,z275,z5,z6])]],
   [[(0,[z2,z9,z362,z12,z5,z6])],[(0,[z322,z2,z10,z3,z5,z6]),(0,[z2,z3,z4,z777,z5,z6]),(0,[z137,z3,z411,z12,z5,z6]),(0,[z91,z2,z3,z12,z5,z778]),(0,[z2,z3,z12,z5,z6,z779])],[(0,[z2,z9,z531,z3,z5,z6]),(0,[z43,z1,z3,z34,z5,z6]),(0,[z8,z2,z246,z4,z5,z6]),(0,[z2,z3,z12,z5,z780,z6]),(0,[z254,z3,z4,z547,z5,z6]),(0,[z2,z3,z781,z12,z5,z6])],[(0,[z1,z2,z3,z131,z5,z6]),(0,[z2,z3,z5,z51,z42,z6])],[(0,[z2,z10,z3,z12,z5,z6]),(0,[z451,z2,z3,z4,z5,z6]),(0,[z8,z2,z5,z106,z23,z6]),(0,[z2,z3,z782,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z783]),(0,[z130,z2,z9,z3,z12,z102]),(0,[z2,z784,z3,z4,z5,z6])],[(0,[z785,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z5,z278])],[(0,[z2,z3,z12,z5,z6,z786]),(0,[z787,z3,z4,z5,z6,z29])],[(0,[z20,z2,z494,z12,z5,z6]),(0,[z2,z3,z4,z5,z788,z6])],[],[(0,[z25,z3,z4,z12,z554,z6]),(0,[z43,z265,z4,z12,z44,z6]),(0,[z2,z9,z5,z6,z473,z29]),(0,[z2,z3,z4,z789,z5,z6]),(0,[z2,z3,z790,z12,z5,z6])],[(0,[z2,z3,z4,z428,z5,z6]),(0,[z20,z3,z358,z116,z5,z6]),(0,[z2,z3,z791,z12,z5,z6]),(0,[z2,z12,z5,z23,z6,z792]),(0,[z2,z246,z4,z571,z5,z6])],[(0,[z2,z793,z3,z4,z5,z6]),(0,[z396,z3,z4,z12,z5,z6]),(0,[z2,z3,z124,z774,z5,z6])],[(0,[z2,z3,z794,z12,z5,z6]),(0,[z2,z3,z12,z5,z795,z6]),(0,[z8,z2,z86,z4,z5,z6]),(0,[z8,z10,z3,z11,z5,z6]),(0,[z796,z2,z4,z12,z5,z6]),(0,[z797,z3,z4,z12,z5,z6])],[(0,[z1,z2,z3,z5,z51,z6]),(0,[z2,z798,z265,z12,z5,z6])],[(0,[z2,z3,z4,z5,z6,z799]),(0,[z26,z2,z3,z476,z23,z6])],[(0,[z43,z3,z4,z44,z42,z6]),(0,[z254,z4,z12,z5,z69,z6]),(0,[z28,z269,z4,z12,z69,z6]),(0,[z800,z2,z86,z12,z5,z6]),(0,[z2,z3,z801,z34,z5,z6]),(0,[z2,z802,z3,z4,z5,z6])],[(0,[z2,z10,z747,z12,z5,z6]),(0,[z2,z55,z3,z576,z5,z6]),(0,[z2,z3,z34,z12,z155,z6])],[(0,[z247,z8,z2,z4,z5,z29]),(0,[z269,z3,z320,z12,z5,z6]),(0,[z2,z3,z4,z5,z803,z6]),(0,[z2,z804,z4,z12,z5,z6])],[(0,[z28,z2,z12,z5,z189,z6]),(0,[z2,z3,z4,z805,z5,z6]),(0,[z2,z3,z4,z806,z5,z6])],[(0,[z8,z2,z10,z85,z5,z6])],[(0,[z25,z3,z12,z15,z23,z6])],[(0,[z807,z2,z3,z12,z5,z6])],[(0,[z2,z808,z3,z12,z5,z6])],[(0,[z2,z151,z12,z5,z21,z6]),(0,[z2,z513,z113,z12,z5,z6]),(0,[z2,z362,z4,z12,z5,z6])],[(0,[z2,z3,z211,z5,z23,z6])],[(0,[z2,z208,z363,z3,z5,z6]),(0,[z2,z3,z4,z809,z5,z6])],[(0,[z2,z810,z4,z12,z5,z6]),(0,[z43,z1,z265,z4,z5,z6])],[(0,[z811,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z812]),(0,[z2,z246,z4,z5,z42,z6])],[(0,[z43,z3,z4,z12,z354,z6]),(0,[z8,z2,z3,z113,z5,z6])],[(0,[z2,z813,z3,z12,z5,z6]),(0,[z2,z10,z3,z260,z5,z6]),(0,[z2,z86,z12,z5,z6,z102]),(0,[z91,z2,z3,z5,z421,z92])],[(0,[z2,z3,z4,z12,z5,z814])]],
   [[(0,[z8,z2,z267,z3,z5,z6]),(0,[z2,z3,z260,z5,z23,z6]),(0,[z2,z86,z12,z5,z541,z6])],[(0,[z2,z3,z815,z12,z5,z6]),(0,[z2,z3,z4,z5,z816,z6]),(0,[z2,z3,z4,z817,z5,z6]),(0,[z818,z3,z4,z12,z5,z6])],[(0,[z2,z3,z4,z186,z5,z585]),(0,[z2,z3,z4,z5,z819,z6]),(0,[z2,z3,z361,z12,z5,z6]),(0,[z2,z55,z3,z5,z605,z6])],[(0,[z2,z820,z3,z12,z5,z6]),(0,[z2,z3,z4,z821,z5,z6]),(0,[z90,z2,z3,z12,z5,z6]),(0,[z1,z3,z4,z5,z6,z279]),(0,[z2,z9,z3,z12,z5,z585]),(0,[z2,z9,z12,z5,z6,z502]),(0,[z2,z3,z12,z5,z822,z6]),(0,[z3,z12,z5,z23,z159,z6]),(0,[z2,z3,z4,z823,z5,z6])],[(0,[z1,z2,z3,z289,z5,z6]),(0,[z8,z162,z3,z4,z5,z6]),(0,[z28,z2,z4,z547,z69,z6]),(0,[z247,z396,z3,z4,z5,z6])],[(0,[z2,z824,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z604,z6]),(0,[z2,z3,z183,z5,z74,z6])],[(0,[z8,z2,z825,z3,z5,z6]),(0,[z2,z3,z113,z236,z5,z6])],[(0,[z0,z2,z3,z5,z23,z6])],[(0,[z1,z2,z9,z157,z5,z6]),(0,[z91,z2,z3,z12,z5,z432]),(0,[z2,z3,z230,z183,z5,z6])],[(0,[z2,z826,z4,z12,z5,z6]),(0,[z2,z3,z5,z189,z42,z6]),(0,[z2,z3,z4,z219,z42,z6]),(0,[z2,z86,z12,z5,z6,z92])],[(0,[z57,z363,z58,z12,z5,z6]),(0,[z2,z405,z4,z5,z42,z6]),(0,[z2,z3,z34,z12,z5,z585]),(0,[z2,z10,z3,z12,z5,z278]),(0,[z2,z53,z12,z5,z6,z29]),(0,[z2,z328,z3,z5,z6,z204]),(0,[z2,z3,z12,z5,z168,z21])],[],[(0,[z2,z3,z4,z12,z5,z827]),(0,[z2,z3,z5,z23,z6,z375]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z396,z3,z52,z4,z5,z6])],[(0,[z57,z58,z34,z12,z5,z6]),(0,[z2,z10,z12,z5,z6,z651])],[(0,[z1,z3,z4,z5,z6,z375]),(0,[z8,z2,z3,z5,z114,z6]),(0,[z2,z3,z4,z547,z5,z6]),(0,[z2,z3,z12,z5,z829,z6]),(0,[z2,z3,z4,z5,z830,z6])],[(0,[z8,z2,z363,z3,z5,z6]),(0,[z1,z2,z246,z4,z5,z6]),(0,[z2,z9,z4,z12,z5,z436]),(0,[z831,z3,z4,z12,z5,z6]),(0,[z832,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z833,z5,z6]),(0,[z115,z3,z81,z12,z5,z6]),(0,[z2,z3,z12,z5,z21,z644]),(0,[z2,z9,z12,z5,z6,z436])],[(0,[z1,z2,z5,z106,z23,z6]),(0,[z2,z3,z12,z5,z6,z834]),(0,[z2,z3,z345,z16,z5,z6])],[(0,[z2,z3,z4,z835,z5,z6])],[(0,[z2,z336,z3,z4,z5,z6]),(0,[z43,z513,z4,z12,z44,z6]),(0,[z25,z3,z4,z12,z720,z6]),(0,[z28,z2,z9,z16,z5,z6])],[(0,[z2,z3,z4,z836,z5,z6]),(0,[z1,z363,z3,z58,z5,z6]),(0,[z2,z837,z4,z12,z5,z6])],[(0,[z2,z838,z4,z12,z5,z6]),(0,[z100,z3,z4,z5,z42,z61]),(0,[z2,z12,z5,z6,z323,z839]),(0,[z2,z9,z3,z5,z42,z6]),(0,[z840,z2,z3,z4,z5,z6])],[],[(0,[z630,z58,z4,z12,z5,z6])],[(0,[z2,z328,z10,z3,z5,z6]),(0,[z254,z3,z320,z12,z5,z6]),(0,[z629,z2,z3,z4,z5,z561]),(0,[z197,z3,z4,z141,z5,z17])],[(0,[z1,z2,z86,z4,z5,z6]),(0,[z2,z3,z52,z12,z5,z624]),(0,[z2,z3,z230,z12,z5,z6]),(0,[z2,z3,z123,z5,z221,z6])],[(0,[z2,z3,z12,z47,z213,z6]),(0,[z2,z136,z3,z5,z42,z6]),(0,[z841,z3,z4,z5,z42,z6])],[(0,[z2,z86,z3,z12,z5,z6])],[(0,[z0,z2,z3,z34,z5,z6]),(0,[z2,z55,z3,z774,z5,z6])],[(0,[z2,z3,z428,z5,z23,z6]),(0,[z351,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z16,z330,z6]),(0,[z513,z4,z12,z5,z44,z6]),(0,[z2,z9,z157,z12,z5,z241])],[(0,[z2,z3,z4,z12,z5,z842]),(0,[z2,z3,z4,z843,z5,z6]),(0,[z130,z2,z246,z4,z12,z102])],[(0,[z2,z9,z68,z5,z42,z6]),(0,[z264,z2,z3,z4,z354,z6]),(1,[z2,z86,z5,z42,z6]),(0,[z2,z101,z4,z5,z449,z6])]],
   [[(0,[z1,z2,z10,z85,z5,z6]),(0,[z2,z9,z12,z5,z6,z538]),(0,[z2,z86,z12,z5,z221,z6])],[(0,[z8,z1,z9,z3,z5,z6]),(0,[z270,z1,z3,z34,z5,z6]),(0,[z2,z3,z12,z564,z5,z6]),(0,[z844,z3,z4,z12,z5,z6])],[(0,[z1,z13,z3,z4,z5,z6]),(0,[z43,z3,z4,z236,z44,z6]),(0,[z90,z2,z3,z5,z6,z375]),(0,[z845,z2,z3,z4,z5,z6]),(0,[z845,z3,z4,z119,z5,z6]),(0,[z2,z3,z12,z5,z6,z846]),(0,[z2,z847,z3,z12,z5,z6]),(0,[z2,z3,z345,z132,z5,z6])],[(0,[z2,z513,z4,z12,z5,z6]),(0,[z199,z1,z261,z4,z5,z6]),(0,[z134,z2,z3,z5,z23,z6]),(0,[z28,z2,z9,z551,z5,z6]),(0,[z2,z848,z12,z5,z23,z6])],[(0,[z162,z3,z131,z12,z5,z6])],[(0,[z849,z2,z3,z12,z5,z6]),(0,[z2,z3,z4,z850,z5,z6]),(0,[z130,z1,z2,z3,z4,z102]),(0,[z441,z3,z4,z78,z5,z6]),(0,[z2,z3,z4,z5,z448,z6])],[(0,[z2,z851,z3,z4,z5,z6])],[],[(0,[z199,z1,z58,z4,z5,z6]),(0,[z852,z3,z4,z12,z5,z6])],[(0,[z1,z3,z4,z433,z5,z6]),(0,[z2,z10,z3,z853,z5,z6]),(0,[z3,z34,z12,z5,z159,z6]),(0,[z2,z494,z52,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z854])],[(0,[z2,z3,z4,z5,z855,z6]),(0,[z1,z2,z3,z113,z5,z6]),(0,[z3,z4,z12,z5,z720,z6]),(0,[z2,z86,z12,z5,z281,z6]),(0,[z2,z856,z3,z4,z5,z6]),(0,[z179,z396,z3,z4,z5,z6])],[(0,[z2,z857,z3,z12,z5,z6])],[(0,[z2,z9,z12,z549,z5,z6]),(0,[z91,z2,z151,z12,z5,z6]),(0,[z858,z10,z3,z12,z5,z6]),(0,[z2,z3,z551,z5,z23,z6]),(0,[z2,z109,z4,z12,z615,z6]),(0,[z2,z86,z12,z5,z6,z56]),(0,[z2,z3,z4,z5,z859,z6])],[(0,[z1,z2,z267,z3,z5,z6]),(0,[z202,z3,z345,z12,z5,z6])],[(0,[z2,z540,z157,z12,z5,z6]),(0,[z2,z3,z12,z5,z21,z666])],[(0,[z2,z860,z3,z12,z5,z6])],[(0,[z2,z9,z246,z12,z5,z6]),(0,[z2,z109,z3,z12,z213,z6])],[(0,[z1,z162,z3,z4,z5,z6]),(0,[z2,z9,z344,z16,z5,z6]),(0,[z2,z109,z12,z119,z23,z6]),(0,[z861,z3,z4,z5,z42,z6])],[(0,[z2,z3,z4,z236,z5,z6]),(0,[z8,z13,z3,z4,z5,z14]),(0,[z2,z9,z513,z12,z5,z6]),(0,[z2,z3,z12,z288,z23,z6]),(0,[z2,z4,z12,z5,z862,z29])],[],[(0,[z863,z2,z3,z4,z5,z6]),(0,[z10,z249,z3,z12,z5,z6]),(0,[z2,z3,z4,z547,z5,z278])],[(0,[z2,z3,z4,z5,z864,z6]),(0,[z2,z540,z12,z5,z6,z29]),(0,[z2,z10,z3,z12,z5,z865]),(0,[z2,z86,z70,z12,z5,z6]),(0,[z866,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z357]),(0,[z8,z2,z9,z58,z5,z6]),(0,[z2,z867,z3,z12,z5,z6]),(0,[z2,z3,z205,z16,z5,z6])],[(0,[z2,z3,z4,z12,z765,z6]),(0,[z2,z3,z12,z5,z23,z436]),(0,[z63,z3,z4,z159,z42,z6]),(0,[z396,z3,z4,z868,z5,z6])],[(0,[z134,z2,z3,z34,z5,z6]),(0,[z2,z3,z12,z569,z23,z6])],[(0,[z2,z10,z3,z27,z5,z6]),(0,[z2,z3,z12,z869,z5,z6])],[(0,[z2,z3,z581,z12,z5,z6]),(0,[z520,z3,z116,z12,z5,z6]),(0,[z28,z2,z320,z12,z69,z6]),(0,[z2,z3,z582,z5,z348,z6])],[(0,[z508,z58,z4,z12,z5,z6]),(0,[z2,z3,z870,z12,z5,z6]),(0,[z1,z2,z3,z5,z114,z6]),(0,[z2,z3,z113,z12,z5,z585]),(0,[z2,z3,z12,z5,z6,z871]),(0,[z872,z2,z3,z4,z5,z6])],[(0,[z1,z2,z363,z3,z5,z6]),(0,[z2,z9,z12,z5,z6,z562]),(0,[z2,z3,z4,z5,z873,z6]),(0,[z2,z10,z3,z5,z354,z6])],[(0,[z8,z2,z874,z4,z5,z6]),(0,[z875,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z876,z6])],[(0,[z501,z58,z4,z12,z5,z6]),(0,[z25,z2,z3,z4,z354,z6]),(0,[z1,z3,z4,z5,z6,z877]),(0,[z2,z3,z232,z16,z5,z6]),(0,[z2,z3,z12,z878,z5,z6]),(0,[z2,z109,z4,z12,z5,z436])],[(0,[z2,z3,z12,z5,z767,z6]),(0,[z2,z4,z12,z119,z879,z6])]],
   [[(0,[z2,z3,z4,z880,z5,z6]),(0,[z2,z3,z289,z551,z5,z6]),(0,[z2,z3,z12,z5,z6,z881]),(0,[z130,z162,z3,z4,z12,z102])],[(0,[z2,z9,z3,z535,z5,z6])],[(0,[z8,z2,z3,z5,z213,z6]),(1,[z396,z3,z5,z23,z6])],[(0,[z1,z2,z3,z882,z5,z6]),(0,[z196,z1,z3,z4,z5,z6]),(1,[z8,z2,z86,z5,z6]),(0,[z2,z3,z4,z883,z5,z6]),(0,[z322,z2,z3,z5,z23,z6]),(0,[z2,z4,z12,z5,z6,z369])],[(0,[z244,z2,z3,z4,z24,z6]),(0,[z247,z2,z34,z12,z5,z29])],[(0,[z2,z3,z4,z5,z884,z6])],[(0,[z8,z2,z3,z5,z74,z6]),(0,[z2,z3,z232,z12,z5,z419]),(1,[z28,z2,z12,z189,z6])],[(0,[z156,z2,z9,z12,z5,z6])],[(0,[z2,z3,z99,z5,z42,z6]),(0,[z2,z3,z34,z535,z5,z6]),(0,[z2,z3,z4,z5,z6,z885])],[(0,[z2,z3,z12,z5,z6,z886]),(0,[z2,z3,z186,z5,z23,z6]),(0,[z3,z887,z4,z5,z42,z6]),(0,[z2,z362,z345,z12,z5,z6])],[(0,[z2,z725,z4,z12,z5,z6]),(0,[z888,z2,z3,z12,z5,z6])],[(0,[z2,z3,z4,z889,z5,z6])],[(0,[z2,z4,z12,z119,z700,z6]),(0,[z2,z107,z120,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z890]),(0,[z296,z2,z3,z4,z5,z279]),(0,[z244,z396,z3,z4,z5,z6])],[(0,[z2,z891,z3,z12,z5,z6]),(0,[z8,z2,z3,z892,z5,z6]),(0,[z893,z3,z4,z12,z5,z6])],[(0,[z2,z3,z12,z5,z6,z894]),(0,[z2,z9,z3,z186,z5,z6]),(0,[z2,z3,z4,z774,z5,z6])],[(0,[z2,z3,z4,z895,z5,z6]),(0,[z896,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z897,z5,z6]),(0,[z2,z3,z34,z12,z233,z6]),(0,[z162,z3,z12,z5,z23,z6]),(0,[z2,z3,z12,z5,z778,z92]),(0,[z396,z3,z4,z5,z5,z6])],[(0,[z898,z2,z3,z4,z5,z6]),(0,[z2,z540,z3,z5,z42,z6]),(0,[z2,z9,z16,z398,z5,z6]),(0,[z2,z10,z3,z899,z5,z6]),(0,[z2,z3,z4,z12,z5,z900]),(0,[z22,z396,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z901,z6])],[(0,[z324,z80,z3,z12,z5,z6]),(0,[z28,z2,z9,z12,z189,z6]),(0,[z2,z3,z5,z42,z6,z204]),(1,[z2,z3,z12,z902,z6])],[(0,[z2,z3,z4,z12,z5,z903]),(0,[z1,z2,z3,z4,z904,z6]),(0,[z2,z3,z4,z16,z5,z436])],[(0,[z2,z10,z3,z358,z5,z6]),(0,[z2,z9,z261,z12,z5,z6]),(0,[z2,z86,z12,z47,z5,z6]),(0,[z396,z3,z4,z141,z5,z6])],[(0,[z396,z3,z4,z78,z5,z6])],[(0,[z2,z3,z905,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z906]),(0,[z2,z3,z34,z186,z5,z6]),(0,[z2,z3,z5,z23,z464,z6])],[(0,[z43,z3,z4,z12,z44,z585]),(0,[z2,z3,z4,z907,z5,z6]),(0,[z2,z3,z12,z5,z51,z6]),(1,[z396,z3,z34,z5,z6])],[(0,[z322,z2,z3,z34,z5,z6]),(0,[z2,z10,z3,z141,z5,z17]),(0,[z2,z3,z4,z908,z5,z6])],[(0,[z2,z9,z58,z12,z5,z6])],[(1,[z2,z4,z12,z879,z6])],[(0,[z8,z3,z4,z5,z159,z6]),(0,[z2,z909,z4,z12,z5,z6]),(0,[z828,z254,z3,z4,z5,z6])],[(0,[z2,z3,z27,z5,z23,z6]),(0,[z2,z86,z16,z5,z23,z6])],[(0,[z1,z13,z3,z4,z5,z388]),(0,[z2,z3,z4,z910,z5,z6]),(0,[z10,z3,z12,z5,z6,z95]),(0,[z2,z911,z3,z12,z5,z6]),(0,[z2,z3,z4,z912,z5,z6])],[(0,[z2,z136,z58,z12,z5,z6]),(0,[z28,z8,z2,z4,z69,z6]),(0,[z3,z4,z5,z6,z375,z95])],[(0,[z1,z13,z3,z4,z5,z14]),(0,[z25,z3,z4,z535,z15,z6]),(0,[z2,z4,z12,z5,z913,z6]),(0,[z2,z4,z12,z5,z6,z792]),(0,[z451,z3,z4,z5,z159,z6])]],
   [[(0,[z2,z914,z3,z4,z5,z6]),(0,[z2,z487,z3,z4,z5,z6])],[(0,[z269,z9,z3,z12,z5,z6]),(0,[z2,z10,z3,z915,z5,z6]),(0,[z2,z3,z34,z12,z373,z6]),(0,[z2,z3,z131,z16,z5,z6])],[(0,[z43,z3,z4,z5,z354,z6]),(0,[z2,z916,z3,z12,z5,z6])],[(0,[z1,z2,z9,z58,z5,z6]),(0,[z26,z2,z3,z12,z902,z6]),(0,[z2,z917,z4,z12,z5,z6])],[(0,[z3,z4,z918,z12,z5,z6]),(0,[z396,z3,z5,z23,z42,z6]),(0,[z2,z3,z34,z23,z42,z6])],[(0,[z2,z70,z75,z4,z5,z6]),(0,[z544,z3,z4,z12,z5,z14]),(0,[z2,z9,z3,z139,z5,z6]),(0,[z2,z919,z12,z5,z23,z6]),(0,[z2,z3,z34,z47,z464,z6])],[(0,[z2,z3,z4,z920,z5,z6]),(0,[z2,z3,z921,z12,z5,z6])],[(0,[z2,z3,z922,z12,z5,z6]),(0,[z1,z3,z4,z5,z6,z426]),(0,[z1,z3,z4,z5,z6,z427]),(0,[z2,z3,z4,z12,z5,z585])],[(0,[z2,z923,z3,z4,z5,z6]),(0,[z269,z3,z34,z12,z5,z6])],[(0,[z2,z3,z774,z291,z5,z6])],[(0,[z57,z58,z4,z12,z5,z6]),(0,[z2,z3,z320,z12,z5,z278]),(0,[z430,z2,z3,z4,z12,z102])],[(0,[z2,z3,z924,z12,z5,z6])],[(0,[z2,z3,z34,z139,z5,z6]),(0,[z26,z2,z3,z23,z42,z6]),(0,[z162,z3,z4,z16,z5,z6])],[(0,[z2,z672,z10,z12,z5,z6]),(0,[z2,z86,z12,z5,z925,z6]),(0,[z2,z3,z12,z47,z902,z6]),(0,[z63,z396,z3,z4,z5,z6]),(0,[z2,z926,z3,z12,z5,z6])],[(0,[z25,z9,z3,z12,z15,z6]),(0,[z2,z3,z4,z5,z6,z927]),(0,[z2,z3,z4,z390,z42,z6])],[(0,[z2,z9,z12,z5,z612,z6]),(0,[z2,z3,z4,z12,z763,z102])],[(0,[z2,z3,z4,z928,z5,z6])],[(0,[z190,z2,z3,z303,z5,z6])],[(0,[z2,z929,z4,z12,z5,z6]),(0,[z2,z3,z131,z132,z5,z6])],[(0,[z1,z2,z3,z5,z74,z6]),(0,[z13,z3,z4,z5,z42,z14]),(0,[z2,z540,z3,z12,z280,z6]),(0,[z2,z3,z4,z16,z569,z6]),(0,[z112,z3,z12,z5,z198,z6]),(0,[z2,z3,z4,z5,z930,z6])],[(0,[z2,z540,z68,z12,z5,z6]),(0,[z2,z3,z99,z535,z5,z6]),(0,[z931,z3,z4,z12,z5,z6]),(0,[z932,z3,z4,z12,z5,z6]),(0,[z396,z552,z3,z4,z5,z6])],[(0,[z25,z3,z34,z12,z15,z6]),(0,[z2,z3,z4,z5,z6,z933]),(0,[z2,z10,z85,z16,z5,z6]),(0,[z2,z3,z53,z5,z42,z6])],[(0,[z2,z9,z439,z12,z5,z6]),(0,[z2,z540,z86,z12,z5,z6]),(0,[z179,z2,z3,z4,z5,z173]),(0,[z2,z3,z4,z16,z803,z6]),(0,[z2,z3,z4,z183,z65,z39])],[(0,[z1,z2,z934,z4,z5,z6]),(0,[z2,z935,z86,z12,z5,z6])],[(0,[z2,z4,z12,z5,z106,z6]),(0,[z2,z10,z3,z12,z5,z436]),(0,[z2,z10,z12,z5,z106,z6]),(0,[z28,z396,z3,z4,z5,z6]),(0,[z2,z3,z161,z16,z5,z6])],[(0,[z2,z10,z3,z331,z5,z6]),(0,[z2,z109,z4,z16,z119,z6]),(0,[z2,z936,z3,z12,z5,z6])],[(0,[z396,z3,z4,z116,z5,z6]),(0,[z2,z937,z34,z12,z5,z6]),(0,[z2,z3,z4,z5,z938,z6])],[(0,[z2,z3,z4,z5,z939,z6]),(0,[z8,z90,z2,z3,z5,z6])],[(0,[z1,z3,z513,z4,z5,z6]),(0,[z8,z2,z108,z3,z5,z6]),(0,[z2,z86,z97,z12,z5,z6]),(0,[z2,z86,z12,z65,z5,z6])],[(0,[z2,z108,z3,z12,z5,z6]),(1,[z787,z3,z4,z5,z6]),(0,[z2,z86,z12,z5,z198,z6]),(0,[z162,z3,z4,z132,z5,z6])],[(0,[z2,z3,z4,z12,z5,z940]),(0,[z8,z2,z3,z232,z5,z6]),(0,[z2,z3,z4,z16,z657,z6])],[(0,[z2,z86,z12,z5,z189,z6]),(0,[z2,z3,z4,z941,z5,z6])]],
   [[(0,[z2,z3,z4,z942,z5,z6]),(0,[z2,z3,z52,z12,z5,z88])],[(0,[z25,z2,z86,z12,z5,z6])],[(0,[z2,z3,z4,z943,z5,z6]),(0,[z944,z9,z3,z12,z5,z6]),(0,[z396,z3,z945,z4,z5,z6]),(0,[z2,z3,z946,z12,z5,z6])],[(0,[z199,z1,z3,z4,z5,z6]),(0,[z8,z2,z947,z3,z5,z6]),(0,[z2,z9,z180,z12,z5,z6]),(0,[z2,z747,z19,z12,z5,z6]),(0,[z130,z2,z3,z4,z12,z763])],[(0,[z3,z4,z918,z170,z5,z6]),(0,[z2,z3,z4,z16,z613,z6]),(0,[z2,z86,z141,z12,z5,z6])],[(0,[z1,z10,z3,z5,z6,z61]),(0,[z1,z462,z3,z4,z5,z6])],[(0,[z2,z86,z4,z5,z42,z6]),(0,[z2,z3,z234,z5,z42,z6])],[(0,[z2,z3,z113,z186,z5,z6]),(0,[z2,z3,z4,z948,z5,z6]),(0,[z2,z3,z4,z12,z65,z39])],[(0,[z1,z3,z4,z5,z159,z6]),(0,[z501,z2,z9,z12,z5,z6]),(0,[z254,z9,z3,z12,z5,z6]),(0,[z396,z949,z3,z4,z5,z6])],[(0,[z8,z20,z3,z116,z5,z6]),(0,[z2,z9,z5,z449,z42,z6]),(0,[z441,z3,z12,z5,z23,z6]),(0,[z950,z2,z3,z4,z5,z6])],[(0,[z872,z254,z3,z4,z5,z6])],[(0,[z2,z109,z4,z12,z879,z6]),(0,[z951,z3,z4,z12,z5,z6])],[(0,[z2,z3,z12,z5,z952,z6]),(0,[z2,z9,z641,z12,z5,z6]),(0,[z249,z3,z34,z12,z5,z6])],[],[(0,[z2,z3,z953,z12,z5,z6]),(0,[z2,z3,z954,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z955])],[(0,[z2,z3,z956,z12,z5,z6]),(0,[z2,z4,z12,z5,z596,z29]),(0,[z254,z3,z34,z12,z5,z6])],[(0,[z2,z3,z4,z957,z5,z6]),(0,[z2,z3,z4,z5,z6,z958])],[(0,[z8,z2,z540,z3,z5,z6]),(0,[z3,z4,z12,z5,z44,z585]),(0,[z959,z2,z3,z12,z5,z6]),(0,[z162,z10,z3,z12,z5,z6])],[(0,[z960,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z141,z5,z854])],[(0,[z2,z109,z12,z119,z604,z6])],[(0,[z664,z2,z3,z4,z42,z6]),(0,[z8,z2,z3,z4,z5,z961]),(0,[z100,z396,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z6,z962])],[(0,[z2,z3,z607,z12,z5,z6]),(0,[z2,z3,z4,z963,z5,z6]),(0,[z2,z3,z12,z5,z23,z419]),(0,[z2,z86,z12,z5,z42,z6])],[(0,[z2,z3,z5,z42,z6,z323]),(0,[z2,z3,z124,z303,z5,z6]),(0,[z153,z2,z86,z12,z5,z6]),(0,[z396,z3,z4,z5,z348,z6]),(0,[z2,z4,z12,z5,z6,z964])],[(0,[z315,z2,z9,z3,z5,z6]),(0,[z2,z10,z3,z5,z6,z473]),(0,[z965,z269,z3,z4,z5,z6]),(0,[z91,z2,z3,z12,z5,z92])],[(0,[z26,z8,z2,z3,z23,z6]),(0,[z2,z9,z293,z12,z5,z6]),(0,[z3,z4,z12,z5,z966,z61]),(0,[z254,z85,z4,z12,z5,z6])],[(0,[z3,z810,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z967]),(0,[z2,z362,z131,z12,z5,z6])],[(0,[z2,z336,z10,z3,z5,z6]),(0,[z2,z3,z4,z968,z5,z6]),(0,[z2,z9,z3,z16,z42,z6]),(0,[z969,z2,z3,z4,z5,z6])],[(0,[z8,z2,z151,z4,z5,z6]),(0,[z1,z325,z3,z4,z5,z6]),(0,[z2,z10,z3,z970,z5,z6]),(0,[z62,z2,z4,z12,z5,z29])],[(0,[z2,z151,z81,z12,z5,z6]),(0,[z1,z2,z3,z5,z6,z971]),(0,[z523,z1,z3,z5,z23,z6]),(1,[z254,z9,z12,z5,z6]),(0,[z2,z3,z205,z5,z448,z6]),(0,[z2,z3,z4,z972,z5,z6]),(0,[z2,z86,z34,z12,z23,z6])],[(0,[z2,z3,z12,z5,z6,z973])],[(0,[z2,z3,z12,z5,z6,z974]),(0,[z2,z3,z4,z12,z466,z39]),(0,[z2,z3,z12,z5,z23,z975]),(0,[z976,z2,z3,z12,z5,z23])],[(0,[z396,z3,z58,z4,z5,z6]),(0,[z2,z3,z4,z977,z5,z6]),(0,[z2,z10,z151,z12,z5,z6]),(0,[z978,z2,z3,z12,z5,z6]),(0,[z2,z979,z3,z4,z5,z6])]],
   [[],[(0,[z0,z3,z4,z15,z5,z6]),(0,[z25,z3,z99,z12,z15,z6]),(0,[z2,z980,z12,z5,z6,z61]),(0,[z396,z3,z85,z4,z5,z6]),(0,[z247,z2,z4,z12,z5,z29]),(0,[z2,z3,z34,z16,z42,z6])],[(0,[z2,z3,z4,z12,z5,z981]),(0,[z2,z3,z4,z547,z5,z436])],[(0,[z1,z3,z58,z4,z5,z6]),(0,[z20,z3,z411,z12,z5,z6]),(0,[z2,z982,z4,z12,z5,z6]),(0,[z2,z3,z983,z12,z5,z6]),(0,[z629,z2,z3,z4,z5,z56])],[(0,[z2,z3,z984,z12,z5,z6]),(0,[z43,z9,z3,z12,z44,z6]),(0,[z2,z4,z12,z5,z6,z985]),(0,[z986,z3,z4,z5,z42,z6]),(0,[z162,z362,z4,z12,z5,z6])],[(0,[z2,z3,z4,z987,z5,z6]),(0,[z2,z3,z4,z535,z5,z6]),(0,[z2,z3,z12,z5,z114,z6]),(0,[z441,z3,z4,z16,z5,z6])],[(0,[z2,z107,z109,z12,z5,z6]),(0,[z2,z171,z328,z3,z5,z6])],[(0,[z179,z2,z3,z4,z5,z262]),(0,[z2,z3,z12,z5,z6,z988])],[(0,[z3,z58,z4,z428,z5,z6]),(0,[z1,z3,z4,z5,z6,z499]),(0,[z2,z989,z3,z12,z5,z6])],[(0,[z1,z2,z108,z3,z5,z6]),(0,[z3,z4,z5,z42,z6,z990])],[(0,[z2,z10,z3,z211,z5,z6]),(0,[z8,z2,z9,z75,z5,z6]),(0,[z396,z3,z4,z5,z23,z6]),(0,[z2,z3,z4,z16,z383,z6])],[(0,[z1,z2,z3,z232,z5,z6]),(0,[z43,z3,z34,z12,z44,z6]),(0,[z423,z2,z3,z4,z42,z6]),(0,[z991,z3,z4,z12,z5,z6])],[(0,[z441,z3,z4,z5,z17,z6])],[(0,[z2,z9,z12,z665,z5,z6]),(0,[z1,z3,z4,z457,z5,z6]),(0,[z28,z2,z12,z114,z69,z6]),(0,[z2,z3,z52,z12,z5,z21])],[(0,[z2,z3,z992,z12,z5,z6]),(0,[z2,z3,z124,z5,z233,z6]),(0,[z993,z3,z4,z12,z5,z6])],[(0,[z2,z994,z3,z4,z5,z6]),(0,[z2,z85,z289,z12,z5,z6]),(0,[z2,z4,z12,z5,z69,z436]),(0,[z2,z86,z12,z5,z106,z6]),(0,[z2,z34,z12,z5,z106,z6])],[(0,[z2,z9,z3,z995,z5,z6])],[(0,[z996,z2,z3,z4,z5,z6]),(0,[z416,z2,z3,z4,z5,z117]),(0,[z2,z3,z4,z16,z5,z419]),(0,[z2,z3,z4,z997,z5,z6]),(0,[z28,z2,z34,z12,z69,z6]),(0,[z2,z3,z16,z5,z604,z6])],[(0,[z2,z9,z3,z12,z5,z998]),(0,[z2,z344,z4,z128,z5,z6])],[(0,[z2,z3,z4,z5,z999,z6]),(0,[z2,z261,z4,z7,z5,z6]),(0,[z2,z3,z4,z186,z5,z6]),(0,[z2,z109,z4,z119,z448,z6]),(0,[z1000,z3,z4,z5,z42,z6])],[(0,[z2,z58,z607,z12,z5,z6]),(0,[z2,z86,z12,z5,z14,z6]),(0,[z2,z3,z422,z12,z5,z6]),(0,[z2,z86,z12,z5,z39,z6]),(0,[z2,z3,z5,z42,z6,z491])],[(0,[z715,z10,z3,z12,z5,z6]),(0,[z2,z3,z4,z1001,z5,z6])],[(0,[z2,z3,z1002,z12,z5,z6])],[(0,[z2,z3,z34,z12,z477,z6]),(0,[z2,z3,z4,z5,z1003,z6]),(0,[z28,z2,z3,z12,z189,z6])],[],[(0,[z2,z3,z34,z12,z343,z6]),(0,[z1,z3,z4,z515,z5,z6]),(0,[z2,z3,z476,z5,z23,z6]),(0,[z396,z3,z12,z5,z23,z6]),(1,[z2,z3,z4,z803,z6])],[(0,[z115,z3,z953,z12,z5,z6]),(0,[z100,z8,z3,z4,z5,z61])],[(0,[z2,z3,z34,z12,z5,z6]),(0,[z2,z3,z1004,z12,z5,z6]),(0,[z3,z4,z12,z5,z6,z1005])],[(0,[z2,z12,z5,z913,z45,z6]),(0,[z2,z3,z4,z1006,z5,z6]),(0,[z2,z9,z328,z5,z6,z29])],[(0,[z1007,z2,z3,z4,z5,z6]),(0,[z134,z3,z4,z15,z5,z6]),(0,[z2,z3,z1008,z12,z5,z6])],[(0,[z43,z1,z3,z113,z5,z6]),(0,[z1,z2,z540,z3,z5,z6]),(0,[z2,z3,z12,z5,z1009,z6])],[(0,[z2,z3,z4,z1010,z5,z6]),(0,[z768,z3,z4,z16,z5,z6])]],
   [[(0,[z2,z9,z747,z12,z5,z6])],[(0,[z2,z4,z12,z879,z69,z6]),(0,[z1011,z2,z3,z4,z5,z6])],[(0,[z179,z2,z3,z5,z23,z56]),(0,[z162,z246,z4,z12,z5,z6])],[(0,[z2,z3,z4,z1012,z5,z6]),(0,[z2,z3,z4,z1013,z5,z6]),(0,[z247,z2,z328,z4,z5,z29]),(0,[z2,z916,z12,z65,z5,z6])],[(0,[z1,z58,z85,z4,z5,z6]),(0,[z2,z3,z1014,z12,z5,z6]),(0,[z197,z3,z152,z4,z5,z6])],[(0,[z269,z3,z4,z12,z5,z6]),(0,[z2,z3,z1015,z12,z5,z6]),(0,[z2,z3,z4,z1016,z5,z6]),(0,[z2,z362,z12,z5,z23,z6])],[],[(0,[z2,z1017,z4,z12,z5,z6])],[(0,[z1,z2,z151,z4,z5,z6]),(0,[z2,z97,z703,z4,z5,z6]),(0,[z3,z4,z12,z5,z6,z731])],[(0,[z199,z9,z68,z12,z5,z6]),(0,[z8,z2,z1018,z4,z5,z6]),(0,[z2,z3,z4,z139,z5,z6]),(0,[z1019,z2,z3,z4,z5,z6]),(0,[z1020,z2,z3,z4,z5,z6])],[(0,[z25,z3,z4,z15,z42,z6])],[(0,[z2,z3,z1021,z12,z5,z6])],[(0,[z2,z1022,z3,z12,z5,z6]),(0,[z2,z10,z3,z5,z532,z6]),(0,[z2,z1023,z3,z12,z5,z6])],[(0,[z1,z3,z170,z5,z23,z6]),(0,[z28,z2,z9,z5,z42,z6]),(0,[z2,z3,z16,z564,z5,z6]),(0,[z2,z3,z12,z5,z23,z814]),(0,[z2,z784,z3,z5,z23,z6])],[(0,[z2,z3,z12,z5,z1024,z6]),(0,[z2,z10,z3,z16,z5,z6]),(0,[z845,z3,z4,z5,z448,z6])],[],[(0,[z2,z3,z4,z1025,z5,z6]),(0,[z2,z9,z3,z12,z1026,z6])],[(1,[z1,z9,z58,z5,z6]),(0,[z1,z2,z3,z984,z5,z6]),(0,[z100,z322,z3,z4,z5,z61]),(0,[z2,z1027,z3,z12,z5,z6])],[(0,[z25,z3,z4,z12,z15,z6]),(0,[z2,z3,z12,z5,z6,z1028]),(0,[z3,z4,z12,z5,z6,z1029])],[(0,[z2,z1030,z3,z12,z5,z6]),(0,[z2,z9,z3,z5,z6,z375])],[(0,[z20,z3,z116,z12,z5,z6]),(0,[z2,z3,z882,z12,z5,z6]),(0,[z2,z3,z1031,z12,z5,z6]),(0,[z2,z3,z4,z1032,z5,z6])],[(0,[z2,z3,z12,z704,z23,z6]),(0,[z396,z3,z4,z16,z5,z6]),(0,[z2,z1033,z3,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1034,z6]),(0,[z1,z2,z1035,z4,z5,z6]),(0,[z2,z10,z3,z12,z5,z419]),(0,[z2,z3,z4,z1036,z5,z6]),(0,[z2,z3,z4,z5,z6,z1037])],[(0,[z3,z953,z4,z12,z5,z6]),(0,[z567,z2,z3,z212,z5,z6]),(0,[z2,z1038,z12,z5,z23,z6]),(0,[z2,z937,z4,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z1039]),(0,[z1,z3,z4,z554,z5,z6]),(0,[z2,z3,z4,z5,z6,z1040]),(0,[z2,z3,z320,z12,z5,z436])],[(0,[z2,z3,z1041,z12,z5,z6]),(0,[z2,z1042,z3,z12,z5,z6])],[(0,[z2,z3,z34,z5,z6,z375]),(0,[z2,z9,z3,z12,z5,z278]),(0,[z2,z55,z3,z219,z5,z6])],[(0,[z2,z9,z680,z12,z5,z6]),(0,[z674,z3,z4,z12,z5,z61]),(0,[z1043,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z50,z803,z6])],[(0,[z1,z3,z5,z198,z23,z6]),(0,[z1044,z2,z3,z4,z5,z6]),(0,[z43,z3,z113,z12,z44,z6]),(0,[z2,z4,z5,z42,z6,z369]),(0,[z396,z3,z4,z5,z17,z6])],[(0,[z2,z3,z12,z5,z74,z6]),(0,[z396,z3,z4,z5,z149,z6])],[(0,[z370,z2,z3,z105,z5,z6]),(0,[z1045,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z515,z42,z6]),(0,[z2,z10,z3,z551,z5,z6]),(0,[z3,z12,z5,z23,z6,z1046])],[(0,[z8,z2,z3,z5,z6,z204]),(0,[z2,z108,z3,z12,z288,z6]),(0,[z2,z10,z3,z132,z5,z6]),(0,[z197,z3,z4,z5,z6,z56])]],
   [[(0,[z724,z2,z3,z4,z5,z6]),(0,[z396,z3,z4,z5,z6,z29])],[(1,[z2,z9,z12,z5,z436]),(0,[z2,z3,z12,z5,z1047,z6]),(0,[z2,z3,z34,z12,z5,z278]),(0,[z1048,z396,z3,z4,z5,z6]),(0,[z2,z362,z4,z16,z5,z6])],[(0,[z2,z9,z3,z1049,z5,z6]),(0,[z2,z3,z12,z5,z1050,z6]),(0,[z2,z3,z12,z5,z6,z741]),(0,[z1051,z2,z86,z12,z5,z6])],[(0,[z2,z1052,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z61,z102]),(0,[z2,z1053,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z1054,z6])],[(0,[z2,z3,z4,z5,z1055,z6])],[(0,[z57,z208,z58,z4,z5,z6]),(0,[z2,z3,z4,z1056,z5,z6]),(0,[z396,z3,z4,z5,z1057,z6]),(0,[z2,z3,z16,z869,z5,z6]),(0,[z2,z3,z12,z5,z6,z1058])],[(0,[z2,z1059,z3,z12,z5,z6])],[(0,[z2,z487,z10,z3,z5,z6]),(0,[z316,z2,z3,z4,z5,z173])],[(0,[z2,z3,z1060,z12,z5,z6]),(0,[z2,z1061,z3,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1062,z6]),(0,[z249,z3,z4,z12,z5,z6]),(0,[z336,z249,z3,z4,z5,z6]),(0,[z2,z109,z4,z12,z665,z6]),(0,[z2,z3,z5,z24,z23,z6]),(0,[z396,z97,z3,z4,z5,z6]),(0,[z2,z3,z12,z902,z23,z6])],[(0,[z2,z3,z289,z5,z42,z6])],[(0,[z2,z12,z119,z5,z1063,z6]),(0,[z269,z3,z4,z12,z5,z278]),(0,[z2,z1064,z3,z12,z5,z6]),(0,[z1065,z2,z3,z4,z5,z6])],[(0,[z254,z3,z4,z12,z5,z6]),(0,[z2,z3,z113,z12,z5,z6]),(0,[z513,z4,z11,z12,z5,z6]),(0,[z2,z3,z1066,z12,z5,z6]),(0,[z247,z2,z12,z5,z204,z29]),(0,[z2,z3,z4,z42,z6,z94]),(0,[z2,z3,z16,z5,z6,z881]),(0,[z130,z2,z3,z4,z132,z102])],[(0,[z2,z802,z3,z34,z5,z6])],[(0,[z8,z2,z136,z3,z5,z6]),(0,[z3,z4,z12,z5,z14,z966]),(0,[z2,z3,z4,z5,z1067,z6]),(0,[z2,z1068,z3,z5,z42,z6])],[(0,[z13,z3,z4,z260,z5,z6]),(0,[z2,z3,z12,z1069,z5,z6]),(0,[z2,z4,z16,z5,z6,z369])],[(0,[z2,z10,z595,z12,z5,z6]),(0,[z0,z13,z3,z4,z5,z6]),(0,[z2,z1070,z4,z12,z5,z6]),(0,[z1071,z2,z86,z12,z5,z6])],[(0,[z336,z3,z4,z11,z5,z6]),(0,[z2,z405,z12,z5,z23,z6]),(0,[z2,z93,z3,z291,z5,z6]),(0,[z2,z34,z12,z106,z23,z6])],[(0,[z2,z3,z4,z194,z42,z6]),(0,[z2,z362,z4,z132,z5,z6])],[(0,[z2,z267,z3,z12,z5,z6]),(0,[z1072,z396,z3,z4,z5,z6])],[(0,[z2,z3,z12,z189,z6,z102]),(0,[z785,z10,z3,z12,z5,z6])],[(0,[z2,z3,z4,z1073,z5,z6]),(0,[z1074,z202,z3,z4,z5,z6])],[],[(0,[z1075,z2,z3,z4,z5,z6]),(0,[z2,z3,z320,z547,z5,z6])],[(0,[z2,z3,z232,z5,z42,z6])],[(0,[z2,z3,z4,z5,z1076,z6]),(0,[z2,z9,z146,z12,z5,z6]),(0,[z2,z3,z1077,z12,z5,z6]),(0,[z2,z86,z1078,z12,z5,z6])],[(0,[z115,z3,z81,z16,z5,z6]),(0,[z2,z10,z265,z12,z5,z6]),(0,[z2,z1079,z4,z12,z5,z6]),(0,[z396,z10,z3,z12,z5,z6]),(0,[z2,z1080,z34,z12,z5,z6])],[(0,[z199,z68,z4,z428,z5,z6]),(0,[z2,z3,z4,z5,z1081,z6]),(0,[z2,z86,z10,z12,z5,z6])],[(0,[z2,z336,z3,z5,z23,z6]),(0,[z199,z134,z3,z4,z5,z6]),(0,[z100,z3,z12,z5,z23,z61]),(0,[z2,z9,z12,z5,z6,z79])],[(0,[z197,z9,z3,z12,z5,z6]),(0,[z247,z2,z10,z12,z5,z29])],[(0,[z2,z3,z4,z12,z5,z1082]),(0,[z3,z4,z5,z1083,z448,z6]),(0,[z2,z3,z4,z16,z42,z6])],[(0,[z57,z10,z58,z12,z5,z6])]],
   [[],[(0,[z115,z2,z494,z12,z5,z6]),(0,[z396,z70,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1084,z6]),(0,[z91,z2,z487,z3,z5,z92]),(0,[z719,z3,z4,z12,z5,z6])],[(0,[z1085,z2,z3,z4,z5,z6]),(0,[z396,z3,z4,z5,z6,z92])],[(0,[z20,z2,z86,z12,z5,z6]),(0,[z8,z269,z3,z4,z5,z6]),(0,[z3,z12,z5,z23,z6,z95])],[(0,[z1,z793,z3,z4,z5,z6]),(0,[z8,z3,z11,z5,z23,z6])],[(1,[z43,z3,z4,z354,z6]),(0,[z2,z3,z12,z5,z6,z971]),(0,[z2,z3,z4,z1086,z5,z6])],[(0,[z2,z109,z4,z119,z42,z6]),(0,[z2,z3,z4,z183,z5,z6])],[(0,[z2,z3,z358,z5,z23,z6]),(0,[z43,z3,z4,z12,z44,z6]),(0,[z430,z2,z4,z12,z69,z6])],[(0,[z2,z3,z12,z1087,z5,z6]),(0,[z63,z2,z3,z4,z354,z6]),(0,[z2,z1088,z3,z4,z5,z6]),(0,[z2,z3,z144,z12,z23,z6]),(0,[z179,z2,z86,z12,z5,z6]),(0,[z2,z86,z12,z5,z21,z6])],[(0,[z199,z1,z10,z3,z5,z6]),(0,[z2,z3,z4,z5,z1089,z6]),(0,[z2,z3,z12,z5,z1090,z6])],[(0,[z1,z13,z3,z5,z23,z6]),(0,[z2,z3,z4,z16,z72,z6]),(0,[z2,z980,z4,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z812]),(0,[z2,z3,z139,z5,z23,z6])],[(0,[z2,z9,z3,z5,z354,z6]),(0,[z1,z2,z3,z5,z6,z204]),(0,[z134,z13,z3,z4,z5,z6])],[(0,[z57,z1,z58,z4,z5,z6]),(0,[z2,z405,z4,z16,z5,z6]),(0,[z305,z2,z9,z12,z5,z6]),(0,[z2,z1091,z3,z4,z5,z6])],[(0,[z1,z25,z3,z4,z15,z6]),(0,[z28,z2,z4,z12,z69,z6])],[],[(0,[z1092,z2,z3,z4,z5,z6]),(0,[z2,z9,z139,z119,z5,z6]),(0,[z2,z86,z289,z12,z5,z6])],[(0,[z2,z336,z3,z34,z5,z6]),(0,[z2,z108,z12,z5,z106,z6])],[(0,[z8,z2,z494,z4,z5,z6]),(0,[z10,z811,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z1093,z6]),(0,[z254,z3,z4,z12,z5,z278]),(0,[z2,z362,z4,z12,z5,z102])],[(0,[z2,z3,z34,z5,z354,z6]),(0,[z1,z452,z3,z4,z5,z6]),(0,[z8,z2,z3,z992,z5,z6]),(0,[z2,z1094,z3,z4,z5,z6])],[(0,[z2,z3,z4,z995,z5,z6]),(0,[z2,z97,z34,z78,z5,z6]),(0,[z162,z3,z4,z571,z5,z6])],[(0,[z2,z513,z4,z12,z5,z419]),(0,[z2,z1095,z12,z5,z45,z6]),(0,[z2,z3,z1096,z4,z5,z6]),(0,[z2,z3,z12,z5,z1097,z6])],[(0,[z2,z9,z3,z5,z6,z1098]),(0,[z396,z2,z10,z3,z5,z6]),(0,[z2,z3,z1099,z12,z5,z6]),(0,[z2,z86,z35,z12,z5,z6])],[],[(0,[z2,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z1100,z6]),(0,[z2,z1101,z3,z12,z5,z6]),(0,[z100,z3,z4,z16,z5,z61]),(0,[z2,z1102,z3,z12,z5,z6]),(0,[z2,z3,z4,z1103,z5,z6])],[(0,[z611,z2,z9,z12,z5,z6]),(0,[z2,z3,z1104,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z1105])],[(0,[z2,z9,z164,z12,z5,z6]),(0,[z1,z2,z10,z3,z5,z6]),(0,[z2,z3,z12,z5,z1106,z6]),(0,[z2,z3,z4,z5,z17,z854])],[(0,[z1,z2,z136,z3,z5,z6]),(0,[z2,z3,z131,z5,z42,z6]),(0,[z202,z246,z4,z12,z5,z6])],[(0,[z2,z3,z1107,z4,z5,z6])],[(0,[z2,z3,z358,z34,z5,z6]),(0,[z2,z9,z3,z5,z464,z6])],[(0,[z199,z396,z3,z4,z5,z6]),(0,[z1,z2,z9,z384,z5,z6]),(0,[z1,z10,z3,z170,z5,z6]),(0,[z28,z2,z3,z12,z213,z6]),(0,[z2,z1108,z4,z12,z5,z6])],[(0,[z1109,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1110]),(0,[z63,z2,z10,z3,z42,z6]),(0,[z2,z86,z12,z5,z241,z6])]],
   [[(0,[z1,z13,z3,z34,z5,z6]),(0,[z179,z2,z3,z4,z5,z437])],[(0,[z2,z3,z4,z12,z5,z1111]),(0,[z2,z3,z4,z1112,z5,z6]),(0,[z2,z10,z3,z5,z6,z176]),(0,[z2,z9,z12,z5,z29,z102]),(0,[z1113,z2,z3,z4,z5,z6])],[(0,[z2,z9,z68,z16,z5,z6]),(0,[z2,z3,z1114,z12,z5,z6]),(0,[z2,z1115,z3,z4,z5,z6]),(1,[z2,z86,z16,z5,z6])],[(0,[z8,z2,z3,z5,z6,z323]),(0,[z2,z3,z12,z5,z1116,z6])],[(0,[z2,z3,z581,z16,z5,z6]),(0,[z2,z9,z3,z358,z5,z6]),(0,[z1,z3,z4,z521,z5,z6]),(0,[z2,z3,z4,z236,z5,z419]),(0,[z1117,z2,z3,z12,z5,z6]),(0,[z2,z9,z184,z12,z5,z6]),(0,[z2,z3,z34,z5,z464,z6]),(0,[z396,z3,z4,z5,z281,z6]),(0,[z2,z3,z5,z74,z42,z6]),(0,[z2,z3,z1118,z12,z5,z6])],[(0,[z2,z3,z12,z5,z6,z1119])],[(0,[z2,z1120,z4,z12,z5,z6]),(0,[z1121,z3,z4,z12,z5,z6]),(0,[z2,z86,z12,z5,z6,z1122]),(0,[z162,z3,z4,z5,z42,z6]),(0,[z396,z3,z4,z5,z6,z56]),(0,[z2,z3,z4,z5,z6,z1123])],[(0,[z1,z3,z5,z6,z323,z61]),(0,[z2,z1124,z3,z12,z5,z6])],[(0,[z416,z1,z3,z4,z5,z6]),(0,[z2,z3,z1125,z12,z5,z6])],[(0,[z2,z59,z3,z5,z42,z6]),(0,[z1,z2,z3,z1041,z5,z6]),(0,[z91,z1,z2,z3,z5,z92]),(0,[z130,z2,z10,z3,z12,z102])],[(0,[z68,z810,z4,z12,z5,z6]),(0,[z2,z3,z5,z23,z6,z176]),(0,[z2,z3,z547,z5,z23,z6]),(0,[z2,z1126,z3,z4,z5,z6]),(0,[z3,z34,z12,z5,z6,z95]),(0,[z2,z3,z4,z528,z42,z6])],[(0,[z25,z9,z58,z12,z5,z6]),(0,[z396,z9,z3,z5,z42,z6]),(0,[z2,z3,z12,z5,z6,z1127])],[(0,[z2,z3,z4,z12,z5,z1128]),(0,[z1129,z2,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z1130,z6])],[(0,[z13,z3,z4,z5,z354,z6]),(0,[z2,z97,z4,z1131,z5,z6]),(0,[z2,z3,z4,z16,z167,z6])],[(0,[z2,z3,z4,z5,z6,z1132]),(0,[z2,z1133,z3,z12,z5,z6])],[(0,[z2,z9,z12,z5,z6,z201]),(0,[z2,z3,z1134,z12,z5,z6]),(0,[z2,z3,z34,z141,z5,z17]),(0,[z2,z3,z4,z12,z39,z763])],[(0,[z2,z10,z3,z222,z5,z6]),(0,[z2,z3,z1135,z12,z5,z6]),(0,[z2,z3,z4,z1136,z5,z6]),(0,[z2,z35,z3,z291,z5,z6]),(0,[z22,z2,z86,z12,z5,z6])],[(0,[z2,z3,z4,z1137,z5,z6]),(0,[z1,z269,z3,z4,z5,z6]),(0,[z1138,z3,z4,z12,z5,z6]),(0,[z2,z4,z12,z5,z6,z1139])],[(0,[z2,z363,z3,z12,z5,z6]),(0,[z2,z1140,z4,z12,z5,z6]),(0,[z2,z3,z4,z260,z5,z6]),(0,[z1141,z3,z4,z12,z5,z6]),(0,[z396,z3,z34,z5,z42,z6])],[(0,[z2,z3,z5,z213,z42,z6]),(0,[z2,z10,z3,z5,z6,z421]),(0,[z2,z3,z12,z1142,z5,z6]),(0,[z2,z3,z12,z5,z6,z1143])],[(0,[z520,z1,z10,z3,z5,z6]),(0,[z118,z3,z4,z12,z5,z61]),(0,[z202,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z1026,z6]),(0,[z2,z10,z3,z850,z5,z6]),(0,[z28,z2,z4,z12,z69,z278]),(0,[z787,z3,z4,z12,z5,z6])],[],[],[(0,[z2,z3,z4,z1144,z5,z6]),(0,[z2,z3,z4,z5,z6,z375]),(0,[z2,z12,z5,z6,z204,z369])],[],[(0,[z2,z9,z820,z12,z5,z6]),(0,[z25,z3,z4,z12,z5,z585]),(0,[z2,z9,z217,z12,z5,z6]),(0,[z2,z3,z16,z50,z23,z6])],[(0,[z2,z3,z4,z1145,z5,z6]),(0,[z396,z3,z4,z50,z5,z6])],[(0,[z441,z70,z4,z7,z5,z6]),(0,[z202,z3,z34,z12,z5,z6]),(0,[z2,z3,z1146,z12,z5,z6])],[(0,[z2,z3,z34,z12,z500,z6]),(0,[z2,z3,z5,z23,z6,z421])],[(0,[z2,z3,z1147,z12,z5,z6]),(0,[z100,z10,z3,z12,z5,z61])],[(0,[z2,z3,z4,z5,z1148,z6]),(0,[z2,z3,z4,z1149,z5,z6]),(0,[z2,z1150,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z278])],[(0,[z43,z1,z3,z232,z5,z6]),(0,[z1,z2,z494,z4,z5,z6])]],
   [[(0,[z2,z3,z251,z12,z23,z6]),(0,[z8,z3,z4,z918,z5,z6]),(0,[z2,z3,z205,z139,z5,z6])],[(0,[z2,z97,z384,z4,z5,z6]),(0,[z8,z2,z3,z5,z6,z491]),(0,[z2,z3,z34,z1151,z5,z6]),(0,[z1152,z202,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z106,z6]),(0,[z2,z9,z3,z12,z5,z1153])],[],[],[(0,[z8,z2,z405,z4,z5,z6]),(0,[z1,z2,z3,z1154,z5,z6])],[(0,[z474,z2,z3,z12,z23,z6]),(0,[z2,z3,z4,z1049,z5,z6]),(0,[z2,z3,z12,z5,z1155,z6]),(0,[z2,z3,z5,z604,z448,z6]),(0,[z2,z1156,z3,z12,z5,z6])],[(0,[z8,z2,z3,z99,z5,z6]),(0,[z2,z3,z12,z5,z6,z1157])],[(0,[z2,z3,z12,z263,z23,z6]),(0,[z2,z9,z3,z12,z5,z436]),(0,[z1158,z2,z3,z4,z5,z42]),(0,[z197,z3,z4,z5,z42,z6]),(0,[z2,z1159,z3,z4,z5,z6])],[(0,[z2,z10,z405,z12,z5,z6]),(0,[z8,z2,z109,z4,z119,z6]),(0,[z396,z3,z4,z11,z5,z6]),(0,[z2,z487,z3,z5,z23,z6])],[(0,[z2,z1160,z3,z12,z5,z6])],[(0,[z100,z1,z3,z4,z5,z61]),(0,[z2,z3,z1161,z12,z5,z6]),(0,[z1162,z269,z3,z4,z5,z6])],[(0,[z63,z2,z86,z12,z5,z6]),(0,[z2,z3,z4,z1163,z5,z6]),(0,[z396,z3,z4,z5,z654,z6])],[(0,[z2,z9,z68,z428,z5,z6]),(0,[z773,z3,z4,z12,z5,z6])],[(0,[z237,z1,z3,z4,z5,z6]),(0,[z2,z328,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z1164,z6])],[(0,[z1165,z10,z3,z12,z5,z6]),(0,[z2,z3,z34,z12,z5,z436]),(0,[z1166,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z5,z6,z323]),(0,[z1167,z2,z3,z4,z5,z6]),(0,[z2,z3,z1168,z12,z5,z6]),(0,[z2,z1095,z12,z15,z5,z6]),(0,[z2,z3,z12,z5,z6,z1169]),(0,[z2,z3,z152,z5,z348,z6])],[(0,[z130,z8,z2,z3,z4,z102]),(0,[z620,z2,z3,z12,z189,z6]),(0,[z2,z3,z16,z5,z114,z6]),(0,[z2,z923,z3,z5,z23,z6])],[(0,[z2,z86,z12,z119,z5,z6])],[(0,[z2,z59,z336,z3,z5,z6]),(0,[z2,z10,z362,z12,z5,z6]),(0,[z3,z4,z12,z5,z6,z1046])],[(0,[z100,z90,z3,z12,z5,z61]),(0,[z2,z540,z3,z16,z5,z6]),(0,[z1170,z2,z3,z4,z5,z6])],[(0,[z315,z2,z3,z4,z5,z6]),(0,[z2,z1171,z10,z3,z5,z6])],[(0,[z25,z2,z3,z4,z24,z6]),(0,[z2,z3,z394,z123,z5,z6]),(0,[z2,z3,z1172,z12,z5,z6]),(1,[z2,z3,z4,z5,z854])],[(0,[z2,z163,z151,z12,z5,z6]),(0,[z28,z2,z86,z12,z5,z6]),(0,[z520,z163,z3,z12,z5,z6]),(0,[z2,z1080,z4,z12,z5,z6])],[(0,[z8,z2,z3,z4,z5,z890])],[(0,[z2,z265,z34,z12,z5,z6]),(0,[z269,z3,z4,z12,z5,z436])],[(0,[z2,z3,z4,z1173,z5,z6]),(0,[z8,z2,z3,z5,z1174,z6]),(0,[z2,z3,z12,z5,z1175,z6])],[(0,[z1,z2,z3,z1176,z5,z6]),(0,[z2,z9,z3,z5,z819,z6])],[(0,[z8,z3,z4,z5,z6,z95]),(1,[z2,z4,z1131,z5,z6])],[(0,[z2,z3,z1177,z12,z5,z6]),(0,[z2,z1095,z4,z12,z5,z6]),(0,[z2,z3,z1178,z12,z5,z6]),(0,[z2,z3,z1179,z12,z5,z6]),(0,[z28,z254,z4,z12,z69,z6])],[(0,[z115,z405,z81,z12,z5,z6]),(0,[z2,z487,z3,z34,z5,z6]),(0,[z130,z2,z3,z4,z571,z102])],[(0,[z1,z372,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z1180,z6]),(0,[z2,z3,z5,z23,z33,z6]),(0,[z396,z3,z4,z19,z5,z6]),(0,[z441,z3,z4,z5,z42,z6]),(0,[z2,z3,z1181,z12,z5,z6])]],
   [[(0,[z3,z4,z11,z12,z5,z585]),(0,[z3,z4,z12,z5,z6,z966]),(0,[z2,z9,z979,z3,z5,z6]),(0,[z2,z10,z3,z12,z5,z900])],[],[(1,[z3,z4,z918,z5,z6])],[],[(0,[z8,z2,z3,z52,z5,z21])],[(0,[z8,z2,z9,z3,z5,z6]),(0,[z2,z9,z574,z12,z5,z6]),(0,[z2,z3,z5,z42,z6,z1182])],[(0,[z199,z1,z3,z607,z5,z6]),(0,[z8,z1,z10,z3,z5,z6]),(0,[z430,z2,z9,z12,z5,z6]),(0,[z2,z3,z5,z6,z473,z204])],[(0,[z2,z3,z4,z650,z42,z6]),(0,[z2,z9,z3,z547,z5,z6]),(0,[z2,z3,z12,z5,z6,z1183])],[],[(0,[z451,z2,z9,z3,z5,z6])],[(0,[z2,z1035,z4,z12,z5,z6]),(0,[z3,z4,z5,z159,z33,z6]),(0,[z28,z2,z10,z12,z69,z6]),(0,[z2,z3,z345,z12,z5,z6]),(0,[z130,z2,z3,z4,z42,z102])],[(0,[z690,z1,z3,z4,z5,z6]),(0,[z28,z2,z136,z12,z69,z6]),(0,[z2,z552,z4,z5,z224,z6])],[(0,[z199,z1,z3,z5,z23,z6]),(0,[z2,z3,z12,z5,z6,z1184]),(0,[z2,z3,z12,z5,z21,z778])],[(0,[z1,z3,z4,z918,z5,z6]),(0,[z2,z55,z3,z444,z5,z6]),(0,[z2,z3,z139,z5,z604,z6]),(0,[z2,z86,z12,z5,z23,z6]),(0,[z202,z3,z4,z571,z5,z6])],[(0,[z1,z2,z3,z5,z6,z491]),(0,[z2,z3,z34,z5,z6,z473])],[(0,[z2,z3,z418,z291,z5,z6]),(0,[z1185,z2,z3,z4,z5,z6]),(0,[z247,z2,z12,z5,z23,z29]),(0,[z2,z1186,z3,z12,z5,z6]),(0,[z63,z2,z3,z23,z42,z6])],[(0,[z9,z58,z12,z5,z44,z6]),(0,[z2,z3,z4,z5,z354,z6]),(0,[z2,z3,z12,z5,z6,z1187])],[(0,[z0,z3,z58,z4,z5,z6]),(0,[z2,z3,z4,z5,z1188,z6]),(0,[z2,z1189,z3,z12,z5,z6]),(0,[z2,z97,z4,z78,z5,z6])],[(0,[z1,z2,z405,z4,z5,z6]),(0,[z8,z2,z3,z4,z5,z585])],[(0,[z2,z151,z34,z12,z5,z6]),(0,[z1,z3,z4,z5,z6,z585]),(1,[z3,z4,z12,z5,z966]),(0,[z100,z2,z86,z12,z5,z6])],[(0,[z1,z2,z3,z99,z5,z6]),(0,[z160,z2,z3,z12,z5,z318]),(0,[z179,z441,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1190])],[(0,[z247,z2,z9,z12,z5,z29]),(0,[z2,z109,z34,z12,z119,z6]),(0,[z1074,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z12,z763])],[(0,[z1,z3,z4,z5,z6,z140]),(0,[z1,z2,z109,z4,z119,z6]),(0,[z2,z3,z12,z5,z6,z204]),(0,[z2,z10,z3,z571,z5,z6]),(0,[z396,z101,z3,z4,z5,z6])],[],[(0,[z2,z68,z12,z5,z189,z6]),(0,[z2,z3,z53,z16,z5,z6]),(0,[z396,z2,z3,z5,z23,z6])],[(0,[z2,z3,z12,z340,z23,z6])],[(0,[z2,z9,z3,z211,z5,z6]),(0,[z2,z1191,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1098]),(0,[z2,z3,z4,z1192,z5,z6]),(0,[z2,z770,z4,z5,z42,z6])],[(0,[z2,z3,z4,z12,z5,z1193]),(0,[z1,z3,z4,z5,z198,z6]),(0,[z2,z86,z1194,z12,z5,z6]),(0,[z2,z3,z4,z5,z1195,z6])],[(0,[z2,z3,z16,z5,z45,z6]),(0,[z2,z3,z4,z12,z545,z39])],[(0,[z8,z2,z3,z983,z5,z6])],[(0,[z2,z1196,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z1197,z6])],[(0,[z301,z2,z3,z4,z5,z143]),(0,[z2,z9,z97,z78,z5,z6]),(0,[z1198,z2,z3,z4,z5,z6]),(0,[z1199,z2,z3,z4,z5,z6]),(0,[z202,z3,z4,z5,z42,z6])]],
   [[(0,[z3,z4,z260,z5,z6,z61]),(0,[z254,z3,z4,z12,z5,z436])],[(0,[z199,z1,z3,z34,z5,z6]),(0,[z3,z953,z116,z12,z5,z6]),(0,[z2,z3,z34,z211,z5,z6]),(0,[z2,z3,z535,z5,z45,z6]),(0,[z367,z2,z9,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1200,z6]),(0,[z2,z1201,z3,z12,z5,z6]),(0,[z2,z494,z4,z5,z42,z6])],[(0,[z523,z3,z116,z12,z5,z6]),(0,[z2,z3,z4,z675,z42,z6]),(0,[z8,z3,z4,z5,z255,z6]),(0,[z2,z109,z4,z139,z119,z6])],[(0,[z2,z157,z12,z5,z189,z6]),(0,[z2,z3,z152,z5,z609,z6]),(0,[z2,z3,z4,z1202,z5,z6])],[],[(0,[z2,z3,z781,z5,z42,z6])],[(0,[z43,z3,z232,z12,z44,z6]),(0,[z121,z271,z3,z12,z5,z6])],[(0,[z2,z1203,z3,z4,z5,z6]),(0,[z199,z261,z4,z12,z5,z6]),(0,[z8,z454,z3,z4,z5,z6]),(0,[z2,z10,z3,z5,z42,z6]),(0,[z91,z2,z3,z12,z5,z262])],[(0,[z2,z3,z4,z1204,z5,z6]),(0,[z1,z3,z4,z5,z6,z95]),(0,[z2,z1205,z3,z12,z5,z6]),(0,[z130,z2,z86,z12,z5,z6]),(0,[z2,z86,z4,z16,z5,z6]),(0,[z2,z3,z12,z5,z6,z778]),(0,[z2,z3,z16,z5,z74,z6]),(0,[z2,z362,z4,z571,z5,z6])],[(0,[z2,z1206,z3,z12,z5,z6])],[],[(0,[z1,z3,z58,z5,z23,z6]),(0,[z2,z3,z4,z141,z5,z17])],[(0,[z134,z3,z58,z4,z5,z6]),(0,[z242,z58,z4,z12,z5,z6]),(0,[z1,z9,z462,z3,z5,z6]),(0,[z2,z3,z12,z5,z6,z1207]),(0,[z2,z3,z1208,z12,z5,z6]),(0,[z396,z2,z3,z34,z5,z6])],[(0,[z2,z9,z12,z5,z6,z357]),(0,[z8,z2,z3,z230,z5,z6]),(0,[z8,z2,z3,z234,z5,z6]),(0,[z2,z3,z1209,z12,z5,z6])],[(0,[z2,z3,z4,z1210,z5,z6]),(0,[z2,z3,z1211,z12,z5,z6]),(0,[z2,z3,z205,z12,z5,z6]),(0,[z396,z3,z4,z5,z42,z6])],[(0,[z8,z556,z3,z4,z5,z6])],[(0,[z1,z2,z3,z52,z5,z21]),(0,[z286,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z49,z5,z404])],[(0,[z1,z2,z9,z3,z5,z6]),(0,[z8,z2,z3,z4,z65,z39]),(0,[z2,z107,z85,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z1212])],[(0,[z269,z3,z12,z5,z23,z6]),(0,[z2,z1213,z3,z12,z5,z6])],[(0,[z2,z9,z253,z12,z5,z6]),(0,[z2,z9,z10,z12,z5,z6])],[(0,[z2,z3,z4,z5,z1214,z6]),(0,[z2,z3,z4,z915,z5,z6]),(0,[z2,z1017,z12,z5,z23,z6])],[(0,[z2,z3,z4,z5,z6,z1215]),(0,[z290,z2,z3,z12,z5,z92]),(0,[z63,z2,z3,z34,z42,z6])],[(0,[z2,z9,z109,z12,z119,z6]),(0,[z63,z2,z9,z3,z42,z6]),(0,[z2,z4,z12,z5,z6,z862]),(0,[z1216,z3,z34,z12,z5,z6]),(0,[z2,z3,z52,z16,z5,z21])],[(0,[z2,z3,z4,z5,z6,z1217])],[(0,[z8,z2,z3,z4,z5,z955]),(0,[z2,z55,z3,z37,z5,z6]),(0,[z26,z2,z12,z106,z23,z6]),(0,[z2,z3,z12,z23,z6,z420]),(0,[z2,z1218,z3,z4,z5,z6])],[(0,[z1000,z3,z12,z5,z23,z6])],[(0,[z2,z9,z669,z12,z5,z6]),(0,[z2,z10,z12,z5,z546,z6]),(0,[z2,z97,z564,z78,z5,z6]),(0,[z2,z362,z4,z5,z42,z6])],[(0,[z2,z3,z12,z5,z6,z1219]),(0,[z2,z9,z3,z5,z532,z6]),(0,[z2,z86,z157,z12,z5,z6]),(0,[z3,z4,z5,z159,z42,z6])],[(0,[z2,z9,z656,z12,z5,z6]),(0,[z2,z9,z19,z12,z5,z6])],[(0,[z2,z3,z4,z1151,z5,z6]),(0,[z2,z9,z552,z12,z5,z6]),(0,[z2,z3,z422,z16,z5,z6]),(0,[z2,z3,z1220,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z585]),(0,[z2,z86,z12,z5,z17,z6])]],
   [[(0,[z13,z3,z4,z5,z14,z176]),(0,[z2,z3,z4,z1221,z5,z6]),(0,[z2,z157,z53,z12,z5,z6]),(0,[z130,z2,z3,z34,z12,z102])],[(0,[z1,z3,z58,z34,z5,z6]),(0,[z1,z3,z4,z5,z6,z73]),(0,[z8,z2,z513,z4,z5,z6]),(0,[z2,z540,z12,z119,z5,z6]),(0,[z2,z3,z4,z12,z6,z763])],[(0,[z2,z3,z4,z5,z1222,z6]),(0,[z28,z2,z4,z12,z69,z436]),(0,[z2,z3,z1223,z12,z5,z6]),(0,[z2,z3,z4,z141,z5,z404])],[(0,[z8,z202,z3,z4,z5,z6]),(0,[z2,z3,z34,z5,z532,z6]),(0,[z2,z9,z191,z12,z5,z6]),(0,[z2,z10,z246,z12,z5,z6]),(0,[z2,z86,z12,z5,z6,z29]),(0,[z396,z396,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z42,z814])],[(0,[z2,z3,z4,z5,z1224,z6]),(0,[z2,z3,z1225,z4,z5,z6]),(0,[z2,z12,z5,z23,z1226,z6])],[(0,[z2,z3,z1227,z12,z5,z6]),(0,[z2,z9,z240,z12,z5,z6]),(0,[z8,z2,z3,z1168,z5,z6]),(0,[z2,z3,z4,z5,z17,z279]),(0,[z2,z3,z4,z186,z5,z419]),(0,[z2,z1228,z3,z12,z5,z6])],[(0,[z199,z68,z607,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1229]),(0,[z2,z3,z4,z12,z5,z1153]),(1,[z2,z3,z774,z5,z6]),(0,[z2,z3,z361,z5,z42,z6])],[(0,[z376,z1,z3,z4,z5,z6]),(0,[z90,z2,z3,z5,z42,z6]),(0,[z2,z1230,z3,z16,z5,z6])],[(0,[z2,z1231,z3,z12,z5,z6]),(0,[z1232,z396,z3,z4,z5,z6])],[(0,[z8,z57,z58,z4,z5,z6]),(0,[z2,z9,z289,z12,z5,z6]),(0,[z2,z3,z34,z12,z700,z6])],[(0,[z2,z3,z4,z5,z1233,z6])],[(0,[z9,z3,z5,z159,z42,z6]),(0,[z2,z10,z3,z5,z1234,z6])],[(0,[z3,z4,z11,z186,z5,z6]),(0,[z2,z127,z3,z444,z5,z6]),(0,[z2,z3,z4,z12,z5,z436]),(0,[z63,z396,z3,z4,z42,z6])],[(0,[z1,z3,z4,z5,z6,z248]),(0,[z2,z3,z34,z12,z5,z419]),(0,[z2,z980,z12,z5,z6,z323]),(0,[z2,z1235,z3,z12,z5,z6])],[(0,[z2,z3,z4,z1236,z5,z6]),(0,[z2,z3,z4,z5,z6,z1237]),(0,[z2,z86,z81,z12,z5,z6]),(0,[z43,z1,z10,z3,z5,z6]),(0,[z396,z3,z4,z5,z14,z6]),(0,[z396,z3,z4,z5,z39,z6])],[(0,[z2,z55,z3,z483,z5,z6]),(0,[z269,z3,z4,z16,z5,z6])],[(0,[z2,z3,z1238,z12,z5,z6])],[(0,[z2,z1239,z3,z12,z5,z6]),(0,[z1,z10,z271,z3,z5,z6]),(0,[z2,z3,z4,z1240,z5,z6]),(0,[z2,z3,z12,z5,z6,z1241])],[(0,[z2,z12,z5,z189,z6,z29])],[],[(0,[z115,z3,z81,z5,z42,z6]),(0,[z8,z2,z3,z205,z5,z6]),(0,[z2,z10,z3,z535,z5,z6]),(0,[z1242,z9,z3,z12,z5,z6])],[(0,[z396,z3,z4,z5,z6,z61]),(0,[z2,z70,z4,z5,z6,z538]),(0,[z2,z3,z34,z551,z5,z6])],[(0,[z2,z265,z4,z12,z5,z6]),(0,[z965,z2,z3,z4,z5,z6]),(0,[z2,z610,z3,z12,z5,z624]),(0,[z2,z10,z566,z12,z5,z6]),(0,[z179,z2,z267,z3,z5,z56])],[(0,[z249,z3,z12,z5,z23,z6])],[(0,[z2,z3,z4,z5,z6,z1243])],[(0,[z2,z3,z12,z5,z1244,z6]),(0,[z1,z3,z4,z5,z6,z61]),(0,[z8,z2,z929,z4,z5,z6])],[(0,[z2,z3,z12,z5,z6,z323]),(0,[z2,z3,z4,z1245,z5,z6]),(0,[z254,z3,z12,z5,z23,z6])],[(0,[z1,z2,z3,z230,z5,z6]),(0,[z1,z2,z3,z234,z5,z6])],[(0,[z2,z3,z12,z5,z1246,z6])],[(0,[z2,z3,z230,z5,z42,z6])],[(0,[z2,z3,z1247,z12,z5,z6]),(0,[z20,z3,z116,z16,z5,z6]),(1,[z2,z980,z12,z5,z6]),(0,[z2,z1070,z12,z5,z23,z6])],[(0,[z1,z2,z3,z4,z65,z39]),(0,[z269,z3,z4,z551,z5,z6]),(0,[z2,z86,z3,z5,z42,z6])]],
   [[(0,[z2,z3,z4,z12,z5,z1248]),(0,[z2,z3,z4,z1249,z5,z6]),(0,[z2,z9,z327,z12,z5,z6]),(0,[z63,z2,z3,z234,z42,z6])],[(0,[z8,z2,z107,z3,z5,z6]),(0,[z845,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z803,z42,z6]),(0,[z1152,z2,z3,z4,z5,z6])],[(0,[z2,z10,z3,z186,z5,z6]),(0,[z2,z3,z4,z671,z42,z6]),(0,[z1250,z2,z3,z12,z5,z6])],[(0,[z2,z3,z4,z1251,z5,z6])],[],[(0,[z1252,z2,z3,z4,z5,z6]),(0,[z8,z2,z3,z1135,z5,z6])],[],[(0,[z2,z513,z4,z5,z42,z6]),(0,[z25,z3,z4,z12,z626,z6])],[(0,[z2,z3,z4,z1253,z5,z6]),(0,[z2,z1254,z3,z4,z5,z6]),(0,[z8,z1,z3,z5,z23,z6]),(0,[z2,z9,z3,z476,z5,z6]),(0,[z2,z3,z4,z5,z6,z1255])],[(0,[z8,z2,z77,z3,z5,z6]),(0,[z396,z3,z4,z186,z5,z6])],[(0,[z2,z9,z12,z5,z39,z29]),(0,[z2,z1256,z3,z12,z5,z6]),(0,[z2,z3,z12,z1257,z5,z6]),(0,[z197,z3,z4,z141,z5,z6])],[(0,[z115,z3,z12,z5,z6,z427]),(0,[z2,z3,z4,z1258,z5,z6]),(0,[z2,z3,z4,z5,z6,z473])],[(0,[z199,z68,z34,z12,z5,z6]),(0,[z2,z3,z4,z1259,z5,z6]),(0,[z43,z1,z3,z4,z15,z6]),(0,[z2,z3,z1260,z12,z5,z6]),(0,[z852,z3,z4,z5,z42,z6]),(0,[z2,z3,z1261,z12,z5,z6])],[(0,[z2,z97,z10,z78,z5,z6]),(0,[z28,z2,z12,z69,z23,z6]),(0,[z63,z2,z3,z4,z803,z6]),(0,[z3,z4,z12,z5,z6,z990])],[(0,[z315,z1,z3,z4,z5,z6]),(0,[z1,z2,z513,z4,z5,z6]),(0,[z2,z3,z4,z5,z1262,z6]),(0,[z8,z2,z3,z1263,z5,z6]),(0,[z2,z10,z85,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z1264])],[(0,[z2,z3,z4,z970,z5,z6]),(0,[z2,z3,z4,z1265,z5,z6]),(0,[z2,z3,z34,z476,z5,z6])],[(0,[z2,z151,z4,z12,z5,z6]),(0,[z1,z202,z3,z4,z5,z6]),(0,[z2,z254,z9,z12,z5,z6]),(0,[z2,z3,z12,z213,z23,z6]),(0,[z2,z3,z1266,z12,z5,z6])],[(0,[z2,z3,z161,z12,z5,z6]),(0,[z2,z12,z5,z23,z6,z1267]),(0,[z2,z36,z3,z576,z5,z6])],[(0,[z2,z3,z4,z5,z1268,z6]),(0,[z2,z109,z4,z12,z119,z6])],[(0,[z3,z4,z5,z6,z877,z61]),(0,[z8,z2,z3,z320,z5,z6]),(0,[z249,z3,z4,z16,z5,z6]),(0,[z2,z540,z109,z12,z119,z6])],[(0,[z2,z3,z4,z5,z6,z1269]),(0,[z269,z10,z3,z12,z5,z6])],[],[(0,[z254,z3,z4,z16,z5,z6])],[(0,[z1,z482,z3,z4,z5,z6]),(0,[z8,z2,z837,z4,z5,z6]),(0,[z130,z2,z3,z4,z16,z102])],[(0,[z1,z13,z3,z4,z5,z143]),(0,[z3,z4,z15,z5,z1148,z6]),(0,[z2,z1270,z3,z12,z5,z6]),(0,[z90,z322,z2,z3,z5,z6]),(0,[z2,z10,z3,z139,z5,z6]),(0,[z2,z3,z12,z5,z6,z491])],[(0,[z2,z3,z331,z5,z23,z6]),(0,[z2,z1271,z34,z12,z5,z6])],[(0,[z8,z2,z1272,z4,z5,z6]),(0,[z2,z1070,z4,z16,z5,z6])],[(0,[z2,z1273,z3,z12,z5,z6])],[(0,[z2,z3,z358,z4,z5,z6]),(0,[z1,z2,z1274,z4,z5,z6]),(0,[z2,z180,z3,z12,z5,z460]),(0,[z315,z2,z10,z3,z5,z6])],[(0,[z8,z1,z3,z34,z5,z6]),(0,[z1275,z2,z3,z4,z5,z6]),(0,[z13,z3,z4,z12,z5,z572]),(0,[z396,z3,z4,z5,z218,z6]),(0,[z2,z267,z3,z16,z5,z6])],[(0,[z2,z3,z581,z5,z42,z6]),(0,[z2,z3,z4,z211,z5,z6]),(0,[z2,z3,z113,z12,z5,z419])],[(0,[z2,z3,z4,z12,z5,z1276]),(0,[z1,z3,z4,z210,z5,z6]),(0,[z2,z3,z892,z12,z5,z6]),(0,[z2,z9,z12,z463,z5,z6]),(0,[z130,z202,z3,z4,z12,z102])]],
   [[(0,[z2,z1277,z4,z12,z5,z6]),(0,[z2,z9,z3,z12,z65,z39]),(0,[z2,z3,z12,z5,z1278,z6])],[(0,[z1,z2,z3,z205,z5,z6]),(0,[z2,z9,z215,z12,z5,z6]),(0,[z2,z3,z1279,z12,z5,z6]),(0,[z1280,z3,z4,z16,z5,z6])],[(0,[z793,z3,z58,z4,z5,z6]),(0,[z2,z86,z68,z12,z5,z6]),(0,[z20,z396,z3,z4,z5,z6]),(0,[z28,z2,z9,z12,z69,z6])],[(0,[z20,z3,z953,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z1281]),(0,[z2,z3,z4,z1282,z5,z6]),(0,[z2,z3,z124,z5,z221,z6])],[(0,[z2,z3,z34,z12,z189,z6]),(0,[z2,z86,z86,z12,z5,z6]),(0,[z2,z267,z3,z5,z17,z6]),(0,[z2,z1283,z3,z12,z5,z6]),(0,[z2,z3,z12,z65,z74,z39])],[],[(0,[z1284,z2,z3,z4,z5,z6]),(0,[z751,z2,z3,z4,z5,z6]),(0,[z254,z3,z4,z551,z5,z6])],[(0,[z2,z3,z4,z5,z1285,z6]),(0,[z787,z3,z4,z5,z6,z473]),(0,[z2,z3,z291,z5,z613,z6])],[(0,[z8,z2,z59,z3,z5,z6]),(0,[z0,z2,z10,z3,z5,z6]),(0,[z1286,z2,z3,z12,z5,z6])],[(0,[z100,z3,z4,z5,z375,z61]),(0,[z2,z3,z4,z5,z1287,z6])],[(0,[z2,z3,z4,z12,z5,z1288]),(0,[z1,z3,z4,z5,z6,z238]),(0,[z2,z9,z271,z12,z5,z6]),(0,[z2,z857,z246,z12,z5,z6])],[(0,[z2,z820,z58,z12,z5,z6]),(0,[z2,z107,z3,z12,z5,z6]),(0,[z2,z9,z12,z5,z6,z478])],[(0,[z2,z1289,z3,z16,z5,z6])],[(0,[z2,z3,z289,z16,z5,z6]),(0,[z2,z3,z5,z23,z6,z1290]),(0,[z2,z3,z16,z50,z51,z6])],[(0,[z1,z2,z107,z3,z5,z6]),(0,[z2,z70,z7,z475,z5,z6])],[(0,[z2,z3,z1163,z5,z23,z6])],[(0,[z2,z3,z4,z12,z6,z1291]),(0,[z2,z1292,z3,z12,z5,z6]),(0,[z2,z3,z12,z1293,z5,z6])],[(0,[z2,z3,z12,z5,z1174,z6]),(0,[z2,z9,z3,z5,z6,z176])],[(0,[z43,z3,z4,z16,z44,z6]),(0,[z2,z1294,z3,z4,z5,z6])],[],[(0,[z199,z1,z3,z581,z5,z6]),(0,[z2,z3,z1295,z12,z5,z6]),(0,[z1216,z3,z4,z12,z5,z6])],[(0,[z451,z2,z3,z4,z515,z6])],[(0,[z1,z2,z77,z3,z5,z6]),(0,[z8,z2,z3,z5,z45,z6]),(0,[z2,z3,z4,z5,z6,z1296]),(0,[z2,z1297,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1298])],[(0,[z2,z9,z12,z5,z6,z492])],[(0,[z2,z3,z34,z5,z6,z176]),(0,[z28,z2,z4,z16,z69,z6]),(0,[z1299,z2,z3,z12,z5,z6])],[(0,[z2,z3,z4,z12,z879,z6])],[(0,[z3,z81,z953,z12,z5,z6]),(0,[z43,z3,z4,z12,z44,z419]),(0,[z2,z3,z12,z5,z1300,z6]),(0,[z2,z9,z297,z12,z5,z6]),(0,[z3,z4,z12,z5,z6,z1301])],[(0,[z8,z266,z3,z4,z5,z6]),(0,[z254,z10,z3,z12,z5,z6]),(0,[z2,z246,z34,z12,z5,z6])],[],[(0,[z2,z9,z58,z5,z42,z6]),(0,[z199,z2,z86,z12,z5,z6]),(0,[z2,z3,z152,z126,z5,z6]),(0,[z2,z86,z12,z50,z5,z6])],[(0,[z43,z1,z3,z4,z32,z6])],[(0,[z2,z336,z363,z3,z5,z6]),(0,[z2,z3,z1302,z12,z5,z6])]],
   [[(0,[z2,z9,z3,z222,z5,z6]),(0,[z20,z1,z3,z116,z5,z6]),(0,[z1,z2,z3,z320,z5,z6]),(0,[z2,z3,z4,z5,z532,z6]),(0,[z2,z10,z12,z5,z6,z369])],[(0,[z2,z3,z12,z697,z23,z6]),(0,[z2,z3,z320,z12,z5,z6]),(0,[z2,z55,z3,z214,z5,z6])],[(0,[z2,z1303,z3,z12,z5,z6]),(0,[z2,z3,z1304,z12,z5,z6])],[(0,[z2,z9,z3,z5,z6,z421]),(0,[z2,z10,z3,z16,z50,z6]),(0,[z2,z3,z1305,z12,z5,z6]),(0,[z396,z3,z4,z5,z21,z6])],[(0,[z1,z2,z3,z581,z5,z6]),(0,[z134,z2,z10,z3,z5,z6])],[],[(0,[z8,z2,z3,z422,z5,z6])],[(0,[z2,z3,z34,z222,z5,z6]),(0,[z2,z70,z7,z5,z23,z6]),(0,[z2,z3,z4,z5,z6,z1306])],[(0,[z28,z2,z4,z551,z69,z6])],[(0,[z2,z3,z4,z5,z1307,z6]),(0,[z1308,z2,z3,z4,z5,z6]),(0,[z1309,z2,z3,z4,z5,z6]),(0,[z1310,z396,z3,z4,z5,z6])],[(0,[z3,z4,z15,z5,z354,z6]),(0,[z8,z2,z3,z1311,z5,z6]),(0,[z2,z3,z4,z12,z5,z419]),(0,[z28,z269,z9,z12,z5,z6]),(0,[z2,z3,z5,z42,z6,z355]),(0,[z2,z3,z34,z5,z6,z421])],[(0,[z2,z3,z4,z5,z42,z585]),(0,[z2,z93,z3,z5,z281,z6])],[(0,[z2,z109,z3,z12,z189,z6])],[(0,[z2,z208,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z585]),(1,[z3,z4,z12,z720,z6]),(0,[z100,z9,z3,z12,z5,z61]),(0,[z2,z108,z3,z12,z213,z6]),(0,[z2,z10,z3,z16,z42,z6]),(0,[z2,z10,z12,z702,z5,z6])],[(0,[z57,z58,z4,z5,z42,z6])],[(0,[z315,z3,z4,z11,z5,z6]),(0,[z2,z86,z12,z5,z69,z6]),(0,[z2,z3,z152,z123,z5,z6])],[(0,[z2,z1312,z4,z12,z5,z6])],[(0,[z2,z1313,z4,z12,z5,z6])],[(0,[z2,z3,z4,z5,z1314,z6]),(0,[z2,z3,z4,z551,z5,z6]),(0,[z3,z4,z5,z42,z6,z95]),(0,[z2,z3,z1125,z16,z5,z6])],[(0,[z2,z3,z4,z12,z5,z975]),(0,[z2,z3,z4,z1315,z5,z6]),(0,[z2,z3,z1316,z12,z5,z6])],[(0,[z100,z3,z34,z12,z5,z61]),(0,[z2,z9,z522,z12,z5,z6]),(0,[z396,z3,z4,z16,z42,z6])],[(0,[z1,z2,z59,z3,z5,z6]),(0,[z115,z1,z3,z81,z5,z6]),(0,[z8,z2,z1196,z4,z5,z6]),(0,[z2,z10,z3,z1086,z5,z6]),(0,[z2,z3,z124,z5,z6,z41])],[(0,[z2,z171,z3,z12,z5,z6])],[(0,[z43,z10,z3,z12,z44,z6]),(0,[z2,z1317,z3,z12,z5,z6]),(0,[z2,z55,z494,z12,z5,z6])],[(0,[z1,z324,z3,z4,z5,z6]),(0,[z1242,z3,z4,z12,z5,z6])],[(0,[z396,z3,z4,z5,z241,z6]),(0,[z2,z4,z12,z5,z1226,z6])],[(0,[z2,z3,z4,z1318,z5,z6]),(0,[z153,z2,z3,z12,z213,z6])],[(0,[z2,z3,z4,z5,z1319,z6]),(0,[z2,z3,z12,z774,z5,z6])],[(0,[z2,z363,z3,z16,z5,z6]),(0,[z209,z2,z3,z12,z23,z6])],[(0,[z2,z9,z3,z1320,z5,z6])],[(0,[z115,z2,z86,z12,z5,z6]),(0,[z8,z2,z3,z5,z189,z6]),(0,[z2,z3,z1321,z12,z5,z6]),(0,[z2,z55,z3,z5,z281,z6])],[(0,[z2,z3,z4,z5,z1322,z6]),(0,[z28,z2,z9,z547,z5,z6]),(0,[z91,z2,z487,z3,z5,z6])]],
   [[(0,[z2,z3,z4,z1323,z5,z6]),(0,[z2,z3,z5,z354,z23,z6])],[(0,[z2,z108,z3,z5,z42,z6]),(0,[z2,z3,z361,z16,z50,z6]),(0,[z2,z1324,z3,z12,z5,z6])],[(0,[z396,z25,z3,z4,z5,z6]),(0,[z2,z3,z16,z5,z6,z204]),(0,[z290,z2,z3,z12,z5,z40])],[(0,[z8,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z45,z6]),(0,[z2,z293,z4,z78,z5,z6]),(1,[z396,z10,z3,z5,z6])],[(0,[z2,z3,z4,z354,z6,z102]),(0,[z2,z9,z3,z5,z24,z6]),(0,[z2,z1325,z86,z12,z5,z6])],[(0,[z43,z1,z3,z4,z44,z6]),(0,[z2,z9,z157,z12,z5,z302]),(0,[z3,z4,z16,z5,z6,z95]),(0,[z2,z3,z5,z74,z456,z6])],[(0,[z43,z1,z9,z3,z5,z6]),(0,[z2,z9,z3,z5,z33,z6])],[(0,[z2,z1326,z3,z12,z5,z6]),(0,[z179,z2,z3,z4,z5,z854]),(1,[z2,z916,z12,z5,z6])],[(0,[z20,z531,z3,z116,z5,z6]),(0,[z1,z598,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1327])],[(0,[z199,z68,z4,z12,z5,z6])],[(0,[z2,z1328,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z1329,z6])],[(0,[z2,z3,z34,z5,z24,z6]),(0,[z1330,z3,z4,z12,z5,z6])],[(0,[z156,z2,z4,z12,z69,z6]),(0,[z2,z59,z3,z16,z5,z6]),(0,[z8,z2,z3,z4,z5,z1111]),(0,[z2,z3,z4,z185,z42,z6]),(0,[z2,z3,z4,z476,z5,z6])],[(0,[z2,z3,z34,z5,z33,z6]),(0,[z3,z4,z5,z42,z1331,z6])],[(0,[z3,z58,z4,z5,z354,z6]),(0,[z416,z197,z3,z4,z5,z6])],[(0,[z197,z3,z12,z5,z23,z6])],[(0,[z3,z4,z11,z5,z6,z375])],[(0,[z2,z3,z1332,z12,z5,z6]),(0,[z2,z3,z5,z114,z42,z6])],[(0,[z2,z77,z3,z12,z5,z6])],[(0,[z43,z1,z3,z4,z5,z585]),(0,[z1,z2,z3,z422,z5,z6]),(0,[z2,z3,z1333,z12,z5,z6]),(0,[z43,z3,z4,z12,z720,z6]),(0,[z2,z4,z747,z12,z5,z6])],[(0,[z2,z70,z422,z7,z5,z6])],[(0,[z91,z2,z3,z12,z5,z496]),(0,[z2,z9,z3,z71,z5,z6]),(0,[z3,z4,z12,z5,z159,z6]),(0,[z2,z265,z232,z12,z5,z6]),(0,[z2,z9,z157,z12,z5,z6]),(0,[z130,z2,z3,z131,z12,z102])],[(0,[z2,z9,z12,z5,z6,z558]),(0,[z2,z1271,z4,z12,z5,z6])],[(0,[z2,z3,z12,z5,z6,z1334]),(0,[z2,z10,z3,z12,z5,z1335]),(0,[z2,z328,z3,z5,z23,z6]),(0,[z2,z34,z12,z5,z6,z369])],[(0,[z199,z3,z4,z428,z5,z6]),(0,[z0,z2,z3,z4,z32,z6]),(0,[z2,z3,z4,z551,z5,z278]),(0,[z2,z16,z5,z106,z23,z6]),(0,[z396,z3,z582,z4,z5,z6])],[(0,[z2,z3,z607,z5,z42,z6]),(0,[z2,z3,z4,z5,z17,z480])],[(0,[z2,z3,z12,z5,z1336,z6]),(0,[z376,z2,z3,z4,z12,z102]),(0,[z2,z136,z157,z12,z5,z6]),(0,[z2,z3,z1337,z12,z5,z6]),(0,[z202,z3,z131,z12,z5,z6])],[(0,[z2,z9,z12,z288,z5,z6]),(0,[z2,z3,z34,z12,z220,z6]),(0,[z2,z70,z34,z7,z5,z6]),(0,[z91,z2,z3,z5,z42,z92])],[(0,[z199,z10,z68,z12,z5,z6]),(0,[z2,z3,z34,z71,z5,z6]),(1,[z1,z513,z4,z5,z6]),(0,[z2,z9,z12,z5,z6,z29]),(0,[z2,z3,z289,z547,z5,z6])],[(0,[z1158,z2,z3,z4,z12,z5])],[(0,[z315,z2,z3,z5,z23,z6])],[(0,[z9,z58,z11,z12,z5,z6]),(0,[z2,z3,z4,z1338,z5,z6]),(0,[z315,z0,z3,z4,z5,z6]),(0,[z1339,z2,z3,z4,z5,z6]),(0,[z1340,z2,z3,z4,z5,z6]),(0,[z2,z3,z5,z42,z1341,z6])]],
   [[(0,[z2,z3,z12,z5,z1342,z6]),(0,[z2,z3,z1343,z12,z5,z6]),(0,[z367,z2,z3,z12,z23,z6]),(0,[z2,z12,z5,z106,z23,z6])],[(0,[z1,z544,z3,z4,z5,z6]),(0,[z2,z136,z12,z5,z6,z29])],[],[(0,[z2,z3,z4,z1344,z5,z6]),(0,[z2,z4,z12,z5,z879,z6])],[(0,[z2,z3,z4,z1345,z5,z6]),(0,[z2,z980,z3,z12,z5,z6]),(0,[z9,z3,z12,z5,z159,z6]),(0,[z2,z3,z34,z12,z47,z6])],[(0,[z2,z1346,z4,z12,z5,z6]),(0,[z2,z9,z636,z12,z5,z6]),(0,[z2,z3,z1347,z12,z5,z6]),(0,[z247,z2,z4,z5,z42,z29])],[(0,[z2,z3,z34,z12,z145,z6]),(0,[z90,z1,z3,z5,z6,z61]),(0,[z2,z10,z3,z5,z6,z375]),(0,[z2,z9,z3,z571,z5,z6]),(0,[z2,z4,z12,z5,z6,z1267])],[(0,[z8,z2,z9,z293,z5,z6]),(0,[z2,z1348,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z1349,z6]),(0,[z1350,z9,z3,z12,z5,z6]),(0,[z2,z9,z70,z7,z5,z6]),(0,[z523,z3,z12,z5,z31,z6])],[(0,[z199,z810,z4,z12,z5,z6]),(0,[z1,z3,z321,z4,z5,z6]),(0,[z2,z1351,z4,z12,z5,z6]),(0,[z3,z887,z34,z12,z5,z6])],[(0,[z8,z2,z3,z4,z5,z278]),(0,[z2,z109,z205,z12,z119,z6])],[(0,[z2,z3,z4,z12,z5,z1352]),(0,[z199,z1,z68,z4,z5,z6]),(0,[z2,z35,z3,z5,z281,z6]),(0,[z2,z3,z4,z5,z1353,z6])],[(0,[z1,z3,z5,z23,z6,z61]),(0,[z1,z2,z3,z5,z189,z6]),(0,[z2,z3,z4,z1354,z5,z6]),(0,[z197,z3,z4,z16,z5,z6])],[(0,[z2,z1038,z4,z12,z5,z6]),(0,[z396,z2,z3,z4,z5,z6]),(0,[z1355,z2,z3,z12,z5,z6]),(0,[z286,z3,z4,z12,z5,z61]),(0,[z2,z9,z12,z5,z6,z318]),(0,[z396,z3,z4,z119,z5,z6]),(0,[z2,z328,z3,z34,z5,z6]),(0,[z2,z3,z4,z16,z662,z6])],[(0,[z396,z3,z4,z291,z5,z6]),(0,[z2,z3,z34,z571,z5,z6])],[(0,[z1,z3,z4,z400,z5,z6]),(0,[z396,z3,z4,z170,z5,z6]),(0,[z2,z3,z12,z23,z609,z6])],[(0,[z2,z9,z163,z12,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z2,z10,z622,z12,z5,z6]),(0,[z2,z540,z522,z12,z5,z6])],[(0,[z324,z9,z68,z12,z5,z6]),(0,[z2,z3,z4,z1356,z5,z6]),(0,[z2,z1357,z3,z12,z5,z6]),(0,[z2,z1358,z3,z12,z5,z6]),(0,[z2,z3,z4,z1359,z5,z6]),(0,[z2,z3,z52,z5,z42,z21])],[(0,[z2,z540,z58,z12,z5,z6]),(0,[z90,z1,z2,z3,z5,z6]),(0,[z1,z3,z4,z170,z5,z6]),(0,[z2,z86,z12,z5,z6,z40]),(0,[z2,z5,z106,z23,z42,z6]),(0,[z2,z3,z582,z584,z5,z6])],[(0,[z315,z2,z3,z34,z5,z6])],[(0,[z8,z3,z292,z4,z5,z6]),(0,[z2,z1360,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1361])],[(0,[z2,z3,z4,z5,z6,z176]),(0,[z8,z2,z9,z10,z5,z6]),(0,[z91,z8,z2,z3,z5,z92]),(0,[z28,z2,z540,z12,z5,z6]),(0,[z2,z3,z12,z5,z1362,z6]),(0,[z63,z2,z3,z4,z42,z6]),(0,[z2,z3,z1363,z12,z5,z6])],[(0,[z2,z1364,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z1365,z6])],[],[(0,[z2,z9,z588,z12,z5,z6]),(0,[z1,z3,z4,z5,z1148,z6]),(0,[z2,z775,z3,z4,z5,z6]),(0,[z2,z3,z422,z5,z42,z6]),(0,[z2,z246,z4,z12,z5,z6])],[(0,[z8,z2,z86,z12,z5,z6]),(0,[z2,z3,z99,z5,z33,z6]),(0,[z2,z3,z5,z709,z23,z6])],[(0,[z322,z2,z3,z5,z6,z323])],[(0,[z2,z3,z12,z5,z1366,z6])],[],[(0,[z57,z59,z58,z12,z5,z6]),(0,[z2,z531,z3,z4,z5,z6]),(0,[z2,z3,z747,z12,z5,z6]),(0,[z2,z3,z5,z23,z6,z473])],[(0,[z43,z2,z3,z4,z354,z6]),(0,[z730,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z854])],[(0,[z2,z513,z232,z12,z5,z6]),(0,[z2,z1367,z3,z12,z5,z6]),(0,[z197,z97,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z6,z1368]),(0,[z2,z3,z12,z277,z23,z6]),(0,[z2,z3,z34,z5,z42,z6]),(0,[z130,z2,z3,z4,z12,z102])]],
   [[(0,[z0,z2,z9,z3,z5,z6]),(0,[z2,z9,z3,z183,z5,z6]),(0,[z2,z4,z5,z106,z42,z6])],[(0,[z1,z3,z4,z5,z495,z6]),(0,[z396,z13,z3,z4,z5,z6]),(0,[z2,z3,z1369,z12,z5,z6])],[(0,[z58,z4,z12,z5,z226,z6]),(0,[z2,z1370,z4,z12,z5,z6]),(0,[z43,z1,z513,z4,z5,z6]),(0,[z2,z9,z701,z12,z5,z6])],[(0,[z1,z2,z1270,z3,z5,z6])],[(0,[z2,z3,z4,z222,z5,z6]),(0,[z13,z3,z4,z12,z5,z966]),(0,[z2,z3,z12,z5,z6,z1371])],[],[(0,[z2,z405,z4,z12,z5,z6]),(0,[z9,z462,z68,z12,z5,z6]),(0,[z2,z3,z16,z5,z6,z323]),(0,[z202,z3,z12,z5,z23,z6])],[(0,[z1,z59,z3,z58,z5,z6]),(0,[z2,z9,z119,z5,z42,z6]),(0,[z2,z3,z4,z5,z6,z421]),(0,[z2,z3,z34,z183,z5,z6]),(0,[z130,z396,z3,z4,z5,z6])],[(0,[z153,z2,z9,z12,z5,z6]),(0,[z2,z9,z107,z12,z5,z6]),(0,[z2,z9,z12,z5,z604,z6])],[(0,[z269,z3,z4,z5,z42,z6]),(0,[z1372,z3,z4,z12,z5,z6]),(0,[z2,z494,z12,z5,z23,z6])],[(0,[z520,z1,z3,z4,z5,z6]),(0,[z1162,z2,z3,z4,z5,z6]),(0,[z2,z1373,z86,z12,z5,z6])],[(0,[z13,z9,z3,z12,z5,z14]),(0,[z2,z3,z4,z5,z1374,z6]),(0,[z2,z1017,z4,z5,z42,z6])],[(0,[z8,z3,z4,z484,z5,z6]),(0,[z2,z3,z1375,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z1376]),(0,[z2,z1377,z3,z12,z5,z6])],[(0,[z2,z3,z232,z236,z5,z6])],[(0,[z2,z3,z4,z1378,z5,z6]),(0,[z2,z86,z152,z12,z5,z6])],[(0,[z197,z10,z3,z12,z5,z6])],[(0,[z2,z9,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z1379]),(0,[z54,z1,z3,z4,z5,z6]),(0,[z100,z3,z4,z12,z5,z61]),(0,[z2,z86,z123,z12,z5,z6])],[(0,[z8,z254,z3,z4,z5,z6]),(0,[z100,z3,z12,z5,z323,z61]),(0,[z13,z3,z34,z12,z5,z14]),(0,[z1380,z3,z4,z12,z5,z6])],[(0,[z1381,z3,z4,z12,z5,z6])],[],[(0,[z0,z396,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z278]),(0,[z2,z9,z12,z615,z5,z6]),(0,[z2,z136,z3,z12,z5,z6]),(0,[z396,z3,z4,z5,z449,z6]),(0,[z841,z3,z4,z12,z5,z6]),(0,[z2,z3,z1382,z12,z5,z6])],[(0,[z2,z3,z1263,z12,z5,z6]),(0,[z1,z2,z3,z1383,z5,z6]),(0,[z197,z70,z3,z4,z5,z6])],[(0,[z20,z3,z116,z5,z42,z6]),(0,[z1,z3,z4,z517,z5,z6]),(0,[z1,z98,z3,z4,z5,z6]),(0,[z8,z2,z3,z161,z5,z6]),(0,[z2,z86,z12,z5,z6,z61]),(0,[z2,z3,z12,z5,z1384,z6]),(0,[z2,z3,z4,z16,z389,z6]),(0,[z1385,z3,z4,z12,z5,z6])],[(0,[z8,z9,z3,z11,z5,z6]),(0,[z2,z3,z16,z475,z5,z6]),(0,[z2,z1033,z3,z5,z42,z6])],[(0,[z2,z151,z116,z12,z5,z6]),(0,[z2,z3,z12,z1386,z5,z6]),(0,[z2,z3,z12,z5,z1387,z6])],[(0,[z2,z9,z68,z12,z5,z6]),(1,[z2,z86,z12,z5,z6]),(1,[z2,z747,z12,z5,z6]),(0,[z2,z3,z4,z5,z654,z218])],[(0,[z591,z68,z4,z12,z5,z6]),(0,[z1,z2,z9,z261,z5,z6]),(0,[z134,z2,z9,z3,z5,z6]),(0,[z2,z3,z4,z16,z609,z6]),(0,[z1388,z2,z86,z12,z5,z6]),(0,[z976,z2,z3,z4,z5,z42])],[(0,[z2,z9,z86,z12,z5,z6]),(0,[z2,z3,z4,z5,z1389,z6])],[(0,[z2,z9,z10,z16,z5,z6]),(0,[z2,z3,z4,z5,z1390,z6]),(0,[z2,z86,z124,z12,z5,z6]),(0,[z2,z3,z1391,z12,z5,z6])],[(0,[z2,z1392,z3,z4,z5,z6]),(0,[z1043,z3,z4,z5,z42,z6])]],
   [[(0,[z2,z136,z68,z12,z5,z6]),(0,[z8,z3,z34,z11,z5,z6])],[(0,[z2,z1393,z3,z4,z5,z6]),(0,[z2,z3,z34,z12,z280,z6]),(0,[z2,z3,z4,z1320,z5,z6])],[(0,[z2,z9,z336,z3,z5,z6]),(0,[z1,z2,z9,z10,z5,z6]),(0,[z28,z1,z2,z9,z5,z6]),(0,[z202,z3,z4,z16,z5,z6])],[(0,[z1165,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z500,z6])],[(0,[z2,z1272,z4,z12,z5,z6]),(0,[z2,z265,z12,z5,z23,z6]),(0,[z2,z3,z4,z5,z654,z17]),(0,[z2,z3,z16,z5,z6,z491])],[(0,[z2,z3,z12,z1394,z5,z6]),(0,[z653,z2,z4,z12,z5,z29]),(0,[z2,z86,z34,z12,z5,z6]),(0,[z2,z494,z4,z16,z5,z6])],[(0,[z396,z3,z4,z5,z354,z6]),(0,[z1,z2,z86,z12,z5,z6])],[(0,[z0,z3,z4,z5,z6,z61]),(0,[z2,z9,z19,z16,z5,z6]),(0,[z441,z10,z3,z12,z5,z6])],[(0,[z2,z3,z4,z1395,z5,z6]),(0,[z2,z3,z4,z5,z24,z6]),(0,[z2,z3,z658,z291,z5,z6]),(0,[z2,z1396,z3,z4,z5,z6])],[(0,[z2,z3,z1397,z12,z5,z6]),(0,[z179,z2,z3,z4,z5,z143]),(0,[z2,z10,z3,z5,z456,z6]),(0,[z2,z3,z4,z5,z1398,z6]),(0,[z247,z2,z4,z12,z5,z862]),(0,[z2,z3,z12,z5,z6,z1182])],[(0,[z2,z3,z4,z5,z33,z6]),(0,[z2,z3,z475,z5,z42,z6]),(0,[z2,z86,z12,z5,z168,z6])],[(0,[z2,z9,z3,z260,z5,z6]),(0,[z2,z1171,z3,z4,z5,z6])],[(0,[z2,z3,z1399,z12,z5,z6]),(0,[z734,z2,z3,z4,z12,z5]),(0,[z8,z2,z9,z119,z5,z6]),(0,[z26,z2,z86,z12,z5,z6])],[(0,[z2,z1400,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z45,z6]),(0,[z396,z3,z81,z4,z5,z6]),(0,[z396,z10,z3,z4,z5,z6]),(0,[z249,z3,z4,z5,z42,z6]),(0,[z2,z1401,z4,z12,z5,z6]),(0,[z861,z3,z4,z12,z5,z6]),(0,[z1402,z2,z3,z4,z5,z6]),(0,[z719,z3,z4,z65,z5,z6])],[(0,[z2,z9,z208,z58,z5,z6]),(0,[z2,z59,z208,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z1403])],[],[(0,[z1,z3,z15,z5,z23,z6]),(0,[z8,z2,z3,z345,z5,z6]),(0,[z2,z3,z113,z5,z42,z6]),(0,[z2,z10,z3,z5,z464,z6]),(0,[z254,z3,z4,z5,z42,z6])],[(0,[z374,z1,z3,z4,z5,z6]),(0,[z1404,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1405,z6]),(0,[z2,z3,z4,z5,z6,z1406]),(0,[z2,z3,z16,z710,z5,z6])],[(0,[z2,z3,z4,z1407,z5,z6]),(0,[z2,z3,z34,z260,z5,z6]),(0,[z2,z3,z16,z5,z23,z6]),(0,[z2,z3,z5,z23,z456,z6])],[(0,[z591,z1,z3,z4,z5,z6]),(0,[z2,z86,z12,z5,z31,z6]),(0,[z3,z4,z5,z42,z6,z1301]),(0,[z202,z3,z4,z132,z5,z6])],[(0,[z2,z208,z10,z3,z5,z6]),(0,[z2,z3,z4,z1408,z5,z6]),(0,[z2,z3,z4,z12,z5,z759])],[(0,[z2,z3,z4,z1409,z5,z6]),(0,[z2,z3,z12,z1410,z5,z6])],[(0,[z2,z3,z1411,z12,z5,z6]),(0,[z2,z3,z4,z65,z354,z6]),(0,[z2,z3,z4,z918,z5,z6]),(0,[z2,z1095,z3,z12,z5,z6])],[(0,[z2,z363,z405,z12,z5,z6]),(0,[z1,z2,z3,z4,z1180,z6]),(0,[z8,z2,z3,z5,z6,z355]),(0,[z2,z86,z12,z5,z44,z6]),(0,[z2,z3,z535,z5,z23,z6]),(0,[z2,z9,z16,z119,z5,z6]),(0,[z2,z1412,z4,z12,z5,z6]),(0,[z2,z267,z3,z5,z42,z6])],[(0,[z2,z3,z4,z1413,z5,z6]),(0,[z2,z70,z4,z7,z5,z6]),(0,[z2,z34,z12,z5,z6,z985])],[(0,[z2,z3,z4,z71,z5,z6]),(0,[z2,z142,z10,z12,z5,z6]),(0,[z2,z3,z4,z1414,z5,z6])],[(0,[z315,z3,z4,z5,z44,z6])],[(1,[z396,z9,z3,z5,z6])],[(0,[z8,z1,z3,z4,z5,z6]),(0,[z2,z4,z12,z5,z6,z1415]),(0,[z322,z2,z9,z3,z5,z6])],[(0,[z2,z3,z4,z1416,z5,z6]),(0,[z8,z2,z4,z5,z6,z369]),(0,[z2,z55,z3,z89,z5,z6])],[(0,[z2,z151,z12,z5,z23,z6]),(0,[z43,z134,z3,z4,z44,z6]),(0,[z396,z10,z3,z5,z42,z6]),(0,[z2,z3,z34,z12,z902,z6]),(0,[z91,z396,z3,z4,z5,z6])],[(0,[z1,z10,z3,z15,z5,z6]),(0,[z1,z254,z3,z4,z5,z6])]],
   [[(0,[z2,z265,z4,z16,z5,z6])],[(0,[z8,z3,z4,z608,z5,z6]),(0,[z43,z2,z86,z12,z5,z6]),(0,[z2,z3,z1417,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1418,z6]),(1,[z2,z1095,z12,z5,z6]),(0,[z2,z12,z5,z106,z604,z6]),(0,[z2,z487,z3,z5,z21,z6])],[(0,[z1,z415,z3,z4,z5,z6]),(0,[z2,z3,z232,z12,z5,z585]),(0,[z134,z3,z4,z5,z6,z61]),(0,[z179,z2,z10,z3,z5,z56]),(0,[z28,z2,z4,z69,z42,z6])],[(0,[z2,z3,z99,z12,z5,z6]),(0,[z2,z540,z107,z12,z5,z6]),(0,[z2,z3,z152,z5,z6,z245]),(0,[z2,z3,z4,z42,z6,z679])],[(0,[z1,z2,z3,z161,z5,z6]),(0,[z2,z3,z12,z5,z1419,z6]),(0,[z3,z887,z4,z12,z5,z6])],[(0,[z2,z3,z4,z551,z5,z436])],[(0,[z2,z3,z4,z12,z5,z966]),(0,[z202,z10,z3,z12,z5,z6]),(0,[z2,z3,z582,z124,z5,z6])],[(0,[z2,z265,z4,z12,z5,z419]),(0,[z1420,z3,z4,z12,z5,z6]),(0,[z2,z3,z1421,z12,z5,z6])],[(0,[z2,z97,z77,z78,z5,z6]),(0,[z2,z3,z361,z16,z5,z6])],[(0,[z115,z271,z3,z12,z5,z6]),(0,[z8,z2,z10,z3,z5,z6]),(0,[z90,z2,z3,z16,z5,z6]),(0,[z63,z2,z3,z161,z42,z6]),(0,[z2,z3,z4,z571,z5,z6]),(0,[z2,z246,z345,z12,z5,z6])],[(0,[z1350,z3,z4,z12,z5,z6])],[(0,[z10,z1422,z3,z12,z5,z6]),(0,[z536,z2,z4,z12,z5,z29])],[(0,[z8,z199,z68,z4,z5,z6]),(0,[z2,z540,z3,z12,z5,z6]),(0,[z0,z3,z4,z210,z5,z6])],[(0,[z2,z3,z1423,z12,z5,z6]),(0,[z451,z2,z10,z3,z5,z6]),(0,[z2,z513,z12,z5,z23,z6]),(0,[z100,z3,z4,z12,z5,z966]),(0,[z1424,z2,z3,z4,z5,z6])],[],[(0,[z179,z2,z267,z3,z5,z6])],[(0,[z199,z0,z3,z4,z5,z6]),(0,[z2,z4,z12,z5,z6,z1425]),(0,[z2,z3,z4,z5,z1426,z6]),(0,[z629,z396,z3,z4,z5,z6])],[(0,[z1,z2,z3,z5,z213,z6]),(0,[z25,z513,z4,z12,z5,z6]),(0,[z2,z9,z157,z12,z5,z29]),(0,[z28,z2,z136,z12,z5,z6]),(0,[z2,z4,z5,z42,z1226,z6])],[(0,[z3,z4,z5,z42,z771,z6]),(0,[z202,z3,z4,z12,z5,z102])],[],[(0,[z2,z3,z1427,z12,z5,z6]),(0,[z2,z3,z12,z5,z189,z6]),(0,[z2,z1428,z3,z4,z5,z6]),(0,[z3,z4,z12,z5,z1429,z6])],[(0,[z2,z10,z3,z428,z5,z6])],[(0,[z2,z3,z4,z1430,z5,z6]),(0,[z2,z1431,z3,z12,z5,z6]),(0,[z8,z2,z3,z4,z5,z436])],[(0,[z156,z1,z3,z4,z5,z6]),(0,[z1,z443,z3,z4,z5,z6]),(0,[z2,z3,z12,z5,z1432,z6])],[(0,[z1,z2,z9,z119,z5,z6]),(0,[z2,z552,z4,z78,z5,z6]),(0,[z2,z1433,z3,z12,z5,z6])],[(0,[z2,z3,z4,z1434,z5,z6]),(0,[z2,z151,z4,z16,z5,z6]),(0,[z202,z362,z4,z12,z5,z6])],[],[(0,[z2,z3,z4,z5,z42,z6]),(0,[z2,z3,z1176,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z1435]),(0,[z2,z3,z1436,z12,z5,z6])],[(0,[z228,z2,z384,z4,z5,z6]),(0,[z1,z2,z3,z345,z5,z6]),(0,[z2,z3,z12,z5,z1437,z6]),(0,[z1438,z2,z3,z4,z5,z6])],[(0,[z1439,z2,z3,z4,z12,z6]),(0,[z2,z3,z4,z12,z5,z1440]),(0,[z2,z344,z4,z7,z5,z6]),(0,[z3,z4,z12,z5,z1083,z6]),(0,[z1441,z396,z3,z4,z5,z6]),(0,[z2,z3,z230,z5,z456,z6])],[(0,[z2,z3,z12,z5,z1442,z6]),(0,[z290,z2,z86,z12,z5,z6])]],
   [[(0,[z2,z3,z230,z16,z5,z6])],[(0,[z1,z103,z3,z4,z5,z6]),(0,[z2,z3,z4,z1443,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1444]),(0,[z2,z86,z3,z16,z5,z6]),(0,[z2,z494,z12,z5,z6,z92])],[(0,[z10,z3,z5,z159,z42,z6])],[(0,[z1,z2,z3,z5,z6,z355]),(0,[z8,z441,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1445]),(0,[z2,z3,z1446,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1447])],[(0,[z247,z1,z2,z4,z5,z29]),(0,[z2,z3,z4,z1448,z5,z6])],[(1,[z810,z4,z12,z5,z6]),(0,[z1,z10,z3,z58,z5,z6]),(0,[z2,z3,z1449,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1450]),(0,[z1,z2,z3,z1014,z5,z6]),(0,[z2,z9,z3,z27,z5,z6])],[(0,[z1451,z2,z3,z12,z5,z6]),(0,[z2,z1452,z4,z12,z5,z6]),(0,[z396,z3,z4,z5,z159,z6])],[],[(0,[z1,z408,z3,z4,z5,z6]),(0,[z2,z171,z3,z5,z6,z473]),(0,[z2,z1453,z3,z12,z5,z6])],[(0,[z1,z2,z4,z5,z6,z369]),(0,[z2,z513,z4,z16,z5,z6])],[(0,[z2,z3,z183,z5,z23,z6])],[(0,[z8,z2,z3,z361,z5,z6]),(0,[z3,z4,z12,z15,z72,z6]),(0,[z2,z12,z119,z5,z189,z6]),(0,[z130,z2,z3,z345,z12,z102])],[(0,[z2,z3,z71,z5,z23,z6]),(0,[z13,z3,z4,z12,z5,z388]),(0,[z2,z86,z108,z12,z5,z6]),(0,[z2,z3,z34,z27,z5,z6]),(0,[z2,z52,z12,z5,z21,z369])],[(0,[z8,z115,z3,z81,z5,z6]),(0,[z2,z692,z10,z12,z5,z6])],[(0,[z1454,z2,z3,z4,z5,z6]),(0,[z13,z3,z4,z12,z5,z14]),(0,[z2,z9,z3,z1455,z5,z6])],[(0,[z3,z4,z12,z5,z194,z61]),(0,[z2,z9,z12,z5,z6,z369]),(0,[z1456,z396,z3,z4,z5,z6])],[(0,[z259,z2,z75,z4,z5,z6]),(0,[z2,z3,z53,z12,z5,z6])],[(0,[z8,z2,z4,z5,z106,z6]),(0,[z2,z3,z34,z12,z23,z6])],[(0,[z2,z9,z3,z16,z50,z6]),(0,[z2,z10,z494,z12,z5,z6]),(0,[z2,z3,z1457,z12,z5,z6]),(0,[z2,z3,z4,z5,z1458,z6])],[(0,[z1,z3,z4,z549,z5,z6]),(0,[z2,z58,z12,z5,z189,z6]),(0,[z738,z3,z4,z12,z5,z6])],[(0,[z8,z2,z3,z53,z5,z6]),(0,[z8,z249,z3,z4,z5,z6]),(0,[z2,z86,z12,z15,z5,z6]),(0,[z2,z3,z1459,z12,z5,z6]),(0,[z2,z9,z5,z42,z6,z29]),(0,[z2,z9,z182,z12,z5,z6]),(0,[z2,z3,z4,z5,z17,z639]),(0,[z2,z107,z3,z16,z5,z6])],[(0,[z2,z363,z3,z5,z42,z6]),(0,[z2,z3,z34,z12,z507,z6]),(0,[z2,z3,z4,z5,z6,z1460]),(0,[z2,z86,z109,z12,z5,z6])],[(0,[z43,z1,z3,z4,z354,z6]),(0,[z2,z1018,z4,z12,z5,z6]),(0,[z2,z798,z3,z12,z5,z6])],[(0,[z2,z9,z3,z1461,z5,z6]),(0,[z1422,z3,z4,z12,z5,z6]),(0,[z1075,z162,z3,z4,z5,z6])],[(0,[z2,z3,z4,z16,z32,z6]),(0,[z2,z3,z34,z331,z47,z6])],[(0,[z2,z10,z3,z547,z5,z6]),(0,[z26,z2,z3,z12,z23,z6]),(0,[z2,z3,z34,z16,z50,z6])],[(0,[z25,z3,z4,z15,z33,z6])],[(0,[z43,z3,z4,z532,z44,z6]),(0,[z2,z9,z487,z3,z5,z6]),(0,[z396,z3,z4,z5,z6,z1462])],[(0,[z8,z3,z4,z11,z5,z6]),(0,[z8,z2,z9,z5,z6,z29]),(0,[z2,z4,z1131,z78,z5,z6])],[(0,[z25,z3,z12,z15,z45,z6]),(0,[z396,z3,z4,z5,z6,z561])],[(0,[z115,z3,z12,z5,z198,z6]),(0,[z2,z3,z4,z5,z6,z1463]),(0,[z2,z3,z4,z5,z1234,z6]),(0,[z2,z85,z12,z5,z6,z204]),(0,[z2,z1464,z3,z12,z5,z6]),(1,[z2,z3,z12,z5,z778]),(0,[z2,z3,z5,z42,z822,z6])]],
   [[(0,[z2,z4,z12,z1131,z5,z6])],[(0,[z1,z3,z4,z559,z5,z6]),(0,[z247,z2,z4,z5,z473,z29]),(0,[z3,z4,z16,z5,z159,z6])],[(0,[z57,z2,z86,z12,z5,z6]),(0,[z2,z3,z5,z6,z375,z323]),(0,[z2,z86,z4,z12,z5,z6]),(0,[z2,z3,z1465,z12,z5,z6]),(0,[z2,z3,z4,z5,z42,z278]),(0,[z2,z3,z234,z12,z5,z6])],[(0,[z2,z3,z12,z1466,z5,z6]),(0,[z1467,z3,z4,z12,z5,z6])],[(0,[z2,z531,z10,z3,z5,z6]),(0,[z43,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z436]),(0,[z270,z3,z60,z12,z5,z6])],[(0,[z1,z3,z4,z626,z5,z6]),(0,[z2,z9,z3,z141,z5,z17]),(0,[z2,z36,z3,z291,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1468]),(0,[z43,z3,z4,z186,z44,z6]),(0,[z2,z3,z564,z5,z42,z6]),(0,[z26,z2,z86,z12,z23,z6]),(0,[z179,z2,z3,z5,z491,z56])],[],[(0,[z1,z271,z3,z4,z5,z6]),(0,[z315,z25,z3,z4,z5,z6]),(0,[z2,z9,z16,z5,z6,z29])],[(0,[z13,z3,z4,z260,z5,z14])],[(0,[z1,z336,z3,z4,z5,z6])],[(0,[z57,z336,z58,z4,z5,z6]),(0,[z2,z9,z75,z12,z5,z6]),(0,[z2,z3,z320,z16,z5,z6]),(0,[z2,z3,z12,z5,z6,z1469]),(0,[z2,z1470,z3,z12,z5,z6])],[(0,[z1,z13,z10,z3,z5,z6])],[(0,[z440,z2,z293,z4,z5,z6]),(0,[z8,z2,z3,z34,z47,z6]),(0,[z2,z3,z1311,z12,z5,z6]),(0,[z2,z3,z12,z65,z23,z39])],[(0,[z2,z917,z12,z5,z23,z6]),(0,[z2,z916,z12,z5,z74,z6])],[(0,[z2,z3,z232,z186,z5,z6]),(0,[z2,z1471,z3,z12,z5,z6])],[(0,[z2,z1472,z3,z12,z5,z6])],[(0,[z1,z441,z3,z4,z5,z6]),(0,[z287,z1,z3,z4,z5,z6]),(0,[z2,z10,z3,z5,z448,z6]),(0,[z467,z2,z3,z12,z5,z432]),(0,[z2,z3,z801,z4,z5,z6])],[(0,[z2,z3,z12,z5,z23,z585]),(0,[z2,z3,z1473,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1474]),(0,[z548,z2,z3,z12,z23,z6]),(0,[z2,z1475,z4,z12,z5,z6]),(0,[z130,z2,z3,z12,z23,z102])],[(0,[z8,z2,z3,z475,z5,z6]),(0,[z269,z3,z289,z12,z5,z6])],[(0,[z2,z9,z614,z12,z5,z6]),(0,[z1476,z2,z3,z4,z5,z6]),(0,[z1477,z2,z3,z4,z5,z6]),(0,[z2,z70,z10,z7,z5,z6])],[(0,[z57,z58,z12,z5,z23,z6]),(0,[z8,z2,z3,z4,z5,z1288]),(0,[z2,z1478,z3,z4,z5,z6])],[(0,[z2,z208,z3,z5,z23,z6]),(0,[z1479,z9,z3,z12,z5,z6])],[(0,[z199,z68,z12,z5,z23,z6])],[(0,[z2,z1480,z3,z12,z5,z6])],[(0,[z2,z9,z363,z12,z5,z6]),(0,[z1,z2,z3,z361,z5,z6]),(0,[z3,z4,z5,z1429,z456,z6])],[(0,[z2,z1481,z3,z4,z5,z6]),(0,[z1,z513,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z1482]),(0,[z2,z4,z7,z1131,z5,z6]),(0,[z2,z3,z5,z23,z448,z6]),(0,[z2,z246,z131,z12,z5,z6])],[(0,[z1483,z9,z3,z12,z5,z6]),(0,[z2,z9,z110,z12,z5,z6]),(0,[z2,z3,z4,z1131,z5,z6]),(0,[z2,z3,z320,z551,z5,z6]),(0,[z2,z3,z4,z12,z902,z6])],[(0,[z115,z396,z3,z4,z5,z6]),(0,[z2,z3,z345,z571,z5,z6])],[(0,[z2,z86,z12,z5,z178,z6])],[(0,[z2,z10,z3,z236,z5,z6])],[]],
   [[(0,[z2,z9,z58,z16,z5,z6]),(0,[z2,z1484,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z1485]),(0,[z986,z3,z4,z12,z5,z6]),(0,[z2,z171,z3,z16,z5,z6]),(0,[z2,z1230,z3,z12,z5,z6])],[(0,[z2,z1486,z3,z12,z5,z6]),(0,[z2,z3,z1487,z12,z5,z6]),(0,[z2,z3,z1488,z12,z5,z6]),(0,[z1489,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z1490,z6]),(0,[z2,z3,z5,z23,z859,z6])],[(0,[z2,z9,z96,z12,z5,z6]),(0,[z1,z2,z3,z53,z5,z6]),(0,[z1,z249,z3,z4,z5,z6]),(0,[z3,z4,z12,z720,z44,z6]),(0,[z2,z9,z158,z12,z5,z6]),(0,[z2,z70,z4,z1131,z5,z6]),(0,[z2,z1213,z362,z12,z5,z6])],[(0,[z536,z2,z9,z12,z5,z6]),(0,[z1491,z3,z4,z12,z5,z6]),(0,[z396,z3,z4,z124,z5,z6])],[(0,[z2,z3,z4,z1492,z5,z6]),(0,[z1,z3,z4,z5,z39,z61]),(0,[z1493,z2,z3,z4,z5,z6]),(0,[z2,z3,z5,z45,z33,z6]),(0,[z2,z3,z394,z124,z5,z6])],[(0,[z2,z9,z12,z5,z106,z6])],[(0,[z1,z9,z58,z4,z5,z6]),(0,[z2,z1494,z3,z12,z5,z6]),(0,[z8,z2,z3,z607,z5,z6]),(0,[z2,z9,z3,z331,z5,z6])],[(0,[z2,z10,z12,z371,z5,z6]),(0,[z396,z3,z4,z5,z224,z6]),(0,[z2,z3,z4,z65,z456,z39])],[(1,[z845,z3,z4,z5,z6]),(0,[z2,z3,z4,z1495,z5,z6])],[(0,[z1,z3,z4,z5,z6,z602]),(0,[z396,z3,z4,z5,z69,z6])],[(0,[z1,z2,z9,z5,z6,z29]),(0,[z2,z3,z4,z5,z1496,z6]),(0,[z2,z10,z109,z12,z119,z6])],[(0,[z2,z208,z3,z34,z5,z6]),(0,[z2,z3,z4,z1497,z5,z6]),(0,[z115,z151,z81,z12,z5,z6]),(0,[z2,z9,z599,z12,z5,z6]),(0,[z2,z86,z7,z12,z5,z6])],[(0,[z2,z1274,z4,z12,z5,z6]),(0,[z8,z2,z3,z5,z23,z6])],[(0,[z2,z3,z12,z1498,z5,z6]),(0,[z2,z3,z34,z331,z5,z6])],[(0,[z2,z3,z4,z16,z5,z585]),(0,[z2,z3,z345,z5,z42,z6]),(0,[z2,z3,z1499,z12,z5,z6])],[(0,[z1000,z3,z4,z12,z5,z6]),(0,[z2,z3,z34,z12,z339,z6])],[(0,[z2,z9,z336,z58,z5,z6]),(0,[z2,z3,z1500,z12,z5,z6]),(0,[z451,z2,z3,z5,z23,z6]),(0,[z2,z3,z4,z5,z6,z1501]),(0,[z2,z86,z12,z291,z5,z6])],[(0,[z57,z58,z4,z16,z5,z6]),(0,[z2,z3,z12,z1502,z5,z6]),(0,[z0,z2,z3,z4,z354,z6]),(0,[z2,z86,z12,z170,z5,z6]),(0,[z396,z3,z1503,z4,z5,z6])],[(0,[z1,z9,z3,z5,z6,z61]),(0,[z30,z2,z3,z126,z5,z6])],[(0,[z2,z3,z4,z5,z1504,z6]),(0,[z199,z68,z4,z16,z5,z6]),(0,[z1505,z2,z3,z4,z5,z6]),(0,[z2,z265,z4,z236,z5,z6])],[(0,[z2,z3,z4,z1506,z5,z6])],[(0,[z2,z9,z597,z12,z5,z6]),(0,[z2,z4,z12,z5,z1507,z6]),(0,[z270,z3,z81,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1508]),(0,[z8,z2,z3,z4,z5,z419]),(0,[z2,z85,z4,z12,z5,z436])],[(0,[z2,z1509,z3,z12,z5,z6]),(0,[z1510,z3,z4,z12,z5,z6]),(0,[z2,z1511,z3,z12,z5,z6])],[(0,[z2,z3,z4,z12,z5,z1281]),(1,[z1,z2,z86,z5,z6]),(0,[z2,z3,z12,z5,z1063,z6])],[(0,[z1,z3,z4,z481,z5,z6]),(0,[z8,z2,z86,z5,z23,z6]),(0,[z2,z3,z4,z5,z6,z1290])],[(0,[z115,z3,z81,z211,z5,z6]),(0,[z1,z3,z34,z5,z6,z61]),(0,[z43,z3,z12,z44,z23,z6])],[(0,[z1,z2,z3,z34,z47,z6]),(0,[z2,z9,z165,z12,z5,z6]),(0,[z2,z3,z4,z853,z5,z6]),(0,[z254,z3,z289,z12,z5,z6]),(0,[z2,z3,z571,z5,z23,z6]),(0,[z179,z2,z3,z34,z5,z56])],[(0,[z2,z3,z4,z12,z904,z6]),(0,[z2,z1512,z4,z12,z5,z6]),(0,[z179,z2,z9,z3,z5,z56]),(0,[z2,z3,z12,z5,z1513,z6])],[(0,[z2,z363,z85,z12,z5,z6]),(0,[z2,z3,z4,z5,z1514,z6]),(0,[z2,z3,z12,z5,z213,z6]),(0,[z9,z249,z3,z12,z5,z6]),(0,[z2,z77,z3,z16,z5,z6]),(0,[z2,z1515,z3,z4,z5,z6]),(0,[z2,z1516,z4,z12,z5,z6])],[(0,[z858,z3,z4,z12,z5,z6]),(0,[z1517,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z906]),(0,[z162,z9,z3,z12,z5,z6])],[(0,[z156,z3,z4,z12,z44,z6]),(0,[z2,z3,z4,z1518,z5,z6]),(0,[z2,z874,z4,z12,z5,z6]),(0,[z2,z9,z157,z16,z5,z6]),(0,[z2,z4,z12,z757,z5,z6]),(0,[z2,z3,z34,z1519,z5,z6]),(0,[z578,z2,z3,z4,z42,z6])]],
   [[(0,[z1,z2,z3,z475,z5,z6])],[(0,[z2,z3,z4,z1520,z5,z6]),(0,[z8,z2,z3,z34,z5,z6]),(0,[z2,z3,z1521,z12,z5,z6])],[],[(0,[z270,z1,z3,z4,z5,z6]),(0,[z2,z713,z513,z12,z5,z6]),(0,[z2,z3,z1522,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z1523])],[(0,[z2,z3,z4,z5,z6,z877]),(0,[z2,z9,z3,z5,z6,z473]),(0,[z2,z108,z3,z16,z5,z6])],[(0,[z451,z2,z3,z34,z5,z6]),(0,[z162,z3,z34,z12,z5,z6])],[(0,[z2,z3,z222,z5,z23,z6]),(0,[z2,z3,z4,z1524,z5,z6]),(0,[z2,z3,z4,z12,z5,z865]),(0,[z247,z2,z86,z12,z5,z6]),(0,[z2,z246,z12,z5,z23,z6])],[(0,[z2,z3,z1525,z4,z5,z6]),(0,[z2,z3,z1526,z12,z5,z6]),(0,[z2,z1527,z3,z12,z5,z6])],[(0,[z2,z1528,z4,z12,z5,z6])],[(0,[z2,z3,z1529,z12,z5,z6]),(0,[z28,z2,z9,z12,z5,z6]),(0,[z944,z3,z4,z12,z5,z6]),(0,[z2,z3,z1530,z12,z5,z6]),(0,[z2,z916,z4,z12,z5,z6])],[(0,[z2,z3,z4,z27,z5,z6])],[(0,[z2,z4,z12,z5,z1531,z6])],[(0,[z1,z58,z4,z5,z69,z6]),(0,[z2,z9,z151,z12,z5,z6]),(0,[z2,z3,z34,z12,z600,z6])],[(0,[z57,z810,z4,z12,z5,z6]),(0,[z20,z462,z3,z12,z5,z6]),(0,[z2,z9,z3,z1532,z5,z6]),(0,[z2,z86,z52,z12,z5,z6])],[(0,[z2,z1533,z3,z4,z5,z6]),(0,[z2,z9,z157,z12,z5,z624]),(0,[z2,z3,z12,z5,z6,z355]),(0,[z2,z3,z34,z16,z47,z6]),(0,[z2,z3,z4,z16,z65,z39])],[(0,[z8,z493,z3,z4,z5,z6]),(0,[z26,z2,z3,z27,z23,z6])],[(0,[z1,z9,z58,z12,z5,z6]),(0,[z2,z1370,z12,z5,z23,z6])],[(0,[z8,z2,z9,z68,z5,z6]),(0,[z2,z97,z78,z5,z23,z6]),(0,[z2,z3,z12,z5,z1534,z6])],[(0,[z28,z1,z2,z4,z69,z6]),(0,[z451,z2,z3,z4,z24,z6]),(0,[z28,z2,z9,z12,z280,z6])],[(0,[z1,z2,z3,z607,z5,z6]),(0,[z2,z3,z4,z1455,z5,z6]),(0,[z2,z3,z12,z1535,z5,z6]),(0,[z2,z10,z3,z12,z5,z585]),(0,[z1536,z2,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z1537]),(0,[z2,z3,z205,z5,z42,z6]),(0,[z2,z3,z12,z219,z23,z6])],[(0,[z810,z58,z4,z12,z5,z6]),(0,[z1,z3,z4,z640,z5,z6])],[(0,[z1,z109,z58,z4,z5,z6]),(0,[z2,z1538,z3,z4,z5,z6]),(0,[z1,z3,z75,z4,z5,z6]),(0,[z2,z3,z12,z5,z460,z92])],[(0,[z2,z3,z1154,z12,z5,z6]),(0,[z3,z4,z12,z5,z6,z95]),(0,[z2,z3,z5,z45,z42,z6]),(0,[z28,z2,z4,z12,z879,z6]),(0,[z2,z3,z12,z5,z1539,z6])],[(0,[z2,z3,z1540,z12,z5,z6]),(0,[z8,z396,z3,z4,z5,z6]),(0,[z2,z3,z4,z1541,z5,z6]),(0,[z2,z9,z12,z5,z1063,z6]),(0,[z1542,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z16,z50,z6])],[(0,[z2,z9,z10,z5,z42,z6])],[(0,[z1,z2,z3,z5,z23,z6]),(0,[z8,z2,z265,z4,z5,z6]),(0,[z2,z9,z12,z216,z5,z6])],[(0,[z134,z2,z3,z4,z5,z6]),(0,[z1280,z3,z4,z12,z5,z6])],[(0,[z2,z1543,z4,z12,z5,z6]),(0,[z451,z396,z3,z4,z5,z6]),(0,[z2,z10,z3,z476,z5,z6]),(0,[z396,z3,z4,z5,z6,z102])],[(0,[z2,z3,z607,z16,z5,z6]),(0,[z2,z3,z4,z1461,z5,z6]),(0,[z28,z2,z289,z12,z69,z6])],[(0,[z2,z513,z4,z236,z5,z6]),(0,[z2,z3,z4,z5,z1544,z6]),(0,[z2,z3,z34,z12,z613,z6])],[(0,[z1,z3,z4,z12,z5,z585]),(0,[z2,z947,z3,z12,z5,z6]),(0,[z91,z2,z3,z16,z5,z92])],[(0,[z2,z825,z3,z12,z5,z6]),(0,[z2,z258,z4,z398,z5,z6])]],
   [[],[(0,[z1,z2,z1528,z4,z5,z6]),(0,[z2,z3,z4,z24,z42,z6]),(0,[z2,z3,z4,z12,z720,z6]),(0,[z2,z9,z19,z5,z42,z6]),(0,[z2,z3,z1545,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1546,z6]),(0,[z1,z2,z3,z4,z5,z419]),(0,[z2,z9,z552,z5,z42,z6]),(0,[z2,z3,z4,z899,z5,z6]),(0,[z2,z246,z4,z16,z5,z6])],[(0,[z592,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z1547,z5,z6]),(0,[z2,z3,z4,z16,z203,z6]),(0,[z2,z12,z5,z1507,z23,z6])],[(0,[z2,z3,z4,z1548,z5,z6]),(0,[z2,z9,z328,z3,z5,z6]),(0,[z2,z3,z1549,z12,z5,z6]),(0,[z2,z3,z1550,z12,z5,z6])],[(0,[z196,z58,z4,z12,z5,z6]),(0,[z1,z2,z86,z5,z23,z6]),(0,[z1,z3,z34,z411,z5,z6]),(0,[z2,z9,z12,z5,z6,z741]),(0,[z9,z3,z12,z5,z6,z95]),(0,[z2,z3,z4,z5,z1551,z6]),(0,[z2,z3,z4,z12,z5,z778]),(0,[z2,z1289,z3,z12,z5,z6])],[(0,[z2,z531,z3,z5,z23,z6]),(0,[z2,z9,z48,z12,z5,z6]),(0,[z2,z3,z289,z12,z5,z6]),(0,[z2,z3,z34,z5,z6,z711]),(0,[z2,z3,z16,z5,z51,z6])],[(0,[z2,z9,z344,z12,z5,z6]),(0,[z2,z86,z19,z12,z5,z6]),(0,[z2,z55,z3,z291,z5,z6]),(0,[z197,z55,z3,z4,z5,z6]),(0,[z197,z3,z34,z12,z5,z6])],[(0,[z199,z574,z4,z12,z5,z6]),(0,[z2,z265,z4,z12,z5,z585]),(0,[z247,z2,z4,z16,z5,z29])],[],[(0,[z2,z1068,z3,z12,z5,z6]),(0,[z2,z3,z12,z5,z6,z1552])],[],[(0,[z2,z1553,z3,z12,z5,z6]),(0,[z2,z86,z55,z12,z5,z6]),(0,[z2,z3,z131,z571,z5,z6])],[(0,[z1554,z3,z4,z12,z5,z6])],[(0,[z1,z2,z3,z34,z5,z6]),(0,[z396,z3,z152,z4,z5,z6]),(0,[z2,z3,z5,z23,z42,z6])],[(0,[z1,z3,z4,z5,z661,z6]),(0,[z28,z2,z9,z12,z5,z278]),(0,[z254,z9,z4,z12,z5,z6]),(0,[z2,z326,z3,z418,z5,z6]),(0,[z2,z3,z4,z5,z854,z56])],[(0,[z2,z3,z12,z5,z1555,z6]),(0,[z2,z3,z4,z5,z42,z436]),(0,[z2,z1556,z3,z12,z5,z6])],[(0,[z43,z8,z3,z4,z44,z6]),(0,[z3,z4,z12,z5,z1331,z6])],[(0,[z2,z3,z4,z1557,z5,z6])],[(0,[z2,z3,z1558,z12,z5,z6]),(0,[z2,z10,z3,z12,z65,z39]),(0,[z2,z1283,z362,z12,z5,z6]),(0,[z2,z246,z4,z132,z5,z6])],[(0,[z2,z3,z232,z12,z5,z6])],[(0,[z2,z3,z1559,z12,z5,z6]),(0,[z2,z848,z4,z12,z5,z6]),(0,[z43,z0,z3,z4,z5,z6])],[(0,[z2,z9,z272,z12,z5,z6]),(0,[z2,z86,z12,z5,z5,z6])],[(0,[z441,z9,z3,z12,z5,z6])],[(0,[z2,z68,z607,z12,z5,z6]),(0,[z1560,z2,z3,z4,z5,z6])],[(1,[z396,z3,z4,z5,z6]),(0,[z1451,z1,z2,z3,z5,z6]),(0,[z2,z9,z3,z5,z456,z6]),(0,[z2,z3,z4,z12,z5,z998])],[(1,[z3,z953,z12,z5,z6]),(0,[z322,z2,z3,z4,z5,z6]),(0,[z2,z265,z4,z5,z42,z6]),(0,[z1479,z3,z4,z12,z5,z6]),(0,[z2,z10,z3,z1354,z5,z6])],[(0,[z2,z531,z3,z34,z5,z6]),(0,[z2,z1561,z4,z12,z5,z6]),(0,[z2,z9,z3,z16,z5,z6]),(0,[z2,z86,z12,z78,z5,z6]),(0,[z2,z86,z5,z23,z42,z6])],[(0,[z8,z2,z9,z19,z5,z6]),(0,[z10,z3,z12,z5,z159,z6])],[(0,[z2,z3,z12,z1562,z5,z6]),(0,[z43,z134,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1563]),(0,[z2,z3,z12,z5,z1564,z6]),(0,[z396,z9,z3,z4,z5,z6]),(0,[z2,z1565,z3,z12,z5,z6]),(0,[z2,z3,z4,z1566,z5,z6]),(0,[z2,z3,z34,z47,z42,z6])],[(0,[z1,z2,z9,z68,z5,z6]),(0,[z2,z3,z4,z1567,z5,z6]),(0,[z441,z3,z34,z12,z5,z6])],[(0,[z1,z3,z597,z4,z5,z6]),(0,[z1483,z3,z4,z12,z5,z6]),(0,[z2,z3,z4,z12,z65,z763])]],
   [[(0,[z1,z3,z4,z76,z5,z6]),(0,[z8,z616,z3,z4,z5,z6]),(0,[z2,z136,z3,z16,z5,z6]),(0,[z2,z3,z34,z5,z456,z6])],[(0,[z2,z3,z16,z5,z189,z6]),(0,[z91,z2,z3,z12,z5,z302])],[(0,[z2,z10,z513,z12,z5,z6]),(0,[z2,z3,z34,z16,z5,z6]),(0,[z3,z12,z5,z23,z771,z6])],[(0,[z2,z9,z3,z12,z5,z419]),(0,[z2,z3,z4,z1568,z5,z6]),(0,[z1569,z3,z4,z12,z5,z6]),(0,[z2,z3,z12,z5,z1341,z6]),(0,[z719,z2,z3,z4,z5,z6])],[(0,[z1,z396,z3,z4,z5,z6]),(0,[z1,z13,z9,z3,z5,z6]),(0,[z396,z3,z34,z4,z5,z6])],[(0,[z2,z97,z4,z398,z5,z6]),(0,[z2,z3,z4,z648,z42,z6])],[(0,[z1,z2,z265,z4,z5,z6]),(0,[z2,z86,z11,z12,z5,z6]),(0,[z2,z9,z703,z12,z5,z6])],[(0,[z2,z86,z12,z1570,z5,z6]),(0,[z2,z4,z16,z5,z106,z6])],[(0,[z2,z3,z105,z124,z5,z6]),(0,[z2,z3,z152,z584,z5,z6])],[(0,[z2,z3,z1571,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1572,z6]),(0,[z2,z3,z4,z331,z5,z6]),(0,[z26,z396,z3,z4,z5,z6]),(0,[z2,z3,z132,z5,z23,z6])],[(0,[z2,z4,z12,z5,z6,z839]),(0,[z2,z9,z3,z551,z5,z6]),(0,[z2,z3,z4,z12,z5,z1335]),(0,[z2,z856,z3,z34,z5,z6])],[(0,[z26,z1,z2,z3,z23,z6]),(0,[z8,z2,z3,z4,z5,z842]),(0,[z13,z2,z86,z12,z5,z6]),(0,[z2,z9,z3,z132,z5,z6]),(0,[z2,z3,z289,z12,z5,z278]),(0,[z2,z1235,z246,z12,z5,z6])],[(0,[z2,z3,z1573,z12,z5,z6]),(0,[z2,z1574,z3,z4,z5,z6])],[(0,[z8,z2,z3,z5,z604,z6])],[(0,[z298,z2,z3,z483,z5,z6]),(0,[z1,z9,z3,z15,z5,z6]),(0,[z2,z3,z12,z5,z902,z6])],[(0,[z523,z2,z86,z12,z5,z6])],[(0,[z2,z1575,z3,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z1576]),(0,[z976,z2,z3,z4,z12,z5])],[(0,[z2,z3,z4,z50,z24,z6]),(0,[z2,z513,z4,z12,z5,z585]),(0,[z2,z10,z85,z5,z42,z6]),(0,[z2,z4,z5,z42,z6,z964])],[(0,[z2,z3,z34,z132,z5,z6]),(0,[z2,z494,z52,z12,z5,z21])],[(0,[z2,z151,z4,z5,z42,z6]),(0,[z1,z2,z1431,z3,z5,z6])],[(0,[z199,z68,z4,z222,z5,z6]),(0,[z187,z2,z3,z658,z5,z6]),(0,[z2,z1367,z265,z12,z5,z6]),(0,[z2,z3,z4,z12,z5,z1105]),(0,[z2,z3,z161,z5,z42,z6])],[(0,[z1,z3,z34,z15,z5,z6]),(0,[z43,z2,z3,z4,z24,z6]),(0,[z863,z2,z9,z3,z5,z6])],[(0,[z441,z3,z4,z7,z5,z6]),(0,[z2,z3,z131,z12,z5,z6])],[(0,[z28,z254,z9,z12,z5,z6])],[(0,[z2,z3,z1577,z4,z5,z6]),(0,[z2,z3,z4,z5,z1578,z6]),(0,[z2,z1579,z3,z12,z5,z6]),(0,[z2,z3,z4,z141,z5,z388]),(0,[z2,z9,z459,z12,z5,z6]),(1,[z719,z3,z4,z5,z6])],[(0,[z2,z494,z124,z12,z5,z6]),(0,[z2,z36,z3,z37,z5,z6])],[(0,[z2,z934,z4,z12,z5,z6]),(0,[z8,z2,z3,z34,z23,z6]),(0,[z396,z93,z3,z4,z5,z6])],[(0,[z2,z3,z4,z1519,z5,z6]),(0,[z2,z813,z513,z12,z5,z6]),(0,[z2,z10,z3,z12,z5,z1376]),(0,[z1580,z2,z3,z4,z5,z6])],[(0,[z2,z9,z3,z777,z5,z6]),(0,[z2,z3,z4,z12,z5,z862]),(0,[z91,z2,z86,z12,z5,z6]),(0,[z2,z12,z5,z1531,z74,z6])],[(0,[z2,z1581,z3,z12,z5,z6]),(0,[z28,z2,z4,z12,z189,z6]),(0,[z254,z109,z4,z12,z5,z6])],[(0,[z43,z396,z3,z4,z5,z6])]],
   [[(0,[z9,z68,z58,z12,z5,z6]),(0,[z2,z3,z34,z12,z648,z6])],[(0,[z2,z3,z4,z236,z5,z585]),(0,[z2,z9,z12,z5,z337,z6]),(0,[z2,z3,z407,z12,z5,z88]),(0,[z2,z494,z34,z12,z5,z6])],[(0,[z440,z1,z3,z4,z5,z6]),(0,[z162,z3,z4,z12,z5,z6])],[(0,[z3,z4,z11,z5,z33,z6]),(0,[z231,z462,z3,z12,z5,z6]),(0,[z2,z9,z638,z12,z5,z6])],[(0,[z8,z3,z4,z5,z6,z256]),(0,[z2,z3,z4,z233,z42,z6]),(0,[z2,z3,z141,z5,z23,z17])],[(0,[z2,z59,z3,z12,z5,z6]),(0,[z2,z1582,z3,z12,z5,z6]),(0,[z3,z4,z141,z5,z17,z95])],[(0,[z2,z9,z3,z428,z5,z6]),(0,[z618,z1,z3,z4,z5,z6]),(0,[z2,z3,z1583,z12,z5,z6]),(0,[z2,z3,z4,z1584,z5,z6])],[(0,[z2,z3,z4,z1585,z5,z6]),(0,[z2,z9,z265,z12,z5,z6]),(0,[z396,z9,z3,z12,z5,z6])],[(0,[z1586,z2,z3,z4,z5,z6]),(0,[z2,z3,z230,z12,z65,z39])],[(0,[z2,z3,z4,z12,z5,z961]),(0,[z1,z2,z9,z19,z5,z6]),(0,[z1,z319,z3,z4,z5,z6]),(0,[z2,z1587,z3,z12,z5,z6])],[(0,[z2,z3,z12,z5,z1588,z6]),(0,[z1,z3,z4,z186,z5,z6]),(0,[z8,z2,z3,z564,z5,z6]),(0,[z2,z3,z12,z475,z5,z6])],[],[(0,[z57,z9,z58,z12,z5,z6]),(0,[z2,z86,z116,z12,z5,z6]),(0,[z396,z109,z3,z4,z5,z6]),(0,[z2,z4,z12,z5,z277,z29]),(0,[z2,z3,z4,z12,z803,z6])],[(0,[z2,z3,z34,z428,z5,z6])],[(0,[z199,z68,z581,z12,z5,z6]),(0,[z2,z3,z1383,z12,z5,z6]),(0,[z2,z3,z99,z16,z5,z6]),(0,[z396,z55,z3,z4,z5,z6]),(0,[z396,z3,z34,z12,z5,z6])],[(0,[z3,z4,z11,z918,z5,z6]),(0,[z1589,z3,z4,z12,z5,z6]),(0,[z2,z107,z3,z5,z42,z6])],[(0,[z2,z3,z5,z532,z23,z6]),(0,[z3,z34,z5,z159,z42,z6]),(0,[z2,z3,z52,z12,z5,z778]),(0,[z2,z3,z4,z16,z332,z6])],[(0,[z396,z3,z4,z5,z44,z6]),(0,[z2,z3,z4,z1532,z5,z6]),(0,[z396,z3,z4,z47,z5,z6])],[(0,[z8,z2,z362,z4,z5,z6])],[(0,[z2,z3,z1590,z12,z5,z6]),(0,[z2,z1591,z4,z12,z5,z6]),(0,[z1,z442,z3,z4,z5,z6]),(0,[z8,z2,z86,z3,z5,z6]),(0,[z2,z3,z113,z16,z5,z6])],[(0,[z8,z2,z3,z581,z5,z6]),(0,[z2,z3,z1592,z12,z5,z6]),(0,[z2,z265,z4,z186,z5,z6]),(0,[z28,z2,z9,z12,z119,z6])],[(0,[z2,z3,z4,z1593,z5,z6]),(0,[z787,z2,z3,z4,z5,z6])],[(0,[z1,z9,z3,z58,z5,z6]),(0,[z2,z3,z12,z5,z6,z1594]),(0,[z2,z3,z12,z23,z6,z412]),(0,[z2,z3,z1595,z12,z5,z6])],[(0,[z2,z10,z3,z5,z24,z6]),(0,[z2,z919,z4,z12,z5,z6])],[(0,[z2,z12,z757,z5,z23,z6]),(0,[z1216,z3,z4,z5,z42,z6])],[(0,[z2,z3,z4,z1596,z5,z6]),(0,[z2,z10,z3,z5,z33,z6])],[(0,[z2,z362,z34,z12,z5,z6]),(0,[z2,z3,z4,z5,z6,z1597])],[(0,[z1,z3,z253,z4,z5,z6]),(0,[z1,z2,z3,z5,z604,z6])],[(0,[z2,z3,z4,z5,z1598,z6]),(0,[z2,z1599,z3,z12,z5,z6])],[(0,[z150,z1,z3,z4,z5,z6]),(0,[z1,z324,z9,z3,z5,z6]),(0,[z2,z3,z4,z5,z117,z56]),(0,[z13,z3,z12,z5,z23,z14]),(0,[z2,z86,z16,z12,z5,z6]),(0,[z2,z3,z12,z5,z1600,z6])],[(0,[z1,z3,z4,z67,z5,z6]),(0,[z2,z3,z236,z5,z23,z6]),(0,[z25,z10,z3,z12,z15,z6])],[(0,[z2,z1601,z3,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 32 1024 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 469) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 469).take 455) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 924).take 452) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1376).take 387) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1763)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [469, 455, 452, 387] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 108).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 202).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 305).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 396).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 515).take 127).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 642).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 744).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc8 : chunkOK 5 ((bkB.flatten.drop 850).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc9 : chunkOK 5 ((bkB.flatten.drop 957).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 1024)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [108, 94, 103, 91, 119, 127, 102, 106, 107, 67] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_cons pc8 (windowsF_cons pc9 (windowsF_nil pcend))))))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 32) (nb2 := 1024) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38587

theorem PEqualNP.Outside.L_meta_38587 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4004031144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4004031144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38587.solve