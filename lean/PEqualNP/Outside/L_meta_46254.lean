import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46254

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277053568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0000085404626d80#64 ++ 0x44000010a808c4db#64 ++ 0x029018fc0ce7ffff#64 ++ 0xfa052031f819cfff#64 : BitVec 256),
   (0x0028633211291680#64 ++ 0x280050c66422522d#64 ++ 0x4568e73233391fee#64 ++ 0xf68ad1ce6466723f#64 : BitVec 256),
   (0x298b05c2c3c1a312#64 ++ 0xb053160b85878346#64 ++ 0xb98f07c3c3c1e3dd#64 ++ 0xaf731e0f878783c7#64 : BitVec 256),
   (0x560db8037c01d824#64 ++ 0xc0ac1b7006f803b0#64 ++ 0xfe0ff803fc01fc3b#64 ++ 0x9ffc1ff007f803f8#64 : BitVec 256),
   (0x1fd00001aa940047#64 ++ 0x003fa00003552800#64 ++ 0x3ff00003fffe0078#64 ++ 0x7e7fe00007fffc00#64 : BitVec 256),
   (0x1ff6d6a800000078#64 ++ 0x003fedad50000000#64 ++ 0xdffffffc00000007#64 ++ 0xffbffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0028632211091200 0x280050c644221224 0x4568e70233180000 0x048ad1ce04663000

def z1 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233391fee 0xf68ad1ce6466723f

def z2 : W := mkw 0x00286b76156b7f80 0x6c0050d6ec2ad6ff 0x47f8fffe3fffffff 0xfe8ff1fffc7fffff

def z3 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003fffe0078 0x7e7fe00007fffc00

def z4 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00000007 0xffbffffff8000000

def z5 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c1e3dd 0xaf731e0f878783c7

def z6 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc01fc3b 0x9ffc1ff007f803f8

def z7 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7ffff 0xfa052031f819cfff

def z8 : W := mkw 0x29ab67f2d3e9b792 0xb85356cfe5a7d36f 0xf98fe7f3c3c1ffdf 0xaff31fcfe78783ff

def z9 : W := mkw 0x0001000040008000 0x8000020000800100 0xb8070001c000e011 0x09700e00038001c0

def z10 : W := mkw 0x0009000240018000 0x8000120004800300 0x800f00000001e001 0x81001e00000003c0

def z11 : W := mkw 0x560db00378019024 0x80ac1b6006f00320 0xfc0fe003f001e019 0x8ff81fc007e003c0

def z12 : W := mkw 0x562dfa337c29dca4 0xc8ac5bf466f853b9 0xfe6ff833fc39fc3b 0xdffcdff067f873f8

def z13 : W := mkw 0x09fa67ba112916d8 0x2813f4cf7422522d 0x45f8e7fe33391fee 0xf68bf1cffc66723f

def z14 : W := mkw 0x1fd00011aab404c7 0x003fa00023556809 0x3ff00033ffff1ffe 0xfe7fe00067fffe3f

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000203000048 0x2602000004060000

def z16 : W := mkw 0x09d0000082940043 0x0013a00001052800 0x05f0000233fe0068 0x760be0000467fc00

def z17 : W := mkw 0x1674d22800000068 0x002ce9a450000000 0x4670f83c00000002 0x508ce1f078000000

def z18 : W := mkw 0x20090142c3c1a302 0xb040120285878346 0x20000003c3c1e3d8 0x00400000078783c7

def z19 : W := mkw 0x1fd90003ea958047 0x803fb20007d52b00 0xbfff0003ffffe079 0xff7ffe0007ffffc0

def z20 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc00ffffc00000007 0x81801ffff8000000

def z21 : W := mkw 0x1604900000000020 0x002c092000000000 0xde0ff80000000003 0x9fbc1ff000000000

def z22 : W := mkw 0x5ffffeab7c01d87c 0xc0bffffd56f803b0 0xfffffffffc01fc3f 0xfffffffffff803f8

def z23 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x000018fc0001ff87 0x80000031f80003ff

def z24 : W := mkw 0x1fd00855aef66dc7 0x443fa010ab5decdb 0x3ff018ffffffffff 0xfe7fe031ffffffff

def z25 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e732333803c4 0x648ad1ce64667007

def z26 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffffffe007f 0xfffffffffffffc00

def z27 : W := mkw 0x565db8037c15d865 0xc0acbb7006f82bb0 0xfe7ff803fc3ffc3b 0xdffcfff007f87ff8

def z28 : W := mkw 0x09890002c2818002 0x8013120005850300 0xb98f0003c3c1e059 0xaf731e00078783c0

def z29 : W := mkw 0x16500001aa940047 0x002ca00003552800 0x26700003fffe0078 0x504ce00007fffc00

def z30 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdfffe70000000000 0x7fbfffce00000000

def z31 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4008e73000011f86 0x808011ce6000023f

def z32 : W := mkw 0x1ff6d6a92800007c 0x003fedad52500000 0xfffffffffc00003f 0xfffffffffff80000

def z33 : W := mkw 0x0000000082940003 0x0000000001052800 0x0000000003fe0040 0x000000000007fc00

def z34 : W := mkw 0x5fdfbc8b7c01d87c 0xc0bfbf7916f803b0 0xfe9ff8cffc01fc3b 0x9ffd3ff19ff803f8

def z35 : W := mkw 0x200205c001402310 0x3040040b80028046 0x000007c000000384 0x0000000f80000007

def z36 : W := mkw 0x0000001000200480 0x0000000020004009 0x0000000000211fe8 0x000000000000423f

def z37 : W := mkw 0x3fdb05c3ebd5a357 0xb07fb60b87d7ab46 0xbfff07c3ffffe3fd 0xff7ffe0f87ffffc7

def z38 : W := mkw 0x09d0000082940043 0x0013a00001052800 0x01f0000003fe0040 0x6003e0000007fc00

def z39 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xc00ff8000001fc03 0x81801ff0000003f8

def z40 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdd6fe70000000000 0x05badfce00000000

def z41 : W := mkw 0x0006948800000038 0x00000d2910000000 0x800718cc00000001 0x01000e3198000000

def z42 : W := mkw 0x09a246a000000010 0x0013448d40000000 0xddefe7f000000007 0xffbbdfcfe0000000

def z43 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x008000c00ce7fffd 0xaa0100018019cfff

def z44 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc29ffffc00000007 0xfb853ffff8000000

def z45 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x009000fc00e603c4 0x60012001f801cc07

def z46 : W := mkw 0x560db00378019024 0x80ac1b6006f00320 0xfc0fe003f0000000 0x05f81fc007e00000

def z47 : W := mkw 0x1650000128140045 0x002ca00002502800 0x067000003c3e0020 0x500ce00000787c00

def z48 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0x800f07c00001e385 0x81001e0f800003c7

def z49 : W := mkw 0x0000004000402100 0x0000000080008042 0x029018fc00c1e3df 0xfa052031f80183c7

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000c00058 0x2a01000000018000

def z51 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e70233391fe8 0x048ad1ce0466723f

def z52 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f0703c3c1e3d8 0x05721e0e078783c7

def z53 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x009018fc00e7ffc7 0xe0012031f801cfff

def z54 : W := mkw 0x09f246a800000058 0x0013e48d50000000 0x01f007fc00000004 0x6003e00ff8000000

def z55 : W := mkw 0x400928037c01d804 0xc080125006f803b0 0x20000003fc01fc38 0x0040000007f803f8

def z56 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3d600003f3180000 0x047ac00007e63000

def z57 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018cc0ce7fff9 0x080520319819cfff

def z58 : W := mkw 0x5ffffeabfe95d87f 0xc0bffffd57fd2bb0 0xfffffffffffffc7f 0xfffffffffffffff8

def z59 : W := mkw 0x0000000128140005 0x0000000002502800 0x000000003c3e0020 0x0000000000787c00

def z60 : W := mkw 0x3fdb05c3ebd5a357 0xb07fb60b87d7ab46 0xbb9f07c3cfc7e3dd 0xaf773e0f879f8fc7

def z61 : W := mkw 0x298205c083c02312 0x3053040b81078046 0x018007c003c003c4 0x2003000f80078007

def z62 : W := mkw 0x5fddb803fe95d867 0xc0bfbb7007fd2bb0 0xfffff803fffffc7b 0xfffffff007fffff8

def z63 : W := mkw 0x567dfa2b7c01d86c 0xc0acfbf456f803b0 0xfe7ff83ffc01fc3b 0xdffcfff07ff803f8

def z64 : W := mkw 0x1650000128140045 0x002ca00002502800 0x0460000030180000 0x0008c00000603000

def z65 : W := mkw 0x1ffef7ba112916f8 0x283ffdef7422522d 0xdffffffe33391fef 0xffbffffffc66723f

def z66 : W := mkw 0x0008200210011000 0x0000104004200220 0x0000000230011c28 0x0000000004600238

def z67 : W := mkw 0x698fbdc2d7c1fb32 0xf0d31f7b85af83f6 0xf98fffc3c3c1ffdf 0xaff31fff878783ff

def z68 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0x47f0fffc00000006 0x708fe1fff8000000

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z70 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0ff803f001fc03 0x85f81ff007e003f8

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x0560000233380068 0x760ac00004667000

def z72 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffe3338006f 0xffbffffffc667000

def z73 : W := mkw 0x3ffff7fad3e9b7fa 0xb87fffeff5a7d36f 0xfffffffff3f9ffff 0xffffffffffe7f3ff

def z74 : W := mkw 0x5624fa313c285ca4 0x48ac49f4627850b9 0x4660f8303c381c22 0x508cc1f060787038

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0x029000000ce60078 0x7a0520000019cc00

def z76 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f07c3c301e385 0x85721e0f878603c7

def z77 : W := mkw 0x0980004082c02102 0x0013000081058042 0x398000c3c3c1e3dd 0xae730001878783c7

def z78 : W := mkw 0x20090102c3818202 0xb040120205870304 0x20000003c3000000 0x0040000007860000

def z79 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3b900003cfc60058 0x2e772000079f8c00

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0x38000003c0000018 0x0e70000007800000

def z81 : W := mkw 0x5fddb003fa959067 0x80bfbb6007f52b20 0xfd6fe003f3180000 0x05fadfc007e63000

def z82 : W := mkw 0x1fd20481aa940057 0x003fa40903552800 0xbfff07c3fffe007d 0xff7ffe0f87fffc00

def z83 : W := mkw 0x3fdb05c3ebd5a357 0xb07fb60b87d7ab46 0xbdef07c3f3d9e3dd 0xaf7bde0f87e7b3c7

def z84 : W := mkw 0x0020433001280680 0x280040866002500d 0x01600730033803c4 0x6002c00e60067007

def z85 : W := mkw 0x1ff246a800000058 0x003fe48d50000000 0x1ff007fc00000004 0x7e3fe00ff8000000

def z86 : W := mkw 0x00000855aef66d87 0x44000010ab5decdb 0x20000003fffffff8 0x0040000007ffffff

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0x029018fc00000007 0xfa052031f8000000

def z88 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe9ff8fffc01fc3f 0xfffd3ff1fff803f8

def z89 : W := mkw 0x00286b36152b5e80 0x6c0050d66c2a56bd 0x4778ff3e3f3f1fee 0xf68ef1fe7c7e7e3f

def z90 : W := mkw 0x298b0582c3818212 0xb053160b05870304 0xb90f0703c3000000 0x05721e0e07860000

def z91 : W := mkw 0x29ab67f2d3e9b792 0xb85356cfe5a7d36f 0xfdefe7f3f3f9ffff 0xfffbdfcfe7e7f3ff

def z92 : W := mkw 0x0980000082800002 0x0013000001050000 0x39800003c3c00058 0x2e73000007878000

def z93 : W := mkw 0x1ff6d6a88280007a 0x003fedad51050000 0xffffffffc3c0005f 0xffffffffff878000

def z94 : W := mkw 0x1600000128000004 0x002c000002500000 0x060000003c000020 0x100c000000780000

def z95 : W := mkw 0x5654b8013c145865 0x40aca970027828b0 0x4670f8003c3e1c22 0x508ce1f000787c38

def z96 : W := mkw 0x0000084404426900 0x44000010880884d2 0x029018cc0cc6e011 0x0805203198198dc0

def z97 : W := mkw 0x298b0dd6c7e3ef92 0xf453161bad8fc7df 0xbb9f1fffcfe7ffff 0xff773e3fff9fcfff

def z98 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbdef07c3f3f9e3fd 0xff7bde0f87e7f3c7

def z99 : W := mkw 0x1ff86333bbbd16c7 0x283ff0c667777a2d 0x7ff8e733ffff1ffe 0xfefff1ce67fffe3f

def z100 : W := mkw 0x00204a7404626d80 0x44004094e808c4db 0x47f8fffc0ce7ffff 0xfe8ff1fff819cfff

def z101 : W := mkw 0x09d0000000000040 0x0013a00000000000 0x01f0000000000000 0x6003e00000000000

def z102 : W := mkw 0x00286333bbbd1687 0x280050c667777a2d 0x6568e733ffff1ffe 0xf6cad1ce67fffe3f

def z103 : W := mkw 0x0009000240018000 0x8000120004800300 0xb80f0003c001e019 0x8f701e00078003c0

def z104 : W := mkw 0x7f8fbdc3ffc1fb36 0xf0ff1f7b87ff83f6 0xff8fffc3ffc1ffff 0xbfff1fff87ff83ff

def z105 : W := mkw 0x3fd205c1abd42357 0x307fa40b8357a846 0x3ff007c3fffe03fc 0x7e7fe00f87fffc07

def z106 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdd6ffffc00000007 0x85badffff8000000

def z107 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff000000ce60078 0x7e3fe0000019cc00

def z108 : W := mkw 0x20090142c3c1a302 0xb040120285878346 0x208000c3c3c1e3dd 0xaa410001878783c7

def z109 : W := mkw 0x1fd69489aa94007f 0x003fad2913552800 0xbff718cffffe0079 0x7f7fee319ffffc00

def z110 : W := mkw 0x0029633251299680 0xa80052c664a2532d 0xfd6fe733f339ffff 0xfffadfce67e673ff

def z111 : W := mkw 0x1fd69ccc04426978 0x443fad39980884d2 0x9a9718cc0cc6e011 0x09352e3198198dc0

def z112 : W := mkw 0x0000080004004800 0x4000001000080090 0x020018000c01fc3b 0x9a040030001803f8

def z113 : W := mkw 0x0008200210011000 0x0000104004200220 0x4408e00230011c2a 0x968811c004600238

def z114 : W := mkw 0x298305c0c3c0a312 0xb053060b81878146 0xb98707c1c3c0e3d5 0x29730e0f838781c7

def z115 : W := mkw 0x1600000128000004 0x002c000002500000 0x3f600003ff380078 0x7e7ec00007fe7000

def z116 : W := mkw 0x5604b8013c005824 0x40ac0970027800b0 0x4600f8003c001c22 0x108c01f000780038

def z117 : W := mkw 0x562dfb337d29dea4 0xe8ac5bf666fa53bd 0xff6fff33ff39ffff 0xfffedffe67fe73ff

def z118 : W := mkw 0x1ff6deec04426978 0x443fedbdd80884d2 0xdffffffc0cc6e017 0xffbffffff8198dc0

def z119 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc0ce6007f 0xffbffffff819cc00

def z120 : W := mkw 0x0008010201010200 0x2000100204020204 0x0008070000010384 0x8000100e00000207

def z121 : W := mkw 0x400108016c00c804 0xc080021002d80190 0x20000001cc00e010 0x00400000039801c0

def z122 : W := mkw 0x1fd82113bbbd16c7 0x283fb04227777a2d 0x3ff00003ffff1ff8 0x7e7fe00007fffe3f

def z123 : W := mkw 0x0008010201010200 0x2000100204020204 0x01080702030103cc 0xa602100e04060207

def z124 : W := mkw 0x1ff06231babc14c7 0x083fe0c463757829 0x7ff0e033fffe1c7a 0x7effe1c067fffc38

def z125 : W := mkw 0x0982048082800012 0x0013040901050000 0xb98f07c3c3c0005d 0xaf731e0f87878000

def z126 : W := mkw 0x0980000082800002 0x0013000001050000 0x0180000003c00040 0x2003000000078000

def z127 : W := mkw 0x1ff6d6a92814007d 0x003fedad52502800 0xdffffffc3c3e0027 0xffbffffff8787c00

def z128 : W := mkw 0x09f6d6a800000078 0x0013edad50000000 0xc1fffffc00000007 0xe183fffff8000000

def z129 : W := mkw 0x0028622210011000 0x000050c444200220 0x4568e73230011c2e 0xf68ad1ce64600238

def z130 : W := mkw 0x0000001000200480 0x0000000020004009 0x0560003233391fee 0xf60ac0006466723f

def z131 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3a900001ccc60010 0x0875200003998c00

def z132 : W := mkw 0x1650000000000040 0x002ca00000000000 0x0670000000000000 0x500ce00000000000

def z133 : W := mkw 0x0026defc04626db8 0x44004dbdf808c4db 0xc29ffffc0ce7ffff 0xfb853ffff819cfff

def z134 : W := mkw 0x5f8fbc837c01d834 0xc0bf1f7906f803b0 0xff8fffc3fc01fc3f 0xbfff1fff87f803f8

def z135 : W := mkw 0x5674fa293c00586c 0x40ace9f4527800b0 0x4670f83c3c001c22 0x508ce1f078780038

def z136 : W := mkw 0x20090956c7e3ef82 0xf4401212ad8fc7df 0x20000003cfe7fff8 0x00400000079fcfff

def z137 : W := mkw 0x00286b3215295e80 0x680050d6642a52bd 0x4768ff323f39ffff 0xfe8ed1fe647e73ff

def z138 : W := mkw 0x0002048000000010 0x0000040900000000 0x800f07c000000005 0x81001e0f80000000

def z139 : W := mkw 0x3fd90143ebd5a347 0xb07fb20287d7ab46 0x3ff00003ffffe3f8 0x7e7fe00007ffffc7

def z140 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233191f86 0x848ad1ce6466323f

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000233380068 0x0000000004667000

def z142 : W := mkw 0x00286b76156b7f80 0x6c0050d6ec2ad6ff 0x4298fffc0ce7ffff 0xfa8531fff819cfff

def z143 : W := mkw 0x1600000000000000 0x002c000000000000 0x1e00000000000000 0x1e3c000000000000

def z144 : W := mkw 0x3fffd7eac3c1a37a 0xb07fffafd5878346 0xffffffffc3c1e3df 0xffffffffff8783c7

def z145 : W := mkw 0x1676d6a800000078 0x002cedad50000000 0xc67ffffc00000007 0xd18cfffff8000000

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000011c2a 0x9200000000000238

def z147 : W := mkw 0x1600000128000004 0x002c000002500000 0x3e000003fc000038 0x1e7c000007f80000

def z148 : W := mkw 0x560db00378019024 0x80ac1b6006f00320 0xfe0fe003fc000038 0x1ffc1fc007f80000

def z149 : W := mkw 0x1fd6948800000078 0x003fad2910000000 0x9a9718cc00000001 0x09352e3198000000

def z150 : W := mkw 0x562dfa237c01d824 0xc0ac5bf446f803b0 0xff6fff33fc01fc3f 0xfffedffe67f803f8

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000ce60078 0x000000000019cc00

def z152 : W := mkw 0x1626d6a800000038 0x002c4dad50000000 0xde0ffffc00000007 0x9fbc1ffff8000000

def z153 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x07f018fe3fffffff 0xfe0fe031fc7fffff

def z154 : W := mkw 0x0982048000000010 0x0013040900000000 0x998f07c000000005 0xaf331e0f80000000

def z155 : W := mkw 0x5ffffeff7c63fdfc 0xc4bffffdfef8c7fb 0xfffffffffce7ffff 0xfffffffffff9cfff

def z156 : W := mkw 0x0000084404426900 0x44000010880884d2 0x029018cc0cc7fc3b 0x9a05203198198ff8

def z157 : W := mkw 0x0008011201210680 0x200010022402420d 0x0108073203211fee 0xf602100e6406423f

def z158 : W := mkw 0x298b05d6c3e3a792 0xb453160bad87c74f 0xb99f07ffc3e7e3dd 0xef733e0fff87cfc7

def z159 : W := mkw 0x298b25c2d3c1b312 0xb053164b85a78366 0xfd8fe7c3f3c1ffff 0xbffb1fcf87e783ff

def z160 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4468e73030391fa6 0xd088d1ce6060723f

def z161 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0x818f07c003c1e3c5 0xa1031e0f800783c7

def z162 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4460e03233391fea 0x5088c1c06466723f

def z163 : W := mkw 0x0020433001280680 0x280040866002500d 0x4568e730033803c6 0xf68ad1ce60067007

def z164 : W := mkw 0x00082956156b7f80 0x6c001052ac2ad6ff 0x000000023ffffff8 0x00000000047fffff

def z165 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xf80ff803c001fc1b 0x8ff01ff0078003f8

def z166 : W := mkw 0x160d900240018020 0x802c1b2004800300 0xfe0ff803c001e01b 0x9ffc1ff0078003c0

def z167 : W := mkw 0x560598016c00c824 0xc0ac0b3002d80190 0xba071801cc01fc3b 0x9b740e30039803f8

def z168 : W := mkw 0x002ef7ba112916b8 0x28005def7422522d 0xc56ffffe33391fef 0xf78adffffc66723f

def z169 : W := mkw 0x00206a34142a5c80 0x4c0040d4682854b9 0x4670f83c3c3e1c22 0x508ce1f078787c38

def z170 : W := mkw 0x560598016c00c824 0xc0ac0b3002d80190 0xfe0ff801cc00e013 0x9ffc1ff0039801c0

def z171 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff0000000000000 0x7e3fe00000000000

def z172 : W := mkw 0x1604985404626da0 0x442c0930a808c4db 0xde9ff8fc0ce7ffff 0xffbd3ff1f819cfff

def z173 : W := mkw 0x09d00001aa940047 0x0013a00003552800 0x21f00003fffe0078 0x6043e00007fffc00

def z174 : W := mkw 0x0008211211291680 0x280010422422522d 0x0000000233391fe8 0x000000000466723f

def z175 : W := mkw 0x1fd6948800000078 0x003fad2910000000 0x9b9f1fcc00000005 0xaf373e3f98000000

def z176 : W := mkw 0x00000001aa940007 0x0000000003552800 0x20000003fffe0078 0x0040000007fffc00

def z177 : W := mkw 0x1ff6d6a88294007b 0x003fedad51052800 0xdffffffc03fe0047 0xffbffffff807fc00

def z178 : W := mkw 0x20296372d3e9b782 0xb84052c6e5a7d36f 0x6568e733f3f9fffe 0xf6cad1ce67e7f3ff

def z179 : W := mkw 0x0020633011281680 0x280040c66022502d 0x4560e73033381fe6 0x708ac1ce6066703f

def z180 : W := mkw 0x5605900168008024 0x80ac0b2002d00100 0xb8070001c0000000 0x01700e0003800000

def z181 : W := mkw 0x60092943ffc1fb06 0xf0c0125287ff83f6 0x20000003ffc1fff8 0x0040000007ff83ff

def z182 : W := mkw 0x0000081404224c80 0x4400001028084499 0x0210183c0c27fc3b 0xda04203078184ff8

def z183 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3d600003fffe0078 0x047ac00007fffc00

def z184 : W := mkw 0x20092152d3e9b782 0xb8401242a5a7d36f 0x20000003f3f9fff8 0x0040000007e7f3ff

def z185 : W := mkw 0x160008012c004804 0x402c001002580090 0x3e001803fc01fc3b 0x9e7c003007f803f8

def z186 : W := mkw 0x1600000128000004 0x002c000002500000 0x3c000003f0000000 0x0478000007e00000

def z187 : W := mkw 0x560598016c00c824 0xc0ac0b3002d80190 0xba071801cc00e011 0x09740e30039801c0

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x029018fc0ce6007f 0xfa052031f819cc00

def z189 : W := mkw 0x29830480c2808012 0x9053060901850100 0xb8070001c0000000 0x01700e0003800000

def z190 : W := mkw 0x0000080004004800 0x4000001000080090 0x020018000c00e011 0x08040030001801c0

def z191 : W := mkw 0x298b04c2c2c1a112 0x9053160985858342 0xb88f00c3c0c1e019 0x8f711e01878183c0

def z192 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdfffffcc00000001 0x0dbfffff98000000

def z193 : W := mkw 0x000900424041a100 0x8000120084808342 0xb88f00c3c0c1e3dd 0xaf711e01878183c7

def z194 : W := mkw 0x5ffdfb33ffbddee7 0xe8bffbf667ff7bbd 0xffffff33ffffffff 0xfffffffe67ffffff

def z195 : W := mkw 0x09d0000082940043 0x0013a00001052800 0x0160000003180000 0x0002c00000063000

def z196 : W := mkw 0x0980000082800002 0x0013000001050000 0x38800001c0c00010 0x0871000003818000

def z197 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000103cc 0xa200000000000207

def z198 : W := mkw 0x0000081404224c80 0x4400001028084499 0x0210183c0c261c22 0x5004203078184c38

def z199 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xda9ffffc00000007 0x89b53ffff8000000

def z200 : W := mkw 0x298304c0c2c0a112 0x9053060981858142 0xb98f07c1c0c0e015 0xaf731e0f838181c0

def z201 : W := mkw 0x3ff7d6e8c2c0a17a 0x907fefadd1858142 0xfffffffdc0c0e017 0xfffffffffb8181c0

def z202 : W := mkw 0x1fd6948800000078 0x003fad2910000000 0xde9ff8cc00000003 0x9fbd3ff198000000

def z203 : W := mkw 0x298304c0c2c0a112 0x9053060981858142 0xb98700c3c3c0e059 0x2f730e01878781c0

def z204 : W := mkw 0x298304c0c2c0a112 0x9053060981858142 0xb88700c1c0c0e011 0x09710e01838181c0

def z205 : W := mkw 0x0000000128000004 0x0000000002500000 0x20000003fc000038 0x0040000007f80000

def z206 : W := mkw 0x5604b8553c627da4 0x44ac0970aa78c4fb 0x4690f8fc3ce7ffff 0xfa8d21f1f879cfff

def z207 : W := mkw 0x0000001000200480 0x0000000020004009 0x0000003000211fee 0xf20000006000423f

def z208 : W := mkw 0x298304c0c2c0a112 0x9053060981858142 0xb88700c1c0c1e3dd 0xab710e01838183c7

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000c000000005 0xaa01000180000000

def z210 : W := mkw 0x560db8577c63fda4 0xc4ac1b70aef8c7fb 0xfe9ff8fffce7ffff 0xfffd3ff1fff9cfff

def z211 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x000018fc0021ffef 0xf2000031f80043ff

def z212 : W := mkw 0x5fffffbb7d29defc 0xe8bfffff76fa53bd 0xffffffffff39ffff 0xfffffffffffe73ff

def z213 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x000000300ce7fffe 0xf20000006019cfff

def z214 : W := mkw 0x002246a800000018 0x0000448d50000000 0x000007fc00000004 0x0000000ff8000000

def z215 : W := mkw 0x0000001000200480 0x0000000020004009 0x0000003000201c22 0x5000000060004038

def z216 : W := mkw 0x1604900128000024 0x002c092002500000 0xfe0ff803fc00003b 0x9ffc1ff007f80000

def z217 : W := mkw 0x1f86948000000030 0x003f0d2900000000 0xdf8fffc000000007 0xbfbf1fff80000000

def z218 : W := mkw 0x0000084404426900 0x44000010880884d2 0x029018cc0cc7e3dd 0xaa05203198198fc7

def z219 : W := mkw 0x298b05c24141a310 0xb053160b84828346 0x998f07c00001e385 0xaf331e0f800003c7

def z220 : W := mkw 0x29820dd487e26f92 0x7453041ba90fc4df 0x03901ffc0fe7ffff 0xfa07203ff81fcfff

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x029000000cc60010 0x0805200000198c00

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x029018cc00000001 0x0805203198000000

def z223 : W := mkw 0x0020422000000000 0x0000408440000000 0x4008e73000000006 0x808011ce60000000

def z224 : W := mkw 0x160cb00210011020 0x002c196004200220 0xde0ff80230011c2b 0x9fbc1ff004600238

def z225 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3e900003fcc60038 0x1e7d200007f98c00

def z226 : W := mkw 0x1fd2048000000050 0x003fa40900000000 0x9fff07c000000005 0xff3ffe0f80000000

def z227 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x0210183c0ce7fffa 0x500420307819cfff

def z228 : W := mkw 0x09f246a800000058 0x0013e48d50000000 0x0160070000000000 0x0002c00e00000000

def z229 : W := mkw 0x0020422000000000 0x0000408440000000 0x0160073000000004 0x6002c00e60000000

def z230 : W := mkw 0x09a6d6a800000038 0x00134dad50000000 0xd98ffffc00000007 0xafb31ffff8000000

def z231 : W := mkw 0x167cf33a112916e8 0x282cf9e67422522d 0x4778ff3e33391fee 0xf68ef1fe7c66723f

def z232 : W := mkw 0x0008280214015800 0x40001050042802b0 0x4608f8023c01fc3b 0x9e8c11f0047803f8

def z233 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffdccc60017 0xfffffffffb998c00

def z234 : W := mkw 0x00082956156b7f80 0x6c001052ac2ad6ff 0x029018fe3fffffff 0xfa052031fc7fffff

def z235 : W := mkw 0x09d2048800000058 0x0013a40910000000 0x009000cc00000000 0x0001200198000000

def z236 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc00fe70000000000 0x01801fce00000000

def z237 : W := mkw 0x1ff6d6fc006225f8 0x043fedadf800c44b 0xdffffffc00e603c7 0xffbffffff801cc07

def z238 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xff6ff803ff39fc7b 0xfffedff007fe73f8

def z239 : W := mkw 0x3fffd7ea4141a378 0xb07fffafd4828346 0xdffffffc0001e387 0xffbffffff80003c7

def z240 : W := mkw 0x09f0433083bc06c3 0x2813e0866107780d 0x01f0073003fe03c4 0x6003e00e6007fc07

def z241 : W := mkw 0x1604900000000020 0x002c092000000000 0x4600f80000000002 0x108c01f000000000

def z242 : W := mkw 0x1fd6948800000078 0x003fad2910000000 0x9ff718cc00000001 0x7f3fee3198000000

def z243 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x009000fc00e71fee 0xf2012001f801ce3f

def z244 : W := mkw 0x5fd92803fe95d847 0xc0bfb25007fd2bb0 0x3ff00003fffffc78 0x7e7fe00007fffff8

def z245 : W := mkw 0x0020423000200480 0x0000408460004009 0x4568e73000211fee 0xf68ad1ce6000423f

def z246 : W := mkw 0x1608200338011004 0x002c104006700220 0x7e08e003fc011c3a 0x9efc11c007f80238

def z247 : W := mkw 0x0009200250019000 0x8000124004a00320 0xfc0fe003f001fc3b 0x9ff81fc007e003f8

def z248 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb88f07c1c0c1e395 0x89711e0f838183c7

def z249 : W := mkw 0x1ffef7bbbbbd16ff 0x283ffdef77777a2d 0xffffffffffff1fff 0xfffffffffffffe3f

def z250 : W := mkw 0x09f246a800000058 0x0013e48d50000000 0x99ff07fc00000005 0xef33fe0ff8000000

def z251 : W := mkw 0x298b0582c3818212 0xb053160b05870304 0xb90f0703c30103cc 0xa7721e0e07860207

def z252 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfa0ff801cc01fc13 0x89f41ff0039803f8

def z253 : W := mkw 0x3f8b05c3ebc1a316 0xb07f160b87d78346 0xbf8f07c3ffc1e3fd 0xbf7f1e0f87ff83c7

def z254 : W := mkw 0x3fffd7eac3c1a37a 0xb07fffafd5878346 0xfdefe7c3c3c1e3dd 0xaffbdfcf878783c7

def z255 : W := mkw 0x0000004000402100 0x0000000080008042 0x008000c000c003c4 0x2001000180018007

def z256 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc56ffffc00000007 0xf78adffff8000000

def z257 : W := mkw 0x0008000200010000 0x0000100004000200 0x0008000200010008 0x8600100004000200

def z258 : W := mkw 0x1624d22000000020 0x002c49a440000000 0xdf6fff3000000007 0xffbedffe60000000

def z259 : W := mkw 0x560db8577c63fda4 0xc4ac1b70aef8c7fb 0xfe0ff8fffc01ffbf 0x9ffc1ff1fff803ff

def z260 : W := mkw 0x1fd49001aa940067 0x003fa92003552800 0xfffff803fffe007b 0xfffffff007fffc00

def z261 : W := mkw 0x400928577c63fd84 0xc4801250aef8c7fb 0x229018fffce7ffff 0xfa452031fff9cfff

def z262 : W := mkw 0x3f8f95c2c3c1a332 0xb07f1f2b85878346 0xff8fffc3c3c1e3df 0xbfff1fff878783c7

def z263 : W := mkw 0x400db8037c01d824 0xc0801b7006f803b0 0xe00ff803fc01fc3b 0x81c01ff007f803f8

def z264 : W := mkw 0x29aa67f293e93792 0x385354cfe527d26f 0x45e8e7f233f91fee 0xf68bd1cfe467f23f

def z265 : W := mkw 0x0980000082800002 0x0013000001050000 0x3de00003f3f80078 0x7e7bc00007e7f000

def z266 : W := mkw 0x5fd59801ee94c867 0xc0bfab3003dd2990 0xbff71803fffee079 0x7f7fee3007fffdc0

def z267 : W := mkw 0x0070422800000048 0x0000e08450000000 0x0070003c00000000 0x4000e00078000000

def z268 : W := mkw 0x0028632211091200 0x280050c644221224 0x4568e702331903cc 0xa68ad1ce04663207

def z269 : W := mkw 0x002ef7ba112916b8 0x28005def7422522d 0xc00ffffc00011f87 0x81801ffff800023f

def z270 : W := mkw 0x00000001aa940007 0x0000000003552800 0x25600003fffe0078 0x764ac00007fffc00

def z271 : W := mkw 0x0008010201010200 0x2000100204020204 0x05680702333903ec 0xf60ad00e04667207

def z272 : W := mkw 0x0000001000200480 0x0000000020004009 0x00000030002003c4 0x6000000060004007

def z273 : W := mkw 0x16786333393d16c5 0x282cf0c666727a2d 0x4778e7323f3f1fee 0xf68ef1ce647e7e3f

def z274 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0x6600f803fc01fc3a 0x10cc01f007f803f8

def z275 : W := mkw 0x0008211211291680 0x280010422422522d 0x0108070233391fec 0xa602100e0466723f

def z276 : W := mkw 0x0020422000000000 0x0000408440000000 0x4568e73000000006 0xf68ad1ce60000000

def z277 : W := mkw 0x200901424141a300 0xb040120284828346 0x000000000001e380 0x00000000000003c7

def z278 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0001ff87 0xfa052031f80003ff

def z279 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029000000ce7fff8 0x7a0520000019cfff

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0x980f000000000001 0x8f301e0000000000

def z281 : W := mkw 0x29f247e883c0235a 0x3053e48fd1078046 0x01f007fc03c003c4 0x6003e00ff8078007

def z282 : W := mkw 0x3fdb0dd7eff7efd7 0xf47fb61bafdfefdf 0xbfff1fffffffffff 0xff7ffe3fffffffff

def z283 : W := mkw 0x0009000240018000 0x8000120004800300 0xb80f0003c0000000 0x05701e0007800000

def z284 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce6e3d5 0x68052031f819cdc7

def z285 : W := mkw 0x560db9037d01da24 0xe0ac1b7206fa03b4 0xff0fff03ff01ffff 0xbffe1ffe07fe03ff

def z286 : W := mkw 0x0000200010001000 0x0000004000200020 0x4400e00030001c22 0x108801c000600038

def z287 : W := mkw 0x1ff04331abbc06c7 0x283fe0866357780d 0x3ff00733fffe03fc 0x7e7fe00e67fffc07

def z288 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x000018fc0ce7ffff 0x80000031f819cfff

def z289 : W := mkw 0x5604b8013c005824 0x40ac0970027800b0 0x7e00f803fc001c3a 0x1efc01f007f80038

def z290 : W := mkw 0x0028623210291480 0x080050c464205229 0x4468e03230391c2a 0xd688d1c064607238

def z291 : W := mkw 0x3fffd7aac381827a 0xb07fffaf55870304 0xffffffffc3000007 0xffffffffff860000

def z292 : W := mkw 0x202b67f25169b790 0xb84056cfe4a2d36f 0xc56fe7f23339ffef 0xf78adfcfe46673ff

def z293 : W := mkw 0x0008201210211480 0x0000104024204229 0x4408e03230211fee 0xf68811c06460423f

def z294 : W := mkw 0x0980000082800002 0x0013000001050000 0x39000003c3000000 0x0472000007860000

def z295 : W := mkw 0x09f246a800000058 0x0013e48d50000000 0x03f01ffc00000007 0xfa07e03ff8000000

def z296 : W := mkw 0x00206a74146a7d80 0x4c0040d4e828d4fb 0x46f0f8fc3cffffff 0xfa8de1f1f879ffff

def z297 : W := mkw 0x0008200210011000 0x0000104004200220 0x4008e00000011c02 0x808011c000000238

def z298 : W := mkw 0x560598016c00c824 0xc0ac0b3002d80190 0xbe071803fc00e039 0x1f7c0e3007f801c0

def z299 : W := mkw 0x165008552c766dc5 0x442ca010aa58ecdb 0x06f018fc3cffffff 0xfa0de031f879ffff

def z300 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4008e73000211fee 0xf28011ce6000423f

def z301 : W := mkw 0x0020623010281480 0x080040c460205029 0x4460e03030381c22 0x5088c1c060607038

def z302 : W := mkw 0x3fdb0583eb958257 0xb07fb60b07d72b04 0xbfff0703fffe0078 0x7f7ffe0e07fffc00

def z303 : W := mkw 0x29a247f083e82792 0x3853448fe107d04f 0x01e007f003f803c4 0x6003c00fe007f007

def z304 : W := mkw 0x560db803fe95d827 0xc0ac1b7007fd2bb0 0xfe0ff803fffffc7b 0x9ffc1ff007fffff8

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x000018fc00000007 0x80000031f8000000

def z306 : W := mkw 0x560db8477c43f924 0xc4ac1b708ef887f2 0xfe9ff8cffcc7fc3b 0x9ffd3ff19ff98ff8

def z307 : W := mkw 0x1ff6defc04626df8 0x443fedbdf808c4db 0xdffffffc0ce7ffff 0xffbffffff819cfff

def z308 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3bf00001cffe0050 0x6877e000039ffc00

def z309 : W := mkw 0x5fddb8037c01d864 0xc0bfbb7006f803b0 0xfffff803fc01fc3b 0xfffffff007f803f8

def z310 : W := mkw 0x1ff6debc04224cf8 0x443fedbd78084499 0xdffffffc0c261c27 0xffbffffff8184c38

def z311 : W := mkw 0x29ab47e2c3c1a312 0xb053568fc5878346 0xfdefe7f3c3c1e3df 0xfffbdfcfe78783c7

def z312 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xffffe703fffe0078 0x7fffffce07fffc00

def z313 : W := mkw 0x298b0dc2c7c1eb12 0xf053161b858f83d6 0xbb8f1fc3cfc1ffff 0xbf771e3f879f83ff

def z314 : W := mkw 0x5605b8017c00d824 0xc0ac0b7002f801b0 0xfe07f801fc00fc33 0x19fc0ff003f801f8

def z315 : W := mkw 0x29830cd4c6e2ed92 0xd4530619a98dc5db 0xba9718fdcce7ffff 0xfb752e31fb99cfff

def z316 : W := mkw 0x400928025401d800 0xc080125004a803b0 0x000000000001fc00 0x00000000000003f8

def z317 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffff3180007 0xffffffffffe63000

def z318 : W := mkw 0x298b0582c3818212 0xb053160b05870304 0xb90f0703c301e019 0x8f721e0e078603c0

def z319 : W := mkw 0x0980000000000000 0x0013000000000000 0x1980000000000000 0x2e33000000000000

def z320 : W := mkw 0x760fbdc37d41fb34 0xf0ec1f7b86fa83f6 0xfe0fffc3fc01ffbf 0x9ffc1fff87f803ff

def z321 : W := mkw 0x3ff6d7e883c0237a 0x307fedafd1078046 0xdffffffc03c003c7 0xffbffffff8078007

def z322 : W := mkw 0x0008010201010200 0x2000100204020204 0x00000002030103c8 0x0000000004060207

def z323 : W := mkw 0x0008200210011000 0x0000104004200220 0x4408e00230000000 0x048811c004600000

def z324 : W := mkw 0x3fffd7ebebd5a37f 0xb07fffafd7d7ab46 0xffffffffffffe3ff 0xffffffffffffffc7

def z325 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0fe003fc01fc38 0x05f81fc007f803f8

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000003000000006 0xf200000060000000

def z327 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0x9bf71ffc00000005 0x6937ee3ff8000000

def z328 : W := mkw 0x29ab6ff6d7ebff92 0xfc5356dfedafd7ff 0xffffffffffffffff 0xffffffffffffffff

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000000c000038 0x1a04000000180000

def z330 : W := mkw 0x1ffed7aa01010278 0x203ffdaf54020204 0xdffffffe030103cf 0xffbffffffc060207

def z331 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x021018fc0c27ffa7 0xd0042031f8184fff

def z332 : W := mkw 0x1fd6948800000078 0x003fad2910000000 0x9a9718fc00000007 0xfb352e31f8000000

def z333 : W := mkw 0x0000081404224c80 0x4400001028084499 0x000000000c261c20 0x0000000000184c38

def z334 : W := mkw 0x560db8177c23dca4 0xc4ac1b702ef847b9 0xfe1ff83ffc27fc3b 0xdffc3ff07ff84ff8

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x0210183c00000002 0x5004203078000000

def z336 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0cc7ff97 0x88052031f8198fff

def z337 : W := mkw 0x1674d22800000068 0x002ce9a450000000 0x4460e00000000000 0x0088c1c000000000

def z338 : W := mkw 0x0000084404426900 0x44000010880884d2 0x029018fc0cc6e017 0xfa052031f8198dc0

def z339 : W := mkw 0x0050000000140041 0x0000a00000002800 0x00700000003e0000 0x4000e00000007c00

def z340 : W := mkw 0x29db05c2c3d5a353 0xb053b60b8587ab46 0xb9ff07c3c3ffe3dd 0xef73fe0f8787ffc7

def z341 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1a90000000000000 0x0835200000000000

def z342 : W := mkw 0x400db8565463fda0 0xc4801b70aca8c7fb 0xc29ff8fc0ce7ffff 0xfb853ff1f819cfff

def z343 : W := mkw 0x20090142c3c1a302 0xb040120285878346 0xb80f0003c3c1e3d9 0x8f701e00078783c7

def z344 : W := mkw 0x5ffffeab7c01d87c 0xc0bffffd56f803b0 0xff6fff03fc01fc3b 0x9ffedffe07f803f8

def z345 : W := mkw 0x1ff86323bb9d1247 0x283ff0c647773a24 0x7d68e703f3180000 0x04fad1ce07e63000

def z346 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x000000000001ff80 0x00000000000003ff

def z347 : W := mkw 0x0020422000000000 0x0000408440000000 0x4568e7323338006e 0xf68ad1ce64667000

def z348 : W := mkw 0x0028432201010200 0x2000508644020204 0x4568e732030103ce 0xf68ad1ce64060207

def z349 : W := mkw 0x3fd794c8c2c0a17a 0x907faf2991858142 0xba9718cdc0c0e011 0x09752e319b8181c0

def z350 : W := mkw 0x1ff6defdaef66dff 0x443fedbdfb5decdb 0xffffffffffffffff 0xffffffffffffffff

def z351 : W := mkw 0x1fd00845aed66947 0x443fa0108b5dacd2 0x3ff018cffffee079 0x7e7fe0319ffffdc0

def z352 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdef7f8fc00000003 0x59bdeff1f8000000

def z353 : W := mkw 0x1ff6f6b8102814f8 0x083feded70205029 0xdffffffc30381c27 0xffbffffff8607038

def z354 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4108e73203011fce 0xa68211ce6406023f

def z355 : W := mkw 0x29ab67e2d3c9b312 0xb85356cfc5a79366 0xfdefe7c3f3d9e3dd 0xaffbdfcf87e7b3c7

def z356 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdf6fff0000000003 0x9fbedffe00000000

def z357 : W := mkw 0x00082113bbbd1687 0x2800104227777a2d 0x20000003ffff1ff8 0x0040000007fffe3f

def z358 : W := mkw 0x09f246a88294005b 0x0013e48d51052800 0x01f007fc03fe0044 0x6003e00ff807fc00

def z359 : W := mkw 0x1fd0000082800042 0x003fa00001050000 0x3ff00003c3c00058 0x7e7fe00007878000

def z360 : W := mkw 0x00204b74056a6f80 0x6c004096e80ad4df 0x03f01ffc0fffffff 0xfa07e03ff81fffff

def z361 : W := mkw 0x560db8025401d820 0xc0ac1b7004a803b0 0xde0ff8000001fc03 0x9fbc1ff0000003f8

def z362 : W := mkw 0x562cfb333d295ea4 0x68ac59f6667a52bd 0x4768ff323f391fee 0xf68ed1fe647e723f

def z363 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xc40ff8023001fc2b 0x97881ff0046003f8

def z364 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xba071803fc01fc39 0x09740e3007f803f8

def z365 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc00e011 0x0dfc1ff007f801c0

def z366 : W := mkw 0x560db8577c63fda4 0xc4ac1b70aef8c7fb 0xfe0ff803fce7fffb 0x9ffc1ff007f9cfff

def z367 : W := mkw 0x5ff7dea96c00c87c 0xc0bfefbd52d80190 0xfffffffdcc00e017 0xfffffffffb9801c0

def z368 : W := mkw 0x0020423000280480 0x0800408460005009 0x0060003000380000 0x4000c00060007000

def z369 : W := mkw 0x0000081404224c80 0x4400001028084499 0x0290183c0ce61c7a 0x7a0520307819cc38

def z370 : W := mkw 0x1fd0000082940043 0x003fa00001052800 0x1ff0000003fe0040 0x7e3fe0000007fc00

def z371 : W := mkw 0x1654900800000068 0x002ca92010000000 0x0210180c00000000 0x0004203018000000

def z372 : W := mkw 0x1fd82003ba951047 0x003fb04007752a20 0x7ff8e003ffff1c7a 0xfefff1c007fffe38

def z373 : W := mkw 0x0000004000402100 0x0000000080008042 0x008000c000c1e3dd 0xaa010001800183c7

def z374 : W := mkw 0x202b67f25169b790 0xb84056cfe4a2d36f 0xc00fe7f00001ff87 0x81801fcfe00003ff

def z375 : W := mkw 0x160008552c626d84 0x442c0010aa58c4db 0x3e9018fffce7ffff 0xfe7d2031fff9cfff

def z376 : W := mkw 0x0000084004406900 0x40000010800880d2 0x028018c00cc1ffff 0xba050031801983ff

def z377 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc001c22 0x15fc1ff007f80038

def z378 : W := mkw 0x1650000128140045 0x002ca00002502800 0x06f000003cfe0078 0x7a0de0000079fc00

def z379 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x000000000ce7fff8 0x000000000019cfff

def z380 : W := mkw 0x7f8fbd83ff81da36 0xf0ff1f7b07ff03b4 0xff0fff03ff01fc3b 0x9ffe1ffe07fe03f8

def z381 : W := mkw 0x09d0005482f625c3 0x0413a000a905ec4b 0x01f000fc03fe03c4 0x6003e001f807fc07

def z382 : W := mkw 0x09d0085486f66dc3 0x4413a010a90decdb 0x03f018fc0fffffff 0xfa07e031f81fffff

def z383 : W := mkw 0x0008010201010200 0x2000100204020204 0x0108070203000000 0x0402100e04060000

def z384 : W := mkw 0x1fd00041aad42147 0x003fa0008355a842 0x3ff000c3ffffe3fd 0xfe7fe00187ffffc7

def z385 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff0000233380068 0x7e3fe00004667000

def z386 : W := mkw 0x5ffff6ab7801907c 0x80bfffed56f00320 0xfd6fe703f0000000 0x05fadfce07e00000

def z387 : W := mkw 0x200b058241018210 0xb040160b04820304 0x800f070000000000 0x01001e0e00000000

def z388 : W := mkw 0x0000080004004800 0x4000001000080090 0x000000000c01fc38 0x00000000001803f8

def z389 : W := mkw 0x0000081004204c80 0x4000001020084099 0x020018300c21ffff 0xfa040030601843ff

def z390 : W := mkw 0x1fd69489aa94007f 0x003fad2913552800 0xba9718cdccc60011 0x09752e319b998c00

def z391 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x008018fc00c1ffdf 0xaa010031f80183ff

def z392 : W := mkw 0x5fddb857fef7fde7 0xc4bfbb70affdeffb 0xfffff8ffffffffff 0xfffffff1ffffffff

def z393 : W := mkw 0x098204c000402110 0x0013040980008042 0x998f07c000c1e3dd 0xaf331e0f800183c7

def z394 : W := mkw 0x3fffdffec7e3effa 0xf47fffbffd8fc7df 0xffffffffcfe7ffff 0xffffffffff9fcfff

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x0560000000000000 0x760ac00000000000

def z396 : W := mkw 0x298b25d2d3e9b792 0xb853164ba5a7d36f 0xb98f07c3f3f9fffd 0xaf731e0f87e7f3ff

def z397 : W := mkw 0x0009010241018200 0xa000120204820304 0xb90f0703c301e3dd 0xaf721e0e078603c7

def z398 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x0000000000e603c0 0x000000000001cc07

def z399 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xddefe7c000000005 0xafbbdfcf80000000

def z400 : W := mkw 0x09f246a800000058 0x0013e48d50000000 0x45f8e7fc00000006 0xf68bf1cff8000000

def z401 : W := mkw 0x09f246fc006225d8 0x0413e48df800c44b 0x01f007fc00e603c4 0x6003e00ff801cc07

def z402 : W := mkw 0x1674d22800000068 0x002ce9a450000000 0x46f0f8fc00000007 0xfa8de1f1f8000000

def z403 : W := mkw 0x560db9137d29dea4 0xe8ac1b7226fa53bd 0xfe0ff803ff39fffb 0x9ffc1ff007fe73ff

def z404 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ef00001fcfe0030 0x587de00003f9fc00

def z405 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x029000fc0ce603fc 0x7a052001f819cc07

def z406 : W := mkw 0x402dfb325529dea0 0xe8805bf664aa53bd 0xc56fff323339ffef 0xf78adffe646673ff

def z407 : W := mkw 0x09f24efc04626dd8 0x4413e49df808c4db 0x03f01ffc0ce7ffff 0xfa07e03ff819cfff

def z408 : W := mkw 0x600fbdc25541fb30 0xf0c01f7b84aa83f6 0xc00fffc00001ff87 0x81801fff800003ff

def z409 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0x808f07c000c1e3dd 0xab011e0f800183c7

def z410 : W := mkw 0x1674f238102814e8 0x082ce9e470205029 0x4670f83c30381c22 0x508ce1f078607038

def z411 : W := mkw 0x20090956c7e3ef82 0xf4401212ad8fc7df 0x229018ffcfe7ffff 0xfa452031ff9fcfff

def z412 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3df00003f3fe0040 0x647be00007e7fc00

def z413 : W := mkw 0x1650000128140045 0x002ca00002502800 0x021000000c060000 0x0004200000180c00

def z414 : W := mkw 0x0000001000200480 0x0000000020004009 0x029000300ce71ffe 0xfa0520006019ce3f

def z415 : W := mkw 0x0000001000200480 0x0000000020004009 0x029018fc00211fef 0xfa052031f800423f

def z416 : W := mkw 0x0008200210011000 0x0000104004200220 0x4568e00233391c6a 0xf68ad1c004667238

def z417 : W := mkw 0x0004900000000020 0x0000092000000000 0xc00ff80000000003 0x81801ff000000000

def z418 : W := mkw 0x562dfb777d6bffa4 0xecac5bf6eefad7ff 0xffffffffffffffff 0xffffffffffffffff

def z419 : W := mkw 0x098a058201010210 0x2013140b04020204 0x998f07c2030103cd 0xaf331e0f84060207

def z420 : W := mkw 0x3fdf95cac3c1a37a 0xb07fbf2b95878346 0xbb9f1fcfc3c1e3dd 0xaf773e3f9f8783c7

def z421 : W := mkw 0x0028633211291680 0x280050c66422522d 0x47f8e7323fff1ffe 0xfe8ff1ce647ffe3f

def z422 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233381c22 0x548ad1ce64667038

def z423 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0xb80f07c3c001e39d 0x8f701e0f878003c7

def z424 : W := mkw 0x200b0dd64563ef90 0xf440161bac8ac7df 0x800f1ffc0001ff87 0x81001e3ff80003ff

def z425 : W := mkw 0x09f247b8012806d8 0x2813e48f7002500d 0x01f007fc033803c4 0x6003e00ff8067007

def z426 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x38000001c0000000 0x0070000003800000

def z427 : W := mkw 0x0000080004004800 0x4000001000080090 0x020018000c001c22 0x1004003000180038

def z428 : W := mkw 0x1674d2292814006d 0x002ce9a452502800 0x4670f83c3c3e0022 0x508ce1f078787c00

def z429 : W := mkw 0x7f8fb583fb819236 0xb0ff1f6b07f70324 0xfd0fe703f3000000 0x05fa1fce07e60000

def z430 : W := mkw 0x200b05c2c3c1a312 0xb040160b85878346 0xa00f07c3c3c1e3dd 0x81401e0f878783c7

def z431 : W := mkw 0x29890142c3c1a302 0xb053120285878346 0x39800003c3c1e3d8 0x2e730000078783c7

def z432 : W := mkw 0x20010040c2c0a102 0x9040020081858142 0x20000001c0c0e010 0x00400000038181c0

def z433 : W := mkw 0x560cb8033c015824 0x40ac1970067802b0 0x4608f8023c011c2a 0x968c11f004780238

def z434 : W := mkw 0x562ffeab7c01d83c 0xc0ac5ffd56f803b0 0xfe0ffffffc01fc3f 0x9ffc1ffffff803f8

def z435 : W := mkw 0x560db8437c41f924 0xc0ac1b7086f883f2 0xfe8ff8c3fcc1ffff 0xbffd1ff187f983ff

def z436 : W := mkw 0x5ffff6ab7801907c 0x80bfffed56f00320 0xfffffffff0000007 0xffffffffffe00000

def z437 : W := mkw 0x16706231383c14c5 0x082ce0c462707829 0x4670e0303c3e1c22 0x508ce1c060787c38

def z438 : W := mkw 0x1fd00855aef66dc7 0x443fa010ab5decdb 0x3ff00003fffffff8 0x7e7fe00007ffffff

def z439 : W := mkw 0x7f879cc1eec0e936 0xd0ff0f3983dd81d2 0xba8718c1ccc0e011 0x09750e31839981c0

def z440 : W := mkw 0x00204374016a2780 0x2c004086e802d44f 0x01f007fc03fe03c4 0x6003e00ff807fc07

def z441 : W := mkw 0x0000080404024800 0x4400001008080490 0x0210180c0c060000 0x0004203018180c00

def z442 : W := mkw 0x0020422000000000 0x0000408440000000 0x4568e70000000000 0x048ad1ce00000000

def z443 : W := mkw 0x0000081404224c80 0x4400001028084499 0x0000183c00001c02 0x0000003078000038

def z444 : W := mkw 0x1fd00055aaf625c7 0x043fa000ab55ec4b 0x3ff000fffffe03fc 0x7e7fe001fffffc07

def z445 : W := mkw 0x298205c083c02312 0x3053040b81078046 0x398007c3c3c003dc 0x2e73000f87878007

def z446 : W := mkw 0x000908564463ed80 0xc4001210ac88c7db 0xba9f18ffcce7ffff 0xff753e31ff99cfff

def z447 : W := mkw 0x1ff6defc04626df8 0x443fedbdf808c4db 0xdffffffc0001ff87 0xffbffffff80003ff

def z448 : W := mkw 0x1fd0085404626dc0 0x443fa010a808c4db 0x1ff018fc0ce7ffff 0xfe3fe031f819cfff

def z449 : W := mkw 0x09aa67b211291690 0x281354cf6422522d 0xddefe7f233391fef 0xffbbdfcfe466723f

def z450 : W := mkw 0x0028633211291680 0x280050c66422522d 0x47f8fffe33391fef 0xfe8ff1fffc66723f

def z451 : W := mkw 0x560928037c01d804 0xc0ac125006f803b0 0x3e000003fc01fc38 0x1e7c000007f803f8

def z452 : W := mkw 0x1674d22800000068 0x002ce9a450000000 0xde7ff83c00000003 0xdfbcfff078000000

def z453 : W := mkw 0x165008152c364cc5 0x442ca0102a586c99 0x0670183c3c3e1c22 0x500ce03078787c38

def z454 : W := mkw 0x0000004000402100 0x0000000080008042 0x0000000000c1e3d8 0x00000000000183c7

def z455 : W := mkw 0x1600000128000004 0x002c000002500000 0x3e900003fce60078 0x7e7d200007f9cc00

def z456 : W := mkw 0x1ffef7aa11091278 0x283ffdef54221224 0xdd6fe70233180000 0x05badfce04663000

def z457 : W := mkw 0x298205d483e22792 0x3453040ba907c44f 0x019007fc03e603c4 0x6003200ff807cc07

def z458 : W := mkw 0x0020433001280680 0x280040866002500d 0x0160073003391fee 0xf202c00e6006723f

def z459 : W := mkw 0x7fdfbdc3ffd5fb77 0xf0ffbf7b87ffabf6 0xffffffc3ffffffff 0xffffffff87ffffff

def z460 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4408e73230011fae 0x968811ce6460023f

def z461 : W := mkw 0x0000004000402100 0x0000000080008042 0x008000c000c0e011 0x08010001800181c0

def z462 : W := mkw 0x0000081404224c80 0x4400001028084499 0x0210183c0c271fee 0xf204203078184e3f

def z463 : W := mkw 0x0980085486e26d82 0x44130010a90dc4db 0x3b9018ffcfe7ffff 0xfe772031ff9fcfff

def z464 : W := mkw 0x29d205c083d42353 0x3053a40b8107a846 0x01f007c003fe03c4 0x6003e00f8007fc07

def z465 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x009000fc0ce7fffc 0x60012001f819cfff

def z466 : W := mkw 0x1ff6d6e800402178 0x003fedadd0008042 0xdffffffc00c1e3df 0xffbffffff80183c7

def z467 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff018fffffe007f 0xfe7fe031fffffc00

def z468 : W := mkw 0x09d0000082940043 0x0013a00001052800 0x03f000000ffe0078 0x7a07e000001ffc00

def z469 : W := mkw 0x5ffffeaa5401d878 0xc0bffffd54a803b0 0xdffffffc0001fc07 0xffbffffff80003f8

def z470 : W := mkw 0x0000081404224c80 0x4400001028084499 0x029018fc0c261c27 0xfa052031f8184c38

def z471 : W := mkw 0x560db8137c21dca4 0xc0ac1b7026f843b9 0xfe0ff833fc21ffff 0xfffc1ff067f843ff

def z472 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00001ccc60010 0x7e7fe00003998c00

def z473 : W := mkw 0x1ffef6aa10011078 0x003ffded54200220 0xdffffffe30011c2f 0xffbffffffc600238

def z474 : W := mkw 0x29fb47eac3c1a35a 0xb053f68fd5878346 0xb9ff07ffc3c1e3dd 0xef73fe0fff8783c7

def z475 : W := mkw 0x0024d22800000028 0x000049a450000000 0x4000f83c00000002 0x008001f078000000

def z476 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb9f07c3cfe7e3fd 0xff773e0f879fcfc7

def z477 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb9f1fffc3c1e3df 0xff773e3fff8783c7

def z478 : W := mkw 0x3ffb67f3fbfdb7d7 0xb87ff6cfe7f7fb6f 0xffffe7f3ffffffff 0xffffffcfe7ffffff

def z479 : W := mkw 0x0000004000402100 0x0000000080008042 0x029000c00ce7e3fd 0xfa0520018019cfc7

def z480 : W := mkw 0x1fd6948800000078 0x003fad2910000000 0x9807000000000000 0x01300e0000000000

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x0090000000e60040 0x600120000001cc00

def z482 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x000000fc00000384 0x00000001f8000007

def z483 : W := mkw 0x0008014201412300 0x2000100284028246 0x018807c203c1e3dd 0xae03100f840783c7

def z484 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe9ff803fce7fc7b 0xfffd3ff007f9cff8

def z485 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xc20ff8000c01fc3b 0x9b841ff0001803f8

def z486 : W := mkw 0x0000000000000000 0x0000000000000000 0x4408e00000000002 0x968811c000000000

def z487 : W := mkw 0x298204c082c02112 0x1053040981058042 0x008000c000c00000 0x0001000180018000

def z488 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdf7fff3c00000002 0x55befffe78000000

def z489 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3de00003f3d80058 0x2e7bc00007e7b000

def z490 : W := mkw 0x1fd0000128000044 0x003fa00002500000 0x3ff00003fc000038 0x7e7fe00007f80000

def z491 : W := mkw 0x0000001000200480 0x0000000020004009 0x0000003000011f86 0x800000006000023f

def z492 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003ffde0010 0x0c7fe00007ffbc00

def z493 : W := mkw 0x0020422000000000 0x0000408440000000 0x47f8fffc00000007 0xfe8ff1fff8000000

def z494 : W := mkw 0x400db00250019020 0x80801b6004a00320 0xc00fe00000000000 0x01801fc000000000

def z495 : W := mkw 0x00286376116b3780 0x2c0050c6ec22d66f 0x45f8e7fe33ff1fee 0xf68bf1cffc67fe3f

def z496 : W := mkw 0x29afd7eac3c1a33a 0xb0535fafd5878346 0xf98fffffc3c1e3df 0xaff31fffff8783c7

def z497 : W := mkw 0x298b0dd6c7e3ef92 0xf453161bad8fc7df 0xb98f07c3cfe7fffd 0xaf731e0f879fcfff

def z498 : W := mkw 0x200b0dd64563ef90 0xf440161bac8ac7df 0x829f1ffc0ce7ffff 0xfb053e3ff819cfff

def z499 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce61fe6 0x70052031f819cc3f

def z500 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x009000fc00e7e3dd 0xea012001f801cfc7

def z501 : W := mkw 0x40092803fe95d807 0xc080125007fd2bb0 0x20000003fffffc78 0x0040000007fffff8

def z502 : W := mkw 0x1f800001aa800006 0x003f000003550000 0x3f800003ffc00078 0x3e7f000007ff8000

def z503 : W := mkw 0x0028632211091200 0x280050c644221224 0x4008e70000000000 0x008011ce00000000

def z504 : W := mkw 0x5fd4b801be945867 0x40bfa970037d28b0 0x7ff0f803fffe1c7a 0x7effe1f007fffc38

def z505 : W := mkw 0x0008211211291680 0x280010422422522d 0x0000003233391fee 0xf20000006466723f

def z506 : W := mkw 0x1ff04221aa940047 0x003fe08443552800 0x7ff8e733fffe007e 0xfefff1ce67fffc00

def z507 : W := mkw 0x1fd80103ab950247 0x203fb00207572a04 0x3ff80703ffff03fc 0xfe7ff00e07fffe07

def z508 : W := mkw 0x0008211211291680 0x280010422422522d 0x0000000000011f80 0x000000000000023f

def z509 : W := mkw 0x5f8db803fe81d826 0xc0bf1b7007fd03b0 0xff8ff803ffc1fc7b 0xbfff1ff007ff83f8

def z510 : W := mkw 0x1fd0000128140045 0x003fa00002502800 0x1ff000003c3e0020 0x7e3fe00000787c00

def z511 : W := mkw 0x7f8fbcc3fec1f936 0xd0ff1f7987fd83f2 0xfe8ff8c3fcc1fc3b 0x9ffd1ff187f983f8

def z512 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x07f000003ffe0060 0x700fe000007ffc00

def z513 : W := mkw 0x5fd59801ee94c867 0xc0bfab3003dd2990 0xba971801ccc6e011 0x09752e3003998dc0

def z514 : W := mkw 0x1674da7c04626de8 0x442ce9b4f808c4db 0x46f0f8fc0ce7ffff 0xfa8de1f1f819cfff

def z515 : W := mkw 0x1ff246a9aa94005f 0x003fe48d53552800 0x3ff007fffffe007c 0x7e7fe00ffffffc00

def z516 : W := mkw 0x5ff6fea93c00587c 0x40bfedfd527800b0 0xdffffffc3c001c27 0xffbffffff8780038

def z517 : W := mkw 0x0020422000000000 0x0000408440000000 0x4460e03000000002 0x5088c1c060000000

def z518 : W := mkw 0x400928577c63fd84 0xc4801250aef8c7fb 0x20000003fce7fff8 0x0040000007f9cfff

def z519 : W := mkw 0x1ff4d229aa94006f 0x003fe9a453552800 0x7ff0f83ffffe007a 0x7effe1f07ffffc00

def z520 : W := mkw 0x298b05d2c3e1a792 0xb053160ba587c34f 0xb98f07f3c3e1ffff 0xff731e0fe787c3ff

def z521 : W := mkw 0x1650000128140045 0x002ca00002502800 0x3e700003fc3e0038 0x5e7ce00007f87c00

def z522 : W := mkw 0x0028637211693780 0x280050c6e422d26f 0x45e8e7f233f9ffff 0xfe8bd1cfe467f3ff

def z523 : W := mkw 0x200304c04040a110 0x9040060980808142 0x800700c00000e001 0x01000e01800001c0

def z524 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x020018000ce7fffb 0x9a0400300019cfff

def z525 : W := mkw 0x560498012c004824 0x40ac093002580090 0x020018000c000000 0x0004003000180000

def z526 : W := mkw 0x1fd00815aeb64cc7 0x443fa0102b5d6c99 0x3ff0183ffffe1c7a 0x7e7fe0307ffffc38

def z527 : W := mkw 0x16000001aa940007 0x002c000003552800 0x3e000003fffe0078 0x1e7c000007fffc00

def z528 : W := mkw 0x1ffef7aa11091278 0x283ffdef54221224 0xdffffffe33180007 0xffbffffffc663000

def z529 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1d60000000000000 0x043ac00000000000

def z530 : W := mkw 0x5604b8013c005824 0x40ac0970027800b0 0x4600f8003c01fc3b 0x9a8c01f0007803f8

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x07f000023ffe0078 0x7e0fe000047ffc00

def z532 : W := mkw 0x298b0dd6c7e3ef92 0xf453161bad8fc7df 0xb98f1fffc3c1ffdf 0xaf731e3fff8783ff

def z533 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xddffe7fc00000004 0x65bbffcff8000000

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000230000028 0x1608000004600000

def z535 : W := mkw 0x400928037c01d804 0xc080125006f803b0 0x6408e003fc01fc3a 0x96c811c007f803f8

def z536 : W := mkw 0x09d0000082940043 0x0013a00001052800 0x39f00003c3fe0058 0x6e73e0000787fc00

def z537 : W := mkw 0x1ff6dea804004878 0x403fedbd50080090 0xdffffffc0c01fc3f 0xffbffffff81803f8

def z538 : W := mkw 0x1674d22800000068 0x002ce9a450000000 0x4778ff3c00000006 0xf68ef1fe78000000

def z539 : W := mkw 0x00000001aa940007 0x0000000003552800 0x22900003fffe0078 0x7a45200007fffc00

def z540 : W := mkw 0x5604b00138001024 0x00ac096002700020 0x4400e00030000000 0x008801c000600000

def z541 : W := mkw 0x0020433001280680 0x280040866002500d 0x0000073000000384 0x0000000e60000007

def z542 : W := mkw 0x562dfb337d29dea4 0xe8ac5bf666fa53bd 0xfe0fff33fc01ffbf 0x9ffc1ffe67f803ff

def z543 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4008e73233391fee 0x808011ce6466723f

def z544 : W := mkw 0x0980000082800002 0x0013000001050000 0x3b900003cfe60078 0x7e772000079fcc00

def z545 : W := mkw 0x29ab47f2c3e9a792 0xb853568fe587d34f 0xb9ef07f3c3f9e3dd 0xef73de0fe787f3c7

def z546 : W := mkw 0x0028633211291680 0x280050c66422522d 0x0160073233391fec 0x6002c00e6466723f

def z547 : W := mkw 0x09f8633293bd16c3 0x2813f0c665277a2d 0x45f8e73233ff1fee 0xf68bf1ce6467fe3f

def z548 : W := mkw 0x3fffd7aac381827a 0xb07fffaf55870304 0xfd6fe703c3000000 0x05fadfce07860000

def z549 : W := mkw 0x698b2dc3ffc1fb16 0xf0d3165b87ff83f6 0xb98f07c3ffc1fffd 0xaf731e0f87ff83ff

def z550 : W := mkw 0x00286b76156b7f80 0x6c0050d6ec2ad6ff 0x4008fffc0001ff87 0x808011fff80003ff

def z551 : W := mkw 0x0000011001280680 0x280000022002500d 0x00000000033803c0 0x0000000000067007

def z552 : W := mkw 0x0982048000000010 0x0013040900000000 0x990f070000000000 0x05321e0e00000000

def z553 : W := mkw 0x0000004000402100 0x0000000080008042 0x000000c00001e385 0x80000001800003c7

def z554 : W := mkw 0x1604900000000020 0x002c092000000000 0x9a07180000000001 0x09340e3000000000

def z555 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3f600003ff180038 0x1e7ec00007fe3000

def z556 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0x810f07c20301e3cd 0xa7021e0f840603c7

def z557 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c0e011 0x0d731e0f878781c0

def z558 : W := mkw 0x0028632211091200 0x280050c644221224 0x4568e73233180006 0xf68ad1ce64663000

def z559 : W := mkw 0x0020623010281480 0x080040c460205029 0x4460e03030391fee 0xf288c1c06060723f

def z560 : W := mkw 0x400928037c01d804 0xc080125006f803b0 0x22001803fc01fc3b 0x9a44003007f803f8

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x009000fc00000004 0x60012001f8000000

def z562 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb88700c3c3c1e3d9 0x09710e01878783c7

def z563 : W := mkw 0x5fddb803fe95d867 0xc0bfbb7007fd2bb0 0xfe9ff803fcc7fc3b 0x9ffd3ff007f98ff8

def z564 : W := mkw 0x402ffeaa5401d838 0xc0805ffd54a803b0 0xc00ffffc0001fc07 0x81801ffff80003f8

def z565 : W := mkw 0x298205c083c02312 0x3053040b81078046 0x998f07c003c003c5 0xaf331e0f80078007

def z566 : W := mkw 0x4009200378019004 0x8080124006f00320 0x20000003f0000000 0x0040000007e00000

def z567 : W := mkw 0x1600000128000004 0x002c000002500000 0x3a000001cc000010 0x0874000003980000

def z568 : W := mkw 0x40296b337d29de84 0xe88052d666fa53bd 0x6568e733ff39fffe 0xf6cad1ce67fe73ff

def z569 : W := mkw 0x562dfb237d09da24 0xe8ac5bf646fa13b4 0xff6fff03ff19fc3b 0x9ffedffe07fe33f8

def z570 : W := mkw 0x1ff86332112916c0 0x283ff0c66422522d 0x5ff8e73233391fee 0xfebff1ce6466723f

def z571 : W := mkw 0x560db00378019024 0x80ac1b6006f00320 0xfc0fe003f0011c2a 0x97f81fc007e00238

def z572 : W := mkw 0x0028632211091200 0x280050c644221224 0x4568e70233191c2a 0x968ad1ce04663238

def z573 : W := mkw 0x1ff86323bb9d1247 0x283ff0c647773a24 0x7ff8e703fffe0078 0x7efff1ce07fffc00

def z574 : W := mkw 0x5fddb003fa959067 0x80bfbb6007f52b20 0xffffe003fffe0078 0x7fffffc007fffc00

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000200068 0x7200000000004000

def z576 : W := mkw 0x162cf332112916a0 0x282c59e66422522d 0xdf6fff3233391fef 0xffbedffe6466723f

def z577 : W := mkw 0x0008210211011200 0x2000104204220224 0x4508e70233011fee 0xb68a11ce0466023f

def z578 : W := mkw 0x0982048000000010 0x0013040900000000 0x988700c000000001 0x09310e0180000000

def z579 : W := mkw 0x0026defc04626db8 0x44004dbdf808c4db 0xc00ffffc0001ff87 0x81801ffff80003ff

def z580 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff018fc00000007 0xfe3fe031f8000000

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000001e019 0x8a000000000003c0

def z582 : W := mkw 0x2982058083800212 0x3053040b01070004 0x0100070003000000 0x0002000e00060000

def z583 : W := mkw 0x1fd00855aef66dc7 0x443fa010ab5decdb 0x3a9018fdcce7ffff 0xfa752031fb99cfff

def z584 : W := mkw 0x0000084404426900 0x44000010880884d2 0x029018cc0ce6e079 0x7a0520319819cdc0

def z585 : W := mkw 0x400028013c005804 0x40800050027800b0 0x000000003c001c20 0x0000000000780038

def z586 : W := mkw 0x0020622010081000 0x080040c440201020 0x4460e00030180000 0x0088c1c000603000

def z587 : W := mkw 0x3fdb0583eb958257 0xb07fb60b07d72b04 0xbd6f0703f3180000 0x057ade0e07e63000

def z588 : W := mkw 0x00286b76156b7f80 0x6c0050d6ec2ad6ff 0x4568fffe3339ffef 0xf68ad1fffc6673ff

def z589 : W := mkw 0x1ff0422000000040 0x003fe08440000000 0x5ff8e73000000006 0xfebff1ce60000000

def z590 : W := mkw 0x1628633339291684 0x282c50c66672522d 0x7f68e733ff391ffe 0xfefed1ce67fe723f

def z591 : W := mkw 0x4004b80014005820 0x40800970002800b0 0x4000f80000001c02 0x008001f000000038

def z592 : W := mkw 0x562df333792996a4 0xa8ac5be666f2532d 0xfd6fe733f3391fee 0xf7fadfce67e6723f

def z593 : W := mkw 0x298205c083c02312 0x3053040b81078046 0x018007c003c1e3dd 0xaa03000f800783c7

def z594 : W := mkw 0x0000201010281480 0x0800004020205029 0x0000000030381c20 0x0000000000607038

def z595 : W := mkw 0x0000080004004800 0x4000001000080090 0x029018000ce7fc7b 0xfa0520300019cff8

def z596 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x020018fc0c01ffbf 0x9a040031f81803ff

def z597 : W := mkw 0x1ff86333bbbd16c7 0x283ff0c667777a2d 0x7d68e733f3391fee 0xf6fad1ce67e6723f

def z598 : W := mkw 0x3fd304c1ead4a157 0x907fa60983d5a942 0xbff700c3fffee079 0x7f7fee0187fffdc0

def z599 : W := mkw 0x1ffef7ba112916f8 0x283ffdef7422522d 0xdffffffc00011f87 0xffbffffff800023f

def z600 : W := mkw 0x1ff4d22800000068 0x003fe9a450000000 0x5ff0f83c00000002 0x7ebfe1f078000000

def z601 : W := mkw 0x1ff86b77bfff7fc7 0x6c3ff0d6ef7ffeff 0x7ff8ffffffffffff 0xfefff1ffffffffff

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0x0560000233180000 0x040ac00004663000

def z603 : W := mkw 0x0028632211091200 0x280050c644221224 0x4568e70233380068 0x768ad1ce04667000

def z604 : W := mkw 0x560db00378019024 0x80ac1b6006f00320 0xfe0ff803f0000003 0x9ffc1ff007e00000

def z605 : W := mkw 0x400598004400c820 0xc0800b3000880190 0x800718000000e001 0x01000e30000001c0

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x0108070000000004 0xa602100e00000000

def z607 : W := mkw 0x1fffd6aa40018078 0x803fffad54800300 0xffffffffc001e01f 0xffffffffff8003c0

def z608 : W := mkw 0x298b0dc6c7c3eb12 0xf453161b8d8f87d6 0xbb9f1fcfcfc7e3dd 0xaf773e3f9f9f8fc7

def z609 : W := mkw 0x0982048000000010 0x0013040900000000 0x9b9f1ffc00000007 0xff373e3ff8000000

def z610 : W := mkw 0x7faffff3ffe9ffb6 0xf8ff5fffe7ffd3ff 0xffeffff3fff9ffff 0xffffdfffe7fff3ff

def z611 : W := mkw 0x2000014083c02302 0x3040000281078046 0x0000000003c003c0 0x0000000000078007

def z612 : W := mkw 0x1ff6d6b8002004f8 0x003fedad70004009 0xdffffffc00211fef 0xffbffffff800423f

def z613 : W := mkw 0x00000001aa940007 0x0000000003552800 0x20000003f3180000 0x0040000007e63000

def z614 : W := mkw 0x098b048240018010 0x8013160904800300 0xb98f07c3c001e01d 0xaf731e0f878003c0

def z615 : W := mkw 0x1650000128140045 0x002ca00002502800 0x077000023f3e0068 0x760ee000047e7c00

def z616 : W := mkw 0x562df32379099224 0xa8ac5be646f21324 0xfd6fe703f3180000 0x05fadfce07e63000

def z617 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xc60ff8003c01fc23 0x918c1ff0007803f8

def z618 : W := mkw 0x400928037c01d804 0xc080125006f803b0 0xb80f0003fc01fc39 0x8f701e0007f803f8

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200180000000003 0x9a04003000000000

def z620 : W := mkw 0x00000001aa940007 0x0000000003552800 0x20000001ccc60010 0x0040000003998c00

def z621 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73000011f86 0xf68ad1ce6000023f

def z622 : W := mkw 0x0008211211291680 0x280010422422522d 0x0560000233391fe8 0x760ac0000466723f

def z623 : W := mkw 0x0020623010281480 0x080040c460205029 0x4560e03233381c6a 0x768ac1c064667038

def z624 : W := mkw 0x0020623010281480 0x080040c460205029 0x4568e73030381c26 0xf68ad1ce60607038

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x0460000030380020 0x5008c00000607000

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x0290000000000000 0x7a05200000000000

def z627 : W := mkw 0x1fd00801ae944847 0x403fa010035d2890 0x3ff01803fffffc7b 0xfe7fe03007fffff8

def z628 : W := mkw 0x400db8565463fda0 0xc4801b70aca8c7fb 0xc00ff8fc0001ff87 0x81801ff1f80003ff

def z629 : W := mkw 0x20090142c3c1a302 0xb040120285878346 0x21080703c3c1e3dc 0xa642100e078783c7

def z630 : W := mkw 0x5604b8013c005824 0x40ac0970027800b0 0xde0ff8003c001c23 0x9fbc1ff000780038

def z631 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3d600003f3380068 0x767ac00007e67000

def z632 : W := mkw 0x0000005000602580 0x00000000a000c04b 0x008000f000e1ffff 0xfa010001e001c3ff

def z633 : W := mkw 0x20090143ebd5a307 0xb040120287d7ab46 0x20000003ffffe3f8 0x0040000007ffffc7

def z634 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3f700003ff3e0020 0x547ee00007fe7c00

def z635 : W := mkw 0x560598456c42e924 0xc4ac0b308ad885d2 0xba9718cdccc6e011 0x09752e319b998dc0

def z636 : W := mkw 0x7fffffebffc1fb7e 0xf0ffffffd7ff83f6 0xffffffffffc1ffff 0xffffffffffff83ff

def z637 : W := mkw 0x29ab67a2d3899212 0xb85356cf45a71324 0xfd6fe703f3180000 0x05fadfce07e63000

def z638 : W := mkw 0x402dfb325529dea0 0xe8805bf664aa53bd 0xc00fff300001ff87 0x81801ffe600003ff

def z639 : W := mkw 0x0020433001280680 0x280040866002500d 0x05600732333803ec 0x760ac00e64667007

def z640 : W := mkw 0x00000855aef66d87 0x44000010ab5decdb 0x229018ffffffffff 0xfa452031ffffffff

def z641 : W := mkw 0x0008285614637d80 0x44001050ac28c6fb 0x4698f8fe3ce7ffff 0xfe8d31f1fc79cfff

def z642 : W := mkw 0x0020432001080200 0x2800408640021004 0x0160070003180000 0x0002c00e00063000

def z643 : W := mkw 0x000908024401c800 0xc000121004880390 0xba0f1803cc01fc3b 0x9f741e30079803f8

def z644 : W := mkw 0x760db943ffc1fb26 0xf0ec1b7287ff83f6 0xfe0ff803ffc1fffb 0x9ffc1ff007ff83ff

def z645 : W := mkw 0x1604980004004820 0x402c093000080090 0xde0ff8000c01fc3b 0x9fbc1ff0001803f8

def z646 : W := mkw 0x1604900000000020 0x002c092000000000 0xdc0fe00000000000 0x05b81fc000000000

def z647 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c003c4 0x25731e0f87878007

def z648 : W := mkw 0x1674da3c04224ce8 0x442ce9b478084499 0x4670f83c0c261c22 0x508ce1f078184c38

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x0160000003380040 0x6002c00000067000

def z650 : W := mkw 0x0028433201290680 0x280050866402520d 0x01680732033903cc 0xe602d00e64067207

def z651 : W := mkw 0x7f8f9dc3efc1eb36 0xf0ff1f3b87df83d6 0xbb8f1fc3cfc1e3dd 0xaf771e3f879f83c7

def z652 : W := mkw 0x0982048000000010 0x0013040900000000 0x018007c000000004 0x2003000f80000000

def z653 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdd6fe73000000006 0xf7badfce60000000

def z654 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfd6fe703f3180000 0x05fadfce07e63000

def z655 : W := mkw 0x0000000082800002 0x0000000001050000 0x20000003c3c00058 0x0040000007878000

def z656 : W := mkw 0x0000084404426900 0x44000010880884d2 0x000018cc0000e001 0x00000031980001c0

def z657 : W := mkw 0x0000084404426900 0x44000010880884d2 0x000000000cc6e010 0x0000000000198dc0

def z658 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3a900001cce60078 0x7a7520000399cc00

def z659 : W := mkw 0x09800001aa940007 0x0013000003552800 0x39800003fffe0078 0x2e73000007fffc00

def z660 : W := mkw 0x0988010283810202 0x2013100205070204 0x39880703c3c103dc 0xae73100e07878207

def z661 : W := mkw 0x5604b8153c225ca4 0x44ac09702a7844b9 0x4610f83c3c261c22 0x508c21f078784c38

def z662 : W := mkw 0x0020623010281480 0x080040c460205029 0x4000e03000001c02 0x008001c060000038

def z663 : W := mkw 0x1fd69cdc04626df8 0x443fad39b808c4db 0x9a9718fc0ce7ffff 0xfb352e31f819cfff

def z664 : W := mkw 0x1ff6d7b8012806f8 0x283fedaf7002500d 0xdffffffc033803c7 0xffbffffff8067007

def z665 : W := mkw 0x560598556c62eda4 0xc4ac0b30aad8c5db 0xba9718fdcce7ffff 0xfb752e31fb99cfff

def z666 : W := mkw 0x5fd79c896c00c87c 0xc0bfaf3912d80190 0xba9718cdcc00e011 0x09752e319b9801c0

def z667 : W := mkw 0x0000080004004800 0x4000001000080090 0x000018000001fc03 0x80000030000003f8

def z668 : W := mkw 0x29830cc4c6c2e912 0xd4530619898d85d2 0xba9718cdccc6e011 0x09752e319b998dc0

def z669 : W := mkw 0x29ab67b2d3a99692 0xb85356cf65a7532d 0xfd6fe733f3391fee 0xf7fadfce67e6723f

def z670 : W := mkw 0x09d0000082940043 0x0013a00001052800 0x0090000000c60000 0x0001200000018c00

def z671 : W := mkw 0x3fdb05c2c3c1a352 0xb07fb60b85878346 0xbfff07c3c3c1e3dd 0xff7ffe0f878783c7

def z672 : W := mkw 0x298b05c3ebd5a317 0xb053160b87d7ab46 0xb98f07c3ffffe3fd 0xaf731e0f87ffffc7

def z673 : W := mkw 0x7f8fbdd7ffe3ffb6 0xf4ff1f7bafffc7ff 0xff9fffffffe7ffff 0xffff3fffffffcfff

def z674 : W := mkw 0x3fd304c1ead4a157 0x907fa60983d5a942 0xba9700c1ccc6e011 0x09752e0183998dc0

def z675 : W := mkw 0x0000080004004800 0x4000001000080090 0x029018fc0c01fc3f 0xfa052031f81803f8

def z676 : W := mkw 0x298a05c283c12312 0x3053140b85078246 0x018807c203c103cc 0xa603100f84078207

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x021000000c260020 0x5004200000184c00

def z678 : W := mkw 0x0000004400422100 0x0400000088008442 0x009000cc00c60000 0x0001200198018c00

def z679 : W := mkw 0x1fd00845aed66947 0x443fa0108b5dacd2 0x3a9018cdccc6e011 0x087520319b998dc0

def z680 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0x218007c3c3c1e3dc 0x2043000f878783c7

def z681 : W := mkw 0x0000005400622580 0x04000000a800c44b 0x029018fc00e603c7 0xfa052031f801cc07

def z682 : W := mkw 0x7f8fb5c3fbc1b336 0xb0ff1f6b87f78366 0xfd8fe7c3f3c1e3dd 0xaffb1fcf87e783c7

def z683 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3a900003fffe0078 0x0875200007fffc00

def z684 : W := mkw 0x400929137d29de84 0xe880125226fa53bd 0x20000003ff39fff8 0x0040000007fe73ff

def z685 : W := mkw 0x0008210211091200 0x2800104204221224 0x0000000233180000 0x0000000004663000

def z686 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce6fc33 0x58052031f819cdf8

def z687 : W := mkw 0x1fd4900000000060 0x003fa92000000000 0xdffff80000000003 0xffbffff000000000

def z688 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003f3180000 0x7e7fe00007e63000

def z689 : W := mkw 0x09a8633293a91682 0x281350c66527522d 0x7de8e733f3f91ffe 0xfefbd1ce67e7f23f

def z690 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4168e73003391fc6 0xe082d1ce6006723f

def z691 : W := mkw 0x0000001400220480 0x0400000028004409 0x0010003c00260000 0x4000200078004c00

def z692 : W := mkw 0x0009000240018000 0x8000120004800300 0x20000003c001e018 0x00400000078003c0

def z693 : W := mkw 0x560d98036c01c824 0xc0ac1b3006d80390 0xba0f1803cc01e019 0x8f741e30079803c0

def z694 : W := mkw 0x0008211211291680 0x280010422422522d 0x4408e00233391fea 0x968811c00466723f

def z695 : W := mkw 0x00286b76156b7f80 0x6c0050d6ec2ad6ff 0x4568e7323ffffffe 0xf68ad1ce647fffff

def z696 : W := mkw 0x1ffef7ba112916f8 0x283ffdef7422522d 0xdd6fe73233391fee 0xf7badfce6466723f

def z697 : W := mkw 0x0008095605636f80 0x64001012ac0ac6df 0x03981ffe0fe7ffff 0xfe07303ffc1fcfff

def z698 : W := mkw 0x298b0582c3818212 0xb053160b05870304 0xb98f07c3c3000005 0xaf731e0f87860000

def z699 : W := mkw 0x5fddb803fe95d867 0xc0bfbb7007fd2bb0 0xff6ff803ff19fc3b 0x9ffedff007fe33f8

def z700 : W := mkw 0x1604900000000020 0x002c092000000000 0xde9ff8fc00000007 0xffbd3ff1f8000000

def z701 : W := mkw 0x1609000368018004 0x802c120006d00300 0xbe0f0003fc01e039 0x9f7c1e0007f803c0

def z702 : W := mkw 0x09820cd404626d90 0x44130419a808c4db 0x9b9f1ffc0ce7ffff 0xff373e3ff819cfff

def z703 : W := mkw 0x202fd7ea4141a338 0xb0405fafd4828346 0xc00ffffc0001e387 0x81801ffff80003c7

def z704 : W := mkw 0x1ffefffe156b7ff8 0x6c3ffdfffc2ad6ff 0xdffffffe3fffffff 0xffbffffffc7fffff

def z705 : W := mkw 0x298b0582c3818212 0xb053160b05870304 0xb98f0703c3c00058 0x2f731e0e07878000

def z706 : W := mkw 0x0000010001000200 0x2000000200020004 0x01000700030003c4 0x2002000e00060007

def z707 : W := mkw 0x29db05c2c3d5a353 0xb053b60b8587ab46 0xbbff07c3cfffe3fd 0xff77fe0f879fffc7

def z708 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe9ff8fffce7fc7f 0xfffd3ff1fff9cff8

def z709 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xd80ffffc00000007 0x8fb01ffff8000000

def z710 : W := mkw 0x298305c0c3c0a312 0xb053060b81878146 0xb88707c1c0c0e395 0x09710e0f838181c7

def z711 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568fffe33391fef 0xf68ad1fffc66723f

def z712 : W := mkw 0x365b05c36955a355 0xb06cb60b86d2ab46 0x867f07c03c3fe3a5 0xd10cfe0f80787fc7

def z713 : W := mkw 0x298305c0c3c0a312 0xb053060b81878146 0xb98707c1c3c1e3dd 0xab730e0f838783c7

def z714 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc29ffffc0ce6007f 0xfb853ffff819cc00

def z715 : W := mkw 0x7f86bdc1bfc07b36 0x70ff0d7b837f80f6 0x4780ffc03fc01fe6 0x308f01ff807f803f

def z716 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f1fffc3c1e3df 0xaf731e3fff8783c7

def z717 : W := mkw 0x09a6d6a800000038 0x00134dad50000000 0xdb9ffffc00000007 0xffb73ffff8000000

def z718 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e70233191f80 0x048ad1ce0466323f

def z719 : W := mkw 0x367dd36ac3c1a36a 0xb06cfba6d5878346 0x6670f83fc3c1e3da 0x50cce1f07f8783c7

def z720 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb88f07c3c3c1e3dd 0x89711e0f878783c7

def z721 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xde9ffffc00000007 0x9fbd3ffff8000000

def z722 : W := mkw 0x29a366f0d2e8b592 0x985346cde1a5d16b 0xfce7e0f1f0f8fc33 0x59f9cfc1e3e1f1f8

def z723 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f0703c3c1e3dc 0xa7721e0e078783c7

def z724 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfa9ffffdccc60017 0x89f53ffffb998c00

def z725 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb8f1fc3c3c1e3df 0xbf771e3f878783c7

def z726 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x07f018fc0ce7ffff 0xfe0fe031f819cfff

def z727 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7fffe 0x70052031f819cfff

def z728 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb9f1fcfc3c1e3dd 0xaf773e3f9f8783c7

def z729 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe8ff803fcc1fc7b 0xbffd1ff007f983f8

def z730 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xddfffffc00000007 0xe5bbfffff8000000

def z731 : W := mkw 0x1ff6d6a92814007d 0x003fedad52502800 0xdffffffc30180007 0xffbffffff8603000

def z732 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0fe003fc01fc39 0x8ff81fc007f803f8

def z733 : W := mkw 0x1ff6d6a88294007b 0x003fedad51052800 0xdffffffc00c60007 0xffbffffff8018c00

def z734 : W := mkw 0x1fd00855aef66dc7 0x443fa010ab5decdb 0x3d6018fff319ff87 0x847ac031ffe633ff

def z735 : W := mkw 0x09f6d6a800000078 0x0013edad50000000 0xc5fffffc00000007 0xf78bfffff8000000

def z736 : W := mkw 0x29db05cac3c1a35a 0xb053b60b95878346 0xb99f07cfc3c1e3dd 0xaf733e0f9f8783c7

def z737 : W := mkw 0x49fb6eab7c01d85c 0xc093f6dd56f803b0 0x21f007fffc01fc3c 0x6043e00ffff803f8

def z738 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7ffd7 0xe8052031f819cfff

def z739 : W := mkw 0x09a6d6a88280003a 0x00134dad51050000 0xf98fffffc3c0005f 0xaff31fffff878000

def z740 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00011c2f 0xffbffffff8000238

def z741 : W := mkw 0x1676d6a800000078 0x002cedad50000000 0xde7ffffc00000007 0xdfbcfffff8000000

def z742 : W := mkw 0x560db9037d01da24 0xe0ac1b7206fa03b4 0xff0fff03ff01fc3b 0x9ffe1ffe07fe03f8

def z743 : W := mkw 0x1ff6defc04626df8 0x443fedbdf808c4db 0xdd6fe7000ce7fff8 0x05badfce0019cfff

def z744 : W := mkw 0x16000001aa940007 0x002c000003552800 0x3f600003fffe0078 0x7e7ec00007fffc00

def z745 : W := mkw 0x160498012c004824 0x402c093002580090 0xfe0ff803fc01fc3b 0x9ffc1ff007f803f8

def z746 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ef00003fffe0078 0x587de00007fffc00

def z747 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc21fc7b 0xfffc1ff007f843f8

def z748 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e70233391fec 0xa68ad1ce0466723f

def z749 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003ffffe079 0xfe7fe00007ffffc0

def z750 : W := mkw 0x298b25c2d3c1b312 0xb053164b85a78366 0xfd8fe7c3f3c1e3dd 0xaffb1fcf87e783c7

def z751 : W := mkw 0x09a6d6a800000038 0x00134dad50000000 0xc18ffffc00000007 0xa1831ffff8000000

def z752 : W := mkw 0x00286b66154b7b00 0x6c0050d6cc2a96f6 0x47f8ffce3fdee011 0x0c8ff1ff9c7fbdc0

def z753 : W := mkw 0x1ff86333bbbd16c7 0x283ff0c667777a2d 0x7a98e731ccc71f96 0x88f531ce63998e3f

def z754 : W := mkw 0x1fdeb59a112916f8 0x283fbd6b3422522d 0x9a9718ce33391fe9 0x09352e319c66723f

def z755 : W := mkw 0x1626d6a800000038 0x002c4dad50000000 0xda0ffffc00000007 0x89b41ffff8000000

def z756 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0xb88f07c3c0c1e3dd 0xaf711e0f878183c7

def z757 : W := mkw 0x1fd49001aa940067 0x003fa92003552800 0xffffe003fffe0078 0x7fffffc007fffc00

def z758 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003fffe0078 0x0c7fe00007fffc00

def z759 : W := mkw 0x00000001aa940007 0x0000000003552800 0x25600003fffe0078 0x044ac00007fffc00

def z760 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff0183ffffe007a 0x7e7fe0307ffffc00

def z761 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7fffd 0x68052031f819cfff

def z762 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff80703fffe007c 0xfe7ff00e07fffc00

def z763 : W := mkw 0x09a246a000000010 0x0013448d40000000 0xdffffffc00000007 0xffbffffff8000000

def z764 : W := mkw 0x0029633251299680 0xa80052c664a2532d 0xfd6fe733f3391fee 0xf7fadfce67e6723f

def z765 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffdcffe0057 0xfffffffffb9ffc00

def z766 : W := mkw 0x400db8037c01d824 0xc0801b7006f803b0 0xf80ff803fc01fc3b 0x8ff01ff007f803f8

def z767 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3f600003fffe0078 0x1e7ec00007fffc00

def z768 : W := mkw 0x098b058241018210 0xa013160b04820304 0xb98f07c3c301e3dd 0xaf731e0f878603c7

def z769 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fe3fffffff 0xfa052031fc7fffff

def z770 : W := mkw 0x1676d6a800000078 0x002cedad50000000 0xc46ffffc00000007 0x8188dffff8000000

def z771 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc46ffffc00000007 0xd188dffff8000000

def z772 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc08ffffc00000007 0xab811ffff8000000

def z773 : W := mkw 0x1fd49009aa94006f 0x003fa92013552800 0x3ff0180ffffe0078 0x7e7fe0301ffffc00

def z774 : W := mkw 0x565db8037c15d865 0xc0acbb7006f82bb0 0xfe6ff803fc19fc3b 0x9ffcdff007f833f8

def z775 : W := mkw 0x5625db316d28cea4 0xe8ac4bb662da519d 0xbb671f31cf38e3d5 0x6976ce3e639e71c7

def z776 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00000007 0x8dbffffff8000000

def z777 : W := mkw 0x0029623250299480 0x880052c464a05329 0xfc6fe033f039fc3b 0xdff8dfc067e073f8

def z778 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff000fffffe007c 0x7e7fe001fffffc00

def z779 : W := mkw 0x0020633011281680 0x280040c66022502d 0x4560e73233381fee 0x768ac1ce6466703f

def z780 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00000003 0x5dbffffff8000000

def z781 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3de00003fffe0078 0x2e7bc00007fffc00

def z782 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffff338006f 0xffffffffffe67000

def z783 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3f3f9e3fd 0xaf731e0f87e7f3c7

def z784 : W := mkw 0x09f6d6a88294007b 0x0013edad51052800 0xc1fffffc03fe0047 0xe183fffff807fc00

def z785 : W := mkw 0x1fd69ccdaed6697f 0x443fad399b5dacd2 0xba9718cdccc6e011 0x09752e319b998dc0

def z786 : W := mkw 0x560598016c00c824 0xc0ac0b3002d80190 0xfe0ff801cc01fc3b 0x9ffc1ff0039803f8

def z787 : W := mkw 0x29f247f083fc27d3 0x3853e48fe107f84f 0x01f007f003fe03c4 0x6003e00fe007fc07

def z788 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe9ff8cffc01fc3b 0x9ffd3ff19ff803f8

def z789 : W := mkw 0x0028633211291680 0x280050c66422522d 0x45e8e7f233391fef 0xfe8bd1cfe466723f

def z790 : W := mkw 0x0028633211291680 0x280050c66422522d 0x47f8fffe3fff1fff 0xfe8ff1fffc7ffe3f

def z791 : W := mkw 0x298b05c2c3d5a313 0xb053160b8587ab46 0xb98f07c3c3ffe3dd 0xaf731e0f8787ffc7

def z792 : W := mkw 0x0020423000200480 0x0000408460004009 0x4568e73233391fee 0xf68ad1ce6466723f

def z793 : W := mkw 0x298b0d96c7a3ce92 0xf453161b2d8f479d 0xbb1f1f3fcf261c22 0x55763e3e7f9e4c38

def z794 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc20ffffc00000007 0x9b841ffff8000000

def z795 : W := mkw 0x402dfb76556bffa0 0xec805bf6ecaad7ff 0xc00ffffc0001ff87 0x81801ffff80003ff

def z796 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff018cffffe0079 0x7e7fe0319ffffc00

def z797 : W := mkw 0x560db0577863b5a4 0x84ac1b60aef0c76b 0xfc9fe0fff0e603c4 0x65f93fc1ffe1cc07

def z798 : W := mkw 0x09d00001aa940047 0x0013a00003552800 0x25f00003fffe0078 0x764be00007fffc00

def z799 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4560e73233391fee 0x708ac1ce6466723f

def z800 : W := mkw 0x0026d6a9aa94003f 0x00004dad53552800 0xe00ffffffffe007f 0x81c01ffffffffc00

def z801 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xd80ffffc00000007 0x81b01ffff8000000

def z802 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e7323fff1ffe 0xf68ad1ce647ffe3f

def z803 : W := mkw 0x1626d6a800000038 0x002c4dad50000000 0xdf6ffffc00000007 0xffbedffff8000000

def z804 : W := mkw 0x16500001aa940047 0x002ca00003552800 0x3e700003fffe0078 0x5e7ce00007fffc00

def z805 : W := mkw 0x1fd69489aa94007f 0x003fad2913552800 0xfffff8cffffe007b 0xfffffff19ffffc00

def z806 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0fe003fc01fc38 0x1ffc1fc007f803f8

def z807 : W := mkw 0x5605b8017c00d824 0xc0ac0b7002f801b0 0xfe0ff801fc00fc33 0x9ffc1ff003f801f8

def z808 : W := mkw 0x00000001aa940007 0x0000000003552800 0x21600003fffe0078 0x6042c00007fffc00

def z809 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xff0ff803ff01fc7b 0xbffe1ff007fe03f8

def z810 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233191fce 0xa68ad1ce6466323f

def z811 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdefffffc00000007 0xd9bdfffff8000000

def z812 : W := mkw 0x1676d6a800000078 0x002cedad50000000 0xc6fffffc00000007 0xfb8dfffff8000000

def z813 : W := mkw 0x0029433241298680 0xa80052866482530d 0xb96f0733c339e3dd 0xef72de0e678673c7

def z814 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c1e3d9 0x0d731e0f878783c7

def z815 : W := mkw 0x49ddb802d695d863 0xc093bb7005ad2bb0 0xc1fff80003fffc43 0xe183fff00007fff8

def z816 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe8ff8c3fc01fc3f 0xbffd1ff187f803f8

def z817 : W := mkw 0x1ff6d6a88280007a 0x003fedad51050000 0xfffffffff3f8007f 0xffffffffffe7f000

def z818 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0xb80f07c3c001e385 0x85701e0f878003c7

def z819 : W := mkw 0x0028633211291680 0x280050c66422522d 0x45f8e73233ff1fee 0xf68bf1ce6467fe3f

def z820 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc0020006f 0xffbffffff8004000

def z821 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0fe003fc01fc3a 0x97f81fc007f803f8

def z822 : W := mkw 0x1626d6a800000038 0x002c4dad50000000 0xdc0ffffc00000007 0x85b81ffff8000000

def z823 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffff3fe0047 0xffffffffffe7fc00

def z824 : W := mkw 0x000928025401d800 0xc000125004a803b0 0xfe0ff803fc01fc3b 0x9ffc1ff007f803f8

def z825 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3e1e3fd 0xff731e0f8787c3c7

def z826 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb88f07c1c0c1e3dd 0xab711e0f838183c7

def z827 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98707c3c3c1e3dd 0x29730e0f878783c7

def z828 : W := mkw 0x565db8037c15d865 0xc0acbb7006f82bb0 0xff7ff803ff3ffc7b 0xfffefff007fe7ff8

def z829 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7ffe7 0xf0052031f819cfff

def z830 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb9f1fffcfe7e3ff 0xff773e3fff9fcfc7

def z831 : W := mkw 0x0029633251299680 0xa80052c664a2532d 0xc56fe7323339ffef 0xf78adfce646673ff

def z832 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c1ffff 0xbf731e0f878783ff

def z833 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb99f07c3c3e7e3dd 0xef733e0f8787cfc7

def z834 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb9ef07c3c3f9e3dd 0xef73de0f8787f3c7

def z835 : W := mkw 0x09f6d6a800000078 0x0013edad50000000 0xc16ffffc00000007 0x8182dffff8000000

def z836 : W := mkw 0x1626d6a92800003c 0x002c4dad52500000 0xfe0ffffffc00003f 0x9ffc1ffffff80000

def z837 : W := mkw 0x560db8025401d820 0xc0ac1b7004a803b0 0xfe0ff803c001fc1b 0x9ffc1ff0078003f8

def z838 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xdffffffc3ffe0067 0xffbffffff87ffc00

def z839 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x06f018fc3cffffff 0xfa0de031f879ffff

def z840 : W := mkw 0x1ff6d6a92800007c 0x003fedad52500000 0xdffffffc3c000027 0xffbffffff8780000

def z841 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc30380027 0xffbffffff8607000

def z842 : W := mkw 0x560db9037d01da24 0xe0ac1b7206fa03b4 0xfe0fff03fc01ffbf 0x9ffc1ffe07f803ff

def z843 : W := mkw 0x1fd20481aa940057 0x003fa40903552800 0xbfff0703fffe0078 0x7f7ffe0e07fffc00

def z844 : W := mkw 0x1f86948000000030 0x003f0d2900000000 0xdf9ffffc00000007 0xffbf3ffff8000000

def z845 : W := mkw 0x098b04c24041a110 0x8013160984808342 0xb98f07c3c0c1e3dd 0xaf731e0f878183c7

def z846 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00c0005f 0xffbffffff8018000

def z847 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f07c3c301e3cd 0xa7721e0f878603c7

def z848 : W := mkw 0x0028633211291680 0x280050c66422522d 0x45f8e7fe33391fee 0xf68bf1cffc66723f

def z849 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffe3ffe007f 0xffbffffffc7ffc00

def z850 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f0703c301e380 0x05721e0e078603c7

def z851 : W := mkw 0x1ff6d6a92814007d 0x003fedad52502800 0xfffffffffc3e003f 0xfffffffffff87c00

def z852 : W := mkw 0x29db05c2c3d5a353 0xb053b60b8587ab46 0xb9ef07c3c3d9e3dd 0xaf73de0f8787b3c7

def z853 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0cc7ffdf 0xaa052031f8198fff

def z854 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc01fc39 0x0dfc1ff007f803f8

def z855 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233391fea 0x548ad1ce6466723f

def z856 : W := mkw 0x1fd49001aa940067 0x003fa92003552800 0x7ff0f803fffe007a 0x7effe1f007fffc00

def z857 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffe0300004f 0xffbffffffc060000

def z858 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00033fffe007e 0xfe7fe00067fffc00

def z859 : W := mkw 0x298b25c2d3c9b312 0xb853164b85a79366 0xb98f07c3f3d9e3dd 0xaf731e0f87e7b3c7

def z860 : W := mkw 0x16500001aa940047 0x002ca00003552800 0x26f00003fffe0078 0x7a4de00007fffc00

def z861 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c1e3c5 0xa5731e0f878783c7

def z862 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233391fa6 0xd48ad1ce6466723f

def z863 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xffffffffff18003f 0xfffffffffffe3000

def z864 : W := mkw 0x1674da3d2c364ced 0x442ce9b47a586c99 0x4670f83c3c3e1c22 0x508ce1f078787c38

def z865 : W := mkw 0x09800001aa940007 0x0013000003552800 0x3de00003fffe0078 0x7e7bc00007fffc00

def z866 : W := mkw 0x298a25c293c13312 0x3053144b85278266 0x4588e7c233c11fee 0xb68b11cf8467823f

def z867 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc29ffffc00000007 0x89853ffff8000000

def z868 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb88f07c3c0c1e39d 0x8f711e0f878183c7

def z869 : W := mkw 0x29a247f083e82792 0x3853448fe107d04f 0x018007f003c003c4 0x2003000fe0078007

def z870 : W := mkw 0x0076d6a800000078 0x0000edad50000000 0xc07ffffc00000007 0xc180fffff8000000

def z871 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0xb90f07c3c301e3dd 0xaf721e0f878603c7

def z872 : W := mkw 0x1626d6a800000038 0x002c4dad50000000 0xc60ffffc00000007 0x918c1ffff8000000

def z873 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f07c3c3c1e3dd 0x85721e0f878783c7

def z874 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0ff803fc01fc3b 0x85f81ff007f803f8

def z875 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7ffff 0x88052031f819cfff

def z876 : W := mkw 0x1676d6a92814007d 0x002cedad52502800 0xc67ffffc3c3e0027 0xd18cfffff8787c00

def z877 : W := mkw 0x1ff6d6a92800007c 0x003fedad52500000 0xfffffffdcc000017 0xfffffffffb980000

def z878 : W := mkw 0x09a6d6a800000038 0x00134dad50000000 0xd88ffffc00000007 0x89b11ffff8000000

def z879 : W := mkw 0x1624d22000000020 0x002c49a440000000 0xdffffffc00000007 0xffbffffff8000000

def z880 : W := mkw 0x400929577d6bff84 0xec801252aefad7ff 0x20000003fffffff8 0x0040000007ffffff

def z881 : W := mkw 0x560db9037d09da24 0xe8ac1b7206fa13b4 0xfe0ff803ff19fc3b 0x9ffc1ff007fe33f8

def z882 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff01803fffe007b 0xfe7fe03007fffc00

def z883 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc00ffffc00000007 0xf3801ffff8000000

def z884 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb80f07c1c001e385 0x81701e0f838003c7

def z885 : W := mkw 0x1ff6d6a88294007b 0x003fedad51052800 0xffffffffc3fe005f 0xffffffffff87fc00

def z886 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffe33180007 0xffbffffffc663000

def z887 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233381fe6 0x748ad1ce6466703f

def z888 : W := mkw 0x09f246fc82f625db 0x0413e48df905ec4b 0x01f007fc03fe03c4 0x6003e00ff807fc07

def z889 : W := mkw 0x565db8037c01d864 0xc0acbb7006f803b0 0xfe7ff803fc01fc3b 0xdffcfff007f803f8

def z890 : W := mkw 0x09d00001aa940047 0x0013a00003552800 0x21600003fffe0078 0x0042c00007fffc00

def z891 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0xbfff0003fffe0079 0xff7ffe0007fffc00

def z892 : W := mkw 0x202b6ff6556bff90 0xfc4056dfecaad7ff 0xc00ffffc0001ff87 0x81801ffff80003ff

def z893 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0ff803f001fc2b 0x97f81ff007e003f8

def z894 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xfc0ff803f001fc3b 0x9ff81ff007e003f8

def z895 : W := mkw 0x09890102c3818202 0xa013120205870304 0xb98f0703c3c1e3dd 0xaf731e0e078783c7

def z896 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c1c0c1e395 0xaf731e0f838183c7

def z897 : W := mkw 0x298b05c24141a310 0xb053160b84828346 0xb98f07c3c001e39d 0xaf731e0f878003c7

def z898 : W := mkw 0x1ff6d6a88294007b 0x003fedad51052800 0xdffffffc0ffe007f 0xffbffffff81ffc00

def z899 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff000c3fffe007d 0xfe7fe00187fffc00

def z900 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdf7ffffc00000007 0xd5befffff8000000

def z901 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe1ff83ffc01fc3b 0xdffc3ff07ff803f8

def z902 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc01fc13 0x8dfc1ff007f803f8

def z903 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc01ffff 0xbffc1ff007f803ff

def z904 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc0c00003f 0xffbffffff8180000

def z905 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfffff803fffffc7b 0xfffffff007fffff8

def z906 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x03f018fc0fffffff 0xfa07e031f81fffff

def z907 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4768ff3233391fef 0xfe8ed1fe6466723f

def z908 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c1e3dc 0x25731e0f878783c7

def z909 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x069018fe3ce7ffff 0xfe0d2031fc79cfff

def z910 : W := mkw 0x1609200378019004 0x802c124006f00320 0xfe0fe003fc01fc3b 0x9ffc1fc007f803f8

def z911 : W := mkw 0x1ff6d6a92800007c 0x003fedad52500000 0xfffffffffce6007f 0xfffffffffff9cc00

def z912 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233391fec 0x648ad1ce6466723f

def z913 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0ff803f001fc1b 0x8ff81ff007e003f8

def z914 : W := mkw 0x0020633011281680 0x280040c66022502d 0x4560e73033391fee 0xf28ac1ce6066723f

def z915 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73033391fe6 0xf08ad1ce6066723f

def z916 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbfff07c3ffffe3fd 0xff7ffe0f87ffffc7

def z917 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4768e7323f391ffe 0xfe8ed1ce647e723f

def z918 : W := mkw 0x400928037c01d804 0xc080125006f803b0 0xfc0fe003fc01fc3b 0x9ff81fc007f803f8

def z919 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f0703c3c1e3d8 0x2f731e0e078783c7

def z920 : W := mkw 0x1ff6d6a800140079 0x003fedad50002800 0xdffffffc003e0007 0xffbffffff8007c00

def z921 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803f001fc03 0x9ffc1ff007e003f8

def z922 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff801fc01fc33 0x99fc1ff003f803f8

def z923 : W := mkw 0x1ff6d6a9aa80007e 0x003fedad53550000 0xffffffffffc0007f 0xffffffffffff8000

def z924 : W := mkw 0x09a6d6a800000038 0x00134dad50000000 0xddeffffc00000007 0xffbbdffff8000000

def z925 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xddeffffc00000007 0xafbbdffff8000000

def z926 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3bf00003fffe0078 0x6877e00007fffc00

def z927 : W := mkw 0x298305c0c3c0a312 0xb053060b81878146 0xb98f07c1c3c0e3d5 0xaf731e0f838781c7

def z928 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff833fc01fc3f 0xfffc1ff067f803f8

def z929 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xf80ff801c001fc03 0x81f01ff0038003f8

def z930 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xf80ff801c001fc13 0x89f01ff0038003f8

def z931 : W := mkw 0x00500001aa940047 0x0000a00003552800 0x20700003fffe0078 0x4040e00007fffc00

def z932 : W := mkw 0x298b0582c3818212 0xb053160b05870304 0xb90f0703c301e3dd 0xaf721e0e078603c7

def z933 : W := mkw 0x5674fa313c3c5ce5 0x48ace9f4627878b9 0x4670f8303c3e1c22 0x508ce1f060787c38

def z934 : W := mkw 0x7fd79cc1eed4e977 0xd0ffaf3983dda9d2 0xba9718c1ccc6e011 0x09752e3183998dc0

def z935 : W := mkw 0x1ff6d6a88294007b 0x003fedad51052800 0xdffffffc03180007 0xffbffffff8063000

def z936 : W := mkw 0x560db8037c15d825 0xc0ac1b7006f82bb0 0xfe0ff803fc3ffc3b 0x9ffc1ff007f87ff8

def z937 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803ff39fc7b 0x9ffc1ff007fe73f8

def z938 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb8f07c3cfc1e3fd 0xbf771e0f879f83c7

def z939 : W := mkw 0x1fd49001aa940067 0x003fa92003552800 0xfffff8fffffe007f 0xfffffff1fffffc00

def z940 : W := mkw 0x298b25c2d3c1b312 0xb053164b85a78366 0xfdefe7c3f3f9ffff 0xfffbdfcf87e7f3ff

def z941 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfa0ff803fc01fc3b 0x89f41ff007f803f8

def z942 : W := mkw 0x09f6d6a800000078 0x0013edad50000000 0xd9fffffc00000007 0xefb3fffff8000000

def z943 : W := mkw 0x0028633211291680 0x280050c66422522d 0x7d68e733f3391ffe 0xfefad1ce67e6723f

def z944 : W := mkw 0x1fa6d6a800000038 0x003f4dad50000000 0xdf8ffffc00000007 0xbfbf1ffff8000000

def z945 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb9f07c3cfc7e3dd 0xaf773e0f879f8fc7

def z946 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfd6ffffff3180007 0x85fadfffffe63000

def z947 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003fffe0030 0x5c7fe00007fffc00

def z948 : W := mkw 0x5605b8017c00d824 0xc0ac0b7002f801b0 0xfe07f801fc01fc3b 0x9bfc0ff003f803f8

def z949 : W := mkw 0x1ff6d6a92800007c 0x003fedad52500000 0xfffffffff0000007 0xffffffffffe00000

def z950 : W := mkw 0x0009010241018200 0xa000120204820304 0xb80f0703c001e39d 0x8f701e0e078003c7

def z951 : W := mkw 0x160db00250019020 0x802c1b6004a00320 0xfe0ff803f001fc3b 0x9ffc1ff007e003f8

def z952 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc01fc3a 0x15fc1ff007f803f8

def z953 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdd6ffffc00000007 0xf7badffff8000000

def z954 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc16ffffc00000007 0xe182dffff8000000

def z955 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07f3c3c1e3df 0xff731e0fe78783c7

def z956 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc000103cf 0xffbffffff8000207

def z957 : W := mkw 0x29db05c2c3d5a353 0xb053b60b8587ab46 0xbdff07c3f3ffe3fd 0xff7bfe0f87e7ffc7

def z958 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb99f07ffc3c1e3dd 0xef733e0fff8783c7

def z959 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f0703c3c1e3d9 0x8f721e0e078783c7

def z960 : W := mkw 0x298b25c2d3c1b312 0xb053164b85a78366 0xb98f07c3f3c1fffd 0xaf731e0f87e783ff

def z961 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffdcce6007f 0xfffffffffb99cc00

def z962 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x7ff8e003fffe007a 0xfefff1c007fffc00

def z963 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xff6ff803fc01fc3b 0xfffedff007f803f8

def z964 : W := mkw 0x298b25c2d3c1b312 0xb053164b85a78366 0xf98fe7c3c3c1ffdf 0xaff31fcf878783ff

def z965 : W := mkw 0x200b05c2c3c1a312 0xb040160b85878346 0xb80f07c3c3c1e3dd 0x8f701e0f878783c7

def z966 : W := mkw 0x1fd69489aa94007f 0x003fad2913552800 0xbff70003fffe0078 0x7f7fee0007fffc00

def z967 : W := mkw 0x60092957ffe3ff86 0xf4c01252afffc7ff 0x20000003ffe7fff8 0x0040000007ffcfff

def z968 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff8fffc01fc3f 0x9ffc1ff1fff803f8

def z969 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003fffe0050 0x6c7fe00007fffc00

def z970 : W := mkw 0x565db8037c15d865 0xc0acbb7006f82bb0 0xfe1ff803fc07fc3b 0x9ffc3ff007f80ff8

def z971 : W := mkw 0x1ff6d6a88294007b 0x003fedad51052800 0xdffffffe33fe006f 0xffbffffffc67fc00

def z972 : W := mkw 0x000901424141a300 0xa000120284828346 0xb98f07c3c3c1e3dd 0xaf731e0f878783c7

def z973 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233391fee 0x848ad1ce6466723f

def z974 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc09ffffc00000007 0xe1813ffff8000000

def z975 : W := mkw 0x1fd20481aa940057 0x003fa40903552800 0x3ff007c3fffe007c 0x7e7fe00f87fffc00

def z976 : W := mkw 0x29db05c2c3d5a353 0xb053b60b8587ab46 0xb99f07c3c3c7e3dd 0xaf733e0f87878fc7

def z977 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003fffe0060 0x747fe00007fffc00

def z978 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0cc7ff97 0xfa052031f8198fff

def z979 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00e60047 0xffbffffff801cc00

def z980 : W := mkw 0x1626d6a800000038 0x002c4dad50000000 0xde9ffffc00000007 0xffbd3ffff8000000

def z981 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe6ff803fc39fc3b 0xdffcdff007f873f8

def z982 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4778ff3e33391fee 0xf68ef1fe7c66723f

def z983 : W := mkw 0x560db9037d01da24 0xe0ac1b7206fa03b4 0xfe0ff803ff01fffb 0x9ffc1ff007fe03ff

def z984 : W := mkw 0x0009200250019000 0x8000124004a00320 0xf80fe003c001fc1b 0x8ff01fc0078003f8

def z985 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3f700003fffe0078 0x547ee00007fffc00

def z986 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffdfcfe0037 0xfffffffffbf9fc00

def z987 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdf6ffffc00000007 0x9fbedffff8000000

def z988 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc00fc33 0x1dfc1ff007f801f8

def z989 : W := mkw 0x098204c082c02112 0x0013040981058042 0xb98f07c3c3c1e3dd 0xaf731e0f878783c7

def z990 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffdc0000007 0xfffffffffb800000

def z991 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e70233391fe8 0x768ad1ce0466723f

def z992 : W := mkw 0x1ff6d6a88280007a 0x003fedad51050000 0xdffffffc03c00047 0xffbffffff8078000

def z993 : W := mkw 0x1fd20481aa940057 0x003fa40903552800 0xbff700c3fffe0079 0x7f7fee0187fffc00

def z994 : W := mkw 0x20090142c3c1a302 0xb040120285878346 0xb90f0703c3c1e3dd 0xaf721e0e078783c7

def z995 : W := mkw 0x09f6d6a800000078 0x0013edad50000000 0xc3fffffc00000007 0xfb87fffff8000000

def z996 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xffffffffff3e0027 0xfffffffffffe7c00

def z997 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc21ffffc00000007 0xd1843ffff8000000

def z998 : W := mkw 0x00286336112b1680 0x2c0050c66c22562d 0x4578e73e333f1fee 0xf68af1ce7c667e3f

def z999 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xda9ffffc00000007 0xfbb53ffff8000000

def z1000 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7ffb7 0xd8052031f819cfff

def z1001 : W := mkw 0x1ff6d6a92800007c 0x003fedad52500000 0xffffffffff38007f 0xfffffffffffe7000

def z1002 : W := mkw 0x09d00001aa940047 0x0013a00003552800 0x39f00003fffe0078 0x6e73e00007fffc00

def z1003 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fc01fc23 0x95fc1ff007f803f8

def z1004 : W := mkw 0x1676d6a800000078 0x002cedad50000000 0xc21ffffc00000007 0x81843ffff8000000

def z1005 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xffffffffcfc6005f 0xffffffffff9f8c00

def z1006 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc56ffffc00000007 0x858adffff8000000

def z1007 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3d600003fffe0078 0x767ac00007fffc00

def z1008 : W := mkw 0x09a6d6a800000038 0x00134dad50000000 0xd90ffffc00000007 0x85b21ffff8000000

def z1009 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xf80ff803c001fc03 0x85f01ff0078003f8

def z1010 : W := mkw 0x5605b8017c00d824 0xc0ac0b7002f801b0 0xfe07f803fc00fc3b 0x1ffc0ff007f801f8

def z1011 : W := mkw 0x29f247f883e827da 0x3853e48ff107d04f 0x01f007fc03f803c4 0x6003e00ff807f007

def z1012 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xffffffffc000001f 0xffffffffff800000

def z1013 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e7323339ffff 0xfe8ad1ce646673ff

def z1014 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x3a9018ffcce7ffff 0xfe752031ff99cfff

def z1015 : W := mkw 0x0020633011281680 0x280040c66022502d 0x4568e73033381fe6 0xf68ad1ce6066703f

def z1016 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xc7fffffc00000007 0xf18ffffff8000000

def z1017 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003ffff1c7a 0xfe7fe00007fffe38

def z1018 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00000006 0x75bffffff8000000

def z1019 : W := mkw 0x29db05c2c3c1a352 0xb053b60b85878346 0xb9ff07c3c3c1e3dd 0xef73fe0f878783c7

def z1020 : W := mkw 0x5624fa313c285ca4 0x48ac49f4627850b9 0x4600f8303c001c22 0x108c01f060780038

def z1021 : W := mkw 0x200b05c24141a310 0xb040160b84828346 0xb80f07c1c001e395 0x89701e0f838003c7

def z1022 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xffffffffffde0017 0xffffffffffffbc00

def z1023 : W := mkw 0x1fd20481aa940057 0x003fa40903552800 0xbfff1ffffffe007f 0xff7ffe3ffffffc00

def z1024 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233191f86 0xf68ad1ce6466323f

def z1025 : W := mkw 0x560db9037d01da24 0xe0ac1b7206fa03b4 0xff6fff03ff39ffff 0xfffedffe07fe73ff

def z1026 : W := mkw 0x29f247fc83e227da 0x3453e48ff907c44f 0x01f007fc03e603c4 0x6003e00ff807cc07

def z1027 : W := mkw 0x1ff6d6a92814007d 0x003fedad52502800 0xdffffffc0c060007 0xffbffffff8180c00

def z1028 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c0e3d5 0x2d731e0f878781c7

def z1029 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x9a9f18fc0ce7ffff 0xff353e31f819cfff

def z1030 : W := mkw 0x1fd69489aa94007f 0x003fad2913552800 0xbfff1fcffffe007d 0xff7ffe3f9ffffc00

def z1031 : W := mkw 0x298b05c6c3c3a312 0xb453160b8d878746 0xb99f07cfc3c7e3dd 0xaf733e0f9f878fc7

def z1032 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdbfffffc00000007 0xe9b7fffff8000000

def z1033 : W := mkw 0x5674fa393c285cec 0x48ace9f4727850b9 0x4670f83c3c381c22 0x508ce1f078787038

def z1034 : W := mkw 0x5605b8017c00d824 0xc0ac0b7002f801b0 0xfa07f801cc00fc13 0x09f40ff0039801f8

def z1035 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe9ff803fcc7fc3b 0x9ffd3ff007f98ff8

def z1036 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfa0ff801cc01fc3b 0x9bf41ff0039803f8

def z1037 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x4698f8fc0ce7ffff 0xfe8d31f1f819cfff

def z1038 : W := mkw 0x0980000082800002 0x0013000001050000 0x3ff00003fffe0078 0x7e7fe00007fffc00

def z1039 : W := mkw 0x1676d6a800000078 0x002cedad50000000 0xc77ffffc00000007 0xf78efffff8000000

def z1040 : W := mkw 0x0028633211291680 0x280050c66422522d 0x47f8e73233391fee 0xfe8ff1ce6466723f

def z1041 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4778e7323f3f1fee 0xf68ef1ce647e7e3f

def z1042 : W := mkw 0x09d00001aa940047 0x0013a00003552800 0x23f00003fffe0078 0x7a47e00007fffc00

def z1043 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x27f00003fffe0078 0x704fe00007fffc00

def z1044 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233391fc6 0xe48ad1ce6466723f

def z1045 : W := mkw 0x20092956d7ebff82 0xfc401252adafd7ff 0x20000003fffffff8 0x0040000007ffffff

def z1046 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe1ff803fc27fc3b 0xdffc3ff007f84ff8

def z1047 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e73233191fae 0x968ad1ce6466323f

def z1048 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc40ffffc00000007 0x97881ffff8000000

def z1049 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfc0fe003f001fc00 0x05f81fc007e003f8

def z1050 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbd8f07c3f3c1e3fd 0xbf7b1e0f87e783c7

def z1051 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc03380047 0xffbffffff8067000

def z1052 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbdef07c3f3d9e3dd 0xaf7bde0f87e7b3c7

def z1053 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc0cc60017 0xffbffffff8198c00

def z1054 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xfd8fe7c3c3c1e3df 0xbffb1fcf878783c7

def z1055 : W := mkw 0x5674fa3d3c225cec 0x44ace9f47a7844b9 0x4670f83c3c261c22 0x508ce1f078784c38

def z1056 : W := mkw 0x29a247f483ea2792 0x3c53448fe907d44f 0x01f007fc03fe03c4 0x6003e00ff807fc07

def z1057 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbb9f07c3c3c1e3dd 0xff773e0f878783c7

def z1058 : W := mkw 0x565db80b7c01d86c 0xc0acbb7016f803b0 0xfe1ff80ffc01fc3b 0x9ffc3ff01ff803f8

def z1059 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdb9ffffc00000007 0xafb73ffff8000000

def z1060 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c1c3c1e3d5 0xa9731e0f838783c7

def z1061 : W := mkw 0x1fd20489aa94005f 0x003fa40913552800 0x3ff000cffffe0078 0x7e7fe0019ffffc00

def z1062 : W := mkw 0x565db8037c15d865 0xc0acbb7006f82bb0 0xfefff803fcfffc7b 0xfffdfff007f9fff8

def z1063 : W := mkw 0x0028633211291680 0x280050c66422522d 0xdd6fe73233391fef 0xffbadfce6466723f

def z1064 : W := mkw 0x0028632211091200 0x280050c644221224 0x4568e70233191fee 0xb68ad1ce0466323f

def z1065 : W := mkw 0x0008210211011200 0x2000104204220224 0x4568e70233391fee 0xf68ad1ce0466723f

def z1066 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc7fffffc00000007 0xff8ffffff8000000

def z1067 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffe3000002f 0xffbffffffc600000

def z1068 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x039018fe0fe7ffff 0xfe072031fc1fcfff

def z1069 : W := mkw 0x00000001aa940007 0x0000000003552800 0x24600003fffe0078 0x5048c00007fffc00

def z1070 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c301e385 0xaf731e0f878603c7

def z1071 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3ff00003ffff03fc 0xfe7fe00007fffe07

def z1072 : W := mkw 0x560db00378019024 0x80ac1b6006f00320 0xfc0fe003f001fc3b 0x9ff81fc007e003f8

def z1073 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff803fce7fc7b 0x9ffc1ff007f9cff8

def z1074 : W := mkw 0x5624fa353c2a5ca4 0x4cac49f46a7854b9 0x4670f83c3c3e1c22 0x508ce1f078787c38

def z1075 : W := mkw 0x16500001aa940047 0x002ca00003552800 0x27700003fffe0078 0x764ee00007fffc00

def z1076 : W := mkw 0x1600000128000004 0x002c000002500000 0x3ff00003fffe0078 0x7e7fe00007fffc00

def z1077 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb90f07c3c301e39d 0x8f721e0f878603c7

def z1078 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xff0fff03fc01fc3f 0xbffe1ffe07f803f8

def z1079 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffffcc6003f 0xfffffffffff98c00

def z1080 : W := mkw 0x1ff6d6a88280007a 0x003fedad51050000 0xffffffffcfe6007f 0xffffffffff9fcc00

def z1081 : W := mkw 0x1fd00001aa940047 0x003fa00003552800 0x3df00003fffe0078 0x647be00007fffc00

def z1082 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xbdef07c3c3c1e3dd 0xff7bde0f878783c7

def z1083 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0cc7ffbf 0x9a052031f8198fff

def z1084 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x03981ffc0ce7ffff 0xfe07303ff819cfff

def z1085 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3c3c1e395 0x8d731e0f878783c7

def z1086 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc00000005 0x6dbffffff8000000

def z1087 : W := mkw 0x0028633211291680 0x280050c66422522d 0x45e8e73233f91ffe 0xfe8bd1ce6467f23f

def z1088 : W := mkw 0x400db8025401d820 0xc0801b7004a803b0 0xfa0ff803cc01fc3b 0x9ff41ff0079803f8

def z1089 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc0001e01f 0xffbffffff80003c0

def z1090 : W := mkw 0x298305c0c3c0a312 0xb053060b81878146 0xb98707c3c3c0e3dd 0x2f730e0f878781c7

def z1091 : W := mkw 0x1fd49001aa940067 0x003fa92003552800 0xbff71803fffe0079 0x7f7fee3007fffc00

def z1092 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc10ffffc00000007 0xa7821ffff8000000

def z1093 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe0ff801cc01fc13 0x9ffc1ff0039803f8

def z1094 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe9ff803fc01fc3b 0xfffd3ff007f803f8

def z1095 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfe07f803fc01fc3b 0x19fc0ff007f803f8

def z1096 : W := mkw 0x09f6d6a800000078 0x0013edad50000000 0xc09ffffc00000007 0x81813ffff8000000

def z1097 : W := mkw 0x0029633251299680 0xa80052c664a2532d 0x6568e733f339fffe 0xf6cad1ce67e673ff

def z1098 : W := mkw 0x0028633211291680 0x280050c66422522d 0x4568e70233391fea 0x968ad1ce0466723f

def z1099 : W := mkw 0x560cb9033d015a24 0x60ac1972067a02b4 0x4708ff023f011fee 0xb68e11fe047e023f

def z1100 : W := mkw 0x1fd69481aa940077 0x003fad2903552800 0xffffffc3fffe007f 0xffffffff87fffc00

def z1101 : W := mkw 0x298304c0c2c0a112 0x9053060981858142 0xb98f07c1c0c1e3dd 0xaf731e0f838183c7

def z1102 : W := mkw 0x1ff6d6a88280007a 0x003fedad51050000 0xfffffffdc0c00017 0xfffffffffb818000

def z1103 : W := mkw 0x298b05c2c3c1a312 0xb053160b85878346 0xb98f07c3cfe7e3fd 0xaf731e0f879fcfc7

def z1104 : W := mkw 0x0000085404626d80 0x44000010a808c4db 0x029018fc0ce7fffb 0x58052031f819cfff

def z1105 : W := mkw 0x560db8077c03d824 0xc4ac1b700ef807b0 0xfe1ff80ffc07fc3b 0x9ffc3ff01ff80ff8

def z1106 : W := mkw 0x1ff6d6a9aa94007f 0x003fedad53552800 0xfffffffff3d8005f 0xffffffffffe7b000

def z1107 : W := mkw 0x1ff6d6a92814007d 0x003fedad52502800 0xdffffffc3cfe007f 0xffbffffff879fc00

def z1108 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xfa0ff803cc01fc1b 0x8ff41ff0079803f8

def z1109 : W := mkw 0x1ff6d6a88280007a 0x003fedad51050000 0xffffffffc3000007 0xffffffffff860000

def z1110 : W := mkw 0x00000001aa940007 0x0000000003552800 0x27f00003fffe0078 0x7e4fe00007fffc00

def z1111 : W := mkw 0x1ff6d6a800000078 0x003fedad50000000 0xdffffffc0c260027 0xffbffffff8184c00

def z1112 : W := mkw 0x1fd69489aa94007f 0x003fad2913552800 0xbff718fffffe007f 0xff7fee31fffffc00

def z1113 : W := mkw 0x160d98024401c820 0xc02c1b3004880390 0xfe0ff803cc01fc3b 0x9ffc1ff0079803f8

def z1114 : W := mkw 0x16500001aa940047 0x002ca00003552800 0x24600003fffe0078 0x0048c00007fffc00

def z1115 : W := mkw 0x0026d6a800000038 0x00004dad50000000 0xc56ffffe3338006f 0xf78adffffc667000

def z1116 : W := mkw 0x560db8037c01d824 0xc0ac1b7006f803b0 0xff6ff803ff19fc3b 0x9ffedff007fe33f8

def z1117 : W := mkw 0x1ff6d6a92814007d 0x003fedad52502800 0xdffffffe3f3e006f 0xffbffffffc7e7c00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z8,z6]),(0,[z7,z9,z1,z3,z4,z5,z6]),(0,[z7,z10,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z11,z6]),(0,[z7,z1,z3,z4,z5,z6,z12]),(0,[z7,z1,z13,z3,z4,z5,z6])],[(0,[z7,z1,z3,z14,z4,z5,z6]),(0,[z15,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z16,z3,z4,z5,z6]),(0,[z7,z1,z17,z3,z4,z18,z6]),(0,[z7,z1,z3,z19,z4,z5,z6])],[(0,[z7,z20,z20,z1,z3,z5,z6]),(1,[z7,z1,z21,z3,z5,z22])],[(0,[z23,z7,z1,z24,z4,z5,z6]),(0,[z7,z25,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z27]),(0,[z7,z1,z28,z3,z4,z5,z6]),(1,[z7,z1,z29,z4,z5,z6])],[(0,[z7,z1,z3,z30,z4,z5,z6]),(0,[z7,z31,z1,z4,z26,z5,z6]),(0,[z7,z1,z3,z3,z26,z5,z6]),(1,[z7,z1,z3,z32,z5,z6])],[(0,[z33,z7,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z3,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z34]),(0,[z7,z1,z3,z4,z35,z5,z6])]],
   [[(0,[z36,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z4,z26,z5,z37,z6]),(0,[z7,z1,z38,z3,z4,z5,z39])],[(0,[z7,z20,z1,z3,z40,z5,z6]),(0,[z7,z41,z1,z3,z4,z5,z6]),(0,[z7,z1,z42,z3,z4,z5,z6]),(0,[z43,z7,z1,z3,z4,z5,z6])],[(0,[z7,z44,z1,z3,z4,z5,z6]),(0,[z45,z1,z3,z4,z5,z46,z6]),(0,[z7,z1,z47,z4,z48,z5,z6]),(0,[z49,z7,z1,z3,z4,z5,z6])],[(0,[z50,z7,z1,z3,z4,z5,z6]),(0,[z7,z51,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z52,z6]),(0,[z53,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z54,z3,z5,z55,z6])],[(0,[z7,z1,z56,z3,z4,z5,z6]),(0,[z57,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z58]),(0,[z59,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z60,z6]),(0,[z7,z1,z3,z4,z61,z5,z62]),(0,[z7,z1,z3,z4,z5,z6,z63])],[(0,[z7,z1,z64,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z65,z5,z6]),(0,[z7,z66,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z18,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z67]),(0,[z7,z1,z3,z68,z4,z5,z6])],[(0,[z69,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z70,z6]),(0,[z71,z7,z1,z3,z72,z5,z6]),(0,[z7,z1,z3,z4,z5,z73,z6]),(0,[z7,z1,z3,z4,z5,z6,z74])]],
   [[(0,[z75,z7,z1,z3,z4,z76,z6]),(0,[z7,z1,z77,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z78,z5,z6]),(0,[z7,z1,z79,z3,z4,z5,z6]),(0,[z80,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z81]),(0,[z7,z1,z3,z82,z4,z5,z6])],[(0,[z23,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z83,z6]),(0,[z7,z84,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z85,z4,z5,z6])],[(0,[z7,z86,z1,z3,z4,z5,z6]),(0,[z87,z7,z1,z3,z4,z5,z88]),(0,[z7,z1,z89,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z48,z90,z6]),(0,[z7,z84,z3,z4,z5,z91,z6]),(0,[z7,z1,z92,z3,z93,z5,z6]),(0,[z7,z1,z94,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z95])],[(0,[z96,z7,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z24,z5,z6]),(0,[z7,z20,z1,z3,z5,z97,z6])],[(0,[z7,z1,z3,z4,z5,z98,z6]),(0,[z7,z1,z3,z4,z99,z5,z6]),(0,[z7,z100,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z65,z5,z6]),(0,[z7,z1,z101,z3,z4,z5,z6]),(0,[z7,z1,z102,z3,z4,z5,z6]),(0,[z7,z1,z3,z5,z55,z6,z22]),(1,[z7,z103,z1,z3,z4,z104]),(0,[z7,z1,z3,z4,z5,z105,z6])],[(0,[z7,z1,z3,z106,z4,z5,z6]),(0,[z7,z1,z107,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z108,z5,z6]),(0,[z7,z1,z3,z109,z4,z5,z6]),(0,[z7,z1,z4,z48,z5,z37,z6])],[(0,[z96,z7,z0,z3,z4,z5,z6]),(0,[z23,z7,z20,z1,z3,z5,z6]),(0,[z7,z103,z110,z3,z4,z5,z6])],[(0,[z96,z7,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z111,z4,z5,z6]),(0,[z112,z7,z1,z3,z26,z5,z6]),(0,[z7,z113,z1,z3,z4,z114,z6]),(0,[z7,z1,z115,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z116,z117]),(1,[z7,z1,z3,z93,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z118,z5,z6]),(1,[z7,z1,z3,z119,z5,z6]),(0,[z7,z120,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z121,z6]),(0,[z7,z1,z3,z122,z4,z5,z6]),(0,[z7,z123,z1,z3,z4,z116,z6]),(0,[z7,z1,z3,z124,z4,z5,z6]),(1,[z7,z1,z3,z4,z6,z74]),(0,[z7,z1,z125,z3,z4,z5,z6]),(0,[z7,z1,z126,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z127,z5,z6]),(0,[z7,z1,z128,z3,z4,z5,z6]),(0,[z7,z129,z1,z3,z4,z5,z6])],[],[],[(0,[z130,z7,z1,z3,z4,z5,z6]),(0,[z87,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z131,z3,z4,z5,z6]),(0,[z7,z131,z3,z4,z99,z5,z6]),(0,[z7,z1,z132,z3,z4,z5,z6]),(0,[z7,z20,z133,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z134]),(0,[z7,z1,z3,z4,z5,z6,z135])],[(0,[z7,z1,z3,z4,z136,z5,z6]),(0,[z112,z7,z20,z1,z3,z5,z6]),(0,[z7,z20,z1,z3,z5,z6,z117]),(0,[z7,z103,z1,z3,z4,z61,z6])],[(0,[z7,z1,z3,z4,z90,z5,z6]),(0,[z7,z1,z137,z3,z4,z5,z6]),(0,[z7,z138,z20,z1,z3,z5,z6]),(0,[z7,z1,z4,z5,z39,z6,z62]),(0,[z7,z1,z3,z4,z5,z139,z6])],[(0,[z75,z7,z140,z3,z4,z5,z6]),(0,[z141,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z142,z3,z4,z5,z6]),(0,[z7,z1,z143,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z97,z144,z6]),(0,[z7,z1,z145,z3,z4,z5,z6])]],
   [[(0,[z146,z7,z1,z3,z4,z5,z6]),(0,[z7,z123,z1,z3,z4,z91,z6]),(0,[z7,z1,z147,z4,z5,z6,z62])],[(0,[z7,z1,z3,z4,z5,z148,z6]),(0,[z7,z1,z3,z149,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z150])],[(0,[z151,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z5,z6]),(0,[z7,z1,z152,z3,z4,z5,z6])],[(0,[z7,z153,z1,z3,z4,z5,z6]),(0,[z7,z1,z154,z3,z26,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z155]),(0,[z7,z1,z3,z4,z97,z37,z6]),(0,[z156,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z154,z3,z4,z144,z6])],[(0,[z7,z157,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z158,z6]),(1,[z7,z1,z3,z4,z159,z6]),(0,[z7,z160,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z161,z5,z6]),(0,[z7,z162,z1,z3,z4,z5,z6]),(0,[z7,z163,z1,z3,z4,z5,z6])],[(0,[z7,z164,z1,z3,z4,z5,z6])],[(0,[z7,z123,z1,z3,z26,z5,z6]),(0,[z7,z113,z1,z3,z4,z61,z5]),(0,[z7,z20,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z61,z5,z6]),(0,[z7,z1,z47,z3,z4,z5,z165]),(0,[z7,z1,z166,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z167,z6]),(0,[z7,z1,z3,z4,z48,z91,z6]),(0,[z7,z20,z1,z168,z3,z5,z6])],[(0,[z7,z169,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z170,z6]),(1,[z7,z1,z171,z26,z5,z6]),(0,[z7,z1,z172,z3,z4,z5,z6]),(0,[z7,z1,z173,z21,z4,z5,z6])],[(1,[z7,z31,z1,z26,z5,z6]),(0,[z7,z174,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z175,z4,z5,z6]),(0,[z176,z7,z1,z4,z5,z6,z62]),(0,[z7,z1,z3,z4,z177,z5,z6]),(0,[z7,z1,z3,z4,z178,z5,z6]),(0,[z7,z103,z179,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z180,z6]),(0,[z45,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z54,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z181]),(0,[z182,z7,z1,z3,z4,z5,z6])],[(0,[z87,z7,z1,z183,z4,z5,z6]),(0,[z7,z123,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z184,z5,z6])],[(0,[z7,z1,z185,z3,z4,z5,z6]),(0,[z23,z1,z56,z3,z4,z5,z6]),(0,[z7,z1,z186,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z187,z104]),(0,[z188,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z154,z82,z4,z5,z6])],[(0,[z7,z1,z3,z4,z189,z5,z6]),(0,[z190,z7,z1,z3,z4,z5,z6]),(0,[z7,z31,z1,z3,z4,z5,z6]),(0,[z7,z174,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z191,z5,z6]),(0,[z7,z20,z1,z3,z18,z5,z6]),(1,[z7,z1,z3,z4,z5,z165])]],
   [[(0,[z7,z1,z3,z192,z4,z5,z6]),(0,[z7,z193,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z194]),(0,[z7,z31,z131,z3,z4,z5,z6])],[(0,[z7,z1,z195,z3,z4,z5,z6]),(0,[z7,z1,z196,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z48,z5,z6])],[(0,[z197,z7,z1,z3,z4,z5,z6]),(0,[z198,z1,z3,z4,z90,z5,z6]),(0,[z71,z7,z1,z3,z199,z5,z6]),(0,[z7,z1,z3,z4,z200,z5,z6]),(0,[z7,z1,z3,z4,z5,z201,z6]),(0,[z7,z1,z3,z202,z4,z5,z6]),(1,[z7,z1,z147,z4,z5,z62])],[(0,[z7,z31,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z203,z5,z6]),(0,[z7,z3,z4,z204,z5,z91,z6]),(0,[z205,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z206,z6])],[(0,[z207,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z208,z5,z6]),(0,[z209,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z39,z210]),(0,[z211,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z212]),(0,[z213,z7,z1,z3,z4,z5,z6]),(0,[z7,z214,z20,z1,z3,z5,z6])],[(0,[z215,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z187,z6]),(0,[z7,z1,z216,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z18,z5,z6]),(0,[z7,z1,z217,z3,z4,z5,z6])],[(0,[z218,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z219,z5,z6]),(0,[z7,z20,z1,z54,z3,z5,z6]),(0,[z7,z1,z3,z4,z220,z5,z6])],[(0,[z221,z7,z1,z3,z4,z5,z6]),(0,[z222,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z56,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z210,z62]),(0,[z7,z223,z1,z3,z4,z5,z6]),(0,[z7,z1,z224,z3,z4,z5,z6]),(0,[z7,z1,z225,z3,z4,z5,z6]),(0,[z7,z1,z3,z226,z4,z5,z6]),(0,[z227,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z228,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z6]),(0,[z7,z229,z1,z3,z4,z5,z6]),(1,[z7,z1,z230,z3,z5,z6]),(0,[z7,z1,z231,z3,z4,z5,z6])],[(0,[z7,z232,z1,z3,z4,z5,z6]),(0,[z75,z23,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z55,z46]),(1,[z7,z1,z3,z233,z5,z6]),(0,[z7,z234,z1,z3,z4,z5,z6]),(0,[z7,z1,z235,z3,z4,z5,z6])],[(0,[z7,z236,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z237,z5,z6]),(0,[z71,z7,z1,z3,z4,z5,z238]),(0,[z7,z174,z1,z3,z65,z5,z6]),(0,[z7,z113,z84,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z239,z6])],[(0,[z7,z1,z3,z4,z5,z46,z6]),(0,[z7,z1,z240,z3,z4,z5,z6]),(0,[z7,z1,z241,z3,z4,z5,z6])],[(1,[z96,z0,z3,z4,z5,z6]),(0,[z7,z1,z3,z242,z4,z5,z6]),(0,[z243,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z244]),(0,[z7,z103,z1,z3,z4,z5,z104])],[(0,[z7,z245,z1,z3,z4,z5,z6]),(0,[z45,z7,z1,z3,z4,z5,z46]),(0,[z7,z1,z246,z3,z4,z5,z6]),(1,[z7,z247,z1,z3,z4,z5])],[(1,[z7,z1,z3,z4,z248,z6]),(0,[z7,z1,z3,z26,z249,z5,z6]),(0,[z7,z20,z1,z154,z3,z5,z6]),(1,[z7,z1,z54,z3,z5,z55]),(0,[z7,z1,z250,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z251,z5,z6]),(1,[z7,z1,z3,z4,z5,z252]),(0,[z7,z1,z3,z4,z5,z253,z6])]],
   [[(0,[z7,z1,z3,z4,z76,z5,z6]),(0,[z7,z1,z3,z4,z5,z254,z6]),(0,[z255,z7,z1,z3,z4,z5,z6]),(0,[z112,z7,z1,z3,z4,z5,z6]),(1,[z7,z256,z1,z3,z5,z6]),(0,[z7,z257,z1,z3,z4,z5,z6]),(0,[z7,z1,z258,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z259]),(0,[z7,z1,z183,z3,z4,z5,z6]),(0,[z1,z3,z4,z90,z5,z97,z6]),(0,[z7,z103,z1,z3,z26,z5,z6]),(0,[z7,z138,z1,z3,z4,z5,z6]),(0,[z7,z1,z21,z260,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z261,z6])],[(0,[z7,z0,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z52,z5,z6]),(0,[z7,z1,z3,z4,z5,z262,z6])],[(0,[z7,z20,z1,z2,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z263,z6]),(1,[z7,z1,z47,z4,z48,z6]),(0,[z7,z1,z3,z4,z5,z264,z6])],[(0,[z7,z1,z265,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z266]),(0,[z7,z1,z267,z3,z4,z5,z6])],[(0,[z7,z268,z1,z3,z4,z5,z6]),(0,[z7,z1,z269,z3,z4,z5,z6]),(0,[z270,z7,z1,z149,z4,z5,z6])],[(1,[z7,z1,z24,z26,z5,z6]),(0,[z7,z1,z149,z109,z4,z5,z6]),(0,[z7,z103,z20,z1,z3,z5,z6]),(0,[z7,z271,z1,z3,z4,z5,z6])],[(0,[z272,z7,z1,z3,z4,z5,z6]),(0,[z7,z103,z1,z3,z4,z37,z6]),(0,[z7,z1,z273,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z274,z6])]],
   [[(0,[z198,z7,z1,z3,z26,z5,z6]),(0,[z7,z20,z1,z3,z61,z5,z6]),(0,[z7,z275,z1,z3,z4,z5,z6])],[(1,[z7,z276,z3,z65,z5,z6]),(0,[z7,z1,z3,z4,z277,z5,z6]),(0,[z278,z7,z1,z3,z4,z5,z6]),(0,[z279,z7,z20,z1,z3,z5,z6]),(0,[z280,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z281,z6])],[(0,[z7,z113,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z26,z5,z6,z62]),(0,[z7,z1,z3,z4,z32,z5,z6])],[(0,[z7,z1,z3,z4,z5,z282,z6]),(0,[z7,z283,z1,z3,z4,z5,z6]),(0,[z284,z7,z1,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z5,z285]),(0,[z7,z286,z1,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z76,z6]),(0,[z198,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z287,z4,z5,z6]),(0,[z288,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z289,z6]),(0,[z7,z290,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z291,z6]),(0,[z7,z1,z3,z4,z91,z37,z6]),(0,[z7,z1,z3,z26,z5,z39,z6]),(0,[z7,z1,z3,z4,z292,z5,z6])],[(0,[z7,z293,z1,z3,z4,z5,z6]),(0,[z7,z113,z20,z1,z3,z5,z6]),(1,[z7,z1,z26,z5,z37,z6]),(0,[z7,z1,z54,z3,z4,z5,z22])]],
   [[(0,[z7,z1,z294,z3,z4,z5,z6]),(0,[z7,z123,z1,z3,z4,z5,z6])],[(0,[z7,z1,z295,z3,z4,z5,z6]),(0,[z7,z296,z1,z3,z4,z5,z6]),(0,[z176,z7,z1,z171,z4,z5,z6])],[(0,[z112,z7,z1,z3,z4,z5,z46]),(0,[z7,z297,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z298,z6]),(0,[z176,z7,z31,z1,z4,z5,z6]),(0,[z270,z7,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z48,z5,z6]),(0,[z7,z1,z299,z3,z4,z5,z6]),(0,[z7,z103,z1,z3,z4,z6,z104])],[(0,[z7,z300,z1,z3,z4,z5,z6]),(0,[z7,z174,z1,z3,z4,z5,z6]),(1,[z7,z301,z3,z4,z204,z6])],[(0,[z7,z1,z3,z4,z5,z302,z6]),(0,[z7,z1,z3,z4,z5,z303,z91]),(0,[z7,z1,z3,z4,z5,z6,z304]),(0,[z305,z7,z20,z1,z3,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z306]),(0,[z7,z1,z3,z26,z307,z5,z6]),(0,[z7,z1,z3,z199,z4,z5,z6]),(0,[z7,z301,z3,z4,z204,z5,z6]),(0,[z7,z1,z308,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z309])],[(0,[z7,z174,z0,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z5,z187,z6]),(1,[z7,z1,z128,z3,z5,z6])],[(0,[z7,z174,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z310,z5,z6]),(0,[z7,z1,z3,z4,z5,z311,z6])]],
   [[(0,[z207,z7,z1,z3,z4,z5,z6]),(0,[z7,z0,z31,z3,z4,z5,z6]),(0,[z71,z7,z1,z131,z4,z5,z6]),(0,[z7,z214,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z312,z5,z6]),(0,[z7,z1,z3,z4,z5,z313,z6]),(0,[z7,z1,z3,z4,z5,z6,z285]),(0,[z7,z123,z1,z3,z4,z5,z314]),(0,[z7,z1,z3,z4,z91,z6,z104]),(0,[z7,z1,z3,z4,z315,z5,z6]),(0,[z7,z84,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z316,z6]),(1,[z7,z1,z92,z4,z37,z6]),(0,[z7,z1,z147,z3,z4,z5,z62]),(0,[z7,z1,z3,z4,z61,z116,z6])],[(0,[z7,z1,z3,z4,z317,z5,z6]),(0,[z7,z1,z3,z4,z318,z5,z6]),(0,[z7,z174,z3,z149,z4,z5,z6]),(0,[z7,z1,z319,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z320]),(0,[z7,z1,z3,z4,z5,z321,z6])],[(0,[z207,z7,z0,z3,z4,z5,z6]),(1,[z7,z140,z3,z4,z5,z6]),(0,[z7,z322,z1,z3,z4,z5,z6]),(1,[z7,z1,z17,z3,z18,z6])],[(0,[z7,z7,z1,z3,z4,z5,z6]),(0,[z207,z7,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z97,z6]),(0,[z7,z1,z3,z4,z5,z187,z6]),(0,[z7,z1,z3,z4,z5,z39,z187]),(0,[z7,z1,z3,z4,z93,z5,z6])],[(0,[z7,z1,z1,z3,z4,z5,z6]),(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z7,z323,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z119,z5,z6]),(0,[z7,z1,z3,z26,z5,z324,z6]),(0,[z7,z1,z47,z3,z4,z48,z6])],[(0,[z96,z23,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z325,z6]),(0,[z7,z1,z230,z3,z4,z5,z6])],[(0,[z326,z7,z1,z3,z4,z5,z6]),(0,[z176,z7,z1,z56,z4,z5,z6]),(0,[z71,z7,z1,z4,z26,z5,z6]),(0,[z7,z1,z3,z327,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z159,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z328,z6]),(0,[z329,z7,z1,z3,z4,z5,z6]),(0,[z1,z56,z3,z24,z4,z5,z6]),(0,[z71,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z330,z5,z6]),(0,[z331,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z92,z3,z4,z48,z6])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z332,z4,z5,z6]),(0,[z7,z44,z1,z56,z3,z5,z6]),(0,[z333,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z334]),(1,[z45,z1,z3,z4,z5,z46]),(1,[z71,z7,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z61,z91,z6])],[(0,[z335,z7,z1,z3,z4,z5,z6]),(0,[z336,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z38,z3,z4,z5,z62]),(0,[z7,z1,z21,z3,z5,z6,z22])],[(0,[z87,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z337,z3,z4,z5,z6]),(0,[z338,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z38,z26,z5,z6]),(0,[z7,z1,z339,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z48,z116,z6]),(0,[z7,z1,z38,z3,z4,z340,z6]),(0,[z7,z1,z3,z4,z61,z5,z104])],[(0,[z7,z1,z341,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z91,z6,z117]),(0,[z7,z84,z1,z3,z4,z5,z187]),(0,[z7,z1,z3,z4,z5,z342,z6]),(0,[z7,z1,z154,z3,z4,z18,z6]),(0,[z7,z1,z3,z4,z343,z5,z6])],[(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z3,z4,z99,z5,z6]),(0,[z7,z0,z3,z4,z65,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z344]),(0,[z71,z336,z1,z3,z4,z5,z6]),(0,[z71,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z345,z5,z6]),(0,[z7,z1,z3,z4,z249,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z117]),(0,[z346,z7,z1,z3,z26,z5,z6]),(0,[z7,z347,z1,z3,z4,z5,z6]),(0,[z7,z348,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z349,z6])],[(0,[z75,z7,z1,z56,z4,z5,z6]),(0,[z7,z1,z3,z4,z350,z5,z6])],[(0,[z7,z1,z3,z351,z4,z5,z6]),(0,[z87,z7,z1,z3,z4,z52,z6]),(0,[z7,z1,z3,z352,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z303,z6]),(0,[z7,z1,z3,z4,z353,z5,z6]),(0,[z7,z354,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z154,z29,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z355,z6]),(0,[z87,z7,z1,z3,z40,z5,z6]),(0,[z7,z1,z3,z356,z4,z5,z6]),(0,[z7,z357,z1,z3,z4,z5,z6]),(0,[z7,z1,z358,z3,z4,z5,z6]),(0,[z7,z1,z359,z3,z4,z5,z6])],[(0,[z7,z360,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z361,z6]),(0,[z7,z103,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z362])],[(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z363,z6]),(0,[z7,z1,z3,z4,z5,z364,z6]),(0,[z7,z20,z1,z3,z5,z6,z62])],[(0,[z7,z1,z3,z4,z5,z365,z6]),(0,[z7,z1,z3,z4,z5,z6,z366]),(0,[z7,z1,z131,z3,z233,z5,z6]),(0,[z7,z20,z1,z3,z149,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z367])],[(0,[z7,z368,z1,z3,z4,z5,z6]),(0,[z369,z7,z1,z3,z4,z5,z6])],[(0,[z176,z7,z1,z24,z4,z5,z6]),(1,[z7,z1,z3,z72,z5,z6]),(0,[z7,z20,z1,z3,z5,z144,z6])],[(0,[z7,z1,z3,z4,z18,z97,z6]),(0,[z71,z7,z1,z4,z99,z5,z6]),(0,[z7,z20,z1,z3,z5,z39,z6]),(0,[z7,z1,z370,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z4,z5,z6]),(0,[z7,z1,z371,z3,z4,z5,z6]),(0,[z7,z301,z1,z3,z4,z91,z6]),(0,[z7,z1,z3,z372,z4,z5,z6]),(0,[z7,z20,z1,z171,z3,z5,z6])],[(0,[z7,z1,z3,z3,z4,z5,z6]),(0,[z198,z7,z1,z3,z4,z5,z6]),(0,[z373,z7,z1,z3,z4,z90,z6]),(0,[z7,z20,z31,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z374,z5,z6]),(0,[z7,z1,z92,z4,z5,z37,z6]),(0,[z7,z1,z375,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z62]),(0,[z376,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z377,z6]),(0,[z1,z3,z4,z5,z46,z6,z210])],[(1,[z7,z1,z3,z4,z5,z88]),(0,[z7,z1,z378,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z210,z22]),(0,[z7,z1,z3,z4,z6,z74,z117]),(0,[z7,z1,z171,z4,z26,z5,z6])],[(0,[z1,z2,z3,z24,z4,z5,z6]),(0,[z87,z379,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z380]),(0,[z7,z1,z3,z4,z5,z46,z62]),(0,[z7,z276,z1,z3,z26,z5,z6]),(0,[z7,z1,z171,z3,z26,z5,z6])],[(0,[z75,z7,z1,z24,z4,z5,z6]),(0,[z7,z1,z381,z3,z4,z5,z6]),(0,[z379,z1,z3,z40,z4,z5,z6]),(0,[z176,z7,z1,z4,z5,z37,z6]),(0,[z7,z1,z3,z4,z5,z39,z6]),(0,[z7,z1,z382,z3,z4,z5,z6])],[(0,[z7,z383,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z307,z5,z6]),(0,[z71,z7,z31,z3,z4,z5,z6]),(0,[z7,z123,z1,z3,z4,z204,z6]),(0,[z7,z3,z4,z5,z187,z6,z117]),(0,[z7,z1,z21,z3,z26,z5,z6])],[(1,[z7,z51,z3,z4,z5,z6]),(0,[z7,z1,z3,z384,z4,z5,z6]),(0,[z7,z1,z385,z3,z4,z5,z6]),(0,[z7,z301,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z386])]],
   [[(0,[z7,z1,z3,z4,z387,z5,z6]),(0,[z388,z7,z1,z3,z4,z5,z6]),(0,[z379,z7,z1,z3,z26,z5,z6]),(0,[z389,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z390,z26,z5,z6]),(1,[z7,z1,z173,z4,z5,z6]),(0,[z7,z103,z1,z3,z4,z5,z116])],[(0,[z7,z276,z20,z1,z3,z5,z6]),(0,[z391,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z392]),(0,[z7,z1,z393,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z394,z6]),(1,[z198,z1,z3,z4,z90,z6]),(0,[z395,z7,z1,z3,z4,z5,z6]),(0,[z7,z3,z149,z4,z65,z5,z6]),(0,[z7,z1,z3,z4,z5,z396,z6]),(0,[z7,z397,z1,z3,z4,z5,z6]),(0,[z7,z1,z38,z3,z26,z5,z6])],[(0,[z75,z7,z1,z3,z106,z5,z6]),(0,[z398,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z399,z4,z5,z6]),(0,[z71,z7,z1,z3,z4,z98,z6]),(0,[z7,z1,z400,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z307,z5,z6]),(0,[z7,z1,z401,z3,z4,z5,z6]),(0,[z7,z1,z402,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z403]),(0,[z7,z1,z404,z3,z4,z5,z6]),(0,[z7,z301,z20,z1,z3,z5,z6]),(0,[z405,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z406,z6]),(0,[z7,z1,z407,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z408])],[(0,[z23,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z409,z5,z6]),(0,[z379,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z410,z3,z4,z5,z6]),(0,[z7,z84,z1,z3,z4,z5,z6]),(0,[z7,z133,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z411,z5,z6])],[(0,[z7,z20,z1,z56,z3,z5,z6]),(0,[z7,z1,z412,z3,z4,z5,z6]),(0,[z7,z256,z1,z131,z3,z5,z6]),(0,[z7,z1,z3,z4,z48,z204,z6]),(0,[z7,z1,z17,z3,z26,z5,z6])],[(0,[z7,z1,z413,z3,z4,z5,z6]),(0,[z7,z1,z38,z152,z3,z5,z6]),(0,[z7,z1,z17,z3,z4,z144,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z6,z88]),(0,[z414,z7,z1,z3,z4,z5,z6]),(0,[z415,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z116,z6]),(0,[z7,z416,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z40,z26,z5,z6]),(0,[z45,z112,z1,z3,z4,z5,z6]),(0,[z7,z417,z20,z1,z3,z5,z6]),(1,[z7,z1,z152,z3,z5,z6])],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z418]),(0,[z7,z1,z419,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z420,z6]),(0,[z7,z1,z3,z4,z5,z117,z62]),(0,[z7,z20,z1,z17,z3,z5,z6])],[(0,[z75,z7,z421,z3,z4,z5,z6]),(0,[z379,z7,z1,z3,z40,z5,z6]),(0,[z7,z422,z1,z3,z4,z5,z6]),(0,[z71,z7,z3,z4,z99,z5,z6]),(0,[z7,z1,z38,z3,z4,z423,z6])],[(0,[z7,z276,z1,z3,z65,z5,z6]),(0,[z7,z1,z3,z4,z5,z324,z6])],[(0,[z7,z1,z3,z4,z424,z5,z6]),(0,[z7,z1,z425,z3,z4,z5,z6])],[(0,[z7,z1,z426,z3,z4,z5,z6]),(0,[z427,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z428,z3,z26,z5,z6]),(0,[z7,z1,z3,z26,z5,z6,z22]),(0,[z7,z1,z3,z4,z5,z6,z429])],[(0,[z87,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z430,z5,z6]),(0,[z7,z20,z1,z3,z431,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z432,z5,z6]),(0,[z7,z1,z3,z26,z5,z91,z6]),(0,[z7,z1,z47,z3,z127,z5,z6])],[(0,[z71,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z433,z6]),(0,[z7,z1,z3,z4,z37,z116,z6])],[(0,[z75,z1,z3,z24,z4,z5,z6]),(0,[z7,z247,z1,z3,z4,z5,z91]),(0,[z7,z20,z1,z3,z5,z6,z434]),(0,[z7,z20,z1,z21,z3,z5,z6]),(1,[z7,z1,z260,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z435]),(0,[z7,z1,z3,z4,z5,z6,z436]),(0,[z176,z7,z1,z38,z4,z5,z6])],[(0,[z7,z1,z3,z24,z26,z5,z6]),(0,[z7,z1,z437,z3,z4,z5,z6]),(1,[z7,z1,z109,z4,z5,z6]),(1,[z7,z1,z3,z4,z114,z6]),(0,[z7,z103,z1,z3,z4,z5,z39])],[(0,[z7,z1,z3,z438,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z6,z210]),(0,[z7,z1,z3,z4,z5,z6,z439])],[(0,[z7,z440,z1,z3,z4,z5,z6]),(0,[z441,z7,z1,z3,z4,z5,z6]),(0,[z7,z442,z1,z3,z4,z5,z6]),(0,[z443,z7,z1,z3,z4,z5,z6]),(0,[z373,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z444,z4,z5,z6]),(0,[z7,z1,z3,z4,z445,z5,z6]),(0,[z7,z446,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z447,z5,z6]),(0,[z7,z1,z3,z448,z4,z5,z6]),(0,[z7,z1,z449,z3,z4,z5,z6]),(0,[z7,z1,z154,z3,z4,z5,z6])]],
   [[(1,[z7,z450,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z144,z6]),(0,[z7,z20,z1,z3,z5,z451,z6])],[(1,[z7,z1,z3,z199,z5,z6]),(0,[z7,z1,z3,z4,z61,z5,z6]),(0,[z7,z1,z452,z3,z4,z5,z6])],[(0,[z7,z1,z453,z3,z4,z5,z6]),(0,[z454,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z455,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z456,z5,z6])],[(0,[z87,z7,z1,z3,z307,z5,z6]),(0,[z373,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z457,z5,z6]),(0,[z7,z458,z1,z3,z4,z5,z6]),(0,[z71,z153,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z459]),(0,[z7,z460,z1,z3,z4,z5,z6])],[(0,[z461,z7,z1,z3,z4,z5,z6]),(0,[z462,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z463,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z464,z6]),(1,[z7,z1,z154,z3,z144,z6]),(0,[z465,z7,z1,z3,z4,z5,z6]),(1,[z7,z110,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z466,z5,z6]),(0,[z7,z123,z301,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z37,z6])],[(1,[z7,z1,z467,z4,z5,z6]),(0,[z7,z1,z468,z3,z4,z5,z6]),(1,[z7,z84,z3,z4,z5,z187]),(0,[z7,z1,z3,z4,z5,z6,z469]),(0,[z470,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z471]),(0,[z7,z276,z3,z4,z65,z5,z6]),(0,[z7,z1,z472,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z473,z5,z6]),(0,[z7,z1,z54,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z474,z6])]],
   [[(0,[z71,z176,z7,z1,z4,z5,z6]),(0,[z7,z174,z1,z3,z149,z5,z6]),(0,[z7,z475,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z423,z5,z6])],[(0,[z75,z7,z1,z3,z4,z476,z6]),(0,[z7,z1,z3,z4,z5,z477,z6]),(0,[z7,z1,z3,z4,z5,z314,z6])],[(0,[z7,z1,z3,z4,z5,z478,z6]),(0,[z188,z7,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z92,z3,z5,z6]),(0,[z7,z1,z92,z145,z3,z5,z6]),(0,[z479,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z21,z3,z4,z5,z22])],[(1,[z207,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z480,z4,z5,z6]),(0,[z7,z1,z168,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z48,z5,z6]),(0,[z7,z1,z54,z3,z4,z5,z55])],[],[(0,[z481,z7,z1,z3,z4,z5,z6]),(0,[z482,z7,z1,z3,z4,z5,z6]),(0,[z7,z113,z1,z3,z4,z5,z187]),(1,[z7,z1,z47,z26,z5,z6])],[(0,[z7,z483,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z484]),(0,[z7,z1,z3,z4,z5,z485,z6]),(0,[z486,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z487,z5,z6])],[(0,[z7,z1,z3,z488,z4,z5,z6]),(0,[z7,z1,z489,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z340,z6]),(0,[z7,z1,z490,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z61,z5,z116])]],
   [[(0,[z7,z1,z56,z3,z26,z5,z6]),(1,[z270,z7,z1,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z6,z104]),(0,[z7,z1,z38,z3,z177,z5,z6])],[(0,[z491,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z492,z3,z4,z5,z6]),(0,[z7,z493,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z494,z6]),(0,[z7,z1,z495,z3,z4,z5,z6]),(0,[z7,z1,z3,z390,z4,z5,z6]),(0,[z7,z1,z216,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z5,z496,z6]),(0,[z7,z20,z1,z3,z5,z116,z6])],[(1,[z7,z1,z3,z4,z477,z6]),(1,[z7,z1,z3,z4,z5,z325]),(0,[z7,z1,z3,z4,z5,z497,z6]),(0,[z7,z41,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z498,z5,z6]),(0,[z499,z7,z1,z3,z4,z5,z6]),(0,[z500,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z55,z210]),(0,[z7,z1,z3,z4,z5,z501,z6]),(0,[z7,z1,z502,z3,z4,z5,z6])],[(0,[z7,z503,z1,z3,z4,z5,z6]),(0,[z75,z7,z1,z3,z4,z5,z484]),(1,[z7,z31,z131,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z504])],[(0,[z7,z505,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z506,z4,z5,z6]),(0,[z7,z1,z3,z507,z4,z5,z6]),(0,[z7,z508,z1,z3,z26,z5,z6]),(0,[z7,z417,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z509]),(0,[z7,z1,z510,z3,z4,z5,z6]),(0,[z7,z1,z173,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z511]),(0,[z7,z1,z512,z3,z4,z5,z6])],[(0,[z96,z7,z1,z3,z26,z5,z6]),(0,[z45,z7,z1,z3,z4,z5,z210]),(0,[z7,z20,z1,z3,z5,z6,z22]),(0,[z7,z1,z3,z4,z5,z6,z513]),(0,[z7,z1,z154,z17,z3,z5,z6]),(0,[z7,z1,z514,z3,z4,z5,z6]),(0,[z7,z1,z3,z515,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z516])]],
   [[(0,[z7,z2,z3,z4,z99,z5,z6]),(0,[z7,z517,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z204,z5,z6]),(1,[z7,z1,z3,z4,z340,z6]),(1,[z7,z179,z3,z4,z5,z6])],[(0,[z207,z96,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z5,z91,z6])],[(0,[z7,z1,z3,z40,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z518,z6]),(0,[z7,z1,z3,z26,z99,z5,z6]),(0,[z7,z123,z103,z1,z3,z4,z6]),(0,[z7,z84,z1,z3,z4,z5,z117]),(0,[z7,z20,z1,z38,z3,z5,z6]),(0,[z7,z1,z3,z519,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z520,z6]),(0,[z7,z1,z3,z4,z5,z6,z484]),(1,[z23,z1,z56,z4,z5,z6]),(0,[z198,z7,z1,z3,z4,z97,z6]),(1,[z7,z123,z3,z4,z91,z6]),(0,[z7,z301,z1,z3,z4,z116,z6]),(0,[z7,z1,z521,z3,z4,z5,z6])],[(0,[z96,z7,z20,z1,z3,z5,z6]),(0,[z75,z7,z1,z3,z4,z5,z70]),(0,[z7,z1,z522,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z523,z5,z6]),(0,[z7,z1,z3,z4,z204,z37,z6]),(0,[z7,z1,z47,z3,z4,z5,z27]),(0,[z7,z1,z29,z3,z4,z5,z6]),(0,[z524,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z525,z6])],[(0,[z7,z20,z1,z3,z5,z6,z210])],[(0,[z96,z1,z3,z24,z4,z5,z6]),(0,[z7,z1,z3,z526,z4,z5,z6]),(1,[z71,z7,z4,z99,z5,z6]),(0,[z7,z1,z428,z3,z4,z5,z6]),(0,[z7,z1,z17,z3,z18,z5,z6]),(0,[z7,z1,z527,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z528,z5,z6]),(0,[z7,z1,z529,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z530,z6]),(0,[z279,z7,z1,z3,z4,z5,z6])],[(0,[z531,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z532,z6]),(0,[z7,z1,z3,z533,z4,z5,z6]),(0,[z534,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z535,z6]),(0,[z7,z1,z536,z3,z4,z5,z6])],[(0,[z23,z7,z1,z56,z4,z5,z6]),(0,[z7,z1,z3,z4,z90,z144,z6]),(0,[z7,z1,z3,z4,z537,z5,z6]),(0,[z7,z1,z538,z3,z4,z5,z6])],[(0,[z7,z1,z56,z3,z317,z5,z6]),(0,[z539,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z540,z6]),(0,[z7,z1,z3,z26,z90,z5,z6]),(0,[z7,z541,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z61,z5,z39])],[(0,[z7,z1,z3,z4,z5,z6,z210]),(0,[z7,z1,z3,z4,z5,z6,z542]),(0,[z7,z123,z1,z3,z4,z5,z285]),(0,[z7,z543,z1,z3,z4,z5,z6]),(0,[z7,z1,z147,z3,z26,z5,z6]),(0,[z7,z1,z38,z147,z4,z5,z6])],[(0,[z7,z1,z544,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z545,z6]),(0,[z7,z546,z1,z3,z4,z5,z6])],[(0,[z7,z113,z1,z3,z4,z5,z6]),(0,[z7,z1,z47,z4,z26,z5,z6]),(0,[z7,z20,z1,z3,z5,z37,z6])],[(0,[z373,z7,z1,z3,z4,z5,z6]),(0,[z373,z1,z3,z4,z5,z97,z6]),(0,[z7,z1,z3,z4,z90,z37,z6]),(0,[z7,z1,z3,z4,z204,z6,z104]),(0,[z7,z1,z3,z4,z61,z204,z6]),(0,[z7,z1,z47,z3,z26,z5,z6]),(0,[z7,z1,z547,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z548,z6]),(0,[z7,z1,z3,z4,z5,z144,z6]),(0,[z7,z1,z54,z21,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z549])]],
   [[(1,[z7,z1,z3,z106,z5,z6])],[(0,[z7,z1,z550,z3,z4,z5,z6]),(0,[z551,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z552,z3,z4,z5,z6]),(0,[z7,z1,z92,z3,z26,z5,z6])],[(0,[z305,z7,z1,z3,z4,z5,z6]),(0,[z553,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z554,z3,z4,z5,z6])],[(0,[z7,z1,z555,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z556,z5,z6]),(1,[z7,z20,z1,z26,z5,z6]),(0,[z7,z1,z38,z4,z26,z5,z6]),(0,[z7,z475,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z557,z5,z6]),(0,[z7,z558,z1,z3,z4,z5,z6]),(0,[z7,z559,z1,z3,z4,z5,z6]),(1,[z7,z397,z1,z3,z4,z6]),(0,[z7,z397,z1,z3,z4,z6,z117]),(0,[z7,z1,z4,z26,z5,z6,z62]),(0,[z7,z1,z3,z26,z5,z55,z6]),(0,[z7,z1,z47,z3,z4,z37,z6])],[(0,[z7,z1,z3,z4,z5,z560,z6]),(0,[z7,z1,z3,z4,z248,z5,z6]),(0,[z7,z113,z3,z4,z5,z6,z117]),(0,[z176,z7,z1,z3,z26,z5,z6])],[(0,[z561,z7,z1,z3,z4,z5,z6]),(0,[z45,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z562,z5,z6]),(0,[z7,z84,z3,z4,z5,z187,z6]),(1,[z7,z1,z3,z26,z5,z6])]],
   [[(1,[z7,z421,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z563]),(0,[z7,z1,z92,z3,z4,z37,z6]),(0,[z7,z1,z3,z4,z5,z564,z6]),(0,[z7,z1,z3,z4,z565,z5,z6])],[(0,[z7,z1,z3,z4,z5,z566,z6]),(0,[z7,z1,z3,z4,z233,z5,z6]),(0,[z7,z1,z567,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z303]),(1,[z7,z1,z26,z5,z6,z62]),(0,[z7,z20,z1,z3,z5,z6,z104]),(0,[z7,z1,z92,z47,z4,z5,z6])],[(0,[z7,z1,z450,z3,z4,z5,z6]),(0,[z7,z84,z301,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z114,z5,z6]),(0,[z7,z1,z3,z4,z5,z568,z6])],[(0,[z7,z1,z3,z4,z5,z6,z569]),(0,[z7,z31,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z570,z5,z6]),(0,[z176,z7,z20,z1,z3,z5,z6])],[(0,[z7,z1,z3,z4,z5,z571,z6]),(1,[z87,z1,z3,z307,z5,z6]),(1,[z373,z1,z3,z4,z97,z6]),(0,[z7,z572,z1,z3,z4,z5,z6]),(0,[z45,z7,z20,z1,z3,z5,z6]),(1,[z336,z1,z3,z4,z5,z6]),(1,[z7,z20,z1,z3,z5,z6])],[(0,[z7,z1,z3,z4,z573,z5,z6]),(0,[z75,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z574]),(0,[z176,z7,z1,z47,z4,z5,z6]),(0,[z7,z1,z128,z147,z3,z5,z6])],[(0,[z575,z7,z1,z3,z4,z5,z6]),(0,[z7,z301,z1,z3,z4,z204,z6]),(0,[z7,z1,z576,z3,z4,z5,z6]),(0,[z7,z1,z110,z3,z4,z5,z6]),(0,[z7,z577,z1,z3,z4,z5,z6])],[(0,[z7,z1,z578,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z104])]],
   [[(0,[z7,z579,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z423,z6])],[(0,[z7,z1,z580,z3,z4,z5,z6]),(0,[z581,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z582,z5,z6]),(0,[z7,z1,z3,z583,z4,z5,z6]),(0,[z7,z20,z1,z3,z204,z5,z6]),(1,[z7,z113,z3,z4,z5,z117])],[(0,[z7,z20,z0,z1,z3,z5,z6]),(0,[z75,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z39,z46]),(0,[z584,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z82,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z585,z6])],[(0,[z7,z586,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z99,z5,z6]),(0,[z7,z1,z3,z4,z5,z587,z6])],[(0,[z7,z1,z588,z3,z4,z5,z6]),(0,[z7,z1,z3,z589,z4,z5,z6]),(0,[z7,z1,z590,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z476,z6]),(0,[z7,z174,z276,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z591,z6])],[(0,[z7,z1,z3,z4,z5,z6,z592]),(0,[z7,z1,z3,z4,z593,z5,z6]),(0,[z7,z508,z1,z3,z4,z5,z6]),(0,[z7,z594,z1,z3,z4,z5,z6]),(0,[z595,z7,z1,z3,z4,z5,z6]),(0,[z596,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z597,z5,z6]),(0,[z7,z1,z3,z4,z204,z5,z6]),(0,[z7,z1,z3,z4,z5,z598,z6]),(0,[z7,z113,z103,z1,z3,z4,z5])]],
   [[(1,[z7,z1,z183,z4,z5,z6]),(0,[z7,z256,z1,z3,z4,z5,z6]),(0,[z7,z223,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z431,z5,z6]),(0,[z7,z1,z3,z260,z4,z5,z6])],[(0,[z346,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z46,z6]),(0,[z7,z1,z3,z4,z599,z5,z6]),(0,[z7,z1,z3,z4,z5,z116,z187]),(0,[z7,z1,z3,z600,z4,z5,z6])],[(0,[z7,z1,z3,z4,z601,z5,z6]),(0,[z602,z7,z1,z3,z4,z5,z6]),(0,[z7,z603,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z317,z5,z6]),(0,[z7,z1,z3,z4,z5,z604,z6]),(0,[z373,z198,z1,z3,z4,z5,z6]),(0,[z7,z31,z1,z4,z99,z5,z6]),(0,[z7,z1,z3,z4,z5,z605,z6]),(0,[z606,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z607,z5,z6])],[(0,[z7,z1,z3,z4,z5,z608,z6]),(0,[z87,z7,z51,z3,z4,z5,z6]),(0,[z7,z1,z609,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z610]),(0,[z7,z236,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z434]),(1,[z7,z1,z3,z127,z5,z6]),(0,[z7,z1,z3,z4,z611,z5,z6])],[(0,[z7,z1,z3,z4,z612,z5,z6]),(0,[z613,z7,z1,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z90,z5,z6]),(0,[z7,z20,z1,z147,z3,z5,z6]),(0,[z7,z1,z614,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z48,z97,z6]),(0,[z7,z20,z1,z131,z3,z5,z6]),(0,[z7,z1,z615,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z616]),(0,[z7,z1,z3,z4,z5,z617,z6]),(0,[z7,z1,z3,z4,z5,z618,z6])],[(1,[z7,z1,z3,z4,z476,z6]),(0,[z7,z1,z154,z3,z5,z144,z6])],[(0,[z619,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z620,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z117,z104]),(0,[z7,z1,z3,z4,z5,z187,z62]),(0,[z7,z621,z1,z3,z4,z5,z6]),(0,[z7,z622,z20,z1,z3,z5,z6]),(0,[z7,z1,z230,z47,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z165,z6]),(0,[z7,z623,z1,z3,z4,z5,z6]),(0,[z7,z624,z1,z3,z4,z5,z6])],[(0,[z625,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z451,z6])],[(1,[z7,z1,z3,z4,z98,z6])],[(0,[z626,z7,z1,z3,z4,z5,z6]),(0,[z75,z7,z1,z3,z119,z5,z6]),(0,[z7,z1,z3,z627,z4,z5,z6]),(0,[z112,z1,z3,z4,z5,z6,z210]),(0,[z7,z1,z3,z4,z5,z628,z6]),(0,[z7,z1,z3,z4,z629,z5,z6]),(1,[z176,z7,z20,z1,z5,z6]),(0,[z7,z1,z3,z4,z5,z630,z6])],[(0,[z7,z1,z631,z3,z4,z5,z6]),(0,[z7,z1,z3,z467,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z238])],[(0,[z632,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z26,z5,z6]),(0,[z7,z1,z3,z4,z633,z5,z6]),(0,[z7,z1,z147,z3,z4,z5,z6])],[(0,[z7,z1,z634,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z5,z55,z6])],[(0,[z7,z1,z3,z4,z5,z635,z6]),(0,[z71,z7,z1,z3,z4,z248,z6]),(0,[z7,z1,z3,z26,z277,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z636])]],
   [[(0,[z71,z7,z1,z3,z4,z5,z252]),(0,[z7,z276,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z637,z6]),(0,[z7,z247,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z638,z6]),(0,[z7,z1,z171,z3,z4,z5,z6]),(0,[z7,z1,z47,z3,z4,z5,z6])],[(1,[z75,z1,z24,z4,z5,z6]),(0,[z7,z639,z1,z3,z4,z5,z6])],[(0,[z7,z1,z56,z4,z26,z5,z6]),(0,[z7,z276,z1,z3,z149,z5,z6]),(0,[z7,z640,z1,z3,z4,z5,z6]),(1,[z7,z1,z145,z3,z5,z6]),(0,[z7,z1,z21,z3,z4,z5,z6])],[(0,[z7,z1,z24,z4,z26,z5,z6]),(0,[z7,z301,z1,z3,z4,z5,z6]),(0,[z7,z641,z1,z3,z4,z5,z6]),(0,[z7,z113,z1,z3,z4,z5,z117]),(0,[z7,z103,z84,z1,z3,z4,z5]),(0,[z7,z1,z92,z3,z4,z5,z6])],[(0,[z7,z642,z1,z3,z4,z5,z6]),(0,[z379,z7,z1,z3,z4,z5,z6]),(0,[z7,z643,z1,z3,z4,z5,z6]),(0,[z176,z7,z20,z1,z4,z5,z6]),(0,[z7,z20,z1,z47,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z644]),(0,[z7,z1,z3,z4,z5,z55,z6])],[(0,[z7,z1,z645,z3,z4,z5,z6]),(0,[z7,z1,z646,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z647,z5,z6]),(0,[z7,z123,z3,z4,z5,z91,z6]),(0,[z7,z103,z301,z1,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z39,z117]),(0,[z7,z1,z3,z26,z5,z6,z58]),(1,[z7,z1,z3,z177,z5,z6])],[(0,[z69,z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z38,z3,z4,z5,z6]),(0,[z7,z103,z1,z3,z4,z5,z62]),(0,[z7,z1,z21,z3,z4,z5,z55])],[(0,[z7,z1,z648,z3,z4,z5,z6]),(0,[z649,z7,z1,z3,z4,z5,z6]),(0,[z176,z7,z1,z3,z4,z5,z6]),(0,[z7,z103,z1,z3,z4,z48,z6]),(0,[z7,z650,z1,z3,z4,z5,z6])]],
   [[(0,[z198,z7,z1,z3,z4,z90,z6]),(0,[z7,z1,z3,z4,z5,z6,z651]),(0,[z7,z1,z652,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z5,z70]),(0,[z7,z1,z3,z4,z5,z6,z238])],[(0,[z7,z1,z3,z653,z4,z5,z6]),(0,[z87,z1,z3,z4,z307,z5,z6]),(0,[z7,z1,z3,z654,z26,z5,z6]),(0,[z655,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z496,z6]),(0,[z7,z1,z38,z4,z5,z39,z6]),(0,[z7,z1,z17,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z116,z6])],[(0,[z7,z2,z3,z4,z65,z5,z6]),(0,[z656,z7,z1,z3,z4,z5,z6]),(0,[z657,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z658,z3,z4,z5,z6]),(0,[z7,z301,z3,z4,z5,z6,z117]),(0,[z69,z7,z20,z1,z3,z5,z6]),(0,[z7,z1,z659,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z61,z116])],[(0,[z207,z7,z1,z3,z26,z5,z6]),(0,[z87,z7,z450,z3,z4,z5,z6]),(0,[z7,z1,z660,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z661,z6]),(0,[z7,z662,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z65,z5,z6]),(0,[z7,z1,z3,z663,z4,z5,z6]),(0,[z7,z1,z3,z4,z664,z5,z6])],[(0,[z75,z7,z1,z3,z4,z5,z6]),(0,[z7,z84,z1,z3,z4,z61,z5]),(0,[z7,z1,z3,z4,z5,z665,z6]),(0,[z7,z1,z3,z4,z5,z6,z666])],[(0,[z667,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z668,z5,z6]),(0,[z7,z1,z3,z4,z5,z669,z6]),(0,[z7,z1,z3,z4,z18,z90,z6]),(0,[z7,z1,z670,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z671,z6]),(0,[z7,z1,z125,z3,z26,z5,z6]),(0,[z7,z1,z3,z26,z5,z316,z6]),(0,[z7,z1,z3,z4,z5,z672,z6])]],
   [[(0,[z379,z7,z1,z3,z307,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z673]),(0,[z7,z1,z3,z4,z5,z674,z6]),(0,[z675,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z22])],[(0,[z373,z7,z1,z3,z4,z97,z6]),(1,[z7,z1,z3,z4,z5,z314]),(0,[z7,z1,z3,z4,z676,z5,z6])],[(0,[z7,z1,z421,z3,z4,z5,z6]),(0,[z677,z7,z1,z3,z4,z5,z6]),(0,[z87,z7,z1,z467,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z97,z6]),(0,[z7,z20,z1,z3,z5,z46,z6]),(1,[z153,z1,z3,z4,z5,z6]),(0,[z7,z1,z131,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z91,z6])],[(0,[z678,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z679,z4,z5,z6]),(0,[z1,z3,z40,z4,z307,z5,z6]),(0,[z7,z1,z3,z4,z5,z46,z22]),(0,[z7,z113,z1,z3,z4,z159,z6]),(0,[z7,z1,z3,z4,z680,z5,z6]),(0,[z681,z7,z1,z3,z4,z5,z6]),(0,[z7,z179,z1,z3,z4,z5,z6])],[(1,[z7,z44,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z682])],[(0,[z7,z1,z2,z3,z26,z5,z6]),(0,[z7,z1,z683,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z684,z6])],[(0,[z7,z685,z1,z3,z4,z5,z6]),(0,[z7,z140,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z72,z5,z6]),(0,[z686,z7,z1,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z5,z27]),(0,[z7,z1,z3,z687,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z24,z4,z5,z6]),(0,[z7,z1,z3,z149,z26,z5,z6])],[(0,[z7,z1,z688,z3,z4,z5,z6]),(0,[z7,z347,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z654,z5,z6]),(0,[z7,z1,z689,z3,z4,z5,z6]),(0,[z7,z690,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z18,z5,z144,z6])],[(1,[z379,z1,z3,z40,z5,z6]),(0,[z691,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z147,z3,z32,z5,z6]),(0,[z7,z692,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z693,z6]),(0,[z7,z1,z3,z26,z5,z6,z117]),(0,[z7,z694,z1,z3,z4,z5,z6])],[(0,[z7,z1,z695,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z696,z5,z6]),(0,[z7,z697,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z350,z5,z6]),(0,[z7,z622,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z698,z5,z6]),(1,[z112,z1,z3,z4,z5,z210]),(0,[z7,z1,z358,z3,z26,z5,z6]),(0,[z7,z20,z1,z4,z26,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z699]),(0,[z87,z7,z1,z3,z4,z477,z6]),(0,[z87,z7,z1,z3,z4,z5,z325]),(0,[z7,z1,z700,z3,z4,z5,z6]),(0,[z7,z31,z1,z131,z4,z5,z6]),(0,[z7,z20,z1,z3,z26,z5,z6]),(0,[z7,z1,z701,z3,z4,z5,z6]),(0,[z7,z1,z702,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z703,z5,z6])],[(0,[z7,z1,z3,z4,z704,z5,z6]),(0,[z7,z1,z3,z4,z705,z5,z6]),(0,[z112,z7,z1,z3,z4,z5,z210]),(0,[z7,z1,z3,z4,z5,z252,z6]),(0,[z706,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z37,z6]),(0,[z7,z1,z147,z3,z4,z5,z39]),(0,[z7,z1,z3,z4,z116,z6,z104])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z51,z183,z4,z5,z6]),(0,[z7,z1,z3,z4,z707,z6]),(0,[z7,z1,z3,z4,z91,z285]),(0,[z7,z1,z3,z26,z5,z708]),(0,[z7,z709,z1,z3,z5,z6])],[(0,[z7,z1,z3,z4,z98,z6]),(0,[z7,z247,z301,z1,z3,z4]),(0,[z7,z1,z3,z4,z710,z6])],[(0,[z7,z1,z453,z26,z5,z6]),(0,[z7,z711,z3,z4,z5,z6]),(0,[z7,z1,z438,z26,z5,z6]),(0,[z71,z7,z1,z233,z5,z6]),(0,[z176,z7,z20,z1,z5,z6])],[(0,[z7,z1,z444,z26,z5,z6]),(0,[z395,z7,z1,z26,z5,z6]),(0,[z7,z31,z390,z26,z5,z6]),(0,[z7,z354,z1,z26,z5,z6]),(0,[z7,z417,z1,z3,z5,z434])],[(0,[z7,z1,z448,z26,z5,z6]),(0,[z7,z103,z1,z26,z5,z62]),(0,[z7,z1,z47,z4,z712,z6])],[(0,[z7,z1,z3,z4,z713,z6]),(0,[z7,z714,z1,z26,z5,z6]),(0,[z7,z1,z467,z4,z5,z88]),(0,[z7,z397,z1,z3,z4,z285]),(0,[z7,z1,z3,z4,z6,z715])],[(0,[z7,z1,z3,z4,z716,z6]),(0,[z23,z44,z1,z56,z5,z6]),(0,[z7,z1,z717,z3,z5,z6]),(0,[z71,z336,z4,z99,z5,z6]),(0,[z7,z718,z3,z4,z5,z6]),(0,[z7,z1,z3,z719,z144,z6])],[(0,[z7,z1,z3,z4,z720,z6]),(0,[z7,z1,z3,z721,z5,z6]),(0,[z7,z347,z3,z65,z5,z6]),(0,[z7,z1,z3,z26,z5,z285]),(0,[z7,z301,z3,z4,z722,z6]),(0,[z7,z1,z26,z5,z6,z434]),(0,[z7,z1,z38,z26,z340,z6]),(0,[z7,z103,z1,z3,z4,z459])]],
   [[(0,[z75,z1,z24,z4,z5,z6]),(0,[z7,z1,z3,z26,z76,z6]),(0,[z7,z3,z4,z5,z91,z285]),(0,[z7,z475,z1,z82,z5,z6])],[(0,[z7,z1,z3,z4,z723,z6]),(0,[z7,z1,z3,z724,z5,z6]),(0,[z7,z103,z368,z1,z3,z4]),(0,[z7,z1,z3,z4,z61,z433])],[(0,[z7,z1,z3,z4,z725,z6]),(0,[z726,z1,z3,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z459]),(0,[z727,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z728,z6]),(0,[z7,z1,z3,z4,z5,z729])],[(0,[z7,z1,z3,z730,z5,z6]),(0,[z7,z20,z1,z3,z5,z285]),(0,[z7,z1,z3,z177,z5,z6]),(0,[z7,z20,z711,z3,z5,z6])],[(0,[z7,z20,z1,z3,z76,z6]),(0,[z7,z1,z3,z731,z5,z6]),(0,[z7,z1,z3,z4,z5,z732]),(0,[z7,z1,z3,z733,z5,z6]),(0,[z7,z1,z171,z26,z5,z6]),(0,[z7,z1,z154,z82,z144,z6]),(0,[z7,z1,z54,z260,z5,z6])],[(0,[z7,z1,z734,z4,z5,z6]),(0,[z7,z1,z735,z3,z5,z6]),(0,[z7,z1,z3,z4,z736,z6]),(0,[z7,z301,z3,z26,z204,z6]),(0,[z7,z1,z115,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z737])],[(0,[z7,z1,z3,z4,z5,z6]),(0,[z738,z1,z3,z4,z5,z6]),(0,[z7,z1,z308,z26,z5,z6]),(0,[z7,z1,z739,z26,z5,z6]),(0,[z7,z416,z1,z26,z5,z6]),(0,[z7,z1,z358,z3,z5,z55])]],
   [[(0,[z7,z1,z3,z740,z5,z6]),(0,[z414,z2,z3,z4,z5,z6]),(0,[z7,z1,z402,z3,z18,z6]),(0,[z176,z7,z1,z4,z98,z6]),(0,[z7,z1,z741,z3,z5,z6])],[(0,[z7,z1,z3,z4,z5,z742]),(0,[z7,z1,z3,z4,z477,z88]),(0,[z1,z3,z4,z743,z5,z6]),(0,[z7,z1,z744,z4,z5,z6]),(0,[z7,z1,z745,z3,z26,z5])],[(0,[z7,z1,z746,z4,z5,z6]),(0,[z7,z1,z230,z47,z48,z6]),(0,[z7,z1,z3,z4,z61,z116])],[(0,[z7,z1,z3,z4,z5,z747]),(0,[z130,z7,z1,z26,z5,z6]),(1,[z7,z1,z26,z5,z238])],[(0,[z7,z748,z3,z4,z5,z6]),(0,[z7,z1,z749,z4,z5,z6]),(0,[z71,z7,z31,z26,z5,z6]),(0,[z7,z1,z26,z5,z638,z6]),(0,[z7,z1,z92,z26,z37,z6]),(0,[z7,z1,z230,z26,z5,z6]),(0,[z7,z1,z512,z4,z48,z6])],[(0,[z7,z1,z3,z4,z750,z6]),(0,[z7,z1,z3,z4,z98,z252]),(0,[z7,z1,z751,z3,z5,z6])],[(0,[z7,z752,z3,z4,z5,z6]),(0,[z7,z140,z3,z26,z5,z6]),(1,[z7,z4,z753,z5,z6]),(0,[z7,z256,z31,z131,z5,z6]),(0,[z7,z3,z754,z4,z5,z6]),(0,[z7,z113,z397,z1,z3,z4]),(0,[z7,z397,z110,z3,z4,z6]),(0,[z7,z1,z26,z5,z340,z6]),(0,[z7,z1,z216,z3,z5,z22]),(0,[z7,z214,z1,z260,z5,z6])],[(0,[z1,z752,z3,z4,z5,z6]),(0,[z7,z1,z755,z3,z5,z6]),(0,[z7,z20,z1,z527,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z756,z6]),(0,[z7,z1,z757,z4,z5,z6]),(0,[z7,z1,z4,z753,z5,z6]),(0,[z7,z1,z3,z4,z5,z314])],[(0,[z7,z1,z758,z4,z5,z6]),(0,[z153,z1,z3,z4,z5,z6]),(0,[z759,z7,z1,z4,z5,z6]),(0,[z7,z450,z183,z4,z5,z6]),(0,[z71,z153,z4,z99,z5,z6]),(0,[z7,z1,z21,z260,z5,z22])],[(0,[z176,z7,z44,z1,z5,z6]),(0,[z7,z1,z760,z4,z5,z6]),(0,[z761,z1,z3,z4,z5,z6]),(0,[z7,z1,z507,z26,z5,z6])],[(0,[z7,z1,z56,z26,z5,z6]),(0,[z7,z1,z762,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z504])],[(0,[z7,z1,z763,z3,z5,z6]),(0,[z7,z764,z3,z4,z5,z6]),(0,[z45,z1,z3,z26,z5,z46]),(0,[z7,z3,z4,z91,z117,z104]),(0,[z7,z1,z3,z765,z5,z6]),(0,[z7,z1,z230,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z766])],[(0,[z7,z1,z631,z26,z5,z6]),(0,[z1,z56,z24,z26,z5,z6]),(0,[z7,z1,z767,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z238]),(0,[z7,z1,z768,z3,z4,z6]),(0,[z7,z397,z1,z3,z4,z62]),(0,[z7,z20,z110,z3,z5,z6]),(0,[z7,z1,z54,z3,z5,z737])],[(0,[z7,z1,z3,z119,z76,z6]),(0,[z769,z1,z3,z4,z5,z6]),(0,[z7,z1,z16,z26,z5,z6])],[(0,[z7,z1,z770,z3,z5,z6]),(0,[z7,z771,z1,z3,z5,z6]),(0,[z7,z3,z4,z159,z6,z117]),(0,[z7,z214,z1,z26,z5,z6]),(0,[z7,z1,z125,z4,z37,z6])]],
   [[(0,[z7,z772,z1,z3,z5,z6]),(0,[z49,z1,z3,z4,z97,z6]),(0,[z7,z1,z773,z4,z5,z6]),(0,[z7,z1,z154,z29,z144,z6])],[(0,[z602,z7,z1,z26,z5,z6]),(0,[z7,z300,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z774]),(0,[z45,z20,z1,z3,z5,z46]),(0,[z7,z247,z1,z3,z4,z5]),(1,[z7,z3,z4,z5,z775])],[(0,[z7,z1,z3,z776,z5,z6]),(0,[z7,z1,z3,z4,z248,z6]),(0,[z7,z1,z777,z3,z4,z6]),(1,[z7,z1,z26,z340,z6]),(0,[z7,z1,z54,z3,z5,z55])],[(0,[z1,z3,z734,z4,z5,z6]),(0,[z7,z153,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z252]),(0,[z7,z1,z26,z204,z37,z6]),(0,[z7,z1,z3,z4,z5,z775]),(1,[z7,z1,z3,z4,z715])],[(0,[z531,z7,z4,z99,z5,z6]),(0,[z7,z1,z778,z4,z5,z6]),(0,[z7,z1,z526,z26,z5,z6]),(0,[z112,z1,z3,z4,z5,z210]),(0,[z7,z256,z1,z3,z5,z6]),(0,[z649,z7,z1,z26,z5,z6]),(0,[z7,z779,z3,z4,z5,z6])],[(0,[z7,z1,z3,z780,z5,z6]),(0,[z1,z734,z24,z4,z5,z6]),(0,[z7,z1,z781,z4,z5,z6]),(0,[z7,z1,z152,z3,z340,z6])],[(0,[z7,z1,z3,z4,z712,z6])],[(0,[z7,z1,z3,z782,z5,z6]),(0,[z75,z20,z1,z24,z5,z6]),(0,[z7,z1,z3,z4,z783,z6]),(0,[z7,z1,z784,z3,z5,z6]),(0,[z7,z1,z38,z26,z423,z6]),(0,[z176,z7,z1,z230,z5,z6]),(0,[z7,z1,z47,z4,z48,z6])]],
   [[(0,[z7,z3,z785,z4,z5,z6]),(0,[z7,z1,z128,z147,z5,z62]),(0,[z7,z1,z3,z4,z423,z62])],[(0,[z7,z1,z3,z4,z5,z786]),(0,[z7,z1,z3,z4,z5,z787]),(0,[z7,z20,z1,z92,z37,z6])],[(0,[z7,z1,z3,z4,z5,z788]),(0,[z75,z1,z24,z4,z76,z6]),(0,[z7,z1,z21,z3,z5,z22])],[(0,[z7,z1,z183,z4,z5,z325]),(0,[z7,z789,z3,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z542]),(0,[z7,z790,z3,z26,z5,z6]),(0,[z7,z1,z230,z3,z5,z27])],[(0,[z7,z140,z3,z119,z5,z6]),(0,[z153,z1,z3,z4,z248,z6]),(0,[z7,z3,z4,z753,z5,z6]),(0,[z7,z31,z390,z4,z5,z6]),(0,[z7,z623,z3,z4,z204,z6]),(0,[z7,z1,z3,z4,z791,z6])],[(0,[z153,z1,z3,z4,z5,z252]),(0,[z7,z113,z3,z4,z159,z117]),(0,[z7,z20,z1,z173,z5,z6])],[(0,[z7,z20,z450,z3,z5,z6]),(0,[z7,z1,z3,z26,z5,z88]),(0,[z7,z1,z26,z90,z37,z6]),(0,[z336,z1,z3,z72,z5,z6]),(0,[z7,z397,z1,z3,z26,z6]),(0,[z7,z792,z3,z26,z5,z6]),(1,[z7,z1,z26,z5,z27]),(0,[z7,z1,z21,z3,z5,z737])],[(0,[z1,z3,z4,z793,z97,z6]),(0,[z7,z794,z1,z3,z5,z6]),(0,[z7,z247,z1,z3,z4,z61])]],
   [[(0,[z7,z1,z4,z5,z795,z6]),(0,[z7,z1,z796,z4,z5,z6]),(0,[z1,z3,z4,z5,z797,z210]),(0,[z7,z1,z798,z4,z5,z6]),(0,[z7,z799,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z76,z6]),(0,[z7,z421,z3,z106,z5,z6]),(0,[z7,z1,z700,z3,z5,z22]),(0,[z71,z7,z102,z4,z5,z6]),(0,[z7,z800,z1,z26,z5,z6])],[(0,[z7,z1,z3,z801,z5,z6]),(0,[z7,z802,z3,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z699]),(0,[z7,z51,z3,z26,z5,z6]),(0,[z7,z1,z803,z3,z5,z6]),(0,[z7,z84,z3,z4,z61,z91]),(0,[z7,z1,z216,z3,z5,z58]),(0,[z7,z1,z804,z4,z5,z6])],[(0,[z96,z603,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z5,z88]),(0,[z87,z1,z3,z307,z5,z88]),(0,[z7,z271,z3,z4,z91,z6]),(0,[z7,z1,z3,z4,z159,z187]),(0,[z7,z1,z805,z4,z5,z6]),(0,[z7,z1,z26,z5,z37,z6]),(0,[z7,z1,z173,z26,z5,z6]),(0,[z7,z1,z147,z32,z5,z62])],[(0,[z7,z1,z3,z4,z5,z806]),(0,[z7,z1,z3,z4,z5,z807]),(0,[z7,z123,z3,z4,z303,z91]),(0,[z7,z247,z1,z3,z4,z104]),(0,[z808,z7,z1,z4,z5,z6])],[(0,[z198,z1,z3,z26,z90,z6]),(0,[z7,z1,z3,z4,z5,z809])],[(0,[z7,z0,z31,z26,z5,z6]),(0,[z7,z810,z3,z4,z5,z6]),(0,[z112,z1,z3,z4,z5,z797]),(0,[z7,z1,z3,z811,z5,z6]),(0,[z7,z123,z3,z4,z91,z285])],[(0,[z7,z1,z812,z3,z5,z6]),(0,[z87,z51,z3,z307,z5,z6]),(0,[z71,z7,z1,z26,z98,z6]),(0,[z7,z301,z3,z4,z204,z6]),(0,[z7,z1,z813,z3,z4,z5]),(0,[z7,z1,z26,z5,z564,z6])]],
   [[(0,[z7,z1,z3,z4,z814,z6]),(0,[z75,z140,z24,z4,z5,z6]),(0,[z1,z3,z743,z307,z5,z6]),(0,[z7,z1,z26,z5,z6,z27]),(0,[z7,z1,z147,z4,z5,z815])],[(0,[z7,z1,z3,z4,z5,z816]),(0,[z7,z1,z3,z817,z5,z6])],[(0,[z198,z20,z1,z3,z90,z6]),(0,[z7,z1,z3,z4,z818,z6])],[(0,[z7,z819,z3,z4,z5,z6]),(0,[z7,z51,z3,z4,z52,z6]),(0,[z7,z1,z3,z4,z116,z285]),(0,[z7,z397,z3,z4,z91,z6]),(0,[z7,z103,z1,z3,z4,z104])],[(0,[z752,z2,z3,z4,z5,z6]),(0,[z421,z3,z24,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z574]),(0,[z7,z20,z1,z109,z5,z6])],[(0,[z7,z1,z3,z820,z5,z6]),(0,[z75,z1,z734,z4,z5,z6]),(0,[z7,z20,z1,z82,z5,z6])],[(0,[z7,z3,z4,z5,z159,z117]),(0,[z7,z1,z3,z93,z5,z6])],[(0,[z7,z140,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z821]),(0,[z7,z1,z183,z4,z5,z88]),(0,[z7,z1,z822,z3,z5,z6]),(0,[z7,z103,z1,z3,z4,z67]),(0,[z7,z1,z17,z3,z18,z6])]],
   [[(0,[z415,z2,z3,z4,z5,z6]),(0,[z7,z140,z3,z4,z5,z70])],[(0,[z7,z1,z3,z823,z5,z6]),(1,[z7,z3,z4,z91,z285]),(0,[z7,z1,z26,z61,z5,z62])],[(0,[z7,z824,z1,z3,z4,z5]),(0,[z7,z1,z82,z26,z5,z6]),(0,[z7,z1,z3,z4,z715,z104])],[(0,[z7,z1,z3,z4,z825,z6]),(0,[z7,z247,z1,z3,z4,z159])],[(0,[z7,z1,z3,z4,z826,z6]),(0,[z7,z347,z31,z26,z5,z6]),(0,[z7,z1,z3,z4,z827,z6]),(0,[z7,z1,z3,z4,z5,z828]),(0,[z829,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z26,z830,z6]),(0,[z7,z1,z260,z26,z5,z6]),(0,[z7,z1,z17,z3,z431,z6]),(0,[z7,z831,z3,z4,z5,z6]),(0,[z7,z1,z152,z3,z423,z6])],[(0,[z7,z1,z3,z4,z832,z6]),(0,[z7,z1,z3,z4,z833,z6]),(0,[z7,z1,z3,z72,z5,z238]),(0,[z7,z1,z3,z4,z834,z6]),(0,[z7,z1,z26,z5,z598,z6]),(0,[z7,z1,z26,z5,z6,z95])],[(0,[z7,z1,z3,z106,z476,z6]),(0,[z45,z1,z3,z4,z5,z797]),(0,[z7,z1,z109,z26,z5,z6]),(0,[z7,z1,z3,z26,z114,z6]),(0,[z7,z1,z38,z26,z5,z6]),(1,[z7,z110,z3,z4,z104])]],
   [[(0,[z7,z1,z835,z3,z5,z6]),(0,[z7,z1,z26,z5,z98,z6]),(0,[z7,z662,z1,z26,z5,z6]),(1,[z7,z800,z1,z5,z6])],[(0,[z7,z301,z3,z4,z116,z117]),(0,[z7,z1,z836,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z837]),(0,[z7,z1,z110,z3,z4,z104]),(0,[z7,z1,z3,z838,z5,z6]),(0,[z7,z103,z1,z3,z4,z715])],[(0,[z7,z1,z724,z26,z5,z6]),(0,[z7,z103,z1,z3,z4,z159]),(0,[z176,z7,z1,z152,z5,z6]),(0,[z7,z110,z3,z4,z5,z104])],[(0,[z7,z450,z3,z26,z5,z6]),(0,[z7,z1,z455,z4,z5,z62]),(0,[z839,z1,z3,z4,z5,z6]),(0,[z7,z247,z84,z3,z4,z5]),(0,[z7,z113,z3,z4,z74,z117]),(0,[z7,z1,z359,z26,z5,z6])],[(0,[z7,z1,z3,z4,z159,z6]),(0,[z7,z20,z1,z3,z114,z6]),(0,[z7,z1,z216,z26,z5,z62]),(0,[z7,z1,z3,z840,z5,z6])],[(0,[z7,z1,z3,z841,z5,z6]),(0,[z7,z1,z3,z4,z5,z842]),(0,[z7,z1,z47,z26,z5,z27])],[(0,[z7,z1,z843,z4,z5,z6]),(0,[z7,z103,z84,z301,z3,z4]),(0,[z7,z20,z1,z519,z5,z6])],[(0,[z7,z421,z3,z4,z476,z6]),(0,[z7,z1,z844,z3,z5,z6]),(0,[z7,z20,z1,z506,z5,z6]),(0,[z7,z1,z26,z5,z187,z62]),(0,[z7,z110,z3,z26,z5,z6])]],
   [[(0,[z7,z714,z1,z3,z5,z6]),(0,[z87,z450,z3,z307,z5,z6]),(0,[z7,z1,z845,z3,z4,z6]),(0,[z7,z1,z627,z26,z5,z6]),(0,[z7,z1,z412,z26,z5,z6]),(0,[z625,z7,z1,z26,z5,z6]),(0,[z7,z20,z1,z29,z5,z6]),(0,[z7,z1,z4,z48,z712,z6])],[(0,[z7,z1,z467,z26,z5,z6]),(0,[z7,z31,z1,z26,z5,z6]),(0,[z7,z20,z1,z683,z5,z6]),(0,[z7,z113,z3,z4,z114,z117]),(0,[z7,z84,z3,z26,z5,z187]),(0,[z7,z1,z26,z5,z139,z6]),(0,[z7,z223,z168,z3,z5,z6])],[(0,[z7,z1,z3,z106,z5,z484]),(0,[z7,z1,z3,z846,z5,z6])],[(0,[z7,z1,z3,z4,z847,z6]),(0,[z7,z848,z3,z4,z5,z6]),(0,[z7,z579,z1,z26,z5,z6]),(0,[z7,z247,z110,z3,z4,z5])],[(0,[z7,z1,z3,z849,z5,z6]),(0,[z7,z450,z3,z4,z52,z6]),(1,[z7,z1,z26,z98,z6]),(0,[z7,z1,z3,z26,z850,z6]),(0,[z7,z1,z428,z26,z37,z6]),(0,[z7,z1,z3,z851,z5,z6])],[(0,[z7,z1,z3,z4,z852,z6]),(0,[z7,z1,z195,z26,z5,z6]),(0,[z853,z1,z3,z4,z5,z6]),(0,[z7,z110,z3,z4,z37,z6])],[(0,[z7,z1,z3,z4,z5,z854]),(0,[z207,z2,z3,z26,z5,z6]),(0,[z87,z1,z467,z307,z5,z6]),(0,[z7,z855,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z204,z285]),(0,[z7,z1,z3,z4,z5,z165]),(0,[z7,z1,z856,z4,z5,z6])],[(0,[z7,z792,z3,z4,z5,z6]),(0,[z7,z1,z3,z857,z5,z6])]],
   [[(0,[z7,z347,z3,z249,z5,z6])],[(0,[z7,z1,z858,z4,z5,z6]),(0,[z7,z1,z3,z4,z859,z6]),(0,[z7,z1,z3,z26,z5,z484]),(0,[z23,z1,z734,z4,z5,z6]),(0,[z7,z1,z860,z4,z5,z6]),(0,[z7,z247,z3,z4,z5,z117]),(0,[z7,z1,z147,z4,z5,z62])],[(0,[z7,z421,z3,z4,z5,z484]),(0,[z7,z1,z3,z4,z861,z6]),(0,[z7,z1,z467,z4,z52,z6]),(0,[z7,z1,z739,z3,z5,z6]),(1,[z7,z1,z3,z719,z6])],[(0,[z491,z2,z3,z4,z5,z6]),(0,[z7,z51,z3,z4,z5,z6]),(0,[z7,z862,z3,z4,z5,z6]),(0,[z7,z1,z3,z863,z5,z6]),(0,[z270,z7,z1,z26,z5,z6]),(0,[z7,z1,z864,z3,z26,z6])],[(0,[z7,z1,z467,z40,z5,z6]),(0,[z153,z1,z3,z72,z5,z6]),(0,[z7,z1,z865,z4,z5,z6]),(0,[z7,z1,z3,z4,z866,z5])],[(0,[z7,z867,z1,z3,z5,z6]),(0,[z7,z1,z3,z26,z477,z6]),(0,[z7,z1,z3,z26,z5,z325]),(0,[z7,z1,z3,z4,z868,z6]),(0,[z7,z1,z3,z4,z5,z869]),(0,[z7,z1,z428,z3,z277,z6]),(0,[z7,z1,z152,z26,z5,z6]),(0,[z7,z1,z870,z3,z5,z6])],[(0,[z7,z20,z1,z3,z5,z484]),(0,[z7,z1,z3,z4,z871,z6]),(0,[z7,z1,z47,z26,z37,z6]),(0,[z7,z1,z872,z3,z5,z6])],[(0,[z7,z31,z131,z26,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z873,z6]),(0,[z7,z1,z3,z233,z5,z6]),(0,[z7,z301,z20,z3,z204,z6]),(0,[z7,z110,z3,z4,z6,z104])],[(0,[z7,z140,z3,z4,z76,z6]),(0,[z7,z1,z3,z4,z5,z874]),(0,[z176,z153,z1,z4,z5,z6]),(0,[z875,z1,z3,z4,z5,z6]),(0,[z7,z1,z26,z5,z496,z6]),(0,[z7,z1,z876,z3,z5,z6])],[(0,[z7,z421,z3,z4,z5,z70]),(0,[z7,z20,z1,z3,z477,z6]),(0,[z87,z1,z3,z307,z477,z6]),(0,[z7,z20,z1,z3,z5,z325]),(0,[z87,z1,z3,z307,z5,z325]),(0,[z373,z1,z3,z4,z793,z6]),(0,[z7,z223,z1,z26,z5,z6]),(0,[z7,z1,z3,z877,z5,z6]),(0,[z7,z1,z878,z3,z5,z6]),(0,[z7,z1,z615,z4,z48,z6]),(0,[z7,z1,z4,z26,z340,z6])],[(0,[z96,z0,z3,z4,z5,z6]),(0,[z7,z1,z879,z3,z5,z6]),(0,[z7,z1,z64,z26,z5,z6]),(0,[z7,z1,z3,z26,z340,z6]),(0,[z7,z179,z3,z26,z5,z6]),(0,[z7,z1,z230,z3,z5,z165])],[(0,[z7,z1,z3,z5,z880,z6]),(0,[z7,z1,z3,z4,z5,z881]),(0,[z7,z1,z381,z26,z5,z6]),(0,[z188,z1,z3,z350,z5,z6]),(0,[z7,z1,z382,z26,z5,z6]),(0,[z7,z103,z179,z3,z4,z104])],[(0,[z7,z44,z1,z183,z5,z6]),(0,[z7,z1,z882,z4,z5,z6]),(0,[z7,z3,z4,z5,z187,z775]),(0,[z7,z103,z1,z26,z37,z6])],[(0,[z7,z883,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z884,z6]),(0,[z96,z20,z0,z3,z5,z6]),(0,[z23,z1,z56,z26,z5,z6]),(0,[z7,z1,z3,z4,z52,z325]),(0,[z7,z1,z385,z26,z5,z6]),(0,[z7,z123,z3,z26,z91,z6]),(0,[z7,z1,z26,z5,z671,z6]),(0,[z7,z1,z3,z885,z5,z6])],[(0,[z96,z752,z3,z4,z5,z6]),(0,[z7,z1,z3,z886,z5,z6]),(0,[z7,z887,z3,z4,z5,z6])]],
   [[(0,[z0,z752,z3,z4,z5,z6]),(0,[z7,z1,z888,z3,z4,z5]),(0,[z270,z7,z20,z1,z5,z6]),(0,[z7,z20,z1,z3,z340,z6])],[(0,[z7,z1,z3,z199,z5,z238]),(0,[z7,z1,z3,z4,z5,z889]),(0,[z7,z1,z38,z26,z5,z39])],[(0,[z7,z1,z890,z4,z5,z6]),(0,[z7,z123,z110,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z815]),(0,[z7,z1,z891,z4,z5,z6])],[(0,[z7,z1,z4,z892,z5,z6]),(0,[z7,z1,z3,z4,z5,z893]),(0,[z7,z1,z26,z5,z210,z62]),(0,[z7,z1,z3,z4,z5,z894]),(0,[z7,z247,z1,z3,z26,z5]),(0,[z7,z577,z3,z4,z5,z117]),(0,[z7,z475,z1,z26,z5,z6])],[(0,[z71,z7,z26,z99,z5,z6]),(0,[z7,z1,z895,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z708]),(0,[z7,z1,z687,z26,z5,z6]),(0,[z7,z1,z92,z93,z37,z6])],[(0,[z7,z1,z24,z26,z5,z6]),(0,[z7,z1,z609,z3,z144,z6]),(0,[z7,z1,z3,z4,z896,z6]),(0,[z7,z286,z3,z4,z5,z117]),(0,[z7,z460,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z897,z6]),(0,[z7,z110,z3,z4,z61,z6]),(0,[z7,z103,z110,z3,z4,z104])],[(0,[z7,z1,z183,z4,z477,z6]),(0,[z7,z1,z3,z898,z5,z6]),(0,[z7,z1,z3,z4,z676,z116]),(0,[z7,z1,z512,z26,z5,z6]),(0,[z7,z1,z260,z4,z5,z6]),(0,[z7,z1,z47,z4,z48,z165]),(0,[z7,z1,z3,z5,z719,z6])],[(0,[z7,z1,z899,z4,z5,z6]),(0,[z7,z1,z4,z5,z815,z62])]],
   [[(0,[z7,z1,z3,z900,z5,z6]),(0,[z7,z1,z3,z4,z476,z484]),(0,[z7,z1,z3,z4,z5,z901]),(0,[z270,z7,z1,z199,z5,z6]),(0,[z7,z276,z3,z65,z5,z6]),(0,[z7,z1,z47,z4,z219,z6])],[(0,[z7,z1,z3,z4,z5,z902]),(0,[z7,z1,z3,z4,z5,z903]),(0,[z7,z20,z421,z3,z5,z6]),(0,[z7,z1,z3,z904,z5,z6])],[(0,[z1,z2,z24,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z905]),(0,[z338,z0,z3,z4,z5,z6]),(0,[z906,z1,z3,z4,z5,z6]),(0,[z7,z276,z3,z754,z5,z6]),(0,[z7,z1,z299,z26,z5,z6])],[(0,[z7,z907,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z908,z6]),(0,[z909,z1,z3,z4,z5,z6]),(0,[z7,z1,z910,z3,z4,z5]),(0,[z7,z1,z3,z4,z5,z285]),(0,[z7,z397,z1,z3,z4,z104])],[(0,[z7,z450,z3,z4,z5,z6]),(0,[z7,z1,z56,z119,z5,z6]),(0,[z7,z1,z3,z911,z5,z6])],[(0,[z7,z397,z301,z3,z4,z6]),(0,[z7,z1,z26,z703,z5,z6])],[(0,[z7,z912,z3,z4,z5,z6]),(0,[z7,z1,z688,z26,z5,z6])],[(0,[z7,z1,z14,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z913]),(0,[z7,z914,z3,z4,z5,z6]),(0,[z7,z1,z26,z5,z8,z6]),(0,[z7,z3,z4,z204,z722,z6]),(1,[z7,z3,z4,z159,z117]),(0,[z7,z1,z19,z26,z5,z6]),(0,[z7,z915,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z916,z6]),(0,[z7,z1,z3,z4,z476,z70]),(0,[z7,z917,z3,z4,z5,z6]),(0,[z7,z1,z580,z26,z5,z6]),(0,[z7,z20,z1,z183,z5,z6]),(0,[z7,z1,z3,z4,z5,z918]),(0,[z7,z113,z397,z3,z4,z117]),(0,[z7,z1,z26,z5,z6,z266])],[(0,[z23,z1,z56,z317,z5,z6]),(0,[z7,z1,z3,z4,z248,z252]),(0,[z7,z1,z3,z4,z159,z117]),(0,[z7,z1,z17,z82,z5,z6])],[(0,[z7,z1,z467,z4,z5,z6]),(0,[z7,z1,z3,z4,z52,z88]),(0,[z188,z1,z3,z307,z5,z6]),(0,[z7,z276,z1,z109,z5,z6]),(0,[z7,z84,z3,z4,z5,z187]),(0,[z7,z20,z1,z3,z919,z6]),(0,[z7,z1,z3,z920,z5,z6])],[(0,[z96,z1,z24,z26,z5,z6]),(0,[z7,z421,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z921]),(0,[z75,z1,z24,z4,z5,z484]),(0,[z7,z1,z3,z4,z5,z922]),(0,[z7,z1,z3,z923,z5,z6])],[(0,[z1,z24,z654,z26,z5,z6]),(0,[z7,z1,z634,z26,z5,z6]),(0,[z7,z1,z3,z26,z5,z303]),(0,[z7,z800,z1,z3,z5,z6]),(0,[z7,z1,z29,z26,z5,z6])],[(0,[z7,z1,z107,z26,z5,z6]),(0,[z7,z1,z924,z3,z5,z6]),(0,[z7,z1,z128,z3,z5,z6])],[(0,[z7,z1,z3,z925,z5,z6]),(0,[z7,z1,z926,z4,z5,z6]),(0,[z7,z1,z3,z4,z927,z6])],[(0,[z207,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z928]),(0,[z7,z1,z3,z4,z5,z929]),(0,[z373,z1,z3,z26,z97,z6]),(0,[z470,z1,z3,z4,z90,z6]),(0,[z153,z1,z3,z199,z5,z6]),(0,[z336,z1,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z930]),(0,[z7,z1,z931,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z932,z6]),(0,[z7,z1,z3,z4,z6,z933]),(0,[z7,z1,z92,z4,z37,z6]),(0,[z7,z3,z4,z5,z6,z934])],[(0,[z7,z1,z3,z935,z5,z6]),(0,[z1,z3,z4,z90,z793,z6]),(0,[z7,z20,z1,z3,z5,z303]),(0,[z7,z1,z47,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z936])],[(0,[z207,z752,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z937]),(0,[z7,z1,z26,z91,z37,z6]),(0,[z7,z1,z3,z5,z55,z737])],[(0,[z7,z1,z24,z119,z5,z6]),(0,[z7,z1,z3,z4,z938,z6]),(0,[z7,z1,z939,z4,z5,z6]),(0,[z7,z1,z3,z26,z423,z6]),(0,[z7,z1,z125,z3,z324,z6]),(0,[z7,z1,z3,z127,z5,z27]),(0,[z7,z1,z3,z4,z940,z6])],[(0,[z7,z1,z745,z3,z4,z5]),(0,[z373,z20,z1,z3,z97,z6]),(0,[z336,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z941]),(0,[z7,z113,z3,z26,z5,z117]),(0,[z7,z1,z942,z3,z5,z6])],[(1,[z1,z3,z4,z793,z6]),(0,[z7,z1,z489,z26,z5,z6]),(0,[z7,z103,z1,z3,z26,z104]),(0,[z7,z943,z3,z4,z5,z6]),(0,[z7,z1,z944,z3,z5,z6])],[(0,[z7,z1,z3,z4,z945,z6]),(0,[z7,z1,z3,z946,z5,z6]),(0,[z7,z1,z3,z4,z477,z6]),(0,[z7,z1,z3,z4,z5,z325]),(0,[z7,z1,z467,z307,z5,z6]),(0,[z1,z3,z4,z5,z793,z6]),(0,[z7,z20,z800,z1,z5,z6])],[(0,[z7,z1,z947,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z948]),(0,[z584,z0,z3,z4,z5,z6]),(0,[z7,z1,z3,z949,z5,z6]),(0,[z7,z1,z3,z72,z98,z6]),(0,[z71,z7,z4,z99,z5,z238]),(0,[z7,z950,z1,z3,z4,z6]),(0,[z7,z1,z951,z3,z4,z5]),(0,[z7,z1,z26,z5,z6,z81])]],
   [[(0,[z7,z1,z26,z5,z83,z6]),(0,[z7,z1,z3,z4,z5,z952]),(0,[z45,z1,z3,z4,z5,z46]),(0,[z71,z7,z1,z26,z5,z6]),(0,[z7,z31,z131,z4,z5,z6]),(0,[z7,z20,z1,z3,z423,z6])],[(0,[z130,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z953,z5,z6]),(0,[z7,z397,z20,z1,z3,z6]),(0,[z7,z954,z1,z3,z5,z6]),(0,[z7,z1,z3,z177,z340,z6])],[(0,[z7,z1,z3,z4,z955,z6]),(0,[z7,z1,z3,z956,z5,z6]),(0,[z87,z1,z3,z743,z5,z6]),(0,[z7,z276,z168,z3,z5,z6]),(0,[z7,z1,z3,z4,z957,z6])],[(0,[z7,z1,z183,z26,z5,z6]),(0,[z7,z1,z3,z4,z958,z6]),(0,[z7,z1,z3,z4,z959,z6]),(0,[z7,z1,z26,z5,z105,z6]),(0,[z7,z103,z1,z3,z4,z320])],[(0,[z2,z3,z14,z4,z5,z6]),(0,[z7,z1,z3,z4,z61,z545])],[(0,[z675,z1,z3,z4,z5,z210]),(0,[z7,z1,z122,z26,z5,z6]),(0,[z7,z1,z472,z26,z5,z6]),(0,[z7,z1,z3,z4,z960,z6]),(0,[z7,z1,z38,z32,z5,z6])],[(0,[z7,z1,z3,z961,z5,z6]),(0,[z1,z3,z40,z743,z5,z6])],[(0,[z7,z1,z962,z4,z5,z6]),(0,[z7,z247,z1,z3,z4,z48]),(0,[z7,z3,z4,z5,z775,z117]),(0,[z279,z236,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z464,z116])]],
   [[(0,[z207,z20,z2,z3,z5,z6]),(0,[z87,z1,z183,z307,z5,z6]),(0,[z87,z133,z1,z3,z5,z6]),(0,[z479,z1,z3,z4,z97,z6]),(0,[z7,z1,z3,z4,z5,z963]),(0,[z7,z1,z3,z4,z48,z165])],[(0,[z7,z421,z3,z119,z5,z6]),(0,[z7,z1,z3,z26,z476,z6]),(0,[z7,z1,z378,z4,z48,z6]),(0,[z7,z1,z3,z4,z964,z6]),(0,[z7,z1,z3,z4,z965,z6])],[(0,[z7,z1,z966,z4,z5,z6]),(0,[z7,z1,z3,z5,z6,z967]),(0,[z7,z20,z1,z3,z5,z968])],[(0,[z7,z1,z969,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z970]),(0,[z7,z1,z3,z971,z5,z6])],[(0,[z7,z972,z1,z3,z4,z6]),(0,[z7,z973,z3,z4,z5,z6]),(0,[z7,z1,z183,z4,z52,z6]),(0,[z7,z974,z1,z3,z5,z6]),(0,[z336,z1,z3,z199,z5,z6]),(0,[z7,z1,z269,z26,z5,z6]),(0,[z7,z1,z836,z3,z5,z6])],[(0,[z75,z1,z24,z106,z5,z6]),(0,[z7,z1,z3,z72,z5,z6]),(0,[z7,z1,z3,z26,z98,z6])],[(0,[z7,z20,z1,z3,z476,z6]),(0,[z7,z20,z1,z467,z5,z6]),(0,[z7,z1,z4,z26,z5,z238]),(0,[z7,z639,z3,z4,z5,z187]),(0,[z7,z20,z1,z147,z5,z62]),(0,[z7,z1,z975,z4,z5,z6])],[(0,[z7,z1,z3,z26,z5,z238]),(0,[z7,z790,z3,z4,z5,z6]),(0,[z7,z20,z1,z260,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z976,z6]),(0,[z7,z123,z3,z4,z91,z314]),(0,[z176,z7,z800,z1,z5,z6]),(0,[z7,z1,z93,z5,z37,z6])],[(0,[z7,z1,z351,z26,z5,z6]),(0,[z7,z1,z977,z4,z5,z6]),(0,[z978,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z979,z5,z6]),(0,[z7,z1,z980,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z88]),(0,[z7,z20,z1,z3,z98,z6]),(0,[z7,z1,z3,z4,z5,z981]),(0,[z7,z20,z31,z131,z5,z6]),(0,[z7,z110,z3,z4,z5,z39])],[(0,[z7,z982,z3,z4,z5,z6]),(0,[z7,z1,z26,z97,z37,z6]),(0,[z71,z7,z1,z26,z248,z6]),(0,[z7,z1,z3,z4,z5,z983]),(0,[z176,z7,z1,z4,z340,z6])],[(0,[z7,z1,z3,z106,z5,z6]),(0,[z75,z1,z24,z26,z5,z6]),(0,[z336,z1,z3,z4,z5,z238]),(0,[z7,z20,z1,z3,z5,z238]),(0,[z71,z7,z1,z26,z5,z252]),(0,[z7,z301,z3,z4,z6,z362])],[(0,[z75,z421,z24,z4,z5,z6]),(0,[z7,z1,z3,z106,z5,z70]),(0,[z7,z984,z1,z3,z4,z5]),(0,[z7,z3,z4,z91,z6,z285]),(0,[z7,z1,z101,z26,z5,z6]),(0,[z7,z800,z1,z4,z5,z6]),(0,[z7,z1,z339,z26,z5,z6])],[(0,[z7,z1,z3,z4,z919,z6]),(0,[z7,z1,z985,z4,z5,z6]),(0,[z7,z1,z544,z4,z37,z6]),(0,[z7,z1,z3,z986,z5,z6]),(0,[z7,z622,z1,z26,z5,z6]),(0,[z7,z20,z1,z47,z48,z6]),(0,[z7,z1,z521,z4,z5,z62])],[(0,[z7,z1,z3,z987,z5,z6]),(0,[z7,z1,z173,z4,z5,z6]),(0,[z7,z20,z1,z3,z716,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z988]),(0,[z7,z1,z989,z3,z4,z6]),(0,[z7,z20,z1,z26,z5,z6])],[(0,[z7,z1,z492,z26,z5,z6]),(0,[z7,z1,z3,z990,z5,z6]),(0,[z198,z1,z3,z4,z90,z6]),(0,[z7,z20,z991,z3,z5,z6]),(0,[z7,z138,z1,z3,z496,z6]),(0,[z7,z1,z3,z992,z5,z6]),(0,[z7,z1,z3,z4,z61,z715])],[(0,[z7,z1,z993,z4,z5,z6]),(0,[z7,z1,z3,z4,z994,z6]),(0,[z7,z1,z3,z4,z61,z159])],[(0,[z7,z1,z995,z3,z5,z6]),(0,[z7,z1,z3,z996,z5,z6]),(0,[z7,z997,z1,z3,z5,z6]),(0,[z7,z998,z3,z4,z5,z6]),(0,[z7,z84,z20,z3,z5,z187])],[(0,[z7,z421,z3,z4,z5,z6]),(0,[z7,z1,z3,z26,z5,z70])],[(0,[z7,z1,z3,z999,z5,z6]),(1,[z1,z3,z4,z5,z797]),(0,[z1000,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1001,z5,z6]),(0,[z7,z800,z1,z171,z5,z6])],[(0,[z7,z20,z140,z3,z5,z6]),(0,[z7,z1,z3,z26,z61,z116]),(0,[z7,z1,z1002,z4,z5,z6])],[(0,[z7,z1,z3,z119,z476,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z1003]),(0,[z595,z1,z3,z4,z5,z210]),(0,[z7,z1,z3,z72,z248,z6]),(0,[z7,z1,z1004,z3,z5,z6]),(0,[z7,z1,z3,z1005,z5,z6]),(0,[z7,z1,z152,z3,z5,z6]),(0,[z7,z1,z510,z26,z5,z6])],[(0,[z7,z1006,z1,z3,z5,z6]),(0,[z7,z20,z1,z3,z5,z70]),(0,[z7,z1,z3,z72,z5,z252]),(0,[z7,z1,z3,z177,z423,z6])],[(0,[z7,z1,z1007,z4,z5,z6]),(0,[z7,z1,z3,z199,z98,z6])],[(0,[z7,z20,z51,z3,z5,z6]),(0,[z7,z1,z1008,z3,z5,z6]),(0,[z71,z7,z1,z724,z5,z6]),(0,[z7,z1,z404,z26,z5,z6]),(0,[z7,z20,z1,z3,z61,z116]),(0,[z7,z1,z154,z3,z496,z6])],[(0,[z7,z1,z3,z4,z5,z1009]),(0,[z153,z1,z4,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z1010]),(0,[z7,z1,z3,z4,z5,z1011]),(0,[z7,z1,z3,z26,z5,z314]),(0,[z7,z1,z226,z26,z5,z6]),(0,[z7,z1,z3,z1012,z5,z6]),(1,[z7,z1,z3,z5,z737])],[(0,[z7,z236,z1,z467,z5,z6]),(0,[z153,z1,z3,z26,z5,z6]),(0,[z305,z133,z1,z3,z5,z6]),(0,[z7,z103,z1,z3,z4,z408])],[(0,[z7,z1013,z3,z4,z5,z6]),(0,[z7,z1,z82,z4,z5,z6]),(0,[z1014,z1,z3,z4,z5,z6]),(0,[z7,z1015,z3,z4,z5,z6])],[(0,[z7,z1,z3,z1016,z5,z6])]],
   [[],[(0,[z7,z1,z1017,z4,z5,z6]),(0,[z7,z1,z3,z1018,z5,z6]),(0,[z369,z1,z3,z4,z90,z6]),(0,[z7,z1,z555,z26,z5,z6]),(0,[z7,z1,z142,z26,z5,z6]),(0,[z7,z1,z242,z26,z5,z6]),(0,[z7,z20,z1,z3,z5,z314]),(0,[z7,z1,z3,z4,z830,z6]),(0,[z7,z1,z4,z26,z5,z27]),(0,[z7,z20,z1,z515,z5,z6])],[(0,[z7,z1,z3,z119,z5,z484]),(0,[z7,z1,z529,z26,z5,z6]),(0,[z153,z20,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z98,z238]),(0,[z7,z1,z3,z4,z1019,z6]),(0,[z7,z1,z3,z26,z5,z27])],[(0,[z75,z1,z24,z4,z476,z6]),(0,[z7,z1,z109,z4,z5,z6]),(0,[z7,z1,z3,z4,z114,z6]),(0,[z7,z1,z265,z26,z5,z6]),(0,[z7,z1,z125,z26,z37,z6]),(0,[z7,z1,z26,z5,z6,z244])],[(0,[z7,z1,z183,z4,z5,z6]),(0,[z1,z3,z4,z5,z797,z6]),(0,[z7,z1,z3,z4,z6,z1020]),(0,[z7,z84,z3,z4,z5,z693]),(0,[z7,z1,z3,z4,z1021,z6])],[(0,[z278,z1,z56,z4,z5,z6]),(0,[z7,z123,z3,z4,z722,z6]),(0,[z7,z1,z358,z3,z5,z316]),(0,[z7,z179,z20,z3,z5,z6]),(0,[z7,z1,z4,z712,z37,z6])],[(0,[z7,z1,z3,z4,z5,z968]),(0,[z7,z1,z125,z3,z144,z6])],[(0,[z7,z236,z1,z26,z5,z6]),(0,[z7,z1,z3,z127,z5,z6]),(0,[z7,z20,z1,z3,z5,z27]),(0,[z7,z1,z3,z4,z116,z715])]],
   [[(0,[z7,z1,z3,z1022,z5,z6]),(0,[z112,z1,z3,z26,z5,z210]),(0,[z71,z336,z1,z26,z5,z6]),(0,[z7,z1,z3,z199,z5,z6]),(0,[z7,z301,z3,z4,z5,z285]),(0,[z7,z123,z20,z3,z91,z6]),(0,[z7,z9,z1,z3,z4,z104]),(0,[z7,z133,z1,z26,z5,z6]),(0,[z7,z271,z1,z26,z5,z6]),(0,[z7,z1,z216,z4,z5,z62])],[(0,[z7,z1,z1023,z4,z5,z6]),(0,[z405,z1,z3,z4,z5,z46]),(0,[z7,z1,z265,z4,z37,z6]),(0,[z7,z1,z38,z836,z5,z6])],[(0,[z7,z1,z3,z4,z476,z6]),(0,[z7,z1,z3,z119,z5,z70]),(0,[z7,z1024,z3,z4,z5,z6]),(0,[z7,z3,z754,z65,z5,z6]),(0,[z7,z290,z3,z4,z204,z6]),(0,[z7,z1,z92,z4,z712,z6])],[(0,[z71,z7,z199,z99,z5,z6]),(0,[z7,z110,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1025]),(0,[z7,z1,z154,z3,z144,z6])],[(0,[z7,z1,z3,z4,z5,z1026]),(0,[z7,z1,z3,z1027,z5,z6]),(0,[z7,z301,z110,z3,z4,z6]),(0,[z7,z1,z615,z26,z5,z6]),(0,[z7,z1,z3,z4,z719,z6])],[(0,[z7,z1,z3,z4,z1028,z6]),(0,[z112,z20,z1,z3,z5,z210]),(0,[z7,z1,z26,z37,z116,z6]),(0,[z1029,z1,z3,z4,z5,z6]),(0,[z7,z1,z173,z21,z5,z22])],[(0,[z7,z1,z3,z106,z76,z6]),(0,[z1,z56,z734,z4,z5,z6]),(0,[z7,z174,z1,z109,z5,z6])],[(0,[z1,z3,z4,z5,z46,z797]),(0,[z7,z1,z1030,z4,z5,z6]),(0,[z7,z1,z536,z26,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z1031,z6]),(0,[z7,z1,z3,z4,z793,z6]),(0,[z7,z1,z3,z4,z5,z238]),(0,[z7,z1,z3,z1032,z5,z6]),(0,[z7,z1,z3,z4,z6,z1033]),(1,[z7,z3,z4,z722,z6]),(0,[z7,z1,z3,z4,z850,z6]),(0,[z7,z1,z3,z4,z5,z1034])],[(0,[z7,z1,z3,z4,z5,z1035]),(0,[z7,z1,z3,z4,z5,z1036]),(0,[z279,z1,z3,z40,z5,z6])],[(0,[z7,z1,z26,z5,z282,z6]),(1,[z1,z3,z743,z5,z6]),(0,[z7,z31,z4,z753,z5,z6]),(0,[z1037,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z722,z6])],[(0,[z7,z1,z1038,z4,z5,z6]),(0,[z153,z31,z3,z4,z5,z6]),(0,[z7,z1,z1039,z3,z5,z6]),(0,[z7,z397,z1,z3,z4,z39]),(0,[z7,z1,z38,z26,z5,z62])],[(0,[z7,z1040,z3,z4,z5,z6]),(0,[z7,z1,z230,z29,z5,z6]),(0,[z7,z1,z3,z18,z719,z6])],[(0,[z7,z1,z3,z4,z5,z484]),(0,[z7,z1041,z3,z4,z5,z6]),(0,[z7,z1,z1042,z4,z5,z6]),(0,[z7,z1,z536,z4,z37,z6]),(0,[z7,z1,z1043,z4,z5,z6])],[(0,[z7,z421,z3,z4,z76,z6]),(0,[z75,z1,z24,z4,z5,z70]),(0,[z7,z51,z467,z4,z5,z6]),(0,[z7,z1,z3,z26,z52,z6]),(0,[z7,z247,z20,z1,z3,z5]),(0,[z7,z1,z145,z3,z5,z6])],[(0,[z270,z7,z1,z4,z5,z6]),(0,[z176,z7,z1,z199,z5,z6])]],
   [[(0,[z7,z1044,z3,z4,z5,z6]),(0,[z379,z1,z3,z654,z5,z6]),(0,[z153,z1,z3,z4,z98,z6]),(0,[z71,z7,z4,z99,z98,z6]),(0,[z7,z84,z3,z4,z5,z264]),(0,[z7,z1,z26,z5,z464,z6]),(0,[z7,z1,z47,z26,z5,z165])],[(0,[z7,z1,z3,z1045,z5,z6]),(0,[z7,z1,z3,z4,z5,z1046]),(0,[z7,z1047,z3,z4,z5,z6]),(0,[z7,z1048,z1,z3,z5,z6]),(0,[z7,z1,z3,z26,z5,z1049]),(0,[z7,z110,z3,z4,z5,z116])],[(0,[z153,z1,z3,z4,z5,z238]),(0,[z7,z1,z199,z26,z5,z6]),(0,[z7,z1,z3,z4,z1050,z6]),(0,[z7,z3,z4,z5,z722,z6]),(0,[z7,z1,z21,z3,z5,z434])],[(0,[z7,z20,z1,z3,z52,z6]),(0,[z87,z1,z3,z307,z52,z6]),(0,[z7,z1,z26,z5,z302,z6]),(0,[z71,z153,z1,z26,z5,z6]),(0,[z7,z1,z3,z199,z248,z6]),(0,[z7,z1,z3,z1051,z5,z6]),(0,[z7,z31,z1,z233,z5,z6]),(0,[z7,z577,z3,z4,z91,z6]),(0,[z7,z1,z173,z152,z5,z6])],[(0,[z7,z140,z3,z106,z5,z6]),(0,[z188,z1,z24,z26,z5,z6]),(0,[z7,z1,z3,z199,z5,z252]),(0,[z7,z1,z26,z5,z6,z309])],[(0,[z7,z31,z2,z26,z5,z6]),(0,[z7,z1,z3,z4,z1052,z6]),(0,[z7,z31,z658,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z70]),(0,[z7,z103,z1,z3,z4,z285]),(0,[z7,z20,z1,z3,z5,z806])],[(0,[z7,z1,z3,z1053,z5,z6]),(0,[z7,z1,z864,z3,z4,z6]),(0,[z7,z1,z3,z4,z1054,z6]),(0,[z7,z1,z3,z4,z423,z39])],[(0,[z531,z1,z24,z4,z5,z6]),(0,[z176,z7,z1,z4,z5,z238]),(0,[z7,z179,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z340,z6]),(0,[z7,z1,z47,z127,z48,z6])]],
   [[(0,[z7,z44,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z6,z1055]),(0,[z153,z3,z4,z99,z5,z6]),(0,[z7,z84,z3,z4,z159,z6])],[(0,[z7,z1,z3,z4,z5,z1056])],[(0,[z23,z1,z56,z4,z5,z6]),(0,[z7,z1,z3,z4,z1057,z6]),(0,[z7,z51,z3,z4,z477,z6]),(0,[z7,z51,z3,z4,z5,z325]),(0,[z7,z123,z3,z4,z91,z6])],[(1,[z1,z734,z4,z5,z6]),(0,[z7,z1,z3,z4,z248,z238]),(0,[z7,z1,z3,z4,z5,z1058]),(0,[z7,z1,z3,z26,z6,z74]),(0,[z7,z1,z739,z47,z5,z6]),(0,[z7,z1,z154,z3,z719,z6])],[(0,[z23,z1,z631,z4,z5,z6]),(0,[z7,z1,z3,z1059,z5,z6]),(0,[z7,z1,z3,z4,z1060,z6]),(0,[z7,z1,z1061,z4,z5,z6]),(0,[z7,z475,z1,z3,z431,z6]),(0,[z7,z1,z17,z3,z719,z6])],[(0,[z7,z493,z3,z65,z5,z6])],[(0,[z531,z7,z1,z26,z5,z6]),(0,[z7,z991,z3,z4,z5,z6]),(0,[z71,z7,z4,z99,z5,z6]),(0,[z7,z131,z4,z753,z5,z6]),(0,[z7,z301,z3,z4,z191,z6]),(0,[z7,z113,z20,z3,z5,z117])],[(0,[z7,z1,z3,z4,z5,z1062]),(0,[z7,z1,z4,z26,z98,z6]),(0,[z7,z113,z3,z4,z5,z775]),(0,[z7,z1,z4,z5,z712,z6]),(0,[z7,z1063,z3,z4,z5,z6])]],
   [[(0,[z7,z44,z1,z3,z5,z6]),(0,[z7,z1064,z3,z4,z5,z6]),(0,[z7,z20,z1,z3,z6,z74]),(0,[z7,z1065,z3,z4,z5,z6])],[(0,[z7,z1066,z1,z3,z5,z6]),(0,[z7,z1,z3,z1067,z5,z6]),(0,[z7,z31,z131,z233,z5,z6]),(0,[z7,z397,z84,z1,z3,z4]),(0,[z7,z1,z47,z93,z5,z6])],[(0,[z7,z1,z428,z3,z18,z6])],[(1,[z752,z3,z4,z5,z6]),(0,[z198,z1,z3,z4,z793,z6]),(0,[z7,z1,z3,z4,z5,z27])],[],[(0,[z7,z1,z468,z26,z5,z6]),(0,[z336,z1,z3,z4,z98,z6]),(0,[z1068,z1,z3,z4,z5,z6]),(0,[z1069,z7,z1,z4,z5,z6]),(0,[z7,z718,z3,z26,z5,z6])],[(0,[z379,z1,z3,z40,z5,z6]),(0,[z71,z7,z20,z99,z5,z6]),(0,[z7,z123,z247,z3,z4,z91]),(0,[z7,z1,z3,z4,z61,z95])],[(0,[z7,z450,z467,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z1070,z6]),(0,[z7,z1,z3,z4,z5,z797]),(0,[z7,z1,z3,z26,z159,z6]),(0,[z7,z103,z20,z1,z3,z104])],[(0,[z7,z1,z1071,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1072]),(0,[z7,z503,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z1073]),(0,[z7,z1,z295,z3,z5,z55])],[],[(0,[z7,z3,z4,z722,z91,z6]),(0,[z7,z1,z3,z4,z116,z12])],[(0,[z7,z4,z753,z99,z5,z6]),(0,[z7,z397,z1,z3,z4,z6])],[(0,[z7,z1,z3,z4,z6,z1074]),(0,[z539,z7,z20,z1,z5,z6]),(0,[z7,z1,z1075,z4,z5,z6]),(0,[z706,z7,z3,z4,z91,z6]),(0,[z7,z1,z372,z26,z5,z6]),(0,[z7,z20,z1,z3,z159,z6]),(0,[z7,z1,z92,z145,z37,z6]),(1,[z7,z1,z4,z712,z6])],[(0,[z7,z1,z3,z26,z5,z6]),(0,[z7,z1,z550,z26,z5,z6]),(0,[z7,z1,z1076,z4,z5,z6]),(0,[z7,z1,z3,z4,z1077,z6]),(0,[z7,z51,z3,z4,z5,z88]),(0,[z7,z1,z132,z26,z5,z6])],[(0,[z7,z1,z3,z4,z76,z484]),(0,[z7,z1,z3,z4,z5,z1078]),(0,[z7,z416,z3,z4,z5,z117]),(0,[z7,z1,z3,z1079,z5,z6])]],
   [[(0,[z7,z1,z3,z1080,z5,z6]),(1,[z153,z1,z26,z5,z6]),(0,[z7,z1,z3,z4,z5,z303]),(0,[z7,z1,z26,z374,z5,z6]),(0,[z7,z543,z1,z26,z5,z6]),(0,[z7,z1,z29,z4,z5,z6]),(0,[z7,z1,z26,z5,z6,z62])],[(0,[z7,z1,z1081,z4,z5,z6]),(0,[z7,z1,z3,z4,z1082,z6]),(0,[z71,z7,z4,z99,z248,z6]),(0,[z7,z247,z1,z3,z4,z37]),(0,[z7,z1,z3,z32,z5,z6]),(0,[z7,z1,z54,z3,z5,z451])],[(0,[z7,z140,z3,z4,z476,z6]),(0,[z379,z1,z3,z743,z5,z6]),(0,[z71,z7,z4,z99,z5,z252]),(0,[z7,z113,z110,z3,z4,z5]),(0,[z7,z84,z3,z4,z5,z775]),(0,[z7,z1,z989,z3,z26,z6]),(0,[z7,z1,z3,z26,z5,z165]),(0,[z176,z7,z1,z4,z5,z27]),(0,[z7,z1,z3,z5,z737,z22])],[(0,[z7,z20,z1,z3,z5,z6]),(0,[z336,z1,z3,z4,z5,z6]),(0,[z87,z1,z3,z307,z5,z6]),(0,[z7,z450,z3,z4,z477,z6]),(0,[z7,z450,z3,z4,z5,z325]),(0,[z373,z1,z3,z4,z97,z6]),(0,[z7,z1,z378,z26,z5,z6]),(0,[z7,z1,z26,z5,z46,z62]),(0,[z1083,z1,z3,z4,z5,z6])],[(0,[z7,z1,z384,z26,z5,z6]),(0,[z71,z7,z72,z99,z5,z6]),(0,[z1084,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z1085,z6]),(0,[z7,z1,z147,z26,z5,z62])],[(0,[z7,z1,z3,z1086,z5,z6]),(0,[z7,z1087,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1088]),(0,[z7,z1,z3,z1089,z5,z6]),(0,[z7,z1,z3,z4,z1090,z6]),(0,[z7,z1,z1091,z4,z5,z6]),(0,[z7,z1,z260,z5,z6,z22])],[(0,[z23,z421,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z76,z70]),(0,[z7,z1,z3,z4,z52,z6]),(0,[z681,z1,z3,z4,z5,z46]),(0,[z7,z20,z1,z3,z5,z165]),(0,[z7,z1,z3,z4,z423,z6]),(0,[z7,z1,z3,z5,z737,z6]),(0,[z7,z1,z3,z4,z5,z715])]],
   [[(0,[z7,z714,z1,z56,z5,z6]),(0,[z7,z1092,z1,z3,z5,z6]),(0,[z7,z113,z3,z4,z5,z117]),(0,[z7,z1,z3,z4,z37,z165])],[(0,[z7,z1,z26,z5,z6,z392]),(0,[z7,z1,z467,z4,z477,z6]),(0,[z7,z1,z467,z4,z5,z325]),(0,[z7,z1,z3,z4,z5,z1093]),(0,[z7,z541,z1,z26,z5,z6])],[(0,[z7,z397,z1,z3,z4,z116]),(0,[z7,z1,z3,z4,z5,z1049]),(0,[z7,z214,z1,z3,z5,z451])],[(0,[z7,z1,z3,z4,z5,z1094]),(0,[z7,z1,z3,z4,z5,z1095]),(0,[z7,z1,z1096,z3,z5,z6]),(0,[z7,z1,z47,z4,z48,z27]),(0,[z7,z1,z4,z5,z815,z6]),(0,[z7,z1097,z3,z4,z5,z6])],[(0,[z7,z1098,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z1099,z6]),(0,[z7,z20,z1,z659,z5,z6]),(0,[z7,z110,z3,z4,z5,z62])],[(0,[z7,z140,z3,z4,z5,z484]),(0,[z75,z1,z24,z119,z5,z6]),(0,[z188,z1,z24,z4,z5,z6]),(0,[z7,z20,z1,z312,z5,z6]),(0,[z7,z1,z888,z3,z26,z5]),(0,[z7,z110,z3,z4,z48,z6]),(0,[z7,z1,z82,z5,z144,z6]),(0,[z7,z1,z1100,z4,z5,z6])],[(0,[z7,z1,z3,z4,z1101,z6]),(0,[z71,z7,z1,z26,z5,z238]),(0,[z7,z1,z3,z1102,z5,z6]),(0,[z7,z1,z115,z4,z5,z62]),(0,[z346,z1,z3,z654,z5,z6])],[(0,[z96,z0,z3,z26,z5,z6]),(0,[z7,z1,z3,z4,z1103,z6]),(0,[z1104,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z1105]),(0,[z7,z1,z3,z754,z5,z6])],[(0,[z7,z1,z3,z317,z5,z6]),(0,[z7,z1,z3,z1106,z5,z6]),(0,[z7,z1,z3,z26,z248,z6]),(0,[z71,z7,z4,z753,z5,z6]),(0,[z7,z1,z26,z5,z117,z62]),(0,[z7,z1,z358,z26,z5,z62]),(0,[z7,z1,z521,z26,z5,z6]),(0,[z7,z1,z490,z26,z5,z6]),(0,[z7,z577,z103,z1,z3,z4])],[(0,[z7,z1,z3,z1107,z5,z6]),(0,[z7,z1,z3,z4,z5,z1108]),(0,[z7,z1,z3,z26,z5,z252]),(0,[z7,z1,z370,z26,z5,z6])],[(0,[z7,z1,z3,z1109,z5,z6]),(0,[z7,z1,z32,z5,z6,z62])],[(0,[z1110,z7,z1,z4,z5,z6]),(0,[z7,z1,z3,z119,z5,z6]),(0,[z7,z1,z3,z1111,z5,z6]),(0,[z7,z1,z3,z4,z6,z74])],[(0,[z7,z1,z1112,z4,z5,z6]),(0,[z7,z1,z3,z4,z477,z325]),(0,[z7,z1,z3,z743,z5,z6]),(0,[z7,z1,z1113,z3,z4,z5]),(0,[z7,z84,z110,z3,z4,z5]),(0,[z7,z650,z3,z4,z5,z187])],[(0,[z7,z1,z1114,z4,z5,z6]),(0,[z336,z1,z3,z4,z248,z6]),(0,[z7,z20,z1,z3,z248,z6]),(0,[z7,z1115,z1,z3,z5,z6]),(0,[z7,z223,z1,z109,z5,z6]),(0,[z7,z3,z4,z5,z6,z775]),(0,[z7,z1,z47,z26,z48,z6]),(0,[z7,z1,z3,z127,z5,z165])],[(0,[z7,z1,z3,z4,z5,z1116]),(0,[z7,z450,z3,z4,z5,z88]),(0,[z336,z1,z3,z4,z5,z252]),(0,[z7,z20,z1,z3,z5,z252]),(0,[z7,z123,z247,z1,z3,z4]),(0,[z7,z1,z3,z1117,z5,z6]),(0,[z7,z3,z785,z26,z5,z6]),(0,[z7,z1,z26,z5,z587,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1043).take 167) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1210)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 521, 167] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 82).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 177).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [82, 95, 79] = true :=
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

end PEqualNP.Outside.L_meta_46254

theorem PEqualNP.Outside.L_meta_46254 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277053568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277053568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46254.solve