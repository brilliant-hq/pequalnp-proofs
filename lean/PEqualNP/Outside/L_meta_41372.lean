import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41372

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4241022976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x02248615c630f0ea#64 ++ 0x000892185718c3c3#64 ++ 0x067d8e3fc631f1fd#64 ++ 0x9819f638ff18c7c7#64 : BitVec 256),
   (0x0890b2cc02d7760c#64 ++ 0x082242cb300b5dd8#64 ++ 0x1992f3cc07fffe3b#64 ++ 0xfc664bcf301ffff8#64 : BitVec 256),
   (0x61630370583a1b70#64 ++ 0x21858c0dc160e86d#64 ++ 0xe1e303f0f83e3ff7#64 ++ 0xaf878c0fc3e0f8ff#64 : BitVec 256),
   (0xb603dc00af402d80#64 ++ 0x16d80f7002bd00b6#64 ++ 0xfe03fc00ffc03fef#64 ++ 0xf7f80ff003ff00ff#64 : BitVec 256),
   (0xdffc0000f5ad8000#64 ++ 0x477ff00003d6b600#64 ++ 0xfffc0000ffffc01f#64 ++ 0xc7fff00003ffff00#64 : BitVec 256),
   (0xfddb69aa00000000#64 ++ 0x03f76da6a8000000#64 ++ 0xffffffff0000003f#64 ++ 0x7bfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x067c00000000001d 0x0019f00000000000

def z1 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d8e3fc631f1fd 0x9819f638ff18c7c7

def z2 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1992f3cc07fffe3b 0xfc664bcf301ffff8

def z3 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e303f0f83e3ff7 0xaf878c0fc3e0f8ff

def z4 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe03fc00ffc03fef 0xf7f80ff003ff00ff

def z5 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffc0000ffffc01f 0xc7fff00003ffff00

def z6 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffffffff0000003f 0x7bfffffffc000000

def z7 : W := mkw 0xffff69aaf5288000 0x47fffda6abd4a200 0xfffffffff800003f 0x7bffffffffe00000

def z8 : W := mkw 0x2003dc000a402d80 0x10800f70002900b6 0xe003fc00f8003fe7 0xb7800ff003e000ff

def z9 : W := mkw 0xfddb480000000000 0x03f76d2000000000 0xfffffc000000003f 0x73fffff000000000

def z10 : W := mkw 0x02240000f5ad8000 0x4408900003d6b600 0x00000000ffffc000 0x8400000003ffff00

def z11 : W := mkw 0xddd8000000000000 0x0377600000000000 0xfffc00000000001f 0x43fff00000000000

def z12 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x00000000c631f1c0 0x800000000318c7c7

def z13 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xf98271c000000002 0x63e609c700000000

def z14 : W := mkw 0xd76c0000f5288000 0x475db00003d4a200 0xe66c0000f8000004 0x0399b00003e00000

def z15 : W := mkw 0xdffcb2ccf7fff60c 0x4f7ff2cb33dfffd8 0xfffef3ccfffffe3f 0xfffffbcf33fffff8

def z16 : W := mkw 0x96000000a5000000 0x0658000002940000 0xfe000000ffc0000f 0xc7f8000003ff0000

def z17 : W := mkw 0xffffdc00ffedad80 0x57ffff7003ffb6b6 0xfffffc00ffffffff 0xf7fffff003ffffff

def z18 : W := mkw 0x0890208800850000 0x0022408220021400 0x1992f3cc07ffc03b 0xfc664bcf301fff00

def z19 : W := mkw 0x0a90b6cc86d7768c 0x082a42db321b5dda 0x1f93ffccc7ffffff 0xfc7e4fff331fffff

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0x067d8e3f0000003d 0x1819f638fc000000

def z21 : W := mkw 0xffffefbfc630f0ea 0x03ffffbeff18c3c3 0xffffffffc631f1ff 0xfbffffffff18c7c7

def z22 : W := mkw 0xfddbfbee02d7760c 0x0bf76fefb80b5dd8 0xffffffff07fffe3f 0xfffffffffc1ffff8

def z23 : W := mkw 0xffff69aaf5ad8000 0x47fffda6abd6b600 0xffffffffffffc03f 0xffffffffffffff00

def z24 : W := mkw 0x00200250583a1b70 0x200080094160e86d 0x00000000f83e3fc0 0x8400000003e0f8ff

def z25 : W := mkw 0x9c98688a00000000 0x027261a228000000 0x1e1cfc0f00000008 0x507873f03c000000

def z26 : W := mkw 0x9e9cdc00a7c5a480 0x567a7370029f1692 0x1e1cfc0007c1c008 0x507873f0001f0700

def z27 : W := mkw 0xf5634b70583a1b70 0x23d58d2dc160e86d 0xffe3fff0f83e3fff 0xffff8fffc3e0f8ff

def z28 : W := mkw 0xf54b492200000000 0x03d52d2488000000 0xe000000000000000 0x0380000000000000

def z29 : W := mkw 0x02240000c4208000 0x0008900003108200 0x066c0000c0000004 0x0019b00003000000

def z30 : W := mkw 0x00008615021070ea 0x00000218540841c3 0x00018e3f000031e0 0x18000638fc0000c7

def z31 : W := mkw 0xdffc8615f7bdf0ea 0x477ff21857def7c3 0xfffd8e3ffffff1ff 0xdffff638ffffffc7

def z32 : W := mkw 0xdffc2088f5ad8000 0x477ff08223d6b600 0xfffef3ccffffc03f 0xfffffbcf33ffff00

def z33 : W := mkw 0x41600370503a1270 0x2105800dc140e849 0x01e003f0003e0010 0x0807800fc000f800

def z34 : W := mkw 0x49fc000050ad8000 0x4127f0000142b600 0xe1fc0000f83fc017 0x8787f00003e0ff00

def z35 : W := mkw 0x9ebc0000f5ad8000 0x467af00003d6b600 0x1e1c0000ffffc008 0xc478700003ffff00

def z36 : W := mkw 0xd548000031080000 0x4755200000c42000 0xe000000038000000 0x0380000000e00000

def z37 : W := mkw 0x02240411c42080e2 0x0008901047108203 0x066d0c33c00001c4 0x0019b430cf000007

def z38 : W := mkw 0x089030c800c70604 0x082240c320031c18 0x198271c001ce0e02 0x646609c700073838

def z39 : W := mkw 0xdfdc0000b58d8000 0x477f700002d63600 0xff9c00003fcfc00a 0x47fe700000ff3f00

def z40 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xfffe71c00000001f 0x63fff9c700000000

def z41 : W := mkw 0xddd80000318d0000 0x4777600000c63400 0xf980000039ce0002 0x47e6000000e73800

def z42 : W := mkw 0xfffbfffaff7a3ff0 0x37ffefffebfde8ff 0xfffffffffffe3fff 0xfffffffffffff8ff

def z43 : W := mkw 0x4160000050280000 0x010580000140a000 0xe1e00000f83e0017 0x8787800003e0f800

def z44 : W := mkw 0x9e9c0000a5858000 0x467a700002961600 0x1e1c000007c1c008 0x40787000001f0700

def z45 : W := mkw 0xfddb0160398f0b10 0x67f76c0580e63c2c 0xf98201c039ce0e02 0x67e6080700e73838

def z46 : W := mkw 0x200369aa00000000 0x00800da6a8000000 0x0003ffff00000020 0x38000ffffc000000

def z47 : W := mkw 0x020484058600e08a 0x0008121016180382 0x061c8c0f0601c008 0x101872303c180700

def z48 : W := mkw 0x61430160180a0b10 0x21850c058060282c 0xe18201c0380e0e02 0x2786080700e03838

def z49 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xf8027000ffc03fc2 0xe7e009c003ff00ff

def z50 : W := mkw 0x0000924402d7760c 0x08000249100b5dd8 0x0000000007fffe00 0x84000000001ffff8

def z51 : W := mkw 0x02009400af402d80 0x1408025002bd00b6 0x00000000ffc03fc0 0x8400000003ff00ff

def z52 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xff83fdc00000002f 0x73fe0ff700000000

def z53 : W := mkw 0x0890000000850000 0x0022400000021400 0x1990000007ffc01b 0xc4664000001fff00

def z54 : W := mkw 0x0000b2cc0252760c 0x080002cb300949d8 0x0002f3cc00003e20 0x38000bcf300000f8

def z55 : W := mkw 0xddd8000000850000 0x0377600000021400 0xfffc000007ffc01f 0xc7fff000001fff00

def z56 : W := mkw 0x2003000008000900 0x00800c0000200024 0xe0030000f8003fe7 0xa7800c0003e000ff

def z57 : W := mkw 0xfddb69aa08000900 0x03f76da6a8200024 0xfffffffff8003fff 0xffffffffffe000ff

def z58 : W := mkw 0x0890b08c02c5640c 0x082242c2300b1590 0x1992f3cc07c1c03b 0x78664bcf301f0700

def z59 : W := mkw 0x0000820402107008 0x00000208100841c0 0x0010820c0631f039 0x980042083018c7c0

def z60 : W := mkw 0x0ab4b6ddc6f7f6ee 0x082ad2db771bdfdb 0x1fffffffc7ffffff 0xfc7fffffff1fffff

def z61 : W := mkw 0x61430160180a0b10 0x21850c058060282c 0xe18301c0f80e3fe7 0xa7860c0703e038ff

def z62 : W := mkw 0x0000100029400d00 0x1400004000a50034 0x0000000039c00e00 0x0400000000e70038

def z63 : W := mkw 0x0000924402d7760c 0x08000249100b5dd8 0x0010820c07fffe39 0x9c004208301ffff8

def z64 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xe6010c00ffc03fc4 0x8798043003ff00ff

def z65 : W := mkw 0x02208610c63030e0 0x000882184318c0c3 0x06618e30c63031fd 0x98198638c318c0c7

def z66 : W := mkw 0x2003037008121b70 0x20800c0dc020486d 0xe00303f0f8003fe7 0xaf800c0fc3e000ff

def z67 : W := mkw 0x0890b08802402400 0x002242c220090090 0x1992f3cc07c03e3b 0xfc664bcf301f00f8

def z68 : W := mkw 0x49d821aa00000000 0x01276086a8000000 0x01fc03ff00000010 0x0807f00ffc000000

def z69 : W := mkw 0xffdbfdaaaf402d80 0x17ff6ff6aabd00b6 0xffffffffffc03fff 0xffffffffffff00ff

def z70 : W := mkw 0x0200840086002080 0x0008021002180082 0x00000000c60031c0 0x80000000031800c7

def z71 : W := mkw 0xd76c0411f52880e2 0x475db01047d4a203 0xe66d0c33f80001c4 0x0399b430cfe00007

def z72 : W := mkw 0xbe9bfc8aaf402d80 0x16fa6ff22abd00b6 0xfe1ffc0fffc03fef 0xf7f87ff03fff00ff

def z73 : W := mkw 0x0890900002c52400 0x00224240000b1490 0x1992f00007fffe3b 0xf4664bc0001ffff8

def z74 : W := mkw 0xdffc8615c630f0ea 0x037ff2185718c3c3 0xfffd8e3fc631f1ff 0xdbfff638ff18c7c7

def z75 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067c8e3f0631c018 0x1819f238fc18c700

def z76 : W := mkw 0x02240411c42080e2 0x0008901047108203 0x00000000c00001c0 0x0000000003000007

def z77 : W := mkw 0x6163033058381970 0x21858c0cc160e065 0xe0610230f83031f5 0x8b818408c3e0c0c7

def z78 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xf9800000ffffc002 0xc7e6000003ffff00

def z79 : W := mkw 0xfddbfbee0252760c 0x0bf76fefb80949d8 0xffffffff00003e3f 0x7bfffffffc0000f8

def z80 : W := mkw 0x6143012000000000 0x01850c0480000000 0xe7ff8fff0000003f 0x3b9ffe3ffc000000

def z81 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xe7fd0fff00000014 0x0b9ff43ffc000000

def z82 : W := mkw 0x49d821aa00000000 0x01276086a8000000 0x19fef3ff0000003b 0x7867fbcffc000000

def z83 : W := mkw 0xf54b492200000000 0x03d52d2488000000 0xe66d0c3300000004 0x0399b430cc000000

def z84 : W := mkw 0x6143012000000000 0x01850c0480000000 0xe1e303f000000037 0x2b878c0fc0000000

def z85 : W := mkw 0xfdfb6bfa583a1b70 0x23f7edafe960e86d 0xfffffffff83e3fff 0xffffffffffe0f8ff

def z86 : W := mkw 0xb603de04af507d88 0x16d80f7812bd41f6 0xfe13fe0cfff1ffff 0xfff84ff833ffc7ff

def z87 : W := mkw 0xb6035800ad400d00 0x16d80d6002b50034 0xfe027000ffc00e0f 0xe7f809c003ff0038

def z88 : W := mkw 0x002486154230f0ea 0x000092185508c3c3 0x007d8e3f0031f1f0 0x1801f638fc00c7c7

def z89 : W := mkw 0xddd830c831cf0604 0x4f7760c320c73c18 0xf98271c039ce0e02 0x67e609c700e73838

def z90 : W := mkw 0x96240000f5ad8000 0x4658900003d6b600 0xfe000000ffffc00f 0xc7f8000003ffff00

def z91 : W := mkw 0x61430360181a1b10 0x21850c0d8060686c 0xe18203c0383e3e33 0xaf86080f00e0f8f8

def z92 : W := mkw 0x69f323fc58bf5b7c 0x29a7cc8ff162fd6d 0xe1f303fcf83ffff7 0xaf87cc0ff3e0ffff

def z93 : W := mkw 0x0ab48615c6b5f0ea 0x002ad218571ad7c3 0x1ffd8e3fc7fff1ff 0xdc7ff638ff1fffc7

def z94 : W := mkw 0x0000924402d7760c 0x08000249100b5dd8 0x018203c007fffe33 0xac06080f001ffff8

def z95 : W := mkw 0xfffffdaaffedad80 0x57fffff6abffb6b6 0xffffffffffffffff 0xffffffffffffffff

def z96 : W := mkw 0x63678775de3afbfa 0x218d9e1dd778ebef 0xe7ff8ffffe3fffff 0xbf9ffe3ffff8ffff

def z97 : W := mkw 0x9600dc00a7402480 0x16580370029d0092 0x1e00fc0007c00008 0x507803f0001f0000

def z98 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x198271c007fffe02 0xe46609c7001ffff8

def z99 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe18201c0f83e3fc2 0xa786080703e0f8ff

def z100 : W := mkw 0x69db21aa00000000 0x01a76c86a8000000 0xe1ff03ff00000037 0x2b87fc0ffc000000

def z101 : W := mkw 0xddfc000050ad8000 0x4377f0000142b600 0xfffc0000003fc01f 0x43fff0000000ff00

def z102 : W := mkw 0x9e9c688aa5858000 0x467a71a22a961600 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z103 : W := mkw 0x63670370fdbf9b70 0x658d9c0dc3f6fe6d 0xe1e303f0fffffff7 0xaf878c0fc3ffffff

def z104 : W := mkw 0xdffc8204f7bdf008 0x477ff20813def7c0 0xfffc820cfffff03f 0xdffff20833ffffc0

def z105 : W := mkw 0x0890b08c02c5640c 0x082242c2300b1590 0x1812f00c07c1fe2b 0xf4604bc0301f07f8

def z106 : W := mkw 0xb403580029400d00 0x16d00d6000a50034 0xf802700039c00e02 0x67e009c000e70038

def z107 : W := mkw 0xddd8208800000000 0x0377608220000000 0xfffef3cc0000003f 0x7bfffbcf30000000

def z108 : W := mkw 0xffff4922f5ad8000 0x47fffd248bd6b600 0xfffd0c33ffffc01f 0xc7fff430cfffff00

def z109 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1812f3cc07c1fe28 0x78604bcf301f07f8

def z110 : W := mkw 0xf763dc00ff682d80 0x17dd8f7003fda0b6 0xffe3fc00fffe3fff 0xf7ff8ff003fff8ff

def z111 : W := mkw 0x6163012050280000 0x01858c048140a000 0xe1e303f0f83e0037 0xaf878c0fc3e0f800

def z112 : W := mkw 0xb627de15ef70fdea 0x16d89f7857bdc3f7 0xfe7ffe3ffff1ffff 0xfff9fff8ffffc7ff

def z113 : W := mkw 0x02248655c632f2ea 0x000892195718cbcb 0x07ff8fffc63fffff 0xbc1ffe3fff18ffff

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x00018e3f00000020 0x18000638fc000000

def z115 : W := mkw 0xffdbdc00bfcd2d80 0x57ff6f7002ff34b6 0xff83fc00ffce3fef 0xf7fe0ff003ff38ff

def z116 : W := mkw 0x0000900402c5640c 0x08000240100b1590 0x0000000007c1c000 0x00000000001f0700

def z117 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xf992f3cc0000003b 0x7be64bcf30000000

def z118 : W := mkw 0xf76f4d33c42080e2 0x03ddbd34cf108203 0xe66d0c33c00001c4 0x0399b430cf000007

def z119 : W := mkw 0x089022cc0097520c 0x0822408b30025d48 0x019003cc003fc010 0x0806400f3000ff00

def z120 : W := mkw 0xb6034c00ad000980 0x16d80d3002b40026 0xfe03fc00f80001ef 0x73f80ff003e00007

def z121 : W := mkw 0xfdfb037079bf1b70 0x67f7ec0dc1e6fc6d 0xf9e303f0f9fe3ff7 0xefe78c0fc3e7f8ff

def z122 : W := mkw 0x49f0b2cc52ff760c 0x0927c2cb314bfdd8 0xf9f2f3ccfffffe3f 0xffe7cbcf33fffff8

def z123 : W := mkw 0x2003dc000a402d80 0x10800f70002900b6 0x0003fc0000003fe0 0x30000ff0000000ff

def z124 : W := mkw 0x49fc000050ad8000 0x4127f0000142b600 0x01fc0000003fc010 0x0007f0000000ff00

def z125 : W := mkw 0x6163013058280970 0x21858c04c160a025 0xe1e10030f83e01d7 0x87878400c3e0f807

def z126 : W := mkw 0x6143036000121200 0x01850c0d80004848 0xe1e303f0003e3e37 0xaf878c0fc000f8f8

def z127 : W := mkw 0x00200250583a1b70 0x200080094160e86d 0x018203c0f83e3ff3 0xac06080f03e0f8ff

def z128 : W := mkw 0xddd869aa00000000 0x037761a6a8000000 0x1ffcffff00000018 0x587ff3fffc000000

def z129 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0x1e03fc0007c03fe8 0x70780ff0001f00ff

def z130 : W := mkw 0xb403480000000000 0x02d00d2000000000 0xfe03fc000000002f 0x73f80ff000000000

def z131 : W := mkw 0xfddb79aa29400d00 0x17f76de6a8a50034 0xf98271c039c00e02 0x67e609c700e70038

def z132 : W := mkw 0x0020021040301060 0x000080084100c041 0x0060023000300010 0x08018008c000c000

def z133 : W := mkw 0x020484058600e08a 0x0008121016180382 0x000000000601c000 0x0000000000180700

def z134 : W := mkw 0x0890b08c02c5640c 0x082242c2300b1590 0x1990f00c07ffc01b 0xd46643c0301fff00

def z135 : W := mkw 0x02249400ffedad80 0x5408925003ffb6b6 0x00000000ffffffc0 0x8400000003ffffff

def z136 : W := mkw 0x2227efbfc630f0ea 0x00889fbeff18c3c3 0x067fffffc631f1fd 0xb819ffffff18c7c7

def z137 : W := mkw 0xddd821aa00000000 0x03776086a8000000 0xfffc03ff0000001f 0x4bfff00ffc000000

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x01800000003e0013 0x840600000000f800

def z139 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe0610030f83e3fc4 0x87818400c3e0f8ff

def z140 : W := mkw 0x02248400c620a080 0x0008921003188282 0x067d8c00c631f1fd 0x9019f6300318c7c7

def z141 : W := mkw 0x0020021040301060 0x000080084100c041 0x00610230c03031f5 0x88018408c300c0c7

def z142 : W := mkw 0x0890b08c02c5640c 0x082242c2300b1590 0x1810f00c07c1c008 0x506043c0301f0700

def z143 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e103f0f83e01d4 0x0b87840fc3e0f807

def z144 : W := mkw 0xbe93fc88af402d80 0x16fa4ff222bd00b6 0xff93ffccffc03fff 0xfffe4fff33ff00ff

def z145 : W := mkw 0xffdf69aaa5858000 0x47ff7da6aa961600 0xffffffff07c1c03f 0x7bfffffffc1f0700

def z146 : W := mkw 0xddd80000318d0000 0x4777600000c63400 0xf99000003fffc01b 0xc7e6400000ffff00

def z147 : W := mkw 0x02240611c43090e2 0x000890184710c243 0x066d0e33c03031f5 0x8819b438cf00c0c7

def z148 : W := mkw 0x0020001058280970 0x200080004160a025 0x00000000f80001c0 0x0000000003e00007

def z149 : W := mkw 0x9c98688a00000000 0x027261a228000000 0x1e7dfe3f0000003d 0x5879f7f8fc000000

def z150 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1fffffff07fffe3f 0xfc7ffffffc1ffff8

def z151 : W := mkw 0x0000900002402400 0x0000024000090090 0x1802f00007c03e2b 0xf4600bc0001f00f8

def z152 : W := mkw 0xbe93feccafd77f8c 0x1efa4ffb32bf5dfe 0xff93ffccffffffff 0xfffe4fff33ffffff

def z153 : W := mkw 0x0000004000020200 0x0000000100000808 0x018201c0000e0e02 0x2406080700003838

def z154 : W := mkw 0x002402154030d06a 0x000090085500c341 0x007c023f0031c010 0x0801f008fc00c700

def z155 : W := mkw 0xb603de15af507dea 0x16d80f7856bd41f7 0xfe03fe3fffc03fef 0xfff80ff8ffff00ff

def z156 : W := mkw 0x6163013058280970 0x21858c04c160a025 0xe0610030f80001c4 0x03818400c3e00007

def z157 : W := mkw 0xf543492000000000 0x03d50d2480000000 0xffe3fff00000003f 0x7bff8fffc0000000

def z158 : W := mkw 0xb627dc00ffedad80 0x56d89f7003ffb6b6 0xfe03fc00ffffffef 0xf7f80ff003ffffff

def z159 : W := mkw 0x41400160100a0210 0x2105000580402808 0x018001c0000e0000 0x0006000700003800

def z160 : W := mkw 0xdffcdc00f7eda480 0x577ff37003dfb692 0xfffcfc00ffffc01f 0xd7fff3f003ffff00

def z161 : W := mkw 0x0890208800000000 0x0022408220000000 0x1fffffff0000003f 0x787ffffffc000000

def z162 : W := mkw 0xb627dc00ef60ad80 0x16d89f7003bd82b6 0xfe7ffc00fff1ffff 0xf7f9fff003ffc7ff

def z163 : W := mkw 0xb403480000000000 0x02d00d2000000000 0xe6010c0000000004 0x0398043000000000

def z164 : W := mkw 0x0224b6ddc672f6ee 0x080892db7719cbdb 0x067fffffc631fffd 0xb819ffffff18c7ff

def z165 : W := mkw 0xffff0370fdbf9b70 0x67fffc0dc3f6fe6d 0xffff03f0ffffffff 0xeffffc0fc3ffffff

def z166 : W := mkw 0x000094000a402d80 0x10000250002900b6 0x0000000000003fc0 0x00000000000000ff

def z167 : W := mkw 0x96009400af402d80 0x1658025002bd00b6 0xfe000000ffc03fcf 0xc7f8000003ff00ff

def z168 : W := mkw 0xffffefbff7bdf0ea 0x47ffffbeffdef7c3 0xfffffffffffff1ff 0xffffffffffffffc7

def z169 : W := mkw 0xbc9378c829c70f04 0x1ef24de320a71c3c 0xf98271c039ce0e02 0x67e609c700e73838

def z170 : W := mkw 0x9e900000a5850000 0x067a400002961400 0xff900000ffffc01f 0xc7fe400003ffff00

def z171 : W := mkw 0xf76fcf37c630f0ea 0x03ddbf3cdf18c3c3 0xe67d8e3fc631f1fd 0x9b99f638ff18c7c7

def z172 : W := mkw 0xfddb69ea180a0b10 0x23f76da7a860282c 0xf98271c0380e0e02 0x67e609c700e03838

def z173 : W := mkw 0xddf8000050280000 0x0377e0000140a000 0xfffc0000f83e001f 0xc7fff00003e0f800

def z174 : W := mkw 0x0000b2cc02d7760c 0x080002cb300b5dd8 0x0002f3cc07fffe20 0xbc000bcf301ffff8

def z175 : W := mkw 0x616383745a3a7b78 0x21858e0dd168e9ed 0xe1f383fcfe3fffff 0xbf87ce0ff3f8ffff

def z176 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xff9efdcf0000000a 0x73fe7bf73c000000

def z177 : W := mkw 0x20036bfa08121b70 0x20800dafe820486d 0x0003ffff00003fe0 0x38000ffffc0000ff

def z178 : W := mkw 0x2003fdaa0a402d80 0x10800ff6a82900b6 0x0003ffff00003fe0 0x38000ffffc0000ff

def z179 : W := mkw 0xd76c8615f738f0ea 0x475db21857dce3c3 0xe67d8e3ffe31f1fd 0x9b99f638fff8c7c7

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000007c0000b 0xc4600000001f0000

def z181 : W := mkw 0xfddb69aa00850000 0x03f76da6a8021400 0xffffffff07ffc03f 0xfffffffffc1fff00

def z182 : W := mkw 0x02040000a5858000 0x4408100002961600 0x0000000007c1c000 0x00000000001f0700

def z183 : W := mkw 0xdfdc0000a5858000 0x477f700002961600 0xfffc000007c1c01f 0x43fff000001f0700

def z184 : W := mkw 0xdffc30c8f5ef8604 0x4f7ff0c323d7be18 0xfffe71c0ffffce1f 0xe7fff9c703ffff38

def z185 : W := mkw 0xfddb69aa318d0000 0x47f76da6a8c63400 0xffffffff39ce003f 0x7ffffffffce73800

def z186 : W := mkw 0xdffcb08cf7ede40c 0x4f7ff2c233dfb790 0xfffcf00cffffc01f 0xd7fff3c033ffff00

def z187 : W := mkw 0x0200860486107088 0x00080218121841c2 0x06118e0cc631f1fd 0x981846383318c7c7

def z188 : W := mkw 0x02240411c42080e2 0x0008901047108203 0x067d0c33c631c1dd 0x8019f430cf18c707

def z189 : W := mkw 0xbc9b688a00000000 0x02f26da228000000 0xfe1ffc0f0000002f 0x73f87ff03c000000

def z190 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x061c8c0fc631f1c8 0x901872303f18c7c7

def z191 : W := mkw 0x49fc21aa50ad8000 0x4127f086a942b600 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z192 : W := mkw 0x0ab40000f5ad8000 0x442ad00003d6b600 0x19900000ffffc01b 0xc466400003ffff00

def z193 : W := mkw 0x9400580021400400 0x1650016000850010 0x1800700001c00000 0x406001c000070000

def z194 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xe7fc0000f83fc014 0x039ff00003e0ff00

def z195 : W := mkw 0x00208615423070ea 0x000082185508c1c3 0x00618e3fc03031f5 0x98018638ff00c0c7

def z196 : W := mkw 0xddd8b2cc33df760c 0x4f7762cb30cf7dd8 0xf992f3cc3ffffe3b 0xffe64bcf30fffff8

def z197 : W := mkw 0x2003024008121b00 0x00800c090020486c 0xe18303c0f83e3ff7 0xaf860c0f03e0f8ff

def z198 : W := mkw 0x9624de15e770f4ea 0x16589378579dc3d3 0x1e7dfe3fc7f1f1fd 0xd879f7f8ff1fc7c7

def z199 : W := mkw 0x0024000040208000 0x0000900001008200 0x007c00000031c010 0x0001f0000000c700

def z200 : W := mkw 0x0000024000121200 0x0000000900004848 0x018203c0003e3e33 0xac06080f0000f8f8

def z201 : W := mkw 0x69f3b3fc5aff7f7c 0x29a7cecff16bfdfd 0xf9f3f3fcffffffff 0xffe7cfcff3ffffff

def z202 : W := mkw 0x200390000a402d00 0x00800e40002900b4 0xf803f000ffc03fef 0xf7e00fc003ff00ff

def z203 : W := mkw 0x2003037008121b70 0x20800c0dc020486d 0x000303f000003fe0 0x28000c0fc00000ff

def z204 : W := mkw 0xb603cc00af002980 0x16d80f3002bc00a6 0xe6018c00fe0031ed 0x9398063003f800c7

def z205 : W := mkw 0xb6035c00ad400d80 0x16d80d7002b50036 0xfe037c00f9c00fc6 0x67f80df003e7003f

def z206 : W := mkw 0x02248655de3afbfa 0x200892195778ebef 0x067d8e3ffe3ffffd 0x9c19f638fff8ffff

def z207 : W := mkw 0xf76f4922f5288000 0x47ddbd248bd4a200 0xe66d0c33f8000004 0x0399b430cfe00000

def z208 : W := mkw 0x61630160582a0b10 0x21858c058160a82c 0xe1e201c0f83e0e17 0xa787880703e0f838

def z209 : W := mkw 0x9408480200000000 0x0250212008000000 0x060c0c0300000000 0x001830300c000000

def z210 : W := mkw 0x9e90b2cca7d7760c 0x0e7a42cb329f5dd8 0xff92f3ccfffffe3f 0xfffe4bcf33fffff8

def z211 : W := mkw 0xdffc0411f5ad80e2 0x477ff01047d6b603 0xfffd0c33ffffc1df 0xc7fff430cfffff07

def z212 : W := mkw 0x69fb23fa583a1b70 0x21a7ec8fe960e86d 0xe1ff03fff83e3ff7 0xaf87fc0fffe0f8ff

def z213 : W := mkw 0x089020c800870204 0x0822408320021c08 0x018001c0000e0000 0x0006000700003800

def z214 : W := mkw 0x0200840086002080 0x0008021002180082 0x06008c0006000008 0x1018023000180000

def z215 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x0192f3cc003ffe30 0x38064bcf3000fff8

def z216 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe02fc003fc00e0a 0x77f80bf000ff0038

def z217 : W := mkw 0x0000024000121200 0x0000000900004848 0x018003c0003e0010 0x0806000f0000f800

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x1802f0000000002b 0x70600bc000000000

def z219 : W := mkw 0x0000840002002080 0x0000021000080082 0x00018c00000031e0 0x10000630000000c7

def z220 : W := mkw 0x49d821aa00000000 0x01276086a8000000 0x018001c000000000 0x0006000700000000

def z221 : W := mkw 0x4160000050280000 0x010580000140a000 0xe0600000f8000004 0x0381800003e00000

def z222 : W := mkw 0x0000037000121270 0x2000000dc0004849 0x000003f000000000 0x0800000fc0000000

def z223 : W := mkw 0x22278775ce32fbfa 0x20889e1dd738cbef 0x067f8fffc631fffd 0xb819fe3fff18c7ff

def z224 : W := mkw 0x69d3b3ec02d7760c 0x09a74ecfb00b5dd8 0xf9f3f3fc07fffe3f 0xffe7cfcff01ffff8

def z225 : W := mkw 0xfddb6bee0097520c 0x0bf76dafb8025d48 0xffffffff003fc03f 0x7bfffffffc00ff00

def z226 : W := mkw 0xd76c0000f5288000 0x475db00003d4a200 0xe67c0000fe31c01d 0x8399f00003f8c700

def z227 : W := mkw 0x000021aa00000000 0x00000086a8000000 0x000003ff00000000 0x0800000ffc000000

def z228 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe7ff8ffff83e3fff 0xbf9ffe3fffe0f8ff

def z229 : W := mkw 0xdffc9244f7fff60c 0x4f7ff24913dfffd8 0xfffc0000fffffe1f 0xc7fff00003fffff8

def z230 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x06018c00c631f1ed 0x901806300318c7c7

def z231 : W := mkw 0xb627dc11ef60ade2 0x16d89f7047bd82b7 0xfe6ffc33ffc03fef 0xf7f9bff0cfff00ff

def z232 : W := mkw 0x0020021040301060 0x000080084100c041 0x00000000c03031c0 0x800000000300c0c7

def z233 : W := mkw 0x02240615c430d0ea 0x000890185710c343 0x067d0e3fc031c1d4 0x0819f438ff00c707

def z234 : W := mkw 0x9ebcee9fc630f0ea 0x027af3ba7f18c3c3 0x1e7dfe3fc631f1fd 0xd879f7f8ff18c7c7

def z235 : W := mkw 0x200369aa00000000 0x00800da6a8000000 0x067fffff0000003d 0x3819fffffc000000

def z236 : W := mkw 0x0000924002523600 0x00000249000948d8 0x1982f3c007fe3e3b 0xfc660bcf001ff8f8

def z237 : W := mkw 0x02240210c4309060 0x000890084310c241 0x067d0230c631f1fd 0x8819f408c318c7c7

def z238 : W := mkw 0x0000020400105008 0x0000000810004140 0x0010020c0031c010 0x080040083000c700

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x066d0c3300000004 0x0019b430cc000000

def z240 : W := mkw 0x0890a2cc0297720c 0x0822428b300a5dc8 0x019083cc063ff039 0x9806420f3018ffc0

def z241 : W := mkw 0x0000025008121b70 0x200000094020486d 0x0000000000003fc0 0x00000000000000ff

def z242 : W := mkw 0x00000000318d0000 0x4400000000c63400 0x0000000039ce0000 0x0400000000e73800

def z243 : W := mkw 0x49f023fc50bf527c 0x2927c08ff142fd49 0x01f003fc003fc010 0x0807c00ff000ff00

def z244 : W := mkw 0xdfd80000a5000000 0x077f600002940000 0xfffc0000ffc0001f 0xc7fff00003ff0000

def z245 : W := mkw 0x02248405c620e08a 0x0008921017188382 0x067c8c0fc631c01d 0x9019f2303f18c700

def z246 : W := mkw 0xb603dc00a7402480 0x16d80f70029d0092 0xfe03fc0007c0002f 0x73f80ff0001f0000

def z247 : W := mkw 0xbc93688800000000 0x02f24da220000000 0xff93ffcc0000003f 0x7bfe4fff30000000

def z248 : W := mkw 0x02249615ef70fdea 0x1408925857bdc3f7 0x00000000fff1ffc0 0x8400000003ffc7ff

def z249 : W := mkw 0x9e9cec8f8600e08a 0x027a73b23e180382 0x1e1cfc0f0601c008 0x507873f03c180700

def z250 : W := mkw 0x63678775de3afbfa 0x218d9e1dd778ebef 0xe1e303f0fe3ffff7 0xaf878c0fc3f8ffff

def z251 : W := mkw 0xf763dd30ff682df0 0x37dd8f74c3fda0b7 0xfe63fc30ffc03fef 0xf7f98ff0c3ff00ff

def z252 : W := mkw 0xfdfb0370583a1b70 0x23f7ec0dc160e86d 0xffff03f0f83e3fff 0xeffffc0fc3e0f8ff

def z253 : W := mkw 0x02240000c4208000 0x0008900003108200 0x067c0000c631c01d 0x8019f0000318c700

def z254 : W := mkw 0x0000900002402400 0x0000024000090090 0x1800f00007c00008 0x506003c0001f0000

def z255 : W := mkw 0xdffcb6ddf7fff6ee 0x4f7ff2db77dfffdb 0xffffffffffffffff 0xffffffffffffffff

def z256 : W := mkw 0xdffc0210f5bd9060 0x477ff00843d6f641 0xfffd0230fffff1ff 0xcffff408c3ffffc7

def z257 : W := mkw 0x0200840086002080 0x0008021002180082 0x06018c00c60031ed 0x90180630031800c7

def z258 : W := mkw 0x0000920402507408 0x00000248100941d0 0x1812f20c07f1fe3b 0xfc604bc8301fc7f8

def z259 : W := mkw 0x9400000000000000 0x0250000000000000 0xfe0000000000000f 0x43f8000000000000

def z260 : W := mkw 0x089030c800c70604 0x082240c320031c18 0x199271c007ffce1b 0xe46649c7001fff38

def z261 : W := mkw 0xddd8000000000000 0x0377600000000000 0xf980000000000002 0x43e6000000000000

def z262 : W := mkw 0x49f823fa503a1270 0x2127e08fe940e849 0x01fc03ff003e0010 0x0807f00ffc00f800

def z263 : W := mkw 0x02249655c6f7f6ee 0x08089259571bdfdb 0x00000000c7ffffc0 0x84000000031fffff

def z264 : W := mkw 0x616387755a3a7bfa 0x21858e1dd568e9ef 0xe1e38ffff83e3ff7 0xbf878e3fffe0f8ff

def z265 : W := mkw 0xf5435960394a0f10 0x37d50d6580e5283c 0xf98271c039ce0e02 0x67e609c700e73838

def z266 : W := mkw 0x00000411000000e2 0x0000001044000003 0x00010c33000001c0 0x00000430cc000007

def z267 : W := mkw 0xbc93facc2bd77f0c 0x1ef24feb30af5dfc 0xf992f3cc3ffffe3b 0xffe64bcf30fffff8

def z268 : W := mkw 0xf56b4b72583a1b70 0x23d5ad2dc960e86d 0xe7ef0ff3f83e3ff7 0xaf9fbc3fcfe0f8ff

def z269 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe7ffe3fffc03fff 0xfff9fff8ffff00ff

def z270 : W := mkw 0xf76f0370fd3a9b70 0x67ddbc0dc3f4ea6d 0xe7ef03f0f83e3ff7 0xaf9fbc0fc3e0f8ff

def z271 : W := mkw 0x2003480000000000 0x00800d2000000000 0x0003fc0000000020 0x30000ff000000000

def z272 : W := mkw 0x49f0000050ad0000 0x0127c0000142b400 0xf9f00000ffffc01f 0xc7e7c00003ffff00

def z273 : W := mkw 0x2003fecc0a527f8c 0x18800ffb302949fe 0x0003ffcc00003fe0 0x38000fff300000ff

def z274 : W := mkw 0x0200840086002080 0x0008021002180082 0x067d8e3fc60031fd 0x9819f638ff1800c7

def z275 : W := mkw 0x0000820402107008 0x00000208100841c0 0x000000000631f000 0x800000000018c7c0

def z276 : W := mkw 0x0020821442307068 0x000082085108c1c1 0x0071823cc631f1fd 0x9801c608f318c7c7

def z277 : W := mkw 0xdffc0000f5288000 0x477ff00003d4a200 0xfffc0000f800001f 0x43fff00003e00000

def z278 : W := mkw 0xbeb7feddeff7ffee 0x1efadffb77bfdfff 0xffffffffffffffff 0xffffffffffffffff

def z279 : W := mkw 0x2003000008000900 0x00800c0000200024 0xe0010000f80001c4 0x0380040003e00007

def z280 : W := mkw 0x9600dc00a7402480 0x16580370029d0092 0x1e02fc0007c03e2b 0xf4780bf0001f00f8

def z281 : W := mkw 0x0204040184008082 0x0008101006100202 0x060c0c0300000000 0x001830300c000000

def z282 : W := mkw 0x96000000a5000000 0x0658000002940000 0xe6000000f8000004 0x0398000003e00000

def z283 : W := mkw 0x02240411c42080e2 0x0008901047108203 0x067d8e3fc00001fd 0x1819f638ff000007

def z284 : W := mkw 0xf743dd60bf4a2f90 0x37dd0f7582fd28be 0xff83fdc0ffce3fef 0xf7fe0ff703ff38ff

def z285 : W := mkw 0x002402154030d06a 0x000090085500c341 0x000000000031c000 0x000000000000c700

def z286 : W := mkw 0x49fc22cc50bfd20c 0x4927f08b3142ff48 0x01fc03cc003fc010 0x0807f00f3000ff00

def z287 : W := mkw 0xd548000000000000 0x0355200000000000 0xe66c000000000004 0x0399b00000000000

def z288 : W := mkw 0x0000b2cc0252760c 0x080002cb300949d8 0x0182f3cc003e3e33 0xbc060bcf3000f8f8

def z289 : W := mkw 0xdffc0215f5bdd06a 0x477ff00857d6f741 0xfffc023fffffc01f 0xcffff008ffffff00

def z290 : W := mkw 0xfffffeccffffff8c 0x5ffffffb33fffffe 0xffffffccffffffff 0xffffffff33ffffff

def z291 : W := mkw 0xb6034800a5000000 0x06d80d2002940000 0xfe03fc00ffc0002f 0xf7f80ff003ff0000

def z292 : W := mkw 0x0020000040200000 0x0000800001008000 0x00600000c0300015 0x800180000300c000

def z293 : W := mkw 0xffff0160fdaf8b10 0x67fffc0583f6be2c 0xfffe01c0ffffce1f 0xe7fff80703ffff38

def z294 : W := mkw 0x002092545aff7f7c 0x28008249516bfdfd 0x00000000ffffffc0 0x8400000003ffffff

def z295 : W := mkw 0x2003df700a523ff0 0x30800f7dc02948ff 0x0003fff000003fe0 0x38000fffc00000ff

def z296 : W := mkw 0x02248204c630f008 0x000892081318c3c0 0x067c820cc631f03d 0x9819f2083318c7c0

def z297 : W := mkw 0x0890208800000000 0x0022408220000000 0x1992f3cc0000003b 0x78664bcf30000000

def z298 : W := mkw 0xb607dc05af40ed8a 0x16d81f7016bd03b6 0xfe1ffc0fffc1ffef 0xf7f87ff03fff07ff

def z299 : W := mkw 0xffdb6daaad000980 0x17ff6db6aab40026 0xfffffffff80001ff 0x7bffffffffe00007

def z300 : W := mkw 0x4160000050280000 0x010580000140a000 0x01e00000003e0010 0x000780000000f800

def z301 : W := mkw 0xb603de40af523f80 0x16d80f7902bd48fe 0xff83ffc0fffe3fff 0xfffe0fff03fff8ff

def z302 : W := mkw 0x0000b08c0240640c 0x080002c230090190 0x0000f00c00000000 0x100003c030000000

def z303 : W := mkw 0x49fc037050bf9270 0x6127f00dc142fe49 0x01fc03f0003fc010 0x0807f00fc000ff00

def z304 : W := mkw 0x000022cc0012520c 0x0800008b30004948 0x000003cc00000000 0x0800000f30000000

def z305 : W := mkw 0xfddbfdaa0a402d80 0x13f76ff6a82900b6 0xffffffff00003fff 0x7bfffffffc0000ff

def z306 : W := mkw 0xdffc0240f5bf9200 0x477ff00903d6fe48 0xfffe03c0fffffe3f 0xeffff80f03fffff8

def z307 : W := mkw 0xf763df70ff7a3ff0 0x37dd8f7dc3fde8ff 0xffe3fff0fffe3fff 0xffff8fffc3fff8ff

def z308 : W := mkw 0x000030c800420604 0x080000c320010818 0x000271c000000e00 0x200009c700000038

def z309 : W := mkw 0x2203dc008e402d80 0x10880f70023900b6 0x0603fc00c6003fed 0xb0180ff0031800ff

def z310 : W := mkw 0x61630370503a1270 0x21858c0dc140e849 0xe1e303f0003e0037 0x2b878c0fc000f800

def z311 : W := mkw 0xdffc21aaf5ad8000 0x477ff086abd6b600 0xfffc03ffffffc01f 0xcffff00fffffff00

def z312 : W := mkw 0x0000021000101060 0x0000000840004041 0x00010230000031e0 0x08000408c00000c7

def z313 : W := mkw 0xffff5800fded8d00 0x57fffd6003f7b634 0xfffe7000ffffce1f 0xe7fff9c003ffff38

def z314 : W := mkw 0x9c98688a00000000 0x027261a228000000 0x1f9effcf0000003b 0x787e7bff3c000000

def z315 : W := mkw 0x49d823ee0097520c 0x0927608fb8025d48 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z316 : W := mkw 0x02248415c620e0ea 0x0008921057188383 0x067d8c3fc601c1cc 0x1019f630ff180707

def z317 : W := mkw 0xfddbf9ae02c5640c 0x0bf76fe6b80b1590 0xffffffff07c1c03f 0x7bfffffffc1f0700

def z318 : W := mkw 0x02248411c620a0e2 0x0008921047188283 0x066d8c33c60031ed 0x9019b630cf1800c7

def z319 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x0010820cc631f1f9 0x980042083318c7c7

def z320 : W := mkw 0xffff6dbbc42080e2 0x03fffdb6ef108203 0xffffffffc00001ff 0x7bffffffff000007

def z321 : W := mkw 0x000084050200608a 0x0000021014080182 0x00008c0f00000000 0x100002303c000000

def z322 : W := mkw 0x4bfc0000d4ad8000 0x412ff0000352b600 0x07fc0000c63fc01d 0x801ff0000318ff00

def z323 : W := mkw 0x0000b2cc0252760c 0x080002cb300949d8 0x1802f3cc07c03e2b 0xfc600bcf301f00f8

def z324 : W := mkw 0x020484058600e08a 0x0008121016180382 0x067d8e3f0601c03d 0x1819f638fc180700

def z325 : W := mkw 0x2893fecc0ad77f8c 0x18a24ffb302b5dfe 0x1993ffcc07fffffb 0xfc664fff301fffff

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x007c023f00000010 0x0801f008fc000000

def z327 : W := mkw 0x2003580008400d00 0x10800d6000210034 0x0002700000000e00 0x200009c000000038

def z328 : W := mkw 0xb403580029400d00 0x16d00d6000a50034 0xfe03fc0039c00e2f 0x77f80ff000e70038

def z329 : W := mkw 0xffdbffeeafd77f8c 0x1fff6fffbabf5dfe 0xffffffffffffffff 0xffffffffffffffff

def z330 : W := mkw 0x69ff037058bf9b70 0x61a7fc0dc162fe6d 0xe1ff03f0f83ffff7 0xaf87fc0fc3e0ffff

def z331 : W := mkw 0xbe93fc8cafc56d8c 0x1efa4ff232bf15b6 0xfe13fc0cffc1ffef 0xf7f84ff033ff07ff

def z332 : W := mkw 0xf54b492200000000 0x03d52d2488000000 0xe67d8e3f0000003d 0x1b99f638fc000000

def z333 : W := mkw 0x02249615c670f4ea 0x000892585719c3d3 0x1e7ffe3fc7f1ffff 0xfc79fff8ff1fc7ff

def z334 : W := mkw 0xf7634d30fd2809f0 0x37dd8d34c3f4a027 0xe6610c30f80001c4 0x03998430c3e00007

def z335 : W := mkw 0x614369aa00000000 0x01850da6a8000000 0xe1e3ffff00000037 0x3b878ffffc000000

def z336 : W := mkw 0x02240215c430d06a 0x000890085710c341 0x067c023fc631c01d 0x8819f008ff18c700

def z337 : W := mkw 0x0000900002402400 0x0000024000090090 0x0000000007c03e00 0x84000000001f00f8

def z338 : W := mkw 0x000002440097520c 0x0800000910025d48 0x00000000003fc000 0x000000000000ff00

def z339 : W := mkw 0xffff4800f5ad8000 0x47fffd2003d6b600 0xfffffc00ffffc03f 0xf7fffff003ffff00

def z340 : W := mkw 0x0a94b48d86c5e48e 0x082a52d2361b1792 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z341 : W := mkw 0x6163033040301060 0x01858c0cc100c041 0xe1e303f0c03031f7 0xab878c0fc300c0c7

def z342 : W := mkw 0x61430160180a0b10 0x21850c058060282c 0xe1e303f0380e0e37 0x2f878c0fc0e03838

def z343 : W := mkw 0x9e9c0000a5858000 0x467a700002961600 0x1f9c000007ffc01b 0xc47e7000001fff00

def z344 : W := mkw 0x002402154030d06a 0x000090085500c341 0x007d023fc031f1f5 0x8801f408ff00c7c7

def z345 : W := mkw 0x02240250fdbf9b70 0x6408900943f6fe6d 0x00000000ffffffc0 0x8400000003ffffff

def z346 : W := mkw 0xb6274c11ed2089e2 0x16d89d3047b48227 0xe66d0c33f80001c4 0x0399b430cfe00007

def z347 : W := mkw 0xb603cc0086002080 0x02d80f3002180082 0xfe03fc00c60031ef 0xf3f80ff0031800c7

def z348 : W := mkw 0x0890b0cc02c7660c 0x082242c3300b1d98 0x1992f1cc07cfce0a 0x74664bc7301f3f38

def z349 : W := mkw 0x6143012000000000 0x01850c0480000000 0xe18201c000000002 0x2386080700000000

def z350 : W := mkw 0x4160021050381060 0x010580084140e041 0xe1e10230f83e31f7 0x8f878408c3e0f8c7

def z351 : W := mkw 0x0ab4b6ddc6f7f6ee 0x082ad2db771bdfdb 0x1992f3ccc7fffffb 0xfc664bcf331fffff

def z352 : W := mkw 0x41600370503a1270 0x2105800dc140e849 0x01e103f0c03e31f5 0x8807840fc300f8c7

def z353 : W := mkw 0xb403d80002402400 0x02d00f6000090090 0xfe03fc0007c03e2f 0xf7f80ff0001f00f8

def z354 : W := mkw 0x49f0b3fc52ff767c 0x2927c2cff14bfdd9 0x19f2f3fc07fffe3b 0xfc67cbcff01ffff8

def z355 : W := mkw 0xffffffffc6f7f6ee 0x0bffffffff1bdfdb 0xffffffffc7ffffff 0xffffffffff1fffff

def z356 : W := mkw 0xffdfedaf8600e08a 0x03ff7fb6be180382 0xffffffff0601c03f 0x7bfffffffc180700

def z357 : W := mkw 0x4140000010080000 0x0105000000402000 0xe1800000380e0002 0x0786000000e03800

def z358 : W := mkw 0xdffc8400f7ada080 0x477ff21003deb682 0xfffd8c00fffff1ff 0xd7fff63003ffffc7

def z359 : W := mkw 0x96008400a7002080 0x06580210029c0082 0xfe018c00ffc031ef 0xd7f8063003ff00c7

def z360 : W := mkw 0xd7600000f5280000 0x075d800003d4a000 0xffe00000fffe001f 0xc7ff800003fff800

def z361 : W := mkw 0x0000924402d7760c 0x08000249100b5dd8 0x1802f00007fffe2b 0xf4600bc0001ffff8

def z362 : W := mkw 0x2003b3fc0a527f7c 0x28800ecff02949fd 0x0003f3fc00003fe0 0x38000fcff00000ff

def z363 : W := mkw 0x6163013058280970 0x21858c04c160a025 0xe0630030f8003fe7 0xa7818c00c3e000ff

def z364 : W := mkw 0x289369aa00000000 0x00a24da6a8000000 0x1993ffff0000003b 0x78664ffffc000000

def z365 : W := mkw 0xffff6bfafdbf9b70 0x67fffdafebf6fe6d 0xffffffffffffffff 0xffffffffffffffff

def z366 : W := mkw 0x43640000f5ad8000 0x450d900003d6b600 0xe1e00000ffffc017 0x8787800003ffff00

def z367 : W := mkw 0x02008615861070ea 0x00080218561841c3 0x06018e3fc60031ed 0x98180638ff1800c7

def z368 : W := mkw 0x089032cc00d7560c 0x082240cb30035d58 0x199273cc01ffce12 0x6c6649cf3007ff38

def z369 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffd8e3fffffc03f 0xdffff638ffffff00

def z370 : W := mkw 0xf54b492200000000 0x03d52d2488000000 0xe7ef0ff300000037 0x2b9fbc3fcc000000

def z371 : W := mkw 0xbe93dc00afc52d80 0x16fa4f7002bf14b6 0xff93fc00ffffffff 0xf7fe4ff003ffffff

def z372 : W := mkw 0x6163013058280970 0x21858c04c160a025 0xe1e303f0f80001f7 0x2b878c0fc3e00007

def z373 : W := mkw 0xbc9b69aa00000000 0x02f26da6a8000000 0x1e1fffff00000028 0x78787ffffc000000

def z374 : W := mkw 0xf767df75ff7afffa 0x37dd9f7dd7fdebff 0xffffffffffffffff 0xffffffffffffffff

def z375 : W := mkw 0x0204000084008000 0x0008100002100200 0x061c00000601c008 0x0018700000180700

def z376 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0x1ffc000007ffc018 0x407ff000001fff00

def z377 : W := mkw 0xfddb79ea00c70604 0x0bf76de7a8031c18 0xffffffff01ce0e3f 0x7ffffffffc073838

def z378 : W := mkw 0xfddbefbf021070ea 0x03f76fbefc0841c3 0xffffffff000031ff 0x7bfffffffc0000c7

def z379 : W := mkw 0x0000820402107008 0x00000208100841c0 0x0000820c00003020 0x18000208300000c0

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x0061023000000035 0x08018408c0000000

def z381 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe06303f0f8003fe4 0x2b818c0fc3e000ff

def z382 : W := mkw 0x02248615f7bdf0ea 0x4408921857def7c3 0x067d8e3ffffff1fd 0x9c19f638ffffffc7

def z383 : W := mkw 0x0024001140208062 0x0000900045008201 0x006c003300000000 0x0001b000cc000000

def z384 : W := mkw 0xddfc000071ad8000 0x4777f00001c6b600 0xf9fc000039ffc012 0x47e7f00000e7ff00

def z385 : W := mkw 0x02000400ad000980 0x1408001002b40026 0x00000000f80001c0 0x0000000003e00007

def z386 : W := mkw 0x0000900002402400 0x0000024000090090 0x0002f00000003e20 0x30000bc0000000f8

def z387 : W := mkw 0x0890000000850000 0x0022400000021400 0x1980000001ce0002 0x4466000000073800

def z388 : W := mkw 0x0890b0c802c72604 0x082242c3200b1c98 0x1982f1c007ce3e2b 0xf4660bc7001f38f8

def z389 : W := mkw 0x0000024000121200 0x0000000900004848 0x000203c000003e20 0x2800080f000000f8

def z390 : W := mkw 0xb6034c00ad000980 0x16d80d3002b40026 0xe6030c00f8003fe7 0xa7980c3003e000ff

def z391 : W := mkw 0x9e9cb2cca7d7f60c 0x4e7a72cb329f5fd8 0x1f9ef3cc07fffe3b 0xfc7e7bcf301ffff8

def z392 : W := mkw 0x6143012008000900 0x01850c0480200024 0xe1e303f0f8003ff7 0xaf878c0fc3e000ff

def z393 : W := mkw 0x9e90fc8ca7c5648c 0x1e7a43f2329f1592 0x1e10fc0c07c1c008 0x507843f0301f0700

def z394 : W := mkw 0x2003000008000900 0x00800c0000200024 0x0003000000003fe0 0x20000c00000000ff

def z395 : W := mkw 0x0000824402127208 0x00000209100849c8 0x019283cc063ffe3b 0xbc064a0f3018fff8

def z396 : W := mkw 0x00200250503a1270 0x200080094140e849 0x00000000003e0000 0x000000000000f800

def z397 : W := mkw 0xb403dc000a402d80 0x12d00f70002900b6 0xfe03fc0000003fef 0x73f80ff0000000ff

def z398 : W := mkw 0x089032c800d71604 0x082240cb20035c58 0x198273c001fe3e33 0xec6609cf0007f8f8

def z399 : W := mkw 0x02009400af402d80 0x1408025002bd00b6 0x1802f000ffc03feb 0xf4600bc003ff00ff

def z400 : W := mkw 0x0898208a00000000 0x0022608228000000 0x001c000f00000000 0x000070003c000000

def z401 : W := mkw 0xb627de15ef70fdea 0x16d89f7857bdc3f7 0xfe03fc00fff1ffef 0xf7f80ff003ffc7ff

def z402 : W := mkw 0x9e9cb08ca7c5e40c 0x4e7a72c2329f1790 0x1e1cf00c07c1c008 0x507873c0301f0700

def z403 : W := mkw 0xfddb492200000000 0x03f76d2488000000 0xfffd0c330000001f 0x43fff430cc000000

def z404 : W := mkw 0x02009400a7402480 0x14080250029d0092 0x0000000007c00000 0x00000000001f0000

def z405 : W := mkw 0x49fcb2cc52fff60c 0x4927f2cb314bffd8 0x19fef3cc07fffe3b 0xfc67fbcf301ffff8

def z406 : W := mkw 0x69d3b3ec1adf7f1c 0x29a74ecfb06b7dfc 0xf992f3cc3ffffe3b 0xffe64bcf30fffff8

def z407 : W := mkw 0xfddb580039cd0d00 0x57f76d6000e73434 0xf982700039ce0e02 0x67e609c000e73838

def z408 : W := mkw 0xffff0000fdad8900 0x47fffc0003f6b624 0xffff0000ffffffff 0xe7fffc0003ffffff

def z409 : W := mkw 0x4bfc8615d6bdf0ea 0x412ff218575af7c3 0x07fd8e3fc63ff1fd 0x981ff638ff18ffc7

def z410 : W := mkw 0x0000800402006008 0x0000020010080180 0x0010800c0601c008 0x1000420030180700

def z411 : W := mkw 0x0000b6dd025276ee 0x080002db740949db 0x0003ffff00003fe0 0x38000ffffc0000ff

def z412 : W := mkw 0x9604dc05a740e48a 0x16581370169d0392 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z413 : W := mkw 0x0890820402957008 0x00224208100a55c0 0x1990820c07fff03b 0xdc664208301fffc0

def z414 : W := mkw 0x2003de150a507dea 0x10800f78542941f7 0x0003fe3f00003fe0 0x38000ff8fc0000ff

def z415 : W := mkw 0xddd8b2cc02d7760c 0x0b7762cb300b5dd8 0xfffef3cc07fffe3f 0xfffffbcf301ffff8

def z416 : W := mkw 0x9c98000021850000 0x4672600000861400 0x1800000001c00000 0x4060000000070000

def z417 : W := mkw 0x22278615ce30f9ea 0x00889e185738c3e7 0xe67f8e3ffe31ffff 0xbf99fe38fff8c7ff

def z418 : W := mkw 0x2893b3fc0ad77f7c 0x28a24ecff02b5dfd 0x1993f3fc07fffffb 0xfc664fcff01fffff

def z419 : W := mkw 0x000002150010506a 0x0000000854004141 0x0000023f00000000 0x08000008fc000000

def z420 : W := mkw 0xdffc0000c4208000 0x037ff00003108200 0xfffc0000c631c01f 0xc3fff0000318c700

def z421 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xe603fc00f8003fe4 0x33980ff003e000ff

def z422 : W := mkw 0x9c98000000000000 0x0272600000000000 0x1e1c000000000008 0x4078700000000000

def z423 : W := mkw 0x4bfca7bfc630f0ea 0x012ff29eff18c3c3 0x07fd8fffc631f1fd 0x981ff63fff18c7c7

def z424 : W := mkw 0x49fc021550bdd06a 0x4127f0085542f741 0x01fc023f003fc010 0x0807f008fc00ff00

def z425 : W := mkw 0x020484058600e08a 0x0008121016180382 0x061d8c0fc601f1ed 0x901876303f1807c7

def z426 : W := mkw 0x4140000000000000 0x0105000000000000 0xe1e0000000000017 0x0387800000000000

def z427 : W := mkw 0x0020021040301060 0x000080084100c041 0x067d8e3fc03031fd 0x9819f638ff00c0c7

def z428 : W := mkw 0x41600240503a1200 0x010580090140e848 0xe1e203c0f83e3e37 0xaf87880f03e0f8f8

def z429 : W := mkw 0x0890308800c50404 0x082240c220031410 0x1800700001c00000 0x406001c000070000

def z430 : W := mkw 0xfdff6bbf4030d06a 0x03f7fdaefd00c341 0xffffffff0031c03f 0x7bfffffffc00c700

def z431 : W := mkw 0xfddb6bea00121200 0x03f76dafa8004848 0xffffffff003e3e3f 0xfffffffffc00f8f8

def z432 : W := mkw 0x49d8b3ee02d7760c 0x092762cfb80b5dd8 0x19fef3ff07fffe3b 0xfc67fbcffc1ffff8

def z433 : W := mkw 0xf7630370fd3a1b70 0x27dd8c0dc3f4e86d 0xffe303f0fffe3fff 0xefff8c0fc3fff8ff

def z434 : W := mkw 0x49fc23bf4030d06a 0x0127f08efd00c341 0x01fc03ff0031c010 0x0807f00ffc00c700

def z435 : W := mkw 0xb403480008000900 0x02d00d2000200024 0xfe03fc00f8003fef 0xf7f80ff003e000ff

def z436 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067c0000c631f1dd 0x8019f0000318c7c7

def z437 : W := mkw 0x089c000000858000 0x4022700000021600 0x001c00000001c000 0x0000700000000700

def z438 : W := mkw 0x41600250583a1b70 0x210580094160e86d 0xe1e00000f83e3fd7 0x8787800003e0f8ff

def z439 : W := mkw 0xb627ce15ef30f9ea 0x16d89f3857bcc3e7 0xe67d8e3ffe31f1fd 0x9b99f638fff8c7c7

def z440 : W := mkw 0x6163df705a7a3ff0 0x31858f7dc169e8ff 0xe1e3fff0f83e3ff7 0xbf878fffc3e0f8ff

def z441 : W := mkw 0x63638770de3a3bf0 0x218d8e1dc378e8ef 0xe7e38ff0fe3e3fff 0xbf9f8e3fc3f8f8ff

def z442 : W := mkw 0xdffc8615f7bdf0ea 0x477ff21857def7c3 0xfffc0000fffff1df 0xc7fff00003ffffc7

def z443 : W := mkw 0x4160013050280070 0x21058004c140a001 0x0060003000000000 0x00018000c0000000

def z444 : W := mkw 0x2003fbee0252760c 0x08800fefb80949d8 0x0003ffff00003e20 0x38000ffffc0000f8

def z445 : W := mkw 0x2003000000000000 0x00800c0000000000 0xe003000000000027 0x23800c0000000000

def z446 : W := mkw 0xf54b69aa00000000 0x03d52da6a8000000 0xe66fffff00000024 0x3b99bffffc000000

def z447 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0x01e303f0003e3ff0 0x28078c0fc000f8ff

def z448 : W := mkw 0xd76c0000f5288000 0x475db00003d4a200 0xe7ec0000f83e0017 0x879fb00003e0f800

def z449 : W := mkw 0xf56b493258280970 0x23d5ad24c960a025 0xe66d0c33f80001c4 0x0399b430cfe00007

def z450 : W := mkw 0x0890b28c02d5740c 0x082242ca300b55d0 0x1810f20c07f1f039 0xd86043c8301fc7c0

def z451 : W := mkw 0xddd8000000000000 0x0377600000000000 0xfffd8e3f0000003f 0x5bfff638fc000000

def z452 : W := mkw 0xb403480000000000 0x02d00d2000000000 0xf802700000000002 0x63e009c000000000

def z453 : W := mkw 0x9ebc0000e5a58000 0x467af00003969600 0x1e7c0000c7f1c01d 0xc079f000031fc700

def z454 : W := mkw 0x0200000084000000 0x0008000002100000 0x06000000c600000d 0x8018000003180000

def z455 : W := mkw 0x020486158610f0ea 0x00081218561843c3 0x061d8e3f0601f1e8 0x18187638fc1807c7

def z456 : W := mkw 0x0000820402107008 0x00000208100841c0 0x067d8e3f0631f03d 0x9819f638fc18c7c0

def z457 : W := mkw 0x4140012000000000 0x0105000480000000 0x01e003f000000010 0x0807800fc0000000

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x00010000c00031e5 0x80000400030000c7

def z459 : W := mkw 0xffdbedaa86002080 0x03ff6fb6aa180082 0xffffffffc60031ff 0xfbffffffff1800c7

def z460 : W := mkw 0x08b4b2dd42f7f66e 0x0822d2cb750bdfd9 0x19fef3ff07fffe3b 0xfc67fbcffc1ffff8

def z461 : W := mkw 0x61670375583adb7a 0x21859c0dd560eb6d 0xe1ff03fff83ffff7 0xaf87fc0fffe0ffff

def z462 : W := mkw 0xb603feccaf527f8c 0x1ed80ffb32bd49fe 0xfe03ffccffc03fef 0xfff80fff33ff00ff

def z463 : W := mkw 0x0020000050280000 0x000080000140a000 0x00000000f83e0000 0x8400000003e0f800

def z464 : W := mkw 0xffffdf70ffffbff0 0x77ffff7dc3fffeff 0xfffffff0ffffffff 0xffffffffc3ffffff

def z465 : W := mkw 0x69f333f858ff1f74 0x29a7cccfe163fc7d 0xf9e373f0f9fe3ff7 0xefe78dcfc3e7f8ff

def z466 : W := mkw 0xdffc0370f5bf9270 0x677ff00dc3d6fe49 0xfffc03f0ffffc01f 0xcffff00fc3ffff00

def z467 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xfe7dfc3f0000000c 0x53f9f7f0fc000000

def z468 : W := mkw 0xb6030000ad000900 0x06d80c0002b40024 0xfe030000ffc03fef 0xe7f80c0003ff00ff

def z469 : W := mkw 0x41600370583a1b70 0x2105800dc160e86d 0x01e003f0f83e3fd0 0x8c07800fc3e0f8ff

def z470 : W := mkw 0xb403580029400d00 0x16d00d6000a50034 0xf8037000f9c03fe7 0xe7e00dc003e700ff

def z471 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1982f3cc01ce3e22 0x7c660bcf300738f8

def z472 : W := mkw 0x416c000050288000 0x4105b0000140a200 0x006c000000000000 0x0001b00000000000

def z473 : W := mkw 0x2003012000000000 0x00800c0480000000 0x000303f000000020 0x28000c0fc0000000

def z474 : W := mkw 0x61636bfa583a1b70 0x21858dafe960e86d 0xe1e3fffff83e3ff7 0xbf878fffffe0f8ff

def z475 : W := mkw 0x200369aa00000000 0x00800da6a8000000 0x000271c000000000 0x200009c700000000

def z476 : W := mkw 0x00008615021070ea 0x00000218540841c3 0x00118e3f0631f1f9 0x98004638fc18c7c7

def z477 : W := mkw 0xb603de44afd77f8c 0x1ed80f7912bf5dfe 0xfe03fc00ffffffef 0xf7f80ff003ffffff

def z478 : W := mkw 0x63639770ff7a3ff0 0x358d8e5dc3fde8ff 0xe1e303f0fffe3ff7 0xaf878c0fc3fff8ff

def z479 : W := mkw 0x69d331e818cf0f14 0x29a74cc7a0633c3c 0xf98271c039ce0e02 0x67e609c700e73838

def z480 : W := mkw 0x0ab4a69dc630f0ea 0x002ad29a7718c3c3 0x1fffffffc631f1ff 0xf87fffffff18c7c7

def z481 : W := mkw 0x089022c800121200 0x0022408b20004848 0x1992f3cc003e3e3b 0xfc664bcf3000f8f8

def z482 : W := mkw 0x2893fbee02d7760c 0x08a24fefb80b5dd8 0x1993ffff07fffe3b 0xfc664ffffc1ffff8

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002000000003e23 0xa4000800000000f8

def z484 : W := mkw 0xb403480029000900 0x16d00d2000a40024 0xe000000038000000 0x0380000000e00000

def z485 : W := mkw 0x2003013008000970 0x20800c04c0200025 0x00010030000001c0 0x00000400c0000007

def z486 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x00018e3fc631f1e0 0x98000638ff18c7c7

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000000f8000007 0x8780000003e00000

def z488 : W := mkw 0x20230370583a1b70 0x20808c0dc160e86d 0x000303f0f83e3fe0 0xac000c0fc3e0f8ff

def z489 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffef7df300000006 0x63ffbdf7cc000000

def z490 : W := mkw 0x61430370181a1b70 0x21850c0dc060686d 0xe18303f0380e3fe2 0x2f860c0fc0e038ff

def z491 : W := mkw 0x020486058610f08a 0x00081218161843c2 0x061c8e0f0631f039 0x981872383c18c7c0

def z492 : W := mkw 0x08b0b2dc5aff7f7c 0x2822c2cb716bfdfd 0x1992f3ccfffffffb 0xfc664bcf33ffffff

def z493 : W := mkw 0xdffc0250fdbf9b70 0x677ff00943f6fe6d 0xfffc0000ffffffdf 0xc7fff00003ffffff

def z494 : W := mkw 0x00008615021070ea 0x00000218540841c3 0x00000000000031c0 0x00000000000000c7

def z495 : W := mkw 0xffff4c00fdad8980 0x57fffd3003f6b626 0xfffd0c00ffffc1df 0xc7fff43003ffff07

def z496 : W := mkw 0x0000000008000900 0x0000000000200024 0x00000000f8003fc0 0x8400000003e000ff

def z497 : W := mkw 0x02009644afd77f8c 0x1c08025912bf5dfe 0x00000000ffffffc0 0x8400000003ffffff

def z498 : W := mkw 0xfddb69aa318d0000 0x47f76da6a8c63400 0xf98271c039ce0002 0x67e609c700e73800

def z499 : W := mkw 0x4148012200000000 0x0105200488000000 0x006c003300000000 0x0001b000cc000000

def z500 : W := mkw 0xf74bdd22af402d80 0x17dd2f748abd00b6 0xfe6ffc33ffc03fef 0xf7f9bff0cfff00ff

def z501 : W := mkw 0xffff69aac4208000 0x03fffda6ab108200 0xffffffffc631c03f 0xfbffffffff18c700

def z502 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfe7c0000ffc1c00c 0x43f9f00003ff0700

def z503 : W := mkw 0x0000dc0002402480 0x1000037000090092 0x0000fc0000000000 0x100003f000000000

def z504 : W := mkw 0x2003dc000a402d80 0x10800f70002900b6 0x1803fc0007c03feb 0xf4600ff0001f00ff

def z505 : W := mkw 0x0890024000971200 0x0022400900025c48 0x199203c007fffe3b 0xec66480f001ffff8

def z506 : W := mkw 0x0890b6dd02d776ee 0x082242db740b5ddb 0x1993ffff07fffffb 0xfc664ffffc1fffff

def z507 : W := mkw 0x0ab4b69dc6f5f4ee 0x082ad2da771bd7d3 0x1e7dfe3fc7f1f1fd 0xd879f7f8ff1fc7c7

def z508 : W := mkw 0x0ab4a6ddc6b7f2ee 0x082ad29b771adfcb 0x07fd8fffc63ff1fd 0x981ff63fff18ffc7

def z509 : W := mkw 0x08b0b2dc42f7766c 0x0822c2cb710bddd9 0x19f3f3fcc7ffffff 0xfc67cfcff31fffff

def z510 : W := mkw 0xffffffbfef70fdea 0x17fffffeffbdc3f7 0xfffffffffff1ffff 0xffffffffffffc7ff

def z511 : W := mkw 0xfdfbfbfe5aff7f7c 0x2bf7efeff96bfdfd 0xffffffffffffffff 0xffffffffffffffff

def z512 : W := mkw 0xdffc688af5ad8000 0x477ff1a22bd6b600 0xfffcfc0fffffc01f 0xd7fff3f03fffff00

def z513 : W := mkw 0xb40369aa00000000 0x02d00da6a8000000 0xfe03ffff0000002f 0x7bf80ffffc000000

def z514 : W := mkw 0xbe93fcc8afc72f84 0x1efa4ff322bf1cbe 0xff83fdc0ffce3fef 0xf7fe0ff703ff38ff

def z515 : W := mkw 0xfdfb6bba40301060 0x03f7edaee900c041 0xffffffffc03031ff 0xfbffffffff00c0c7

def z516 : W := mkw 0x00200250583a1b70 0x200080094160e86d 0x00610230f83e3ff5 0x8c018408c3e0f8ff

def z517 : W := mkw 0xb6034c00ad000980 0x16d80d3002b40026 0xfe010c00ffc001cf 0xc7f8043003ff0007

def z518 : W := mkw 0xbc93facc02d7760c 0x0af24feb300b5dd8 0xff93ffcc07fffe3f 0xfffe4fff301ffff8

def z519 : W := mkw 0xddf8000071ad0000 0x4777e00001c6b400 0xf9e00000f9fe0017 0xc7e7800003e7f800

def z520 : W := mkw 0x49fc000050ad8000 0x4127f0000142b600 0x19fc000007ffc01b 0xc467f000001fff00

def z521 : W := mkw 0x41600370503a1270 0x2105800dc140e849 0xe1e003f0f83e0017 0x8f87800fc3e0f800

def z522 : W := mkw 0x2203dc00af402d80 0x14880f7002bd00b6 0x0003fc00ffc03fe0 0xb4000ff003ff00ff

def z523 : W := mkw 0x616393705a7a3f70 0x21858e4dc169e8fd 0xf9e3f3f0fffe3fff 0xffe78fcfc3fff8ff

def z524 : W := mkw 0x0a94b6cd86d7f68e 0x082a52db361b5fda 0x1f9effcf07fffe3b 0xfc7e7bff3c1ffff8

def z525 : W := mkw 0xfddb79aa29400d00 0x17f76de6a8a50034 0xffffffff39c00e3f 0x7ffffffffce70038

def z526 : W := mkw 0xfddbfbee02d7760c 0x0bf76fefb80b5dd8 0xf992f3cc07fffe3b 0xffe64bcf301ffff8

def z527 : W := mkw 0x08b422dd40b7d26e 0x0822d08b7502df49 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z528 : W := mkw 0x02249655c6f7f6ee 0x08089259571bdfdb 0x067d8e3fc7fffffd 0x9c19f638ff1fffff

def z529 : W := mkw 0x69db69aa00000000 0x01a76da6a8000000 0x01ffffff00000030 0x3807fffffc000000

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x061c8c0f00000008 0x101872303c000000

def z531 : W := mkw 0x4bfc0000f5ad8000 0x452ff00003d6b600 0x01fc0000ffffc010 0x8407f00003ffff00

def z532 : W := mkw 0x0000020000101000 0x0000000800004040 0x0000020000303031 0x880000080000c0c0

def z533 : W := mkw 0xfff3fffcffff7ffc 0x3fffcffff3fffdff 0xfff3fffcffffffff 0xffffcffff3ffffff

def z534 : W := mkw 0xf54b492200000000 0x03d52d2488000000 0xfe6ffc330000002f 0x73f9bff0cc000000

def z535 : W := mkw 0x43648775d63af2fa 0x210d921dd758ebcb 0x07fd8fffc63ff1fd 0x981ff63fff18ffc7

def z536 : W := mkw 0xfddb6bfa08121b70 0x23f76dafe820486d 0xffffffff00003fff 0x7bfffffffc0000ff

def z537 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xf9fe73ff00000012 0x6be7f9cffc000000

def z538 : W := mkw 0x0890000000850000 0x0022400000021400 0x1810000007c1c008 0x40604000001f0700

def z539 : W := mkw 0x02209650ff7a3ff0 0x3408825943fde8ff 0x00000000fffe3fc0 0x8400000003fff8ff

def z540 : W := mkw 0xfdfb69aa50280000 0x03f7eda6a940a000 0xfffffffff83e003f 0xffffffffffe0f800

def z541 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xf983ffff00000022 0x7be60ffffc000000

def z542 : W := mkw 0x9e90fecca7d7768c 0x1e7a43fb329f5dda 0x1f92ffcc07fffe3b 0xfc7e4bff301ffff8

def z543 : W := mkw 0x2023037048321b70 0x20808c0dc120c86d 0x006303f0c0303ff5 0xa8018c0fc300c0ff

def z544 : W := mkw 0xfddbebae02107008 0x03f76faeb80841c0 0xffffffff0631f03f 0xfbfffffffc18c7c0

def z545 : W := mkw 0x41640375503ad27a 0x2105900dd540eb49 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z546 : W := mkw 0xffffefffde3afbfa 0x23ffffbfff78ebef 0xfffffffffe3fffff 0xfffffffffff8ffff

def z547 : W := mkw 0x2003efbf021070ea 0x00800fbefc0841c3 0x0003ffff000031e0 0x38000ffffc0000c7

def z548 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe01fc00ffc001cc 0x53f807f003ff0007

def z549 : W := mkw 0xffffb3fcffffff7c 0x6ffffecff3fffffd 0xfffff3fcffffffff 0xffffffcff3ffffff

def z550 : W := mkw 0x6143037008121b70 0x21850c0dc020486d 0xe1e303f000003ff7 0x2b878c0fc00000ff

def z551 : W := mkw 0x2003016008020b10 0x20800c058020082c 0x000201c000000e00 0x2000080700000038

def z552 : W := mkw 0xb403480000000000 0x02d00d2000000000 0xfe7ffe3f0000003f 0x7bf9fff8fc000000

def z553 : W := mkw 0x02249615ef70fdea 0x1408925857bdc3f7 0x067d8e3ffff1fffd 0x9c19f638ffffc7ff

def z554 : W := mkw 0x0020025040321260 0x000080094100c849 0x01e303f0c03e3ff7 0xac078c0fc300f8ff

def z555 : W := mkw 0x02249244f7fff60c 0x4c08924913dfffd8 0x00000000fffffe00 0x8400000003fffff8

def z556 : W := mkw 0xffff0120f5ad8000 0x47fffc0483d6b600 0xffff03f0ffffc03f 0xeffffc0fc3ffff00

def z557 : W := mkw 0x089022cc0097520c 0x0822408b30025d48 0x199003cc07ffc01b 0xcc66400f301fff00

def z558 : W := mkw 0xdffc8405f7ade08a 0x477ff21017deb782 0xfffc8c0fffffc01f 0xd7fff2303fffff00

def z559 : W := mkw 0xfddb69ea180a0b10 0x23f76da7a860282c 0xffffffff380e0e3f 0x7ffffffffce03838

def z560 : W := mkw 0xb6034c00ad000980 0x16d80d3002b40026 0xe6010c00f80001c4 0x0398043003e00007

def z561 : W := mkw 0x2003492200000000 0x00800d2488000000 0x00010c3300000000 0x00000430cc000000

def z562 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000000631c019 0x800040000018c700

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x06018c000000002d 0x1018063000000000

def z564 : W := mkw 0x0000104000c70604 0x0800004100031c18 0x0000000001ce0e00 0x0400000000073838

def z565 : W := mkw 0x69d321a800000000 0x01a74c86a0000000 0xf9f3f3fc0000003f 0x7be7cfcff0000000

def z566 : W := mkw 0xffdbfdaaa7402480 0x17ff6ff6aa9d0092 0xffffffff07c0003f 0x7bfffffffc1f0000

def z567 : W := mkw 0xf5635b70797a1f70 0x37d58d6dc1e5e87d 0xf9e373f0f9fe3ff7 0xefe78dcfc3e7f8ff

def z568 : W := mkw 0x02240000c4208000 0x0008900003108200 0x00000000c631c000 0x800000000318c700

def z569 : W := mkw 0x002482154230f06a 0x000092085508c3c1 0x007c823f0631f039 0x9801f208fc18c7c0

def z570 : W := mkw 0xb603df70af523ff0 0x36d80f7dc2bd48ff 0xfe03fff0ffc03fef 0xfff80fffc3ff00ff

def z571 : W := mkw 0x0890000000000000 0x0022400000000000 0x199000000000001b 0x4066400000000000

def z572 : W := mkw 0x0890924402d7760c 0x08224249100b5dd8 0x1990000007fffe1b 0xc4664000001ffff8

def z573 : W := mkw 0x61630170582a0b70 0x21858c05c160a82d 0xe1e301f0f80e0fc6 0x27878c07c3e0383f

def z574 : W := mkw 0xdffc9000f7eda400 0x477ff24003dfb690 0xfffef000fffffe3f 0xf7fffbc003fffff8

def z575 : W := mkw 0x9e9c0000a5858000 0x467a700002961600 0xfe1c0000ffc1c00f 0xc7f8700003ff0700

def z576 : W := mkw 0x9600dc00af402d80 0x1658037002bd00b6 0x1e00fc00ffc03fc8 0xd47803f003ff00ff

def z577 : W := mkw 0x20034c0008000980 0x10800d3000200026 0x00010c00000001c0 0x0000043000000007

def z578 : W := mkw 0x9ebc8615e7b5f0ea 0x467af218579ed7c3 0x1e7d8e3fc7f1f1fd 0xd879f638ff1fc7c7

def z579 : W := mkw 0xb623de50ff7a3ff0 0x36d88f7943fde8ff 0xfe03fc00fffe3fef 0xf7f80ff003fff8ff

def z580 : W := mkw 0xf74b4d22ad000980 0x17dd2d348ab40026 0xe66d0c33f80001c4 0x0399b430cfe00007

def z581 : W := mkw 0x49d8000000000000 0x0127600000000000 0x01fc000000000010 0x0007f00000000000

def z582 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x066d0c33c631f1c4 0x8019b430cf18c7c7

def z583 : W := mkw 0x69f3037058bf1b70 0x21a7cc0dc162fc6d 0xf9f303f0ffffffff 0xefe7cc0fc3ffffff

def z584 : W := mkw 0x02240000f5288000 0x4408900003d4a200 0x00000000f8000000 0x0000000003e00000

def z585 : W := mkw 0x02248655de3afbfa 0x200892195778ebef 0x00000000fe3fffc0 0x8400000003f8ffff

def z586 : W := mkw 0x0ab4b2ccc6f7f60c 0x082ad2cb331bdfd8 0x1ffef3ccc7fffe3f 0xfc7ffbcf331ffff8

def z587 : W := mkw 0x9e9c8405a785e08a 0x467a7210169e1782 0x1e1c8c0f07c1c008 0x507872303c1f0700

def z588 : W := mkw 0xdffc22ccf5bfd20c 0x4f7ff08b33d6ff48 0xfffc03ccffffc01f 0xcffff00f33ffff00

def z589 : W := mkw 0x9600dc00a7402480 0x16580370029d0092 0x1e01fc00c7c031ed 0xd07807f0031f00c7

def z590 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e203f0383e0e12 0x2f87880fc0e0f838

def z591 : W := mkw 0xfffffbeef7fff60c 0x4fffffefbbdfffd8 0xfffffffffffffe3f 0xfffffffffffffff8

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z593 : W := mkw 0x96004c00a5000080 0x1658013002940002 0x06000c0000000000 0x0018003000000000

def z594 : W := mkw 0xfddb012000000000 0x03f76c0480000000 0xffff03f00000003f 0x6bfffc0fc0000000

def z595 : W := mkw 0xffdbdc00af402d80 0x17ff6f7002bd00b6 0xfffffc00ffc03fff 0xf7fffff003ff00ff

def z596 : W := mkw 0x6143012018080910 0x21850c0480602024 0xe000000038000000 0x0380000000e00000

def z597 : W := mkw 0x41600370503a1270 0x2105800dc140e849 0x01e203f0003e3e33 0xac07880fc000f8f8

def z598 : W := mkw 0xf76f0130fd288970 0x67ddbc04c3f4a225 0xe66d0030f80001c4 0x0399b400c3e00007

def z599 : W := mkw 0x0a90b6ccafd77f8c 0x1c2a42db32bf5dfe 0x1992f3ccfffffffb 0xfc664bcf33ffffff

def z600 : W := mkw 0xffdbfdaaaf402d80 0x17ff6ff6aabd00b6 0xff83fdc0ffc03fef 0xf7fe0ff703ff00ff

def z601 : W := mkw 0x960c0000a5008000 0x4658300002940200 0x060c000000000000 0x0018300000000000

def z602 : W := mkw 0x000092440252760c 0x08000249100949d8 0x0000000000003e00 0x00000000000000f8

def z603 : W := mkw 0x0024000050ad8000 0x400090000142b600 0x00000000003fc000 0x000000000000ff00

def z604 : W := mkw 0xd76c0000f5ad8000 0x475db00003d6b600 0xe66c0000ffffc004 0x8799b00003ffff00

def z605 : W := mkw 0x089022cc0097520c 0x0822408b30025d48 0x019203cc003ffe33 0xac06480f3000fff8

def z606 : W := mkw 0x63678735c630f0ea 0x018d9e1cd718c3c3 0xe7ff8fffc631f1ff 0xbb9ffe3fff18c7c7

def z607 : W := mkw 0x200387750a127bfa 0x20800e1dd42849ef 0x00038fff00003fe0 0x38000e3ffc0000ff

def z608 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xf9e373f000000037 0x6be78dcfc0000000

def z609 : W := mkw 0x0890208800000000 0x0022408220000000 0x019003cc00000010 0x0806400f30000000

def z610 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x019003cc07fffe10 0x8c06400f301ffff8

def z611 : W := mkw 0x20230250583a1b70 0x20808c094160e86d 0xe0030000f83e3fe7 0xa7800c0003e0f8ff

def z612 : W := mkw 0x9400000021000000 0x0650000000840000 0xf800000039c00002 0x47e0000000e70000

def z613 : W := mkw 0x0890000000850000 0x0022400000021400 0x01900000003fc010 0x000640000000ff00

def z614 : W := mkw 0x63670370dc3a9b70 0x218d9c0dc370ea6d 0xe7ff03f0fe3fffff 0xaf9ffc0fc3f8ffff

def z615 : W := mkw 0x96009000a7402400 0x06580240029d0090 0xfe02f000ffc03e2f 0xf7f80bc003ff00f8

def z616 : W := mkw 0x96248615e730f0ea 0x06589218579cc3c3 0xfe7d8e3ffff1f1ff 0xdff9f638ffffc7c7

def z617 : W := mkw 0x43640000d4288000 0x010d90000350a200 0xe7fc0000fe3fc01f 0x879ff00003f8ff00

def z618 : W := mkw 0x00000040180a0b10 0x200000010060282c 0x00000000380e0e00 0x0400000000e03838

def z619 : W := mkw 0x002402154030d06a 0x000090085500c341 0x067d8e3f0031c03d 0x1819f638fc00c700

def z620 : W := mkw 0x000400050000c00a 0x0000100014000300 0x001c000f0001c000 0x000070003c000700

def z621 : W := mkw 0xffff69aaf5ad8000 0x47fffda6abd6b600 0xfffe71c0ffffc01f 0xe7fff9c703ffff00

def z622 : W := mkw 0x63678735de38f9fa 0x218d9e1cd778e3e7 0xe67d8e3ffe31f1fd 0x9b99f638fff8c7c7

def z623 : W := mkw 0x6143012000000000 0x01850c0480000000 0xe061003000000004 0x03818400c0000000

def z624 : W := mkw 0xddd80000318d0000 0x4777600000c63400 0xfffc000039ce001f 0x47fff00000e73800

def z625 : W := mkw 0xf743dd20af402d80 0x17dd0f7482bd00b6 0xffe3fff0ffc03fff 0xffff8fffc3ff00ff

def z626 : W := mkw 0x9c98face02d7760c 0x0a7263eb380b5dd8 0x1f9effcf07fffe3b 0xfc7e7bff3c1ffff8

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010820c00000039 0x1800420830000000

def z628 : W := mkw 0x9e98fc8aa7402480 0x167a63f22a9d0092 0x1e1cfc0f07c00008 0x507873f03c1f0000

def z629 : W := mkw 0xb403d8002b402d00 0x16d00f6000ad00b4 0xf802f0003fc03e2b 0xf7e00bc000ff00f8

def z630 : W := mkw 0x0890208c0085400c 0x0822408230021500 0x0010000c0001c000 0x0000400030000700

def z631 : W := mkw 0x089022cc0097520c 0x0822408b30025d48 0x1992f3cc003fc03b 0x78664bcf3000ff00

def z632 : W := mkw 0x6bf7b7fddefffffe 0x29afdedff77bffff 0xffffffffffffffff 0xffffffffffffffff

def z633 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1990f3cc07ffc018 0x586643cf301fff00

def z634 : W := mkw 0xfdfb69ba58280970 0x23f7eda6e960a025 0xfffffffff80001ff 0x7bffffffffe00007

def z635 : W := mkw 0xf76fdc00ff68ad80 0x57ddbf7003fda2b6 0xfe6ffc00ffc03fef 0xf7f9bff003ff00ff

def z636 : W := mkw 0x9400480000000000 0x0250012000000000 0x1e00fc0000000008 0x507803f000000000

def z637 : W := mkw 0xb627ce15c630f0ea 0x02d89f385718c3c3 0xfe7ffe3fc631f1ff 0xfbf9fff8ff18c7c7

def z638 : W := mkw 0x69f323f8583a1b70 0x21a7cc8fe160e86d 0xf9f3f3fcf83e3fff 0xffe7cfcff3e0f8ff

def z639 : W := mkw 0x9c98f88e02c5640c 0x0a7263e2380b1590 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z640 : W := mkw 0x616393745aff7f7c 0x29858e4dd16bfdfd 0xe1e303f0fffffff7 0xaf878c0fc3ffffff

def z641 : W := mkw 0x0200040084000080 0x0008001002100002 0x06010c00c00001c4 0x0018043003000007

def z642 : W := mkw 0xf7634f70fd3a1bf0 0x37dd8d3dc3f4e86f 0xe7e30ff0f83e3ff7 0xaf9f8c3fc3e0f8ff

def z643 : W := mkw 0xfddb79ea00c70604 0x0bf76de7a8031c18 0xf98271c001ce0e02 0x67e609c700073838

def z644 : W := mkw 0xddd8688a00000000 0x037761a228000000 0xfffcfc0f0000001f 0x53fff3f03c000000

def z645 : W := mkw 0x00008615021070ea 0x00000218540841c3 0x067d8e3f000031fd 0x1819f638fc0000c7

def z646 : W := mkw 0x96240000e5208000 0x0658900003948200 0xfe7c0000fff1c01f 0xc7f9f00003ffc700

def z647 : W := mkw 0x2003037008121b70 0x20800c0dc020486d 0x018303f0003e3ff3 0xac060c0fc000f8ff

def z648 : W := mkw 0xfdfb6bfa503a1270 0x23f7edafe940e849 0xffffffff003e003f 0x7bfffffffc00f800

def z649 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x007c023fc631f1d0 0x8801f008ff18c7c7

def z650 : W := mkw 0x49d821aa00000000 0x01276086a8000000 0x07fd8fff0000003d 0x181ff63ffc000000

def z651 : W := mkw 0xffdb69aaa5000000 0x07ff6da6aa940000 0xffffffffffc0003f 0xffffffffffff0000

def z652 : W := mkw 0x0890b2cc0252760c 0x082242cb300949d8 0x1992f3cc00003e3b 0x78664bcf300000f8

def z653 : W := mkw 0x02240000f5ad8000 0x4408900003d6b600 0x067c0000ffffc01d 0x8419f00003ffff00

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x018203c000000033 0x2806080f00000000

def z655 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x066d8e3fc00031e4 0x1819b638ff0000c7

def z656 : W := mkw 0x0200940086402480 0x0008025002190092 0x1e03fc00c7c03fef 0xf4780ff0031f00ff

def z657 : W := mkw 0xfdfb6bfa583a1b70 0x23f7edafe960e86d 0xf9e373f0f83e3ff7 0xefe78dcfc3e0f8ff

def z658 : W := mkw 0xfddbf9aa02402400 0x03f76fe6a8090090 0xffffffff07c03e3f 0xfffffffffc1f00f8

def z659 : W := mkw 0x9600dc00a7402480 0x16580370029d0092 0xfe00fc00ffc0000f 0xd7f803f003ff0000

def z660 : W := mkw 0x22039400af402d80 0x14880e5002bd00b6 0xe0030000ffc03fe7 0xa7800c0003ff00ff

def z661 : W := mkw 0x2227de15ce70fdea 0x10889f785739c3f7 0x067ffe3fc631fffd 0xb819fff8ff18c7ff

def z662 : W := mkw 0x0000800002002000 0x0000020000080080 0x0000800006003029 0x90000200001800c0

def z663 : W := mkw 0x0890208800000000 0x0022408220000000 0x1810f00c00000008 0x506043c030000000

def z664 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1810f00c07fffe08 0xd46043c0301ffff8

def z665 : W := mkw 0xffff8775ffbffbfa 0x67fffe1dd7feffef 0xffff8fffffffffff 0xfffffe3fffffffff

def z666 : W := mkw 0x0000b2cc0252760c 0x080002cb300949d8 0x0012f3cc0631fe39 0xb8004bcf3018c7f8

def z667 : W := mkw 0x2893b2cc0ad77f0c 0x08a24ecb302b5dfc 0xf993f3ccffffffff 0xffe64fcf33ffffff

def z668 : W := mkw 0x02000000a5000000 0x0408000002940000 0x00000000ffc00000 0x8400000003ff0000

def z669 : W := mkw 0xb603fdaaaf402d80 0x16d80ff6aabd00b6 0xfe03ffffffc03fef 0xfff80fffffff00ff

def z670 : W := mkw 0x0890208800000000 0x0022408220000000 0x198271c000000002 0x606609c700000000

def z671 : W := mkw 0x089030c800c70604 0x082240c320031c18 0x1992f3cc01ce0e3b 0x7c664bcf30073838

def z672 : W := mkw 0x96000000a5000000 0x0658000002940000 0x1e00000007c00008 0x40780000001f0000

def z673 : W := mkw 0xfdff69aa50ad8000 0x43f7fda6a942b600 0xffffffff003fc03f 0x7bfffffffc00ff00

def z674 : W := mkw 0x43648615d638f0ea 0x010d92185758e3c3 0xe7fd8e3ffe3ff1ff 0x9f9ff638fff8ffc7

def z675 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xffec0000f9ce0006 0x47ffb00003e73800

def z676 : W := mkw 0x63670771dc3a9bf2 0x218d9c1dc770ea6f 0xe7ef0ff3f83e3ff7 0xaf9fbc3fcfe0f8ff

def z677 : W := mkw 0x220384008e002980 0x00880e10023800a6 0xe6038c00fe003fef 0xb7980e3003f800ff

def z678 : W := mkw 0x0000024000121200 0x0000000900004848 0x00000000003e3e00 0x840000000000f8f8

def z679 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x00610230c631f1f5 0x88018408c318c7c7

def z680 : W := mkw 0xffffde15fffdfdea 0x57ffff7857fff7f7 0xfffffe3fffffffff 0xfffffff8ffffffff

def z681 : W := mkw 0x49d80000108d0000 0x4127600000423400 0x01800000000e0000 0x0006000000003800

def z682 : W := mkw 0x2023021048301960 0x00808c084120c065 0xe0630230f8303ff7 0xaf818c08c3e0c0ff

def z683 : W := mkw 0x6163000058280900 0x01858c000160a024 0xe1e30000f83e3ff7 0xa7878c0003e0f8ff

def z684 : W := mkw 0x63670531dc2889f2 0x218d9c14c770a227 0xe66d0c33f80001c4 0x0399b430cfe00007

def z685 : W := mkw 0x2003000008000900 0x00800c0000200024 0xe002000038000e02 0x2780080000e00038

def z686 : W := mkw 0x0ab40000c4a58000 0x002ad00003129600 0x1ffc0000c7ffc01f 0xc47ff000031fff00

def z687 : W := mkw 0x0890a28c02107008 0x0022428a300841c0 0x1992f3cc0631f03b 0xf8664bcf3018c7c0

def z688 : W := mkw 0x02009400af402d80 0x1408025002bd00b6 0x06018c00ffc03fed 0x9418063003ff00ff

def z689 : W := mkw 0x0000100000400400 0x0000004000010010 0x1802700001c00e02 0x646009c000070038

def z690 : W := mkw 0x0000000000850000 0x0000000000021400 0x0000000007ffc000 0x84000000001fff00

def z691 : W := mkw 0x6163b3fc5a7a7f7c 0x29858ecff169e9fd 0xe1e3f3fcf83e3ff7 0xbf878fcff3e0f8ff

def z692 : W := mkw 0x0000208800000000 0x0000008220000000 0x0002f3cc00000020 0x38000bcf30000000

def z693 : W := mkw 0xb623de10ef703de0 0x16d88f7843bdc0f7 0xfe63fe30fff03fff 0xfff98ff8c3ffc0ff

def z694 : W := mkw 0x9c98688a00000000 0x027261a228000000 0x1800700000000000 0x406001c000000000

def z695 : W := mkw 0xf76f4c00fd288980 0x57ddbd3003f4a226 0xe66d0c00f80001c4 0x0399b43003e00007

def z696 : W := mkw 0xdfd80000b58d0000 0x477f600002d63400 0xff800000ffce000f 0xc7fe000003ff3800

def z697 : W := mkw 0xd76c0000f5288000 0x475db00003d4a200 0xfe6c0000ffc0000f 0xc7f9b00003ff0000

def z698 : W := mkw 0xdffc9400ffedad80 0x577ff25003ffb6b6 0xfffc0000ffffffdf 0xc7fff00003ffffff

def z699 : W := mkw 0x02248615f7bdf0ea 0x4408921857def7c3 0x00000000fffff1c0 0x8400000003ffffc7

def z700 : W := mkw 0xbe9fdc00afc5ad80 0x56fa7f7002bf16b6 0xfe1ffc00ffc1ffef 0xf7f87ff003ff07ff

def z701 : W := mkw 0x02240000c4208000 0x0008900003108200 0x067d8e3fc631c03d 0x9819f638ff18c700

def z702 : W := mkw 0x0ab4b2ccf7fff60c 0x4c2ad2cb33dfffd8 0x1992f3ccfffffe3b 0xfc664bcf33fffff8

def z703 : W := mkw 0x0020001040200060 0x0000800041008001 0x00610030c00001c4 0x00018400c3000007

def z704 : W := mkw 0xb403dc002b402d80 0x16d00f7000ad00b6 0xf803fc0039c03fe2 0x77e00ff000e700ff

def z705 : W := mkw 0xffff0130fdad8970 0x67fffc04c3f6b625 0xfffd0030ffffc1df 0xc7fff400c3ffff07

def z706 : W := mkw 0x0000688a00000000 0x000001a228000000 0x0000fc0f00000000 0x100003f03c000000

def z707 : W := mkw 0x2003fbfe0a527f7c 0x28800feff82949fd 0x0003ffff00003fe0 0x38000ffffc0000ff

def z708 : W := mkw 0x0000208800000000 0x0000008220000000 0x067fffff0000003d 0x3819fffffc000000

def z709 : W := mkw 0x61670375583adb7a 0x21859c0dd560eb6d 0xe7ff8ffff83fffff 0xbf9ffe3fffe0ffff

def z710 : W := mkw 0x69ffdc005aedad80 0x51a7ff70016bb6b6 0x01fffc00003ffff0 0x3007fff00000ffff

def z711 : W := mkw 0xdffc0401f5ad8082 0x477ff01007d6b602 0xfffc0c03ffffc01f 0xc7fff0300fffff00

def z712 : W := mkw 0xfddb69aa00850000 0x03f76da6a8021400 0xffffffff01ce003f 0x7ffffffffc073800

def z713 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1f9effcf07fffe3b 0xfc7e7bff3c1ffff8

def z714 : W := mkw 0xf76f4d30fd2889f0 0x77ddbd34c3f4a227 0xe66d0c30f80001c4 0x0399b430c3e00007

def z715 : W := mkw 0xbe9f0370ad979b70 0x66fa7c0dc2b65e6d 0x1e1f03f007c1ffe8 0x68787c0fc01f07ff

def z716 : W := mkw 0x4bd8b5aaaf402d80 0x152f62d6aabd00b6 0x01fc03ffffc03fd0 0x8c07f00fffff00ff

def z717 : W := mkw 0x0890b6dd02d776ee 0x082242db740b5ddb 0x1fffffff07ffffff 0xfc7ffffffc1fffff

def z718 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe03fc00f9c03fe6 0x77f80ff003e700ff

def z719 : W := mkw 0xdffc4800f5ad8000 0x477ff12003d6b600 0xfffcfc00ffffc01f 0xd7fff3f003ffff00

def z720 : W := mkw 0xdffc21aaf5ad8000 0x477ff086abd6b600 0xfffc01c0ffffc01f 0xc7fff00703ffff00

def z721 : W := mkw 0xd76cb2ccf77af60c 0x4f5db2cb33ddebd8 0xe66ef3ccf8003e24 0x3b99bbcf33e000f8

def z722 : W := mkw 0x61634b72583a1b70 0x21858d2dc960e86d 0xe1e30ff3f83e3ff7 0xaf878c3fcfe0f8ff

def z723 : W := mkw 0x9cb86ada583a1b70 0x2272e1ab6960e86d 0x1e1cfc0ff83e3fc8 0xd47873f03fe0f8ff

def z724 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe13fc00fff1ffff 0xf7f84ff003ffc7ff

def z725 : W := mkw 0xfddb69aa18080910 0x23f76da6a8602024 0xffffffff3800003f 0x7bfffffffce00000

def z726 : W := mkw 0x2003facc0a527f0c 0x18800feb302949fc 0x0002f3cc00003e20 0x38000bcf300000f8

def z727 : W := mkw 0x089032c800d71604 0x082240cb20035c58 0x199273c007fffe3b 0xec6649cf001ffff8

def z728 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1ffef3cc07fffe3f 0xfc7ffbcf301ffff8

def z729 : W := mkw 0xdffc4c00f5ad8080 0x577ff13003d6b602 0xfffc0c00ffffc01f 0xc7fff03003ffff00

def z730 : W := mkw 0xb6039000af402d00 0x06d80e4002bd00b4 0xfe03f000ffc03fef 0xf7f80fc003ff00ff

def z731 : W := mkw 0x41600370583a1b70 0x2105800dc160e86d 0xe1e003f0f83e3fd7 0x8f87800fc3e0f8ff

def z732 : W := mkw 0x0890b0c802c72604 0x082242c3200b1c98 0x1992f1c007fffe3b 0xf4664bc7001ffff8

def z733 : W := mkw 0x6143036008121b00 0x01850c0d8020486c 0xe1e303f0f83e3ff7 0xaf878c0fc3e0f8ff

def z734 : W := mkw 0xb603dd22af402d80 0x16d80f748abd00b6 0xfe03fc33ffc03fef 0xf7f80ff0cfff00ff

def z735 : W := mkw 0xdffc0010f5ad8060 0x477ff00043d6b601 0xfffd0030ffffc1df 0xc7fff400c3ffff07

def z736 : W := mkw 0xdffc21aaf5ad8000 0x477ff086abd6b600 0xfffd8fffffffc03f 0xdffff63fffffff00

def z737 : W := mkw 0x020486158610f0ea 0x00081218561843c3 0x067d8e3f0601f1fd 0x1819f638fc1807c7

def z738 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xffec0000ffffc006 0xc7ffb00003ffff00

def z739 : W := mkw 0x61430360181a1b10 0x21850c0d8060686c 0xe18303c0f83e3ff7 0xaf860c0f03e0f8ff

def z740 : W := mkw 0xd76c0000f5ad8000 0x475db00003d6b600 0xe67c0000ffffc01d 0x8799f00003ffff00

def z741 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1992f3cc07ffce1a 0x7c664bcf301fff38

def z742 : W := mkw 0x02240415c420c0ea 0x0008901057108303 0x067d0c3fc001c1c4 0x0019f430ff000707

def z743 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe6ffc33ffc03fef 0xf7f9bff0cfff00ff

def z744 : W := mkw 0x61430370181a1b70 0x21850c0dc060686d 0xe18303f0f80e3fe7 0xaf860c0fc3e038ff

def z745 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1982f1c007fffe2b 0xf4660bc7001ffff8

def z746 : W := mkw 0xffffefbfc630f0ea 0x03ffffbeff18c3c3 0xf98271c0c631f1c2 0xe3e609c70318c7c7

def z747 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xfe7fffff0000002c 0x7bf9fffffc000000

def z748 : W := mkw 0xf54bdb6602d7760c 0x0bd52f6d980b5dd8 0xe66d0c3307fffe04 0x8799b430cc1ffff8

def z749 : W := mkw 0xdffc69aaf5ad8000 0x477ff1a6abd6b600 0xfffcffffffffc01f 0xdffff3ffffffff00

def z750 : W := mkw 0x220394008e402d80 0x00880e50023900b6 0xfe03fc00ffc03fef 0xf7f80ff003ff00ff

def z751 : W := mkw 0x2003b7fd0a527ffe 0x28800edff42949ff 0x0003ffff00003fe0 0x38000ffffc0000ff

def z752 : W := mkw 0x69d321a800000000 0x01a74c86a0000000 0xffffffff0000003f 0x7bfffffffc000000

def z753 : W := mkw 0x61430160180a0b10 0x21850c058060282c 0xe1e303f0f80e3ff7 0xaf878c0fc3e038ff

def z754 : W := mkw 0x96240000f5ad8000 0x4658900003d6b600 0xf8000000ffffc002 0xc7e0000003ffff00

def z755 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xf803fc00ffc03fe2 0xf7e00ff003ff00ff

def z756 : W := mkw 0xfddb69aa108d0000 0x43f76da6a8423400 0xffffffff000e003f 0x7bfffffffc003800

def z757 : W := mkw 0x2003037008121b70 0x20800c0dc020486d 0xe18303f0f83e3ff7 0xaf860c0fc3e0f8ff

def z758 : W := mkw 0x020484058600e08a 0x0008121016180382 0x067d8e3fc601f1fd 0x9819f638ff1807c7

def z759 : W := mkw 0xfddb69aa29000900 0x17f76da6a8a40024 0xffffffff3800003f 0x7bfffffffce00000

def z760 : W := mkw 0x02240615c430d0ea 0x000890185710c343 0x067d8e3fc031c1fd 0x1819f638ff00c707

def z761 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1992f3cc07fffe38 0x78664bcf301ffff8

def z762 : W := mkw 0xd760df70f77a36f0 0x375d837dc3dde8db 0x1fe0fff007fe0018 0x587f83ffc01ff800

def z763 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xfffeffff0000001a 0x7bfffbfffc000000

def z764 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e203f0f83e3fd2 0xaf87880fc3e0f8ff

def z765 : W := mkw 0x69f3b1bc5aed6d7c 0x29a7cec6f16bb5b5 0xf871f03cffc1c1cc 0x53e1c7c0f3ff0707

def z766 : W := mkw 0xddf8000050ad0000 0x0377e0000142b400 0xfffc0000ffffc01f 0xc7fff00003ffff00

def z767 : W := mkw 0x4bf40000f5ad8000 0x452fd00003d6b600 0xf9f00000ffffc01f 0xc7e7c00003ffff00

def z768 : W := mkw 0x61634b70583a1b70 0x21858d2dc160e86d 0xe1e3fff0f83e3ff7 0xbf878fffc3e0f8ff

def z769 : W := mkw 0xdfdc0000b58d8000 0x477f700002d63600 0xff9c00003fffc01b 0xc7fe700000ffff00

def z770 : W := mkw 0xddfc000071ad8000 0x4777f00001c6b600 0xf9fc00003fffc01b 0xc7e7f00000ffff00

def z771 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e38ffff83e3ff7 0xbf878e3fffe0f8ff

def z772 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe03fe3fffc03fef 0xfff80ff8ffff00ff

def z773 : W := mkw 0x9e9cfc8aa7c5a480 0x567a73f22a9f1692 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z774 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xf802f000ffc03feb 0xf7e00bc003ff00ff

def z775 : W := mkw 0x61670375583adb7a 0x21859c0dd560eb6d 0xe1e303f0f83ffff7 0xaf878c0fc3e0ffff

def z776 : W := mkw 0x002486154230f0ea 0x000092185508c3c3 0x067d8e3f0031f1fd 0x1819f638fc00c7c7

def z777 : W := mkw 0x222769aaf5ad8000 0x44889da6abd6b600 0x0003ffffffffc020 0xbc000fffffffff00

def z778 : W := mkw 0x6163012058280900 0x01858c048160a024 0xe1e303f0f83e3ff7 0xaf878c0fc3e0f8ff

def z779 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e301f0f83e3fc6 0xa7878c07c3e0f8ff

def z780 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xff9c0000ffffc00a 0xc7fe700003ffff00

def z781 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffc0000ffffc01c 0x43fff00003ffff00

def z782 : W := mkw 0x0020821442307068 0x000082085108c1c1 0x067d8e3fc631f1fd 0x9819f638ff18c7c7

def z783 : W := mkw 0xdffc21aaf5ad8000 0x477ff086abd6b600 0xfffef3ffffffc03f 0xfffffbcfffffff00

def z784 : W := mkw 0x0890b08802c52400 0x002242c2200b1490 0x1992f3cc07fffe3b 0xfc664bcf301ffff8

def z785 : W := mkw 0x2023025048321b60 0x00808c094120c86d 0xe1e303f0f83e3ff7 0xaf878c0fc3e0f8ff

def z786 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe02fc00ffc03fca 0xf7f80bf003ff00ff

def z787 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xff83fc00fffe3fff 0xf7fe0ff003fff8ff

def z788 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xe7ffffff00000034 0x3b9ffffffc000000

def z789 : W := mkw 0x0200860486107088 0x00080218121841c2 0x067d8e3fc631f1fd 0x9819f638ff18c7c7

def z790 : W := mkw 0x9c90000021850000 0x0672400000861400 0xf99000003fffc01b 0xc7e6400000ffff00

def z791 : W := mkw 0x02249615c670f4ea 0x000892585719c3d3 0x067ffe3fc631fffd 0xb819fff8ff18c7ff

def z792 : W := mkw 0xb6034800ad000900 0x06d80d2002b40024 0xfe03fc00ffc03fef 0xf7f80ff003ff00ff

def z793 : W := mkw 0xb6035c00ad400d80 0x16d80d7002b50036 0xfe037c00f9c03fe7 0xe7f80df003e700ff

def z794 : W := mkw 0x200369aa00000000 0x00800da6a8000000 0x066fffff00000024 0x3819bffffc000000

def z795 : W := mkw 0x0ab434d9c4e786e6 0x082ad0d367139e1b 0x1fef7df3c1ce0fc6 0x647fbdf7cf07383f

def z796 : W := mkw 0x20230250583a1b70 0x20808c094160e86d 0xe18303c0f83e3ff7 0xaf860c0f03e0f8ff

def z797 : W := mkw 0xb607dc05af40ed8a 0x16d81f7016bd03b6 0xfe03fc00ffc1ffef 0xf7f80ff003ff07ff

def z798 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffffffff0631c03f 0xfbfffffffc18c700

def z799 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffe03c0ffffc03f 0xeffff80f03ffff00

def z800 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe63fe30ffc03fff 0xfff98ff8c3ff00ff

def z801 : W := mkw 0xb603dd20af402d80 0x16d80f7482bd00b6 0xfe03fff0ffc03fef 0xfff80fffc3ff00ff

def z802 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe7ef0ff3f83e3ff7 0xaf9fbc3fcfe0f8ff

def z803 : W := mkw 0xd7640000f5288000 0x075d900003d4a200 0xfffc0000ffffc01f 0xc7fff00003ffff00

def z804 : W := mkw 0xfddb79ea29c70f04 0x1ff76de7a8a71c3c 0xf98271c039ce0e02 0x67e609c700e73838

def z805 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe1ffc0fffc03fef 0xf7f87ff03fff00ff

def z806 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e303f0f83e3ff4 0x2b878c0fc3e0f8ff

def z807 : W := mkw 0xbe936eccad975b8c 0x1efa4dbb32b65d6e 0xe7910fccf83fc1d4 0x0b9e443f33e0ff07

def z808 : W := mkw 0xbc9b69aa00000000 0x02f26da6a8000000 0x1e7fffff0000003d 0x7879fffffc000000

def z809 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x07ff8fffc631f1ff 0xb81ffe3fff18c7c7

def z810 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d0e3fc631f1d4 0x8819f438ff18c7c7

def z811 : W := mkw 0x96000000a5850000 0x0658000002961400 0xfe000000ffffc00f 0xc7f8000003ffff00

def z812 : W := mkw 0x614369aa00000000 0x01850da6a8000000 0xe7ffffff0000003f 0x3b9ffffffc000000

def z813 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x1e7ffe3fc631f1ff 0xf879fff8ff18c7c7

def z814 : W := mkw 0x61630375583a5b7a 0x21858c0dd560e96d 0xe1e303fff83e3ff7 0xaf878c0fffe0f8ff

def z815 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffffffff003e003f 0xfffffffffc00f800

def z816 : W := mkw 0x02240411c42080e2 0x0008901047108203 0x067d8e3fc631c1fd 0x9819f638ff18c707

def z817 : W := mkw 0x9e94fc8da7c5e48e 0x1e7a53f2369f1792 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z818 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffd0c33ffffc01f 0xc7fff430cfffff00

def z819 : W := mkw 0xdffc2088f5ad8000 0x477ff08223d6b600 0xfffc03ccffffc01f 0xcffff00f33ffff00

def z820 : W := mkw 0x49fc22dd50bfd26e 0x4927f08b7542ff49 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z821 : W := mkw 0xb403580029400d00 0x16d00d6000a50034 0xfe03fc00f9c03fef 0xf7f80ff003e700ff

def z822 : W := mkw 0xfddb69aa10080000 0x03f76da6a8402000 0xffffffff380e003f 0x7ffffffffce03800

def z823 : W := mkw 0x61670370583a9b70 0x21859c0dc160ea6d 0xe1ff03f0f83ffff7 0xaf87fc0fc3e0ffff

def z824 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfe7c0000ffffc00c 0xc7f9f00003ffff00

def z825 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d8e3f0631f1f8 0x1819f638fc18c7c7

def z826 : W := mkw 0xf76f4d22fd288980 0x57ddbd348bf4a226 0xe66d0c33f80001c4 0x0399b430cfe00007

def z827 : W := mkw 0xddd88615339d70ea 0x4777621854ce75c3 0xf9818e3f39ce31e2 0x5fe60638fce738c7

def z828 : W := mkw 0x49fc000050ad8000 0x4127f0000142b600 0xf9fc0000ffffc01f 0xc7e7f00003ffff00

def z829 : W := mkw 0x02248400c620a080 0x0008921003188282 0x067d8e3fc631f1fd 0x9819f638ff18c7c7

def z830 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x199271c007fffe1b 0xe46649c7001ffff8

def z831 : W := mkw 0xf54b69aa00000000 0x03d52da6a8000000 0xfe6fffff0000002f 0x7bf9bffffc000000

def z832 : W := mkw 0x96240000f5ad8000 0x4658900003d6b600 0xe6000000ffffc004 0x8798000003ffff00

def z833 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1f383fcf83e3fff 0xbf87ce0ff3e0f8ff

def z834 : W := mkw 0xb60fdc00af40ad80 0x56d83f7002bd02b6 0xfe0ffc00ffc03fef 0xf7f83ff003ff00ff

def z835 : W := mkw 0x002402154030d06a 0x000090085500c341 0x067d8e3fc031f1fd 0x9819f638ff00c7c7

def z836 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e303f0f80e3fe6 0x2f878c0fc3e038ff

def z837 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1993f3ccc7ffffff 0xfc664fcf331fffff

def z838 : W := mkw 0xb4275a156970dd6a 0x16d09d6855a5c375 0xf87e723f39f1ce12 0x6fe1f9c8fce7c738

def z839 : W := mkw 0x96240000f5ad8000 0x4658900003d6b600 0xfe7c0000ffffc01f 0xc7f9f00003ffff00

def z840 : W := mkw 0xfddb69aa08000900 0x03f76da6a8200024 0xfffffffff80001ff 0x7bffffffffe00007

def z841 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x19f3f3fc07fffe3f 0xfc67cfcff01ffff8

def z842 : W := mkw 0x2003df750a527ffa 0x30800f7dd42949ff 0x0003ffff00003fe0 0x38000ffffc0000ff

def z843 : W := mkw 0x9e9c0000a5858000 0x467a700002961600 0xff9c0000ffffc01f 0xc7fe700003ffff00

def z844 : W := mkw 0xddd869aa00000000 0x037761a6a8000000 0xfffcffff0000001f 0x5bfff3fffc000000

def z845 : W := mkw 0x0890b6cd02d7768e 0x082242db340b5dda 0x1992ffcf07fffe3b 0xfc664bff3c1ffff8

def z846 : W := mkw 0x2003b3ec0a527f1c 0x28800ecfb02949fc 0x0002f3cc00003e20 0x38000bcf300000f8

def z847 : W := mkw 0x2003fffc0a527ffc 0x38800ffff02949ff 0x0003fffc00003fe0 0x38000ffff00000ff

def z848 : W := mkw 0x49fc23fc50bfd27c 0x6927f08ff142ff49 0x01fc03fc003fc010 0x0807f00ff000ff00

def z849 : W := mkw 0x289369aa00000000 0x00a24da6a8000000 0x1fffffff0000003f 0x787ffffffc000000

def z850 : W := mkw 0xd76c0000f5ad8000 0x475db00003d6b600 0xe0000000ffffc000 0x8780000003ffff00

def z851 : W := mkw 0x616b0372583a1b70 0x2185ac0dc960e86d 0xe1ef03f3f83e3ff7 0xaf87bc0fcfe0f8ff

def z852 : W := mkw 0x02248655d63af2fa 0x200892195758ebcb 0x067d8e3fc63ff1fd 0x9819f638ff18ffc7

def z853 : W := mkw 0x02249615e770f4ea 0x14089258579dc3d3 0x067d8e3fc7f1f1fd 0x9819f638ff1fc7c7

def z854 : W := mkw 0x02249655defffffe 0x28089259577bffff 0x00000000ffffffc0 0x8400000003ffffff

def z855 : W := mkw 0xddd869aa00000000 0x037761a6a8000000 0x1ffdffff0000003d 0x587ff7fffc000000

def z856 : W := mkw 0x61630374583a5b78 0x21858c0dd160e96d 0xe1f303fcf83ffff7 0xaf87cc0ff3e0ffff

def z857 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1992f1cc07fffe0a 0xf4664bc7301ffff8

def z858 : W := mkw 0x0890b6cc02d7768c 0x082242db300b5dda 0x1993ffcc07fffffb 0xfc664fff301fffff

def z859 : W := mkw 0xfddb69ea398f0b10 0x67f76da7a8e63c2c 0xf98271c039ce0e02 0x67e609c700e73838

def z860 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffc00003fffc01a 0x47fff00000ffff00

def z861 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067f8e3fc631ffff 0xbc19fe38ff18c7ff

def z862 : W := mkw 0x9c98688a00000000 0x027261a228000000 0x1fffffff0000003f 0x787ffffffc000000

def z863 : W := mkw 0x2003100008400d00 0x00800c4000210034 0xf8037000f9c03fe7 0xe7e00dc003e700ff

def z864 : W := mkw 0x0890b0cc02c7660c 0x082242c3300b1d98 0x1992f1cc07ffce1b 0xf4664bc7301fff38

def z865 : W := mkw 0xf54b69aa00000000 0x03d52da6a8000000 0xe7efffff00000037 0x3b9fbffffc000000

def z866 : W := mkw 0xd76c0000f5ad8000 0x475db00003d6b600 0xe7ec0000ffffc017 0x879fb00003ffff00

def z867 : W := mkw 0x2003ffee0a527f8c 0x18800fffb82949fe 0x0003ffff00003fe0 0x38000ffffc0000ff

def z868 : W := mkw 0x0000924402d7760c 0x08000249100b5dd8 0x1982f3c007fffe3b 0xfc660bcf001ffff8

def z869 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xf9900000ffffc01b 0xc7e6400003ffff00

def z870 : W := mkw 0x02248415c620e0ea 0x0008921057188383 0x067d8c3fc601f1ed 0x9019f630ff1807c7

def z871 : W := mkw 0x96009400af402d80 0x1658025002bd00b6 0xfe02f000ffc03fef 0xf7f80bc003ff00ff

def z872 : W := mkw 0x02249655c672f6ee 0x080892595719cbdb 0x067d8e3fc631fffd 0x9819f638ff18c7ff

def z873 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0xf992f3ccfffffe3f 0xffe64bcf33fffff8

def z874 : W := mkw 0xdffc688af5ad8000 0x477ff1a22bd6b600 0xfffdfe3fffffc03f 0xdffff7f8ffffff00

def z875 : W := mkw 0x43640000f5ad8000 0x450d900003d6b600 0xe1800000ffffc002 0x8786000003ffff00

def z876 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1ff03fff83e3ff7 0xaf87fc0fffe0f8ff

def z877 : W := mkw 0x616f0370583a9b70 0x6185bc0dc160ea6d 0xe1ef03f0f83e3ff7 0xaf87bc0fc3e0f8ff

def z878 : W := mkw 0x9e90fc88a7c52484 0x1e7a43f2229f1492 0x1e00fc0007c00008 0x507803f0001f0000

def z879 : W := mkw 0xfddb69aa31080000 0x47f76da6a8c42000 0xffffffff3800003f 0x7bfffffffce00000

def z880 : W := mkw 0xdffc0011f5ad8062 0x477ff00047d6b601 0xfffc0033ffffc01f 0xc7fff000cfffff00

def z881 : W := mkw 0x634785659e0aeb9a 0x218d1e1596782bae 0xe79e8dcf3e0fce0a 0x379e7a373cf83f38

def z882 : W := mkw 0xb403dc002b402d80 0x16d00f7000ad00b6 0xf803fc00f9c03fe7 0xf7e00ff003e700ff

def z883 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe01fc00ffc03fcc 0xd7f807f003ff00ff

def z884 : W := mkw 0x02240000f5ad8000 0x4408900003d6b600 0xe0000000ffffc007 0x8780000003ffff00

def z885 : W := mkw 0x0000924402527608 0x00000249100949d8 0x1992f3cc07fffe3b 0xfc664bcf301ffff8

def z886 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d8c3fc631f1cc 0x9019f630ff18c7c7

def z887 : W := mkw 0x02248415c620e0ea 0x0008921057188383 0x067d8e3fc601c1fd 0x1819f638ff180707

def z888 : W := mkw 0x4bfc0000f5ad8000 0x452ff00003d6b600 0xe1fc0000ffffc017 0x8787f00003ffff00

def z889 : W := mkw 0xb603dc04af406d88 0x16d80f7012bd01b6 0xfe13fc0cffc1ffef 0xf7f84ff033ff07ff

def z890 : W := mkw 0x02249615c670f4ea 0x000892585719c3d3 0x1e7dfe3fc7f1f1fd 0xd879f7f8ff1fc7c7

def z891 : W := mkw 0x02240615c430d0ea 0x000890185710c343 0x067d0e3fc631c1dd 0x8819f438ff18c707

def z892 : W := mkw 0x9e98fc8ea7c5648c 0x1e7a63f23a9f1592 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z893 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0x1fffffff00000038 0x787ffffffc000000

def z894 : W := mkw 0x9eb40000f5ad8000 0x467ad00003d6b600 0xff900000ffffc01f 0xc7fe400003ffff00

def z895 : W := mkw 0x9ebc0000f5ad8000 0x467af00003d6b600 0xfe1c0000ffffc00f 0xc7f8700003ffff00

def z896 : W := mkw 0x43640000f5ad8000 0x450d900003d6b600 0xe7fc0000ffffc01f 0x879ff00003ffff00

def z897 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d8e3fc631c1dc 0x1819f638ff18c707

def z898 : W := mkw 0x49fc23fa50bf9270 0x6127f08fe942fe49 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z899 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x199273cc07fffe12 0xec6649cf301ffff8

def z900 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffffffff07c0003f 0xfffffffffc1f0000

def z901 : W := mkw 0x0890000000850000 0x0022400000021400 0xf9900000ffffc01f 0xc7e6400003ffff00

def z902 : W := mkw 0xfddb69aa318d0000 0x47f76da6a8c63400 0xffffffff3fffc03f 0xfffffffffcffff00

def z903 : W := mkw 0x089030c800c70604 0x082240c320031c18 0x198271c007ffce02 0xe46609c7001fff38

def z904 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffd0000fffff1ff 0xc7fff40003ffffc7

def z905 : W := mkw 0x49d00000108d0000 0x0127400000423400 0xf99000003fffc01b 0xc7e6400000ffff00

def z906 : W := mkw 0xdffc0122f5ad8000 0x477ff0048bd6b600 0xfffc0033ffffc01f 0xc7fff000cfffff00

def z907 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0xe67d8e3ffe31f1ff 0x9f99f638fff8c7c7

def z908 : W := mkw 0x9e9cfc8ca7c5e48c 0x5e7a73f2329f1792 0x1e1cfc0c07c1c008 0x507873f0301f0700

def z909 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffefffff00000026 0x7bffbffffc000000

def z910 : W := mkw 0x4bf40000d4ad8000 0x012fd0000352b600 0xfffc0000ffffc01f 0xc7fff00003ffff00

def z911 : W := mkw 0x4160000050ad0000 0x010580000142b400 0xe1e00000ffffc017 0x8787800003ffff00

def z912 : W := mkw 0xddd80000318d0000 0x4777600000c63400 0xfffc00003fffc01f 0xc7fff00000ffff00

def z913 : W := mkw 0xb403580029400d00 0x16d00d6000a50034 0xf8027000f9c03fc2 0xe7e009c003e700ff

def z914 : W := mkw 0x22039400af402d80 0x14880e5002bd00b6 0xf803f000ffc03fef 0xf7e00fc003ff00ff

def z915 : W := mkw 0xd76c0000f5ad8000 0x475db00003d6b600 0xfe6c0000ffffc00f 0xc7f9b00003ffff00

def z916 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe03fc00ffc03fec 0x73f80ff003ff00ff

def z917 : W := mkw 0xdffc4802f5ad8000 0x477ff1200bd6b600 0xfffc0c03ffffc01f 0xc7fff0300fffff00

def z918 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffef000ffffc03f 0xf7fffbc003ffff00

def z919 : W := mkw 0x02249615c670f4ea 0x000892585719c3d3 0x067d8e3fc7f1fffd 0x9c19f638ff1fc7ff

def z920 : W := mkw 0x2003b2cc0a527f0c 0x08800ecb302949fc 0x0003f3cc00003fe0 0x38000fcf300000ff

def z921 : W := mkw 0x9eb40000e5a58000 0x067ad00003969600 0xfffc0000ffffc01f 0xc7fff00003ffff00

def z922 : W := mkw 0x02249655f7fff6ee 0x4c08925957dfffdb 0x00000000ffffffc0 0x8400000003ffffff

def z923 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe18203c0f83e3ff3 0xaf86080f03e0f8ff

def z924 : W := mkw 0xb60bdc02af402d80 0x16d82f700abd00b6 0xfe0ffc03ffc03fef 0xf7f83ff00fff00ff

def z925 : W := mkw 0x49f423fd50bfd27e 0x2927d08ff542ff49 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z926 : W := mkw 0xfddb69aa08000900 0x03f76da6a8200024 0xffffffff00003fff 0x7bfffffffc0000ff

def z927 : W := mkw 0x089030c800c70604 0x082240c320031c18 0x1992f3cc07ffce3b 0xfc664bcf301fff38

def z928 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xe7fc0000ffffc014 0x879ff00003ffff00

def z929 : W := mkw 0x61630240583a1b00 0x01858c090160e86c 0xe1e303c0f83e3ff7 0xaf878c0f03e0f8ff

def z930 : W := mkw 0xdffc0120f5ad8000 0x477ff00483d6b600 0xfffc03f0ffffc01f 0xcffff00fc3ffff00

def z931 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1f93ffcc07fffe3f 0xfc7e4fff301ffff8

def z932 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe18301c0f83e3fe7 0xa7860c0703e0f8ff

def z933 : W := mkw 0xb6035800ad400d00 0x16d80d6002b50034 0xfe037000ffc03fef 0xe7f80dc003ff00ff

def z934 : W := mkw 0xdffc2088f5ad8000 0x477ff08223d6b600 0xfffcf00cffffc01f 0xd7fff3c033ffff00

def z935 : W := mkw 0x61630160582a0b10 0x21858c058160a82c 0xe1e301c0f83e3ff7 0xa7878c0703e0f8ff

def z936 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x1e7d8e3fc7f1f1ff 0xdc79f638ff1fc7c7

def z937 : W := mkw 0x200393740a527f7c 0x28800e4dd02949fd 0x000303f000003fe0 0x28000c0fc00000ff

def z938 : W := mkw 0x9600dc00af402d80 0x1658037002bd00b6 0xfe00fc00ffc03fcf 0xd7f803f003ff00ff

def z939 : W := mkw 0x61430160180a0b10 0x21850c058060282c 0xe18201c0f80e3fc2 0xa786080703e038ff

def z940 : W := mkw 0x61630170582a0b70 0x21858c05c160a82d 0xe1e301f0f80e3fe7 0xa7878c07c3e038ff

def z941 : W := mkw 0xddd8208800000000 0x0377608220000000 0xffffffff0000003f 0x7bfffffffc000000

def z942 : W := mkw 0x61670371583a9b72 0x21859c0dc560ea6d 0xe1ef03f3f83e3ff7 0xaf87bc0fcfe0f8ff

def z943 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xfffdffff0000001c 0x5bfff7fffc000000

def z944 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xf9e303f0fffe3fff 0xefe78c0fc3fff8ff

def z945 : W := mkw 0xdffc0400f5ad8080 0x477ff01003d6b602 0xfffd0c00ffffc1df 0xc7fff43003ffff07

def z946 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x198273c007fffe33 0xec6609cf001ffff8

def z947 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe7e38ff0f83e3fff 0xbf9f8e3fc3e0f8ff

def z948 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xf9e3f3f0f83e3fff 0xffe78fcfc3e0f8ff

def z949 : W := mkw 0x96009400a7402480 0x06580250029d0092 0xfe03fc00ffc03fef 0xf7f80ff003ff00ff

def z950 : W := mkw 0xfddb79ea18cf0f14 0x2bf76de7a8633c3c 0xf98271c039ce0e02 0x67e609c700e73838

def z951 : W := mkw 0x00008615021070ea 0x00000218540841c3 0x067d8e3f0631f1fd 0x9819f638fc18c7c7

def z952 : W := mkw 0xdffc208af5ad8000 0x477ff0822bd6b600 0xfffc000fffffc01f 0xc7fff0003fffff00

def z953 : W := mkw 0x2003004008020b00 0x00800c010020082c 0xe18301c0f80e3fe7 0xa7860c0703e038ff

def z954 : W := mkw 0xfddb69aa21850000 0x47f76da6a8861400 0xffffffff01c0003f 0x7bfffffffc070000

def z955 : W := mkw 0xdffc0130f5ad8070 0x677ff004c3d6b601 0xfffc0030ffffc01f 0xc7fff000c3ffff00

def z956 : W := mkw 0x49d821aa00000000 0x01276086a8000000 0x1fffffff0000003f 0x787ffffffc000000

def z957 : W := mkw 0xdffc688af5ad8000 0x477ff1a22bd6b600 0xfffeffcfffffc03f 0xfffffbff3fffff00

def z958 : W := mkw 0xfddb79aa39cd0d00 0x57f76de6a8e73434 0xf98271c039ce0e02 0x67e609c700e73838

def z959 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xff800000ffffc00f 0xc7fe000003ffff00

def z960 : W := mkw 0xfddb69aa08000900 0x03f76da6a8200024 0xffffffff38000e3f 0x7ffffffffce00038

def z961 : W := mkw 0x2003de440a527f8c 0x18800f79102949fe 0x0003fc0000003fe0 0x30000ff0000000ff

def z962 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffc023fffffc01f 0xcffff008ffffff00

def z963 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1982f3cc07fffe22 0xfc660bcf301ffff8

def z964 : W := mkw 0xbc93688800000000 0x02f24da220000000 0xffffffff0000003f 0x7bfffffffc000000

def z965 : W := mkw 0x49f023f850bf1274 0x2927c08fe142fc49 0x01e003f0003e0010 0x0807800fc000f800

def z966 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x19fef3ff07fffe3b 0xfc67fbcffc1ffff8

def z967 : W := mkw 0xdfd80000a5850000 0x077f600002961400 0xfffc0000ffffc01f 0xc7fff00003ffff00

def z968 : W := mkw 0x0890924002d73600 0x00224249000b5cd8 0x1992f3c007fffe3b 0xfc664bcf001ffff8

def z969 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xff83ffc0ffc03fff 0xfffe0fff03ff00ff

def z970 : W := mkw 0xfddb69aa00850000 0x03f76da6a8021400 0xffffffff003fc03f 0x7bfffffffc00ff00

def z971 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xf9fc0000ffffc012 0xc7e7f00003ffff00

def z972 : W := mkw 0x0890b2dd02d7766e 0x082242cb740b5dd9 0x1992f3ff07fffe3b 0xfc664bcffc1ffff8

def z973 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffe0000fffffe3f 0xe7fff80003fffff8

def z974 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xf8037000ffc03fe7 0xe7e00dc003ff00ff

def z975 : W := mkw 0x9e9cb48da7c5e48e 0x4e7a72d2369f1792 0x1e1cfc0f07c1c008 0x507873f03c1f0700

def z976 : W := mkw 0xdffc2088f5ad8000 0x477ff08223d6b600 0xffffffffffffc03f 0xffffffffffffff00

def z977 : W := mkw 0xb403d8000a402d00 0x02d00f60002900b4 0xfe03fc00ffc03fef 0xf7f80ff003ff00ff

def z978 : W := mkw 0x49f823fe50bf527c 0x2927e08ff942fd49 0x01fc03ff003fc010 0x0807f00ffc00ff00

def z979 : W := mkw 0xddf8000071ad0000 0x4777e00001c6b400 0xf9f00000ffffc01f 0xc7e7c00003ffff00

def z980 : W := mkw 0xdfd80000b58d0000 0x477f600002d63400 0xff900000ffffc01f 0xc7fe400003ffff00

def z981 : W := mkw 0x0890b2dc02d7766c 0x082242cb700b5dd9 0x1993f3fc07fffffb 0xfc664fcff01fffff

def z982 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffffffff00003e3f 0xfffffffffc0000f8

def z983 : W := mkw 0x02249655c672f6ee 0x080892595719cbdb 0x00000000c631ffc0 0x800000000318c7ff

def z984 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe037c00ffc03fc6 0xe7f80df003ff00ff

def z985 : W := mkw 0x2003fedd0a527fee 0x18800ffb742949ff 0x0003ffff00003fe0 0x38000ffffc0000ff

def z986 : W := mkw 0xdff00000f5ad0000 0x077fc00003d6b400 0xfff00000ffffc01f 0xc7ffc00003ffff00

def z987 : W := mkw 0xddd869aa00000000 0x037761a6a8000000 0x1ffeffff0000003b 0x787ffbfffc000000

def z988 : W := mkw 0x02249655eff7ffee 0x1c08925957bfdfff 0x00000000ffffffc0 0x8400000003ffffff

def z989 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffc8c0fffffc01f 0xd7fff2303fffff00

def z990 : W := mkw 0xdffc0411f5ad80e2 0x477ff01047d6b603 0xfffc0000ffffc1df 0xc7fff00003ffff07

def z991 : W := mkw 0x02249655ff7afffa 0x3408925957fdebff 0x00000000ffffffc0 0x8400000003ffffff

def z992 : W := mkw 0x0890b2cc02d7760c 0x082242cb300b5dd8 0x1993ffff07fffe3b 0xfc664ffffc1ffff8

def z993 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xf9e00000ffffc017 0xc7e7800003ffff00

def z994 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe027000ffc03fcf 0xe7f809c003ff00ff

def z995 : W := mkw 0x0890b6dd02d776ee 0x082242db740b5ddb 0x1992f3cc07fffffb 0xfc664bcf301fffff

def z996 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e103f0f83e3fd4 0x8f87840fc3e0f8ff

def z997 : W := mkw 0xddd80000318d0000 0x4777600000c63400 0xf98000003fffc002 0xc7e6000000ffff00

def z998 : W := mkw 0x02248615e730f0ea 0x04089218579cc3c3 0x067d8e3ffff1f1fd 0x9c19f638ffffc7c7

def z999 : W := mkw 0xfddb69aa21000000 0x07f76da6a8840000 0xffffffff39c0003f 0x7ffffffffce70000

def z1000 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe7ffc00ffc03fff 0xf7f9fff003ff00ff

def z1001 : W := mkw 0xdffc0411f5ad80e2 0x477ff01047d6b603 0xfffd8e3fffffc1ff 0xdffff638ffffff07

def z1002 : W := mkw 0x41600250503a1260 0x010580094140e849 0xe1e303f0f83e3ff7 0xaf878c0fc3e0f8ff

def z1003 : W := mkw 0x089032cc00d7560c 0x082240cb30035d58 0x199273cc07ffce1b 0xec6649cf301fff38

def z1004 : W := mkw 0xb403d8002b402d00 0x16d00f6000ad00b4 0xf803f000ffc03fef 0xf7e00fc003ff00ff

def z1005 : W := mkw 0x02248655c632f2ea 0x000892195718cbcb 0x07fd8fffc63ff1fd 0x981ff63fff18ffc7

def z1006 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xffffffffc00031ff 0xfbffffffff0000c7

def z1007 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe18303f0f83e3fe2 0xaf860c0fc3e0f8ff

def z1008 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x07fd8e3fc63ff1ff 0x9c1ff638ff18ffc7

def z1009 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1e201c0f83e3fd7 0xa787880703e0f8ff

def z1010 : W := mkw 0x41600250583a1b70 0x210580094160e86d 0xe1e203c0f83e3ff7 0xaf87880f03e0f8ff

def z1011 : W := mkw 0x089022c800971200 0x0022408b20025c48 0x1992f3cc07fffe3b 0xfc664bcf301ffff8

def z1012 : W := mkw 0xdffc688af5ad8000 0x477ff1a22bd6b600 0xfffc7000ffffc01f 0xc7fff1c003ffff00

def z1013 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d8e3fc601f1ec 0x1819f638ff1807c7

def z1014 : W := mkw 0x02248655c632f2ea 0x000892195718cbcb 0x067f8fffc631fffd 0xb819fe3fff18c7ff

def z1015 : W := mkw 0xd7640000f5ad8000 0x475d900003d6b600 0xffe00000ffffc01f 0xc7ff800003ffff00

def z1016 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe1f303f0fe3fffff 0xaf87cc0fc3f8ffff

def z1017 : W := mkw 0xb603dc00af402d80 0x16d80f7002bd00b6 0xfe13fe0cffc03fff 0xfff84ff833ff00ff

def z1018 : W := mkw 0xb40369aa00000000 0x02d00da6a8000000 0xfe7fffff0000003f 0x7bf9fffffc000000

def z1019 : W := mkw 0x02240615c430d0ea 0x000890185710c343 0x067d0e3fc031f1f5 0x8819f438ff00c7c7

def z1020 : W := mkw 0x0898b2ce02d7760c 0x082262cb380b5dd8 0x199ef3cf07fffe3b 0xfc667bcf3c1ffff8

def z1021 : W := mkw 0x02240210c4309060 0x000890084310c241 0x067d8e3fc631f1fd 0x9819f638ff18c7c7

def z1022 : W := mkw 0xdffc2088f5ad8000 0x477ff08223d6b600 0xfffe71c0ffffc01f 0xe7fff9c703ffff00

def z1023 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffd0230ffffc03f 0xcffff408c3ffff00

def z1024 : W := mkw 0x69db69aa00000000 0x01a76da6a8000000 0x07ffffff0000003d 0x381ffffffc000000

def z1025 : W := mkw 0x2003dc000a402d80 0x10800f70002900b6 0xf803fc00ffc03fef 0xf7e00ff003ff00ff

def z1026 : W := mkw 0x02248615f738f0ea 0x4408921857dce3c3 0x067d8e3ffe31f1fd 0x9819f638fff8c7c7

def z1027 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffc820cffffc03f 0xdffff20833ffff00

def z1028 : W := mkw 0x02248615c630f0ea 0x000892185718c3c3 0x067d8e3fc031f1f4 0x1819f638ff00c7c7

def z1029 : W := mkw 0x61630370583a1b70 0x21858c0dc160e86d 0xe7ff03f0f83e3fff 0xaf9ffc0fc3e0f8ff

def z1030 : W := mkw 0xf543492000000000 0x03d50d2480000000 0xffffffff0000003f 0x7bfffffffc000000

def z1031 : W := mkw 0xf7674d31fd2889f2 0x37dd9d34c7f4a227 0xe66d0c33f80001c4 0x0399b430cfe00007

def z1032 : W := mkw 0xb603dc05af406d8a 0x16d80f7016bd01b6 0xfe03fc0fffc03fef 0xf7f80ff03fff00ff

def z1033 : W := mkw 0x43640000f5ad8000 0x450d900003d6b600 0xe0600000ffffc004 0x8781800003ffff00

def z1034 : W := mkw 0xf54b69aa00000000 0x03d52da6a8000000 0xe67fffff0000003d 0x3b99fffffc000000

def z1035 : W := mkw 0x02248415c620e0ea 0x0008921057188383 0x067d8c3fc631c1dd 0x9019f630ff18c707

def z1036 : W := mkw 0xfddb69aa00850000 0x03f76da6a8021400 0xffffffff07c1c03f 0x7bfffffffc1f0700

def z1037 : W := mkw 0xb607dc05af40ed8a 0x16d81f7016bd03b6 0xfe7ffe3fffc1ffff 0xfff9fff8ffff07ff

def z1038 : W := mkw 0xb607dc01af40ad82 0x16d81f7006bd02b6 0xfe0ffc03ffc03fef 0xf7f83ff00fff00ff

def z1039 : W := mkw 0xfddb69aa00000000 0x03f76da6a8000000 0xfffffffff800003f 0xffffffffffe00000

def z1040 : W := mkw 0xb607dc00af40ad80 0x16d81f7002bd02b6 0xfe1ffc00ffc1ffef 0xf7f87ff003ff07ff

def z1041 : W := mkw 0xdffc0000f5ad8000 0x477ff00003d6b600 0xfffd8c00ffffc03f 0xd7fff63003ffff00

def z1042 : W := mkw 0x02248655c632f2ea 0x000892195718cbcb 0x067d8e3fc63ffffd 0x9c19f638ff18ffff

def z1043 : W := mkw 0x02249655c672f6ea 0x000892595719cbdb 0x1fffffffc7ffffff 0xfc7fffffff1fffff

def z1044 : W := mkw 0x02248615d638f0ea 0x000892185758e3c3 0x067d8e3ffe3ff1fd 0x9c19f638fff8ffc7

def z1045 : W := mkw 0xf76f4932fd288970 0x67ddbd24cbf4a225 0xe66d0c33f80001c4 0x0399b430cfe00007

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z6]),(0,[z10,z1,z2,z3,z4,z11,z6])],[(0,[z12,z1,z2,z3,z4,z5,z13]),(0,[z1,z3,z4,z14,z5,z15,z6]),(0,[z1,z2,z3,z16,z5,z6,z17])],[(0,[z1,z18,z2,z3,z4,z5,z6])],[(0,[z1,z2,z19,z3,z4,z5,z6]),(0,[z20,z2,z3,z4,z5,z6,z21]),(0,[z1,z2,z3,z4,z5,z22,z23]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z25,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z6])],[(0,[z1,z2,z3,z4,z5,z28,z6]),(0,[z29,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z31,z6]),(0,[z1,z2,z3,z4,z5,z32,z6]),(0,[z1,z2,z33,z3,z4,z5,z6]),(0,[z1,z2,z34,z3,z4,z5,z6]),(0,[z1,z2,z3,z35,z4,z5,z6])],[(0,[z1,z2,z3,z4,z36,z5,z6]),(1,[z37,z38,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z39,z5,z6]),(0,[z1,z2,z3,z4,z5,z40,z6]),(1,[z30,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z1,z2,z43,z3,z44,z4,z6]),(0,[z1,z2,z3,z4,z5,z45,z6]),(0,[z10,z1,z2,z46,z3,z4,z6])],[(1,[z47,z2,z48,z4,z5,z6]),(1,[z1,z2,z3,z49,z5,z6]),(0,[z50,z1,z2,z3,z4,z5,z22]),(0,[z51,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z52,z6]),(0,[z1,z53,z2,z43,z3,z4,z6]),(0,[z54,z1,z2,z3,z16,z4,z6]),(0,[z1,z2,z3,z4,z55,z5,z6]),(0,[z1,z2,z43,z3,z4,z6,z23])]],
   [[(0,[z10,z1,z2,z3,z4,z31,z6]),(0,[z12,z1,z2,z3,z4,z5,z23]),(0,[z1,z2,z56,z3,z4,z5,z57]),(0,[z1,z58,z2,z3,z4,z5,z6])],[(0,[z59,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z64,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z1,z2,z68,z3,z5,z6,z69])],[(0,[z1,z38,z2,z3,z4,z5,z6]),(0,[z38,z2,z60,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z31,z6]),(0,[z1,z2,z3,z4,z71,z5,z6]),(0,[z1,z2,z3,z4,z72,z5,z6]),(0,[z1,z73,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z74,z6])],[],[(0,[z75,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z5,z69])],[(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z77,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z78,z6]),(0,[z1,z2,z3,z4,z5,z6,z79])],[(0,[z1,z2,z80,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z81,z6]),(0,[z1,z2,z82,z3,z4,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z83]),(1,[z1,z2,z84,z4,z5,z85])],[(0,[z1,z2,z3,z4,z86,z5,z6]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z6,z23]),(0,[z88,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z89,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6])],[],[(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z2,z93,z3,z4,z5,z6]),(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z95]),(0,[z10,z1,z2,z46,z3,z4,z5])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z96,z97,z4,z5,z6]),(1,[z1,z98,z3,z4,z5,z6]),(0,[z20,z1,z2,z99,z4,z5,z6]),(0,[z1,z2,z3,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z6]),(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z104,z6]),(0,[z54,z1,z2,z3,z4,z31,z6]),(0,[z1,z105,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z16,z6,z17])],[(0,[z1,z2,z56,z3,z4,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z6])],[(0,[z47,z2,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z106,z5,z6,z69]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z108]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z110,z6]),(1,[z24,z1,z2,z25,z4,z5]),(0,[z1,z2,z111,z3,z4,z5,z6])],[(0,[z1,z2,z3,z112,z5,z6,z69]),(0,[z1,z113,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z96,z4,z5,z6,z85]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z115]),(1,[z20,z2,z3,z4,z5,z21]),(0,[z116,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z117,z6]),(0,[z1,z2,z3,z4,z5,z118,z6]),(0,[z1,z119,z2,z56,z3,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z121]),(0,[z1,z2,z122,z3,z4,z5,z6]),(0,[z1,z2,z123,z124,z3,z4,z6])],[(0,[z1,z2,z3,z4,z112,z5,z6]),(0,[z50,z12,z1,z2,z3,z4,z5]),(0,[z1,z2,z125,z3,z4,z5,z6]),(0,[z1,z2,z126,z3,z4,z5,z6]),(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z6]),(0,[z1,z2,z3,z129,z4,z5,z6]),(0,[z1,z2,z68,z3,z130,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z131])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z13,z6,z21]),(0,[z1,z134,z2,z3,z4,z5,z6]),(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z1,z2,z136,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z137,z5,z6])],[(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z23])],[(1,[z141,z2,z96,z4,z5,z6]),(0,[z1,z142,z2,z3,z4,z5,z6]),(0,[z1,z2,z143,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z144,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z145])]],
   [[(0,[z37,z1,z2,z3,z4,z146,z6])],[(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z3,z4,z14,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z22])],[(0,[z50,z1,z38,z3,z4,z5,z6]),(0,[z1,z2,z3,z149,z4,z5,z6])],[(0,[z20,z1,z150,z3,z4,z5,z6]),(0,[z151,z1,z2,z3,z152,z5,z6])],[],[(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z154,z1,z2,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z142,z2,z156,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z157,z6]),(0,[z1,z2,z3,z4,z158,z5,z6])],[(0,[z1,z2,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z160,z6])],[(0,[z1,z161,z2,z60,z3,z4,z5]),(0,[z1,z2,z3,z4,z162,z5,z6]),(0,[z1,z2,z3,z163,z4,z5,z6]),(0,[z1,z164,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z5,z6,z165]),(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z167,z4,z5,z6])]],
   [[(1,[z1,z2,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z168]),(0,[z1,z2,z3,z4,z169,z5,z6]),(0,[z1,z2,z3,z170,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z171,z6]),(0,[z1,z2,z3,z4,z5,z6,z172]),(0,[z1,z2,z3,z4,z173,z5,z6]),(0,[z174,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z175,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z176,z6]),(0,[z1,z2,z177,z3,z4,z5,z6]),(0,[z1,z2,z178,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z179,z5,z6])],[(0,[z180,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z170,z4,z6]),(1,[z1,z2,z3,z4,z5,z181]),(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z183,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z69])],[(0,[z1,z2,z3,z4,z5,z184,z6]),(0,[z1,z2,z3,z4,z5,z6,z185]),(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z1,z2,z3,z4,z5,z186,z6]),(0,[z187,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z53,z3,z4,z5,z6])],[(0,[z188,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z189,z5,z6]),(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z191,z3,z4,z5,z6])],[(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z1,z2,z25,z4,z5,z6,z85]),(1,[z1,z2,z3,z130,z5,z69])],[(0,[z1,z2,z3,z193,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z17])]],
   [[(0,[z1,z38,z3,z4,z14,z5,z6]),(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z1,z2,z197,z4,z152,z5,z6]),(0,[z1,z2,z3,z198,z4,z5,z6])],[(0,[z1,z2,z3,z96,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z6]),(1,[z200,z1,z201,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z6]),(0,[z1,z2,z203,z43,z4,z5,z6])],[(0,[z1,z2,z3,z204,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z78,z6])],[(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z1,z206,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z68,z3,z5,z6]),(0,[z1,z2,z46,z3,z4,z11,z5]),(0,[z1,z2,z3,z4,z5,z207,z6])],[(0,[z1,z2,z3,z4,z31,z6,z23]),(0,[z1,z2,z208,z3,z4,z5,z6]),(0,[z1,z2,z3,z209,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z5,z181]),(0,[z1,z2,z3,z210,z4,z5,z6])],[(1,[z1,z161,z2,z3,z4,z5]),(0,[z37,z1,z2,z3,z4,z211,z6]),(0,[z1,z2,z3,z170,z4,z152,z6]),(0,[z1,z2,z3,z212,z4,z5,z6])],[(0,[z1,z213,z2,z3,z4,z5,z6]),(0,[z214,z1,z2,z3,z4,z5,z6])],[(0,[z1,z215,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z216,z4,z5,z6]),(0,[z217,z1,z2,z3,z4,z5,z6]),(0,[z218,z1,z2,z3,z4,z5,z6])],[(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z1,z2,z221,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z14,z5,z6]),(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z223,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z225])],[(0,[z1,z2,z3,z4,z226,z5,z6]),(0,[z1,z2,z33,z3,z97,z5,z6]),(0,[z227,z1,z2,z3,z4,z5,z6])],[(0,[z2,z60,z3,z96,z4,z5,z6]),(0,[z20,z1,z2,z228,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z230,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(1,[z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z234,z4,z5,z6])],[(0,[z1,z2,z235,z3,z4,z5,z6]),(0,[z236,z1,z2,z3,z4,z5,z6]),(0,[z237,z1,z2,z3,z4,z5,z6])],[(0,[z238,z1,z2,z3,z4,z5,z6]),(0,[z239,z1,z2,z3,z4,z5,z6]),(0,[z1,z240,z2,z3,z4,z5,z6]),(0,[z241,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z59,z1,z38,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z235,z3,z4,z41,z5]),(0,[z1,z2,z243,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z244,z5,z6])],[(0,[z141,z2,z3,z96,z4,z5,z6]),(0,[z1,z156,z3,z201,z4,z5,z6]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z4,z5,z6]),(1,[z51,z1,z2,z68,z3,z5])],[(0,[z1,z2,z3,z4,z247,z5,z6])],[(0,[z1,z248,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z249,z4,z5,z6]),(0,[z1,z2,z3,z250,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z251,z6]),(1,[z54,z1,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z5,z6,z252])],[(0,[z30,z253,z2,z3,z4,z5,z6]),(0,[z254,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z128,z5])],[(0,[z1,z2,z3,z4,z5,z255,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z257,z2,z3,z4,z112,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z259,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z23])],[(0,[z47,z1,z2,z48,z4,z5,z6]),(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z261,z5,z6]),(0,[z1,z2,z262,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z5,z6])],[(0,[z1,z263,z2,z60,z3,z4,z5]),(0,[z47,z1,z2,z96,z4,z5,z6]),(0,[z1,z2,z3,z264,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z265,z6])]],
   [[(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z267,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z21]),(0,[z1,z2,z3,z4,z5,z268,z6])],[(1,[z1,z2,z3,z269,z5,z6]),(0,[z1,z2,z3,z4,z5,z270,z6]),(0,[z1,z2,z271,z3,z4,z5,z6])],[(0,[z20,z1,z2,z3,z4,z5,z21]),(0,[z10,z1,z2,z43,z3,z4,z6])],[(0,[z1,z2,z272,z3,z4,z5,z6]),(1,[z1,z2,z273,z3,z4,z6]),(0,[z1,z2,z273,z3,z4,z5,z6]),(0,[z274,z1,z2,z3,z4,z5,z6])],[(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z48,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z276,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z277,z5,z6]),(0,[z1,z2,z56,z3,z97,z5,z6])],[(0,[z1,z2,z3,z4,z278,z5,z6]),(0,[z24,z1,z2,z96,z4,z5,z6]),(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z2,z3,z280,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z15,z6]),(0,[z24,z1,z2,z3,z4,z5,z85])],[(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z5,z6]),(0,[z200,z113,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z282,z4,z5,z6]),(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z203,z3,z4,z6,z165])],[(0,[z1,z2,z3,z4,z5,z284,z6]),(1,[z257,z2,z3,z112,z5,z6]),(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z286,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z5,z6]),(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z130,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z1,z2,z3,z4,z5,z6,z290]),(0,[z1,z2,z3,z291,z4,z5,z6])],[(0,[z292,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z293]),(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z295,z3,z4,z5,z6])],[(0,[z59,z37,z2,z3,z4,z5,z6]),(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z1,z297,z3,z4,z5,z6,z22])],[(0,[z1,z2,z3,z4,z298,z5,z6]),(0,[z151,z1,z2,z56,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z299]),(0,[z1,z2,z300,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6])],[(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z43,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z305])],[(0,[z1,z2,z3,z4,z5,z306,z6]),(0,[z1,z2,z56,z3,z5,z307,z6])]],
   [[(0,[z308,z1,z2,z3,z4,z5,z6]),(1,[z253,z2,z3,z4,z31,z6]),(0,[z1,z2,z309,z3,z4,z5,z6]),(0,[z1,z2,z273,z3,z4,z152,z6]),(0,[z24,z1,z2,z3,z25,z4,z5]),(0,[z1,z2,z310,z3,z4,z5,z6]),(0,[z1,z2,z68,z3,z4,z311,z6])],[(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z313]),(0,[z1,z2,z3,z314,z4,z5,z6]),(0,[z1,z2,z315,z3,z4,z5,z6])],[(0,[z1,z53,z60,z3,z4,z5,z6]),(0,[z200,z316,z2,z3,z4,z5,z6])],[(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z317]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z50,z1,z3,z4,z5,z83,z6]),(0,[z319,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z320]),(0,[z321,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z322,z3,z4,z5,z6]),(0,[z323,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z68,z3,z4,z5])],[(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z324,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z1,z2,z325,z3,z4,z5,z6])],[(0,[z1,z2,z56,z48,z4,z5,z6]),(0,[z326,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z185]),(0,[z1,z2,z3,z328,z4,z5,z6])],[(0,[z1,z2,z56,z96,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z329]),(0,[z1,z2,z124,z3,z5,z6,z17]),(0,[z1,z2,z3,z330,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z331,z5,z6])],[(0,[z1,z2,z3,z4,z5,z332,z6]),(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z334,z6]),(0,[z1,z2,z335,z3,z4,z5,z6]),(0,[z1,z2,z124,z3,z4,z5,z6]),(0,[z336,z1,z2,z3,z4,z5,z6])],[(0,[z154,z257,z2,z3,z4,z5,z6]),(0,[z20,z50,z1,z2,z3,z4,z5]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z338,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z339]),(0,[z1,z2,z3,z4,z11,z5,z6])],[(1,[z59,z60,z3,z4,z5,z6]),(0,[z1,z2,z340,z3,z4,z5,z6])],[(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z2,z342,z3,z4,z5,z6]),(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z344,z1,z2,z3,z4,z5,z6]),(0,[z345,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z346,z5,z6]),(0,[z154,z1,z2,z3,z106,z5,z6]),(0,[z1,z2,z3,z347,z4,z5,z6]),(0,[z1,z2,z3,z44,z4,z5,z6])],[(0,[z1,z348,z2,z3,z4,z5,z6]),(0,[z1,z2,z349,z3,z4,z5,z6]),(0,[z1,z2,z350,z3,z4,z5,z6]),(0,[z1,z2,z351,z3,z4,z5,z6]),(0,[z1,z2,z203,z3,z4,z5,z6])],[(0,[z37,z1,z38,z3,z4,z5,z6]),(0,[z1,z2,z352,z3,z4,z5,z6]),(0,[z1,z2,z3,z353,z4,z5,z6]),(0,[z1,z2,z354,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z355]),(0,[z1,z2,z3,z4,z5,z6,z356]),(0,[z1,z2,z357,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z358,z6]),(0,[z1,z2,z3,z359,z4,z5,z6]),(0,[z200,z1,z2,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z360,z5,z6]),(0,[z361,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z362,z3,z4,z5,z6]),(0,[z1,z2,z363,z3,z4,z5,z6]),(0,[z1,z2,z364,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z365]),(0,[z1,z2,z366,z3,z4,z5,z6]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z46,z3,z4,z6,z23])],[(0,[z1,z60,z3,z4,z14,z5,z6]),(0,[z1,z368,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z369,z6]),(0,[z1,z2,z3,z4,z5,z370,z6]),(0,[z151,z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z371,z5,z6]),(0,[z1,z2,z372,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z373,z5,z6])],[(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z375,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z376,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z377]),(0,[z1,z2,z3,z4,z5,z6,z378]),(0,[z1,z2,z99,z3,z4,z5,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z51,z1,z2,z3,z130,z5,z6])],[(0,[z379,z1,z2,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z200,z1,z2,z201,z4,z5,z6]),(0,[z1,z2,z381,z3,z4,z5,z6]),(1,[z1,z2,z366,z3,z4,z6]),(0,[z1,z382,z2,z3,z4,z5,z6])],[(0,[z383,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z384,z5,z6]),(0,[z20,z1,z2,z3,z49,z5,z6]),(0,[z385,z1,z2,z3,z4,z5,z6]),(0,[z1,z53,z3,z4,z5,z15,z6]),(0,[z1,z2,z366,z3,z25,z4,z6])],[(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z56,z33,z4,z5,z6]),(1,[z1,z2,z3,z4,z311,z6])]],
   [[(0,[z1,z387,z2,z3,z4,z5,z6]),(0,[z1,z388,z2,z3,z4,z5,z6]),(1,[z113,z2,z3,z4,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z390,z4,z5,z6]),(0,[z1,z2,z3,z391,z4,z5,z6]),(0,[z1,z2,z392,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z11,z23])],[(0,[z20,z1,z2,z46,z3,z4,z5])],[(1,[z1,z2,z393,z4,z5,z6]),(0,[z1,z2,z394,z3,z4,z5,z6])],[(1,[z1,z263,z2,z3,z4,z5]),(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z396,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z397,z4,z5,z6])],[(0,[z1,z398,z2,z3,z4,z5,z6]),(0,[z399,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z400,z3,z4,z5,z6]),(0,[z1,z2,z3,z130,z4,z5,z69])],[(0,[z1,z2,z3,z4,z5,z369,z6]),(0,[z1,z2,z3,z4,z401,z5,z6])],[(0,[z1,z2,z3,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z403,z6]),(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z405,z3,z4,z5,z6])],[(0,[z1,z2,z3,z406,z4,z5,z6]),(1,[z333,z2,z3,z4,z5,z6]),(1,[z1,z2,z33,z97,z5,z6]),(0,[z1,z2,z3,z4,z5,z407,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z408]),(0,[z1,z2,z409,z3,z4,z5,z6])],[(0,[z410,z1,z2,z3,z4,z5,z6]),(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z412,z4,z5,z6]),(0,[z1,z413,z2,z3,z4,z5,z6])],[(0,[z1,z2,z414,z3,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z5,z311,z6]),(0,[z1,z2,z3,z4,z415,z5,z6])],[(0,[z1,z2,z3,z416,z4,z5,z6]),(0,[z20,z1,z98,z3,z4,z5,z6]),(0,[z1,z2,z417,z3,z4,z5,z6]),(0,[z1,z2,z418,z3,z4,z5,z6])],[(0,[z257,z1,z2,z3,z106,z5,z6]),(0,[z419,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z420,z5,z6]),(1,[z316,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z421,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z57]),(0,[z1,z2,z3,z422,z4,z5,z6]),(0,[z1,z2,z423,z3,z4,z5,z6])],[(0,[z1,z263,z2,z3,z4,z5,z6])],[(0,[z1,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z424,z3,z4,z5,z6]),(0,[z200,z1,z142,z3,z4,z5,z6]),(0,[z425,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z426,z3,z4,z5,z6]),(0,[z427,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z428,z3,z4,z5,z6])]],
   [[(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z430]),(0,[z1,z2,z3,z4,z5,z6,z431]),(1,[z1,z297,z3,z4,z5,z22]),(0,[z1,z2,z432,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z433,z6])],[(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z434,z3,z4,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z436,z1,z2,z3,z4,z5,z6])],[(1,[z1,z260,z3,z4,z5,z6]),(0,[z1,z2,z437,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z146,z6]),(0,[z200,z1,z3,z201,z4,z5,z6]),(0,[z151,z1,z3,z4,z152,z5,z6]),(0,[z1,z2,z3,z4,z152,z5,z6]),(0,[z1,z2,z3,z16,z4,z6,z17]),(0,[z1,z2,z438,z3,z4,z5,z6])],[(0,[z20,z1,z297,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z21]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z1,z2,z3,z440,z4,z5,z6])],[(0,[z1,z2,z3,z441,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z442,z6]),(0,[z1,z2,z443,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z14,z6]),(0,[z1,z297,z2,z3,z4,z5,z83]),(0,[z1,z2,z444,z3,z4,z5,z6]),(0,[z1,z2,z445,z3,z4,z5,z6])],[(0,[z2,z48,z3,z96,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z446,z6]),(0,[z1,z2,z447,z3,z4,z5,z6])]],
   [[(0,[z30,z1,z260,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z448,z5,z6]),(0,[z1,z2,z3,z4,z5,z449,z6])],[(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z451,z5,z6]),(1,[z1,z2,z3,z4,z5,z185]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z33,z3,z5,z307,z6])],[(0,[z154,z1,z2,z3,z112,z5,z6]),(0,[z1,z2,z3,z452,z4,z5,z6]),(0,[z1,z2,z84,z4,z5,z6,z85])],[(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z454,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z97,z4,z5,z6])],[(0,[z1,z38,z3,z4,z5,z6,z22]),(0,[z455,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z85,z69]),(0,[z1,z2,z68,z3,z4,z5,z6]),(0,[z1,z2,z68,z3,z90,z4,z6])],[(0,[z1,z2,z48,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z14,z6,z23]),(0,[z456,z1,z2,z3,z4,z5,z6]),(1,[z50,z1,z3,z4,z5,z83]),(0,[z1,z2,z457,z3,z4,z5,z6])],[(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(0,[z1,z2,z460,z3,z4,z5,z6]),(0,[z154,z1,z2,z461,z4,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z463,z1,z2,z3,z4,z5,z6])],[(0,[z20,z1,z2,z3,z4,z369,z6])]],
   [[(0,[z200,z1,z2,z56,z4,z5,z6]),(0,[z1,z53,z2,z123,z3,z4,z6]),(0,[z10,z1,z2,z3,z4,z15,z6]),(0,[z1,z2,z3,z4,z5,z6,z464]),(0,[z1,z2,z123,z3,z16,z5,z6]),(0,[z10,z1,z2,z123,z3,z4,z6])],[(0,[z154,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z465,z4,z5,z6]),(1,[z1,z2,z235,z3,z4,z5]),(0,[z1,z53,z2,z3,z4,z5,z446]),(0,[z1,z2,z3,z4,z5,z466,z6])],[(0,[z1,z2,z48,z4,z5,z6,z85]),(0,[z1,z2,z3,z4,z5,z15,z6])],[(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z1,z2,z197,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z6]),(1,[z1,z2,z203,z44,z4,z6]),(0,[z1,z2,z469,z3,z4,z5,z6])],[(1,[z1,z2,z3,z470,z5,z6]),(0,[z1,z471,z2,z3,z4,z5,z6])],[(0,[z1,z2,z202,z3,z201,z5,z6]),(0,[z1,z2,z472,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z22]),(0,[z1,z2,z473,z3,z4,z5,z6]),(0,[z1,z2,z3,z474,z4,z5,z6])],[(0,[z1,z2,z475,z3,z4,z5,z6]),(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z1,z2,z3,z478,z4,z5,z6])],[(0,[z1,z2,z56,z3,z106,z5,z6]),(0,[z1,z2,z3,z479,z4,z5,z6]),(0,[z1,z53,z2,z203,z3,z4,z6]),(0,[z1,z2,z480,z3,z4,z5,z6])]],
   [[(0,[z1,z481,z2,z3,z4,z5,z6]),(0,[z1,z2,z482,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z211,z6]),(0,[z1,z2,z3,z106,z4,z5,z6]),(0,[z483,z1,z2,z3,z4,z5,z6]),(0,[z1,z297,z2,z3,z4,z5,z22]),(1,[z1,z2,z43,z4,z6,z165])],[(0,[z1,z2,z3,z484,z4,z5,z6]),(0,[z1,z2,z485,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z6,z23]),(0,[z486,z1,z2,z3,z4,z5,z6])],[(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z43,z3,z4,z6,z165]),(0,[z1,z2,z123,z3,z4,z6,z17]),(0,[z1,z2,z488,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z489,z6]),(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z491,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z15,z6]),(0,[z54,z1,z2,z123,z3,z4,z6]),(0,[z1,z2,z492,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z493,z6])],[(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z4,z5,z6,z495]),(0,[z496,z1,z2,z3,z4,z5,z6])],[(0,[z497,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z97,z4,z5,z307,z6]),(0,[z1,z2,z3,z4,z5,z6,z498])],[(0,[z1,z2,z499,z3,z4,z5,z6])]],
   [[],[(0,[z257,z1,z2,z3,z112,z5,z6]),(0,[z1,z53,z2,z3,z4,z41,z6]),(0,[z1,z2,z156,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6])],[(0,[z1,z2,z3,z4,z5,z6,z501]),(0,[z1,z2,z3,z4,z502,z5,z6]),(0,[z503,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z504,z3,z4,z5,z6]),(0,[z1,z505,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z211,z6]),(0,[z253,z1,z2,z3,z4,z41,z6]),(0,[z30,z1,z506,z3,z4,z5,z6]),(0,[z1,z2,z243,z3,z201,z5,z6]),(0,[z1,z2,z507,z3,z4,z5,z6]),(0,[z151,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z508,z3,z4,z5,z6])],[(0,[z1,z2,z509,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z510]),(0,[z1,z2,z3,z4,z5,z6,z511]),(0,[z1,z2,z43,z4,z5,z6,z165]),(1,[z1,z2,z3,z4,z512,z6]),(0,[z1,z2,z3,z513,z4,z5,z6]),(1,[z10,z1,z2,z46,z3,z4])],[(0,[z1,z2,z3,z4,z514,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z515]),(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z362,z3,z201,z4,z6]),(0,[z1,z2,z3,z517,z4,z5,z6]),(0,[z1,z2,z3,z4,z518,z5,z6])],[(0,[z1,z2,z3,z4,z519,z5,z6]),(0,[z1,z119,z2,z33,z3,z5,z6]),(0,[z1,z2,z520,z3,z4,z5,z6]),(0,[z1,z2,z521,z3,z4,z5,z6]),(0,[z1,z2,z522,z3,z4,z5,z6])]],
   [[(0,[z50,z1,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z523,z4,z5,z6]),(0,[z1,z2,z393,z4,z152,z5,z6])],[(0,[z1,z2,z524,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z525]),(0,[z1,z2,z3,z4,z5,z6,z526])],[(0,[z1,z2,z527,z3,z4,z5,z6]),(0,[z1,z528,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z529,z4,z5,z6])],[(0,[z47,z1,z2,z3,z470,z5,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z99,z4,z5,z6]),(0,[z1,z2,z531,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z23])],[(0,[z532,z1,z2,z3,z4,z5,z6]),(0,[z154,z2,z3,z106,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z533]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z1,z53,z2,z3,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6])],[(0,[z1,z142,z156,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z536])],[(0,[z1,z2,z3,z4,z5,z537,z6]),(0,[z1,z2,z3,z4,z5,z6,z69])],[(1,[z154,z2,z3,z106,z5,z6]),(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z539,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z540])]],
   [[(0,[z1,z2,z3,z4,z5,z541,z6]),(0,[z50,z1,z2,z3,z4,z5,z83]),(0,[z1,z2,z3,z542,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z512,z6]),(0,[z1,z2,z124,z3,z16,z4,z6])],[(0,[z1,z2,z543,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z269,z5,z6]),(0,[z1,z2,z123,z3,z4,z6,z23])],[(0,[z1,z2,z3,z4,z5,z6,z544]),(0,[z1,z2,z545,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z546]),(0,[z1,z2,z547,z3,z4,z5,z6]),(0,[z12,z1,z2,z46,z3,z4,z5]),(0,[z1,z2,z3,z548,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z549]),(0,[z1,z2,z550,z3,z4,z5,z6])],[(0,[z1,z2,z551,z3,z4,z5,z6]),(0,[z1,z2,z3,z552,z4,z5,z6]),(0,[z1,z2,z43,z3,z4,z5,z6]),(0,[z1,z553,z2,z3,z4,z5,z6])],[(0,[z233,z1,z2,z3,z4,z5,z6])],[(0,[z554,z1,z2,z3,z4,z5,z6]),(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z556]),(0,[z1,z557,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z558,z6]),(0,[z1,z2,z3,z4,z5,z6,z559]),(0,[z1,z2,z3,z393,z4,z5,z6]),(0,[z1,z2,z56,z3,z4,z128,z5]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z2,z3,z4,z11,z6,z23])],[(0,[z141,z47,z2,z3,z4,z5,z6]),(0,[z257,z1,z2,z3,z4,z5,z6]),(0,[z1,z119,z3,z560,z4,z5,z6]),(0,[z1,z2,z561,z3,z4,z5,z6])]],
   [[(0,[z562,z1,z2,z3,z4,z5,z6]),(1,[z1,z53,z3,z4,z15,z6]),(0,[z1,z2,z3,z4,z15,z6,z23]),(0,[z1,z2,z203,z3,z44,z4,z6])],[],[(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z203,z3,z4,z6,z23])],[(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z6]),(0,[z1,z2,z3,z565,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z566])],[(0,[z37,z38,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z567,z6]),(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z570,z5,z6])],[(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z571,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z14,z6]),(0,[z1,z572,z2,z3,z4,z5,z6])],[(0,[z1,z2,z573,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6]),(0,[z1,z119,z2,z3,z560,z5,z6]),(0,[z1,z2,z3,z575,z4,z5,z6]),(0,[z1,z2,z3,z576,z4,z5,z6])],[(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z1,z2,z3,z578,z4,z5,z6]),(0,[z1,z2,z3,z4,z579,z5,z6]),(0,[z1,z2,z3,z4,z5,z580,z6])]],
   [[(0,[z20,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z581,z3,z4,z5,z6])],[(0,[z582,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z583,z4,z5,z6]),(0,[z584,z1,z2,z3,z4,z5,z6])],[(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z142,z2,z97,z4,z5,z6])],[(0,[z200,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z298,z5,z6]),(0,[z1,z2,z586,z3,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z31,z6]),(0,[z1,z2,z3,z587,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z588,z6])],[(0,[z59,z1,z60,z3,z4,z5,z6]),(0,[z1,z60,z3,z4,z5,z6,z22]),(0,[z12,z1,z297,z2,z3,z4,z5])],[(0,[z1,z2,z3,z589,z4,z5,z6]),(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z5,z23])]],
   [[(0,[z253,z1,z2,z3,z4,z31,z6]),(0,[z1,z142,z2,z201,z4,z5,z6])],[(0,[z1,z2,z33,z3,z106,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z591])],[(0,[z592,z1,z2,z3,z4,z5,z6]),(0,[z200,z1,z2,z156,z4,z5,z6]),(0,[z1,z2,z3,z593,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z594,z6])],[(0,[z51,z1,z2,z3,z106,z5,z6]),(0,[z1,z2,z272,z3,z201,z4,z6]),(1,[z1,z2,z3,z4,z5,z446]),(0,[z50,z1,z297,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z595])],[(0,[z1,z2,z596,z3,z4,z5,z6]),(0,[z1,z2,z506,z3,z4,z5,z6]),(0,[z1,z2,z597,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z598,z6]),(0,[z1,z2,z3,z130,z5,z6,z69]),(0,[z1,z2,z599,z3,z4,z5,z6])],[(0,[z37,z2,z3,z4,z112,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z600]),(0,[z1,z2,z3,z601,z4,z5,z6]),(0,[z1,z3,z560,z4,z152,z5,z6]),(0,[z602,z1,z2,z3,z4,z5,z6]),(0,[z603,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z181]),(0,[z1,z297,z2,z3,z4,z604,z6]),(0,[z1,z3,z4,z5,z83,z6,z22]),(0,[z1,z605,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z606,z4,z5,z6])],[(0,[z1,z2,z607,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z609,z2,z3,z4,z5,z6]),(0,[z1,z610,z2,z3,z4,z5,z6]),(0,[z1,z2,z611,z3,z4,z5,z6])]],
   [[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z612,z4,z5,z6]),(0,[z151,z1,z2,z3,z4,z5,z6]),(0,[z1,z613,z2,z3,z4,z5,z6]),(0,[z1,z297,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z1,z2,z3,z615,z4,z5,z6]),(0,[z1,z2,z3,z616,z4,z5,z6])],[(0,[z1,z2,z617,z3,z4,z5,z6])],[(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z201,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z85]),(0,[z619,z1,z2,z3,z4,z5,z6])],[(0,[z1,z53,z38,z3,z4,z5,z6]),(0,[z620,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z461,z4,z5,z6]),(1,[z1,z2,z228,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z621])],[(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z1,z2,z3,z461,z4,z5,z6]),(0,[z1,z2,z3,z228,z4,z5,z6]),(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z1,z2,z3,z622,z4,z5,z6]),(0,[z1,z2,z623,z3,z4,z5,z6])],[(0,[z30,z2,z3,z4,z41,z5,z6]),(0,[z1,z2,z68,z3,z4,z5,z85])],[(0,[z1,z2,z3,z4,z269,z5,z6]),(0,[z1,z2,z3,z4,z624,z5,z6]),(0,[z1,z2,z3,z4,z5,z625,z6]),(0,[z1,z2,z3,z626,z4,z5,z6])]],
   [[],[(0,[z627,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z272,z3,z4,z6]),(0,[z1,z119,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z57]),(0,[z1,z2,z3,z4,z5,z6,z165]),(0,[z1,z2,z3,z628,z4,z5,z6])],[(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z154,z37,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z41,z5,z31,z6]),(0,[z1,z630,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z203,z3,z4,z6]),(0,[z1,z631,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z632,z4,z5,z6]),(0,[z1,z633,z2,z3,z4,z5,z6])],[(0,[z47,z1,z2,z3,z298,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z634]),(0,[z1,z2,z3,z4,z5,z635,z6]),(0,[z1,z2,z3,z636,z4,z5,z6]),(0,[z1,z2,z3,z4,z637,z5,z6])],[(0,[z1,z2,z3,z638,z4,z5,z6]),(0,[z1,z2,z3,z639,z4,z5,z6]),(0,[z1,z2,z3,z640,z4,z5,z6])],[(0,[z641,z1,z2,z3,z4,z5,z6]),(0,[z20,z12,z2,z3,z4,z5,z6]),(1,[z151,z1,z3,z152,z5,z6]),(0,[z1,z2,z3,z4,z5,z642,z6]),(0,[z1,z2,z3,z4,z604,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z643]),(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z645,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z243,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z646,z4,z5,z6]),(0,[z1,z2,z647,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z648]),(0,[z649,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z650,z3,z4,z5,z6]),(0,[z151,z1,z2,z33,z3,z5,z6]),(0,[z1,z2,z84,z3,z4,z5,z6]),(0,[z24,z1,z2,z84,z4,z5,z6]),(0,[z1,z2,z68,z3,z25,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z651]),(0,[z1,z652,z2,z3,z4,z5,z6])],[(1,[z1,z506,z3,z4,z5,z6]),(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z362,z3,z4,z6]),(0,[z655,z1,z2,z3,z4,z5,z6])],[(0,[z2,z60,z3,z4,z112,z5,z6]),(0,[z37,z2,z3,z96,z4,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z297,z2,z3,z4,z32,z6])],[(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z1,z2,z3,z4,z5,z6,z658]),(1,[z1,z2,z3,z4,z604,z6]),(0,[z1,z2,z56,z4,z5,z307,z6]),(0,[z1,z2,z3,z659,z4,z5,z6]),(0,[z1,z2,z203,z44,z4,z5,z6]),(0,[z1,z2,z660,z3,z4,z5,z6]),(0,[z1,z2,z661,z3,z4,z5,z6])],[(0,[z2,z3,z106,z4,z112,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6]),(0,[z141,z1,z2,z48,z4,z5,z6]),(0,[z54,z1,z2,z203,z3,z4,z6]),(1,[z1,z2,z3,z90,z4,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z141,z1,z2,z96,z4,z5,z6]),(1,[z1,z2,z202,z3,z5,z6]),(0,[z1,z663,z2,z3,z4,z5,z6]),(1,[z1,z119,z3,z560,z5,z6]),(0,[z1,z664,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z665]),(0,[z1,z2,z150,z3,z4,z5,z6]),(1,[z12,z2,z3,z4,z5,z13]),(0,[z1,z2,z84,z3,z4,z5,z85])],[(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z253,z2,z3,z4,z5,z31,z6]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z1,z119,z2,z3,z152,z5,z6]),(0,[z1,z2,z3,z25,z4,z512,z6])],[(1,[z1,z2,z197,z4,z5,z6])],[(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z12,z2,z3,z4,z5,z13,z6]),(0,[z1,z142,z2,z56,z4,z5,z6]),(0,[z1,z2,z667,z3,z4,z5,z6]),(0,[z1,z2,z33,z97,z4,z5,z6])],[(0,[z151,z1,z119,z3,z4,z5,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z669,z5,z6])],[(0,[z37,z1,z60,z3,z4,z5,z6]),(0,[z1,z670,z2,z3,z4,z5,z6]),(0,[z1,z98,z2,z3,z4,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z23]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z673])],[(0,[z47,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z33,z3,z112,z5,z6]),(0,[z316,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z674,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z675,z5,z6]),(0,[z1,z2,z3,z676,z4,z5,z6]),(0,[z1,z2,z677,z3,z4,z5,z6]),(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z51,z1,z2,z3,z112,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z680]),(0,[z54,z1,z2,z3,z4,z41,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z560,z4,z5,z6])],[(0,[z1,z2,z681,z3,z4,z5,z6])],[(0,[z1,z2,z682,z3,z4,z5,z6]),(0,[z1,z2,z84,z3,z25,z4,z5]),(0,[z1,z2,z683,z3,z4,z5,z6])],[(0,[z47,z37,z2,z3,z4,z5,z6]),(1,[z1,z2,z56,z5,z307,z6]),(1,[z1,z2,z123,z124,z3,z6])],[(0,[z1,z2,z3,z684,z4,z5,z6]),(0,[z1,z2,z685,z3,z4,z5,z6])],[(0,[z1,z2,z686,z3,z4,z5,z6]),(0,[z1,z687,z2,z3,z4,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6])],[(0,[z689,z1,z2,z3,z4,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z151,z1,z2,z3,z560,z5,z6]),(0,[z1,z2,z3,z691,z4,z5,z6]),(0,[z692,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z693,z5,z6]),(0,[z1,z2,z3,z694,z4,z5,z6]),(1,[z1,z2,z3,z4,z32,z6])],[(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z695,z6])],[(0,[z1,z2,z3,z4,z696,z5,z6]),(0,[z1,z2,z3,z4,z697,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z1,z53,z2,z3,z16,z4,z6]),(0,[z10,z1,z2,z3,z16,z4,z6]),(0,[z1,z2,z3,z4,z5,z698,z6])],[],[(0,[z47,z1,z2,z3,z4,z5,z6]),(0,[z1,z699,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z700,z5,z6]),(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z702,z3,z4,z5,z6])],[(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z704,z4,z5,z6]),(1,[z1,z150,z3,z4,z5,z6]),(0,[z1,z2,z123,z124,z3,z5,z6])],[(0,[z1,z2,z56,z3,z112,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z706,z1,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z20,z2,z3,z4,z369,z21]),(0,[z1,z2,z272,z3,z4,z6]),(0,[z1,z2,z707,z3,z4,z6]),(0,[z1,z53,z122,z3,z4,z6]),(0,[z708,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z57]),(0,[z1,z2,z709,z4,z5,z6])],[(0,[z154,z2,z461,z106,z5,z6]),(0,[z1,z2,z124,z3,z710,z6])],[(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z713,z3,z4,z5,z6]),(0,[z1,z2,z3,z106,z5,z57]),(0,[z1,z150,z3,z49,z5,z6]),(0,[z1,z2,z123,z3,z462,z6]),(0,[z1,z3,z4,z5,z714,z6]),(0,[z1,z2,z44,z4,z715,z6]),(0,[z1,z2,z716,z3,z4,z5]),(0,[z51,z1,z2,z716,z3,z5]),(0,[z1,z717,z3,z4,z5,z6])],[(0,[z1,z2,z3,z718,z5,z6]),(0,[z141,z2,z96,z4,z5,z6]),(0,[z655,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z4,z719,z6]),(1,[z1,z2,z4,z715,z6])]],
   [[(0,[z1,z2,z3,z4,z720,z6]),(0,[z1,z2,z3,z4,z41,z181]),(0,[z20,z2,z99,z4,z5,z21]),(0,[z1,z3,z4,z721,z15,z6]),(0,[z1,z2,z722,z4,z5,z6]),(0,[z1,z2,z3,z4,z715,z6]),(0,[z1,z2,z84,z723,z4,z5]),(0,[z1,z2,z3,z710,z6,z17])],[(0,[z1,z2,z3,z724,z5,z6]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z2,z96,z470,z5,z6]),(0,[z1,z2,z726,z3,z4,z6]),(0,[z51,z1,z2,z650,z3,z5]),(0,[z1,z150,z46,z3,z4,z5]),(0,[z151,z1,z3,z152,z5,z6])],[(0,[z1,z727,z3,z4,z5,z6]),(0,[z1,z2,z48,z4,z5,z57]),(0,[z1,z728,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z2,z3,z730,z5,z6]),(0,[z1,z2,z731,z4,z5,z6])],[(0,[z1,z732,z3,z4,z5,z6]),(0,[z1,z2,z733,z4,z5,z6]),(0,[z1,z2,z3,z734,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z735,z6]),(0,[z47,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z150,z3,z269,z5,z6]),(0,[z151,z1,z273,z3,z152,z6]),(0,[z737,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z68,z3,z311])],[(0,[z1,z2,z3,z4,z738,z6]),(0,[z1,z2,z739,z4,z5,z6]),(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z741,z3,z4,z5,z6]),(0,[z1,z150,z3,z4,z78,z6]),(0,[z151,z1,z197,z152,z5,z6]),(0,[z742,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z743,z5,z6]),(0,[z1,z2,z744,z4,z5,z6]),(0,[z701,z2,z3,z4,z31,z6]),(0,[z1,z2,z33,z92,z5,z6])],[(0,[z1,z745,z3,z4,z5,z6]),(0,[z12,z2,z3,z4,z5,z746]),(0,[z1,z2,z3,z4,z5,z747]),(0,[z54,z1,z3,z4,z721,z6]),(0,[z1,z2,z192,z46,z3,z4])]],
   [[(0,[z47,z2,z48,z298,z5,z6]),(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z3,z4,z749,z6])],[(0,[z554,z2,z96,z4,z5,z6]),(0,[z1,z2,z750,z3,z5,z6]),(0,[z1,z2,z751,z3,z4,z6]),(0,[z1,z2,z3,z752,z4,z5]),(0,[z1,z2,z753,z4,z5,z6]),(0,[z1,z2,z3,z754,z4,z6]),(0,[z1,z2,z3,z755,z5,z6])],[(0,[z427,z2,z96,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z756]),(0,[z1,z2,z202,z3,z5,z6]),(0,[z1,z119,z3,z560,z5,z6]),(0,[z1,z2,z56,z523,z5,z6]),(0,[z1,z2,z757,z4,z5,z6]),(0,[z1,z2,z56,z5,z307,z57]),(0,[z758,z2,z3,z4,z5,z6])],[(0,[z59,z161,z60,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z12,z2,z3,z4,z5,z13]),(0,[z760,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z170,z4,z6]),(0,[z1,z761,z3,z4,z5,z6]),(1,[z1,z2,z762,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z2,z764,z4,z5,z6]),(0,[z1,z3,z765,z4,z5,z6]),(0,[z1,z2,z3,z4,z766,z6]),(0,[z1,z2,z767,z3,z4,z6]),(0,[z1,z2,z768,z4,z5,z6])],[(0,[z1,z2,z3,z4,z769,z6]),(0,[z1,z2,z3,z4,z770,z6]),(0,[z1,z2,z771,z4,z5,z6]),(0,[z1,z2,z3,z772,z5,z6]),(0,[z1,z2,z197,z4,z5,z6]),(0,[z151,z1,z393,z152,z5,z6]),(0,[z1,z2,z773,z4,z5,z6])],[(0,[z1,z53,z3,z4,z255,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z775,z4,z5,z6]),(0,[z200,z1,z243,z201,z5,z6]),(0,[z776,z2,z3,z4,z5,z6]),(1,[z1,z2,z777,z3,z4])],[(0,[z50,z1,z3,z4,z5,z332]),(0,[z1,z2,z46,z3,z4,z78]),(0,[z1,z2,z778,z4,z5,z6])]],
   [[(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z2,z3,z4,z780,z6]),(0,[z274,z2,z3,z112,z5,z6]),(0,[z20,z150,z3,z4,z5,z21]),(0,[z1,z2,z3,z4,z781,z6]),(0,[z782,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z783,z6]),(0,[z1,z784,z3,z4,z5,z6])],[(0,[z1,z2,z785,z4,z5,z6]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z200,z1,z201,z4,z5,z6]),(0,[z1,z2,z3,z787,z5,z6]),(0,[z200,z1,z362,z201,z4,z6]),(0,[z1,z2,z3,z4,z5,z788]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z23]),(0,[z10,z1,z2,z3,z529,z4])],[(0,[z1,z2,z3,z790,z4,z6]),(0,[z1,z297,z150,z3,z4,z5]),(0,[z791,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z792,z5,z6]),(1,[z1,z2,z3,z710,z6]),(0,[z1,z2,z3,z4,z311,z6])],[(0,[z1,z2,z3,z793,z5,z6]),(0,[z1,z2,z794,z3,z4,z5]),(0,[z37,z795,z3,z4,z5,z6]),(0,[z1,z2,z3,z269,z78,z6]),(0,[z1,z2,z796,z4,z5,z6]),(0,[z1,z652,z3,z4,z14,z6]),(0,[z1,z2,z3,z710,z16,z6]),(0,[z1,z2,z3,z4,z11,z23])]],
   [[(0,[z154,z2,z3,z629,z5,z6]),(0,[z1,z2,z3,z797,z5,z6]),(0,[z154,z2,z61,z106,z5,z6]),(0,[z54,z1,z325,z3,z4,z6])],[(0,[z1,z161,z2,z3,z4,z5]),(0,[z1,z2,z393,z4,z5,z6]),(0,[z1,z2,z56,z762,z5,z6]),(0,[z1,z2,z46,z777,z3,z4])],[(0,[z1,z2,z3,z4,z5,z798]),(0,[z1,z263,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z32]),(0,[z1,z2,z3,z4,z799,z6])],[(0,[z1,z2,z3,z4,z451,z23]),(0,[z1,z2,z235,z3,z4,z78]),(0,[z1,z2,z228,z49,z5,z6]),(0,[z200,z1,z765,z4,z5,z6]),(0,[z1,z2,z56,z5,z307,z6]),(0,[z1,z2,z123,z124,z3,z6])]],
   [[(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z2,z202,z362,z3,z6]),(0,[z1,z630,z2,z56,z5,z6]),(0,[z1,z2,z3,z801,z5,z6])],[(0,[z1,z2,z802,z4,z5,z6]),(0,[z1,z2,z3,z4,z803,z6]),(0,[z54,z1,z3,z4,z71,z6]),(0,[z1,z98,z3,z269,z5,z6]),(0,[z1,z2,z97,z331,z5,z6]),(0,[z2,z3,z4,z5,z6,z804])],[(0,[z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z150,z3,z4,z5,z23]),(0,[z200,z1,z2,z202,z5,z6]),(0,[z1,z2,z806,z4,z5,z6]),(0,[z1,z119,z3,z807,z5,z6])],[(0,[z1,z2,z3,z4,z808,z5]),(0,[z1,z260,z3,z4,z41,z6]),(0,[z809,z2,z3,z4,z5,z6]),(0,[z810,z2,z3,z4,z5,z6]),(0,[z1,z119,z354,z3,z5,z6]),(0,[z1,z2,z3,z811,z4,z6]),(0,[z24,z1,z2,z366,z25,z4]),(0,[z1,z2,z3,z710,z4,z6])]],
   [[(0,[z1,z795,z3,z4,z5,z6]),(0,[z1,z2,z812,z3,z4,z5]),(0,[z113,z2,z56,z4,z5,z6]),(0,[z813,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z6]),(0,[z1,z2,z3,z4,z137,z23])],[(0,[z476,z60,z3,z4,z5,z6]),(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z2,z56,z5,z567,z6]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z2,z362,z243,z3,z6]),(0,[z816,z2,z3,z4,z5,z6])],[(0,[z1,z2,z817,z4,z5,z6]),(0,[z1,z2,z3,z4,z818,z6]),(0,[z344,z2,z96,z4,z5,z6]),(0,[z619,z2,z3,z106,z5,z6]),(0,[z1,z2,z228,z4,z78,z6]),(0,[z20,z2,z3,z269,z5,z21]),(0,[z1,z2,z3,z4,z819,z6]),(0,[z236,z1,z2,z56,z5,z6])],[(0,[z1,z2,z820,z3,z5,z6]),(0,[z1,z2,z80,z4,z5,z85]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z20,z2,z3,z4,z78,z21]),(0,[z1,z3,z560,z807,z5,z6])]],
   [[(0,[z1,z2,z823,z4,z5,z6]),(0,[z1,z2,z235,z3,z4,z23]),(0,[z1,z2,z3,z4,z824,z6]),(0,[z1,z53,z3,z4,z15,z181]),(0,[z51,z1,z2,z68,z3,z90])],[(0,[z825,z2,z3,z4,z5,z6]),(1,[z1,z2,z723,z4,z5]),(0,[z1,z2,z392,z4,z5,z85]),(0,[z1,z3,z4,z5,z826,z6]),(0,[z51,z1,z2,z68,z3,z5])],[(1,[z2,z3,z4,z827,z6]),(0,[z1,z2,z828,z3,z4,z6]),(0,[z1,z3,z4,z807,z5,z6]),(0,[z1,z2,z3,z723,z4,z5]),(0,[z1,z2,z25,z723,z4,z5]),(0,[z829,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z112,z5,z57]),(0,[z1,z830,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z3,z832,z4,z6]),(0,[z1,z297,z3,z4,z5,z22]),(0,[z1,z2,z762,z5,z307,z6]),(0,[z1,z2,z33,z762,z5,z6])]],
   [[(0,[z1,z2,z833,z4,z5,z6]),(0,[z1,z2,z3,z4,z31,z181]),(0,[z1,z98,z228,z4,z5,z6]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z56,z128,z5,z307]),(0,[z835,z2,z3,z4,z5,z6])],[(0,[z1,z2,z836,z4,z5,z6]),(0,[z2,z60,z461,z4,z5,z6]),(0,[z1,z837,z3,z4,z5,z6]),(0,[z2,z3,z838,z112,z5,z6]),(0,[z1,z2,z3,z839,z4,z6]),(0,[z1,z2,z3,z4,z5,z840])],[(0,[z1,z260,z3,z4,z5,z6]),(0,[z1,z841,z3,z4,z5,z6]),(0,[z1,z2,z842,z3,z4,z6]),(0,[z1,z2,z3,z843,z4,z6]),(0,[z1,z2,z3,z4,z107,z23]),(0,[z1,z2,z3,z4,z844,z5])],[(0,[z1,z2,z3,z4,z146,z6]),(0,[z1,z2,z777,z3,z4,z6])]],
   [[(0,[z1,z845,z3,z4,z5,z6]),(0,[z1,z2,z846,z3,z4,z6]),(0,[z30,z2,z3,z4,z41,z6]),(0,[z2,z3,z4,z5,z746,z21]),(0,[z1,z2,z847,z3,z4,z6]),(0,[z1,z2,z848,z3,z5,z6]),(0,[z1,z2,z56,z5,z265,z6])],[(0,[z1,z2,z849,z3,z4,z5]),(0,[z1,z161,z2,z3,z4,z850]),(0,[z47,z2,z48,z4,z5,z6]),(0,[z1,z2,z3,z49,z5,z6]),(0,[z20,z2,z228,z4,z5,z21]),(0,[z1,z2,z3,z4,z78,z23]),(0,[z1,z2,z851,z4,z5,z6]),(0,[z1,z2,z43,z3,z4,z181]),(0,[z852,z2,z3,z4,z5,z6]),(0,[z853,z2,z3,z4,z5,z6])],[(0,[z1,z854,z2,z3,z4,z5]),(0,[z1,z161,z150,z3,z4,z5]),(0,[z1,z2,z3,z4,z855,z5])],[(0,[z1,z2,z856,z4,z5,z6]),(0,[z37,z2,z461,z4,z5,z6]),(0,[z1,z857,z3,z4,z5,z6]),(0,[z1,z858,z3,z4,z5,z6]),(0,[z1,z2,z273,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z446]),(0,[z54,z1,z418,z3,z4,z6]),(0,[z2,z3,z4,z5,z6,z859])]],
   [[(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z2,z3,z4,z860,z6]),(0,[z861,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z862,z4,z5]),(0,[z1,z2,z863,z3,z5,z6]),(0,[z1,z864,z3,z4,z5,z6]),(0,[z253,z2,z3,z4,z827,z6]),(0,[z1,z2,z3,z49,z369,z6]),(0,[z20,z2,z3,z4,z5,z746]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z2,z3,z4,z866,z6]),(0,[z1,z2,z867,z3,z4,z6]),(0,[z868,z1,z3,z4,z5,z6]),(0,[z1,z2,z43,z103,z4,z6]),(0,[z1,z2,z68,z716,z3,z5])],[(0,[z1,z2,z3,z4,z869,z6]),(0,[z12,z2,z3,z4,z5,z498]),(0,[z200,z113,z201,z4,z5,z6]),(0,[z870,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z871,z5,z6]),(0,[z872,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z748,z22]),(0,[z1,z873,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z874,z6]),(0,[z1,z2,z875,z3,z4,z6]),(0,[z257,z2,z3,z112,z5,z6]),(0,[z1,z2,z876,z4,z5,z6]),(0,[z50,z1,z351,z3,z4,z5]),(0,[z1,z2,z877,z4,z5,z6]),(0,[z1,z53,z3,z210,z4,z6])]],
   [[(0,[z1,z2,z878,z4,z5,z6]),(0,[z1,z2,z56,z5,z284,z6]),(0,[z2,z3,z4,z5,z6,z746])],[(0,[z1,z2,z3,z4,z5,z879]),(0,[z1,z2,z3,z4,z880,z6]),(0,[z2,z881,z96,z4,z5,z6]),(0,[z1,z2,z3,z882,z5,z6]),(0,[z1,z2,z99,z269,z5,z6]),(0,[z1,z2,z3,z883,z5,z6]),(0,[z884,z1,z2,z3,z4,z6])],[(0,[z37,z388,z3,z4,z5,z6]),(0,[z655,z38,z3,z4,z5,z6]),(0,[z885,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z838,z5,z6]),(0,[z50,z1,z150,z3,z4,z5]),(0,[z886,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z371,z6]),(0,[z1,z2,z203,z102,z4,z6]),(0,[z1,z2,z723,z4,z5,z85])],[(0,[z1,z38,z3,z4,z5,z181]),(0,[z2,z3,z881,z4,z5,z6]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z1,z2,z888,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z2,z461,z4,z5,z6]),(0,[z1,z2,z3,z552,z5,z69]),(0,[z890,z2,z3,z4,z5,z6]),(0,[z151,z233,z3,z152,z5,z6]),(0,[z891,z2,z3,z4,z5,z6]),(0,[z1,z2,z777,z3,z4,z5])],[(0,[z2,z48,z881,z4,z5,z6]),(0,[z1,z2,z892,z4,z5,z6]),(0,[z1,z2,z3,z4,z721,z6]),(0,[z1,z2,z3,z4,z5,z893])],[(0,[z1,z98,z3,z4,z5,z6]),(0,[z1,z2,z794,z3,z4,z146]),(0,[z1,z2,z56,z301,z5,z6]),(0,[z1,z2,z202,z272,z3,z6]),(0,[z1,z2,z3,z894,z4,z6]),(0,[z1,z297,z3,z4,z32,z22]),(0,[z50,z1,z3,z4,z5,z748]),(0,[z1,z2,z3,z4,z128,z749]),(0,[z1,z2,z3,z895,z4,z6]),(0,[z10,z1,z2,z3,z4,z373]),(1,[z1,z2,z716,z3,z5])],[(0,[z1,z2,z3,z470,z5,z6]),(0,[z1,z2,z896,z3,z4,z6]),(0,[z897,z2,z3,z4,z5,z6]),(0,[z1,z2,z898,z3,z5,z6]),(0,[z1,z2,z3,z16,z6,z17])]],
   [[(0,[z1,z899,z3,z4,z5,z6]),(0,[z253,z2,z3,z4,z31,z6]),(0,[z1,z2,z765,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z900]),(0,[z1,z2,z203,z691,z4,z6]),(0,[z1,z901,z2,z3,z4,z6])],[(0,[z1,z60,z3,z4,z5,z181]),(0,[z1,z2,z3,z4,z5,z902]),(0,[z2,z3,z4,z827,z31,z6]),(0,[z1,z2,z203,z3,z4,z181]),(0,[z1,z18,z3,z4,z15,z6]),(0,[z24,z1,z2,z25,z4,z5]),(0,[z1,z903,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z904,z6]),(0,[z1,z2,z905,z3,z4,z6]),(0,[z1,z98,z3,z4,z369,z6]),(0,[z1,z2,z3,z4,z906,z6]),(0,[z907,z2,z3,z4,z5,z6])],[(0,[z2,z3,z838,z4,z5,z6]),(0,[z1,z2,z908,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z211,z6])],[(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z2,z910,z3,z4,z6]),(0,[z1,z2,z48,z470,z5,z6]),(0,[z1,z2,z911,z3,z4,z6])],[(0,[z2,z3,z106,z838,z5,z6]),(1,[z1,z3,z4,z5,z748])],[(0,[z1,z2,z3,z4,z912,z6]),(0,[z1,z260,z3,z4,z31,z6]),(0,[z2,z3,z4,z41,z827,z6]),(0,[z1,z2,z243,z3,z5,z6]),(0,[z1,z2,z4,z715,z6,z165]),(0,[z1,z2,z3,z913,z5,z6])]],
   [[(0,[z656,z2,z3,z112,z5,z6]),(0,[z411,z1,z3,z4,z14,z6]),(0,[z24,z1,z2,z149,z4,z5]),(0,[z1,z2,z914,z3,z5,z6]),(0,[z1,z53,z3,z4,z15,z446]),(0,[z884,z1,z2,z3,z4,z128]),(0,[z24,z1,z2,z723,z4,z5])],[(0,[z30,z2,z3,z4,z827,z6]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z1,z2,z3,z4,z915,z6])],[(0,[z1,z506,z3,z4,z5,z6]),(0,[z20,z2,z136,z3,z4,z5]),(0,[z1,z2,z3,z916,z5,z6]),(0,[z1,z2,z362,z3,z4,z6]),(0,[z1,z2,z3,z4,z917,z6]),(0,[z1,z2,z3,z710,z5,z6])],[(0,[z59,z60,z3,z4,z5,z6]),(1,[z2,z3,z838,z5,z6]),(0,[z151,z1,z2,z197,z5,z6]),(0,[z1,z2,z3,z4,z55,z23])]],
   [[(0,[z75,z2,z3,z106,z5,z6]),(0,[z1,z2,z3,z4,z918,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z604,z6])],[(0,[z1,z2,z545,z97,z5,z6]),(0,[z30,z260,z3,z4,z41,z6]),(1,[z2,z3,z4,z5,z746]),(0,[z1,z2,z920,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z921,z4,z6]),(0,[z37,z38,z3,z4,z146,z6]),(0,[z1,z2,z96,z4,z5,z57]),(0,[z1,z2,z170,z393,z4,z6]),(0,[z1,z2,z3,z90,z4,z6])],[(0,[z1,z922,z2,z3,z4,z5]),(0,[z1,z2,z923,z4,z5,z6]),(0,[z1,z2,z3,z924,z5,z6])]],
   [[(0,[z1,z2,z925,z3,z5,z6]),(0,[z283,z38,z3,z4,z5,z6]),(0,[z141,z2,z881,z4,z5,z6]),(0,[z75,z2,z48,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z926]),(0,[z1,z2,z3,z4,z512,z6]),(0,[z10,z1,z2,z46,z3,z4])],[(0,[z59,z263,z60,z3,z4,z5]),(0,[z1,z927,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z928,z6]),(0,[z1,z2,z929,z4,z5,z6]),(0,[z1,z2,z3,z762,z5,z6]),(0,[z1,z2,z3,z4,z930,z6]),(0,[z24,z1,z2,z25,z4,z512])],[(0,[z1,z931,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z369,z6]),(0,[z645,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z435,z5,z69])],[(0,[z1,z2,z61,z4,z5,z6]),(0,[z324,z2,z48,z4,z5,z6]),(0,[z1,z2,z932,z4,z5,z6]),(0,[z30,z2,z3,z4,z41,z185]),(0,[z200,z1,z272,z201,z4,z6]),(0,[z1,z2,z43,z4,z715,z6])]],
   [[(0,[z1,z2,z56,z5,z374,z6]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z150,z228,z4,z5,z6]),(0,[z1,z2,z3,z4,z934,z6]),(0,[z1,z2,z716,z3,z130,z5])],[(0,[z395,z60,z3,z4,z5,z6]),(0,[z1,z2,z61,z106,z5,z6]),(0,[z1,z2,z43,z583,z4,z6]),(0,[z1,z2,z366,z3,z4,z6])],[(0,[z1,z2,z99,z4,z5,z6]),(0,[z425,z2,z3,z112,z5,z6]),(0,[z1,z2,z935,z4,z5,z6]),(0,[z12,z528,z2,z3,z4,z5]),(0,[z936,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z181]),(0,[z1,z2,z937,z3,z4,z6]),(0,[z1,z2,z3,z938,z5,z6]),(0,[z1,z2,z939,z4,z5,z6])],[(0,[z1,z2,z940,z4,z5,z6]),(0,[z1,z2,z3,z4,z941,z5]),(0,[z1,z2,z942,z4,z5,z6]),(0,[z1,z38,z3,z4,z146,z6]),(0,[z1,z2,z3,z4,z5,z943]),(0,[z1,z2,z944,z4,z5,z6])]],
   [[(0,[z113,z2,z3,z4,z5,z6]),(0,[z456,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z49,z78,z6]),(0,[z1,z2,z3,z4,z624,z23])],[(0,[z1,z2,z3,z4,z945,z6]),(0,[z37,z398,z3,z4,z5,z6]),(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z2,z947,z4,z5,z6]),(0,[z20,z2,z480,z3,z4,z5]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z1,z2,z3,z130,z5,z69])],[(0,[z1,z2,z3,z949,z5,z6]),(0,[z154,z2,z3,z106,z5,z6]),(0,[z1,z2,z99,z4,z369,z6]),(0,[z2,z3,z4,z5,z6,z950]),(0,[z1,z2,z197,z170,z4,z6]),(0,[z951,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z83]),(0,[z1,z2,z3,z4,z952,z6]),(0,[z1,z2,z3,z4,z644,z23]),(0,[z1,z2,z123,z191,z3,z6])],[(0,[z1,z2,z953,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z2,z3,z4,z5,z13,z746])]],
   [[(0,[z258,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z827,z6]),(0,[z1,z2,z3,z4,z955,z6])],[(0,[z1,z60,z3,z4,z146,z6]),(0,[z1,z2,z956,z3,z4,z5]),(0,[z188,z2,z3,z4,z31,z6]),(0,[z1,z2,z3,z4,z957,z6]),(0,[z151,z1,z667,z3,z5,z6]),(0,[z1,z2,z660,z68,z3,z5]),(0,[z2,z3,z4,z5,z6,z958]),(0,[z1,z2,z716,z3,z5,z6])],[(0,[z38,z795,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z959,z6]),(0,[z1,z98,z3,z49,z5,z6]),(0,[z1,z2,z4,z762,z5,z6]),(0,[z1,z2,z611,z25,z4,z5])],[(0,[z1,z2,z3,z4,z146,z902]),(0,[z47,z2,z48,z470,z5,z6]),(0,[z1,z2,z3,z4,z5,z960]),(0,[z1,z2,z272,z243,z3,z6]),(0,[z1,z2,z961,z3,z4,z6]),(0,[z1,z2,z33,z97,z5,z6]),(0,[z1,z2,z4,z715,z5,z6]),(0,[z10,z1,z2,z777,z3,z4])]],
   [[(0,[z1,z2,z3,z4,z962,z6]),(0,[z200,z1,z667,z4,z5,z6])],[(0,[z2,z60,z3,z298,z5,z6]),(0,[z1,z2,z881,z4,z5,z6]),(0,[z1,z963,z3,z4,z5,z6]),(0,[z200,z1,z202,z201,z5,z6]),(0,[z1,z2,z3,z4,z14,z181]),(0,[z1,z297,z3,z4,z5,z748])],[(0,[z1,z2,z3,z4,z964,z5]),(0,[z1,z2,z965,z3,z5,z6]),(0,[z1,z966,z3,z4,z5,z6]),(0,[z1,z2,z228,z269,z5,z6]),(0,[z333,z2,z56,z3,z5,z6]),(0,[z1,z3,z807,z152,z5,z6]),(0,[z1,z2,z273,z393,z4,z6]),(0,[z1,z2,z3,z4,z967,z6]),(0,[z1,z2,z3,z16,z4,z181]),(0,[z1,z968,z3,z4,z5,z6])],[(0,[z37,z38,z3,z4,z211,z6]),(0,[z20,z2,z3,z49,z5,z21]),(0,[z1,z765,z201,z4,z5,z6]),(0,[z151,z333,z3,z152,z5,z6]),(0,[z1,z53,z3,z4,z15,z6]),(0,[z1,z3,z4,z14,z721,z6]),(0,[z10,z1,z2,z364,z3,z4]),(0,[z1,z2,z203,z4,z715,z6])]],
   [[(0,[z316,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z969,z5,z6]),(0,[z1,z2,z3,z4,z5,z970]),(0,[z1,z2,z3,z16,z158,z6])],[(0,[z1,z2,z3,z4,z971,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z98,z3,z4,z78,z6]),(0,[z1,z2,z3,z4,z973,z6])],[(0,[z1,z150,z3,z4,z5,z6]),(0,[z1,z2,z3,z974,z5,z6]),(0,[z1,z297,z3,z4,z604,z22])],[(0,[z795,z60,z3,z4,z5,z6]),(0,[z2,z795,z3,z4,z5,z6]),(0,[z1,z2,z975,z4,z5,z6]),(0,[z1,z161,z2,z3,z4,z976]),(0,[z37,z2,z3,z298,z5,z6]),(0,[z1,z2,z3,z977,z5,z6]),(0,[z1,z2,z978,z3,z5,z6]),(0,[z1,z3,z4,z721,z5,z6])]],
   [[(0,[z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z979,z6]),(0,[z1,z2,z3,z4,z980,z6]),(0,[z1,z981,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z983,z2,z3,z4,z5])],[(0,[z1,z2,z3,z984,z5,z6]),(0,[z30,z506,z3,z4,z41,z6]),(0,[z1,z18,z3,z4,z5,z22]),(0,[z1,z572,z3,z4,z5,z83])],[(0,[z1,z2,z985,z3,z4,z6]),(0,[z1,z150,z3,z4,z369,z6]),(0,[z1,z2,z3,z4,z986,z6]),(0,[z1,z2,z3,z4,z987,z5])],[(0,[z1,z988,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z989,z6]),(0,[z2,z3,z4,z827,z5,z6]),(0,[z1,z2,z777,z3,z4,z23])]],
   [[(0,[z1,z2,z3,z4,z990,z6]),(0,[z10,z1,z2,z235,z3,z4]),(0,[z151,z1,z3,z170,z152,z6]),(0,[z1,z2,z3,z4,z415,z23])],[(0,[z37,z38,z3,z4,z5,z6]),(0,[z1,z991,z2,z3,z4,z5]),(0,[z1,z992,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z22]),(0,[z1,z3,z4,z5,z748,z6])],[(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z3,z994,z5,z6]),(0,[z1,z995,z3,z4,z5,z6]),(0,[z1,z150,z99,z4,z5,z6]),(0,[z1,z2,z996,z4,z5,z6]),(0,[z151,z1,z3,z807,z5,z6]),(0,[z54,z1,z3,z4,z14,z6]),(0,[z1,z53,z3,z4,z721,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z998,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z128,z5]),(0,[z1,z2,z123,z3,z710,z6])]],
   [[(0,[z1,z2,z3,z298,z5,z6]),(0,[z1,z2,z3,z4,z5,z999]),(0,[z1,z2,z3,z1000,z5,z6]),(0,[z20,z98,z3,z4,z5,z21]),(0,[z200,z316,z201,z4,z5,z6]),(0,[z333,z2,z33,z3,z5,z6]),(0,[z1,z2,z3,z4,z1001,z6]),(0,[z1,z2,z723,z4,z5,z6])],[(0,[z1,z2,z1002,z4,z5,z6]),(0,[z1,z1003,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z185]),(0,[z1,z3,z4,z5,z83,z748])],[(1,[z795,z3,z4,z5,z6]),(0,[z1,z2,z3,z1004,z5,z6]),(1,[z2,z881,z4,z5,z6]),(0,[z1005,z2,z3,z4,z5,z6]),(0,[z1,z53,z3,z4,z89,z6])],[(0,[z59,z795,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1,z2,z1007,z4,z5,z6]),(0,[z30,z2,z235,z3,z4,z41]),(0,[z1008,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z721,z6])]],
   [[(0,[z1,z2,z3,z269,z5,z6]),(0,[z1,z2,z1009,z4,z5,z6]),(0,[z1,z2,z1010,z4,z5,z6])],[(0,[z1,z2,z3,z4,z78,z6]),(0,[z50,z1,z3,z4,z5,z83]),(0,[z1,z2,z97,z762,z5,z6]),(0,[z1,z1011,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z99,z49,z5,z6]),(0,[z1013,z2,z3,z4,z5,z6]),(0,[z1014,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1015,z6]),(0,[z1,z2,z84,z4,z5,z85])],[(0,[z1,z2,z1016,z4,z5,z6]),(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z2,z3,z1018,z4,z5]),(0,[z1019,z2,z3,z4,z5,z6]),(0,[z1,z2,z197,z273,z4,z6]),(0,[z1,z2,z3,z4,z15,z181]),(0,[z1,z2,z123,z3,z4,z181]),(0,[z1,z1020,z3,z4,z5,z6]),(0,[z1021,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1022,z6]),(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z1024,z4,z5]),(0,[z1,z2,z3,z269,z369,z6]),(0,[z1,z2,z1025,z3,z5,z6])],[(0,[z50,z1,z161,z3,z4,z5]),(0,[z1,z2,z235,z3,z4,z5]),(0,[z1026,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1027,z6]),(0,[z1,z2,z61,z112,z5,z6]),(0,[z1028,z2,z3,z4,z5,z6])],[(0,[z47,z2,z881,z4,z5,z6]),(0,[z1,z2,z1029,z4,z5,z6]),(0,[z1,z2,z203,z44,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z976,z6]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z257,z2,z3,z838,z5,z6]),(0,[z113,z2,z97,z4,z5,z6])],[(0,[z1,z53,z3,z4,z184,z6]),(0,[z1,z2,z99,z4,z78,z6]),(0,[z1,z142,z2,z202,z5,z6])],[(0,[z1,z3,z4,z5,z1031,z6]),(0,[z1,z2,z3,z1032,z5,z6]),(0,[z1,z2,z1033,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1034]),(0,[z1,z2,z228,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z746]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1036]),(1,[z1,z3,z807,z5,z6]),(0,[z1,z119,z2,z197,z5,z6]),(0,[z1,z2,z3,z1037,z5,z6])]],
   [[(0,[z1,z161,z3,z4,z5,z22]),(0,[z20,z2,z3,z4,z5,z21]),(0,[z1,z2,z777,z3,z4,z11])],[(0,[z1,z2,z33,z412,z5,z6]),(0,[z154,z2,z3,z838,z5,z6]),(0,[z1,z53,z3,z4,z196,z6]),(0,[z20,z1,z2,z3,z4,z32]),(0,[z1,z2,z43,z4,z6,z165])],[(0,[z1,z2,z3,z1038,z5,z6]),(0,[z1,z2,z3,z4,z5,z1039]),(0,[z1,z2,z716,z3,z5,z69])],[(0,[z1,z2,z3,z1040,z5,z6]),(0,[z1,z2,z3,z4,z1041,z6]),(0,[z1,z98,z99,z4,z5,z6]),(0,[z1,z2,z228,z4,z369,z6]),(0,[z1042,z2,z3,z4,z5,z6]),(0,[z1043,z2,z3,z4,z5,z6]),(0,[z1044,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1045,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 558) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 558).take 467) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1025)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [558, 467] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 95).take 33).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [95, 33] = true :=
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

end PEqualNP.Outside.L_meta_41372

theorem PEqualNP.Outside.L_meta_41372 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4241022976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4241022976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41372.solve