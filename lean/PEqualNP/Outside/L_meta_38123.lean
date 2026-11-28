import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38123

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
  Nat.testBit (4278124266 * 2 ^ 32 + 4277075080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0a8000424222c8a2#64 ++ 0xa054000212111645#64 ++ 0x774410c7c666c9ff#64 ++ 0x7bba20863e33364f#64 : BitVec 256),
   (0x4100211900890351#64 ++ 0x02080108c804481a#64 ++ 0xeee8633909990ffe#64 ++ 0xf7774319c84cc87f#64 : BitVec 256),
   (0x8201842e11e15185#64 ++ 0xc4100c21708f0a8c#64 ++ 0xddf38c3e31e1f195#64 ++ 0xeeef9c61f18f0f8c#64 : BitVec 256),
   (0x2c1c0ac02e00ac02#64 ++ 0x1960e05601700560#64 ++ 0xc3fc0fc03e01fe13#64 ++ 0xde1fe07e01f00ff0#64 : BitVec 256),
   (0x301ed0003d540004#64 ++ 0x1180f68001eaa000#64 ++ 0x3fdff0003ffe000f#64 ++ 0xc1feff8001fff000#64 : BitVec 256),
   (0xc01f7fb580000018#64 ++ 0x1e00fbfdac000000#64 ++ 0xffdfffffc0000000#64 ++ 0x3ffefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x02800002402240a0 0xa014000012011205 0x00000007c00001e0 0x200000003e00000f

def z1 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7c666c9ff 0x7bba20863e33364f

def z2 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03e01fe13 0xde1fe07e01f00ff0

def z3 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0003ffe000f 0xc1feff8001fff000

def z4 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee8633909990ffe 0xf7774319c84cc87f

def z5 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e31e1f195 0xeeef9c61f18f0f8c

def z6 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc0000000 0x3ffefffffe000000

def z7 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaee863380999060e 0xc5774319c04cc830

def z8 : W := mkw 0x8001042400000000 0x0400082120000000 0xddf38c3e3001f011 0xeeef9c61f1800f80

def z9 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc1f00fc03001fe11 0xde0f807e01800ff0

def z10 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x400000c7c666c9ff 0x7a0000063e33364f

def z11 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcce8633809990794 0xe6674319c04cc83c

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f00c003001f011 0xce0f806001800f80

def z13 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x360410c7c66609ee 0x31b020863e33304f

def z14 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x400000c7c000c9f0 0x3a0000063e00064f

def z15 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x089be00039980000 0x8044df0001ccc000

def z16 : W := mkw 0x3c1edac03f54ac06 0x19e0f6d601faa560 0xffffffc03ffffe1f 0xdffffffe01fffff0

def z17 : W := mkw 0x711ef1193ddd0355 0x1388f788c9eee81a 0xfffff3393fff0fff 0xf7ffff99c9fff87f

def z18 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc0200fc00001fe10 0x1e01007e00000ff0

def z19 : W := mkw 0xed1f7ffdae89af5b 0x1f68fbffed744d7a 0xffffffffff99ffff 0xfffffffffffccfff

def z20 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xfffffc003ffff01f 0xcfffffe001ffff80

def z21 : W := mkw 0x4100211900890351 0x02080108c804481a 0xc020033900010ff0 0x36010019c800087f

def z22 : W := mkw 0x0a8080425362c8a6 0xa0540402129b1645 0x7fd790c7f7e6c9ff 0xfbfebc863fbf364f

def z23 : W := mkw 0x02800002402240a0 0xa014000012011205 0x34001007c06601ec 0x21a000803e03300f

def z24 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0xf7fc1fc7fe67ffff 0xffbfe0fe3ff33fff

def z25 : W := mkw 0x7d1efbd93fddaf57 0x1be8f7dec9feed7a 0xfffffff93fffffff 0xffffffffc9ffffff

def z26 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7f41cc7f667f9ff 0xffbfa0e63fb33fcf

def z27 : W := mkw 0xa41d8eac3dc13505 0x5d20ec7561ee09a8 0x88bb8f3839813600 0x8445dc79c1cc09b0

def z28 : W := mkw 0x0000000800810101 0x0000000040040808 0xcce0003801810194 0xe6670001c00c080c

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d00c0000000000 0x0e0e806000000000

def z30 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0xe3fc7fc03e1ffe1b 0xdf1fe3fe01f0fff0

def z31 : W := mkw 0x0100000800890341 0x000800004004481a 0x0020000009990ffe 0xc0010000004cc87f

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x4240000000000812 0x5212000000000040

def z33 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0x83fc0f003e013603 0xc41fe07801f009b0

def z34 : W := mkw 0x3a9ed0427f76c8a6 0xb1d4f68213fbb645 0x3fdff0c6fffec00f 0xc9feff8637fff600

def z35 : W := mkw 0x0880004042028822 0x2044000202101441 0x220410c1c606086a 0x111020860e303043

def z36 : W := mkw 0x8a81846e53e3d9a7 0xe4540c23729f1ecd 0xfff79cfff7e7f9ff 0xffffbce7ffbf3fcf

def z37 : W := mkw 0x9203d42e11f55185 0xc4901ea1708faa8c 0xfdf3fc3e31fff19d 0xefef9fe1f18fff8c

def z38 : W := mkw 0xc81f7ff58200881a 0x1e40fbffac100440 0xffdfffffc600c813 0x7ffefffffe300640

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x220000010000086a 0x1110000008000043

def z40 : W := mkw 0x49802151420a8a72 0x224c010a8a105453 0x220c73c1ce1e0e6a 0x1110639e0e70f073

def z41 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0x11179cc6c0000000 0x0888bce636000000

def z42 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x889bef3800000000 0x0444df79c0000000

def z43 : W := mkw 0x3a8080427f76c8a6 0xa1d4040213fbb645 0x774410c7fffec9ff 0xfbba20863ffff64f

def z44 : W := mkw 0x02800002402240a0 0xa014000012011205 0x10001006c0660000 0x0080008036033000

def z45 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0xbfffff003fff360f 0xc5fffff801fff9b0

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x6640000100000000 0x3332000008000000

def z47 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xe3fc1fc1fe07fe7b 0xdf1fe0fe0ff03ff3

def z48 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdffb8f3e39e1ff97 0xfeffdc79f1cf0ffc

def z49 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7ec13c7ce67cfff 0xffbf609e3e733e7f

def z50 : W := mkw 0xc1012fbd80890359 0x0e08097dec04481a 0xc0200fffc0010ff0 0x3e01007ffe00087f

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x66400001000009fe 0x733200000800004f

def z52 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0xffec73ffcfffcfff 0xffff639ffe7ffe7f

def z53 : W := mkw 0x8a81846e53e3d9a7 0xe4540c23729f1ecd 0xddf38c3e37e7f9ff 0xeeef9c61f1bf3fcf

def z54 : W := mkw 0x201c00002c000000 0x1100e00001600000 0x03dc00003e000003 0xc01ee00001f00000

def z55 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0xfc03ffffc0000000 0x3fe01ffffe000000

def z56 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2ec86039099801ee 0xe1764301c84cc00f

def z57 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xfffff3003fff0e1f 0xd7ffff9801fff870

def z58 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0x3fdffcc6c0000000 0x09feffe636000000

def z59 : W := mkw 0x821fd42e11e15185 0xd410fea1708f0a8c 0xfffffc3e31e1f195 0xefffffe1f18f0f8c

def z60 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1dd7900037e60005 0xc0eebc8001bf3000

def z61 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xddf38c3e39f9ffff 0xeeef9c61f1cfcfff

def z62 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x110410c6c666c001 0x0888208636333600

def z63 : W := mkw 0x8a81846e53e3d9a7 0xe4540c23729f1ecd 0xddf38cfff1e1f9f5 0xfeef9c67ff8f0fcf

def z64 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc00009fe 0x7ffefffffe00004f

def z65 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdc238c3e01e1f194 0x2ee11c61f00f0f8c

def z66 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x220c70000e1e000a 0x011063800070f000

def z67 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xc9f38c383181f011 0xce4f9c61c18c0f80

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x264000000000000e 0x4132000000000000

def z69 : W := mkw 0x1002500000140000 0x008012800000a000 0x20007000001e0008 0x010003800000f000

def z70 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x350410c7c666c1ed 0x29a820863e33360f

def z71 : W := mkw 0x311ed0083ddd0345 0x1188f68041eee81a 0x3ffff0003fff0fff 0xc1ffff8001fff87f

def z72 : W := mkw 0xba9fd46e7ff7d9a7 0xf5d4fea373ffbecd 0xfffffcfffffff9ff 0xffffffe7ffffffcf

def z73 : W := mkw 0x0000000800810101 0x0000000040040808 0xcee8033809810f96 0xf6774019c04c087c

def z74 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0xc3dc0fc000000000 0x1e1ee07e00000000

def z75 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0x002000003e01fe13 0xc001000001f00ff0

def z76 : W := mkw 0xec1f7ff5ae00ac1a 0x1f60fbffad700560 0xfffffffffe01fe13 0xfffffffffff00ff0

def z77 : W := mkw 0xb01fdea4bd54000c 0x1d80fef525eaa000 0x11179cc6f6660001 0x0888bce637b33000

def z78 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc666000f 0x7ffefffffe333000

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x774410c7c0000000 0x3bba20863e000000

def z80 : W := mkw 0xca9f7ff7c222c8ba 0xbe54fbffbe111645 0xffdfffffc666c9ff 0x7ffefffffe33364f

def z81 : W := mkw 0x4100211900890351 0x02080108c804481a 0xec20633901990ffc 0x37610319c80cc87f

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2e8030008010e12 0xd617401800400870

def z83 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x01140cc03600f001 0x0808a06601b00780

def z84 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xffdffffffe000003 0xfffefffffff00000

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x0344000006000003 0x401a200000300000

def z86 : W := mkw 0x8a81846e53e3d9a7 0xe4540c23729f1ecd 0xddf79cfef7e7f195 0xeeefbce7f7bf3f8c

def z87 : W := mkw 0x8001042400000000 0x0400082120000000 0xffd79cffc0000000 0x3ffebce7fe000000

def z88 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3c03f00001fe000c 0x01e01f80000ff000

def z89 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0x3c03f03fc0000000 0x21e01f81fe000000

def z90 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0xc02003ffc001cff0 0x3e01001ffe000e7f

def z91 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0c7fffe000f 0xfbfeff863ffff000

def z92 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x88b38c3831e1f195 0xc4459c61c18f0f8c

def z93 : W := mkw 0xc11f7fbd80890359 0x1e08fbfdec04481a 0xffffffffc9990ffe 0xfffffffffe4cc87f

def z94 : W := mkw 0x4000211100000010 0x0200010888000000 0xc000033900000000 0x36000019c8000000

def z95 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xffffffc03e01fe13 0xdffffffe01f00ff0

def z96 : W := mkw 0x0200800a11e15185 0xc0100400508f0a8c 0x0020000031e1f195 0xc0010000018f0f8c

def z97 : W := mkw 0xb01fdea4bd54000c 0x1d80fef525eaa000 0x3fdffcc6fffe000f 0xc9feffe637fff000

def z98 : W := mkw 0x49802159428b8b73 0x224c010aca145c5b 0xeeec73f9cf9f0ffe 0xf777639fce7cf87f

def z99 : W := mkw 0x8001042400000000 0x0400082120000000 0x11138c0600000000 0x08889c6030000000

def z100 : W := mkw 0x4a8021534222c8b2 0xa254010a9a111645 0xffcc73ffc666c9ff 0x7ffe639ffe33364f

def z101 : W := mkw 0x6c1c2bd12e00ac12 0x1b60e15e89700560 0xeffc6ff93e01fe13 0xff7fe37fc9f00ff0

def z102 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0x88b38c3831813000 0x84459c61c18c0980

def z103 : W := mkw 0xc21fffbf91e1519d 0xde10fffdfc8f0a8c 0xfffffffff1e1f195 0xffffffffff8f0f8c

def z104 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0xd3df9fc6c0000000 0x1e9efcfe36000000

def z105 : W := mkw 0xd003f5359154001c 0x06801fa9ac8aa000 0x3c03f03fc1fe000c 0x21e01f81fe0ff000

def z106 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xc0000fffc0000000 0x3e00007ffe000000

def z107 : W := mkw 0xf01fffb5bd54001c 0x1f80fffdadeaa000 0xffdffffffffe000f 0xfffefffffffff000

def z108 : W := mkw 0xc01f7fbd80810119 0x1e00fbfdec040808 0xffffffffc1810194 0xfffffffffe0c080c

def z109 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee8633909990600 0xb7774319c84cc830

def z110 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x000000003ffe000f 0xc000000001fff000

def z111 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc2ec03c00e010e12 0xd617601e00700870

def z112 : W := mkw 0x0200800211604084 0x80100400108b0204 0x5dd3800631e0c195 0xeaee9c00318f060c

def z113 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x199ff0003ffe0001 0x80ccff8001fff000

def z114 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc8010e12 0xfffffffffe400870

def z115 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeff86f393999ffff 0xff7fc379c9cccfff

def z116 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xc0200c3e31e1f195 0xee010061f18f0f8c

def z117 : W := mkw 0x0800004002008802 0x0040000200100440 0x434400c00600c813 0x5a1a200600300640

def z118 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0x80b80f0038013600 0x8405c07801c009b0

def z119 : W := mkw 0x0a80804a53e3d9a7 0xe0540402529f1ecd 0x0020000037e7f9ff 0xc001000001bf3fcf

def z120 : W := mkw 0xc01fffbd91c1111d 0x5e00fffdec8e0888 0xfffffffff1813000 0xbfffffffff8c0980

def z121 : W := mkw 0xfc1ffff5bf54ac1e 0x1fe0ffffadfaa560 0xfffffffffffffe1f 0xfffffffffffffff0

def z122 : W := mkw 0x0200800a11e15185 0xc0100400508f0a8c 0xcce0003831e1f195 0xe6670001c18f0f8c

def z123 : W := mkw 0x201c00002c000000 0x1100e00001600000 0x0098000038000000 0x8004c00001c00000

def z124 : W := mkw 0x4100211900890351 0x02080108c804481a 0xffec73390fff0fff 0xf7ff6399c87ff87f

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0x220410c1c0000000 0x111020860e000000

def z126 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfffffffff001f011 0xffffffffff800f80

def z127 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x999ffffec0000000 0x0cccfffff6000000

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x774410c7c666000f 0x7bba20863e333000

def z129 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0xfffffffff8013600 0xbfffffffffc009b0

def z130 : W := mkw 0x3c1edac03f54ac06 0x19e0f6d601faa560 0xd3ff9fc03e67fe13 0xde9ffcfe01f33ff0

def z131 : W := mkw 0x4100211100080250 0x0208010888004012 0xeec8633908180e6a 0x37764319c840c073

def z132 : W := mkw 0x0200000200204080 0x8010000010010204 0x400000060000c190 0x2a0000003000060c

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x01d0000030000001 0xc00e800001800000

def z134 : W := mkw 0x40002b9180000018 0x0a00015c8c000000 0x000003c1c0000000 0x1000001e0e000000

def z135 : W := mkw 0x001e500000000000 0x1000f28000000000 0x3fdff00000000000 0x01feff8000000000

def z136 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x020c03c00e000e02 0x1010601e00700070

def z137 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x1c03803e01e00184 0x20e01c01f00f000c

def z138 : W := mkw 0x001e500000000000 0x1000f28000000000 0x3fdff0000998000e 0xc1feff80004cc000

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000c7c0000000 0x3a0000063e000000

def z140 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x99b38c3e31e1f001 0x8ccd9c61f18f0f80

def z141 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0x00138c0000000000 0x00009c6000000000

def z142 : W := mkw 0x5102f11911dd0355 0x02881788c88ee81a 0xfeebf33909ff0ffe 0xf7f75f99c84ff87f

def z143 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xbc9bff3fc0000000 0x25e4dff9fe000000

def z144 : W := mkw 0xb01fd42c3dd51105 0x5580fea161eea888 0xbffffc383fff300f 0xc5ffffe1c1fff980

def z145 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x80b80f003e01fe13 0xc405c07801f00ff0

def z146 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0xf76413ffc667cfff 0x7fbb209ffe333e7f

def z147 : W := mkw 0x4000211100000010 0x0200010888000000 0xeec863390998000e 0xf7764319c84cc000

def z148 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0x11138c063060f001 0x08889c6031830780

def z149 : W := mkw 0x001e5a8000000000 0x1800f2d400000000 0xffdfffc000000000 0x1ffefffe00000000

def z150 : W := mkw 0x8001042c00810101 0x0400082160040808 0xddf38c3e01810194 0xeeef9c61f00c080c

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x374410000666000f 0x41ba208000333000

def z152 : W := mkw 0x3a9ed0427f76c8a6 0xb1d4f68213fbb645 0x7fdff0c7fffec9ff 0xfbfeff863ffff64f

def z153 : W := mkw 0xb01fd42c3dd51105 0x5580fea161eea888 0x88bbec3839993000 0x8445df61c1ccc980

def z154 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0xc2e803003e01fe13 0xd617401801f00ff0

def z155 : W := mkw 0x701e7b91ac140018 0x1b80f3dc8d60a000 0x220c73c1ce1e000a 0x1110639e0e70f000

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0x774410c7c00009fe 0x7bba20863e00004f

def z157 : W := mkw 0x8a9f5ee6c222c8aa 0xbc54faf736111645 0x77579cc7c666c9ff 0x7bbabce63e33364f

def z158 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc0b80fc03801fe10 0x9e05c07e01c00ff0

def z159 : W := mkw 0x0000000800810101 0x0000000040040808 0xeee00039018109fe 0xf7770001c80c084f

def z160 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0xc0200c3e0001f190 0x2e010061f0000f8c

def z161 : W := mkw 0x3200800a3df55185 0xc190040051efaa8c 0x002000003ffff19f 0xc001000001ffff8c

def z162 : W := mkw 0x201c00002c000000 0x1100e00001600000 0x2fdc60003f98000f 0xc17ee30001fcc000

def z163 : W := mkw 0xae1d0eee2ea1fd83 0xdd70e87771750fec 0xc3fc0ffe3e01ff93 0xfe1fe07ff1f00ffc

def z164 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe7fc0fc13e01ffff 0xff3fe07e09f00fff

def z165 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0x11141cc6f666f001 0x0888a0e637b33780

def z166 : W := mkw 0x80010ea480000008 0x0c00087524000000 0x00000cc6c0000000 0x0800006636000000

def z167 : W := mkw 0x6d1c2bd12e08ae52 0x1b68e15e89704572 0x220c63c10e180e6a 0x1110631e0870c073

def z168 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2c006039019801ec 0x21600301c80cc00f

def z169 : W := mkw 0x8001042400000000 0x0400082120000000 0x1c03803e00000000 0x20e01c01f0000000

def z170 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0x3c03903fc1e601ec 0x21e01c81fe0f300f

def z171 : W := mkw 0x0000800011400004 0x00000400008a0000 0xddf38c0031e1f015 0xceef9c60018f0f80

def z172 : W := mkw 0xae01846e3fe1fd87 0xc5700c2371ff0fec 0xddf38c3e3fe1ff97 0xeeef9c61f1ff0ffc

def z173 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0xfdd3fc3fc0000000 0x2fee9fe1fe000000

def z174 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc998000e 0xfffefffffe4cc000

def z175 : W := mkw 0x0200000200204080 0x8010000010010204 0x774000070060c9ff 0x7bba00003803064f

def z176 : W := mkw 0x0880004042028822 0x2044000202101441 0x664410c1c60609fe 0x733220860e30304f

def z177 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x374410003ffe000f 0xc1ba208001fff000

def z178 : W := mkw 0xae1d8ee63f60fc86 0xdd70ec7731fb07e4 0x11178cc63660f001 0x0888bc6631b30780

def z179 : W := mkw 0x8001042400000000 0x0400082120000000 0xddd38c3e00000000 0x2eee9c61f0000000

def z180 : W := mkw 0x401e7b9180000018 0x1a00f3dc8c000000 0x220c73c1c0000000 0x1110639e0e000000

def z181 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3e0ff0000ffe000e 0x01f07f80007ff000

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0200c000001f010 0x0e01006000000f80

def z183 : W := mkw 0x0000800011400004 0x00000400008a0000 0x1c03800001e00004 0x00e01c00000f0000

def z184 : W := mkw 0xc11f7fbd80890359 0x1e08fbfdec04481a 0xffffffffc9990600 0xbffffffffe4cc830

def z185 : W := mkw 0x0100000800890341 0x000800004004481a 0x2ee8600009990ffe 0xc1774300004cc87f

def z186 : W := mkw 0xc103753d80890359 0x06081ba9ec04481a 0xfeebf33fc9990ffe 0xf7f75f99fe4cc87f

def z187 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0xddd38c3e3060f001 0x2eee9c61f1830780

def z188 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xfdf39c3ff1e7f1fd 0xefef9ce1ff8f3f8f

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x4440000000000194 0x622200000000000c

def z190 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x1dd3803e31e00185 0xe0ee9c01f18f000c

def z191 : W := mkw 0x0880004042028822 0x2044000202101441 0x634410c1c606c87b 0x5b1a20860e303643

def z192 : W := mkw 0xb21fd42e3df55185 0xd590fea171efaa8c 0xfffffc3e3ffff19f 0xefffffe1f1ffff8c

def z193 : W := mkw 0x2d1c0ac82e89af43 0x1968e05641744d7a 0xc3fc0fc03f99ffff 0xde1fe07e01fccfff

def z194 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x664000010666c9ff 0x733200000833364f

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x24000001000001ec 0x212000000800000f

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0e0000000010010 0xc607000000000800

def z197 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0xfdf3ec3f31f9f1fd 0xefef9f61f98fcf8f

def z198 : W := mkw 0x0c0000400200ac02 0x0060000200100560 0x002000000001fe10 0x0001000000000ff0

def z199 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0xddf38c3e0001f190 0x2eef9c61f0000f8c

def z200 : W := mkw 0x6d1c2bd92e89af53 0x1b68e15ec9744d7a 0xeeec63f90f990ffe 0xf777631fc87cc87f

def z201 : W := mkw 0x4100211100080250 0x0208010888004012 0x2208630108180e6a 0x111043180840c073

def z202 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffdfffffc8180e6a 0x3ffefffffe40c073

def z203 : W := mkw 0x8a01846e13e1d987 0xc4500c23709f0ecc 0xdff78cfe37e1f997 0xfeffbc67f1bf0fcc

def z204 : W := mkw 0xca812ff7c222c8ba 0xae54097fbe111645 0xc0000fffc000c9f0 0x3e00007ffe00064f

def z205 : W := mkw 0x4100211900890351 0x02080108c804481a 0x88a8633809990600 0x84454319c04cc830

def z206 : W := mkw 0x4000211100000010 0x0200010888000000 0xeec8633900000000 0x37764319c8000000

def z207 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xbfdfff3800000000 0x05fefff9c0000000

def z208 : W := mkw 0xae1d8eee3fe1fd87 0xdd70ec7771ff0fec 0xdfff8ffe3fe1ff97 0xfefffc7ff1ff0ffc

def z209 : W := mkw 0x4000211100000010 0x0200010888000000 0x2208630100000000 0x1110431808000000

def z210 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1117900036660001 0x0088bc8001b33000

def z211 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xeffc6fc03f99fe1f 0xdf7fe37e01fccff0

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x340010000066000c 0x01a0008000033000

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x110410c6c0000000 0x0888208636000000

def z214 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1ddbe00039f80005 0xc0eedf0001cfc000

def z215 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0x01140cc000000000 0x0808a06600000000

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0xccc0003800000000 0x26660001c0000000

def z217 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0x7f4470ffc7fec9ff 0x7bfa2387fe3ff64f

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x220860000818000a 0x011043000040c000

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x220410000606000a 0x0110208000303000

def z220 : W := mkw 0x4100211100080250 0x0208010888004012 0xe2e8630108190e7a 0xd71743180840c873

def z221 : W := mkw 0xc11f7fbd80890359 0x1e08fbfdec04481a 0xffffffffc0010ff0 0x3ffffffffe00087f

def z222 : W := mkw 0x0200000200204080 0x8010000010010204 0x774410c7c060c195 0x7bba20863e03060c

def z223 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x43540cc03600f813 0x5a1aa06601b007c0

def z224 : W := mkw 0x389ed0407f568826 0x31c4f68203fab441 0x3fdff0c1fffe086f 0xd1feff860ffff043

def z225 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0xffdfffc03ffe000f 0xdffefffe01fff000

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x02c8000008000002 0xc016400000400000

def z227 : W := mkw 0x4d002bd90289af53 0x0a68015ec8144d7a 0xc0200ff90001fff0 0x3e01007fc8000fff

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x1104100006660001 0x0088208000333000

def z229 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0x9df38c3831e13005 0xc4ef9c61c18f0980

def z230 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0xc1f00c3e3001f191 0xee0f8061f1800f8c

def z231 : W := mkw 0x8003542480000008 0x04001aa124000000 0x10039006c0000000 0x00801c8036000000

def z232 : W := mkw 0x8e010eee02a1fd83 0xcc70087770150fec 0xc0200ffe0001ff90 0x3e01007ff0000ffc

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0x2ec860000998000e 0xc1764300004cc000

def z234 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0xfffbef3f39f9ffff 0xffffdf79f9cfcfff

def z235 : W := mkw 0x0200000200204080 0x8010000010010204 0x110000060060c001 0x0888000030030600

def z236 : W := mkw 0xca9f7ff7c222c8ba 0xbe54fbffbe111645 0xffdfffffc666c001 0x3ffefffffe333600

def z237 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x000000000666c9ff 0x400000000033364f

def z238 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x3d17fcffc0000000 0x29e8bfe7fe000000

def z239 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x7fcc70c7cffec9ff 0xfbfe63863e7ff64f

def z240 : W := mkw 0xf11fffbdbddd035d 0x1f88fffdedeee81a 0xffffffffffff0fff 0xfffffffffffff87f

def z241 : W := mkw 0x4380211b40ab43f1 0xa21c0108da055a1f 0x3c00703fc1fe01ec 0x21e00381fe0ff00f

def z242 : W := mkw 0x3c0080403f54ac06 0x01e0040201faa560 0x002000003ffffe1f 0xc001000001fffff0

def z243 : W := mkw 0xc29f7fb7c02240b8 0xbe14fbfdbe011205 0xffdfffffc06601ec 0x3ffefffffe03300f

def z244 : W := mkw 0xf01fffb5bd54001c 0x1f80fffdadeaa000 0xbfdfff383ffe000f 0xc5fefff9c1fff000

def z245 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff79c3e37e7f19f 0xefffbce1f1bf3f8c

def z246 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xeedbef3900000000 0x3776df79c8000000

def z247 : W := mkw 0x6d1c2bd12e08ae52 0x1b68e15e89704572 0xe3fc6fc13e19fe7b 0xdf1fe37e09f0cff3

def z248 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x000000000666c001 0x0000000000333600

def z249 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff79cfff1e1f195 0xffffbce7ff8f0f8c

def z250 : W := mkw 0x4100211900890351 0x02080108c804481a 0xc2e8033908010ff2 0xf6174019c840087f

def z251 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x1d138c3e31e0f185 0x28e89c61f18f078c

def z252 : W := mkw 0x201e50002c000000 0x1100f28001600000 0x3fdff0003e000003 0xc1feff8001f00000

def z253 : W := mkw 0x301c80003d540004 0x1180e40001eaa000 0x03dc00003ffe000f 0xc01ee00001fff000

def z254 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0x00000cc00000f000 0x0800006600000780

def z255 : W := mkw 0x0002500000000000 0x0000128000000000 0x3c03f00000000000 0x01e01f8000000000

def z256 : W := mkw 0x0100000800890341 0x000800004004481a 0x0020000000010ff0 0x000100000000087f

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee8630009990e1e 0xd7774318004cc870

def z258 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0x220c73c00e1e0e0a 0x1110639e0070f070

def z259 : W := mkw 0xc101a53d11c91355 0x46080d29e88e489a 0x88bbef3839993600 0x8445df79c1ccc9b0

def z260 : W := mkw 0x2a9c00426e22c8a2 0xb154e00213711645 0x77dc10c7fe66c9ff 0xfbbee0863ff3364f

def z261 : W := mkw 0x201c00002c000000 0x1100e00001600000 0x020c00000e000002 0x0010600000700000

def z262 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xf7441fffc0000000 0x3fba20fffe000000

def z263 : W := mkw 0x0800004002008802 0x0040000200100440 0xc3ec03c00e01ce13 0xde1f601e00700e70

def z264 : W := mkw 0x4100211900890351 0x02080108c804481a 0xffec73ffc9990ffe 0xffff639ffe4cc87f

def z265 : W := mkw 0x6d1c2bd92e89af53 0x1b68e15ec9744d7a 0xeffc6ff93f99ffff 0xff7fe37fc9fccfff

def z266 : W := mkw 0xc11f7fbd80890359 0x1e08fbfdec04481a 0xffdfffffc19801ec 0x3ffefffffe0cc00f

def z267 : W := mkw 0x0880004042028822 0x2044000202101441 0x374410c1c666086f 0x51ba20860e333043

def z268 : W := mkw 0xc11f7fbd80890359 0x1e08fbfdec04481a 0x88bbef3809990600 0x8445df79c04cc830

def z269 : W := mkw 0xec1f7ff5ae00ac1a 0x1f60fbffad700560 0xffdfffffce000e02 0x3ffefffffe700070

def z270 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x23dc70003e1e000b 0xc11ee38001f0f000

def z271 : W := mkw 0x201c00002c000000 0x1100e00001600000 0xc3fc0c003e01f013 0xce1fe06001f00f80

def z272 : W := mkw 0x0000800011400004 0x00000400008a0000 0x1113800030600001 0x00889c0001830000

def z273 : W := mkw 0x6c1e7bd1ae00ac1a 0x1b60f3de8d700560 0x220c73c1ce000e02 0x1110639e0e700070

def z274 : W := mkw 0x4100211900890351 0x02080108c804481a 0xc8a8633909990ff0 0xb6454319c84cc87f

def z275 : W := mkw 0x0880004042028822 0x2044000202101441 0x000000c1c0000860 0x100000060e000043

def z276 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x0000000039980000 0x8000000001ccc000

def z277 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff38c3f31e1f9ff 0xffff9c61f98f0fcf

def z278 : W := mkw 0x4000211100000010 0x0200010888000000 0xeee8633908010e12 0xf7774319c8400870

def z279 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0x220c13c1ce060e6a 0x1110609e0e703073

def z280 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0xd3fc1fc6fe67fe13 0xde9fe0fe37f33ff0

def z281 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff00039980000 0x81feff8001ccc000

def z282 : W := mkw 0x4d002bd90289af53 0x0a68015ec8144d7a 0xeee86ff90999fffe 0xff77437fc84ccfff

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3f80f003801fe13 0xde1fc07801c00ff0

def z284 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x9cb38c3e31e13184 0xa4e59c61f18f098c

def z285 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0x55538c063060f195 0x6aaa9c603183078c

def z286 : W := mkw 0xb201842e3df55185 0xc5900c2171efaa8c 0xddf38c3e3ffff19f 0xeeef9c61f1ffff8c

def z287 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3f47f00007fe000f 0x41fa3f80003ff000

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x1540000000600005 0x40aa000000030000

def z289 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x2edbe0003998000e 0xc176df0001ccc000

def z290 : W := mkw 0x201c00002c000000 0x1100e00001600000 0x0114000036000001 0x0008a00001b00000

def z291 : W := mkw 0xc001253580000018 0x06000929ac000000 0x0000003fc0000000 0x20000001fe000000

def z292 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x220c70003ffe000f 0xc110638001fff000

def z293 : W := mkw 0x401c2b9100000010 0x1a00e15c88000000 0xefdc6ff900000000 0x3f7ee37fc8000000

def z294 : W := mkw 0x0000000800810101 0x0000000040040808 0xeee860380999019e 0xe7774301c04cc80c

def z295 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x331ff0003e7e000b 0x0198ff8001f3f000

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x80b00c0030013000 0x8405806001800980

def z297 : W := mkw 0xcc1f7ff58200ac1a 0x1e60fbffac100560 0xffffffffc001fe10 0x3ffffffffe000ff0

def z298 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc22c0fc00e01fe12 0x1e11607e00700ff0

def z299 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0xc0200fc03e01fe13 0xde01007e01f00ff0

def z300 : W := mkw 0x240000002c002400 0x0120000001600120 0x0020000038013600 0x8001000001c009b0

def z301 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x740010c7c066c9fc 0x3ba000863e03364f

def z302 : W := mkw 0xa21d842e3de15185 0xd510ec2171ef0a8c 0xdfff8c3e3fe1f197 0xeefffc61f1ff0f8c

def z303 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xf7fc1fc7fe01fe13 0xffbfe0fe3ff00ff0

def z304 : W := mkw 0x3a9e50426e36c8a2 0xb1d4f2821371b645 0x774c70c7ce7ec9ff 0x7bba63863e73f64f

def z305 : W := mkw 0x4100211100080250 0x0208010888004012 0x0008630008180600 0x000043180040c030

def z306 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x620410c7c606c9fa 0x3b1020863e30364f

def z307 : W := mkw 0x0c1c0ac00200ac02 0x1860e05600100560 0xc3fc0fc00001fe10 0x1e1fe07e00000ff0

def z308 : W := mkw 0x4a9e7bd3c222c8ba 0xba54f3de9e111645 0x774c73c7c666c9ff 0x7bba639e3e33364f

def z309 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc2f80f0038013e12 0xd617c07801c009f0

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x01100c003000f001 0x0808806001800780

def z311 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x510410c7c666c9f1 0x3a8820863e33364f

def z312 : W := mkw 0x0200000200204080 0x8010000010010204 0x774410060666c19f 0x6bba20803033360c

def z313 : W := mkw 0xc201a53f11e15195 0xc6100d29f88f0a8c 0xfffbef3f31e1f195 0xffffdf79f98f0f8c

def z314 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x81bc0fc03e01f601 0x8c0de07e01f00fb0

def z315 : W := mkw 0x4002711180000018 0x020013888c000000 0x20007001c0000000 0x010003800e000000

def z316 : W := mkw 0xf01f7fb5ac140018 0x1f80fbfdad60a000 0xffdfffffce1e000a 0x3ffefffffe70f000

def z317 : W := mkw 0x0300800a11e953c5 0xc0180400508f4a9e 0x0020000039f9ffff 0xc001000001cfcfff

def z318 : W := mkw 0x651c2b992c892751 0x1b28e15cc964493a 0xeef86f3939993ffe 0xf777c379c9ccc9ff

def z319 : W := mkw 0x001e500000000000 0x1000f28000000000 0x089be00000000000 0x0044df0000000000

def z320 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1340fc03601fe11 0x1e09a07e01b00ff0

def z321 : W := mkw 0x4000211100000010 0x0200010888000000 0x8888633800000000 0x04444319c0000000

def z322 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x0004100006060000 0x0000208000303000

def z323 : W := mkw 0x8a8184665362d8a6 0xe4540c23329b16c5 0x77579cc7f666f9ff 0x7bbabce63fb337cf

def z324 : W := mkw 0x701ef1113d540014 0x1380f78889eaa000 0xffdff3393ffe000f 0xf7feff99c9fff000

def z325 : W := mkw 0x821fdeae91e1518d 0xdc10fef5748f0a8c 0xddf79cfef1e1f195 0xeeefbce7f78f0f8c

def z326 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0xc3fc0fc03001f011 0xde1fe07e01800f80

def z327 : W := mkw 0x310080083ddd0345 0x0188040041eee81a 0x002000003fff0fff 0xc001000001fff87f

def z328 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x110410c6c666c9ff 0x488820863633364f

def z329 : W := mkw 0xd01fffb59154001c 0x1e80fffdac8aa000 0xffdfffffc1fe000c 0x3ffefffffe0ff000

def z330 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xd1179fffc0000000 0x3e88bcfffe000000

def z331 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcce0033901810ff4 0xf6670019c80c087f

def z332 : W := mkw 0x001ed00011400004 0x1000f680008a0000 0x3fdff00031e00005 0xc1feff80018f0000

def z333 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x1dd380003ffe000f 0xc0ee9c0001fff000

def z334 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0x3c03e03f01f801ec 0x21e01f01f80fc00f

def z335 : W := mkw 0xc301253f00a953d1 0xc6180929f8054a9e 0xc0200f3f0001fff0 0x3e010079f8000fff

def z336 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0x0000003e00000180 0x20000001f000000c

def z337 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0x020c03c000000000 0x1010601e00000000

def z338 : W := mkw 0xc101a53d11c91355 0x46080d29e88e489a 0xeefbef3939993ffe 0xf777df79c9ccc9ff

def z339 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x089be0003ffe000f 0xc044df0001fff000

def z340 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0x7f47f0ffc0000000 0x3bfa3f87fe000000

def z341 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x374c70000e7e000f 0x41ba63800073f000

def z342 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000998000e 0xc0000000004cc000

def z343 : W := mkw 0x001e500000000000 0x1000f28000000000 0x220c700000000000 0x0110638000000000

def z344 : W := mkw 0x4100211900890351 0x02080108c804481a 0x6e406039019809fe 0x73720301c80cc04f

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x3744100000000000 0x01ba208000000000

def z346 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x13df90003e660003 0xc09efc8001f33000

def z347 : W := mkw 0x4b802153422acaf2 0xa25c010a9a115657 0x774c73c7ce7ecfff 0x7bba639e3e73f67f

def z348 : W := mkw 0xc203f53f91e1519d 0xc6101fa9fc8f0a8c 0x3c03f03fc1e00184 0x21e01f81fe0f000c

def z349 : W := mkw 0x0a80804a53e3d9a7 0xe0540402529f1ecd 0x776410c7f7e7f9ff 0xfbbb20863fbf3fcf

def z350 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x1c23803e31e1f195 0xe0e11c01f18f0f8c

def z351 : W := mkw 0x1282d002517640a4 0xa0941680128bb205 0x3c03f007c1fe01ec 0x21e01f803e0ff00f

def z352 : W := mkw 0x00000a8000000000 0x0800005400000000 0xc0000fc000000000 0x1e00007e00000000

def z353 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcae8633809990e12 0xd6574319c04cc870

def z354 : W := mkw 0x04000a8000002400 0x0820005400000120 0x80200f0000013600 0x04010078000009b0

def z355 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2e08633909980fee 0x31704319c84cc07f

def z356 : W := mkw 0xee1fffffbfe1fd9f 0xdf70fffffdff0fec 0xffffffffffe1ff97 0xffffffffffff0ffc

def z357 : W := mkw 0x0800004002008802 0x0040000200100440 0x400000c00000c810 0x1a00000600000640

def z358 : W := mkw 0xfa9ffff7ff76c8be 0xbfd4ffffbffbb645 0xffdffffffffec9ff 0xfffefffffffff64f

def z359 : W := mkw 0x8e018eee13e1fd87 0xcc700c77709f0fec 0xddf38ffe31e1ff95 0xfeef9c7ff18f0ffc

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x5540000600000000 0x2aaa000030000000

def z361 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x3c03f0003ffe000f 0xc1e01f8001fff000

def z362 : W := mkw 0x6d1c2bd92e89af53 0x1b68e15ec9744d7a 0xc3fc0ff93e01fff3 0xfe1fe07fc9f00fff

def z363 : W := mkw 0x301ed0083dd50105 0x1180f68041eea808 0xfffff0383fff019f 0xe7ffff81c1fff80c

def z364 : W := mkw 0xc2012fbf80a15199 0xce10097dfc050a8c 0xc0200fffc001f190 0x3e01007ffe000f8c

def z365 : W := mkw 0x2e1c0ac22e20ec82 0x9970e05611710764 0xd7fc0fc63e61ff97 0xfebfe07e31f30ffc

def z366 : W := mkw 0x0000800811c11105 0x40000400408e0888 0x0020000031813000 0x80010000018c0980

def z367 : W := mkw 0x6c1e7bd1ae00ac1a 0x1b60f3de8d700560 0xe3fc7fc1fe01fe13 0xdf1fe3fe0ff00ff0

def z368 : W := mkw 0x201c00002c000000 0x1100e00001600000 0x37dc10003e66000f 0xc1bee08001f33000

def z369 : W := mkw 0x711ef1193ddd0355 0x1388f788c9eee81a 0xeefbe33939990ffe 0xf777df19c9ccc87f

def z370 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x664000c7c000c9fe 0x7b3200063e00064f

def z371 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x03dc03c03e000e03 0xd01ee01e01f00070

def z372 : W := mkw 0x8001042c00811101 0x4400082160040888 0x80200c3800013000 0x04010061c0000980

def z373 : W := mkw 0xc21f7fb780204098 0x9e10fbfdbc010204 0xffdfffffc060c195 0x7ffefffffe03060c

def z374 : W := mkw 0x8a8184665362d8a6 0xe4540c23329b16c5 0x11179cc6f666f001 0x0888bce637b33780

def z375 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2c20603909990ffe 0xe1610301c84cc87f

def z376 : W := mkw 0x4100a11911c90355 0x02080508c88e481a 0xfffbe33939f90fff 0xf7ffdf19c9cfc87f

def z377 : W := mkw 0x3a8080427f76c8a6 0xa1d4040213fbb645 0x000000003ffec9ff 0xc000000001fff64f

def z378 : W := mkw 0xca837577c222c8ba 0xa6541babbe111645 0x7f47f0ffc666c9ff 0x7bfa3f87fe33364f

def z379 : W := mkw 0x281c00402e008802 0x1140e00201700440 0x43dc00c03e00c813 0xda1ee00601f00640

def z380 : W := mkw 0x0880004042028822 0x2044000202101441 0x000000000606086a 0x0000000000303043

def z381 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x554000c7c060c9f5 0x7aaa00063e03064f

def z382 : W := mkw 0x0b80004a42abcbe3 0xa05c000252155e5f 0x002000000fffcfff 0xc0010000007ffe7f

def z383 : W := mkw 0x1000800011540004 0x00800400008aa000 0x0000000001fe000c 0x00000000000ff000

def z384 : W := mkw 0xb21fd42e3df55185 0xd590fea171efaa8c 0xddf79c3e37e7f195 0xeeefbce1f1bf3f8c

def z385 : W := mkw 0xc21fffb79160509c 0xde10fffdbc8b0284 0xffdffffff060f001 0x3ffeffffff830780

def z386 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x434400c7c600c9f3 0x7a1a20063e30064f

def z387 : W := mkw 0x0000800011400004 0x00000400008a0000 0x1dd3800031e00005 0xc0ee9c00018f0000

def z388 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0x80980f0000000000 0x0404c07800000000

def z389 : W := mkw 0x0000000800810101 0x0000000040040808 0x0020000001810194 0xc0010000000c080c

def z390 : W := mkw 0x0200000200204080 0x8010000010010204 0xd5f00c063061f195 0xeeaf806031830f8c

def z391 : W := mkw 0x0000000800810101 0x0000000040040808 0xcdf00c383181f195 0xee6f8061c18c0f8c

def z392 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x0000000036660001 0x0000000001b33000

def z393 : W := mkw 0xec1f7ff5ae00ac1a 0x1f60fbffad700560 0xffdffffff600f001 0x3ffeffffffb00780

def z394 : W := mkw 0x0a9e50424222c8a2 0xb054f28212111645 0x7fdff0c7c666c9ff 0x7bfeff863e33364f

def z395 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff00036660001 0x01feff8001b33000

def z396 : W := mkw 0x801f542400000000 0x1400faa120000000 0xffdffc3e00000000 0x2ffeffe1f0000000

def z397 : W := mkw 0xc01fffbd91c1111d 0x5e00fffdec8e0888 0x88bbef3831813000 0x8445df79c18c0980

def z398 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x534410c6c666c813 0x5a9a208636333640

def z399 : W := mkw 0x001e500000000000 0x1000f28000000000 0x1117900000000000 0x0088bc8000000000

def z400 : W := mkw 0x0200000200204080 0x8010000010010204 0x1400000600600184 0x20a000003003000c

def z401 : W := mkw 0x0000000800810101 0x0000000040040808 0x0c00003801800184 0x20600001c00c000c

def z402 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x330410c7c666c86b 0x199820863e333643

def z403 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xc8b38c3e3181f190 0xae459c61f18c0f8c

def z404 : W := mkw 0x0000000800810101 0x0000000040040808 0x88a0003801810000 0x84450001c00c0800

def z405 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0xc3fc0fc03e67ffff 0xde1fe07e01f33fff

def z406 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0x88bbef3838013600 0x8445df79c1c009b0

def z407 : W := mkw 0x5102f11911dd0355 0x02881788c88ee81a 0x3c03f03901fe01ec 0x21e01f81c80ff00f

def z408 : W := mkw 0x0100000000080240 0x0008000000004012 0x0000000008180e6a 0x000000000040c073

def z409 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x0bdfe0003f980003 0xc05eff0001fcc000

def z410 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc3fc0fc038013600 0x9e1fe07e01c009b0

def z411 : W := mkw 0x2d0000482e89af43 0x0168000241744d7a 0x002000003f99ffff 0xc001000001fccfff

def z412 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x01340cc03e01fe13 0xc809a06601f00ff0

def z413 : W := mkw 0x0b80004a42abcbe3 0xa05c000252155e5f 0x776410c7cfffcfff 0xfbbb20863e7ffe7f

def z414 : W := mkw 0x4100211900890351 0x02080108c804481a 0xe660033900010ffe 0x77330019c800087f

def z415 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xe20c7fffc0000000 0x3f1063fffe000000

def z416 : W := mkw 0x0e800ac24222eca2 0xa874005612111765 0xc0200fc7c001fff0 0x3e01007e3e000fff

def z417 : W := mkw 0x401e711100000010 0x1200f38888000000 0xffdff33900000000 0x37feff99c8000000

def z418 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3d17f00037fe000d 0x01e8bf8001bff000

def z419 : W := mkw 0xef1dafff3fe9ffd7 0xdf78ed7ff9ff4ffe 0xffffefff3ff9ffff 0xffffff7ff9ffcfff

def z420 : W := mkw 0x0200800a11e15185 0xc0100400508f0a8c 0x1df3800031e1f195 0xc0ef9c00018f0f8c

def z421 : W := mkw 0x0880004042028822 0x2044000202101441 0x000410c0c6060000 0x0000208606303000

def z422 : W := mkw 0x3a9ed0427f76c8a6 0xb1d4f68213fbb645 0x775790c7f666c9ff 0x7bbabc863fb3364f

def z423 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x000000c6c000c000 0x0800000636000600

def z424 : W := mkw 0xcb81a57f53ebdbf7 0xe65c0d2bfa9f5edf 0xffffffffffffffff 0xffffffffffffffff

def z425 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0xddfbef3e39f9f795 0xeeefdf79f1cfcfbc

def z426 : W := mkw 0x8201042600205080 0xc410082130010284 0x00000c060000f000 0x0800006030000780

def z427 : W := mkw 0x8a8104664222c8a2 0xa454082332111645 0xffd79cffc666c9ff 0x7ffebce7fe33364f

def z428 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0x0008030008000600 0x0000401800400030

def z429 : W := mkw 0x4100211900890351 0x02080108c804481a 0x88a8633809990ffe 0xc4454319c04cc87f

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x002000003001f011 0xc001000001800f80

def z431 : W := mkw 0x7100a1193ddd0355 0x03880508c9eee81a 0xeee863393fff0fff 0xf7774319c9fff87f

def z432 : W := mkw 0x3e9edac27f76eca6 0xb9f4f6d613fbb765 0xffffffc7ffffffff 0xfffffffe3fffffff

def z433 : W := mkw 0x389e50406e168822 0x31c4f2820370b441 0x220c70c1ce1e086a 0x111063860e70f043

def z434 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0xddf38f3f31e1fff5 0xfeef9c79f98f0fff

def z435 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc1f80f003801f611 0xce0fc07801c00fb0

def z436 : W := mkw 0x401e7b9180000018 0x1a00f3dc8c000000 0x774c73c7c0000000 0x3bba639e3e000000

def z437 : W := mkw 0xb21fd42e3df55185 0xd590fea171efaa8c 0x3fdff03e3ffe018f 0xe1feff81f1fff00c

def z438 : W := mkw 0x401e7b9180000018 0x1a00f3dc8c000000 0x3fdff3c1c0000000 0x11feff9e0e000000

def z439 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0xd5600c3e0061f195 0x6eab0061f0030f8c

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ec86001099809fe 0xf3764300084cc04f

def z441 : W := mkw 0x2c1c0ac82e81ad03 0x1960e05641740d68 0xcffc0ff83f81ff97 0xfe7fe07fc1fc0ffc

def z442 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x331fffc7c0000000 0x1998fffe3e000000

def z443 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0x0803803801800000 0x00401c01c00c0000

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x2ec8600000000000 0x0176430000000000

def z445 : W := mkw 0xca812ff7c222c8ba 0xae54097fbe111645 0xf7441fffc666c9ff 0x7fba20fffe33364f

def z446 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xaa9ffff9c0000000 0x1554ffffce000000

def z447 : W := mkw 0x6d0021592e89af53 0x0368010ac9744d7a 0xeee863393f99ffff 0xf7774319c9fccfff

def z448 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x374410000666c9ff 0x41ba20800033364f

def z449 : W := mkw 0xac1f5ee4ae00ac0a 0x1d60faf725700560 0xd3ff9fc6fe01fe13 0xde9ffcfe37f00ff0

def z450 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x0803e00001980000 0x00401f00000cc000

def z451 : W := mkw 0x0200800a11e15185 0xc0100400508f0a8c 0x5560000631e1f195 0xeaab0000318f0f8c

def z452 : W := mkw 0x3c1c8ac03f54ac06 0x19e0e45601faa560 0xc3fc0fc03ffffe1f 0xde1fe07e01fffff0

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x34001007c0000000 0x21a000803e000000

def z454 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xddd38fffc0000000 0x3eee9c7ffe000000

def z455 : W := mkw 0x321ed00a3df55185 0xd190f68051efaa8c 0x3ffff0003ffff19f 0xc1ffff8001ffff8c

def z456 : W := mkw 0x711ef1193ddd0355 0x1388f788c9eee81a 0xbffff3383fff060f 0xc5ffff99c1fff830

def z457 : W := mkw 0x0100000800890341 0x000800004004481a 0xc2e8030009990ffe 0xd6174018004cc87f

def z458 : W := mkw 0xb21fd4263d745084 0xd590fea131eba284 0x3fdffc063ffef00f 0xc9feffe031fff780

def z459 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x000000000000c9f0 0x000000000000064f

def z460 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xdddbef3e00000000 0x2eeedf79f0000000

def z461 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0xcce00c3e0181f194 0xee670061f00c0f8c

def z462 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddd38c3e01e00184 0x2eee9c61f00f000c

def z463 : W := mkw 0xc201afbf91e1519d 0xce100d7dfc8f0a8c 0xddf38ffff1e1f195 0xfeef9c7fff8f0f8c

def z464 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x554000060666c9ff 0x6aaa00003033364f

def z465 : W := mkw 0x8001042400000000 0x0400082120000000 0xc0000c3e00000000 0x2e000061f0000000

def z466 : W := mkw 0x2e1c8aca3fe1fd87 0xd970e45651ff0fec 0xc3fc0fc03fe1ff97 0xde1fe07e01ff0ffc

def z467 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x375790003666000f 0x41babc8001b33000

def z468 : W := mkw 0x0200000200204080 0x8010000010010204 0x554000060060c195 0x6aaa00003003060c

def z469 : W := mkw 0x8001042400000000 0x0400082120000000 0x88938c3800000000 0x04449c61c0000000

def z470 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x1003900000660000 0x00801c8000033000

def z471 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0x1dd38c0631e0f005 0xc8ee9c60318f0780

def z472 : W := mkw 0x0a9c0ac24222c8a2 0xb854e05612111645 0xf7dc1fc7c666c9ff 0x7fbee0fe3e33364f

def z473 : W := mkw 0xf31ff53f3dfd53d5 0xd798ffa9f9efea9e 0xffffff3f3fffffff 0xfffffff9f9ffffff

def z474 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x11338c0631e1f195 0xc8899c60318f0f8c

def z475 : W := mkw 0x0100000800890341 0x000800004004481a 0xcce0003809990ffe 0xe6670001c04cc87f

def z476 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0xc3fc0fc7fe01fff3 0xfe1fe07e3ff00fff

def z477 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0x1003800600600000 0x00801c0030030000

def z478 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee8633900010ff0 0x37774319c800087f

def z479 : W := mkw 0x001e500000000000 0x1000f28000000000 0x3fdff0000666000f 0x41feff8000333000

def z480 : W := mkw 0xc21f7fbf80a15199 0xde10fbfdfc050a8c 0xffffffffc001f190 0x3ffffffffe000f8c

def z481 : W := mkw 0x0200000a00a14181 0x8010000050050a0c 0xdde0003e01e1c195 0xeeef0001f00f0e0c

def z482 : W := mkw 0x4100211900890351 0x02080108c804481a 0xece06039019901fc 0xe7670301c80cc80f

def z483 : W := mkw 0xc1012fbd80890359 0x0e08097dec04481a 0xeee86fffc9990ffe 0xff77437ffe4cc87f

def z484 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2228630109990ffe 0xd1114318084cc87f

def z485 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xf7fc1fc03e67fe1f 0xdfbfe0fe01f33ff0

def z486 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x000400c006000000 0x0000200600300000

def z487 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0013ffe09ff 0xf3feff8009fff04f

def z488 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3c9bf00039fe000c 0x81e4df8001cff000

def z489 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1f40cc03601f011 0xce0fa06601b00f80

def z490 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xddf38c3e31813000 0xaeef9c61f18c0980

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dd3800000000000 0x00ee9c0000000000

def z492 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x82bc0fc03e013e02 0x9415e07e01f009f0

def z493 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x2a9ff0003f9e000a 0x8154ff8001fcf000

def z494 : W := mkw 0x081c0ac002008802 0x1840e05600100440 0xc3dc0fc00600c813 0x5e1ee07e00300640

def z495 : W := mkw 0x0800004002008802 0x0040000200100440 0x674400c10600c9ff 0x7b3a20060830064f

def z496 : W := mkw 0xf21fffbfbdf5519d 0xdf90fffdfdefaa8c 0xfffffffffffff19f 0xffffffffffffff8c

def z497 : W := mkw 0x4000211100000010 0x0200010888000000 0xeec86339000009fe 0x77764319c800004f

def z498 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x554410c6c666c195 0x6aaa20863633360c

def z499 : W := mkw 0x8001842411400004 0x04000c21208a0000 0xddd38c3e31e00005 0xeeee9c61f18f0000

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xc020030000010e10 0x1601001800000870

def z501 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdce3803e01e10194 0xe6e71c01f00f080c

def z502 : W := mkw 0xc001253500000010 0x06000929a8000000 0xffdbef3f00000000 0x3ffedf79f8000000

def z503 : W := mkw 0x401e7b9180000018 0x1a00f3dc8c000000 0xeecc73f9c0000000 0x3776639fce000000

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z505 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0x0803e03800000000 0x00401f01c0000000

def z506 : W := mkw 0xca9f7ff7c222c8ba 0xbe54fbffbe111645 0xffdfffffc000c9f0 0x3ffefffffe00064f

def z507 : W := mkw 0x0880004042028822 0x2044000202101441 0x774410c7c606086a 0x3bba20863e303043

def z508 : W := mkw 0x0000800011400004 0x00000400008a0000 0x0000000031e00005 0xc0000000018f0000

def z509 : W := mkw 0x0800004002008802 0x0040000200100440 0x774410c00666c81f 0x5bba208600333640

def z510 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3ecbf00009fe000e 0xc1f65f80004ff000

def z511 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0x000000003600f001 0x0000000001b00780

def z512 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0xf7dc1fc7c0000000 0x3fbee0fe3e000000

def z513 : W := mkw 0xc11f7fbd80890359 0x1e08fbfdec04481a 0xeefbef3909990ffe 0xf777df79c84cc87f

def z514 : W := mkw 0x02800002402240a0 0xa014000012011205 0x00000000006601ec 0x000000000003300f

def z515 : W := mkw 0x0100000800890341 0x000800004004481a 0x6660000109990ffe 0xf3330000084cc87f

def z516 : W := mkw 0xc01d2fb580000018 0x1e00e97dac000000 0xc3dc0fffc0000000 0x3e1ee07ffe000000

def z517 : W := mkw 0x711ef1193ddd0355 0x1388f788c9eee81a 0x3fdff0393ffe01ef 0xe1feff81c9fff00f

def z518 : W := mkw 0x201c80003d400004 0x1100e40001ea0000 0x1fdf80003fe00007 0xc0fefc0001ff0000

def z519 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeec86339019801ec 0x37764319c80cc00f

def z520 : W := mkw 0x0000800811c10105 0x00000400408e0808 0xddf3803831e10195 0xe6ef9c01c18f080c

def z521 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0xc1f00c003e01fe13 0xce0f806001f00ff0

def z522 : W := mkw 0x6d1c2bd92e89af53 0x1b68e15ec9744d7a 0xcbfc6ff83f99fe13 0xde5fe37fc1fccff0

def z523 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x031c0fc03e00fe03 0x1818e07e01f007f0

def z524 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0x436400c03e01fe13 0xda1b200601f00ff0

def z525 : W := mkw 0x3c1ed0403f54ac06 0x11e0f68201faa560 0x3ffff0003ffffe1f 0xc1ffff8001fffff0

def z526 : W := mkw 0x4100211100080250 0x0208010888004012 0x2000600100180068 0x010003000800c003

def z527 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x022c03c03e01fe13 0xd011601e01f00ff0

def z528 : W := mkw 0xbe1fdeee3ff5fd87 0xddf0fef771ffafec 0xfffffffe3fffff9f 0xfffffffff1fffffc

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x0208030008000e02 0x1010401800400070

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020000008010e12 0xc001000000400870

def z531 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3dd3f00031fe000d 0xc1ee9f80018ff000

def z532 : W := mkw 0xc21fffbf91e1519d 0xde10fffdfc8f0a8c 0xffdfffffc1e00184 0x3ffefffffe0f000c

def z533 : W := mkw 0x0000000800810101 0x0000000040040808 0xc020003800010190 0x26010001c000080c

def z534 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xeec86fffc0000000 0x3f76437ffe000000

def z535 : W := mkw 0x4000211100000010 0x0200010888000000 0xffcc73ffc0000000 0x3ffe639ffe000000

def z536 : W := mkw 0x300000002c140000 0x018000000160a000 0x000000000e1e000a 0x000000000070f000

def z537 : W := mkw 0xf01fffb5bd54001c 0x1f80fffdadeaa000 0xffdffffff6660001 0x3ffeffffffb33000

def z538 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x3fdff0000e1e000a 0x01feff800070f000

def z539 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaca86339099907ec 0xa5654319c84cc83f

def z540 : W := mkw 0xc21fffbf91e1519d 0xde10fffdfc8f0a8c 0xddfbef3e31e1f195 0xeeefdf79f18f0f8c

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c0060000198000c 0x01600300000cc000

def z542 : W := mkw 0x4100211100080250 0x0208010888004012 0x0000030100000e60 0x1000001808000073

def z543 : W := mkw 0x651c2b992c892751 0x1b28e15cc964493a 0x88b86f3839993600 0x8445c379c1ccc9b0

def z544 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x34001007c666c9ff 0x61a000803e33364f

def z545 : W := mkw 0xb01fd4243d540004 0x1580fea121eaa000 0xffdffc3e3ffe000f 0xeffeffe1f1fff000

def z546 : W := mkw 0x0800004002008802 0x0040000200100440 0x010400c00600c001 0x0808200600300600

def z547 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xc89befffc0000000 0x3e44df7ffe000000

def z548 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0xd1f38c063061f011 0xce8f9c6031830f80

def z549 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xd1338c3e3061f191 0x2e899c61f1830f8c

def z550 : W := mkw 0x200000002c000000 0x0100000001600000 0x000000003e000003 0xc000000001f00000

def z551 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x0013800030000000 0x00009c0001800000

def z552 : W := mkw 0x821fdea69160508c 0xdc10fef5348b0284 0x11179cc6f060f001 0x0888bce637830780

def z553 : W := mkw 0x4100211900890351 0x02080108c804481a 0x00000039000001e0 0x20000001c800000f

def z554 : W := mkw 0x4300211b00a943d1 0x82180108d8054a1e 0xffe8633f09f9cfff 0xffff4319f84fce7f

def z555 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0x77541cc7f666f9ff 0x7bbaa0e63fb337cf

def z556 : W := mkw 0x411c2b9900890351 0x1a08e15cc804481a 0xeffc6ff909990ffe 0xff7fe37fc84cc87f

def z557 : W := mkw 0x4100211900890351 0x02080108c804481a 0xc020033909990ffe 0xf6010019c84cc87f

def z558 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0xddd79cfec0000000 0x2eeebce7f6000000

def z559 : W := mkw 0x001c000000000000 0x1000e00000000000 0x03dc000000000000 0x001ee00000000000

def z560 : W := mkw 0x0080000040020020 0x2004000002001001 0x20001001c0060068 0x010000800e003003

def z561 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7c666c001 0x3bba20863e333600

def z562 : W := mkw 0xac1d0ee42e00ac02 0x1d60e87721700560 0xdfff8ffe3e01fe13 0xfefffc7ff1f00ff0

def z563 : W := mkw 0x1a82d0425376c8a6 0xa0d41682129bb645 0x7f47f0c7c7fec9ff 0x7bfa3f863e3ff64f

def z564 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc2e80fc00801fe12 0xde17407e00400ff0

def z565 : W := mkw 0x0100000800890341 0x000800004004481a 0x0020000009990600 0x80010000004cc830

def z566 : W := mkw 0x0200000200204080 0x8010000010010204 0x000000000060c195 0x400000000003060c

def z567 : W := mkw 0x4100211100080250 0x0208010888004012 0x2ec8630109980e6e 0xd1764318084cc073

def z568 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x374410c6c666c00f 0x49ba208636333600

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6e8030108010ffe 0xf73740180840087f

def z570 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0x88bbef0039993600 0x8445df7801ccc9b0

def z571 : W := mkw 0x4000211100000010 0x0200010888000000 0x2c00603900000000 0x21600301c8000000

def z572 : W := mkw 0x0800004002008802 0x0040000200100440 0xc3f40cc03601f813 0xde1fa06601b00fc0

def z573 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0x000003c000000e00 0x1000001e00000070

def z574 : W := mkw 0x711ef1193ddd0355 0x1388f788c9eee81a 0x88bbe33839990600 0x8445df19c1ccc830

def z575 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7c000c9f0 0x3bba20863e00064f

def z576 : W := mkw 0xec1d2ff5ae00ac1a 0x1f60e97fad700560 0xc3fc0ffffe01fe13 0xfe1fe07ffff00ff0

def z577 : W := mkw 0x2e8000426e22eca2 0xa174000213711765 0x002000003e67ffff 0xc001000001f33fff

def z578 : W := mkw 0x0200000a00a15181 0xc010000050050a8c 0x002000000001f190 0x0001000000000f8c

def z579 : W := mkw 0x0800004002008802 0x0040000200100440 0x000000000600c813 0x4000000000300640

def z580 : W := mkw 0x0800004002008802 0x0040000200100440 0x020400c006000802 0x1010200600300040

def z581 : W := mkw 0x6f9c2bdb6eabeff3 0xbb7ce15edb755f7f 0xfffc7fffffffffff 0xffffe3ffffffffff

def z582 : W := mkw 0xcb9f7fffc2abcbfb 0xbe5cfbfffe155e5f 0xffffffffcfffcfff 0xfffffffffe7ffe7f

def z583 : W := mkw 0xac1f5ee4ae00ac0a 0x1d60faf725700560 0x11179cc6f600f001 0x0888bce637b00780

def z584 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfffbec3e39f9f19f 0xefffdf61f1cfcf8c

def z585 : W := mkw 0x201c00002c000000 0x1100e00001600000 0xc3fc03003e010e13 0xd61fe01801f00870

def z586 : W := mkw 0xc101253d00890351 0x06080929e804481a 0xfffbef3f09990ffe 0xffffdf79f84cc87f

def z587 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0xc3fc0fc008010e12 0xde1fe07e00400870

def z588 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x2ec860003ffe000f 0xc176430001fff000

def z589 : W := mkw 0xf01fffb5bd54001c 0x1f80fffdadeaa000 0xffdffffff9980000 0xbffeffffffccc000

def z590 : W := mkw 0xc01f753580000018 0x1600fba9ac000000 0x3fdff03fc0000000 0x21feff81fe000000

def z591 : W := mkw 0xae1d8eee3fe1fd87 0xdd70ec7771ff0fec 0xddf78cfe37e1f195 0xeeefbc67f1bf0f8c

def z592 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x0008600008180000 0x000043000040c000

def z593 : W := mkw 0x2c1c8ac03f40ac06 0x1960e45601fa0560 0xdfff8fc03fe1fe17 0xdefffc7e01ff0ff0

def z594 : W := mkw 0xa61d8eae3de17585 0xdd30ec7571ef0bac 0xddfb8f3e39e1f795 0xeeefdc79f1cf0fbc

def z595 : W := mkw 0xb21fd4263d745084 0xd590fea131eba284 0x11179c063666f001 0x0888bce031b33780

def z596 : W := mkw 0xac1d8eec3fc1bd07 0x5d60ec7761fe0de8 0xcbff8ff83f81fe13 0xde5ffc7fc1fc0ff0

def z597 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3dc0fc03600f001 0x1e1ee07e01b00780

def z598 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x3e0ff3ffc0000000 0x31f07f9ffe000000

def z599 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3dc0fc00e000e02 0x1e1ee07e00700070

def z600 : W := mkw 0x3c1edac03f54ac06 0x19e0f6d601faa560 0x11179cc03666f001 0x0888bce601b33780

def z601 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0xfecbf33fc0000000 0x37f65f99fe000000

def z602 : W := mkw 0x0e800ac24222eca2 0xa874005612111765 0xf7641fc7c667ffff 0x7fbb20fe3e333fff

def z603 : W := mkw 0x411e711900890351 0x1208f388c804481a 0xfffff33909990ffe 0xf7ffff99c84cc87f

def z604 : W := mkw 0x001e500000000000 0x1000f28000000000 0x7fdff0c7c0000000 0x3bfeff863e000000

def z605 : W := mkw 0xc203f53f91e1519d 0xc6101fa9fc8f0a8c 0xfdf3fc3ff1e1f195 0xefef9fe1ff8f0f8c

def z606 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaaa8633909990e6a 0x95554319c84cc873

def z607 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x434400c00666c9ff 0x5a1a20060033364f

def z608 : W := mkw 0x2c1c00402e00ac02 0x1160e00201700560 0x03fc00003e01fe13 0xc01fe00001f00ff0

def z609 : W := mkw 0x411e7b9180080258 0x1a08f3dc8c004012 0x220c73c1c8180e6a 0x1110639e0e40c073

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x80a8030008010600 0x8405401800400830

def z611 : W := mkw 0x821d8eae11e15185 0xdc10ec75708f0a8c 0xdfff8ffe31e1f195 0xfefffc7ff18f0f8c

def z612 : W := mkw 0x7b9ef15b7fffcbf7 0xb3dcf78adbfffe5f 0xfffff3ffffffcfff 0xffffff9ffffffe7f

def z613 : W := mkw 0xc89f7ff5c202883a 0x3e44fbffae101441 0xffdfffffc606086a 0x3ffefffffe303043

def z614 : W := mkw 0x3a9ed0427f76c8a6 0xb1d4f68213fbb645 0x3fdff0003ffec9ff 0xc1feff8001fff64f

def z615 : W := mkw 0x4100211900890351 0x02080108c804481a 0x0800603801980000 0x00400301c00cc000

def z616 : W := mkw 0x3c1edac03f54ac06 0x19e0f6d601faa560 0xcbffefc03f99fe13 0xde5fff7e01fccff0

def z617 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x434c03c00e00ce13 0x5a1a601e00700670

def z618 : W := mkw 0x8a81046e42a3d9a3 0xe454082372151ecd 0xf7641cffc667f9ff 0x7fbb20e7fe333fcf

def z619 : W := mkw 0x3c1edac03f54ac06 0x19e0f6d601faa560 0x3fdffcc03ffef00f 0xc9feffe601fff780

def z620 : W := mkw 0x711e71112c1c0250 0x1388f3888960e012 0x220c73010e1e0e6a 0x111063980870f073

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x3fcc70000ffe000f 0xc1fe6380007ff000

def z622 : W := mkw 0x8a81046e42a3d9a3 0xe454082372151ecd 0xc0200cffc001f9f0 0x3e010067fe000fcf

def z623 : W := mkw 0x4100211100080250 0x0208010888004012 0x6648630108180ffe 0x733243180840c07f

def z624 : W := mkw 0x02800002402240a0 0xa014000012011205 0x75401007c066c1fd 0x6baa00803e03360f

def z625 : W := mkw 0x4300a11b11e953d5 0xc2180508d88f4a9e 0xeee8633939f9ffff 0xf7774319c9cfcfff

def z626 : W := mkw 0x2e00804a3fe1fd87 0xc170040251ff0fec 0x002000003fe1ff97 0xc001000001ff0ffc

def z627 : W := mkw 0x02800002402240a0 0xa014000012011205 0x774410c7c06601ec 0x3bba20863e03300f

def z628 : W := mkw 0x201c0a802c000000 0x1900e05401600000 0xc3dc0fc03e000003 0xde1ee07e01f00000

def z629 : W := mkw 0x4000211900810111 0x02000108c8040808 0xeee8633901810194 0xf7774319c80c080c

def z630 : W := mkw 0xcc012ff58200ac1a 0x0e60097fac100560 0xc0200fffc001fe10 0x3e01007ffe000ff0

def z631 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0x00100c0030003000 0x0000806001800180

def z632 : W := mkw 0x4380211b40ab43f1 0xa21c0108da055a1f 0xfee8733fc9ff0ffe 0xf7f74399fe4ff87f

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000666000f 0x4000000000333000

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x0888600009980000 0x80444300004cc000

def z635 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0x77579cc7c0000000 0x3bbabce63e000000

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x77441001066609ff 0x73ba20800833304f

def z637 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0xeee863ffc999cffe 0xff77431ffe4cce7f

def z638 : W := mkw 0x9203d42e11f55185 0xc4901ea1708faa8c 0x3c03f03e01fe018c 0x21e01f81f00ff00c

def z639 : W := mkw 0x0200800a11e15185 0xc0100400508f0a8c 0xc1f00c0031e1f195 0xce0f8060018f0f8c

def z640 : W := mkw 0x411e7b9980890359 0x1a08f3dccc04481a 0xeeec73f9c9990ffe 0xf777639fce4cc87f

def z641 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x111790003ffe000f 0xc088bc8001fff000

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000001000009f0 0x320000000800004f

def z643 : W := mkw 0x2e9c0ac26e22eca2 0xb974e05613711765 0x774c13c7ce66cfff 0x7bba609e3e73367f

def z644 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x5d43803e01e0c195 0x6aea1c01f00f060c

def z645 : W := mkw 0xb21fd42e3df55185 0xd590fea171efaa8c 0xddfbec3e39f9f195 0xeeefdf61f1cfcf8c

def z646 : W := mkw 0x0200800a11e15185 0xc0100400508f0a8c 0x0000000001e00184 0x00000000000f000c

def z647 : W := mkw 0x401e7b9180000018 0x1a00f3dc8c000000 0xe3dc7fc1c0000000 0x1f1ee3fe0e000000

def z648 : W := mkw 0xc01fffb59140001c 0x1e00fffdac8a0000 0xffdffffff1e00005 0xfffeffffff8f0000

def z649 : W := mkw 0x711e71192c9d0351 0x1388f388c964e81a 0xeeec73390f9f0ffe 0xf7776399c87cf87f

def z650 : W := mkw 0xf01fffb5bd54001c 0x1f80fffdadeaa000 0x889bef3839980000 0x8444df79c1ccc000

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000009fe 0x400000000000004f

def z652 : W := mkw 0x0a0000420220c882 0x8050000210110644 0x574400c60660c997 0x7aba20063033064c

def z653 : W := mkw 0xae1d8ee63f60fc86 0xdd70ec7731fb07e4 0xd3ff8fc63e61fe13 0xde9ffc7e31f30ff0

def z654 : W := mkw 0x4900215902898b53 0x0248010ac8144c5a 0xefec63f90f99cfff 0xff7f631fc87cce7f

def z655 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0x000000000e000e02 0x0000000000700070

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2c8030000000000 0x1616401800000000

def z657 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0xfeebe33f09f90ffe 0xf7f75f19f84fc87f

def z658 : W := mkw 0x0a80004a42a3c9a3 0xa054000252151e4d 0xffe410ffc7e7c9ff 0xffff2087fe3f3e4f

def z659 : W := mkw 0x401e7b9180000018 0x1a00f3dc8c000000 0x0008630000000000 0x0000431800000000

def z660 : W := mkw 0x8a9f5ee6c222c8aa 0xbc54faf736111645 0x11179cc6c666c001 0x0888bce636333600

def z661 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x03dc0cc03e00f003 0xc81ee06601f00780

def z662 : W := mkw 0x711ef1113d5c0254 0x1388f78889eae012 0x3fdff3013ffe0e6f 0xd1feff9809fff073

def z663 : W := mkw 0x701efb91bd54001c 0x1b80f7dc8deaa000 0x3fdff3c1fffe000f 0xd1feff9e0ffff000

def z664 : W := mkw 0x0000800011400004 0x00000400008a0000 0x3fdbe00039f8000f 0xc1fedf0001cfc000

def z665 : W := mkw 0x0000800011400004 0x00000400008a0000 0x3fd7900037e6000f 0xc1febc8001bf3000

def z666 : W := mkw 0xae9d8eee7fe3fda7 0xfd74ec7773ff1fed 0xffff9fffffe7ffff 0xfffffcffffff3fff

def z667 : W := mkw 0x8201042600204080 0x8410082130010204 0xddd38c3e0060c195 0x6eee9c61f003060c

def z668 : W := mkw 0x02800002402240a0 0xa014000012011205 0x76401007c06609fe 0x73b200803e03304f

def z669 : W := mkw 0x8a81846e53e3d9a7 0xe4540c23729f1ecd 0x7f4790ffc7e6c9ff 0x7bfa3c87fe3f364f

def z670 : W := mkw 0x001e5a8080000008 0x1800f2d404000000 0x000410c0c0000000 0x0000208606000000

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x414000000000c011 0x4a0a000000000600

def z672 : W := mkw 0x8001842411401004 0x44000c21208a0080 0x00138c0030003000 0x00009c6001800180

def z673 : W := mkw 0xec1f7ff5ae00ac1a 0x1f60fbffad700560 0xcbffeff83e01fe13 0xde5fff7fc1f00ff0

def z674 : W := mkw 0xc301253f00a953d1 0xc6180929f8054a9e 0xeee86f3f0999fffe 0xff774379f84ccfff

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x434400c000000000 0x1a1a200600000000

def z676 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0xeee863390fffcfff 0xf7774319c87ffe7f

def z677 : W := mkw 0x4100211900890351 0x02080108c804481a 0x8020033800010600 0x04010019c0000830

def z678 : W := mkw 0x0000800011400004 0x00000400008a0000 0x0893800031800000 0x80449c00018c0000

def z679 : W := mkw 0x301e50002c140000 0x1180f2800160a000 0x2ecc70000f9e000e 0xc1766380007cf000

def z680 : W := mkw 0x329ed0027d7640a4 0xb194f68013ebb205 0x3fdff007fffe01ef 0xe1feff803ffff00f

def z681 : W := mkw 0x321ed0023d744084 0x9190f68011eba204 0x7fdff0063ffec19f 0xebfeff8031fff60c

def z682 : W := mkw 0x4100211900890351 0x02080108c804481a 0xe228633908190ffa 0x37114319c840c87f

def z683 : W := mkw 0x381ed0403f548806 0x11c0f68201faa440 0x7fdff0c03ffec81f 0xdbfeff8601fff640

def z684 : W := mkw 0xca9fffffd3e3d9bf 0xfe54fffffe9f1ecd 0xfffffffff7e7f9ff 0xffffffffffbf3fcf

def z685 : W := mkw 0xc2837537c02240b8 0xa6141ba9be011205 0x3c03f03fc06601ec 0x21e01f81fe03300f

def z686 : W := mkw 0x611c21192c890351 0x1308e108c964481a 0xeffc63393f990fff 0xf77fe319c9fcc87f

def z687 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc3640fc00601fe13 0x5e1b207e00300ff0

def z688 : W := mkw 0xee9f7ff7ee22ecba 0xbf74fbffbf711765 0xfffffffffe67ffff 0xfffffffffff33fff

def z689 : W := mkw 0x3a9ed0427f76c8a6 0xb1d4f68213fbb645 0x111790c6f666c001 0x0888bc8637b33600

def z690 : W := mkw 0xf01ff535bd54001c 0x1780ffa9adeaa000 0x3fdff03ffffe000f 0xe1feff81fffff000

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cc0000001800004 0xc0660000000c0000

def z692 : W := mkw 0x489e7bd1c202883a 0x3a44f3de8e101441 0x220c73c1c606086a 0x1110639e0e303043

def z693 : W := mkw 0x0100000800890341 0x000800004004481a 0x00000000019801ec 0x00000000000cc00f

def z694 : W := mkw 0x3c1edac03f54ac06 0x19e0f6d601faa560 0x3fdff3c03ffe0e0f 0xd1feff9e01fff070

def z695 : W := mkw 0x0200800211605084 0xc0100400108b0284 0x000000003060f001 0x0000000001830780

def z696 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x220410c1c666c9ff 0x511020860e33364f

def z697 : W := mkw 0x02800002402240a0 0xa014000012011205 0x37441007c66601ef 0x61ba20803e33300f

def z698 : W := mkw 0xc31fffbf91e953dd 0xde18fffdfc8f4a9e 0xfffffffff9f9ffff 0xffffffffffcfcfff

def z699 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xcbdfeff800000000 0x1e5eff7fc0000000

def z700 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0x80000f3800000000 0x04000079c0000000

def z701 : W := mkw 0x801d0ea400000000 0x1c00e87520000000 0xdfdf8ffe00000000 0x3efefc7ff0000000

def z702 : W := mkw 0x101ed00011540004 0x1080f680008aa000 0x3fdff00001fe000c 0x01feff80000ff000

def z703 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xccf38c3831813194 0xe6679c61c18c098c

def z704 : W := mkw 0x0800004002008802 0x0040000200100440 0x774410c7c600c813 0x7bba20863e300640

def z705 : W := mkw 0x2e8000426e22eca2 0xa174000213711765 0x776410c7fe67ffff 0xfbbb20863ff33fff

def z706 : W := mkw 0xc103753d80890359 0x06081ba9ec04481a 0x3c03f03fc19801ec 0x21e01f81fe0cc00f

def z707 : W := mkw 0x711ef1193ddd0355 0x1388f788c9eee81a 0xd137933936670ff1 0x3689bc99c9b3387f

def z708 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfffffffff801fe13 0xffffffffffc00ff0

def z709 : W := mkw 0x4100211900890351 0x02080108c804481a 0xfee8733909ff0ffe 0xf7f74399c84ff87f

def z710 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc00001ec 0x3ffefffffe00000f

def z711 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xd5738c3e3061f195 0x6eab9c61f1830f8c

def z712 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xdddffffec0000000 0x2eeefffff6000000

def z713 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0x3e07f0ffc0000000 0x31f03f87fe000000

def z714 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x88b38c3831e1f001 0x84459c61c18f0f80

def z715 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0x3fdff3c03ffe000f 0xd1feff9e01fff000

def z716 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0xffd79cffc0000000 0x3ffebce7fe000000

def z717 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0x1d179cfec0000000 0x28e8bce7f6000000

def z718 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x7fd790c7c666c9ff 0x7bfebc863e33364f

def z719 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xddf38c3ff1e1f1f5 0xeeef9c61ff8f0f8f

def z720 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdd338c3e31e1f195 0x2ee99c61f18f0f8c

def z721 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3e0ff0003ffe000f 0xc1f07f8001fff000

def z722 : W := mkw 0xae1d8eee3fe1fd87 0xdd70ec7771ff0fec 0x1e0f83fe0fe00f86 0x30f07c1ff07f007c

def z723 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xffffffc03f99fe1f 0xdffffffe01fccff0

def z724 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0013ffe01ef 0xe1feff8009fff00f

def z725 : W := mkw 0xec037575ae00ac1a 0x07601babad700560 0x3c23f03ffe01fe13 0xe1e11f81fff00ff0

def z726 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3e9ff0003ffe000e 0x81f4ff8001fff000

def z727 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xdbdffffec0000000 0x1edefffff6000000

def z728 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xc9f38c3831e1f195 0xce4f9c61c18f0f8c

def z729 : W := mkw 0x4100211900890351 0x02080108c804481a 0x6e48633909980ffe 0x73724319c84cc07f

def z730 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc3f80fc03801fe13 0xde1fc07e01c00ff0

def z731 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xc0338c3e3001f190 0x2e019c61f1800f8c

def z732 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xf7fc1fc13e67ffff 0xffbfe0fe09f33fff

def z733 : W := mkw 0x4100211900890351 0x02080108c804481a 0xfffbe33909990ffe 0xf7ffdf19c84cc87f

def z734 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdffc003ffef00f 0xc9feffe001fff780

def z735 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xf7579fffc0000000 0x3fbabcfffe000000

def z736 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff007fffe000f 0xe1feff803ffff000

def z737 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeef86f3939993ffe 0xf777c379c9ccc9ff

def z738 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xd99fffffc0000000 0x3eccfffffe000000

def z739 : W := mkw 0x8001042400000000 0x0400082120000000 0xddd79cfec0000000 0x2eeebce7f6000000

def z740 : W := mkw 0x80010ea480000008 0x0c00087524000000 0xddd38cfec0000000 0x2eee9c67f6000000

def z741 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03601fe11 0x1e1fe07e01b00ff0

def z742 : W := mkw 0x4b80215b42abcbf3 0xa25c010ada155e5f 0x99ac73fecfffc601 0x8ccd639ff67ffe30

def z743 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0x3d07f0ffc0000000 0x29e83f87fe000000

def z744 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x776410c7ce67cfff 0xfbbb20863e733e7f

def z745 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xf7fc1fc1fe67fe7f 0xdfbfe0fe0ff33ff3

def z746 : W := mkw 0x421efb9b91e1519d 0xda10f7dcdc8f0a8c 0x222c73c1f1e1f195 0xd111639e0f8f0f8c

def z747 : W := mkw 0x4100211900890351 0x02080108c804481a 0xc8a8633909990ffe 0xf6454319c84cc87f

def z748 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x81bc0fc03e01fe13 0xcc0de07e01f00ff0

def z749 : W := mkw 0x801d0ea400000000 0x1c00e87520000000 0xffdf9fffc0000000 0x3ffefcfffe000000

def z750 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3fd7f00037fe000f 0xc1febf8001bff000

def z751 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xffd79fffc0000000 0x3ffebcfffe000000

def z752 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc3fc0fc03801f611 0xde1fe07e01c00fb0

def z753 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc0b00fc03001fe10 0x9e05807e01800ff0

def z754 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0xd0039fffc0000000 0x3e801cfffe000000

def z755 : W := mkw 0x269c0a826c2264a0 0xb934e05413611325 0xb4b81f07f86737ec 0xa5a5c0f83fc339bf

def z756 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x83fc0f003e01fe13 0xc41fe07801f00ff0

def z757 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc7fc0fc03e01ff97 0xfe3fe07e01f00ffc

def z758 : W := mkw 0xc301a537116852d4 0xc6180d29b88b4296 0x331bef073878fe6b 0x1998df7839c3c7f3

def z759 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xddf38c3e31f9f1fd 0xeeef9c61f18fcf8f

def z760 : W := mkw 0x811f5eac80890349 0x1c08faf56404481a 0x11379cc6c9990ffe 0xc889bce6364cc87f

def z761 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe3fc1fc1fe01fe13 0xdf1fe0fe0ff00ff0

def z762 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0xdfdf9ffec0000000 0x3efefcfff6000000

def z763 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdffffff0000001 0xfffeffffff800000

def z764 : W := mkw 0x1c02dac01354ac06 0x08e016d6009aa560 0xfc23ffc001fffe1c 0x1fe11ffe000ffff0

def z765 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1bdff0003ffe0003 0xc0deff8001fff000

def z766 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc818000a 0x3ffefffffe40c000

def z767 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3ecff0000ffe000e 0xc1f67f80007ff000

def z768 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3c07f00007fe000c 0x01e03f80003ff000

def z769 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc6000003 0x7ffefffffe300000

def z770 : W := mkw 0x3c9e5ac06e16ac22 0x39e4f2d60370b561 0xe3fc7fc1fe1ffe7b 0xdf1fe3fe0ff0fff3

def z771 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaca8633909990ffe 0xe5654319c84cc87f

def z772 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e3181f190 0xaeef9c61f18c0f8c

def z773 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xeffc6fc13f99ffff 0xff7fe37e09fccfff

def z774 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeeec73f9c9990ffe 0xf777639fce4cc87f

def z775 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc0010010 0xfffffffffe000800

def z776 : W := mkw 0xb21f542e2cb55181 0xd590faa17165aa8c 0xe22c7c3e0e1ff19a 0x2f1163e1f070ff8c

def z777 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff38c3e31e1f19f 0xefff9c61f18f0f8c

def z778 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1f80f003e01fe13 0xce0fc07801f00ff0

def z779 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xffdff3003ffe000f 0xd7feff9801fff000

def z780 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0xffffffc03e1ffe1b 0xdffffffe01f0fff0

def z781 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee863390fff0fff 0xf7774319c87ff87f

def z782 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03e01ffff 0xde1fe07e01f00fff

def z783 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03e67fe1f 0xde1fe07e01f33ff0

def z784 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x77541cc7f666f9ff 0x7bbaa0e63fb337cf

def z785 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc6660001 0x3ffefffffe333000

def z786 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0xfffffffffe013603 0xfffffffffff009b0

def z787 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffdfffffc8180ffe 0x7ffefffffe40c07f

def z788 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7c666c9f1 0x3bba20863e33364f

def z789 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x754410c7c666c1fd 0x6baa20863e33360f

def z790 : W := mkw 0x341ed0003d542404 0x11a0f68001eaa120 0x3ffff0003fff360f 0xc1ffff8001fff9b0

def z791 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0013ffe000f 0xf3feff8009fff000

def z792 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfffffc3e3ffff19f 0xefffffe1f1ffff8c

def z793 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff3003ffe0e0f 0xd1feff9801fff070

def z794 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0xffdffffff0003000 0x3ffeffffff800180

def z795 : W := mkw 0x001c0a8000000000 0x1800e05400000000 0xc3fc0fc03801fe13 0xde1fe07e01c00ff0

def z796 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x3dd3f0003ffe000f 0xc1ee9f8001fff000

def z797 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7fc1fc7fe67ffff 0xffbfe0fe3ff33fff

def z798 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x83bc0fc03e01fe03 0x9c1de07e01f00ff0

def z799 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0003ffe09ff 0xc1feff8001fff04f

def z800 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3e07f00007fe000e 0x01f03f80003ff000

def z801 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0xffffffc03ffff01f 0xdffffffe01ffff80

def z802 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x1917fcfec0000000 0x08c8bfe7f6000000

def z803 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xeedbefffc0000000 0x3f76df7ffe000000

def z804 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xffdffffffe66000f 0xfffefffffff33000

def z805 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0xc0200fc03801fe10 0x9e01007e01c00ff0

def z806 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3fcff0000ffe000f 0xc1fe7f80007ff000

def z807 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1bc0fc03e01fe11 0x9e0de07e01f00ff0

def z808 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xf7fc1fc7fe07fe7b 0xffbfe0fe3ff03ff3

def z809 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfffbef3e39f9ff9f 0xffffdf79f1cfcffc

def z810 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x7fc410c7c7e6c9ff 0xfbfe20863e3f364f

def z811 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc2f80f003e01fe13 0xd617c07801f00ff0

def z812 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0x99938c3e3060f001 0x0ccc9c61f1830780

def z813 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0003ffe0001 0x81feff8001fff000

def z814 : W := mkw 0x9201842e11f55185 0xc4900c21708faa8c 0xddf38c3e31fff19d 0xeeef9c61f18fff8c

def z815 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e39e1ff97 0xeeef9c61f1cf0ffc

def z816 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff79cfff7e7f19f 0xffffbce7ffbf3f8c

def z817 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x350410c7c666c9ff 0x69a820863e33364f

def z818 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0x3fdffc003ffe300f 0xc1feffe001fff180

def z819 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1f80fc03801fe11 0xde0fc07e01c00ff0

def z820 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xfff39c3ff1e7f9ff 0xffff9ce1ff8f3fcf

def z821 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3740fc03601fe13 0x5e1ba07e01b00ff0

def z822 : W := mkw 0xf001afb5bd54001c 0x0f800d7dadeaa000 0xc0000ffffffe000f 0xfe00007ffffff000

def z823 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddfb8f3e39e1f795 0xeeefdc79f1cf0fbc

def z824 : W := mkw 0xcb812fffc2abcbfb 0xae5c097ffe155e5f 0xc0200fffc001cff0 0x3e01007ffe000e7f

def z825 : W := mkw 0x8201042600204080 0x8410082130010204 0xddf38c3e3061f195 0xeeef9c61f1830f8c

def z826 : W := mkw 0x8001042400000000 0x0400082120000000 0xddd38cffc0000000 0x3eee9c67fe000000

def z827 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7cc13c7c666c9ff 0x7fbe609e3e33364f

def z828 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2ec8633909980fee 0xf1764319c84cc07f

def z829 : W := mkw 0x6d1c2bd92e89af53 0x1b68e15ec9744d7a 0x2d146cf93798f1ed 0x2968a367c9bcc78f

def z830 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x340410c7c66601ec 0x21a020863e33300f

def z831 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfffffffff0013000 0xbfffffffff800980

def z832 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3d17f0003ffe000f 0xc1e8bf8001fff000

def z833 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe7fc0fc03e01fe1f 0xdf3fe07e01f00ff0

def z834 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc9980000 0xbffefffffe4cc000

def z835 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x80b80f003e01f601 0x8405c07801f00fb0

def z836 : W := mkw 0x4100211900890351 0x02080108c804481a 0xefe863390999cfff 0xff7f4319c84cce7f

def z837 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xbffff3003fff060f 0xc5ffff9801fff830

def z838 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7d41cc7c666c9ff 0x7fbea0e63e33364f

def z839 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7e410c7c667c9ff 0xffbf20863e333e4f

def z840 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc7fe01fe13 0xfe1fe07e3ff00ff0

def z841 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x11138c3e3060f181 0x28889c61f183078c

def z842 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xd3df9fffc0000000 0x3e9efcfffe000000

def z843 : W := mkw 0x2e80804a7fe3fda7 0xe174040253ff1fed 0x002000003fe7ffff 0xc001000001ff3fff

def z844 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xc0138fffc0000000 0x3e009c7ffe000000

def z845 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0xfecbffffc0000000 0x3ff65ffffe000000

def z846 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x81340fc03601f601 0x0c09a07e01b00fb0

def z847 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddd38c3e31e0f185 0x2eee9c61f18f078c

def z848 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0xd1138c3e3060f001 0x2e889c61f1830780

def z849 : W := mkw 0x3a9ed0427f76c8a6 0xb1d4f68213fbb645 0x489be0c7f998c9f0 0xba44df063fccc64f

def z850 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3b9ff0003ffe000b 0x81dcff8001fff000

def z851 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff79cfff1e1f9ff 0xffffbce7ff8f0fcf

def z852 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xffdffffff6000001 0x3ffeffffffb00000

def z853 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc9990e1e 0xfffffffffe4cc870

def z854 : W := mkw 0x3b80804a7fffcbe7 0xa1dc040253fffe5f 0x002000003fffcfff 0xc001000001fffe7f

def z855 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0x1c03e03e01f80184 0x20e01f01f00fc00c

def z856 : W := mkw 0x3c1c0ac02e14ac02 0x19e0e0560170a560 0xc3fc0fc03e1ffe1b 0xde1fe07e01f0fff0

def z857 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeeec73390f9f0ffe 0xf7776399c87cf87f

def z858 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xeffc6fc03e01fe13 0xdf7fe37e01f00ff0

def z859 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x2a9ff0003ffe000f 0xc154ff8001fff000

def z860 : W := mkw 0xf01f7fb5ac140018 0x1f80fbfdad60a000 0xffdffffffe1e000b 0xfffefffffff0f000

def z861 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xfff79cfff1e7f1fd 0xffffbce7ff8f3f8f

def z862 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x99b38c3e31e1f195 0xcccd9c61f18f0f8c

def z863 : W := mkw 0x6c1e7bd1ae00ac1a 0x1b60f3de8d700560 0x020c63c00e000e02 0x1010631e00700070

def z864 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf76413c7c667cfff 0x7fbb209e3e333e7f

def z865 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe3fc6fc03e19fe1b 0xdf1fe37e01f0cff0

def z866 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0xbfdfff003ffe000f 0xc5fefff801fff000

def z867 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x2edbe0003ffe000f 0xc176df0001fff000

def z868 : W := mkw 0xd01f7fb580140018 0x1e80fbfdac00a000 0xffdfffffc01e0008 0x3ffefffffe00f000

def z869 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0003ffe081f 0xd3feff8001fff040

def z870 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xfffff3013fff0fff 0xf7ffff9809fff87f

def z871 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xc8938fffc0000000 0x3e449c7ffe000000

def z872 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xd3ff9fc03e01fe13 0xde9ffcfe01f00ff0

def z873 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xdddbefffc0000000 0x3eeedf7ffe000000

def z874 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc3f40fc03601fe13 0xde1fa07e01b00ff0

def z875 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x9df38c3e31e1f005 0xccef9c61f18f0f80

def z876 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc3f80f003801fe13 0xde1fc07801c00ff0

def z877 : W := mkw 0x8201042e00a15181 0xc410082170050a8c 0xddf38c3e3001f191 0xeeef9c61f1800f8c

def z878 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeec8633909980fee 0x37764319c84cc07f

def z879 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774c70c7ce7ec9ff 0x7bba63863e73f64f

def z880 : W := mkw 0x0c1c0ac00200ac02 0x1860e05600100560 0xc3fc0fc03001fe11 0xde1fe07e01800ff0

def z881 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xffffff003ffffe1f 0xdffffff801fffff0

def z882 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeca8633909990ffc 0xb7654319c84cc87f

def z883 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3f57f00037fe000f 0x41fabf8001bff000

def z884 : W := mkw 0xd303f53f11fd53d5 0xc6981fa9f88fea9e 0x3c03f03f01fe01ec 0x21e01f81f80ff00f

def z885 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x620410c7c666c9ff 0x7b1020863e33364f

def z886 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1340fc03e01fe13 0xde09a07e01f00ff0

def z887 : W := mkw 0x7d1e7bd12e1cae52 0x1be8f3de8970e572 0x220c73c10e1e0e6a 0x1110639e0870f073

def z888 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x88b38c383181f190 0x84459c61c18c0f8c

def z889 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee863ffc9990ffe 0xff77431ffe4cc87f

def z890 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0c6fffe000f 0xc9feff8637fff000

def z891 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffdfffffc0180068 0x3ffefffffe00c003

def z892 : W := mkw 0x04000a8000002400 0x0820005400000120 0xc1f00f003001f611 0xce0f807801800fb0

def z893 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc0000194 0x7ffefffffe00000c

def z894 : W := mkw 0xf01f7fb5ac140018 0x1f80fbfdad60a000 0xffdfffffc6060000 0x3ffefffffe303000

def z895 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0x80b80f003801f611 0xc405c07801c00fb0

def z896 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xcbffefc03e01fe13 0xde5fff7e01f00ff0

def z897 : W := mkw 0x0e8000424222eca2 0xa074000212111765 0x776410c7c667ffff 0x7bbb20863e333fff

def z898 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xf31fffffc0000000 0x3f98fffffe000000

def z899 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff79c3e31e1f195 0xefffbce1f18f0f8c

def z900 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x88b38c3e3181f000 0x8c459c61f18c0f80

def z901 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xf7fc1fc7fe67fe1f 0xffbfe0fe3ff33ff0

def z902 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaaa8633909990ffe 0xd5554319c84cc87f

def z903 : W := mkw 0x8001842411400004 0x04000c21208a0000 0xddf38c3e31e1f015 0xeeef9c61f18f0f80

def z904 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffdfffffc9980e6e 0xfffefffffe4cc073

def z905 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7c666c1ed 0x3bba20863e33360f

def z906 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xd1338c3e31e1f195 0xee899c61f18f0f8c

def z907 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfdf39c3ff1e1f195 0xefef9ce1ff8f0f8c

def z908 : W := mkw 0xf01f7fb5ac140018 0x1f80fbfdad60a000 0xffdfffffc8180000 0x3ffefffffe40c000

def z909 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc000086a 0x3ffefffffe000043

def z910 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0x81b80f003801f601 0x8c0dc07801c00fb0

def z911 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0xddd38c3e3060f195 0x6eee9c61f183078c

def z912 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x91179ffec0000000 0x0c88bcfff6000000

def z913 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc22c0fc03e01fe13 0xde11607e01f00ff0

def z914 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x19138c3e31e0f001 0x08c89c61f18f0780

def z915 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddfbec3e39f9f195 0xeeefdf61f1cfcf8c

def z916 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xd3fc1fc03e67fe13 0xde9fe0fe01f33ff0

def z917 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfffbec3f39f9f9ff 0xffffdf61f9cfcfcf

def z918 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x110410c7c666c1e1 0x288820863e33360f

def z919 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e3061f191 0x2eef9c61f1830f8c

def z920 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0c7fffe09ff 0xfbfeff863ffff04f

def z921 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0x7c03f0ffc0000000 0x3be01f87fe000000

def z922 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xfffff0003fff001f 0xc7ffff8001fff800

def z923 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x82bc0fc03e01fe13 0xd415e07e01f00ff0

def z924 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0xc3fc1fc03e07fe13 0xde1fe0fe01f03ff0

def z925 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0xc803efffc0000000 0x3e401f7ffe000000

def z926 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0xc3640fc03e01fe13 0xde1b207e01f00ff0

def z927 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x11179cffc0000000 0x2888bce7fe000000

def z928 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0xfdd3ffffc0000000 0x3fee9ffffe000000

def z929 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x776410c7f667f9ff 0xfbbb20863fb33fcf

def z930 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0x3c03fcffc0000000 0x29e01fe7fe000000

def z931 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc1300fc03001fe11 0x1e09807e01800ff0

def z932 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x0bdfe0003ffe000f 0xc05eff0001fff000

def z933 : W := mkw 0xc41f7fb580002418 0x1e20fbfdac000120 0xffffffffc0013600 0x3ffffffffe0009b0

def z934 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e37e7f19f 0xeeef9c61f1bf3f8c

def z935 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3ffff0003fff0e1f 0xc1ffff8001fff870

def z936 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0x1d138c3e3060f001 0x28e89c61f1830780

def z937 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfdf38c3f31e1f1fd 0xefef9c61f98f0f8f

def z938 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc000000e 0x7ffefffffe000000

def z939 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcce8633909990ff4 0xf6674319c84cc87f

def z940 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38cfff1e1f195 0xfeef9c67ff8f0f8c

def z941 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee863393999ffff 0xf7774319c9cccfff

def z942 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0xffdffcfec0000000 0x2ffeffe7f6000000

def z943 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfe0fffffc0000000 0x3ff07ffffe000000

def z944 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0x89b38c383181f001 0x8c4d9c61c18c0f80

def z945 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xcffc0fc03f81fe17 0xde7fe07e01fc0ff0

def z946 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc0b80fc03e01fe13 0xde05c07e01f00ff0

def z947 : W := mkw 0x8001042400000000 0x0400082120000000 0xc9f38c383001f011 0xce4f9c61c1800f80

def z948 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3ffff0003ffff01f 0xc1ffff8001ffff80

def z949 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffdfffffc8180600 0x3ffefffffe40c030

def z950 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0c03ffe000f 0xdbfeff8601fff000

def z951 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3dd7f00037fe000d 0xc1eebf8001bff000

def z952 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03f99fe1f 0xde1fe07e01fccff0

def z953 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdcb38c3e31e1f194 0xaee59c61f18f0f8c

def z954 : W := mkw 0x4100211900890351 0x02080108c804481a 0xe228633909990ffe 0xf7114319c84cc87f

def z955 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0xeffc7fc03f9ffe1f 0xdf7fe3fe01fcfff0

def z956 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc066000c 0x3ffefffffe033000

def z957 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xccf38c3831e1f195 0xe6679c61c18f0f8c

def z958 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x9cb38c3e31e1f195 0xe4e59c61f18f0f8c

def z959 : W := mkw 0x0000800811c10105 0x00000400408e0808 0xddf38c3831e1f195 0xeeef9c61c18f0f8c

def z960 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee86f390999fffe 0xff774379c84ccfff

def z961 : W := mkw 0x201c00002c000000 0x1100e00001600000 0xc3fc0f003e01fe13 0xde1fe07801f00ff0

def z962 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xddf39c3ef1e7f195 0xeeef9ce1f78f3f8c

def z963 : W := mkw 0x401e711100000010 0x1200f38888000000 0xffdff3ffc0000000 0x3ffeff9ffe000000

def z964 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0xc1f00fc03e01fe13 0xde0f807e01f00ff0

def z965 : W := mkw 0xca9f7ff7c222c8ba 0xbe54fbffbe111645 0x889bef380666c9ff 0x4444df79c033364f

def z966 : W := mkw 0x6c1e7bd1ae00ac1a 0x1b60f3de8d700560 0x220c73c1c6000000 0x1110639e0e300000

def z967 : W := mkw 0x4100211900890351 0x02080108c804481a 0xfee8733fc9990ffe 0xf7f74399fe4cc87f

def z968 : W := mkw 0x2c1e5ac0ae00ac0a 0x1960f2d605700560 0xc3fc1fc0fe01fe13 0xde1fe0fe07f00ff0

def z969 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc8000e02 0x3ffefffffe400070

def z970 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xcbfc6fc03f99fe13 0xde5fe37e01fccff0

def z971 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xd1f38c3e3061f191 0xee8f9c61f1830f8c

def z972 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3c9bf0003ffe000f 0xc1e4df8001fff000

def z973 : W := mkw 0xc303f53f91e953dd 0xc6181fa9fc8f4a9e 0x3c03f03fc1f801ec 0x21e01f81fe0fc00f

def z974 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0xffffff003fff3e1f 0xd7fffff801fff9f0

def z975 : W := mkw 0x6d1e7bd1ae08ae5a 0x1b68f3de8d704572 0x220c73c1ce180e6a 0x1110639e0e70c073

def z976 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1f40fc03601fe11 0xde0fa07e01b00ff0

def z977 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xf7fc1fc03e01fe13 0xdfbfe0fe01f00ff0

def z978 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e31e1f9ff 0xeeef9c61f18f0fcf

def z979 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcae8633909990ff2 0xf6574319c84cc87f

def z980 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0xfffffffff801f611 0xffffffffffc00fb0

def z981 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x330410c7c666c9ff 0x599820863e33364f

def z982 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xd9b38c3e31e1f191 0xaecd9c61f18f0f8c

def z983 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0xf7fc7fc03e7ffe1f 0xdfbfe3fe01f3fff0

def z984 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0xc2e80fc03e01fe13 0xde17407e01f00ff0

def z985 : W := mkw 0x4100211900890351 0x02080108c804481a 0x88a8633809990ff0 0x84454319c04cc87f

def z986 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xddf38c3e31e7f1fd 0xeeef9c61f18f3f8f

def z987 : W := mkw 0x3a80804a7ff7d9a7 0xe1d4040253ffbecd 0x002000003ffff9ff 0xc001000001ffffcf

def z988 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc0b80f003801f610 0x8e05c07801c00fb0

def z989 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0xffdfffc7fffe000f 0xfffefffe3ffff000

def z990 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff38c3f31e1f195 0xffff9c61f98f0f8c

def z991 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf79cfef1e1f195 0xeeefbce7f78f0f8c

def z992 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x1d338c3e31e1f195 0xe8e99c61f18f0f8c

def z993 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1ddff0003ffe0005 0xc0eeff8001fff000

def z994 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc000c011 0x7ffefffffe000600

def z995 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xfff38c3f39f9ffff 0xffff9c61f9cfcfff

def z996 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x510410c7c666c9ff 0x7a8820863e33364f

def z997 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xccf38c3e3181f194 0xee679c61f18c0f8c

def z998 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffcffe000f 0xfffefffffe7ff000

def z999 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc00009f0 0x3ffefffffe00004f

def z1000 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xbfdffffec0000000 0x0dfefffff6000000

def z1001 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x9df38c3831e1f195 0xc4ef9c61c18f0f8c

def z1002 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3c03f00007fe000f 0x41e01f80003ff000

def z1003 : W := mkw 0x0a80804a53e3d9a7 0xe0540402529f1ecd 0x0000000007e6c9ff 0x40000000003f364f

def z1004 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x730410c7c666c9fb 0x3b9820863e33364f

def z1005 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc1800004 0xfffefffffe0c0000

def z1006 : W := mkw 0x1002d00011540004 0x00801680008aa000 0x3d07f00007fe000d 0x01e83f80003ff000

def z1007 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3f1ff0003ffe000f 0x01f8ff8001fff000

def z1008 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xbe9fffffc0000000 0x35f4fffffe000000

def z1009 : W := mkw 0xc01f753580000018 0x1600fba9ac000000 0x7fdff0ffc0000000 0x3bfeff87fe000000

def z1010 : W := mkw 0x2c0000402e00ac02 0x0160000201700560 0xc3f80f003e01fe13 0xde1fc07801f00ff0

def z1011 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xcbdfefffc0000000 0x3e5eff7ffe000000

def z1012 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc2bc0fc03e01fe12 0x9e15e07e01f00ff0

def z1013 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0013ffe086f 0xd1feff8009fff043

def z1014 : W := mkw 0x0b80804a53ebdbe7 0xe05c0402529f5edf 0x002000003fffffff 0xc001000001ffffff

def z1015 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e39f9f19f 0xeeef9c61f1cfcf8c

def z1016 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeff8633939990fff 0xf77fc319c9ccc87f

def z1017 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x3fdffcffc0000000 0x29feffe7fe000000

def z1018 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xffdff0383ffe000f 0xe7feff81c1fff000

def z1019 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x3c07f0ffc0000000 0x21e03f87fe000000

def z1020 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xbd9fffffc0000000 0x2decfffffe000000

def z1021 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc8010ffe 0xfffffffffe40087f

def z1022 : W := mkw 0x7c1e7bd1ae14ac1a 0x1be0f3de8d70a560 0x220c73c1ce1e0e0a 0x1110639e0e70f070

def z1023 : W := mkw 0x4100211900890351 0x02080108c804481a 0xffe8633909f90fff 0xf7ff4319c84fc87f

def z1024 : W := mkw 0x801f542400000000 0x1400faa120000000 0xffdffcffc0000000 0x3ffeffe7fe000000

def z1025 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdff38c3e31e1f997 0xfeff9c61f18f0fcc

def z1026 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x0803e0003ffe000f 0xc0401f0001fff000

def z1027 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0003ffec01f 0xcbfeff8001fff600

def z1028 : W := mkw 0x4100211900890351 0x02080108c804481a 0xefec63f909990ffe 0xff7f631fc84cc87f

def z1029 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xc9f38c3e3181f191 0xee4f9c61f18c0f8c

def z1030 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x199ff0003ffe000f 0xc0ccff8001fff000

def z1031 : W := mkw 0x4100211900890351 0x02080108c804481a 0x2e28633909990ffe 0xf1714319c84cc87f

def z1032 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xfffffffffe010e13 0xfffffffffff00870

def z1033 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03801fe10 0x9e1fe07e01c00ff0

def z1034 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdffb8f3e31e1f195 0xfeffdc79f18f0f8c

def z1035 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0x3fdffcc03ffe000f 0xc9feffe601fff000

def z1036 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xffdffffff8000000 0xbffeffffffc00000

def z1037 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0x3fdff3003ffe060f 0xc1feff9801fff030

def z1038 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xbb9fffffc0000000 0x1ddcfffffe000000

def z1039 : W := mkw 0x301eda80bd54000c 0x1980f6d405eaa000 0x3fdff0c0fffe000f 0xc1feff8607fff000

def z1040 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xf7fc1fc7fe01ffff 0xffbfe0fe3ff00fff

def z1041 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0063ffe000f 0xebfeff8031fff000

def z1042 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0xffffffc03fff360f 0xdffffffe01fff9b0

def z1043 : W := mkw 0x300080003d540004 0x0180040001eaa000 0x3fdbe0003ffe000f 0xc1fedf0001fff000

def z1044 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xe7fc1fc1fe07ffff 0xff3fe0fe0ff03fff

def z1045 : W := mkw 0x0800004002008802 0x0040000200100440 0xc3fc0fc03e01fe13 0xde1fe07e01f00ff0

def z1046 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xdffb8f3e39f9ffff 0xfeffdc79f1cfcfff

def z1047 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0xc0200fc03601fe11 0x1e01007e01b00ff0

def z1048 : W := mkw 0xc001253500000010 0x06000929a8000000 0xffdfffffc0000000 0x3ffefffffe000000

def z1049 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdffffff000f001 0x3ffeffffff800780

def z1050 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xd7fc0fc63e01fe13 0xfebfe07e31f00ff0

def z1051 : W := mkw 0x8881846c53c39927 0x64440c23629e1cc9 0xaab79cf9f787386a 0x9555bce7cfbc39c3

def z1052 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfdf3ec3e31f9f19d 0xefef9f61f18fcf8c

def z1053 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x3f1fffffc0000000 0x39f8fffffe000000

def z1054 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xffdbefffc0000000 0x3ffedf7ffe000000

def z1055 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xfffffffffe01f013 0xfffffffffff00f80

def z1056 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x80b80fc03801f600 0x8c05c07e01c00fb0

def z1057 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeaa8633909990ffa 0xb7554319c84cc87f

def z1058 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfff79c3f37e7f9ff 0xffffbce1f9bf3fcf

def z1059 : W := mkw 0x2c000ac02e00ac02 0x0960005601700560 0x80200f003e01fe13 0xc401007801f00ff0

def z1060 : W := mkw 0xcb81257f42abdbf3 0xe65c092bfa155edf 0xc0200fffc001fff0 0x3e01007ffe000fff

def z1061 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc13e01fff3 0xfe1fe07e09f00fff

def z1062 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcce8633809990ffe 0xe6674319c04cc87f

def z1063 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xffdfffffff98000f 0xfffefffffffcc000

def z1064 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdff78cfe31e1f195 0xfeffbc67f18f0f8c

def z1065 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x370410c7c666c9ef 0x39b820863e33364f

def z1066 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfecff3ffc0000000 0x37f67f9ffe000000

def z1067 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x360410c7c666c9ff 0x71b020863e33364f

def z1068 : W := mkw 0x4100211900890351 0x02080108c804481a 0xffe8633f09990ffe 0xffff4319f84cc87f

def z1069 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3d9ff0003ffe000d 0x81ecff8001fff000

def z1070 : W := mkw 0x0000800011400004 0x00000400008a0000 0x3fdff0003ffe000f 0xc1feff8001fff000

def z1071 : W := mkw 0x0000000000000000 0x0000000000000000 0x774410c7c66609ff 0x7bba20863e33304f

def z1072 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x3f47f0003ffe000f 0xc1fa3f8001fff000

def z1073 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xc3fc0fc03e07fe7b 0xde1fe07e01f03ff3

def z1074 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xddf38c3e31e1fff5 0xeeef9c61f18f0fff

def z1075 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xffffffc03e67fe1f 0xdffffffe01f33ff0

def z1076 : W := mkw 0x02800002402240a0 0xa014000012011205 0x774410c7c66601ef 0x7bba20863e33300f

def z1077 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc0000812 0x7ffefffffe000040

def z1078 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xddf38c3e3181f011 0xeeef9c61f18c0f80

def z1079 : W := mkw 0x341eda803d542404 0x19a0f6d401eaa120 0xffffff003ffff61f 0xcffffff801ffffb0

def z1080 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc8000002 0xfffefffffe400000

def z1081 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0x3c03f3ffc0000000 0x31e01f9ffe000000

def z1082 : W := mkw 0x4100211900890351 0x02080108c804481a 0xffec733909990ffe 0xf7ff6399c84cc87f

def z1083 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0xffd7fcffc0000000 0x3ffebfe7fe000000

def z1084 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xffdffc003ffe000f 0xcffeffe001fff000

def z1085 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xd1138fffc0000000 0x3e889c7ffe000000

def z1086 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x77cc10c7ce66c9ff 0xfbbe60863e73364f

def z1087 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xddd79fffc0000000 0x3eeebcfffe000000

def z1088 : W := mkw 0xf01f7fb5ac140018 0x1f80fbfdad60a000 0xffdfffffcf9e000e 0xfffefffffe7cf000

def z1089 : W := mkw 0x241c0a802c002400 0x1920e05401600120 0xc3fc0f003e01f613 0xce1fe07801f00fb0

def z1090 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc0600005 0x7ffefffffe030000

def z1091 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeee8633909990ff0 0xb7774319c84cc87f

def z1092 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x7fdff0003ffe019f 0xe3feff8001fff00c

def z1093 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0xfffffffff8013e12 0xffffffffffc009f0

def z1094 : W := mkw 0xc301a53f11e953d5 0xc6180d29f88f4a9e 0x1c03803f01e001e4 0x20e01c01f80f000f

def z1095 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x7fcc70c7c666c9ff 0x7bfe63863e33364f

def z1096 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7cffec9ff 0xfbba20863e7ff64f

def z1097 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x7f4ff3ffc0000000 0x3bfa7f9ffe000000

def z1098 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x7f4470c7c7fec9ff 0x7bfa23863e3ff64f

def z1099 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f00f003001fe11 0xde0f807801800ff0

def z1100 : W := mkw 0xc381a53f51eb53f5 0xe61c0d29fa8f5a9f 0x3c03f03fc1fe01ec 0x21e01f81fe0ff00f

def z1101 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x1dd38c3e31e0f185 0xe8ee9c61f18f078c

def z1102 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfdd7fcffc0000000 0x2feebfe7fe000000

def z1103 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff00037fe000d 0x01feff8001bff000

def z1104 : W := mkw 0xf11fffbdbddd035d 0x1f88fffdedeee81a 0x88bbef3839990600 0x8445df79c1ccc830

def z1105 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe7fc0fc13e01fe13 0xff3fe07e09f00ff0

def z1106 : W := mkw 0x8001042c00810101 0x0400082160040808 0xddf38c3e3181f195 0xeeef9c61f18c0f8c

def z1107 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x889beffec0000000 0x0c44df7ff6000000

def z1108 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0xddd38c3e31e0f005 0xeeee9c61f18f0780

def z1109 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0x99979cfec0000000 0x0cccbce7f6000000

def z1110 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774c13c7ce66cfff 0x7bba609e3e73367f

def z1111 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x374410c7c66609ef 0x71ba20863e33304f

def z1112 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x77d410c7f666c9ff 0xfbbea0863fb3364f

def z1113 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xffec73c7cfffcfff 0xffff639e3e7ffe7f

def z1114 : W := mkw 0x8281842e51e351a5 0xe4140c21728f1a8d 0xfff79c3ff7e7f1ff 0xefffbce1ffbf3f8f

def z1115 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3e31e1f001 0xaeef9c61f18f0f80

def z1116 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xd7fc0fc03e61fe17 0xdebfe07e01f30ff0

def z1117 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xddf38c3e39f9f795 0xeeef9c61f1cfcfbc

def z1118 : W := mkw 0xe41f7fb5ac002418 0x1f20fbfdad600120 0xffdfffffc8000600 0x3ffefffffe400030

def z1119 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x91338c3e3061f001 0x0c899c61f1830f80

def z1120 : W := mkw 0xc0012fb580000018 0x0e00097dac000000 0xdc038fffc0000000 0x3ee01c7ffe000000

def z1121 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc606000a 0x3ffefffffe303000

def z1122 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe3fc0fc13e01fe7b 0xdf1fe07e09f00ff3

def z1123 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x089be0003ffe0001 0x8044df0001fff000

def z1124 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xffffffc7fe01fe13 0xfffffffe3ff00ff0

def z1125 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x5d538c3e31e0f195 0x6aea9c61f18f078c

def z1126 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x7f57fcffc0000000 0x3bfabfe7fe000000

def z1127 : W := mkw 0x001e500000000000 0x1000f28000000000 0x3fdff0000ffe000f 0xc1feff80007ff000

def z1128 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0xbffffc003fff300f 0xc5ffffe001fff980

def z1129 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xe3fc1fc03e07fe1b 0xdf1fe0fe01f03ff0

def z1130 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfd17ffffc0000000 0x3fe8bffffe000000

def z1131 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x534410c7c666c9f3 0x7a9a20863e33364f

def z1132 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x3c03f0000ffe000e 0x01e01f80007ff000

def z1133 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xfffc7fc03ffffe1f 0xdfffe3fe01fffff0

def z1134 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1917f00037fe0001 0x00c8bf8001bff000

def z1135 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x750410c7c666c9fd 0x3ba820863e33364f

def z1136 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc66609ff 0x7ffefffffe33304f

def z1137 : W := mkw 0x801f5ea480000008 0x1c00faf524000000 0xd1179cfec0000000 0x2e88bce7f6000000

def z1138 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc2f80fc03801fe12 0xde17c07e01c00ff0

def z1139 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdffb8c3e39e1f197 0xeeffdc61f1cf0f8c

def z1140 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfdf39c3e31e7f19d 0xefef9ce1f18f3f8c

def z1141 : W := mkw 0x0a80804a53e3d9a7 0xe0540402529f1ecd 0x0020000037e7f195 0xc001000001bf3f8c

def z1142 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x760410c7c666c9fe 0x3bb020863e33364f

def z1143 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x80b80f003801fe10 0x8405c07801c00ff0

def z1144 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xd9f38c3e31e1f011 0xcecf9c61f18f0f80

def z1145 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xf7641cc7c667f9ff 0x7fbb20e63e333fcf

def z1146 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x554410c7c666c9f5 0x7aaa20863e33364f

def z1147 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x331ff0003ffe000f 0xc198ff8001fff000

def z1148 : W := mkw 0x4100211900890351 0x02080108c804481a 0xefec63390f990fff 0xf77f6319c87cc87f

def z1149 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0c1fffe000f 0xd1feff860ffff000

def z1150 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x1ddbe0003ffe000f 0xc0eedf0001fff000

def z1151 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc0010e10 0x3ffffffffe000870

def z1152 : W := mkw 0x4100211900890351 0x02080108c804481a 0xeff86f3909990ffe 0xff7fc379c84cc87f

def z1153 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xcdf38c383181f195 0xee6f9c61c18c0f8c

def z1154 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc8010600 0xbffffffffe400830

def z1155 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x83fc0fc03e01f603 0xcc1fe07e01f00fb0

def z1156 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xddf38c3831e1f015 0xceef9c61c18f0f80

def z1157 : W := mkw 0xf11f7fb5ac1c0258 0x1f88fbfdad60e012 0xffdfffffce1e0e6a 0x3ffefffffe70f073

def z1158 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38c3f31e1f9f5 0xfeef9c61f98f0fcf

def z1159 : W := mkw 0x0c000ac00200ac02 0x0860005600100560 0xc0200fc03001fe11 0xde01007e01800ff0

def z1160 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaea8633909990fee 0xb5754319c84cc87f

def z1161 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc1fc0fc03e01f611 0xce0fe07e01f00fb0

def z1162 : W := mkw 0xe01f7fb5ac000018 0x1f00fbfdad600000 0xffdfffffce000002 0x3ffefffffe700000

def z1163 : W := mkw 0x301eda803d540004 0x1980f6d401eaa000 0xffffffc03fff0e1f 0xdffffffe01fff870

def z1164 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0x3fdff3ffc0000000 0x31feff9ffe000000

def z1165 : W := mkw 0x0a80804a53e3d9a7 0xe0540402529f1ecd 0x0020000031e1f9f5 0xc0010000018f0fcf

def z1166 : W := mkw 0x6c9e7bd1ee02ac3a 0x3b64f3de8f701561 0x220c73c1ce060e6a 0x1110639e0e703073

def z1167 : W := mkw 0x8201842611605084 0xc4100c21308b0284 0xddf38c3e3061f011 0xeeef9c61f1830f80

def z1168 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc33c0fc03e01fe13 0x1e19e07e01f00ff0

def z1169 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0x033c0fc03e01fe13 0xd819e07e01f00ff0

def z1170 : W := mkw 0x4100211900890351 0x02080108c804481a 0xcae8633809990ffe 0xd6574319c04cc87f

def z1171 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f80f003801f611 0xce0fc07801c00fb0

def z1172 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xdfff8fc03e01fe13 0xdefffc7e01f00ff0

def z1173 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xdff78c3e37e1f197 0xeeffbc61f1bf0f8c

def z1174 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xfc9bffffc0000000 0x3fe4dffffe000000

def z1175 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf79c3e37e7f195 0xeeefbce1f1bf3f8c

def z1176 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3f4ff0000ffe000f 0x41fa7f80007ff000

def z1177 : W := mkw 0xc003753580000018 0x06001ba9ac000000 0xffcff3ffc0000000 0x3ffe7f9ffe000000

def z1178 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xea9fffffc0000000 0x3f54fffffe000000

def z1179 : W := mkw 0xc0037fb580000018 0x0e001bfdac000000 0xff47ffffc0000000 0x3ffa3ffffe000000

def z1180 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xc8b38c3e31e1f195 0xee459c61f18f0f8c

def z1181 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0xc8b38c383181f010 0x8e459c61c18c0f80

def z1182 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffffffffc001f010 0x3ffffffffe000f80

def z1183 : W := mkw 0x301ed0003d540004 0x1180f68001eaa000 0x3fdff0000ffe000e 0x01feff80007ff000

def z1184 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xcffc0ff83e01fe13 0xfe7fe07fc1f00ff0

def z1185 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffffffffc8190e7a 0xfffffffffe40c873

def z1186 : W := mkw 0xf01f7fb5ac140018 0x1f80fbfdad60a000 0xffdfffffce7e000f 0x7ffefffffe73f000

def z1187 : W := mkw 0x8001842c11c11105 0x44000c21608e0888 0x88b38c383181f011 0xc4459c61c18c0f80

def z1188 : W := mkw 0x8001042400000000 0x0400082120000000 0xddd38c3e3000f001 0x2eee9c61f1800780

def z1189 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfffbec3e31e1f195 0xefffdf61f18f0f8c

def z1190 : W := mkw 0x2c1e5ac02e00ac02 0x1960f2d601700560 0xe3fc7fc03e01fe13 0xdf1fe3fe01f00ff0

def z1191 : W := mkw 0x4100211900890351 0x02080108c804481a 0xffec73ffcfff0fff 0xffff639ffe7ff87f

def z1192 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xddf38f3e31e1ff95 0xfeef9c79f18f0ffc

def z1193 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc198000c 0x3ffefffffe0cc000

def z1194 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x3ecbf0003ffe000f 0xc1f65f8001fff000

def z1195 : W := mkw 0x3002d0003d540004 0x0180168001eaa000 0x3c03f00037fe000d 0x01e01f8001bff000

def z1196 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0x9db38c3e31e1f185 0xaced9c61f18f0f8c

def z1197 : W := mkw 0xc01f7fb580000018 0x1e00fbfdac000000 0xffdfffffc99809fe 0xfffefffffe4cc04f

def z1198 : W := mkw 0x4100211900890351 0x02080108c804481a 0xee28633909990ffe 0x37714319c84cc87f

def z1199 : W := mkw 0x8301842e11e953c5 0xc4180c21708f4a9e 0xfffbec3e39f9ffff 0xefffdf61f1cfcfff

def z1200 : W := mkw 0x8201842e11e15185 0xc4100c21708f0a8c 0xfffb8f3f39e1ffff 0xffffdc79f9cf0fff

def z1201 : W := mkw 0x4100211900890351 0x02080108c804481a 0xaee8633809990ffe 0xc5774319c04cc87f

def z1202 : W := mkw 0x8001042400000000 0x0400082120000000 0x7f4790ffc0000000 0x3bfa3c87fe000000

def z1203 : W := mkw 0x3c1e5ac02e14ac02 0x19e0f2d60170a560 0xc3fc6fc03e19fe13 0xde1fe37e01f0cff0

def z1204 : W := mkw 0xc11f7fb580080258 0x1e08fbfdac004012 0xffdfffffc0000e60 0x3ffefffffe000073

def z1205 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xc3fc0fc1fe01fe73 0xde1fe07e0ff00ff3

def z1206 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xd3fc1fc6fe01fe13 0xde9fe0fe37f00ff0

def z1207 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x774410c7c66609ee 0x3bba20863e33304f

def z1208 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x374410c7c666c1ef 0x69ba20863e33360f

def z1209 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0x764410c7c66609fe 0x73b220863e33304f

def z1210 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc0300fc03001fe10 0x1e01807e01800ff0

def z1211 : W := mkw 0x2c9c0ac06e02ac22 0x3964e05603701561 0xc3fc1fc0fe07fe13 0xde1fe0fe07f03ff0

def z1212 : W := mkw 0xc01d2fb580000018 0x1e00e97dac000000 0xdfdf8fffc0000000 0x3efefc7ffe000000

def z1213 : W := mkw 0x0a8000424222c8a2 0xa054000212111645 0xffc410ffc666c9ff 0x7ffe2087fe33364f

def z1214 : W := mkw 0x101ed00011540004 0x1080f680008aa000 0x3fdff00007fe000f 0x41feff80003ff000

def z1215 : W := mkw 0x2c1c0ac02e00ac02 0x1960e05601700560 0xc3fc0fc03e01f601 0x9e1fe07e01f00fb0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z5,z6]),(1,[z1,z9,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z11,z4,z5,z6]),(0,[z12,z13,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z14,z2,z15,z3,z4,z5,z6]),(0,[z1,z2,z16,z4,z17,z5,z6]),(0,[z12,z1,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z19]),(0,[z1,z2,z3,z20,z4,z5,z6]),(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z22,z2,z3,z4,z5,z6])],[(0,[z23,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z25,z5,z6]),(0,[z12,z26,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z28,z1,z2,z3,z4,z5,z6])],[(0,[z29,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z30,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z5,z6])],[(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z5,z37,z6]),(0,[z1,z2,z3,z4,z17,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z38]),(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z42]),(0,[z1,z2,z3,z43,z4,z5,z6])],[(0,[z44,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z36,z6]),(1,[z1,z47,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z48,z6])]],
   [[(0,[z1,z49,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z50])],[(0,[z51,z2,z3,z4,z52,z5,z6]),(0,[z1,z2,z3,z4,z5,z53,z6]),(0,[z1,z54,z2,z3,z4,z5,z55]),(0,[z1,z2,z3,z56,z4,z5,z6]),(1,[z1,z2,z57,z4,z5,z6]),(0,[z1,z2,z3,z4,z58,z5,z6]),(0,[z1,z2,z3,z4,z5,z59,z6]),(0,[z1,z2,z60,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z61,z6])],[(0,[z62,z2,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z6]),(0,[z1,z2,z3,z4,z5,z6,z64]),(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z1,z66,z3,z30,z4,z5,z6])],[(0,[z23,z1,z2,z3,z4,z67,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z6])],[(1,[z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z71,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z72,z6]),(0,[z12,z1,z2,z20,z4,z5,z6]),(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z75,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z76]),(0,[z1,z2,z3,z4,z5,z77,z6])],[(1,[z1,z2,z3,z4,z5,z78]),(0,[z79,z2,z3,z4,z5,z6,z80]),(0,[z1,z2,z3,z81,z4,z5,z6]),(0,[z82,z1,z83,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z84])]],
   [[(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z86,z6]),(1,[z1,z2,z3,z4,z87,z5]),(1,[z1,z18,z88,z4,z5,z6]),(0,[z1,z75,z2,z3,z4,z5,z89])],[(0,[z1,z2,z3,z4,z90,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z92,z6]),(0,[z1,z2,z3,z4,z5,z93,z80]),(0,[z1,z2,z3,z94,z4,z5,z6]),(1,[z1,z95,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z93]),(0,[z1,z2,z3,z4,z5,z97,z6])],[(0,[z1,z2,z3,z4,z98,z5,z6]),(0,[z1,z2,z3,z4,z99,z5,z6]),(0,[z1,z2,z3,z4,z100,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z6])],[(0,[z1,z2,z3,z4,z102,z6,z103]),(0,[z1,z2,z3,z4,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z105]),(0,[z1,z2,z4,z5,z106,z6,z107]),(0,[z1,z2,z3,z4,z5,z6,z108])],[(0,[z79,z1,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z109,z4,z5,z6]),(0,[z1,z88,z2,z110,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z6])],[(0,[z112,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z113,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z114]),(0,[z1,z2,z3,z4,z115,z5,z6]),(0,[z1,z2,z3,z4,z116,z5,z6])],[(0,[z117,z1,z2,z3,z4,z5,z6]),(1,[z117,z24,z3,z4,z5,z6]),(0,[z1,z118,z2,z45,z4,z5,z6]),(0,[z1,z119,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z120]),(0,[z1,z2,z3,z4,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z121]),(0,[z122,z1,z2,z3,z4,z5,z6])],[(0,[z23,z1,z118,z3,z4,z5,z6]),(0,[z1,z123,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z124,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z102,z6]),(0,[z1,z2,z3,z4,z5,z6,z126])]],
   [[(0,[z62,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z127]),(0,[z128,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z107])],[(0,[z1,z2,z3,z4,z5,z6,z129]),(0,[z12,z1,z2,z3,z4,z102,z6]),(0,[z1,z2,z3,z130,z4,z5,z6]),(0,[z1,z2,z3,z131,z4,z5,z6])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z127,z6]),(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z134,z4,z5,z6]),(1,[z135,z1,z2,z4,z5,z107])],[(1,[z51,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z52,z5,z6,z93]),(0,[z1,z54,z3,z16,z4,z5,z6]),(0,[z1,z136,z2,z3,z4,z137,z6]),(0,[z138,z1,z2,z3,z4,z5,z6])],[(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z140,z6]),(0,[z1,z2,z3,z4,z141,z5,z6]),(0,[z1,z2,z3,z4,z142,z5,z6])],[(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(0,[z79,z1,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z2,z3,z147,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z148,z6])],[(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z5,z6])],[(1,[z151,z2,z152,z4,z5,z6]),(0,[z151,z1,z2,z152,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z6]),(0,[z1,z154,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z57,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z107]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z156,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z157,z6])],[(0,[z1,z158,z2,z3,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z160,z6]),(0,[z1,z2,z3,z161,z4,z5,z6])],[(0,[z1,z162,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z163,z6])],[(1,[z1,z164,z3,z4,z5,z6])],[(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z166,z5,z6])],[(0,[z1,z2,z3,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z167,z5,z6]),(0,[z1,z83,z2,z3,z168,z5,z6]),(0,[z1,z2,z3,z4,z169,z5,z6])],[(0,[z12,z1,z118,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z170,z6]),(0,[z171,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z172,z6])],[(0,[z1,z18,z2,z16,z4,z5,z6]),(0,[z1,z18,z75,z3,z4,z5,z6]),(0,[z12,z1,z3,z168,z4,z5,z6]),(0,[z12,z1,z136,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z173,z6]),(1,[z1,z2,z3,z4,z5,z174]),(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z176,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z36,z6,z103]),(0,[z1,z2,z177,z3,z4,z5,z6]),(0,[z1,z18,z3,z4,z137,z5,z6]),(0,[z1,z2,z3,z4,z5,z178,z6]),(0,[z1,z2,z3,z4,z179,z5,z6])],[(1,[z1,z119,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z180,z4,z6])],[(1,[z1,z2,z181,z4,z5,z6]),(1,[z1,z2,z3,z4,z8,z6])],[(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z184]),(0,[z35,z2,z3,z4,z102,z5,z6]),(0,[z185,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z186]),(0,[z135,z1,z2,z3,z4,z5,z106]),(0,[z31,z1,z2,z3,z4,z187,z6])],[(0,[z23,z1,z2,z3,z4,z188,z6]),(0,[z51,z62,z2,z3,z4,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6]),(0,[z1,z119,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z4,z190,z5,z6]),(0,[z191,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z192,z6]),(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z194,z1,z2,z3,z4,z5,z6])],[(0,[z195,z1,z2,z3,z4,z5,z6]),(0,[z196,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z197])]],
   [[(0,[z23,z62,z2,z3,z4,z5,z6]),(0,[z1,z198,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z199,z5,z6])],[(0,[z151,z1,z2,z3,z4,z5,z78]),(0,[z151,z1,z2,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z1,z2,z3,z201,z4,z5,z202]),(1,[z31,z1,z2,z3,z41,z5]),(0,[z1,z2,z3,z180,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z203,z6]),(0,[z1,z2,z3,z4,z5,z6,z204])],[(1,[z1,z2,z3,z4,z5,z64]),(0,[z2,z3,z205,z4,z52,z5,z6]),(0,[z1,z2,z3,z206,z4,z5,z93])],[(0,[z1,z118,z75,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z207,z6]),(0,[z1,z2,z3,z4,z5,z48,z6]),(0,[z1,z3,z4,z137,z5,z208,z6]),(0,[z1,z2,z3,z209,z4,z5,z6])],[(0,[z1,z118,z3,z4,z137,z5,z6]),(0,[z1,z2,z15,z210,z4,z5,z6]),(0,[z1,z54,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z3,z4,z5,z76]),(1,[z1,z211,z3,z4,z5,z6])],[(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z213,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z215,z1,z2,z3,z4,z5,z6]),(0,[z216,z1,z2,z3,z4,z5,z6])],[(1,[z79,z2,z3,z4,z5,z80]),(0,[z12,z82,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z217,z5,z6]),(0,[z218,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z210,z3,z17,z5,z6]),(0,[z1,z2,z3,z4,z5,z93,z107]),(0,[z1,z2,z3,z206,z5,z6,z93])]],
   [[(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z220,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z221]),(0,[z222,z1,z2,z3,z4,z5,z6])],[(0,[z1,z83,z24,z3,z4,z5,z6]),(0,[z1,z223,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z225,z4,z5,z6]),(1,[z74,z1,z3,z4,z5,z76]),(0,[z96,z1,z2,z3,z4,z179,z6])],[(0,[z151,z1,z2,z3,z124,z5,z6]),(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z5,z6]),(1,[z1,z2,z225,z4,z5,z6])],[(0,[z228,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6])],[(0,[z79,z1,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z4,z5,z106,z42]),(0,[z1,z2,z3,z4,z5,z232,z6]),(0,[z233,z1,z2,z210,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z6,z234])],[(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z236]),(0,[z1,z136,z2,z3,z4,z5,z6])],[(0,[z237,z1,z2,z3,z4,z5,z89]),(0,[z1,z2,z3,z4,z5,z238,z6]),(0,[z1,z239,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z240])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z52,z17,z5,z6]),(0,[z82,z49,z2,z3,z4,z5,z6]),(0,[z233,z1,z2,z3,z17,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z241,z5,z6]),(0,[z1,z2,z3,z242,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z126])],[(0,[z1,z2,z3,z4,z5,z6,z243]),(0,[z1,z2,z15,z3,z4,z5,z6]),(0,[z14,z1,z2,z152,z4,z5,z6]),(0,[z237,z1,z2,z3,z4,z5,z76]),(0,[z1,z2,z3,z4,z5,z6,z244]),(0,[z1,z75,z3,z16,z4,z5,z6])],[(0,[z1,z24,z3,z16,z4,z5,z6])],[(1,[z1,z2,z3,z4,z245,z6]),(0,[z1,z2,z3,z4,z5,z246,z6]),(0,[z1,z2,z3,z4,z247,z5,z6])],[(1,[z1,z158,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z64]),(0,[z248,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z249,z6]),(0,[z1,z2,z3,z4,z179,z5,z103])],[(0,[z1,z2,z3,z250,z4,z5,z6]),(1,[z1,z2,z3,z4,z251,z6]),(0,[z1,z252,z2,z3,z4,z5,z6]),(0,[z1,z2,z253,z3,z4,z5,z6])],[(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z255,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z93]),(0,[z256,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z113,z4,z5,z6]),(0,[z257,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z258,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z259])]],
   [[(0,[z1,z2,z3,z4,z5,z188,z6]),(1,[z12,z1,z3,z4,z208,z6]),(0,[z1,z2,z3,z4,z148,z208,z6]),(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z107])],[(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z1,z261,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z208,z6])],[(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z263,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z264,z5,z6]),(0,[z1,z2,z3,z201,z265,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z266]),(0,[z267,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z268])],[(0,[z1,z2,z3,z4,z5,z6,z269]),(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z74,z1,z3,z4,z5,z6,z76]),(0,[z1,z271,z2,z3,z4,z5,z6])],[(0,[z1,z18,z24,z3,z4,z5,z6]),(0,[z151,z14,z2,z3,z4,z5,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z202])],[(0,[z1,z2,z3,z4,z102,z5,z6]),(0,[z1,z2,z3,z4,z273,z5,z6])],[(0,[z23,z2,z3,z4,z52,z5,z6]),(1,[z1,z2,z3,z274,z5,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z276,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z277,z6]),(1,[z1,z2,z3,z4,z140,z6]),(0,[z1,z83,z3,z168,z4,z5,z6]),(0,[z1,z2,z3,z278,z4,z5,z6]),(1,[z1,z2,z3,z4,z179,z103])],[(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z2,z281,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z282,z5,z6]),(0,[z283,z1,z3,z4,z5,z6,z234])]],
   [[(0,[z1,z2,z3,z4,z284,z5,z6]),(0,[z1,z2,z3,z4,z285,z5,z6]),(0,[z1,z2,z3,z4,z102,z192,z6]),(0,[z1,z2,z3,z4,z5,z286,z6])],[(0,[z1,z287,z118,z2,z4,z5,z6]),(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z289,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z93]),(0,[z1,z290,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z291,z6]),(0,[z1,z2,z3,z225,z4,z5,z6]),(0,[z1,z2,z292,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z55]),(0,[z1,z2,z3,z293,z4,z5,z6]),(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z295,z3,z4,z5,z6])],[(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z297]),(0,[z1,z298,z2,z3,z4,z5,z6]),(1,[z1,z299,z3,z4,z5,z6])],[(0,[z1,z300,z2,z3,z4,z5,z6]),(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z302,z6]),(0,[z82,z1,z2,z3,z168,z5,z6]),(0,[z12,z1,z2,z3,z4,z179,z6]),(0,[z1,z2,z3,z4,z5,z208,z6])],[(0,[z12,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z110,z152,z4,z5,z6]),(0,[z79,z1,z303,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z237,z1,z2,z3,z4,z179,z5]),(0,[z1,z2,z3,z304,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z106])],[(0,[z1,z2,z3,z152,z4,z5,z6]),(0,[z1,z2,z3,z305,z4,z5,z6]),(0,[z1,z88,z2,z4,z5,z192,z6]),(0,[z306,z1,z2,z3,z4,z5,z6])],[(0,[z1,z307,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z16,z4,z5,z6,z107]),(0,[z1,z2,z3,z206,z4,z41,z5]),(0,[z1,z2,z3,z4,z308,z5,z6])],[(0,[z117,z1,z118,z3,z4,z5,z6]),(0,[z118,z2,z24,z3,z4,z5,z6]),(0,[z1,z309,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z205,z5,z6,z93]),(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z103,z76]),(0,[z311,z1,z2,z3,z4,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z313])],[(0,[z1,z2,z152,z4,z17,z5,z6]),(0,[z51,z1,z314,z3,z4,z5,z6]),(0,[z1,z2,z3,z315,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z89]),(0,[z1,z2,z66,z3,z4,z5,z316]),(0,[z317,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z318,z5,z6]),(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z75,z2,z3,z4,z5,z6]),(0,[z1,z320,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z1,z2,z322,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(0,[z1,z2,z3,z4,z5,z325,z6]),(0,[z326,z1,z2,z3,z4,z5,z6])],[(0,[z151,z1,z2,z15,z4,z5,z6]),(0,[z31,z1,z2,z3,z205,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z76]),(0,[z1,z2,z3,z327,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z6]),(0,[z328,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z188,z6]),(0,[z23,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z3,z4,z5,z6,z329]),(0,[z233,z1,z2,z3,z4,z5,z330]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z332,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z333,z3,z4,z5,z6])],[(0,[z82,z1,z2,z3,z4,z5,z238]),(0,[z1,z3,z4,z5,z6,z334,z234]),(0,[z1,z2,z3,z4,z5,z6,z335])]],
   [[(0,[z1,z18,z118,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z336,z5,z6])],[(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z179,z6,z234])],[(0,[z1,z2,z3,z4,z5,z6,z338]),(1,[z1,z2,z339,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z8,z6,z76]),(0,[z1,z2,z3,z148,z5,z6,z234])],[(0,[z1,z118,z2,z3,z4,z5,z340]),(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z201,z4,z5,z6])],[(0,[z1,z2,z3,z344,z4,z5,z6]),(0,[z345,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z346,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z348]),(0,[z1,z349,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z1,z2,z3,z4,z36,z192,z6]),(0,[z1,z18,z3,z4,z5,z6,z76]),(0,[z1,z26,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z350,z5,z6])],[(0,[z151,z1,z2,z3,z4,z245,z6]),(0,[z1,z351,z2,z3,z4,z5,z6]),(0,[z1,z88,z3,z16,z4,z5,z6]),(0,[z352,z1,z2,z3,z4,z5,z6])],[(0,[z1,z24,z3,z4,z137,z5,z6]),(0,[z1,z2,z3,z353,z4,z5,z6]),(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z151,z1,z158,z3,z4,z5,z6]),(0,[z1,z2,z110,z16,z4,z5,z6]),(1,[z1,z2,z3,z355,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z356]),(0,[z1,z2,z3,z4,z5,z106,z93]),(1,[z28,z1,z2,z3,z6,z234])]],
   [[(0,[z357,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z358]),(0,[z1,z2,z3,z4,z5,z359,z6])],[(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z237,z1,z2,z3,z4,z5,z80])],[(0,[z1,z2,z3,z4,z5,z277,z6]),(0,[z35,z1,z47,z3,z4,z5,z6]),(0,[z1,z2,z361,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z362,z5,z6]),(0,[z1,z2,z3,z363,z4,z5,z6]),(0,[z1,z2,z3,z180,z4,z6,z234]),(0,[z1,z2,z3,z4,z5,z6,z364])],[(0,[z1,z2,z365,z3,z4,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z367,z5,z6])],[(0,[z1,z368,z2,z3,z4,z5,z6]),(0,[z62,z2,z3,z152,z4,z5,z6]),(0,[z1,z2,z3,z4,z369,z5,z6]),(0,[z370,z1,z2,z3,z4,z5,z6]),(0,[z1,z371,z2,z3,z4,z5,z6])],[(0,[z1,z2,z152,z4,z5,z6,z107]),(0,[z1,z2,z3,z4,z372,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z373]),(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z1,z2,z3,z375,z4,z5,z6]),(0,[z1,z2,z3,z4,z376,z5,z6])],[(0,[z1,z2,z3,z377,z4,z5,z6]),(0,[z1,z2,z15,z4,z17,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z378])],[(0,[z2,z24,z3,z4,z52,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z3,z21,z52,z5,z6]),(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z1,z383,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z384,z6]),(0,[z1,z2,z3,z4,z5,z6,z385])],[(0,[z151,z1,z2,z3,z274,z5,z6]),(0,[z62,z1,z2,z3,z205,z5,z6]),(0,[z1,z2,z3,z4,z5,z249,z6]),(0,[z386,z1,z2,z3,z4,z5,z6]),(1,[z387,z1,z2,z4,z192,z6]),(0,[z1,z2,z3,z4,z5,z6,z103])],[(0,[z388,z1,z2,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z52,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z16,z4,z137,z5,z6])],[(0,[z390,z1,z2,z3,z4,z5,z6]),(0,[z96,z237,z1,z2,z3,z4,z5]),(0,[z1,z88,z2,z210,z4,z5,z6]),(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z387,z1,z2,z3,z4,z160,z6])],[(0,[z74,z1,z2,z3,z4,z5,z89]),(0,[z233,z1,z2,z4,z17,z5,z6]),(0,[z1,z2,z392,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z106])],[(0,[z23,z118,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z102,z5,z36,z6]),(0,[z1,z2,z3,z4,z5,z6,z393]),(0,[z233,z1,z2,z3,z21,z5,z6]),(0,[z387,z1,z2,z4,z5,z192,z6]),(0,[z1,z394,z2,z3,z4,z5,z6]),(0,[z1,z2,z395,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z396,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z397])]],
   [[(0,[z79,z1,z2,z3,z4,z5,z80]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z89,z6,z76]),(0,[z399,z1,z2,z3,z4,z5,z6])],[(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z41,z5])],[(0,[z1,z2,z3,z4,z403,z5,z6]),(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z405,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z406]),(0,[z1,z2,z3,z4,z407,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z409,z3,z4,z5,z6]),(0,[z1,z410,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z84]),(0,[z1,z2,z411,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z334]),(0,[z1,z412,z2,z3,z4,z5,z6]),(0,[z1,z413,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z414,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z1,z2,z3,z355,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z415,z6])],[(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z2,z15,z3,z152,z4,z5,z6]),(0,[z1,z2,z3,z205,z17,z5,z6]),(0,[z1,z2,z3,z4,z148,z137,z6]),(0,[z1,z2,z3,z417,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z418,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z419]),(0,[z12,z1,z2,z3,z4,z137,z6])],[(0,[z2,z24,z3,z4,z5,z36,z6]),(0,[z14,z1,z2,z15,z4,z5,z6]),(0,[z420,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z14,z2,z3,z4,z52,z5,z6]),(1,[z1,z2,z3,z4,z277,z6]),(0,[z421,z1,z2,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z6]),(1,[z1,z75,z3,z4,z5,z89]),(0,[z1,z2,z3,z4,z5,z330,z6]),(0,[z1,z2,z3,z41,z5,z6,z93])],[(0,[z1,z2,z15,z4,z5,z6,z107]),(0,[z82,z1,z2,z57,z4,z5,z6]),(0,[z1,z2,z3,z422,z4,z5,z6])],[(0,[z423,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z424]),(0,[z1,z2,z3,z4,z5,z6,z425]),(0,[z1,z136,z2,z3,z180,z4,z6]),(0,[z1,z2,z210,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z426,z5,z6]),(1,[z283,z1,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z61,z6]),(0,[z1,z2,z3,z4,z5,z427,z6])],[(0,[z1,z428,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z429,z5,z6]),(1,[z49,z2,z3,z4,z5,z6]),(0,[z430,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z3,z4,z431,z5,z6])],[(0,[z1,z2,z3,z432,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z129]),(0,[z1,z2,z3,z433,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z80]),(1,[z1,z2,z3,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z434]),(0,[z1,z2,z3,z4,z179,z148,z6]),(0,[z96,z1,z2,z3,z4,z5,z6])],[(0,[z62,z1,z2,z3,z52,z5,z6]),(0,[z1,z435,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z6,z234]),(0,[z1,z2,z3,z436,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z437,z6]),(0,[z1,z2,z3,z438,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z82,z1,z3,z4,z137,z5,z6])]],
   [[(0,[z117,z1,z24,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z403,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z80])],[(0,[z440,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z355,z5,z6]),(0,[z1,z2,z441,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z442,z6])],[(0,[z1,z2,z3,z4,z443,z5,z6]),(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z445])],[(0,[z1,z2,z3,z4,z5,z446,z6]),(0,[z1,z136,z3,z4,z137,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z107]),(0,[z1,z2,z3,z4,z447,z5,z6]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z449,z6])],[(0,[z1,z450,z2,z3,z4,z5,z6]),(1,[z1,z314,z3,z4,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z452,z4,z5,z6])],[(0,[z453,z1,z2,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z114]),(0,[z1,z2,z3,z4,z137,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z454]),(0,[z1,z2,z3,z455,z4,z5,z6])],[(0,[z1,z2,z3,z4,z456,z5,z6]),(0,[z457,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z458,z6]),(0,[z1,z2,z3,z180,z4,z148,z6])],[(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z460,z6]),(0,[z237,z2,z3,z4,z5,z42,z6]),(0,[z12,z1,z2,z181,z4,z5,z6]),(0,[z1,z2,z3,z4,z461,z5,z6])]],
   [[(0,[z35,z2,z24,z3,z4,z5,z6]),(0,[z2,z3,z152,z4,z52,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z89]),(0,[z1,z18,z3,z4,z265,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z1,z2,z3,z4,z5,z106,z89]),(0,[z1,z2,z3,z4,z5,z6,z463]),(0,[z31,z1,z2,z3,z4,z5,z93]),(0,[z464,z1,z2,z3,z4,z5,z6])],[(0,[z23,z1,z2,z3,z4,z5,z6])],[(0,[z1,z18,z88,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z6,z234]),(1,[z233,z1,z2,z17,z5,z6]),(0,[z1,z2,z3,z4,z465,z5,z6]),(0,[z1,z2,z466,z3,z4,z5,z6])],[(0,[z1,z2,z110,z15,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z468,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z3,z4,z469,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z76]),(0,[z1,z470,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z106,z76])],[(0,[z1,z2,z3,z4,z251,z5,z6]),(1,[z1,z2,z3,z4,z5,z330]),(0,[z1,z2,z3,z4,z471,z5,z6])],[(0,[z1,z472,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z473]),(0,[z1,z2,z3,z4,z474,z5,z6]),(0,[z475,z1,z2,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z5,z6,z234])],[(0,[z1,z2,z476,z3,z4,z5,z6]),(0,[z1,z3,z168,z4,z137,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z1,z2,z3,z478,z4,z5,z6])],[],[(0,[z479,z1,z2,z3,z4,z5,z6]),(0,[z1,z18,z54,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z160,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z480]),(0,[z1,z2,z110,z3,z4,z5,z107])],[(0,[z481,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z36,z6,z234]),(0,[z1,z2,z3,z482,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z483]),(0,[z31,z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z484,z4,z5,z6])],[(0,[z1,z2,z485,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z5,z6]),(0,[z1,z486,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z168,z5,z6,z234]),(0,[z1,z2,z3,z4,z192,z6,z234])],[(0,[z1,z118,z3,z4,z265,z5,z6]),(0,[z51,z1,z2,z487,z4,z5,z6]),(0,[z135,z1,z2,z4,z5,z6,z107])],[(0,[z1,z2,z488,z3,z4,z5,z6]),(0,[z1,z287,z2,z3,z4,z5,z6]),(0,[z79,z1,z2,z3,z429,z5,z6]),(1,[z1,z2,z66,z4,z160,z6]),(0,[z1,z489,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z490,z5,z6]),(0,[z491,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z110,z4,z5,z106]),(0,[z1,z2,z3,z4,z148,z5,z6])]],
   [[(0,[z1,z492,z2,z3,z4,z5,z6]),(0,[z1,z2,z493,z3,z4,z5,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z495,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z387,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z496])],[(0,[z151,z1,z2,z3,z4,z5,z6]),(1,[z468,z2,z3,z4,z36,z6]),(0,[z79,z1,z2,z3,z4,z249,z6]),(0,[z1,z2,z3,z497,z4,z5,z6]),(0,[z498,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z103])],[(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z192,z6])],[(0,[z23,z35,z2,z3,z4,z5,z6]),(0,[z387,z1,z2,z3,z4,z192,z6]),(0,[z1,z2,z3,z4,z499,z5,z6])],[(0,[z1,z136,z2,z3,z4,z36,z6]),(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z501,z5,z6]),(0,[z1,z2,z3,z4,z5,z502,z6]),(0,[z1,z2,z3,z503,z4,z5,z6])],[(0,[z504,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z505,z6]),(0,[z1,z2,z3,z4,z5,z6,z506]),(0,[z51,z1,z2,z3,z205,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z6]),(0,[z507,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z180,z4,z5,z76]),(0,[z508,z1,z2,z3,z4,z5,z6])],[(0,[z79,z1,z2,z3,z264,z5,z6]),(0,[z79,z1,z2,z3,z4,z179,z5]),(0,[z509,z1,z2,z3,z4,z5,z6]),(0,[z1,z510,z2,z3,z4,z5,z6]),(0,[z1,z511,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z115,z5,z6]),(0,[z1,z2,z110,z3,z4,z5,z106]),(0,[z1,z2,z3,z206,z4,z5,z6]),(1,[z1,z2,z3,z4,z187,z6])]],
   [[(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z513]),(1,[z1,z2,z20,z4,z5,z6])],[(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z515,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z516,z6]),(0,[z387,z1,z2,z66,z4,z5,z6])],[(0,[z1,z2,z3,z4,z102,z148,z6]),(0,[z1,z2,z3,z4,z517,z5,z6]),(0,[z1,z518,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z361,z4,z5,z6]),(0,[z1,z2,z3,z519,z4,z5,z6]),(0,[z233,z1,z320,z3,z4,z5,z6]),(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z1,z521,z2,z3,z4,z5,z6])],[(0,[z151,z1,z2,z3,z4,z403,z6]),(0,[z1,z2,z3,z4,z522,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z16,z4,z5,z192,z6]),(1,[z1,z2,z361,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z107]),(0,[z1,z523,z2,z3,z4,z5,z6])],[(1,[z23,z118,z3,z4,z5,z6]),(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z525,z4,z5,z6])],[(1,[z1,z2,z45,z4,z5,z6]),(0,[z1,z83,z3,z16,z4,z5,z6]),(0,[z1,z88,z2,z4,z17,z5,z6]),(0,[z1,z2,z3,z526,z4,z5,z6]),(0,[z1,z2,z210,z21,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z316]),(0,[z1,z527,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z528,z6]),(0,[z1,z83,z2,z3,z265,z5,z6]),(0,[z1,z2,z3,z4,z5,z192,z6])],[(0,[z1,z18,z83,z3,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z531,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z2,z3,z4,z273,z6,z76]),(0,[z533,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z88,z54,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z1,z2,z3,z4,z5,z61,z6])],[(0,[z1,z2,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z535,z4,z5,z6]),(0,[z1,z2,z210,z3,z21,z5,z6]),(0,[z1,z2,z536,z3,z4,z5,z6]),(0,[z1,z2,z3,z201,z148,z5,z6])],[(1,[z1,z435,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z537]),(0,[z1,z2,z4,z160,z5,z192,z6]),(0,[z1,z9,z66,z3,z4,z5,z6]),(0,[z1,z2,z538,z3,z4,z5,z6])],[(0,[z1,z2,z3,z539,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z540]),(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z233,z311,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z542,z4,z5,z6])],[(0,[z1,z2,z3,z4,z87,z5,z36]),(0,[z1,z2,z3,z4,z543,z5,z6]),(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z454,z6]),(0,[z1,z2,z3,z4,z179,z5,z93])],[(0,[z1,z118,z3,z4,z5,z6,z76]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z3,z4,z5,z208,z6]),(0,[z1,z2,z3,z4,z179,z5,z106]),(0,[z1,z2,z3,z4,z187,z5,z6]),(0,[z1,z2,z3,z4,z5,z545,z6])],[(0,[z546,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z547]),(0,[z1,z136,z2,z3,z4,z102,z6]),(0,[z1,z2,z3,z4,z548,z5,z6]),(0,[z1,z2,z3,z4,z549,z5,z6])],[(0,[z23,z117,z2,z3,z4,z5,z6]),(1,[z1,z2,z91,z4,z5,z6])]],
   [[(0,[z1,z550,z2,z3,z4,z5,z6]),(0,[z1,z2,z181,z3,z4,z5,z6])],[(0,[z1,z2,z551,z3,z4,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z107]),(0,[z1,z2,z3,z265,z5,z6,z234]),(0,[z1,z2,z3,z4,z5,z552,z6])],[(0,[z51,z1,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z553,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z6]),(1,[z1,z3,z4,z5,z6,z334]),(0,[z1,z2,z3,z180,z4,z179,z5]),(1,[z96,z1,z2,z3,z180,z4])],[(0,[z1,z2,z3,z4,z554,z5,z6]),(0,[z96,z1,z2,z3,z4,z102,z6]),(0,[z1,z2,z3,z4,z5,z106,z80]),(0,[z1,z2,z66,z16,z4,z5,z6]),(0,[z1,z2,z555,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z556,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z174]),(0,[z1,z2,z3,z557,z4,z5,z6]),(0,[z1,z2,z3,z4,z558,z5,z6])],[(0,[z1,z118,z83,z3,z4,z5,z6]),(0,[z559,z1,z2,z3,z4,z5,z6])],[(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z251,z6]),(0,[z561,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z562,z6])],[(0,[z1,z2,z210,z152,z4,z5,z6]),(0,[z1,z2,z3,z4,z160,z36,z6]),(0,[z1,z563,z2,z3,z4,z5,z6]),(0,[z1,z564,z2,z3,z4,z5,z6])],[(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z79,z1,z2,z339,z4,z5,z6]),(0,[z1,z18,z88,z2,z4,z5,z6]),(0,[z1,z2,z3,z567,z4,z5,z6])]],
   [[(1,[z1,z145,z3,z4,z5,z6]),(0,[z1,z88,z2,z4,z5,z6,z107]),(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z107]),(0,[z1,z2,z3,z201,z4,z148,z6])],[(0,[z1,z2,z3,z201,z168,z5,z6]),(0,[z568,z1,z2,z3,z4,z5,z6])],[(0,[z82,z1,z2,z3,z4,z48,z6]),(0,[z1,z299,z2,z3,z4,z5,z6])],[(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z62,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z36,z6]),(0,[z1,z2,z3,z429,z4,z5,z6]),(0,[z1,z2,z3,z570,z4,z5,z6]),(0,[z1,z2,z3,z571,z4,z5,z6])],[(0,[z572,z1,z2,z3,z4,z5,z6]),(0,[z1,z573,z2,z3,z4,z5,z6])],[(0,[z117,z2,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z1,z54,z2,z16,z4,z5,z6]),(0,[z233,z1,z2,z3,z4,z549,z6]),(0,[z1,z2,z3,z4,z574,z5,z6]),(0,[z1,z2,z3,z30,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6])],[(0,[z468,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z168,z4,z5,z6]),(0,[z1,z2,z3,z4,z137,z6,z234]),(0,[z1,z9,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z576])],[(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z82,z70,z2,z3,z4,z5,z6]),(0,[z1,z83,z2,z3,z4,z5,z6]),(0,[z233,z239,z2,z3,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z113,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z5,z6])],[(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z581,z5,z6]),(0,[z151,z1,z88,z2,z4,z5,z6]),(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z582]),(0,[z12,z1,z3,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z583,z6]),(0,[z233,z1,z2,z3,z4,z584,z6]),(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z586])],[(0,[z1,z2,z339,z3,z4,z5,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z588,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z589]),(0,[z1,z2,z3,z4,z5,z42,z107]),(0,[z1,z2,z3,z4,z5,z590,z6]),(0,[z1,z2,z3,z4,z5,z591,z6]),(0,[z96,z1,z2,z3,z180,z4,z6])],[(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z237,z1,z2,z3,z4,z5,z6]),(0,[z1,z88,z2,z66,z4,z5,z6]),(0,[z1,z2,z593,z3,z4,z5,z6])],[(0,[z1,z75,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z594,z6]),(0,[z1,z118,z3,z16,z4,z5,z6]),(0,[z1,z314,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z595,z6])],[(0,[z1,z2,z3,z4,z5,z596,z6]),(1,[z1,z54,z16,z4,z5,z6]),(0,[z1,z597,z2,z3,z4,z5,z6])],[(0,[z1,z24,z3,z4,z265,z5,z6]),(1,[z1,z2,z487,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z36,z6]),(1,[z1,z2,z3,z4,z5,z598]),(1,[z1,z2,z3,z201,z148,z6]),(0,[z1,z599,z2,z3,z4,z5,z6])]],
   [[(0,[z79,z237,z2,z3,z4,z5,z6]),(0,[z1,z2,z210,z16,z4,z5,z6]),(0,[z1,z75,z2,z3,z4,z5,z76])],[(0,[z1,z2,z3,z600,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6])],[(0,[z35,z1,z435,z3,z4,z5,z6]),(0,[z1,z602,z2,z3,z4,z5,z6]),(0,[z1,z2,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z603,z5,z6])],[(0,[z1,z2,z3,z4,z160,z6,z234])],[(0,[z604,z1,z2,z3,z4,z5,z6]),(1,[z237,z2,z3,z4,z5,z42])],[(0,[z1,z2,z3,z4,z5,z6,z605])],[(0,[z1,z2,z3,z606,z4,z5,z6]),(0,[z1,z75,z3,z4,z5,z89,z6]),(0,[z1,z2,z3,z4,z5,z89,z103])],[(0,[z1,z2,z3,z274,z4,z5,z6]),(0,[z607,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z110,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z468,z35,z2,z3,z4,z5,z6]),(0,[z79,z96,z1,z2,z3,z4,z5]),(0,[z1,z608,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z609,z5,z6])],[(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z151,z1,z2,z3,z4,z5,z547]),(0,[z1,z2,z3,z4,z5,z611,z6]),(0,[z1,z2,z3,z4,z179,z41,z5])],[(0,[z1,z2,z3,z4,z612,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z613]),(0,[z1,z2,z3,z4,z264,z5,z6]),(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z6]),(0,[z1,z2,z110,z4,z5,z106,z6])],[(1,[z1,z485,z3,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z16,z4,z265,z5,z6]),(0,[z1,z2,z3,z4,z5,z106,z6])],[(0,[z1,z2,z3,z615,z4,z5,z6]),(0,[z1,z2,z3,z616,z4,z5,z6]),(0,[z1,z617,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z618,z6])],[(0,[z82,z1,z2,z3,z265,z5,z6]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z2,z3,z4,z620,z5,z6])],[(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z622,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z625,z5,z6])],[(0,[z62,z2,z3,z205,z4,z5,z6]),(1,[z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z626,z3,z4,z5,z6]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z628,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z201,z4,z6,z234]),(0,[z1,z2,z3,z629,z4,z5,z6])]],
   [[(1,[z1,z287,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z630]),(1,[z1,z320,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z454]),(0,[z1,z2,z3,z4,z5,z6,z202]),(0,[z1,z2,z3,z201,z4,z558,z5])],[(0,[z1,z631,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z5,z6]),(1,[z26,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z93])],[(0,[z1,z2,z3,z4,z632,z5,z6]),(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z635,z5,z6]),(1,[z1,z2,z3,z4,z273,z6]),(0,[z636,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z637,z5,z6]),(1,[z1,z136,z3,z4,z137,z6]),(0,[z1,z2,z3,z4,z5,z638,z6]),(0,[z96,z1,z2,z3,z180,z4,z5])],[(0,[z1,z2,z164,z3,z4,z5,z6]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z234]),(0,[z1,z2,z3,z4,z640,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z78]),(1,[z14,z2,z15,z4,z5,z6]),(0,[z1,z2,z641,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z547,z6]),(0,[z642,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z487,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z127]),(0,[z1,z136,z2,z3,z4,z208,z6]),(0,[z1,z2,z643,z3,z4,z5,z6]),(0,[z1,z2,z3,z180,z4,z5,z89])],[(0,[z1,z118,z2,z3,z4,z5,z6]),(0,[z1,z24,z3,z4,z5,z6,z76]),(1,[z1,z2,z3,z4,z5,z238])]],
   [[(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z1,z2,z3,z4,z5,z598,z6])],[(0,[z1,z2,z3,z4,z5,z645,z6]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z647,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z93,z76]),(1,[z311,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z584,z6]),(0,[z1,z2,z3,z4,z5,z6,z648]),(0,[z1,z2,z3,z4,z649,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z650])],[(0,[z1,z2,z3,z4,z124,z5,z6]),(0,[z651,z1,z2,z3,z4,z5,z6]),(0,[z468,z1,z2,z3,z4,z36,z6]),(0,[z237,z1,z2,z3,z4,z5,z42]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z653,z6])],[(0,[z1,z2,z3,z4,z654,z5,z6]),(0,[z14,z1,z88,z2,z4,z5,z6]),(0,[z1,z655,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z179,z5,z107])],[(0,[z96,z1,z2,z3,z4,z36,z6]),(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z114]),(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z1,z658,z2,z3,z4,z5,z6])],[(0,[z1,z2,z66,z4,z160,z5,z6]),(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z206,z5,z6])],[(0,[z1,z118,z2,z3,z4,z5,z129]),(0,[z1,z2,z3,z659,z4,z5,z6]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z660,z6]),(0,[z1,z661,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z662,z5,z6]),(0,[z1,z2,z3,z4,z179,z6,z103]),(0,[z1,z2,z3,z4,z663,z5,z6])],[(0,[z1,z54,z2,z3,z4,z5,z84]),(0,[z82,z1,z3,z4,z265,z5,z6]),(0,[z135,z1,z299,z3,z4,z5,z6]),(0,[z664,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z135,z1,z95,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z666,z6]),(0,[z51,z1,z164,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z667,z5,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z598]),(0,[z1,z136,z2,z3,z4,z179,z6]),(0,[z1,z2,z3,z4,z5,z669,z6]),(0,[z233,z1,z2,z3,z4,z5,z174]),(0,[z135,z1,z2,z110,z4,z5,z6]),(0,[z670,z1,z2,z3,z4,z5,z6])],[(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z340,z6]),(0,[z1,z2,z3,z4,z672,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z80]),(0,[z1,z2,z3,z4,z5,z6,z673]),(0,[z1,z2,z3,z4,z5,z6,z674])],[(0,[z675,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z676,z5,z6]),(0,[z1,z3,z16,z4,z5,z6,z76]),(1,[z1,z2,z3,z206,z5,z93])],[(0,[z1,z2,z3,z677,z4,z5,z6]),(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z679,z3,z4,z5,z6])],[(0,[z1,z2,z3,z680,z4,z5,z6]),(0,[z151,z2,z3,z152,z4,z5,z6]),(0,[z1,z2,z3,z681,z4,z5,z6]),(0,[z1,z2,z3,z4,z265,z5,z6]),(0,[z1,z2,z3,z682,z4,z5,z6])],[(0,[z1,z2,z3,z683,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z684]),(0,[z1,z2,z3,z4,z5,z6,z685]),(0,[z82,z1,z2,z418,z4,z5,z6]),(0,[z1,z2,z211,z3,z4,z5,z6])],[(0,[z1,z2,z3,z205,z21,z5,z6]),(1,[z1,z2,z3,z4,z92,z6]),(0,[z1,z2,z3,z4,z686,z5,z6]),(0,[z1,z2,z418,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z160,z148,z6]),(0,[z28,z1,z2,z3,z201,z5,z6]),(0,[z1,z2,z3,z180,z4,z6,z103])]],
   [[(1,[z1,z2,z3,z4,z67,z6]),(0,[z1,z687,z2,z3,z4,z5,z6]),(1,[z1,z303,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z41,z5])],[(0,[z1,z2,z3,z4,z5,z6,z688]),(0,[z1,z2,z3,z689,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z690]),(0,[z691,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z340]),(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z2,z3,z4,z692,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z694,z4,z5,z6]),(1,[z1,z2,z3,z4,z549,z6]),(1,[z1,z2,z3,z4,z558,z5]),(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z696,z1,z2,z3,z4,z5,z6])],[(0,[z468,z1,z2,z3,z4,z102,z6]),(0,[z697,z1,z2,z3,z4,z5,z6]),(1,[z82,z1,z3,z265,z5,z6]),(0,[z1,z2,z21,z4,z17,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z698])],[(0,[z1,z2,z3,z4,z5,z699,z6]),(0,[z1,z2,z3,z4,z5,z700,z6]),(0,[z1,z2,z3,z4,z701,z5,z6]),(0,[z1,z702,z2,z3,z4,z5,z6]),(1,[z239,z2,z3,z4,z5,z6])],[(0,[z151,z1,z485,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z703,z5,z6]),(0,[z704,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z168,z4,z265,z5,z6]),(0,[z1,z2,z705,z3,z4,z5,z6]),(0,[z233,z1,z211,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z584,z6]),(0,[z1,z2,z66,z3,z4,z160,z6]),(0,[z1,z2,z3,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z82,z1,z3,z115,z5,z6]),(0,[z1,z2,z4,z707,z5,z6]),(0,[z283,z1,z3,z4,z5,z708]),(0,[z1,z2,z3,z4,z179,z698])],[(0,[z1,z2,z3,z709,z5,z6]),(0,[z1,z2,z3,z4,z5,z710]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z96,z1,z2,z3,z4,z87]),(0,[z1,z435,z3,z4,z5,z713]),(0,[z294,z1,z2,z3,z6,z234])],[(0,[z1,z485,z3,z4,z5,z6]),(0,[z23,z118,z45,z4,z5,z6]),(0,[z1,z320,z3,z4,z584,z6])],[(0,[z151,z2,z152,z4,z5,z6]),(0,[z1,z2,z3,z124,z245,z6]),(0,[z1,z2,z3,z4,z714,z6])],[(0,[z1,z158,z3,z124,z5,z6]),(0,[z1,z2,z715,z4,z5,z6])],[(0,[z569,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z4,z716,z5]),(0,[z1,z2,z20,z4,z102,z6]),(0,[z1,z2,z3,z4,z717,z5]),(0,[z718,z2,z3,z4,z5,z6])],[(0,[z13,z2,z3,z4,z5,z6]),(0,[z82,z1,z3,z265,z5,z238])],[(0,[z1,z287,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z719,z6]),(0,[z1,z2,z3,z4,z720,z6]),(0,[z1,z2,z721,z4,z5,z6]),(0,[z1,z3,z4,z722,z208,z6]),(0,[z1,z723,z3,z4,z5,z6])]],
   [[(0,[z26,z2,z3,z4,z5,z6]),(0,[z1,z2,z724,z4,z5,z6]),(0,[z1,z3,z4,z5,z725,z76])],[(0,[z1,z2,z726,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z3,z4,z728,z6]),(0,[z1,z2,z3,z729,z5,z6]),(0,[z1,z164,z3,z4,z277,z6]),(0,[z1,z2,z3,z4,z273,z6]),(0,[z1,z2,z538,z4,z5,z107])],[(0,[z23,z118,z3,z4,z67,z6]),(0,[z1,z314,z3,z4,z5,z127]),(0,[z257,z1,z2,z17,z5,z6]),(0,[z1,z18,z702,z4,z5,z6]),(0,[z1,z136,z3,z4,z137,z6]),(0,[z12,z1,z3,z4,z722,z6]),(0,[z1,z730,z3,z4,z5,z6])],[(0,[z12,z24,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z731,z6]),(0,[z1,z2,z3,z4,z5,z174]),(0,[z1,z732,z3,z4,z5,z6]),(0,[z1,z2,z3,z733,z5,z6])],[(0,[z12,z1,z3,z4,z666,z6]),(0,[z23,z118,z3,z4,z5,z340]),(0,[z14,z2,z15,z4,z5,z6]),(0,[z1,z2,z487,z205,z5,z6]),(0,[z468,z119,z2,z3,z4,z36]),(0,[z1,z2,z339,z4,z249,z6]),(0,[z12,z1,z3,z4,z48,z6]),(0,[z1,z2,z734,z4,z5,z6])],[(0,[z151,z2,z152,z4,z403,z6]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z51,z314,z3,z52,z5,z6]),(0,[z51,z2,z487,z52,z5,z6]),(0,[z1,z2,z3,z4,z87,z148]),(0,[z1,z2,z3,z220,z148,z6]),(0,[z1,z211,z210,z4,z5,z6])],[(0,[z164,z3,z4,z52,z5,z6]),(0,[z1,z2,z3,z264,z5,z80]),(0,[z1,z2,z210,z250,z5,z6]),(0,[z12,z1,z57,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z6]),(0,[z239,z2,z4,z17,z5,z6])],[(0,[z1,z2,z736,z4,z5,z6]),(0,[z1,z2,z3,z737,z5,z6]),(0,[z239,z2,z3,z21,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z340,z76]),(0,[z311,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z738]),(0,[z624,z2,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z257,z1,z3,z265,z5,z6]),(0,[z283,z1,z3,z4,z208,z6])],[(0,[z1,z2,z3,z4,z739,z5]),(0,[z12,z1,z2,z3,z4,z87]),(0,[z1,z2,z3,z4,z740,z5])],[(0,[z1,z2,z339,z264,z5,z6]),(0,[z1,z2,z3,z115,z208,z6]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z741,z3,z4,z5,z6])],[(0,[z1,z2,z57,z4,z5,z238]),(0,[z1,z2,z181,z4,z5,z126])],[(0,[z2,z3,z742,z52,z5,z6]),(0,[z1,z2,z3,z4,z5,z743]),(0,[z1,z2,z91,z4,z92,z6]),(0,[z1,z290,z16,z4,z5,z6]),(0,[z744,z2,z3,z4,z5,z6]),(0,[z13,z2,z3,z4,z5,z598]),(0,[z1,z745,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z746])],[(0,[z1,z2,z3,z747,z5,z6]),(0,[z1,z2,z181,z115,z5,z6]),(0,[z12,z1,z3,z355,z208,z6]),(0,[z74,z1,z3,z4,z5,z725]),(0,[z1,z608,z3,z4,z5,z89]),(0,[z31,z1,z2,z3,z41,z5])],[(0,[z1,z748,z3,z4,z5,z6]),(1,[z1,z16,z4,z5,z84]),(0,[z26,z2,z3,z4,z5,z598])],[(0,[z1,z3,z30,z4,z5,z316]),(0,[z1,z2,z3,z4,z187,z93])]],
   [[(0,[z1,z2,z3,z4,z749,z5]),(0,[z1,z45,z4,z265,z5,z6]),(0,[z1,z750,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z752,z3,z4,z5,z6]),(0,[z1,z753,z3,z4,z5,z6]),(0,[z1,z564,z88,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z754])],[(0,[z755,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z277,z64]),(0,[z1,z211,z3,z4,z5,z6]),(0,[z82,z49,z3,z265,z5,z6]),(0,[z475,z1,z2,z3,z6,z234])],[(0,[z512,z1,z3,z4,z5,z76]),(0,[z1,z88,z2,z4,z5,z78]),(0,[z1,z756,z3,z4,z5,z6]),(0,[z1,z757,z3,z4,z5,z6]),(0,[z1,z2,z3,z6,z758,z234])],[(0,[z79,z2,z3,z4,z5,z80]),(0,[z1,z2,z3,z4,z759,z6]),(0,[z12,z1,z181,z4,z208,z6]),(0,[z1,z2,z3,z4,z179,z126]),(0,[z283,z1,z3,z4,z179,z6]),(0,[z1,z2,z3,z206,z760,z5])],[(0,[z1,z761,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z762,z5]),(0,[z457,z1,z2,z3,z41,z5]),(0,[z1,z239,z2,z17,z5,z6])],[(0,[z1,z145,z3,z4,z92,z6]),(0,[z96,z1,z2,z3,z4,z249]),(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z88,z764,z4,z5,z6]),(0,[z1,z2,z3,z115,z179,z6])],[(0,[z1,z2,z765,z4,z5,z6]),(0,[z1,z2,z225,z4,z5,z6]),(0,[z12,z1,z3,z4,z27,z6])],[(0,[z1,z2,z3,z4,z67,z6]),(0,[z1,z303,z3,z4,z5,z6]),(0,[z156,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z233,z1,z2,z17,z5,z174])]],
   [[(0,[z1,z145,z3,z4,z5,z340]),(0,[z1,z145,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z89]),(0,[z1,z2,z767,z4,z5,z6]),(0,[z1,z2,z768,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z769]),(0,[z1,z75,z45,z4,z5,z6]),(0,[z1,z3,z770,z4,z5,z6]),(0,[z1,z2,z487,z52,z5,z6]),(0,[z79,z2,z3,z429,z5,z80]),(0,[z1,z2,z16,z4,z5,z316])],[(0,[z1,z2,z3,z771,z5,z6]),(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z773,z3,z4,z5,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z3,z4,z549,z6]),(0,[z1,z2,z4,z776,z192,z6]),(0,[z1,z2,z3,z4,z558,z5])],[(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z88,z2,z124,z5,z6]),(0,[z1,z2,z113,z4,z5,z64]),(0,[z1,z778,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z76])],[(0,[z627,z118,z3,z4,z5,z6]),(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z489,z3,z168,z5,z6])],[(0,[z283,z1,z768,z4,z5,z6]),(0,[z1,z3,z780,z4,z5,z6])],[(0,[z1,z2,z3,z781,z5,z6]),(0,[z1,z782,z3,z4,z5,z6])],[(0,[z1,z287,z16,z4,z5,z6]),(0,[z1,z783,z3,z4,z5,z6]),(0,[z1,z9,z3,z4,z5,z6]),(0,[z784,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z155])]],
   [[(0,[z1,z2,z3,z4,z5,z785]),(0,[z1,z2,z3,z4,z5,z786]),(0,[z319,z1,z2,z4,z5,z107]),(0,[z1,z2,z3,z4,z5,z787]),(0,[z82,z1,z57,z265,z5,z6]),(0,[z788,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z742,z5,z6]),(0,[z1,z2,z3,z4,z251,z6]),(0,[z1,z2,z418,z4,z251,z6]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z387,z1,z2,z4,z776,z6]),(0,[z317,z1,z2,z3,z180,z4])],[(0,[z1,z2,z790,z4,z5,z6]),(0,[z1,z2,z3,z4,z140,z64]),(0,[z1,z2,z791,z4,z5,z6]),(0,[z1,z2,z3,z4,z792,z6]),(0,[z13,z2,z3,z4,z36,z6]),(0,[z1,z2,z793,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z103]),(0,[z1,z320,z3,z4,z5,z174]),(1,[z1,z2,z3,z4,z746])],[(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z113,z4,z5,z6]),(0,[z1,z3,z30,z4,z5,z6]),(0,[z1,z2,z3,z115,z5,z126]),(0,[z1,z252,z2,z4,z5,z107]),(0,[z135,z1,z299,z4,z5,z107])],[(0,[z495,z24,z3,z4,z5,z6]),(0,[z12,z1,z3,z4,z208,z6]),(0,[z1,z2,z3,z4,z722,z6]),(0,[z795,z1,z3,z4,z5,z6])],[(0,[z1,z2,z113,z4,z277,z6]),(0,[z1,z2,z796,z4,z5,z6]),(0,[z797,z2,z3,z4,z5,z6])],[(0,[z1,z47,z3,z4,z5,z6]),(0,[z1,z798,z3,z4,z5,z6]),(0,[z1,z2,z799,z4,z5,z6]),(0,[z1,z2,z3,z264,z5,z6]),(0,[z1,z800,z435,z4,z5,z6]),(0,[z1,z2,z3,z429,z249,z6]),(0,[z1,z2,z3,z4,z48,z6]),(0,[z1,z2,z95,z4,z5,z107]),(0,[z1,z2,z801,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z802]),(0,[z1,z2,z3,z4,z5,z803]),(0,[z49,z2,z3,z4,z251,z6]),(0,[z1,z2,z3,z201,z548,z6]),(0,[z311,z320,z3,z4,z5,z6]),(0,[z1,z211,z3,z4,z5,z330]),(0,[z1,z2,z3,z201,z558,z148])]],
   [[(0,[z1,z2,z3,z4,z5,z804]),(0,[z1,z45,z4,z5,z6,z76]),(0,[z1,z158,z3,z4,z245,z6]),(0,[z1,z805,z3,z4,z5,z6]),(0,[z13,z2,z20,z4,z5,z6]),(0,[z639,z1,z2,z3,z180,z4]),(0,[z1,z2,z3,z4,z5,z202])],[(0,[z35,z2,z3,z4,z67,z6]),(0,[z1,z806,z2,z4,z5,z6]),(0,[z1,z807,z3,z4,z5,z6]),(0,[z1,z808,z3,z4,z5,z6])],[(0,[z1,z18,z287,z4,z5,z6]),(0,[z1,z2,z3,z274,z5,z6]),(0,[z1,z158,z3,z4,z403,z6]),(0,[z1,z2,z3,z4,z140,z6]),(0,[z568,z2,z3,z205,z5,z6]),(0,[z1,z2,z3,z4,z809,z6]),(0,[z26,z2,z20,z4,z5,z6]),(0,[z1,z521,z3,z4,z5,z89]),(0,[z810,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z179,z103])],[(0,[z70,z2,z3,z4,z5,z6]),(0,[z1,z811,z3,z4,z5,z6]),(0,[z175,z2,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z812,z6]),(0,[z12,z1,z3,z115,z208,z6])],[(0,[z1,z2,z813,z4,z5,z6]),(0,[z1,z2,z3,z4,z814,z6]),(0,[z49,z2,z3,z4,z48,z6]),(0,[z1,z2,z3,z4,z815,z6]),(0,[z1,z2,z3,z4,z816,z6]),(0,[z31,z1,z2,z3,z760,z5])],[(0,[z817,z2,z3,z4,z5,z6])],[(0,[z621,z1,z2,z17,z5,z6])],[(0,[z1,z2,z818,z4,z5,z6]),(0,[z1,z819,z3,z4,z5,z6]),(0,[z2,z152,z52,z17,z5,z6]),(0,[z1,z18,z88,z4,z5,z6]),(0,[z1,z299,z3,z4,z5,z6]),(0,[z1,z18,z510,z4,z5,z6]),(0,[z1,z2,z3,z4,z820,z6])]],
   [[(0,[z128,z2,z152,z4,z5,z6]),(0,[z1,z821,z3,z4,z5,z6]),(0,[z1,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z822])],[(0,[z1,z2,z3,z4,z823,z6]),(0,[z1,z314,z113,z4,z5,z6]),(1,[z1,z3,z4,z5,z725])],[(0,[z1,z485,z3,z4,z5,z547]),(0,[z1,z2,z4,z5,z6,z824]),(0,[z237,z1,z2,z3,z4,z8]),(0,[z1,z764,z54,z4,z5,z6]),(0,[z1,z628,z16,z4,z5,z6]),(0,[z12,z26,z3,z4,z208,z6]),(0,[z1,z2,z181,z355,z5,z6])],[(0,[z1,z2,z3,z4,z825,z6]),(0,[z151,z2,z152,z4,z5,z547]),(0,[z1,z2,z3,z4,z826,z5]),(0,[z14,z2,z570,z4,z5,z6]),(0,[z1,z2,z4,z5,z106,z822]),(0,[z1,z2,z3,z131,z5,z93])],[(0,[z1,z2,z3,z274,z403,z6]),(0,[z159,z1,z2,z3,z6,z234]),(0,[z1,z2,z3,z4,z5,z114]),(0,[z827,z2,z3,z4,z5,z6])],[(0,[z117,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z828,z5,z6]),(0,[z1,z57,z4,z137,z5,z6])],[(0,[z23,z435,z3,z4,z5,z6]),(0,[z1,z2,z3,z124,z5,z6]),(0,[z82,z1,z3,z829,z5,z6]),(0,[z1,z2,z4,z160,z776,z6]),(0,[z283,z830,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z708])],[(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z91,z4,z5,z42]),(0,[z1,z585,z16,z4,z5,z6])]],
   [[(0,[z1,z287,z2,z4,z5,z340]),(0,[z1,z314,z3,z4,z140,z6]),(0,[z1,z2,z832,z4,z5,z6]),(0,[z1,z2,z3,z484,z41,z5])],[(0,[z1,z24,z20,z4,z5,z6]),(0,[z1,z833,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z834]),(0,[z1,z320,z3,z4,z549,z6]),(0,[z1,z835,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z188,z6]),(0,[z1,z2,z3,z836,z5,z6]),(0,[z1,z2,z837,z4,z5,z6]),(0,[z440,z1,z2,z17,z5,z6]),(0,[z838,z2,z3,z4,z5,z6])],[(0,[z263,z24,z3,z4,z5,z6]),(0,[z14,z2,z289,z4,z5,z6]),(0,[z515,z1,z2,z3,z41,z5]),(0,[z839,z2,z3,z4,z5,z6]),(0,[z239,z320,z3,z4,z5,z6])],[(0,[z1,z840,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z841,z6]),(0,[z1,z2,z3,z4,z5,z842])],[(0,[z1,z2,z843,z3,z4,z5]),(0,[z23,z755,z3,z4,z5,z6]),(0,[z668,z118,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z3,z16,z4,z5,z84]),(0,[z283,z1,z3,z4,z137,z6]),(0,[z1,z2,z3,z148,z6,z758])],[(0,[z1,z2,z339,z4,z5,z6]),(0,[z1,z846,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z847,z6]),(0,[z1,z211,z4,z17,z5,z6]),(0,[z1,z9,z3,z4,z5,z454]),(0,[z1,z2,z3,z4,z848,z6])],[(0,[z14,z2,z849,z4,z5,z6]),(0,[z1,z2,z850,z4,z5,z6]),(0,[z1,z2,z3,z115,z137,z6]),(0,[z1,z9,z66,z4,z160,z6]),(0,[z830,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z851,z6])]],
   [[(0,[z1,z2,z3,z124,z403,z6]),(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z2,z3,z4,z5,z853])],[(0,[z1,z2,z3,z854,z4,z5]),(0,[z1,z3,z4,z5,z6,z855]),(0,[z665,z1,z2,z4,z192,z6]),(0,[z1,z2,z3,z168,z48,z6]),(0,[z1,z2,z3,z4,z584,z174]),(0,[z1,z3,z856,z4,z5,z6])],[(0,[z1,z164,z3,z4,z5,z6]),(0,[z1,z2,z3,z857,z5,z6]),(0,[z311,z2,z3,z4,z549,z6]),(0,[z1,z858,z3,z4,z5,z6]),(0,[z1,z3,z30,z4,z5,z454])],[(0,[z507,z2,z3,z4,z102,z6])],[(0,[z1,z2,z859,z4,z5,z6]),(0,[z1,z2,z339,z429,z5,z6]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z1,z2,z3,z4,z861,z6])],[(0,[z1,z2,z487,z4,z5,z127]),(0,[z1,z2,z3,z4,z862,z6]),(0,[z1,z2,z3,z4,z863,z6]),(0,[z1,z3,z16,z4,z5,z126]),(0,[z864,z2,z3,z4,z5,z6])],[(0,[z1,z271,z16,z4,z5,z6]),(0,[z283,z1,z3,z265,z5,z6]),(0,[z1,z2,z3,z278,z5,z93]),(0,[z311,z2,z3,z4,z584,z6]),(0,[z1,z865,z3,z4,z5,z6])],[(0,[z1,z2,z866,z4,z5,z6]),(0,[z1,z3,z16,z4,z5,z129]),(0,[z1,z485,z3,z4,z5,z78]),(0,[z1,z88,z2,z4,z245,z6]),(0,[z1,z2,z867,z4,z5,z6]),(0,[z1,z3,z16,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z4,z5,z776,z6])]],
   [[(0,[z1,z2,z869,z4,z5,z6]),(0,[z1,z279,z3,z4,z137,z6]),(0,[z1,z2,z870,z4,z5,z6]),(0,[z1,z2,z45,z4,z5,z340]),(0,[z1,z119,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z871]),(0,[z1,z2,z3,z355,z5,z126]),(0,[z1,z872,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z2,z181,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z758])],[(0,[z1,z368,z16,z4,z5,z6]),(0,[z1,z874,z3,z4,z5,z6]),(0,[z62,z2,z487,z4,z5,z6]),(0,[z1,z66,z30,z4,z160,z6])],[(0,[z23,z287,z118,z4,z5,z6]),(1,[z1,z3,z4,z722,z6]),(0,[z283,z797,z3,z4,z5,z6]),(0,[z1,z2,z3,z760,z5,z6])],[(0,[z1,z2,z3,z4,z875,z6]),(0,[z1,z876,z3,z4,z5,z6]),(0,[z79,z2,z91,z4,z5,z80]),(0,[z1,z2,z3,z4,z877,z6]),(0,[z1,z2,z3,z4,z48,z238]),(0,[z1,z2,z3,z878,z5,z6]),(0,[z879,z2,z3,z4,z5,z6]),(0,[z1,z880,z3,z4,z5,z6]),(0,[z1,z2,z881,z4,z5,z6])],[(0,[z1,z2,z3,z882,z5,z6]),(0,[z1,z2,z883,z4,z5,z6]),(0,[z1,z118,z20,z4,z5,z6]),(0,[z1,z303,z3,z4,z92,z6]),(0,[z1,z3,z4,z5,z722,z6]),(0,[z387,z1,z2,z4,z192,z6]),(1,[z1,z95,z4,z5,z107])],[(0,[z12,z1,z20,z4,z208,z6]),(0,[z1,z3,z4,z5,z6,z884]),(0,[z885,z2,z3,z4,z5,z6]),(0,[z1,z9,z3,z4,z5,z316])],[(0,[z1,z9,z88,z4,z5,z6]),(0,[z1,z886,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z41,z187])]],
   [[(0,[z1,z164,z487,z4,z5,z6]),(0,[z51,z2,z3,z742,z5,z6]),(0,[z1,z303,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z887,z6]),(0,[z1,z2,z3,z4,z888,z6])],[(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z2,z890,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z238]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z283,z1,z881,z4,z5,z6])],[(0,[z892,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z64]),(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z16,z4,z686,z5,z6]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z895,z3,z4,z5,z6])],[],[(0,[z1,z145,z3,z4,z5,z76]),(0,[z1,z2,z588,z4,z5,z106])],[(0,[z1,z896,z3,z4,z5,z6]),(0,[z79,z145,z3,z4,z5,z80]),(0,[z897,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z898])],[(0,[z1,z2,z3,z4,z899,z6]),(0,[z239,z2,z3,z4,z549,z6]),(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z901,z3,z4,z5,z6])],[(0,[z1,z2,z3,z902,z5,z6]),(0,[z1,z2,z3,z4,z5,z84]),(0,[z1,z2,z3,z4,z903,z6]),(0,[z1,z2,z181,z4,z5,z598]),(0,[z1,z75,z3,z4,z5,z725]),(0,[z1,z2,z3,z4,z5,z904]),(0,[z1,z2,z3,z4,z179,z552])]],
   [[(0,[z151,z485,z152,z4,z5,z6]),(0,[z905,z2,z3,z4,z5,z6]),(0,[z74,z1,z3,z4,z5,z76]),(0,[z1,z2,z3,z4,z906,z6])],[(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z2,z3,z4,z5,z908]),(0,[z79,z1,z2,z3,z4,z8]),(0,[z49,z3,z4,z265,z5,z6])],[(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z628,z3,z4,z5,z76]),(0,[z239,z2,z3,z4,z584,z6]),(0,[z1,z910,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z911,z6]),(0,[z1,z2,z4,z5,z822,z107])],[(0,[z755,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z912]),(0,[z1,z2,z3,z4,z277,z6]),(0,[z1,z913,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z6,z758])],[(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z2,z3,z4,z915,z6])],[(0,[z1,z916,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z917,z6]),(0,[z1,z2,z91,z264,z5,z6]),(0,[z918,z2,z3,z4,z5,z6]),(0,[z283,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z2,z920,z4,z5,z6])]],
   [[(0,[z24,z3,z4,z654,z5,z6]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z314,z3,z4,z5,z64]),(0,[z1,z2,z487,z4,z5,z64]),(0,[z1,z2,z3,z429,z5,z6]),(0,[z96,z1,z2,z3,z436,z4]),(0,[z49,z2,z418,z4,z5,z6]),(0,[z1,z2,z922,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z129]),(0,[z1,z923,z3,z4,z5,z6]),(0,[z1,z162,z16,z4,z5,z6]),(0,[z82,z1,z3,z265,z48,z6]),(0,[z1,z2,z3,z115,z5,z6]),(0,[z1,z3,z924,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z925]),(0,[z1,z2,z3,z4,z245,z6]),(0,[z642,z2,z3,z52,z5,z6]),(0,[z1,z926,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z927]),(0,[z26,z18,z3,z4,z5,z6])],[(0,[z1,z158,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z6]),(0,[z1,z2,z3,z4,z5,z928]),(0,[z1,z181,z16,z4,z5,z6]),(0,[z171,z1,z2,z4,z192,z6]),(0,[z929,z2,z3,z4,z5,z6]),(0,[z1,z75,z225,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z930])],[(0,[z1,z2,z3,z4,z403,z6]),(0,[z1,z931,z3,z4,z5,z6])],[(0,[z1,z2,z932,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z933]),(0,[z1,z75,z3,z4,z5,z340]),(0,[z228,z2,z152,z4,z5,z6]),(0,[z1,z2,z3,z4,z934,z6]),(0,[z1,z2,z935,z4,z5,z6]),(0,[z283,z1,z3,z115,z5,z6]),(0,[z1,z2,z3,z4,z936,z6])],[(0,[z1,z2,z3,z4,z937,z6]),(0,[z2,z3,z4,z67,z36,z6]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z939,z5,z6]),(0,[z1,z2,z3,z4,z940,z6]),(0,[z1,z2,z3,z941,z5,z6]),(0,[z1,z3,z225,z4,z5,z76]),(0,[z1,z2,z3,z4,z942,z5])]],
   [[(0,[z1,z314,z3,z4,z5,z6]),(0,[z23,z118,z3,z4,z188,z6]),(0,[z1,z2,z152,z4,z5,z78]),(0,[z1,z145,z3,z264,z5,z6]),(0,[z1,z2,z3,z4,z5,z943]),(0,[z149,z1,z3,z4,z5,z76]),(0,[z1,z18,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z944,z6]),(0,[z1,z136,z3,z4,z722,z6]),(0,[z1,z945,z3,z4,z5,z6])],[],[(0,[z1,z946,z3,z4,z5,z6]),(1,[z2,z849,z4,z5,z6]),(0,[z2,z3,z849,z4,z5,z6]),(0,[z1,z314,z3,z4,z277,z6]),(0,[z1,z2,z487,z4,z277,z6]),(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z16,z4,z5,z6,z84]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z73,z1,z2,z3,z6,z234])],[(1,[z755,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z949])],[(0,[z1,z2,z950,z4,z5,z6]),(0,[z509,z24,z3,z4,z5,z6]),(0,[z1,z9,z16,z4,z5,z6]),(0,[z1,z2,z951,z4,z5,z6]),(0,[z1,z952,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z179,z385])],[(0,[z1,z2,z3,z4,z953,z6]),(0,[z222,z2,z3,z4,z36,z6]),(0,[z1,z225,z4,z5,z6,z76]),(0,[z1,z2,z3,z954,z5,z6]),(0,[z1,z3,z955,z4,z5,z6]),(0,[z1,z2,z3,z4,z760,z5]),(0,[z1,z2,z3,z180,z4,z746])],[(0,[z1,z2,z3,z4,z5,z956]),(0,[z1,z2,z3,z124,z5,z547]),(0,[z604,z1,z2,z4,z5,z107]),(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z2,z57,z4,z48,z6]),(0,[z1,z3,z4,z829,z5,z6]),(0,[z311,z2,z3,z4,z5,z174]),(0,[z233,z1,z320,z17,z5,z6])],[(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z136,z2,z3,z4,z87]),(0,[z959,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z960,z5,z6]),(0,[z82,z1,z3,z265,z5,z114]),(0,[z1,z3,z4,z137,z6,z197]),(0,[z1,z961,z3,z4,z5,z6])]],
   [[(0,[z13,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z962,z6]),(0,[z1,z2,z3,z963,z4,z5]),(0,[z2,z3,z4,z742,z5,z6]),(0,[z1,z2,z341,z4,z160,z6]),(0,[z1,z2,z3,z4,z5,z330]),(0,[z1,z964,z3,z4,z5,z6]),(0,[z1,z95,z4,z5,z6,z107])],[(0,[z1,z2,z152,z124,z5,z6]),(0,[z312,z2,z3,z4,z36,z6]),(1,[z2,z3,z4,z5,z965]),(0,[z1,z2,z3,z4,z5,z55])],[(0,[z1,z2,z3,z4,z966,z6]),(0,[z1,z3,z4,z137,z722,z6]),(0,[z1,z154,z3,z4,z5,z89])],[(0,[z1,z2,z3,z967,z5,z6]),(0,[z1,z2,z91,z4,z5,z80]),(0,[z70,z2,z57,z4,z5,z6]),(0,[z1,z968,z3,z4,z5,z6])],[(0,[z79,z2,z3,z4,z5,z965]),(0,[z1,z3,z4,z137,z48,z6]),(0,[z1,z2,z3,z4,z5,z969]),(0,[z1,z2,z3,z4,z776,z6])],[(0,[z1,z970,z3,z4,z5,z6]),(0,[z479,z1,z2,z4,z5,z107]),(0,[z237,z349,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z971,z6]),(0,[z12,z1,z3,z4,z208,z598])],[(0,[z1,z2,z972,z4,z5,z6]),(0,[z440,z2,z3,z52,z5,z6]),(0,[z1,z3,z4,z5,z6,z973])],[(0,[z151,z563,z2,z4,z5,z6]),(0,[z1,z2,z974,z4,z5,z6]),(0,[z1,z2,z3,z4,z975,z6]),(0,[z1,z211,z3,z4,z5,z174]),(0,[z1,z976,z3,z4,z5,z6])]],
   [[(0,[z1,z24,z3,z4,z8,z6]),(0,[z13,z2,z3,z4,z67,z6]),(0,[z1,z977,z3,z4,z5,z6]),(0,[z49,z83,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z978,z6]),(0,[z1,z2,z3,z201,z148,z202])],[(0,[z1,z2,z3,z979,z5,z6]),(0,[z118,z755,z3,z4,z5,z6]),(0,[z1,z2,z16,z4,z5,z78]),(0,[z621,z2,z152,z4,z5,z6]),(0,[z1,z435,z3,z4,z5,z980]),(0,[z1,z2,z3,z4,z48,z114]),(0,[z981,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z982,z6]),(0,[z1,z2,z487,z4,z140,z6]),(0,[z12,z1,z3,z4,z359,z6])],[(0,[z1,z2,z3,z497,z5,z93]),(0,[z1,z18,z764,z4,z5,z6]),(0,[z1,z2,z57,z4,z5,z114]),(0,[z311,z211,z3,z4,z5,z6])],[(0,[z468,z2,z3,z4,z36,z6]),(0,[z1,z3,z983,z4,z5,z6]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z1,z2,z3,z985,z5,z6])],[(0,[z1,z2,z3,z4,z986,z6]),(0,[z1,z2,z3,z987,z4,z5])],[(0,[z1,z88,z2,z4,z5,z84]),(0,[z1,z550,z16,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z114]),(0,[z1,z2,z3,z707,z5,z6]),(0,[z1,z988,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z989,z4,z5,z6]),(0,[z1,z2,z3,z4,z990,z6]),(0,[z1,z2,z3,z4,z991,z6]),(0,[z1,z145,z339,z4,z5,z6]),(0,[z1,z252,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z2,z3,z4,z549,z174]),(0,[z1,z2,z3,z147,z5,z93])],[(0,[z1,z2,z993,z4,z5,z6]),(0,[z1,z95,z110,z4,z5,z6]),(0,[z1,z2,z110,z4,z5,z822]),(0,[z1,z2,z3,z4,z179,z325])],[(0,[z1,z2,z3,z4,z5,z994]),(0,[z239,z2,z3,z4,z5,z174])],[(0,[z1,z2,z16,z124,z5,z6]),(0,[z1,z2,z3,z4,z36,z126]),(0,[z1,z3,z258,z4,z137,z6]),(0,[z1,z2,z3,z4,z187,z6])],[(0,[z13,z118,z3,z4,z5,z6]),(1,[z1,z764,z4,z5,z6]),(0,[z233,z1,z2,z17,z5,z330]),(1,[z1,z2,z4,z5,z822])],[(0,[z1,z2,z3,z4,z995,z6]),(0,[z74,z1,z361,z4,z5,z76]),(0,[z1,z3,z4,z5,z89,z725]),(0,[z996,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z997,z6]),(0,[z1,z2,z110,z4,z5,z262]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z3,z355,z5,z6]),(0,[z185,z1,z2,z3,z41,z5]),(0,[z28,z1,z2,z3,z6,z234])],[(0,[z1,z485,z3,z274,z5,z6]),(0,[z1,z88,z158,z4,z5,z6]),(0,[z1,z2,z3,z264,z5,z42])]],
   [[(0,[z1,z2,z3,z4,z5,z999]),(1,[z1,z2,z3,z760,z5])],[(0,[z1,z24,z3,z4,z67,z6]),(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1,z2,z3,z4,z1001,z6]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z156,z2,z3,z4,z5,z80]),(0,[z1,z1002,z2,z4,z5,z6]),(0,[z1,z2,z20,z4,z5,z126]),(0,[z1,z2,z3,z180,z115,z6]),(0,[z1,z1003,z2,z3,z4,z5]),(0,[z1004,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1005])],[(1,[z2,z152,z124,z5,z6]),(0,[z2,z3,z152,z124,z5,z6]),(0,[z1,z2,z3,z4,z251,z238])],[(0,[z151,z2,z152,z4,z5,z78]),(0,[z1,z1006,z2,z4,z5,z6]),(0,[z31,z1,z2,z3,z635,z5]),(0,[z1,z2,z91,z4,z5,z89]),(0,[z1,z2,z1007,z4,z5,z6]),(0,[z1,z2,z20,z115,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z3,z4,z5,z1009]),(0,[z1,z118,z3,z4,z8,z6]),(0,[z79,z2,z3,z4,z92,z80]),(0,[z1,z2,z3,z4,z179,z463])],[(0,[z79,z303,z3,z4,z5,z80]),(0,[z1,z1010,z3,z4,z5,z6])],[(0,[z1,z435,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z1012,z3,z4,z5,z6]),(0,[z1,z2,z1013,z4,z5,z6]),(0,[z1,z1014,z2,z3,z4,z5]),(0,[z1,z2,z91,z4,z5,z76]),(0,[z1,z211,z3,z4,z549,z6]),(0,[z1,z2,z3,z4,z1015,z6]),(0,[z1,z394,z2,z4,z5,z107])],[(0,[z23,z118,z3,z4,z5,z129]),(0,[z79,z2,z3,z4,z5,z378]),(0,[z1,z2,z3,z1016,z5,z6]),(0,[z1,z2,z3,z4,z5,z1017]),(0,[z1,z320,z3,z4,z5,z330]),(0,[z1,z2,z1018,z4,z5,z6]),(0,[z283,z1,z3,z4,z5,z1019])]],
   [[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z2,z45,z4,z5,z129]),(0,[z237,z2,z3,z4,z5,z965]),(0,[z1,z2,z3,z4,z1022,z6]),(0,[z239,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z187])],[(0,[z1,z2,z3,z1023,z5,z6]),(0,[z1,z2,z3,z4,z1024,z5]),(0,[z51,z2,z3,z52,z5,z127]),(0,[z1,z111,z3,z4,z137,z6]),(0,[z1,z2,z253,z4,z5,z106]),(0,[z1,z2,z3,z4,z558,z234])],[(0,[z1,z2,z3,z4,z1025,z6]),(0,[z1,z2,z1026,z4,z5,z6]),(0,[z128,z2,z3,z4,z5,z80]),(0,[z1,z2,z3,z4,z8,z93]),(0,[z1,z211,z3,z4,z584,z6])],[(0,[z1,z2,z1027,z4,z5,z6]),(0,[z1,z2,z3,z1028,z5,z6]),(0,[z1,z485,z3,z124,z5,z6])],[(0,[z1,z2,z3,z4,z1029,z6]),(0,[z151,z2,z152,z124,z5,z6]),(0,[z1,z2,z849,z4,z5,z6]),(0,[z1,z2,z1030,z4,z5,z6]),(0,[z1,z145,z3,z4,z5,z89]),(0,[z1,z2,z3,z355,z5,z598]),(0,[z1,z2,z3,z1031,z5,z6]),(0,[z1,z2,z3,z4,z5,z1032])],[(0,[z1,z755,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z126]),(0,[z1,z764,z3,z4,z5,z6])],[(0,[z1,z1033,z3,z4,z5,z6]),(0,[z1,z2,z3,z429,z92,z6]),(0,[z96,z1,z2,z3,z180,z4])],[(0,[z1,z2,z3,z4,z1034,z6]),(0,[z1,z2,z1035,z4,z5,z6])]],
   [[(0,[z572,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z1,z2,z1037,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1038]),(0,[z1,z2,z1039,z4,z5,z6]),(0,[z1,z1040,z3,z4,z5,z6])],[(0,[z370,z2,z15,z4,z5,z6]),(0,[z1,z164,z3,z4,z5,z127]),(0,[z1,z2,z1041,z4,z5,z6]),(0,[z1,z2,z91,z429,z5,z6]),(0,[z1,z410,z3,z4,z5,z76]),(0,[z1,z3,z168,z137,z6,z234])],[(0,[z1,z2,z3,z4,z245,z547])],[(0,[z1,z158,z3,z4,z5,z547]),(0,[z1,z2,z3,z535,z5,z93]),(0,[z1,z2,z3,z4,z5,z965]),(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z2,z1043,z4,z5,z6]),(0,[z1,z1044,z3,z4,z5,z6])],[(0,[z51,z164,z3,z52,z5,z6]),(0,[z1045,z1,z3,z4,z5,z6]),(0,[z1,z2,z91,z4,z249,z6]),(0,[z1,z2,z3,z4,z1046,z6]),(0,[z233,z1,z2,z707,z5,z6]),(0,[z1,z1047,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z118,z3,z4,z67,z6]),(0,[z12,z1,z3,z4,z594,z6]),(0,[z1,z2,z418,z4,z5,z6]),(0,[z1,z307,z88,z4,z5,z6]),(0,[z1,z57,z4,z265,z5,z6]),(0,[z1,z3,z829,z265,z5,z6])],[(0,[z12,z1,z3,z4,z596,z6]),(0,[z2,z3,z4,z5,z965,z80])],[(0,[z1,z2,z3,z4,z5,z1048]),(0,[z1,z136,z3,z4,z170,z6]),(0,[z1,z2,z3,z623,z148,z6]),(0,[z1,z2,z3,z264,z92,z6]),(0,[z82,z1,z3,z265,z251,z6]),(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z75,z3,z4,z5,z89])]],
   [[(0,[z1,z1050,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1051,z6]),(0,[z1,z303,z3,z264,z5,z6]),(0,[z149,z1,z2,z4,z5,z107])],[(0,[z1,z83,z45,z4,z5,z6]),(0,[z2,z3,z4,z5,z42,z965]),(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z2,z3,z4,z5,z1053]),(0,[z1,z2,z3,z180,z4,z8]),(0,[z233,z311,z2,z17,z5,z6]),(0,[z1,z2,z3,z4,z5,z1054]),(0,[z1,z2,z3,z4,z5,z1055])],[(0,[z1,z145,z3,z429,z5,z6]),(0,[z1,z2,z91,z4,z179,z5]),(0,[z1,z2,z707,z17,z5,z6]),(0,[z1,z1056,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z6])],[(0,[z49,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z3,z4,z1058,z6])],[(0,[z1,z1059,z3,z4,z5,z6]),(0,[z1,z2,z16,z4,z5,z84])],[(0,[z1,z2,z3,z274,z5,z547]),(0,[z1,z2,z4,z5,z6,z1060]),(0,[z1,z145,z3,z4,z249,z6]),(0,[z1,z2,z3,z180,z4,z126]),(0,[z283,z1,z3,z180,z4,z6])],[(0,[z1,z2,z15,z4,z5,z78]),(0,[z1,z1061,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z234]),(0,[z1,z2,z3,z1062,z5,z6]),(0,[z1,z2,z3,z4,z5,z1063])],[(0,[z1,z2,z3,z4,z1064,z6]),(0,[z1,z54,z16,z4,z5,z84]),(0,[z1065,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z2,z3,z100,z5,z93])]],
   [[(0,[z1,z45,z4,z137,z5,z6]),(0,[z1067,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1068,z5,z6]),(0,[z1,z2,z66,z4,z160,z316])],[(0,[z1,z2,z1069,z4,z5,z6]),(0,[z1,z33,z16,z4,z5,z6]),(0,[z1070,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z249]),(0,[z13,z2,z181,z4,z5,z6]),(0,[z1,z136,z3,z4,z367,z6])],[(0,[z1,z2,z487,z4,z5,z6]),(0,[z1,z2,z3,z205,z5,z64]),(0,[z1,z18,z181,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z598]),(0,[z1071,z2,z3,z4,z5,z6])],[(0,[z51,z2,z3,z52,z5,z64]),(0,[z96,z1,z2,z3,z264,z5]),(0,[z1,z2,z57,z4,z251,z6]),(0,[z26,z2,z181,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z822])],[(0,[z1,z2,z1072,z4,z5,z6]),(0,[z1,z2,z3,z4,z584,z330])],[(0,[z1,z2,z16,z4,z245,z6]),(0,[z1,z2,z3,z4,z245,z78]),(0,[z2,z849,z152,z4,z5,z6]),(0,[z1,z1073,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z251,z6])]],
   [[(0,[z1,z158,z16,z4,z5,z6]),(0,[z1,z158,z3,z4,z5,z78]),(0,[z237,z2,z3,z4,z5,z42]),(0,[z1,z2,z20,z355,z5,z6])],[(0,[z1,z88,z2,z4,z5,z316]),(0,[z233,z1,z2,z17,z5,z6]),(0,[z1,z2,z3,z4,z1074,z6])],[(0,[z1,z435,z3,z4,z36,z6]),(0,[z1,z1075,z3,z4,z5,z6]),(0,[z1076,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z115,z5,z598])],[(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z3,z4,z1078,z6]),(0,[z468,z2,z3,z4,z1051,z6]),(0,[z1,z435,z1079,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1080]),(0,[z12,z49,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z48,z6]),(0,[z1,z2,z3,z4,z5,z1081])],[(0,[z1,z2,z3,z1082,z5,z6])],[(0,[z51,z2,z3,z52,z277,z6])],[(0,[z1,z2,z3,z4,z5,z1083]),(0,[z151,z2,z849,z4,z5,z6]),(0,[z636,z2,z3,z52,z5,z6]),(0,[z1,z2,z339,z4,z92,z6]),(0,[z237,z2,z3,z4,z5,z406]),(0,[z1,z2,z66,z4,z230,z6]),(0,[z1,z2,z1084,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1085])]],
   [[(0,[z1,z303,z339,z4,z5,z6]),(0,[z96,z1,z2,z91,z4,z5]),(0,[z1086,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z251,z114]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z4,z5,z1088])],[(0,[z1,z1089,z3,z4,z5,z6]),(0,[z1,z314,z487,z4,z5,z6]),(0,[z1,z18,z3,z4,z5,z84]),(0,[z12,z13,z3,z4,z208,z6])],[(0,[z1,z2,z3,z274,z5,z78]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z2,z3,z1091,z5,z6]),(0,[z1,z2,z1092,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z83,z57,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1094])],[(0,[z117,z755,z3,z4,z5,z6]),(0,[z1095,z2,z3,z4,z5,z6]),(0,[z1096,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1097]),(0,[z1,z320,z3,z4,z5,z6]),(0,[z255,z1,z2,z4,z5,z107]),(0,[z74,z1,z3,z4,z273,z76]),(0,[z1,z2,z3,z4,z5,z454])],[(0,[z23,z309,z3,z4,z5,z6]),(0,[z1,z2,z113,z4,z5,z127]),(0,[z283,z1,z3,z168,z5,z6]),(0,[z233,z1,z211,z17,z5,z6]),(0,[z1,z2,z66,z4,z160,z6]),(0,[z1,z95,z3,z4,z5,z106])],[(0,[z1098,z2,z3,z4,z5,z6]),(0,[z1099,z1,z3,z4,z5,z6]),(0,[z1,z2,z110,z4,z5,z106]),(0,[z96,z1,z2,z3,z4,z609])],[(0,[z1,z485,z3,z4,z245,z6]),(0,[z1,z3,z4,z5,z6,z1100]),(0,[z1,z2,z3,z4,z1101,z6]),(0,[z1,z2,z3,z4,z5,z1102]),(0,[z1,z2,z1103,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1104])]],
   [[(0,[z191,z24,z3,z4,z5,z6]),(0,[z151,z2,z152,z4,z245,z6]),(0,[z51,z2,z113,z52,z5,z6]),(0,[z1,z2,z3,z52,z5,z64]),(0,[z13,z2,z3,z4,z5,z126]),(0,[z664,z1,z2,z4,z192,z6]),(0,[z1,z2,z66,z4,z776,z6])],[(0,[z1,z287,z158,z4,z5,z6]),(0,[z1,z485,z3,z4,z403,z6]),(0,[z151,z158,z152,z4,z5,z6]),(0,[z1,z1105,z3,z4,z5,z6]),(0,[z1,z54,z16,z4,z5,z55]),(0,[z1,z18,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z1106,z6]),(0,[z74,z1,z3,z4,z8,z76]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z3,z4,z1108,z6]),(0,[z1,z2,z3,z41,z760,z5])],[(0,[z1,z2,z1079,z4,z5,z6]),(0,[z1,z2,z3,z4,z1109,z5]),(0,[z1,z764,z2,z4,z5,z6]),(0,[z1110,z2,z3,z4,z5,z6]),(0,[z26,z2,z3,z4,z5,z126]),(0,[z13,z2,z3,z115,z5,z6])],[(0,[z546,z24,z3,z4,z5,z6]),(0,[z1,z287,z2,z4,z5,z129]),(0,[z1,z18,z3,z4,z5,z129]),(0,[z2,z3,z4,z1051,z36,z6]),(0,[z1111,z2,z3,z4,z5,z6]),(0,[z1,z18,z3,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z238]),(0,[z1,z2,z418,z4,z5,z238])],[(0,[z1,z2,z3,z4,z140,z127]),(0,[z1,z435,z3,z4,z102,z6]),(0,[z1112,z2,z3,z4,z5,z6]),(0,[z1113,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1114,z6]),(0,[z26,z2,z3,z115,z5,z6])],[(0,[z62,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z4,z1115,z6])],[(0,[z1,z2,z3,z124,z5,z78]),(0,[z1,z1116,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1117,z6]),(0,[z283,z1,z3,z4,z36,z6]),(0,[z135,z1,z2,z4,z5,z822]),(0,[z28,z1,z3,z6,z334,z234])],[(0,[z569,z1,z3,z265,z5,z6]),(0,[z1,z2,z3,z4,z5,z1118]),(0,[z636,z2,z152,z4,z5,z6]),(0,[z51,z2,z3,z52,z140,z6]),(0,[z1,z2,z20,z4,z5,z6]),(1,[z1,z2,z3,z6,z758])]],
   [[(0,[z1,z164,z113,z4,z5,z6]),(0,[z1,z2,z3,z115,z36,z6]),(0,[z1,z2,z3,z4,z8,z126]),(0,[z326,z1,z3,z4,z5,z76]),(1,[z1,z2,z4,z776,z6])],[(0,[z1,z2,z3,z4,z1119,z6]),(0,[z448,z2,z3,z4,z5,z42]),(0,[z49,z2,z3,z4,z5,z238]),(0,[z1,z2,z3,z4,z8,z107]),(0,[z587,z1,z3,z4,z5,z76])],[(0,[z1,z2,z361,z4,z5,z6]),(0,[z1,z2,z3,z265,z48,z6]),(0,[z1,z2,z3,z4,z5,z1120])],[(0,[z23,z118,z3,z4,z5,z6]),(0,[z151,z2,z152,z274,z5,z6]),(0,[z1,z75,z3,z4,z5,z590]),(0,[z1,z9,z181,z4,z5,z6]),(0,[z1,z2,z225,z4,z5,z89])],[(0,[z1,z2,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z316])],[(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z1122,z3,z4,z5,z6]),(0,[z79,z2,z3,z4,z5,z427]),(0,[z239,z2,z210,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z1123,z4,z5,z6])],[(0,[z1,z2,z225,z4,z5,z76]),(0,[z1,z2,z3,z4,z746,z179])],[(0,[z1,z1124,z3,z4,z5,z6]),(0,[z1,z164,z3,z4,z140,z6]),(0,[z1,z2,z3,z206,z5,z93])]],
   [[(0,[z1,z2,z3,z4,z1125,z6]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1127,z1,z2,z4,z5,z6]),(0,[z12,z1,z3,z4,z562,z6]),(0,[z239,z2,z3,z17,z5,z6])],[(0,[z1,z24,z3,z4,z5,z126]),(0,[z1,z2,z1128,z4,z5,z6]),(0,[z1,z1129,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1130]),(0,[z1131,z2,z3,z4,z5,z6]),(0,[z74,z1,z225,z4,z5,z76]),(0,[z1,z2,z1132,z4,z5,z6])],[(0,[z1,z1133,z3,z4,z5,z6]),(0,[z135,z1,z95,z4,z5,z107]),(0,[z1,z2,z3,z4,z746,z6])],[(0,[z1,z24,z3,z115,z5,z6]),(0,[z1,z2,z1134,z4,z5,z6]),(0,[z2,z15,z849,z4,z5,z6]),(0,[z1,z2,z3,z4,z92,z6])],[(0,[z1135,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z4,z5,z107])],[(0,[z1,z2,z3,z4,z5,z547]),(0,[z1,z2,z3,z321,z5,z93]),(0,[z1,z2,z20,z4,z5,z598]),(0,[z1,z2,z3,z4,z5,z1136]),(0,[z1,z2,z3,z4,z1137,z5]),(0,[z1,z2,z292,z4,z5,z106])],[(0,[z1,z2,z3,z4,z5,z340]),(0,[z435,z24,z3,z4,z5,z6]),(0,[z1,z2,z91,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z106]),(0,[z1,z2,z679,z4,z160,z6])],[(0,[z1,z1138,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1139,z6]),(0,[z1,z2,z3,z760,z5,z93])]],
   [[(0,[z1,z2,z3,z4,z1140,z6]),(0,[z1,z1141,z2,z3,z4,z5]),(0,[z283,z1,z3,z4,z102,z6]),(0,[z1142,z2,z3,z4,z5,z6]),(0,[z82,z1,z3,z265,z5,z6]),(0,[z82,z1,z418,z265,z5,z6]),(0,[z1,z1143,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1144,z6]),(0,[z239,z2,z3,z4,z5,z6]),(0,[z634,z1,z2,z17,z5,z6]),(0,[z79,z2,z3,z4,z249,z80]),(0,[z1145,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z334]),(0,[z1,z2,z3,z180,z4,z269]),(0,[z1146,z2,z3,z4,z5,z6]),(0,[z1,z2,z1147,z4,z5,z6])],[(0,[z1,z2,z3,z1148,z5,z6]),(0,[z2,z152,z4,z124,z5,z6]),(0,[z575,z2,z15,z4,z5,z6]),(0,[z1,z2,z1149,z4,z5,z6]),(0,[z1,z2,z1150,z4,z5,z6]),(0,[z1,z2,z3,z115,z102,z6]),(0,[z1,z303,z3,z429,z5,z6]),(0,[z1,z2,z177,z4,z5,z106]),(0,[z1,z2,z3,z4,z5,z1151]),(0,[z1,z2,z3,z1152,z5,z6])],[(0,[z1,z2,z3,z4,z1153,z6]),(0,[z1,z2,z3,z4,z5,z1154]),(0,[z1,z2,z3,z264,z5,z89]),(0,[z352,z1,z3,z4,z5,z76]),(0,[z311,z2,z3,z4,z5,z330]),(0,[z1,z2,z3,z4,z584,z6]),(0,[z283,z28,z1,z3,z6,z234]),(0,[z31,z1,z2,z3,z41,z61])],[(0,[z1,z1155,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z53]),(0,[z1,z2,z66,z4,z160,z454])],[(0,[z1,z2,z3,z4,z1156,z6]),(0,[z1,z303,z3,z4,z249,z6]),(0,[z1,z3,z4,z5,z6,z725]),(0,[z1,z2,z3,z4,z5,z1157])],[(0,[z1,z2,z3,z4,z1158,z6]),(0,[z1,z2,z3,z264,z5,z76]),(0,[z194,z2,z3,z4,z5,z42]),(0,[z1,z1159,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1160,z5,z6]),(0,[z1,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z403,z547]),(0,[z1,z1161,z3,z4,z5,z6]),(0,[z79,z2,z3,z264,z5,z80]),(0,[z1,z2,z3,z4,z5,z1162]),(0,[z1,z2,z1163,z4,z5,z6])]],
   [[(0,[z390,z2,z3,z4,z36,z6]),(0,[z1,z2,z3,z4,z5,z1164])],[(0,[z14,z2,z3,z124,z5,z6]),(0,[z1,z1165,z2,z3,z4,z5]),(0,[z62,z164,z3,z4,z5,z6]),(0,[z2,z487,z4,z52,z5,z6])],[(0,[z1,z2,z3,z4,z1166,z6]),(0,[z1,z764,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z1167,z6]),(0,[z1,z1168,z3,z4,z5,z6]),(0,[z1,z1169,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1170,z5,z6]),(0,[z1171,z1,z3,z4,z5,z6]),(0,[z1,z2,z418,z4,z48,z6]),(0,[z1,z1172,z3,z4,z5,z6]),(0,[z1,z2,z3,z567,z148,z6]),(0,[z1,z2,z441,z3,z6,z234]),(0,[z1,z2,z3,z201,z6,z758])],[(0,[z1,z2,z3,z4,z1173,z6]),(0,[z1,z2,z3,z4,z5,z1174]),(0,[z1,z2,z3,z4,z1175,z6]),(0,[z1,z2,z3,z4,z179,z249]),(0,[z1,z2,z3,z484,z148,z6])],[(0,[z1,z2,z1176,z4,z5,z6]),(0,[z1,z118,z3,z4,z5,z126]),(0,[z1,z2,z57,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1177]),(0,[z1,z2,z3,z4,z5,z1178]),(0,[z26,z3,z16,z4,z5,z6]),(0,[z1,z16,z4,z5,z76,z107]),(0,[z82,z70,z3,z265,z5,z6]),(0,[z12,z1,z3,z4,z208,z126])],[(0,[z1,z2,z3,z4,z5,z1179]),(0,[z1,z118,z3,z115,z5,z6]),(0,[z1,z2,z3,z4,z1180,z6]),(0,[z1,z2,z3,z4,z1181,z6]),(0,[z1,z2,z3,z4,z5,z1182]),(0,[z13,z2,z3,z355,z5,z6]),(0,[z1,z2,z1183,z4,z5,z6]),(0,[z1,z1184,z3,z4,z5,z6])]],
   [[(0,[z70,z2,z418,z4,z5,z6]),(0,[z283,z1,z3,z4,z48,z6]),(0,[z1,z3,z168,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z1185])],[(0,[z697,z118,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1186]),(0,[z26,z2,z3,z355,z5,z6]),(0,[z1,z2,z3,z4,z1187,z6])],[(0,[z1,z2,z3,z4,z5,z78]),(0,[z1,z2,z110,z4,z5,z516]),(0,[z1,z2,z3,z4,z1188,z6]),(1,[z239,z2,z17,z5,z6]),(0,[z1,z2,z3,z4,z1189,z6]),(0,[z1,z1190,z3,z4,z5,z6]),(0,[z1,z2,z3,z1191,z5,z6]),(0,[z1,z2,z3,z4,z746,z5])],[(0,[z468,z2,z3,z4,z87,z36]),(0,[z1,z2,z20,z4,z36,z6]),(0,[z49,z2,z57,z4,z5,z6]),(0,[z233,z1,z2,z17,z549,z6])],[(0,[z1,z2,z3,z4,z87,z5]),(0,[z1,z2,z3,z264,z249,z6]),(0,[z1,z3,z16,z4,z8,z6]),(0,[z1,z2,z3,z4,z1192,z6]),(0,[z1,z2,z3,z4,z5,z1193]),(0,[z1,z2,z1194,z4,z5,z6]),(0,[z1,z2,z1195,z4,z5,z6])],[(0,[z12,z1,z45,z4,z5,z6]),(0,[z1,z54,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z549,z330])],[(0,[z1,z2,z3,z4,z1196,z6]),(0,[z1,z2,z3,z4,z5,z1197]),(0,[z2,z3,z4,z5,z6,z965]),(0,[z1,z2,z3,z1198,z5,z6]),(0,[z1,z2,z3,z201,z148,z6]),(0,[z1,z2,z3,z4,z746,z103])],[(0,[z704,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z274,z245,z6]),(0,[z1,z2,z210,z414,z5,z6]),(1,[z2,z487,z52,z5,z6]),(0,[z2,z3,z487,z52,z5,z6]),(0,[z13,z435,z3,z4,z5,z6]),(0,[z239,z2,z3,z4,z5,z330]),(0,[z233,z1,z2,z17,z584,z6]),(0,[z1,z2,z3,z4,z1199,z6]),(0,[z1,z2,z3,z4,z6,z758])]],
   [[(0,[z1,z2,z3,z4,z1200,z6]),(0,[z1,z158,z3,z274,z5,z6]),(0,[z1,z2,z3,z1201,z5,z6]),(0,[z1,z2,z3,z4,z87,z103]),(0,[z1,z800,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z1202,z5]),(0,[z1,z2,z3,z4,z558,z148])],[(0,[z1,z3,z1203,z4,z5,z6]),(0,[z49,z3,z4,z137,z5,z6]),(0,[z1,z2,z418,z4,z5,z114]),(0,[z1,z2,z3,z4,z8,z41]),(0,[z1,z2,z3,z4,z5,z1204])],[(0,[z1,z2,z15,z124,z5,z6]),(0,[z1,z1205,z3,z4,z5,z6]),(0,[z1,z2,z3,z264,z179,z5]),(0,[z401,z1,z2,z3,z6,z234])],[(0,[z1,z2,z113,z4,z140,z6]),(0,[z1,z1206,z3,z4,z5,z6]),(0,[z1207,z2,z3,z4,z5,z6]),(0,[z1,z95,z3,z4,z5,z107])],[(0,[z1,z2,z3,z4,z403,z78]),(0,[z1,z2,z3,z4,z5,z127]),(0,[z1208,z2,z3,z4,z5,z6]),(0,[z391,z1,z2,z3,z6,z234]),(0,[z1209,z2,z3,z4,z5,z6])],[(1,[z1,z225,z4,z5,z76])],[(0,[z1,z2,z3,z4,z277,z127]),(0,[z1,z1210,z3,z4,z5,z6]),(0,[z1,z1211,z3,z4,z5,z6]),(0,[z1,z2,z467,z21,z5,z6]),(0,[z1,z270,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z233,z239,z2,z17,z5,z6]),(0,[z135,z1,z2,z4,z5,z107]),(0,[z1213,z2,z3,z4,z5,z6])],[(0,[z1,z1214,z2,z4,z5,z6]),(0,[z51,z2,z3,z52,z5,z6]),(0,[z1,z164,z3,z4,z5,z64]),(0,[z1,z1215,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z79,z2,z339,z4,z5,z80]),(0,[z49,z2,z3,z4,z5,z114])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 527).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1066).take 92) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1158)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [527, 539, 92] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 103).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 206).take 50).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [103, 103, 50] = true :=
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

end PEqualNP.Outside.L_meta_38123

theorem PEqualNP.Outside.L_meta_38123 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38123.solve