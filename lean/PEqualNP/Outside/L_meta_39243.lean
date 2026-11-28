import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39243

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4276680840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x800081240c34c540#64 ++ 0x0a0002049030d315#64 ++ 0x409187fc1c7ccffd#64 ++ 0xfd02461ff071f33f#64 : BitVec 256),
   (0x01266490618b0aa8#64 ++ 0xa404999241862c2a#64 ++ 0xe36e6490e38f0ffb#64 ++ 0x7b8db992438e3c3f#64 : BitVec 256),
   (0x047028e102d15331#64 ++ 0x0811c0a3840b454c#64 ++ 0xdc7078e303f3f337#64 ++ 0xd771c1e38c0fcfcc#64 : BitVec 256),
   (0x0b805702b402ac02#64 ++ 0x302e015c0ad00ab0#64 ++ 0xdf807f03fc03fc2f#64 ++ 0xcf7e01fc0ff00ff0#64 : BitVec 256),
   (0x1edb8003db6c0003#64 ++ 0xc07b6e000f6db000#64 ++ 0xffff8003fffc001f#64 ++ 0x3ffffe000ffff000#64 : BitVec 256),
   (0x0ffd7ed80000003c#64 ++ 0x003ff5fb60000000#64 ++ 0xeffffffc00000000#64 ++ 0xffbffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc0078030003f027 0xc77001e00c000fc0

def z1 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6490e38f0ffb 0x7b8db992438e3c3f

def z2 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc7078e303f3f337 0xd771c1e38c0fcfcc

def z3 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f03fc03fc2f 0xcf7e01fc0ff00ff0

def z4 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc00000000 0xffbffffff0000000

def z5 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x23ff8000fffc0018 0x388ffe0003fff000

def z6 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409187fc1c7ccffd 0xfd02461ff071f33f

def z7 : W := mkw 0x0000002102d15301 0x08000000840b454c 0x1000000303f3f337 0x004000000c0fcfcc

def z8 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0x238f871c00000000 0x288e3e1c70000000

def z9 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fffc001f 0x3ffffe000ffff000

def z10 : W := mkw 0x8b80d726bc36ed42 0x3a2e035c9af0dbb5 0xdf91ff6ffc73fc2f 0xcf7e47fdbff1cff0

def z11 : W := mkw 0x0450000102400001 0x0011400004090000 0xdc70000303f00017 0x1771c0000c0fc000

def z12 : W := mkw 0x0020208000810220 0x0000808200020408 0xc0606490038f0ffb 0x7b018192400e3c3f

def z13 : W := mkw 0x05766cd163cb1ab9 0xa415d9b3458f2c6a 0xff6e7c93e38f3ffb 0x7bfdb9f24f8e3cff

def z14 : W := mkw 0x0000002102505101 0x0800000084094144 0x100000030070f004 0x004000000c01c3c0

def z15 : W := mkw 0x0000800008240000 0x0000020000209000 0x009180001c700004 0x040246000071c000

def z16 : W := mkw 0x002028c000000030 0x000080a300000000 0x000078e000000000 0xc00001e380000000

def z17 : W := mkw 0x01266490418902a8 0x840499924106240a 0xe36e6490038c03d0 0x7b8db992400e300f

def z18 : W := mkw 0x0126e49069af0aa8 0xa4049b9241a6bc2a 0xe3ffe490ffff0fff 0x7f8fff9243fffc3f

def z19 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6000e3830002 0x028db980038e0c00

def z20 : W := mkw 0x0fff7ed8618b0abc 0xa43ffdfb61862c2a 0xeffffffce38f0ffb 0xffbffffff38e3c3f

def z21 : W := mkw 0x1edb8003fbef0a83 0xe47b6e000fefbc2a 0xffff8003ffff0fff 0x3ffffe000ffffc3f

def z22 : W := mkw 0x0124649000000028 0x0004919240000000 0xe3ffe7fc00000000 0xff8fff9ff0000000

def z23 : W := mkw 0x8470a9e50ef5d771 0x0a11c2a7943bd75d 0xdcf1fbef1ff3f337 0xd773c7efbc7fcfcc

def z24 : W := mkw 0x01064410618b0a88 0xa404191041862c2a 0x230e0410e38f0ffb 0x288c3810438e3c3f

def z25 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x408007001c7ccffd 0xcd02001c0071f33f

def z26 : W := mkw 0x0002000041080000 0x8000080001042000 0xe36e0490e38c0ffb 0x7b8db812438e303f

def z27 : W := mkw 0x0fff7ed8610a08bc 0xa43ffdfb61842822 0xeffffffce00c0cc8 0xffbffffff3803033

def z28 : W := mkw 0x1ed980039a640003 0x407b66000e699000 0x1c9180031c700004 0x047246000c71c000

def z29 : W := mkw 0x1fffe493fbef0aab 0xe47fff924fefbc2a 0xffffe493ffff0fff 0x7fffff924ffffc3f

def z30 : W := mkw 0x9efba9e7dffdd773 0xca7beea79f7ff75d 0xffffffffffffffff 0xffffffffffffffff

def z31 : W := mkw 0x0b805722b412ed02 0x382e015c8ad04bb4 0xdf907fe3fc73ff3f 0xdf7e41ff8ff1cffc

def z32 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe3ffe7fce38f0ffb 0xff8fff9ff38e3c3f

def z33 : W := mkw 0x0100440000000000 0x0004011000000000 0xc300640000000000 0x4b0c019000000000

def z34 : W := mkw 0x010057002402ac00 0x3004015c00900ab0 0x00007f000003fc20 0xc00001fc00000ff0

def z35 : W := mkw 0x0ff07ee3b2d37b33 0x383fc1fb8ecb4dec 0xdf7078e3e3f3f337 0xd77dc1e38f8fcfcc

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x409187fc00000000 0xfd02461ff0000000

def z37 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f007803fc03fc2f 0x027c01e00ff00ff0

def z38 : W := mkw 0x0002000041080000 0x8000080001042000 0xe36e0000e38c001b 0x3b8db800038e3000

def z39 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xdc91ffff1c7fffff 0xff7247fffc71ffff

def z40 : W := mkw 0x0000002000104100 0x0800000080004104 0x000000000070c335 0x000000000001c30c

def z41 : W := mkw 0x047028c102400031 0x0011c0a304090000 0xdc7078e303f00017 0xd771c1e38c0fc000

def z42 : W := mkw 0x9ed981279e74c543 0x4a7b66049e79d315 0x1c91836f1c70c004 0x8472460dbc71c300

def z43 : W := mkw 0x9edb8127df7cc543 0xca7b6e049f7df315 0xffff87fffffccfff 0xfffffe1ffffff33f

def z44 : W := mkw 0x0ed9000000000000 0x003b640000000000 0xefff87fc00000000 0xffbffe1ff0000000

def z45 : W := mkw 0x0ff67ff3f7dbffbb 0xbc3fd9ffcfdf6ffe 0xfffe7ff3ffffffff 0xfffff9ffcfffffff

def z46 : W := mkw 0x047628f143d953b9 0x8c11d8a3c50f654e 0x207e00f003fc03d0 0x3081f803c00ff00f

def z47 : W := mkw 0x0450000102400001 0x0011400004090000 0x1c10000300700004 0x047040000c01c000

def z48 : W := mkw 0x05706ce122d35b31 0x2815c1b3848b4d6c 0xdf707ce3e3f3ff3f 0xdf7dc1f38f8fcffc

def z49 : W := mkw 0x00028000492c0000 0x80000a000124b000 0xe3ff8000fffc001f 0x3f8ffe0003fff000

def z50 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbf6e0003fffc001f 0x02fdb8000ffff000

def z51 : W := mkw 0x800281246dbfcfc0 0xae000a0491b6ff3f 0x409187fcffffcfff 0xfd02461ff3ffff3f

def z52 : W := mkw 0x000d00180000000c 0x0000340060000000 0x200f801c00000000 0x20803e0070000000

def z53 : W := mkw 0x047028c000000030 0x0011c0a300000000 0xcc7078e000000000 0xd731c1e380000000

def z54 : W := mkw 0x0ffd7ef902d1533d 0x083ff5fbe40b454c 0xffffffff03f3f337 0xfffffffffc0fcfcc

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x4010000000700015 0x150040000001c000

def z56 : W := mkw 0x0000002000104100 0x0800000080004104 0x000000e00000c320 0xc00000038000030c

def z57 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0x207f80fc00000000 0x3081fe03f0000000

def z58 : W := mkw 0x1ffffedbdb6c003f 0xc07ffffb6f6db000 0xfffffffffffc001f 0xfffffffffffff000

def z59 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffff80000000000 0x3fbfffe000000000

def z60 : W := mkw 0x1a8b8002d92c0002 0xc06a2e000b64b000 0x238f8000fc0c0008 0x288e3e0003f03000

def z61 : W := mkw 0x0fff7fdaf58baebe 0xb43ffdff6bd62eba 0xffffffffff8fffff 0xfffffffffffe3fff

def z62 : W := mkw 0x0124649000000028 0x0004919240000000 0xe36e649000000000 0x7b8db99240000000

def z63 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c70cfe4 0xc402461ff071c33f

def z64 : W := mkw 0x0000000000000000 0x0000000000000000 0x401000e000000000 0xd500400380000000

def z65 : W := mkw 0x0000086000105110 0x0800002180004144 0x000018600000f000 0x80000061800003c0

def z66 : W := mkw 0x0100440020020800 0x2004011000800820 0xc3006400e0030c2b 0x4b0c019003800c30

def z67 : W := mkw 0x0efd3ad80000003c 0x003bf4eb60000000 0x2cff9bfc00000000 0xb4b3fe6ff0000000

def z68 : W := mkw 0x0edb000041080000 0x803b6c0001042000 0xefff8000e38c001b 0x3fbffe00038e3000

def z69 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0x9f007803e0033002 0x027c01e00f800cc0

def z70 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x001180fc007c03d0 0x30004603f001f00f

def z71 : W := mkw 0x00000102b402ac02 0x300000040ad00ab0 0x00000000fc000c08 0x0000000003f00030

def z72 : W := mkw 0x147fa8d94b6c003d 0xc051fea3652db000 0x207f80fc03fc0010 0x3081fe03f00ff000

def z73 : W := mkw 0x000013000400a400 0x1000004c00100290 0x00001b000000f000 0x8000006c000003c0

def z74 : W := mkw 0x047f28d8418902bc 0x8411fca36106240a 0x207f80fc038c03d0 0x3081fe03f00e300f

def z75 : W := mkw 0x0000010004008400 0x0000000400100210 0x008007001c000c08 0x0802001c00700030

def z76 : W := mkw 0x012664b0619b4ba8 0xac049992c1866d2e 0xe37e64f0e3ffcfff 0xff8df993c38fff3f

def z77 : W := mkw 0x1a8b8002d92c0002 0xc06a2e000b64b000 0x639f8000fc7c001d 0x3d8e7e0003f1f000

def z78 : W := mkw 0x0ed9000000000000 0x003b640000000000 0x0c91800000000000 0x0432460000000000

def z79 : W := mkw 0x0ffd7fdab402ac3e 0x303ff5ff6ad00ab0 0xfffffffffc03fc2f 0xfffffffffff00ff0

def z80 : W := mkw 0x00262090618b0aa8 0xa400988241862c2a 0x206e0090e38f0ffb 0x3081b802438e3c3f

def z81 : W := mkw 0x1fdbd603db6c0003 0xc07f6f580f6db000 0xffffff03fffc001f 0xfffffffc0ffff000

def z82 : W := mkw 0x047d28f902d1533d 0x0811f4a3e40b454c 0xfc7ff8ff03f3f337 0xf7f1ffe3fc0fcfcc

def z83 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xefee7f0000000000 0xcfbfb9fc00000000

def z84 : W := mkw 0x057d6cd80000003c 0x0015f5b360000000 0xe37fe4fc00000000 0x7b8dff93f0000000

def z85 : W := mkw 0x00000102b402ac02 0x300000040ad00ab0 0x10000003fc03fc2f 0x004000000ff00ff0

def z86 : W := mkw 0x0b80560000000000 0x002e015800000000 0xcf807f0000000000 0xcf3e01fc00000000

def z87 : W := mkw 0x0ed9000000000000 0x003b640000000000 0xefff800000000000 0x3fbffe0000000000

def z88 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x000000001c7ccffd 0x000000000071f33f

def z89 : W := mkw 0x0020208000000020 0x0000808200000000 0xc060608000000000 0x5301818200000000

def z90 : W := mkw 0x0450084000000010 0x0011402100000000 0x0c10186000000000 0x8430406180000000

def z91 : W := mkw 0x0124649020830aa8 0x2404919240820c2a 0x0000600000030000 0x0000018000000c00

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000490000c0ff9 0x790000124000303f

def z93 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc707cf303ffffff 0xff71c1f3cc0fffff

def z94 : W := mkw 0x0bad7ed80000003c 0x002eb5fb60000000 0x238ffffc00000000 0xe88e3ffff0000000

def z95 : W := mkw 0x1efba8e3dbfd5333 0xc87beea38f6ff54c 0xfffff8e3fffff33f 0xffffffe38fffffcc

def z96 : W := mkw 0x0000000020020800 0x2000000000800820 0x00000000e0030c2b 0x0000000003800c30

def z97 : W := mkw 0x10028003db6c0003 0xc0400a000f6db000 0xf36e0003fffc001f 0x3bcdb8000ffff000

def z98 : W := mkw 0x800081040c248440 0x0200020410309211 0x409187fc1c0c0cc8 0xfd02461ff0703033

def z99 : W := mkw 0x0ff07fe3b6d3ff33 0x383fc1ff8edb4ffc 0xdff07fe3fff3ff3f 0xdf7fc1ff8fffcffc

def z100 : W := mkw 0x90028127df7cc543 0xca400a049f7df315 0x10000003fffccfff 0x004000000ffff33f

def z101 : W := mkw 0x0459084800000014 0x0011642120000000 0x0011806c00000000 0x00004601b0000000

def z102 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x007000e003f00310 0x1001c003800fc00c

def z103 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x03800700fc000c08 0x080e001c03f00030

def z104 : W := mkw 0x01064410610a0888 0xa404191041842822 0x230e0410e00c0cc8 0x288c381043803033

def z105 : W := mkw 0x05766cf163db5bb9 0xac15d9b3c58f6d6e 0xff7e7cf3e3ffffff 0xfffdf9f3cf8fffff

def z106 : W := mkw 0x01064410610a0888 0xa404191041842822 0x230e0000e0000000 0x008c380003800000

def z107 : W := mkw 0x0ba67792f58baeaa 0xb42e99de4bd62eba 0xffee7f03ff83fc2f 0xcfffb9fc0ffe0ff0

def z108 : W := mkw 0x8ffdfffc0c34c57c 0x0a3ff7fff030d315 0xeffffffc1c7ccffd 0xffbffffff071f33f

def z109 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0x00000000e38f0ffb 0x00000000038e3c3f

def z110 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0x0c919b6c00000000 0x8432466db0000000

def z111 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaffffb6c00000000 0x86bfffedb0000000

def z112 : W := mkw 0x145b80014b6c0001 0xc0516e00052db000 0x207f800003fc0010 0x3081fe00000ff000

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000008000000331 0x510000020000000c

def z114 : W := mkw 0x0450086102505111 0x0811402184094144 0x1c1018630070f004 0x847040618c01c3c0

def z115 : W := mkw 0x0450086102505111 0x0811402184094144 0x0010006000700000 0x000040018001c000

def z116 : W := mkw 0x0000800008240000 0x0000020000209000 0x409187fc1c7c001d 0xfd02461ff071f000

def z117 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x0091836c1c7ccffd 0x8402460db071f33f

def z118 : W := mkw 0x01064410610a0888 0xa404191041842822 0xe30e6410e00f0ceb 0x6b8c399043803c33

def z119 : W := mkw 0x800081040c248440 0x0200020410309211 0x0081871c1c0c0cc8 0x2802061c70703033

def z120 : W := mkw 0x8470a9e50ef5d771 0x0a11c2a7943bd75d 0xdcf1ffff1fffffff 0xff73c7fffc7fffff

def z121 : W := mkw 0x0ffd7fd82402ac3c 0x303ff5ff60900ab0 0xeffffffc0003fc20 0xffbffffff0000ff0

def z122 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6000e38f001b 0x3b8db980038e3c00

def z123 : W := mkw 0x0a8013029400a402 0x102a004c0a500290 0x1c801b031c00f004 0x8472006c0c7003c0

def z124 : W := mkw 0x8b80d726bc36ed42 0x3a2e035c9af0dbb5 0xdf91fffffc7fffff 0xff7e47fffff1ffff

def z125 : W := mkw 0x8126e5b46dbfcfe8 0xae049b96d1b6ff3f 0xe3ffe7fcffffcfff 0xff8fff9ff3ffff3f

def z126 : W := mkw 0x0124649000810228 0x0004919240020408 0xe36e649003830333 0x7b8db992400e0c0c

def z127 : W := mkw 0x0a89000000000000 0x002a240000000000 0x238f800000000000 0x288e3e0000000000

def z128 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0xe36e0000e38f0ffb 0x3b8db800038e3c3f

def z129 : W := mkw 0x01247ed80000003c 0x000491fb60000000 0x00007ffc00000000 0xc00001fff0000000

def z130 : W := mkw 0x10028003db6c0003 0xc0400a000f6db000 0x10000003fffc001f 0x004000000ffff000

def z131 : W := mkw 0x800081040c248440 0x0200020410309211 0x0081830c1c000000 0x0002060c30700000

def z132 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x3cff80031ffc0014 0x34f3fe000c7ff000

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00780000000000 0xc73001e000000000

def z134 : W := mkw 0x1fffffdbff6eac3f 0xf07fffff6ffdbab0 0xfffffffffffffc3f 0xfffffffffffffff0

def z135 : W := mkw 0x800001240410c540 0x0a00000490104315 0x000007fc0000cfe0 0xc000001ff000033f

def z136 : W := mkw 0x0ffd7ef90250513d 0x083ff5fbe4094144 0xffffffff0070f004 0xfffffffffc01c3c0

def z137 : W := mkw 0x057d7ed80000003c 0x0015f5fb60000000 0x207ffffc00000000 0xf081fffff0000000

def z138 : W := mkw 0x0ba47792b483aeaa 0x342e91de4ad20eba 0xdf807f93fc03ffef 0xcf7e01fe4ff00fff

def z139 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xfffff803fffff03f 0xffffffe00fffffc0

def z140 : W := mkw 0x0ffd7ffbb6d3ff3f 0x383ff5ffeedb4ffc 0xfffffffffff3ff3f 0xffffffffffffcffc

def z141 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc7000e303f00317 0x1771c0038c0fc00c

def z142 : W := mkw 0x01267ed8618b0abc 0xa40499fb61862c2a 0xe36e7ffce38f0ffb 0xfb8db9fff38e3c3f

def z143 : W := mkw 0x0124649000000028 0x0004919240000000 0x0000649000000000 0x4000019240000000

def z144 : W := mkw 0x8470a9e40c34c570 0x0a11c2a79030d315 0xccf1fffc1c7ccffd 0xff33c7fff071f33f

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000049000000000 0x7900001240000000

def z146 : W := mkw 0x00001a4800000014 0x0000006920000000 0x00001b6c00000000 0x8000006db0000000

def z147 : W := mkw 0x1edb0003d3480003 0xc07b6c000f4d2000 0xbf6e0003e3800002 0x02fdb8000f8e0000

def z148 : W := mkw 0x047d28f902d1533d 0x0811f4a3e40b454c 0x207f80fc03f00310 0x3081fe03f00fc00c

def z149 : W := mkw 0x0000010004008400 0x0000000400100210 0x000000001c00cc2d 0x0000000000700330

def z150 : W := mkw 0x0000002102d15301 0x08000000840b454c 0xdc00780303f3f337 0xc77001e00c0fcfcc

def z151 : W := mkw 0x0a80120290002002 0x102a00480a400080 0x1c00180300003000 0x007000600c0000c0

def z152 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x13800703fc03fc2f 0x084e001c0ff00ff0

def z153 : W := mkw 0x847da8fc0834417c 0x0a11f6a3f020d105 0x207f80fc007c03d0 0x3081fe03f001f00f

def z154 : W := mkw 0x0000002000104100 0x0800000080004104 0x401004f0007ccffd 0xfd004013c001f33f

def z155 : W := mkw 0x145b80014b6c0001 0xc0516e00052db000 0xfc7f800303fc0017 0x37f1fe000c0ff000

def z156 : W := mkw 0x1fdb5603f34a2803 0xf07f6d580fcd28a0 0xbf6e7803e3833002 0x02fdb9e00f8e0cc0

def z157 : W := mkw 0x0ffd7ed82002083c 0x203ff5fb60800820 0xeffffffce0030c2b 0xffbffffff3800c30

def z158 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f93fc0fffff 0xff7e01fe4ff03fff

def z159 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xff6e7c93e38fffff 0xfffdb9f24f8e3fff

def z160 : W := mkw 0x00262090418902a8 0x840098824106240a 0x606e0490038c0ff9 0x7981b812400e303f

def z161 : W := mkw 0x0100440020020800 0x2004011000800820 0x03000400e0000c08 0x080c001003800030

def z162 : W := mkw 0x1ed9000392400003 0x407b64000e490000 0x1c00000300000000 0x007000000c000000

def z163 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8493fffc0fff 0x7ffffe124ffff03f

def z164 : W := mkw 0x0ffd7ef80091533c 0x083ff5fbe002454c 0xeffffffc0003f320 0xffbffffff0000fcc

def z165 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x43800700fc00cc2d 0xcd0e001c03f00330

def z166 : W := mkw 0x0000002000104100 0x0800000080004104 0x401000e00070c335 0xd50040038001c30c

def z167 : W := mkw 0x0126649041080028 0x8004999241042000 0xe36e6490e38c001b 0x7b8db992438e3000

def z168 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c60780303f3f337 0x027181e00c0fcfcc

def z169 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x236e0490e38c0fd8 0x388db812438e303f

def z170 : W := mkw 0x01266590658b8ea8 0xa404999641962e3a 0xe3ee6790ff8fcfff 0xff8fb99e43fe3f3f

def z171 : W := mkw 0x000001002402ac00 0x3000000400900ab0 0x000000000003fc20 0x0000000000000ff0

def z172 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdcf1ffff03f3f337 0xff73c7fffc0fcfcc

def z173 : W := mkw 0x0000800008240000 0x0000020000209000 0x409180001c7c001d 0x3d0246000071f000

def z174 : W := mkw 0x0ba67792f58baeaa 0xb42e99de4bd62eba 0xffee7f93ff8fffff 0xffffb9fe4ffe3fff

def z175 : W := mkw 0x1edb8863db7c5113 0xc87b6e218f6df144 0xffff9863fffcf01f 0xbffffe618ffff3c0

def z176 : W := mkw 0x1fff6493f3cb0aab 0xe47ffd924fcf2c2a 0xbf6e6003e3830002 0x02fdb9800f8e0c00

def z177 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfff8003fff00006 0x06fffe000fffc000

def z178 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xffffffff0003f027 0xfffffffffc000fc0

def z179 : W := mkw 0x047028e000915330 0x0811c0a38002454c 0xcc7078e00003f320 0xd731c1e380000fcc

def z180 : W := mkw 0x0124649020830aa8 0x2404919240820c2a 0xe36e649000030fe0 0x7b8db99240000c3f

def z181 : W := mkw 0x800081040c248440 0x0200020410309211 0x4081879c1c0c0ff9 0x7902061e7070303f

def z182 : W := mkw 0x147fa0914bed02a9 0xc451fe82452fb40a 0x207f809003fc03d0 0x3081fe02400ff00f

def z183 : W := mkw 0x1edb0003d3480003 0xc07b6c000f4d2000 0xff6e0003e38c001b 0x3bfdb8000f8e3000

def z184 : W := mkw 0x0000002000104100 0x0800000080004104 0x001000e000700310 0x100040038001c00c

def z185 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0x9c60780303833002 0x027181e00c0e0cc0

def z186 : W := mkw 0x0ffd7ed902c1123d 0x003ff5fb640b0448 0xffffffff03833002 0xfffffffffc0e0cc0

def z187 : W := mkw 0x8126e5946daf8ee8 0xa6049b9651b6be3b 0xe3efe79cff8f0ffb 0x7b8fbf9e73fe3c3f

def z188 : W := mkw 0x80008126bc36ed42 0x3a0002049af0dbb5 0x509187fffc7fffff 0xfd42461ffff1ffff

def z189 : W := mkw 0x1a828003db6c0003 0xc06a0a000f6db000 0xdf800003fffc001f 0x0f7e00000ffff000

def z190 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0xdf807f03e0033002 0xcf7e01fc0f800cc0

def z191 : W := mkw 0x9a8b8106dd2c8442 0xc26a2e041b74b211 0x238f871cfc0c0cc8 0x288e3e1c73f03033

def z192 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x0091836c1c70c004 0x8402460db071c300

def z193 : W := mkw 0x800281246dbfcfc0 0xae000a0491b6ff3f 0x00000000ffffcfff 0x0000000003ffff3f

def z194 : W := mkw 0x0020208000810220 0x0000808200020408 0xc060608003830333 0x53018182000e0c0c

def z195 : W := mkw 0x0fdd5e580000001c 0x003f757960000000 0x2f9f9f7c00000000 0xacbe7e7df0000000

def z196 : W := mkw 0x01246cf020935bb8 0x2c0491b3c0824d6e 0x00007cf00003ffe0 0xc00001f3c0000fff

def z197 : W := mkw 0x1fdfd61bdb6c000f 0xc07f7f586f6db000 0xffff871ffffc001f 0x3ffffe1c7ffff000

def z198 : W := mkw 0x0124649020830aa8 0x2404919240820c2a 0xc060649003830ff3 0x53018192400e0c3f

def z199 : W := mkw 0x0ed91b4a9400a416 0x103b646d2a500290 0x1c919b6f1c00f004 0x8472466dbc7003c0

def z200 : W := mkw 0x0a8013029400a402 0x102a004c0a500290 0xdc807b031c03f027 0xc77201ec0c700fc0

def z201 : W := mkw 0x845089650e74d551 0x0a1142259439d355 0x5c919fff1c7cfffd 0xfd72467ffc71f3ff

def z202 : W := mkw 0x800081040c248440 0x0200020410309211 0x000000001c0c0cc8 0x0000000000703033

def z203 : W := mkw 0x01247ed80000003c 0x000491fb60000000 0x4091fffc00000000 0xfd0247fff0000000

def z204 : W := mkw 0x012477902483aea8 0x340491de40920eba 0x00007f900003ffe0 0xc00001fe40000fff

def z205 : W := mkw 0x8ffdfffc0c34c57c 0x0a3ff7fff030d315 0xeffffffc1c70c004 0xffbffffff071c300

def z206 : W := mkw 0x9edb8107df6c8443 0xc27b6e041f7db211 0xffff871ffffc0cdf 0x3ffffe1c7ffff033

def z207 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0xdc7078e303833002 0xd771c1e38c0e0cc0

def z208 : W := mkw 0x1edb80014b6c0001 0xc07b6e00052db000 0xefff800003fc0010 0x3fbffe00000ff000

def z209 : W := mkw 0x90028127df7cc543 0xca400a049f7df315 0x509187fffffccfff 0xfd42461ffffff33f

def z210 : W := mkw 0x1ffffefbdbfd533f 0xc87ffffbef6ff54c 0xfffffffffffff33f 0xffffffffffffffcc

def z211 : W := mkw 0x8100d7242c36ed40 0x3a04035c90b0dbb5 0x4091fffc1c7ffffd 0xfd0247fff071ffff

def z212 : W := mkw 0x0006001041080088 0x8400180041042002 0x200e0010000c00c0 0x2080380040003003

def z213 : W := mkw 0x8124fffc0c34c57c 0x0a0493fff030d315 0x4091fffc1c7ccffd 0xfd0247fff071f33f

def z214 : W := mkw 0x0ffd7edab002283e 0x303ff5fb6ac008a0 0xbf6e7803e0033002 0x02fdb9e00f800cc0

def z215 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6090e38f03d2 0x328db982438e3c0f

def z216 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff87fffffc001f 0xfffffe1ffffff000

def z217 : W := mkw 0x010057002402ac00 0x3004015c00900ab0 0x40807f001c03fc2d 0xcd0201fc00700ff0

def z218 : W := mkw 0x0a80000290000002 0x002a00000a400000 0xdf807803fc03f02f 0xcf7e01e00ff00fc0

def z219 : W := mkw 0x0fff7ef963db5bbd 0xac3ffdfbe58f6d6e 0xffffffffe3ffffff 0xffffffffff8fffff

def z220 : W := mkw 0x1fffecf3fbff5bbb 0xec7fffb3cfeffd6e 0xfffffcf3ffffffff 0xfffffff3cfffffff

def z221 : W := mkw 0x0b80560000000000 0x002e015800000000 0x0380070000000000 0x080e001c00000000

def z222 : W := mkw 0x0b825702f50aac02 0xb02e095c0bd42ab0 0xffee7f03ff8ffc3f 0xffffb9fc0ffe3ff0

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x000078000003f020 0xc00001e000000fc0

def z224 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x001187fc007ccff0 0xf000461ff001f33f

def z225 : W := mkw 0x8576edf56fffdff9 0xae15dbb7d5bfff7f 0xffffffffffffffff 0xffffffffffffffff

def z226 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x401184fc007c0ff9 0x79004613f001f03f

def z227 : W := mkw 0x0b8f5618610a088c 0xa42e3d5861842822 0x238f871ce00c0cc8 0x288e3e1c73803033

def z228 : W := mkw 0x002028e000915330 0x080080a38002454c 0x000000e000000300 0x000000038000000c

def z229 : W := mkw 0x147ba8e14bfd5331 0xc851eea3852ff54c 0xfc7ff8e303fff337 0xf7f1ffe38c0fffcc

def z230 : W := mkw 0x9edb8127df7cc543 0xca7b6e049f7df315 0xffff8003fffccfff 0x3ffffe000ffff33f

def z231 : W := mkw 0x00000123b6d3ff03 0x380000048edb4ffc 0x10000003fff3ff3f 0x004000000fffcffc

def z232 : W := mkw 0x0ffd7edab002283e 0x303ff5fb6ac008a0 0xffffffffe0033002 0xffffffffff800cc0

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000c0ff9 0x000000000000303f

def z234 : W := mkw 0x0fff7ed8618b0abc 0xa43ffdfb61862c2a 0xeffffffce3830002 0xffbffffff38e0c00

def z235 : W := mkw 0x9a8b8126dd3cc542 0xca6a2e049b74f315 0x639f87fcfc7ccffd 0xfd8e7e1ff3f1f33f

def z236 : W := mkw 0x0000010004008400 0x0000000400100210 0x408007901c0ccffd 0xfd02001e4070333f

def z237 : W := mkw 0x00262090418902a8 0x840098824106240a 0x206e0090038c03d0 0x3081b802400e300f

def z238 : W := mkw 0x8020a9e40cb5d770 0x0a0082a79032d75d 0x4091fffc1c7ffffd 0xfd0247fff071ffff

def z239 : W := mkw 0x8ed981240c34c540 0x0a3b66049030d315 0xefff87fc1c7ccffd 0xffbffe1ff071f33f

def z240 : W := mkw 0x0ffd7ef902d1533d 0x083ff5fbe40b454c 0xff7e78e303f3f337 0xd7fdf9e38c0fcfcc

def z241 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c70786303f3f006 0x8671c1e18c0fcfc0

def z242 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xcf807f00fc000c08 0xcf3e01fc03f00030

def z243 : W := mkw 0x0ba67692f18b2aaa 0xb42e99da4bc62caa 0xff6e7c93e38f3ffb 0x7bfdb9f24f8e3cff

def z244 : W := mkw 0x0124649020830aa8 0x2404919240820c2a 0x0000649000030fe0 0x4000019240000c3f

def z245 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x03807f00fc03fc28 0xc80e01fc03f00ff0

def z246 : W := mkw 0x8000800408240040 0x0200020010209001 0x0001801c000c00c0 0x2000060070003003

def z247 : W := mkw 0x010456180000000c 0x0004115860000000 0x0000071c00000000 0x0000001c70000000

def z248 : W := mkw 0x0ffd7eda9000003e 0x003ff5fb6a400000 0xfffffffffc00000f 0xfffffffffff00000

def z249 : W := mkw 0x0000010004008400 0x0000000400100210 0x408007001c00cc2d 0xcd02001c00700330

def z250 : W := mkw 0x8ba6f7b6fdbfefea 0xbe2e9bdedbf6ffbf 0xffffffffffffffff 0xffffffffffffffff

def z251 : W := mkw 0x047028e102505131 0x0811c0a384094144 0xdc7078e30070f004 0xd771c1e38c01c3c0

def z252 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xafefff1c00000000 0x2abfbffc70000000

def z253 : W := mkw 0x9edb8027db7c4143 0xca7b6e009f6df105 0xffff80fffffc03df 0x3ffffe03fffff00f

def z254 : W := mkw 0x0b804402b0020802 0x202e01100ac00820 0xdf806403fc030c2f 0x4f7e01900ff00c30

def z255 : W := mkw 0x0efd28d80000003c 0x003bf4a360000000 0xefff80fc00000000 0x3fbffe03f0000000

def z256 : W := mkw 0x8b8dd71c0c24844c 0x022e375c70309211 0x238f871c1c0c0cc8 0x288e3e1c70703033

def z257 : W := mkw 0x00020000610a0880 0xa400080001842822 0x00000000e00c0cc8 0x0000000003803033

def z258 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xc3806700fc030c2b 0x4b0e019c03f00c30

def z259 : W := mkw 0x01247ed820830abc 0x240491fb60820c2a 0x00007ffc00030fe0 0xc00001fff0000c3f

def z260 : W := mkw 0x100b8000492c0000 0xc0402e000124b000 0x200f8000000c0000 0x20803e0000003000

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000410000c0cc8 0x2800001040003033

def z262 : W := mkw 0x1edb8023dbfd5303 0xc87b6e008f6ff54c 0xffff8003fffff33f 0x3ffffe000fffffcc

def z263 : W := mkw 0x047028c000000030 0x0011c0a300000000 0xdc7078e30003f027 0xd771c1e38c000fc0

def z264 : W := mkw 0x05746cf102d15339 0x0815d1b3c40b454c 0xff7e7cf303f3f337 0xfffdf9f3cc0fcfcc

def z265 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x409180fc1c7c03dd 0x3d024603f071f00f

def z266 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c6078e30383f322 0xc27181e38c0e0fcc

def z267 : W := mkw 0x047028c000000030 0x0011c0a300000000 0x007000e000000000 0x1001c00380000000

def z268 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x008187fc1c0ccfe8 0xe802061ff070333f

def z269 : W := mkw 0x0a80000290000002 0x002a00000a400000 0xdf800003fc00000f 0x0f7e00000ff00000

def z270 : W := mkw 0x1fdbd703ff6eac03 0xf07f6f5c0ffdbab0 0xffffff03fffffc3f 0xfffffffc0ffffff0

def z271 : W := mkw 0x1fdbc403fb6e0803 0xe07f6f100fedb820 0xffffe403ffff0c3f 0x7fffff900ffffc30

def z272 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x401180fc007cc3f5 0xf5004603f001f30f

def z273 : W := mkw 0x1ffff793ffefaeab 0xf47fffde4fffbeba 0xffffff93ffffffff 0xfffffffe4fffffff

def z274 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0xdf007803e003f027 0xc77c01e00f800fc0

def z275 : W := mkw 0x0450000102400001 0x0011400004090000 0xdc70780303f3f037 0xd771c1e00c0fcfc0

def z276 : W := mkw 0x8126e5b46dbfcfe8 0xae049b96d1b6ff3f 0xe36e6490ffffcfff 0x7b8db99243ffff3f

def z277 : W := mkw 0x0a80010294008402 0x002a00040a500210 0xdf800703fc00cc2f 0xcf7e001c0ff00330

def z278 : W := mkw 0x9ed981279e74c543 0x4a7b66049e79d315 0x5c9187ff1c7ccffd 0xfd72461ffc71f33f

def z279 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6000e38f0ffb 0x028db980038e3c3f

def z280 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0x0c00180000000000 0x0030006000000000

def z281 : W := mkw 0x0a80000290000002 0x002a00000a400000 0x03800000fc000008 0x080e000003f00000

def z282 : W := mkw 0x100280014b6c0001 0xc0400a00052db000 0x0000000003fc0010 0x00000000000ff000

def z283 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaf6e780000000000 0x02bdb9e000000000

def z284 : W := mkw 0x010057002402ac00 0x3004015c00900ab0 0x0000070000000c00 0x0000001c00000030

def z285 : W := mkw 0x047228e163db5bb1 0xac11c8a3858f6d6e 0xdc7078e3e3ffffff 0xd771c1e38f8fffff

def z286 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807b03fc03f006 0x867e01ec0ff00fc0

def z287 : W := mkw 0x8b80d7240c34c540 0x0a2e035c9030d315 0xcf91fffc1c7ccffd 0xff3e47fff071f33f

def z288 : W := mkw 0x1ef9a8e39af55333 0x487be6a38e6bd54c 0xdcf1f8e31ff3f337 0xd773c7e38c7fcfcc

def z289 : W := mkw 0x157fe4916bef0aa9 0xe455ff9245afbc2a 0xe37fe490e3ff0ffb 0x7b8dff92438ffc3f

def z290 : W := mkw 0x1edb0003d3480003 0xc07b6c000f4d2000 0xffff8003e3800002 0x3ffffe000f8e0000

def z291 : W := mkw 0x0124649000000028 0x0004919240000000 0xa36e600000000000 0x028db98000000000

def z292 : W := mkw 0x800081250ef5d741 0x0a000204943bd75d 0x509187ff1fffffff 0xfd42461ffc7fffff

def z293 : W := mkw 0x1b8bd702fd2eac02 0xf06e2f5c0bf4bab0 0xff8fff03fc0ffc2f 0xeffe3ffc0ff03ff0

def z294 : W := mkw 0x0124649020020828 0x2004919240800820 0xe36e6490e0030c2b 0x7b8db99243800c30

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0xe36e000000000000 0x3b8db80000000000

def z296 : W := mkw 0x8b8dd73c0c34c54c 0x0a2e375cf030d315 0x639f87fc1c7ccffd 0xfd8e7e1ff071f33f

def z297 : W := mkw 0x0b80560020020800 0x202e015800800820 0xcf807f00e0030c2b 0xcf3e01fc03800c30

def z298 : W := mkw 0x0ffd649000000028 0x003ff59240000000 0xefffe49000000000 0x7fbfff9240000000

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0xc060000003800013 0x13018000000e0000

def z300 : W := mkw 0x9fffe5b7ffffcfeb 0xee7fff96dfffff3f 0xffffe7ffffffcfff 0xffffff9fffffff3f

def z301 : W := mkw 0x0ed01b639650f513 0x183b406d8e5943d4 0x1c901b631c70f004 0x8472406d8c71c3c0

def z302 : W := mkw 0x045080010a640001 0x0011420004299000 0xdcf180031ffc001f 0x3f73c6000c7ff000

def z303 : W := mkw 0x0fd9560000000000 0x003f655800000000 0xefffff0000000000 0xffbffffc00000000

def z304 : W := mkw 0x800081040c248440 0x0200020410309211 0x4091871c1c7c0cdd 0x3d02461c7071f033

def z305 : W := mkw 0x80008126bc36ed42 0x3a0002049af0dbb5 0x10000003fc7fffff 0x004000000ff1ffff

def z306 : W := mkw 0x0000010004008400 0x0000000400100210 0x000007000000cc20 0xc000001c00000330

def z307 : W := mkw 0x1b82d703ff6eac03 0xf06e0b5c0ffdbab0 0xdf807f03fffffc3f 0xcf7e01fc0ffffff0

def z308 : W := mkw 0x0ed9800008240000 0x003b660000209000 0xefff80001c7c001d 0x3fbffe000071f000

def z309 : W := mkw 0x8ffd7ffc0410c57c 0x0a3ff5fff0104315 0xeffffffc0000cfe0 0xffbffffff000033f

def z310 : W := mkw 0x0a820002d1080002 0x802a08000b442000 0xffee0003ff8c001f 0x3fffb8000ffe3000

def z311 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0x4c919ffc00000000 0xfd32467ff0000000

def z312 : W := mkw 0x1edb8023db7c4103 0xc87b6e008f6df104 0xffff80e3fffcc33f 0xfffffe038ffff30c

def z313 : W := mkw 0x1ed993039e64a403 0x507b664c0e799290 0x1c919b031c70f004 0x8472466c0c71c3c0

def z314 : W := mkw 0x1a8b8003db6c0003 0xc06a2e000f6db000 0x338f8003fffc001f 0x28ce3e000ffff000

def z315 : W := mkw 0x0100560000000000 0x0004015800000000 0x00007f0000000000 0xc00001fc00000000

def z316 : W := mkw 0x0450086102505111 0x0811402184094144 0xdc1078630073f027 0xc77041e18c01cfc0

def z317 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf91fffffc03fc2f 0xff7e47fffff00ff0

def z318 : W := mkw 0x0ba4769000000028 0x002e91da40000000 0xefee7f9000000000 0xffbfb9fe40000000

def z319 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc000c0ff9 0xffbffffff000303f

def z320 : W := mkw 0x0fd95702b402ac02 0x303f655c0ad00ab0 0xffffff03fc03fc2f 0xfffffffc0ff00ff0

def z321 : W := mkw 0x0104441000000008 0x0004111040000000 0x230e041000000000 0x288c381040000000

def z322 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7c0fd8 0x3802461ff071f03f

def z323 : W := mkw 0x0ffd7ed820830abc 0x243ff5fb60820c2a 0xeffffffc00030fe0 0xffbffffff0000c3f

def z324 : W := mkw 0x0b80560000000000 0x002e015800000000 0xcf91fffc00000000 0xff3e47fff0000000

def z325 : W := mkw 0x8106c5146d2e8cc8 0xa6041b1451b4ba33 0x238f871cfc0c0cc8 0x288e3e1c73f03033

def z326 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0xdc60788303833333 0x537181e20c0e0ccc

def z327 : W := mkw 0x00242090008102a8 0x040090824002040a 0x00000090000003c0 0x000000024000000f

def z328 : W := mkw 0x0450000000000000 0x0011400000000000 0xcc70000000000000 0x1731c00000000000

def z329 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0x60ff87fc00000000 0xfd83fe1ff0000000

def z330 : W := mkw 0x1fff7edbd348003f 0xc07ffdfb6f4d2000 0xffffffffe3800002 0xffffffffff8e0000

def z331 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x1f801f03fc00fc0c 0x8c7e007c0ff003f0

def z332 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x1c7018e303f0f314 0x9471c0638c0fc3cc

def z333 : W := mkw 0x0000002000104100 0x0800000080004104 0x409187fc0070c335 0xfd02461ff001c30c

def z334 : W := mkw 0x0020208000810220 0x0000808200020408 0x0000608000030320 0x4000018200000c0c

def z335 : W := mkw 0x0b865712f50aac8a 0xb42e195c4bd42ab2 0xff8e7f13fc0ffcef 0xeffe39fc4ff03ff3

def z336 : W := mkw 0x1efba8c3dbed1233 0xc07beea30f6fb448 0xfffff803ffff301f 0x3fffffe00ffffcc0

def z337 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xef7e78e000000000 0xd7bdf9e380000000

def z338 : W := mkw 0x0ba67692f18b2aaa 0xb42e99da4bc62caa 0xbf6e7803e3833002 0x02fdb9e00f8e0cc0

def z339 : W := mkw 0x0ba47792b402ac2a 0x302e91de4ad00ab0 0xffee7f93fc03fc2f 0xffffb9fe4ff00ff0

def z340 : W := mkw 0x1edb9a4bdb6c0017 0xc07b6e692f6db000 0xffff9b6ffffc001f 0xbffffe6dbffff000

def z341 : W := mkw 0x1b8fc412f92e088a 0xe46e3f104be4b822 0x238f8410fc0c0cc8 0x288e3e1043f03033

def z342 : W := mkw 0x0ffd7ed90240003d 0x003ff5fb64090000 0xffffffff03f00017 0xfffffffffc0fc000

def z343 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0x00000000e3830002 0x00000000038e0c00

def z344 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf800703fc000c0f 0x0f7e001c0ff00030

def z345 : W := mkw 0x002028e000915330 0x080080a38002454c 0x000078e00003f320 0xc00001e380000fcc

def z346 : W := mkw 0x0b8d571ab402ac0e 0x302e355c6ad00ab0 0xff8fff1ffc03fc2f 0xeffe3ffc7ff00ff0

def z347 : W := mkw 0x800001240410c540 0x0a00000490104315 0x409187fc0000cfe0 0xfd02461ff000033f

def z348 : W := mkw 0x0024209000000028 0x0000908240000000 0x206e009000000000 0x3081b80240000000

def z349 : W := mkw 0x1a8b8002d92c0002 0xc06a2e000b64b000 0xff8f8003fc0c000f 0x2ffe3e000ff03000

def z350 : W := mkw 0x0b80560000000000 0x002e015800000000 0x8f00780000000000 0x023c01e000000000

def z351 : W := mkw 0x1edb8103df6c8403 0xc07b6e040f7db210 0xffff8703fffccc3f 0xfffffe1c0ffff330

def z352 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409183ec1c70c335 0xd502460fb071c30c

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3000000e000000b 0x0b0c000003800000

def z354 : W := mkw 0x8026a1b44dbdc7e8 0x8e009a86d136f71f 0x60ff87fc1ffccffd 0xfd83fe1ff07ff33f

def z355 : W := mkw 0x0022208041890220 0x8000888201062408 0xe36e6080e38f033b 0x7b8db982038e3c0c

def z356 : W := mkw 0x0ba47ed80000003c 0x002e91fb60000000 0xcf807ffc00000000 0xcf3e01fff0000000

def z357 : W := mkw 0x8470a8e50af55371 0x0a11c2a3942bd54d 0xdc71f8ff03fff3f7 0xf771c7e3fc0fffcf

def z358 : W := mkw 0x8ffdfefc0834417c 0x0a3ff7fbf020d105 0xeffffffc007c03d0 0xffbffffff001f00f

def z359 : W := mkw 0x0fff7ed84108003c 0x803ffdfb61042000 0xeffffffce38c001b 0xffbffffff38e3000

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc00000300000007 0x077000000c000000

def z361 : W := mkw 0x0000000290000002 0x000000000a400000 0x10000003fc00000f 0x004000000ff00000

def z362 : W := mkw 0x0002002163db5b81 0xac000800858f6d6e 0x10000003e3ffffff 0x004000000f8fffff

def z363 : W := mkw 0x8106c5346d3ecdc8 0xae041b14d1b4fb37 0x639f87fcfc7ccffd 0xfd8e7e1ff3f1f33f

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x0091836c00000000 0x8402460db0000000

def z365 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x0091877c1c7ccccc 0xac02461df071f333

def z366 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x0011806c00700000 0x00004601b001c000

def z367 : W := mkw 0x0000800008240000 0x0000020000209000 0x409184901c7c0ffd 0x7d0246124071f03f

def z368 : W := mkw 0x0000002000915300 0x080000008002454c 0x000000000003f320 0x0000000000000fcc

def z369 : W := mkw 0x00020102f58bae82 0xb40008040bd62eba 0x10000003ff8fffff 0x004000000ffe3fff

def z370 : W := mkw 0x0ef93ae902d15335 0x083be4eba40b454c 0xdcf1fbef03f3f337 0xd773c7efbc0fcfcc

def z371 : W := mkw 0x1fdbd703ff6eac03 0xf07f6f5c0ffdbab0 0xffff8703fffc0c1f 0x3ffffe1c0ffff030

def z372 : W := mkw 0x0100560020022800 0x30040158008008a0 0x0000780000033000 0x000001e000000cc0

def z373 : W := mkw 0x145b000143480001 0xc0516c00050d2000 0x206e000003800000 0x0081b800000e0000

def z374 : W := mkw 0x0450000102400001 0x0011400004090000 0x0070000003f00010 0x1001c000000fc000

def z375 : W := mkw 0x1edb8103ff6eac03 0xf07b6e040ffdbab0 0xffff8003fffffc3f 0x3ffffe000ffffff0

def z376 : W := mkw 0x002028e102d15331 0x080080a3840b454c 0x100078e303f3f337 0xc04001e38c0fcfcc

def z377 : W := mkw 0x1ffffedbdb6c003f 0xc07ffffb6f6db000 0xfffff803fffc001f 0x3fffffe00ffff000

def z378 : W := mkw 0x1ffbffe3ffffff33 0xf87fefff8ffffffc 0xffffffe3ffffff3f 0xffffffff8ffffffc

def z379 : W := mkw 0x147ba8e14bfd5331 0xc851eea3852ff54c 0x207f80e003fc0310 0x3081fe03800ff00c

def z380 : W := mkw 0x0ba47fdab402ac3e 0x302e91ff6ad00ab0 0xdf807ffffc03fc2f 0xcf7e01fffff00ff0

def z381 : W := mkw 0x1b8fd61ad92c000e 0xc06e3f586b64b000 0x238f871cfc0c0008 0x288e3e1c73f03000

def z382 : W := mkw 0x14528003db6c0003 0xc0514a000f6db000 0xdc700003fffc001f 0x1771c0000ffff000

def z383 : W := mkw 0x800081250ef5d741 0x0a000204943bd75d 0x100000031fffffff 0x004000000c7fffff

def z384 : W := mkw 0x810057242412ed40 0x3a04015c90904bb5 0x00007ffc0003ffe0 0xc00001fff0000fff

def z385 : W := mkw 0x1fdfc413fb6e088b 0xe47f7f104fedb822 0xffff8413fffc0cdf 0x3ffffe104ffff033

def z386 : W := mkw 0x0ba67792f58baeaa 0xb42e99de4bd62eba 0xe3ee6790ff8f0ffb 0x7b8fb99e43fe3c3f

def z387 : W := mkw 0x81247ffc0410c57c 0x0a0491fff0104315 0x00007ffc0000cfe0 0xc00001fff000033f

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000090000c03d0 0x300000024000300f

def z389 : W := mkw 0x1efba8c3db6c0033 0xc07beea30f6db000 0xfffff8e3fffc001f 0xffffffe38ffff000

def z390 : W := mkw 0x05707fe126d3ff31 0x3815c1ff849b4ffc 0xdc707fe303f3ff37 0xd771c1ff8c0fcffc

def z391 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409180001c7ccffd 0x3d0246000071f33f

def z392 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409187fc1c70c004 0xfd02461ff071c300

def z393 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0xef8fff1c00000000 0xefbe3ffc70000000

def z394 : W := mkw 0x1ed988639a745113 0x487b66218e69d144 0x1c9198631c70f004 0x847246618c71c3c0

def z395 : W := mkw 0x0000802008344100 0x080002008020d104 0x409180e01c7cc33d 0xfd0246038071f30c

def z396 : W := mkw 0x01247fd82402ac3c 0x300491ff60900ab0 0x00007ffc0003fc20 0xc00001fff0000ff0

def z397 : W := mkw 0x0000010004008400 0x0000000400100210 0x409187fc1c00cc2d 0xfd02461ff0700330

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z399 : W := mkw 0x8a8093269c34e542 0x1a2a024c9a70d395 0x5c919fff1c7cfffd 0xfd72467ffc71f3ff

def z400 : W := mkw 0x012664b163db5ba9 0xac049992c58f6d6e 0xf36e6493e3ffffff 0x7bcdb9924f8fffff

def z401 : W := mkw 0x00000102b402ac02 0x300000040ad00ab0 0xdc007803fc03fc2f 0xc77001e00ff00ff0

def z402 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0x206e000000000000 0x0081b80000000000

def z403 : W := mkw 0x1effa093dbed02ab 0xc47bfe824f6fb40a 0xffff8093fffc03df 0x3ffffe024ffff00f

def z404 : W := mkw 0x0450086102d15311 0x08114021840b454c 0x1c10186303f3f337 0x847040618c0fcfcc

def z405 : W := mkw 0x002020a000914320 0x080080828002450c 0xc07060e003f3c337 0xd701c183800fcf0c

def z406 : W := mkw 0x01266490610a08a8 0xa404999241842822 0xe36e6490e00c0cc8 0x7b8db99243803033

def z407 : W := mkw 0x1edb8002d92c0002 0xc07b6e000b64b000 0xefff8000fc0c0008 0x3fbffe0003f03000

def z408 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x401000e01c7ccffd 0xd50040038071f33f

def z409 : W := mkw 0x845089650e74d551 0x0a1142259439d355 0x1c919b6f1c70f004 0x8472466dbc71c3c0

def z410 : W := mkw 0x0ff07fc3b6c3be33 0x303fc1ff0edb0ef8 0xdfe07f03ff83fc2f 0xcf7f81fc0ffe0ff0

def z411 : W := mkw 0x0000002102d15301 0x08000000840b454c 0x501000e303f3f337 0xd54040038c0fcfcc

def z412 : W := mkw 0x00000102b402ac02 0x300000040ad00ab0 0x50800703fc03fc2f 0xcd42001c0ff00ff0

def z413 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6490e3830fe2 0x428db992438e0c3f

def z414 : W := mkw 0x0a8013029400a402 0x102a004c0a500290 0x5c801f031c00fc2d 0xcd72007c0c7003f0

def z415 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807f03fc033c0a 0x0a7e01fc0ff00cf0

def z416 : W := mkw 0x0450084102401011 0x0011402104090040 0x1c00180300003000 0x007000600c0000c0

def z417 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0x639f87fc00000000 0xfd8e7e1ff0000000

def z418 : W := mkw 0x802029e40491d770 0x0a0080a79012475d 0x00007ffc0003ffe0 0xc00001fff0000fff

def z419 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x23ff87fc00000000 0x388ffe1ff0000000

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x0081871c00000000 0x2802061c70000000

def z421 : W := mkw 0x0470a8e10af55331 0x0811c2a3842bd54c 0xdcf1f8e31ffff33f 0xff73c7e38c7fffcc

def z422 : W := mkw 0x002020a102d15321 0x08008082840b454c 0xd060608303f3f337 0x534181820c0fcfcc

def z423 : W := mkw 0x01064410610a0888 0xa404191041842822 0x630e0490e00c0ff9 0x798c38124380303f

def z424 : W := mkw 0x8ffdffdc0c24847c 0x023ff7ff70309211 0xeffffffc1c0c0cc8 0xffbffffff0703033

def z425 : W := mkw 0x847029e506d1d771 0x0a11c0a7941b475d 0xdc707fff03f3fff7 0xd771c1fffc0fcfff

def z426 : W := mkw 0x812465b42493cfe8 0x2e049196d0924f3f 0x000067fc0003cfe0 0xc000019ff0000f3f

def z427 : W := mkw 0x01266cf0619b5bb8 0xac0499b3c1866d6e 0xe36e7cf0e38ffffb 0xfb8db9f3c38e3fff

def z428 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x409187fc007c03d0 0xfd02461ff001f00f

def z429 : W := mkw 0x047628f143d953b9 0x8c11d8a3c50f654e 0xfc7e78f303fff3f7 0xf7f1f9e3cc0fffcf

def z430 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x4091836c1c7cc01d 0xbd02460db071f300

def z431 : W := mkw 0x1ffdfedb9a64003f 0x407ff7fb6e699000 0xffffffff1c700004 0xfffffffffc71c000

def z432 : W := mkw 0x1ed980039a640003 0x407b66000e699000 0x5c9180031c7c001d 0x3d7246000c71f000

def z433 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x0081871c1c7ccffd 0x2802061c7071f33f

def z434 : W := mkw 0x0fff6490618b0aa8 0xa43ffd9241862c2a 0xefffe490e38f0ffb 0x7fbfff92438e3c3f

def z435 : W := mkw 0x0ffd7fdab402ac3e 0x303ff5ff6ad00ab0 0xffee7f03fc03fc2f 0xcfffb9fc0ff00ff0

def z436 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0xefff9b6c00000000 0xbfbffe6db0000000

def z437 : W := mkw 0x8124e5b42cb7cfe8 0x2e049396d0b2df3f 0x4091e7fc1c7fcffd 0xfd02479ff071ff3f

def z438 : W := mkw 0x01267790658baea8 0xb40499de41962eba 0xe36e7f90e38ffffb 0xfb8db9fe438e3fff

def z439 : W := mkw 0x0ff07ec000000030 0x003fc1fb00000000 0xcff07fe000000000 0xdf3fc1ff80000000

def z440 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xef6e7c9000000000 0x7bbdb9f240000000

def z441 : W := mkw 0x8a8081269c34c542 0x0a2a02049a70d315 0xdf9187fffc7ccfff 0xff7e461ffff1f33f

def z442 : W := mkw 0x0124649020830aa8 0x2404919240820c2a 0xc3006490e0030feb 0x4b0c019243800c3f

def z443 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x000007fc1c7ccffd 0xc000001ff071f33f

def z444 : W := mkw 0x002028e000915330 0x080080a38002454c 0x401078e00073f335 0xd50041e38001cfcc

def z445 : W := mkw 0x0fd05703b642ac03 0x303f415c0ed90ab0 0xdff07f03fff3fc3f 0xdf7fc1fc0fffcff0

def z446 : W := mkw 0x047029e3b6d3ff33 0x3811c0a78edb4ffc 0xdc7078e3fff3ff3f 0xd771c1e38fffcffc

def z447 : W := mkw 0x1472a8e3dbfd5333 0xc851caa38f6ff54c 0xdc7078e3fffff33f 0xd771c1e38fffffcc

def z448 : W := mkw 0x05746cd000000038 0x0015d1b340000000 0xef7e7cf000000000 0xffbdf9f3c0000000

def z449 : W := mkw 0x0bad76980000002c 0x002eb5da60000000 0xe3efe79c00000000 0x7b8fbf9e70000000

def z450 : W := mkw 0x1fdb5703f74aac03 0xf07f6d5c0fdd2ab0 0xffee7f03ff83fc2f 0xcfffb9fc0ffe0ff0

def z451 : W := mkw 0x8b805726b412ed42 0x3a2e015c9ad04bb5 0xdf807ffffc03ffef 0xcf7e01fffff00fff

def z452 : W := mkw 0x1efba083dbed0223 0xc07bee820f6fb408 0xffffe083ffff033f 0x7fffff820ffffc0c

def z453 : W := mkw 0x0a89120800000004 0x002a244820000000 0x0081830c00000000 0x0002060c30000000

def z454 : W := mkw 0x1b8bd702fd2eac02 0xf06e2f5c0bf4bab0 0x238f8700fc0c0c08 0x288e3e1c03f03030

def z455 : W := mkw 0x0ff07fc2b402ac32 0x303fc1ff0ad00ab0 0xdff07fe3fc03fc2f 0xdf7fc1ff8ff00ff0

def z456 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaf7ff8fc00000000 0x32bdffe3f0000000

def z457 : W := mkw 0x8000002400104140 0x0a00000090004105 0x000000fc000003c0 0x00000003f000000f

def z458 : W := mkw 0x0002000041080000 0x8000080001042000 0x206e0000038c0010 0x3081b800000e3000

def z459 : W := mkw 0x1ed980039a640003 0x407b66000e699000 0xdf918003fc70000f 0x0f7e46000ff1c000

def z460 : W := mkw 0x0ba67690618b0aa8 0xa42e99da41862c2a 0xefee7f90e38f0ffb 0xffbfb9fe438e3c3f

def z461 : W := mkw 0x10028002d92c0002 0xc0400a000b64b000 0x00000000fc0c0008 0x0000000003f03000

def z462 : W := mkw 0x8ff0ffe7bef7ff73 0x3a3fc3ff9efbdffd 0xdff1ffffffffffff 0xff7fc7ffffffffff

def z463 : W := mkw 0x1effa8dbdb6c003f 0xc07bfea36f6db000 0xffff80fffffc001f 0x3ffffe03fffff000

def z464 : W := mkw 0x1ffffed94b6c003d 0xc07ffffb652db000 0xeffffffc03fc0010 0xffbffffff00ff000

def z465 : W := mkw 0x1edb0003d3480003 0xc07b6c000f4d2000 0xffee0003ff80000f 0x0fffb8000ffe0000

def z466 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaf6e7ffc00000000 0xc2bdb9fff0000000

def z467 : W := mkw 0x8ffffffc6dbfcffc 0xae3ffffff1b6ff3f 0xeffffffcffffcfff 0xffbffffff3ffff3f

def z468 : W := mkw 0x05766cf163db5bb9 0xac15d9b3c58f6d6e 0xe37e64f0e3ff0ffb 0x7b8df993c38ffc3f

def z469 : W := mkw 0x01266592f58baeaa 0xb40499964bd62eba 0xf36e6493ff8fffff 0x7bcdb9924ffe3fff

def z470 : W := mkw 0x0000800008240000 0x0000020000209000 0x008180001c0c0008 0x2802060000703000

def z471 : W := mkw 0x05746cf122d35bb9 0x2c15d1b3c48b4d6e 0xdc707cf303f3fff7 0xd771c1f3cc0fcfff

def z472 : W := mkw 0x0000002000104100 0x0800000080004104 0xdc1078e30073f337 0xd77041e38c01cfcc

def z473 : W := mkw 0x0020208000810220 0x0000808200020408 0x8060600003830002 0x02018180000e0c00

def z474 : W := mkw 0x0000000102c11201 0x00000000040b0448 0x1000000303833002 0x004000000c0e0cc0

def z475 : W := mkw 0x8b80d726bc36ed42 0x3a2e035c9af0dbb5 0xdf807f03fc7fffff 0xcf7e01fc0ff1ffff

def z476 : W := mkw 0x057f6cd8618b0abc 0xa415fdb361862c2a 0xe37fe4fce38f0ffb 0x7b8dff93f38e3c3f

def z477 : W := mkw 0x0b8057029400a402 0x102e015c0a500290 0xdf807f031c00f004 0xcf7e01fc0c7003c0

def z478 : W := mkw 0x0002000041080000 0x8000080001042000 0xa36e0000e3800002 0x028db800038e0000

def z479 : W := mkw 0x01247ed80000003c 0x000491fb60000000 0xe36e7ffc00000000 0xfb8db9fff0000000

def z480 : W := mkw 0x8000802408344140 0x0a0002009020d105 0x00000000007c03d0 0x000000000001f00f

def z481 : W := mkw 0x0ef928e102d15331 0x083be4a3840b454c 0xfffff8e303f3f337 0xffffffe38c0fcfcc

def z482 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0xdf807803fc03300f 0x0f7e01e00ff00cc0

def z483 : W := mkw 0x8124e5b40c34c568 0x0a049396d030d315 0xe3ffe7fc1c7ccffd 0xff8fff9ff071f33f

def z484 : W := mkw 0x0000000000810200 0x0000000000020408 0x0000000003830333 0x00000000000e0c0c

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000c0019 0x3900000000003000

def z486 : W := mkw 0x0ed9000290000002 0x003b64000a400000 0xffff8003fc00000f 0x3ffffe000ff00000

def z487 : W := mkw 0x8000010404008440 0x0200000410100211 0x0000071c00000cc0 0x0000001c70000033

def z488 : W := mkw 0x145b8003db6c0003 0xc0516e000f6db000 0x307f8003fffc001f 0x30c1fe000ffff000

def z489 : W := mkw 0x0100440020020800 0x2004011000800820 0xc3006490e00f0ffb 0x7b0c019243803c3f

def z490 : W := mkw 0x0ffd7ed80081023c 0x003ff5fb60020408 0xeffffffc03830333 0xffbffffff00e0c0c

def z491 : W := mkw 0x0fff7ed8418902bc 0x843ffdfb6106240a 0xeffffffc038c03d0 0xffbffffff00e300f

def z492 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x400004901c7ccffd 0x790000124071f33f

def z493 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6400e3830c2b 0x4b8db990038e0c30

def z494 : W := mkw 0x0fd95e4800000014 0x003f657920000000 0xcf91ff6c00000000 0xcf3e47fdb0000000

def z495 : W := mkw 0x1efba8e3dbfd5333 0xc87beea38f6ff54c 0xffff80e3fffc031f 0x3ffffe038ffff00c

def z496 : W := mkw 0x0ed9000102400001 0x003b640004090000 0xffff800303f00017 0x3ffffe000c0fc000

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x408000001c00000d 0x0d02000000700000

def z498 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c7078e303f33312 0x1271c1e38c0fcccc

def z499 : W := mkw 0x0fdd56180000000c 0x003f755860000000 0xefff871c00000000 0x3fbffe1c70000000

def z500 : W := mkw 0x0b865712f50aac8a 0xb42e195c4bd42ab2 0x238e0710fc0c0cc8 0x288e381c43f03033

def z501 : W := mkw 0x800081040c248440 0x0200020410309211 0x4081871c1c0ccced 0xed02061c70703333

def z502 : W := mkw 0x002028c000811230 0x000080a300020448 0x0000780000033000 0x000001e000000cc0

def z503 : W := mkw 0x10020003d3480003 0xc04008000f4d2000 0x10000003e3800002 0x004000000f8e0000

def z504 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x1c807f031c03fc24 0xc47201fc0c700ff0

def z505 : W := mkw 0x800001240410c540 0x0a00000490104315 0x401007fc0070cff5 0xd500401ff001c33f

def z506 : W := mkw 0x00262090418902a8 0x840098824106240a 0xe36e0090e38c03db 0x3b8db802438e300f

def z507 : W := mkw 0x01004502b402ac02 0x300401140ad00ab0 0xd3006403fc03fc2f 0x4b4c01900ff00ff0

def z508 : W := mkw 0x8b80d706bc26ac42 0x322e035c1af09ab1 0xdf81ff1ffc0ffcef 0xef7e07fc7ff03ff3

def z509 : W := mkw 0x8026a0b449bd43e8 0x8e009a82d126f50f 0x207f80fc03fc03d0 0x3081fe03f00ff00f

def z510 : W := mkw 0x0b8057002402ac00 0x302e015c00900ab0 0xcf807f000003fc20 0xcf3e01fc00000ff0

def z511 : W := mkw 0x0fd95f4ab402ac16 0x303f657d2ad00ab0 0xdf91ff6ffc03fc2f 0xcf7e47fdbff00ff0

def z512 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x107000e303f3f337 0x1041c0038c0fcfcc

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x000007fc00000000 0xc000001ff0000000

def z514 : W := mkw 0x0020208000810220 0x0000808200020408 0xdc6078830383f337 0xd77181e20c0e0fcc

def z515 : W := mkw 0x145980010a640001 0x4051660004299000 0x0011800000700000 0x000046000001c000

def z516 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0xdf007c03e0033c2b 0x4b7c01f00f800cf0

def z517 : W := mkw 0x1efb28c3d3c91233 0xc07beca30f4f2448 0xbf6e7803e3833002 0x02fdb9e00f8e0cc0

def z518 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xcc7078e003f00310 0xd731c1e3800fc00c

def z519 : W := mkw 0x0452000143480001 0x80114800050d2000 0xff7e0003e3fc001f 0x3ffdf8000f8ff000

def z520 : W := mkw 0x9edb8127df7cc543 0xca7b6e049f7df315 0xffff836ffffcc01f 0xbffffe0dbffff300

def z521 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0x230e000000000000 0x008c380000000000

def z522 : W := mkw 0x0b80560000000000 0x002e015800000000 0xdf807f030003f027 0xcf7e01fc0c000fc0

def z523 : W := mkw 0x0104441020020888 0x2404111040800822 0x0000041000000cc0 0x0000001040000033

def z524 : W := mkw 0x0ffd7ed902c1123d 0x003ff5fb640b0448 0xbf6e780303833002 0x02fdb9e00c0e0cc0

def z525 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x206e6490038f0ff0 0x7081b992400e3c3f

def z526 : W := mkw 0x0ba07782b483ae22 0x302e81de0ad20eb8 0xdfe07f83ff83ff3f 0xdf7f81fe0ffe0ffc

def z527 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0xdc6078030383f027 0xc77181e00c0e0fc0

def z528 : W := mkw 0x0ffd7ef902d1533d 0x083ff5fbe40b454c 0xeffffffc03f00310 0xffbffffff00fc00c

def z529 : W := mkw 0x01024400618b0a80 0xa404091001862c2a 0xc3006400e38f0ffb 0x4b0c0190038e3c3f

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x001180fc00000000 0x30004603f0000000

def z531 : W := mkw 0x0100440020020800 0x2004011000800820 0x0000640000030c20 0x4000019000000c30

def z532 : W := mkw 0x0a80000290000002 0x002a00000a400000 0x1c8000031c000004 0x047200000c700000

def z533 : W := mkw 0x145b80014b6c0001 0xc0516e00052db000 0xe37f8000e3fc001b 0x3b8dfe00038ff000

def z534 : W := mkw 0x8470a9e50ef5d771 0x0a11c2a7943bd75d 0xdc7078e31fffffff 0xd771c1e38c7fffff

def z535 : W := mkw 0x0a8013029400a402 0x102a004c0a500290 0x008003001c000000 0x0002000c00700000

def z536 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0x0060000003800000 0x00018000000e0000

def z537 : W := mkw 0x00000002b0022802 0x300000000ac008a0 0x10000003e0033002 0x004000000f800cc0

def z538 : W := mkw 0x10028103ff6eac03 0xf0400a040ffdbab0 0x10000003fffffc3f 0x004000000ffffff0

def z539 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x407000e003f0c335 0xd501c003800fc30c

def z540 : W := mkw 0x800001240410c540 0x0a00000490104315 0x408007fc1c00cfed 0xcd02001ff070033f

def z541 : W := mkw 0x05747ef902d1533d 0x0815d1fbe40b454c 0xdc707fff03f3f337 0xd771c1fffc0fcfcc

def z542 : W := mkw 0x0124649000000028 0x0004919240000000 0xe36e6490000c0ff9 0x7b8db9924000303f

def z543 : W := mkw 0x1efb28e3d3d95333 0xc87beca38f4f654c 0xff7e78e3e3f3f337 0xd7fdf9e38f8fcfcc

def z544 : W := mkw 0x8ffdfffebc36ed7e 0x3a3ff7fffaf0dbb5 0xfffffffffc7fffff 0xfffffffffff1ffff

def z545 : W := mkw 0x01064410610a0888 0xa404191041842822 0xe36e0410e38c0cdb 0x3b8db810438e3033

def z546 : W := mkw 0x0100450024028c00 0x2004011400900a30 0xc3806700fc03cc2f 0xcf0e019c03f00f30

def z547 : W := mkw 0x0000002000104100 0x0800000080004104 0x001000600070c004 0x840040018001c300

def z548 : W := mkw 0x05766cd163cb1ab9 0xa415d9b3458f2c6a 0xbf6e7803e3833002 0x02fdb9e00f8e0cc0

def z549 : W := mkw 0x01247ef80091533c 0x080491fbe002454c 0x00007ffc0003f320 0xc00001fff0000fcc

def z550 : W := mkw 0x8470a8e50af55371 0x0a11c2a3942bd54d 0x007180fc03fc03d0 0x3001c603f00ff00f

def z551 : W := mkw 0x01024400610a0800 0xa004091001842820 0xe36e6400e38f0c3b 0x7b8db990038e3c30

def z552 : W := mkw 0x9fdbd727ff7eed43 0xfa7f6f5c9ffdfbb5 0xffffffffffffffff 0xffffffffffffffff

def z553 : W := mkw 0x0ef93ac800000034 0x003be4eb20000000 0xccf1fbec00000000 0xd733c7efb0000000

def z554 : W := mkw 0x00262090418902a8 0x840098824106240a 0x206e000003800000 0x0081b800000e0000

def z555 : W := mkw 0x8470a9e50ef5d771 0x0a11c2a7943bd75d 0x40f187fc1ffccffd 0xfd03c61ff07ff33f

def z556 : W := mkw 0x0450000102400001 0x0011400004090000 0x9c60000303800002 0x027180000c0e0000

def z557 : W := mkw 0x0ed9000000000000 0x003b640000000000 0xaf6e000000000000 0x02bdb80000000000

def z558 : W := mkw 0x9fffffffdf7cc57f 0xca7fffffff7df315 0xfffffffffffccfff 0xfffffffffffff33f

def z559 : W := mkw 0x0450002102504101 0x0811400084094104 0xdc7000e303f0c337 0xd771c0038c0fc30c

def z560 : W := mkw 0x1fff7edbd348003f 0xc07ffdfb6f4d2000 0xbf6e7803e3800002 0x02fdb9e00f8e0000

def z561 : W := mkw 0x00222080618b0aa0 0xa400888201862c2a 0xc0606080e38f0ffb 0x53018182038e3c3f

def z562 : W := mkw 0x0450086102505111 0x0811402184094144 0x5c1018e30070f335 0xd57040638c01c3cc

def z563 : W := mkw 0x0000010004008400 0x0000000400100210 0xdc807f031c03fc2f 0xcf7201fc0c700ff0

def z564 : W := mkw 0x1ed99a4b9a640017 0x407b66692e699000 0x1c919b6f1c700004 0x8472466dbc71c000

def z565 : W := mkw 0x0124649020830aa8 0x2404919240820c2a 0x40006490000f0ff9 0x7900019240003c3f

def z566 : W := mkw 0x047028c000000030 0x0011c0a300000000 0x8c60780000000000 0x023181e000000000

def z567 : W := mkw 0x1126e493fbef0aab 0xe4449b924fefbc2a 0xf36e6493ffff0fff 0x7bcdb9924ffffc3f

def z568 : W := mkw 0x047028e000104130 0x0811c0a380004104 0xcc7078e00070c335 0xd731c1e38001c30c

def z569 : W := mkw 0x0b80570004008400 0x002e015c00100210 0xcf807f001c00cc2d 0xcf3e01fc00700330

def z570 : W := mkw 0x10028023dbfd5303 0xc8400a008f6ff54c 0x10000003fffff33f 0x004000000fffffcc

def z571 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbf7f8003e3fc0012 0x32fdfe000f8ff000

def z572 : W := mkw 0x000001029400a402 0x100000040a500290 0x100000031c00f004 0x004000000c7003c0

def z573 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfef8003ff8c000a 0x2affbe000ffe3000

def z574 : W := mkw 0x000081000c248400 0x0000020400309210 0x409187001c7ccc3d 0xfd02461c0071f330

def z575 : W := mkw 0x0000800008240000 0x0000020000209000 0x000000001c7c001d 0x000000000071f000

def z576 : W := mkw 0x10028003db6c0003 0xc0400a000f6db000 0x50918003fffc001f 0x3d4246000ffff000

def z577 : W := mkw 0x0a80120000000000 0x002a004800000000 0x0c801b0000000000 0x8432006c00000000

def z578 : W := mkw 0x0baf7698618b0aac 0xa42ebdda61862c2a 0xe3efe79ce38f0ffb 0x7b8fbf9e738e3c3f

def z579 : W := mkw 0x800001240410c540 0x0a00000490104315 0x000000000000cfe0 0x000000000000033f

def z580 : W := mkw 0x8a8093269c34e542 0x1a2a024c9a70d395 0x1c919b6f1c70f004 0x8472466dbc71c3c0

def z581 : W := mkw 0x0a80800298240002 0x002a02000a609000 0xdf918003fc7c001f 0x3f7e46000ff1f000

def z582 : W := mkw 0x0ff07ec3b2c33a33 0x303fc1fb0ecb0ce8 0x9f607803e3833002 0x027d81e00f8e0cc0

def z583 : W := mkw 0x0b8d571ab402ac0e 0x302e355c6ad00ab0 0x238f871cfc000c08 0x288e3e1c73f00030

def z584 : W := mkw 0x8b80d726bc36ed42 0x3a2e035c9af0dbb5 0x439187fcfc7ccffd 0xfd0e461ff3f1f33f

def z585 : W := mkw 0x0450002102d15301 0x08114000840b454c 0xdc70000303f3f337 0x1771c0000c0fcfcc

def z586 : W := mkw 0x1ed980039a640003 0x407b66000e699000 0xffff80031c700004 0x3ffffe000c71c000

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000030003f027 0x004000000c000fc0

def z588 : W := mkw 0x01207fe02493ff30 0x380481ff80924ffc 0x00007fe00003ff20 0xc00001ff80000ffc

def z589 : W := mkw 0x0ef028e392d15333 0x083bc0a38e4b454c 0xdff078e3fff3f33f 0xdf7fc1e38fffcfcc

def z590 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x230e6490e00f0fe8 0x688c399243803c3f

def z591 : W := mkw 0x0576649163cb0aa9 0xa415d992458f2c2a 0xff7e6493e3ff0fff 0x7ffdf9924f8ffc3f

def z592 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x00006490e38f0ffb 0x40000192438e3c3f

def z593 : W := mkw 0x0002000041890280 0x840008000106240a 0x00000000038c03d0 0x00000000000e300f

def z594 : W := mkw 0x1fd9d703be66ac03 0x707f675c0ef99ab0 0xdf91ff03fc73fc2f 0xcf7e47fc0ff1cff0

def z595 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0x40000490e38f0ffb 0x79000012438e3c3f

def z596 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0x03000000e0000000 0x000c000003800000

def z597 : W := mkw 0x1ffffedad92c003e 0xc07ffffb6b64b000 0xeffffffcfc0c0008 0xffbffffff3f03000

def z598 : W := mkw 0x145b80014b6c0001 0xc0516e00052db000 0x60ff80001ffc001d 0x3d83fe00007ff000

def z599 : W := mkw 0x002028e000915330 0x080080a38002454c 0xc06078e00383f333 0xd30181e3800e0fcc

def z600 : W := mkw 0x0ed0000392400003 0x003b40000e490000 0xdff00003fff0001f 0x1f7fc0000fffc000

def z601 : W := mkw 0x0fd05f63b652fd13 0x383f417d8ed94bf4 0xdf907f63fc73fc2f 0xcf7e41fd8ff1cff0

def z602 : W := mkw 0x8ed99b6c0c34c554 0x0a3b666db030d315 0x4c919ffc1c7ccffd 0xfd32467ff071f33f

def z603 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0xdc70780303f33017 0x1771c1e00c0fccc0

def z604 : W := mkw 0x800001240410c540 0x0a00000490104315 0x0000036c0000c000 0x8000000db0000300

def z605 : W := mkw 0x05766cd0618b0ab8 0xa415d9b341862c2a 0xef7e7cf0e38f0ffb 0xffbdf9f3c38e3c3f

def z606 : W := mkw 0x0000010004008400 0x0000000400100210 0x008003001c00c004 0x8402000c00700300

def z607 : W := mkw 0x05766cf163db5bb9 0xac15d9b3c58f6d6e 0xff7e78e3e3f3f337 0xd7fdf9e38f8fcfcc

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0x409187fc000c0ff9 0xfd02461ff000303f

def z609 : W := mkw 0x0100440020020800 0x2004011000800820 0xdf007c03e003fc2f 0xcf7c01f00f800ff0

def z610 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x4091876c1c70cc2d 0xcd02461db071c330

def z611 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x000000001c70c004 0x000000000071c300

def z612 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x1c1078e30073f324 0xc47041e38c01cfcc

def z613 : W := mkw 0x1bafe492f9af0aaa 0xe46ebf924be6bc2a 0xe3efe490ff8f0ffb 0x7b8fbf9243fe3c3f

def z614 : W := mkw 0x1ed980039a640003 0x407b66000e699000 0xdcf180031ff00017 0x1773c6000c7fc000

def z615 : W := mkw 0x0fff7ed8618b0abc 0xa43ffdfb61862c2a 0xef6e7c90e38f0ffb 0x7bbdb9f2438e3c3f

def z616 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6080e3830333 0x538db982038e0c0c

def z617 : W := mkw 0x1edb0003d3480003 0xc07b6c000f4d2000 0xff7e0003e3f00017 0x17fdf8000f8fc000

def z618 : W := mkw 0x1fdbd603fb6e2803 0xf07f6f580fedb8a0 0xfffff803ffff301f 0x3fffffe00ffffcc0

def z619 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x3f9f8003fc7c000c 0x2cfe7e000ff1f000

def z620 : W := mkw 0x8ffdfffd0ef5d77d 0x0a3ff7fff43bd75d 0xffffffff1fffffff 0xfffffffffc7fffff

def z621 : W := mkw 0x01247ed80000003c 0x000491fb60000000 0x0000780000000000 0x000001e000000000

def z622 : W := mkw 0x8ed99b6c0c34c554 0x0a3b666db030d315 0x0c919b6c1c70c004 0x8432466db071c300

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x4080070000000000 0xcd02001c00000000

def z624 : W := mkw 0x0000002102d15301 0x08000000840b454c 0x0000000003f00310 0x00000000000fc00c

def z625 : W := mkw 0x0ef03be396d1f733 0x183bc0ef8e5b47dc 0xdcf07be31ff3f337 0xd773c1ef8c7fcfcc

def z626 : W := mkw 0x1fffe493fbef0aab 0xe47fff924fefbc2a 0xffffe003ffff001f 0x3fffff800ffffc00

def z627 : W := mkw 0x100080039a640003 0x404002000e699000 0x100000031c700004 0x004000000c71c000

def z628 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6490e3830002 0x7b8db992438e0c00

def z629 : W := mkw 0x800001240410c540 0x0a00000490104315 0x400007fc000ccff9 0xf900001ff000333f

def z630 : W := mkw 0x847da9fc0c34c57c 0x0a11f6a7f030d315 0x60ff87fc1c7ccffd 0xfd83fe1ff071f33f

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x4091800000000000 0x3d02460000000000

def z632 : W := mkw 0x800281244d3cc540 0x8a000a049134f315 0xe3ff87fcfffccfff 0xff8ffe1ff3fff33f

def z633 : W := mkw 0x0ffd7fd80400843c 0x003ff5ff60100210 0xeffffffc1c00cc2d 0xffbffffff0700330

def z634 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0xec7ff8fc00000000 0xf7b1ffe3f0000000

def z635 : W := mkw 0x0ed91a6902505115 0x083b6469a4094144 0x1c919b6f0070f004 0x8472466dbc01c3c0

def z636 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f007f03e003fc22 0xc27c01fc0f800ff0

def z637 : W := mkw 0x945b80254b7c4141 0xca516e00952df105 0x207f80fc03fc03d0 0x3081fe03f00ff00f

def z638 : W := mkw 0x812665b4659bcfe8 0xae049996d1966f3f 0xe36e67fce38fcffb 0xfb8db99ff38e3f3f

def z639 : W := mkw 0x0450086102505111 0x0811402184094144 0xdc70186303f0f017 0x9771c0618c0fc3c0

def z640 : W := mkw 0x0ffd7ef80010413c 0x083ff5fbe0004104 0xeffffffc0070c335 0xffbffffff001c30c

def z641 : W := mkw 0x0459000000000000 0x0011640000000000 0x207f800000000000 0x3081fe0000000000

def z642 : W := mkw 0x945b81254f7cc541 0xca516e04953df315 0x60ff87fc1ffccffd 0xfd83fe1ff07ff33f

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000040000000c29 0x4900001000000030

def z644 : W := mkw 0x0ffdfed80824003c 0x003ff7fb60209000 0xeffffffc1c7c001d 0xffbffffff071f000

def z645 : W := mkw 0x0120648020830a20 0x2004819200820c28 0xc3606480e3830f3b 0x5b0d8192038e0c3c

def z646 : W := mkw 0x0a800102b402ac02 0x302a00040ad00ab0 0xdf800003fc03fc2f 0x0f7e00000ff00ff0

def z647 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x1c918003fffc001f 0x047246000ffff000

def z648 : W := mkw 0x0a8013029400a402 0x102a004c0a500290 0xdf801b03fc00f00f 0x8f7e006c0ff003c0

def z649 : W := mkw 0x002028e000915330 0x080080a38002454c 0xdc0078e30003f327 0xc77001e38c000fcc

def z650 : W := mkw 0x8126e4b469bf4be8 0xae049b92d1a6fd2f 0xe37fe4fce3ff0ffb 0x7b8dff93f38ffc3f

def z651 : W := mkw 0x002428d80000003c 0x000090a360000000 0x000000fc00000000 0x00000003f0000000

def z652 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x0c91fffc00000000 0xc43247fff0000000

def z653 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000000c025 0xc500000000000300

def z654 : W := mkw 0x0002000041080000 0x8000080001042000 0x230e0000e00c0008 0x288c380003803000

def z655 : W := mkw 0x0470208102c10221 0x0011c082040b0408 0xdc70608303f30337 0x5771c1820c0fcc0c

def z656 : W := mkw 0x0ef928c000000030 0x003be4a300000000 0xeffff8e000000000 0xffbfffe380000000

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0018030000f004 0x847000600c0003c0

def z658 : W := mkw 0x0002000041080000 0x8000080001042000 0x00000000e38c001b 0x00000000038e3000

def z659 : W := mkw 0x0a80000290000002 0x002a00000a400000 0x9f000003e0000002 0x027c00000f800000

def z660 : W := mkw 0x845081250e74c541 0x0a1142049439d315 0xdcf187ff1ffccfff 0xff73c61ffc7ff33f

def z661 : W := mkw 0x0ffd7fdab402ac3e 0x303ff5ff6ad00ab0 0xeffffffcfc000c08 0xffbffffff3f00030

def z662 : W := mkw 0x000001200410c500 0x0800000480104314 0x409007e01c70cf3d 0xdd02401f8071c33c

def z663 : W := mkw 0x0a801302b402ac02 0x302a004c0ad00ab0 0x1c801b03fc03fc2f 0x8472006c0ff00ff0

def z664 : W := mkw 0x0fff7ed8618b0abc 0xa43ffdfb61862c2a 0xaf6e7800e3830002 0x02bdb9e0038e0c00

def z665 : W := mkw 0x0000000020830a80 0x2400000000820c2a 0x0000000000030fe0 0x0000000000000c3f

def z666 : W := mkw 0x0b805723b6d3ff03 0x382e015c8edb4ffc 0xdf807f03fff3ff3f 0xcf7e01fc0fffcffc

def z667 : W := mkw 0x047029e106d1d731 0x0811c0a7841b475c 0xdcf07fe31ff3ff3f 0xdf73c1ff8c7fcffc

def z668 : W := mkw 0x00262090418902a8 0x840098824106240a 0xe06e6090038f03f3 0x7381b982400e3c0f

def z669 : W := mkw 0x0000000102400001 0x0000000004090000 0x1000000303f00017 0x004000000c0fc000

def z670 : W := mkw 0x1a89800298240002 0x406a26000a609000 0x008180001c000000 0x0002060000700000

def z671 : W := mkw 0x0100440020020800 0x2004011000800820 0x83006000e0030002 0x020c018003800c00

def z672 : W := mkw 0x047028c000810230 0x0011c0a300020408 0xcc7078e003830333 0xd731c1e3800e0c0c

def z673 : W := mkw 0x0b825702f58bae82 0xb42e095c0bd62eba 0xdf807f03ff8fffff 0xcf7e01fc0ffe3fff

def z674 : W := mkw 0x0ffd7fda9400a43e 0x103ff5ff6a500290 0xffffffff1c00f004 0xfffffffffc7003c0

def z675 : W := mkw 0x1a8b0002d1080002 0xc06a2c000b442000 0x230e0000e0000000 0x008c380003800000

def z676 : W := mkw 0x0ff07ee102d15331 0x083fc1fb840b454c 0xdff07fe303f3f337 0xdf7fc1ff8c0fcfcc

def z677 : W := mkw 0x0ba66492f18b0aaa 0xa42e99924bc62c2a 0xffee6493ff8f0fff 0x7fffb9924ffe3c3f

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000600000030023 0x4300018000000c00

def z679 : W := mkw 0x1ffffedbfbef0abf 0xe47ffffb6fefbc2a 0xffffffffffff0fff 0xfffffffffffffc3f

def z680 : W := mkw 0x047228e143d95331 0x8811c8a3850f654c 0xff7e78e3e3fff33f 0xfffdf9e38f8fffcc

def z681 : W := mkw 0x1fff6493f3cb0aab 0xe47ffd924fcf2c2a 0xff6e6493e38f0ffb 0x7bfdb9924f8e3c3f

def z682 : W := mkw 0x10028003fbef0a83 0xe4400a000fefbc2a 0x10000003ffff0fff 0x004000000ffffc3f

def z683 : W := mkw 0x010057002402ac00 0x3004015c00900ab0 0xc3007f00e003fc2b 0xcb0c01fc03800ff0

def z684 : W := mkw 0x1edb9303df6ca403 0xd07b6e4c0f7db290 0xffff9b03fffcf01f 0xbffffe6c0ffff3c0

def z685 : W := mkw 0x0ba07fe2b493ff32 0x382e81ff8ad24ffc 0xdf807fe3fc03ff2f 0xcf7e01ff8ff00ffc

def z686 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x001180fc1c7ccffd 0x30004603f071f33f

def z687 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x007078e003f3f330 0xd001c1e3800fcfcc

def z688 : W := mkw 0x010057002402ac00 0x3004015c00900ab0 0xdc007f030003fc27 0xc77001fc0c000ff0

def z689 : W := mkw 0x01005702b402ac02 0x3004015c0ad00ab0 0x10007f03fc03fc2f 0xc04001fc0ff00ff0

def z690 : W := mkw 0x1a8b8002d92c0002 0xc06a2e000b64b000 0xe3ef8000ff8c001b 0x3b8fbe0003fe3000

def z691 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xc07060e003f30333 0x5301c183800fcc0c

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c00780300033002 0x027001e00c000cc0

def z693 : W := mkw 0x0a80000000000000 0x002a000000000000 0xcf80000000000000 0x0f3e000000000000

def z694 : W := mkw 0x8020a1a40cb5c760 0x0a0082869032d71d 0xc0f1e7fc1fffcfff 0xff03c79ff07fff3f

def z695 : W := mkw 0x8b80d706bc26ac42 0x322e035c1af09ab1 0x0381871cfc0c0cc8 0x280e061c73f03033

def z696 : W := mkw 0x1fffe493db6c002b 0xc07fff924f6db000 0xffffe493fffc001f 0x7fffff924ffff000

def z697 : W := mkw 0x05747ed80000003c 0x0015d1fb60000000 0xcc707ffc00000000 0xd731c1fff0000000

def z698 : W := mkw 0x047028c000000030 0x0011c0a300000000 0xccf1fffc00000000 0xff33c7fff0000000

def z699 : W := mkw 0x0000800008240000 0x0000020000209000 0x00118000007c0010 0x300046000001f000

def z700 : W := mkw 0x8100c5242c36cd40 0x2a04031490b0db35 0xc391e7fcfc7fcfff 0xff0e479ff3f1ff3f

def z701 : W := mkw 0x0b80560290000002 0x002e01580a400000 0xdf807f03fc00000f 0xcf7e01fc0ff00000

def z702 : W := mkw 0x0b80d702bc26ac02 0x302e035c0af09ab0 0xdf91ff03fc7ffc3f 0xff7e47fc0ff1fff0

def z703 : W := mkw 0x0020208000810220 0x0000808200020408 0x0060008003800310 0x10018002000e000c

def z704 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009183fc1c7cc3d4 0xb402460ff071f30f

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000049000000fe0 0x400000124000003f

def z706 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6410e38f0cca 0x2a8db990438e3c33

def z707 : W := mkw 0x0b80560290000002 0x002e01580a400000 0xdf807f03fc03f02f 0xcf7e01fc0ff00fc0

def z708 : W := mkw 0x0a80010294008402 0x002a00040a500210 0xdf807f03fc03fc2f 0xcf7e01fc0ff00ff0

def z709 : W := mkw 0x0aa63392d589a6aa 0x942a98ce4b56269a 0x3cee1b931f8cf3d4 0xb4f3b86e4c7e33cf

def z710 : W := mkw 0x145b80014b6c0001 0xc0516e00052db000 0xe3ff8000fffc001f 0x3f8ffe0003fff000

def z711 : W := mkw 0x1ffde493bae70aab 0x647ff7924eeb9c2a 0x1c91e4931c730fe4 0x447247924c71cc3f

def z712 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xffffffff00033002 0xfffffffffc000cc0

def z713 : W := mkw 0x0b8d563902d1530d 0x082e3558e40b454c 0x338f871f03f3f337 0x28ce3e1c7c0fcfcc

def z714 : W := mkw 0x00000102b402ac02 0x300000040ad00ab0 0x9c007803fc03fc2f 0x027001e00ff00ff0

def z715 : W := mkw 0x0ffd7edab002283e 0x303ff5fb6ac008a0 0xffffffffe0033c2b 0xffffffffff800cf0

def z716 : W := mkw 0x0ef928c000000030 0x003be4a300000000 0xeffffffc00000000 0xffbffffff0000000

def z717 : W := mkw 0x8126e5b46dbfcfe8 0xae049b96d1b6ff3f 0xa3ffe36cfff3c006 0x868fff8db3ffcf00

def z718 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409187fc1c7c0fdd 0x3d02461ff071f03f

def z719 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe3efe79ce38f0ffb 0x7b8fbf9e738e3c3f

def z720 : W := mkw 0x0450086102d15311 0x08114021840b454c 0xdc10786303f3f337 0xc77041e18c0fcfcc

def z721 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc0000c025 0xffbffffff0000300

def z722 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x1c1078e303f3f337 0xc47041e38c0fcfcc

def z723 : W := mkw 0x0ffd7ed90240003d 0x003ff5fb64090000 0xffffffff03800002 0xfffffffffc0e0000

def z724 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0x20ff87fc00000000 0x3883fe1ff0000000

def z725 : W := mkw 0x0efd28d80000003c 0x003bf4a360000000 0xefff87fc00000000 0xffbffe1ff0000000

def z726 : W := mkw 0x0efd3ad80000003c 0x003bf4eb60000000 0x20ff83fc00000000 0x3083fe0ff0000000

def z727 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaffffbfc00000000 0xb6bfffeff0000000

def z728 : W := mkw 0x147fa8f94bfd533d 0xc851fea3e52ff54c 0x207f80fc03fc0310 0x3081fe03f00ff00c

def z729 : W := mkw 0x0fdd5e580000001c 0x003f757960000000 0x2f9f9b6c00000000 0x84be7e6db0000000

def z730 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdcf07fe303f3f337 0xdf73c1ff8c0fcfcc

def z731 : W := mkw 0x0edb1a48618b0a94 0xa43b6c6921862c2a 0x0c919b6ce38f0ffb 0x8432466db38e3c3f

def z732 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xf36e6493e38fffff 0x7bcdb9924f8e3fff

def z733 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xff7e0003fffc001f 0x17fdf8000ffff000

def z734 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc707cf303f3f337 0xff71c1f3cc0fcfcc

def z735 : W := mkw 0x90028127df7cc543 0xca400a049f7df315 0x10000003fffcc01f 0x004000000ffff300

def z736 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807ffffc03fc2f 0xcf7e01fffff00ff0

def z737 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc7078f303fff3f7 0xf771c1e3cc0fffcf

def z738 : W := mkw 0x1edb9a4bdb6c0017 0xc07b6e692f6db000 0xffff9ffffffc001f 0xfffffe7ffffff000

def z739 : W := mkw 0x01267ed8618b0abc 0xa40499fb61862c2a 0xe36e7c90e38f0ffb 0x7b8db9f2438e3c3f

def z740 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fffff03f 0x3ffffe000fffffc0

def z741 : W := mkw 0x0ffd7ed82002083c 0x203ff5fb60800820 0xffffffffe003fc2f 0xffffffffff800ff0

def z742 : W := mkw 0x0ffd7ed82002083c 0x203ff5fb60800820 0xeffffffc00030c20 0xffbffffff0000c30

def z743 : W := mkw 0x1ffd7edb9240003f 0x407ff5fb6e490000 0xffffffff00000000 0xfffffffffc000000

def z744 : W := mkw 0x01267698618b0aac 0xa40499da61862c2a 0xe36e679ce38f0ffb 0x7b8db99e738e3c3f

def z745 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0x207f87fc00000000 0xf081fe1ff0000000

def z746 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc707ce303f3ff3f 0xdf71c1f38c0fcffc

def z747 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffbec00000000 0xd7bfffefb0000000

def z748 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc7078e303ffffff 0xd771c1e38c0fffff

def z749 : W := mkw 0x0ffd7ed902c1023d 0x003ff5fb640b0408 0xffffffff03f30337 0xfffffffffc0fcc0c

def z750 : W := mkw 0x0ffd7edab002283e 0x303ff5fb6ac008a0 0xeffffffce0000000 0xffbffffff3800000

def z751 : W := mkw 0x057d7ed80000003c 0x0015f5fb60000000 0x207f87fc00000000 0x3081fe1ff0000000

def z752 : W := mkw 0x00262090618b0aa8 0xa400988241862c2a 0xe36e0090e38f0ffb 0x3b8db802438e3c3f

def z753 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6400e38f0ffb 0x4b8db990038e3c3f

def z754 : W := mkw 0x0ffd7ed82002083c 0x203ff5fb60800820 0xeffffffce00f0ffb 0xffbffffff3803c3f

def z755 : W := mkw 0x1edb8843db6c0013 0xc07b6e210f6db000 0xffff9863fffc001f 0xbffffe618ffff000

def z756 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807f03fc03fc0e 0x8e7e01fc0ff00ff0

def z757 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xfffff803fffc001f 0xffffffe00ffff000

def z758 : W := mkw 0x0000002102d15301 0x08000000840b454c 0xdc1078e303f3f337 0xd77041e38c0fcfcc

def z759 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0xafff9b6c00000000 0x86bffe6db0000000

def z760 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xff6e0003fffc001f 0x3bfdb8000ffff000

def z761 : W := mkw 0x0ffd7eda9000003e 0x003ff5fb6a400000 0xffffffffe0000002 0xffffffffff800000

def z762 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fff00017 0x17fffe000fffc000

def z763 : W := mkw 0x0000002102d15301 0x08000000840b454c 0x9c00780303f3f337 0x027001e00c0fcfcc

def z764 : W := mkw 0x1472a8e14bfd5331 0xc851caa3852ff54c 0x007000e003fc0310 0x1001c003800ff00c

def z765 : W := mkw 0x8470a9c50ee59671 0x0211c2a7143b9659 0x9ce1ff1f1f8f3cca 0x2a7387fc7c7e3cf3

def z766 : W := mkw 0x047d29dab402ac3e 0x3011f4a76ad00ab0 0x307f80fffc03fc2f 0x30c1fe03fff00ff0

def z767 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f13fc0ffcef 0xef7e01fc4ff03ff3

def z768 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc00000c29 0xffbffffff0000030

def z769 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7ccff8 0xf802461ff071f33f

def z770 : W := mkw 0x0ffd649000000028 0x003ff59240000000 0xefffe7fc00000000 0xffbfff9ff0000000

def z771 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0x238f87fc00000000 0xe88e3e1ff0000000

def z772 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x63ff8000fffc001d 0x3d8ffe0003fff000

def z773 : W := mkw 0x0450002102d15301 0x08114000840b454c 0xdc70780303f3f337 0xd771c1e00c0fcfcc

def z774 : W := mkw 0x8ffdfffc0c34c57c 0x0a3ff7fff030d315 0xaf6e78001c7ccffd 0x02bdb9e00071f33f

def z775 : W := mkw 0x1b8fd712fd2eac8a 0xf46e3f5c4bf4bab2 0x238f8710fc0c0cc8 0x288e3e1c43f03033

def z776 : W := mkw 0x155bd7016f6eac01 0xf0556f5c05bdbab0 0x207fff0003fffc30 0xf081fffc000ffff0

def z777 : W := mkw 0x05746cd000000038 0x0015d1b340000000 0xeffffffc00000000 0xffbffffff0000000

def z778 : W := mkw 0x0ffd7ed8008102bc 0x043ff5fb6002040a 0xeffffffc000003c0 0xffbffffff000000f

def z779 : W := mkw 0x8b805706b402ac42 0x322e015c1ad00ab1 0xdf807f1ffc03fcef 0xcf7e01fc7ff00ff3

def z780 : W := mkw 0x0ba4769000000028 0x002e91da40000000 0xeffffffc00000000 0xffbffffff0000000

def z781 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f93fc03ffef 0xcf7e01fe4ff00fff

def z782 : W := mkw 0x9edb8007db6c0043 0xc27b6e001f6db001 0xffff801ffffc00df 0x3ffffe007ffff003

def z783 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffee0003fffc001f 0x0fffb8000ffff000

def z784 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf91ff03fc03fc2f 0xff7e47fc0ff00ff0

def z785 : W := mkw 0x0ffd7ed90240003d 0x003ff5fb64090000 0xeffffffc03f00010 0xffbffffff00fc000

def z786 : W := mkw 0x0efd3ad80000003c 0x003bf4eb60000000 0x2cff9b6c00000000 0x84b3fe6db0000000

def z787 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe3ffe490e38f0ffb 0x7f8fff92438e3c3f

def z788 : W := mkw 0x047d28f902d1533d 0x0811f4a3e40b454c 0xfcffffff03f3f337 0xfff3fffffc0fcfcc

def z789 : W := mkw 0x8124e5b40c34c568 0x0a049396d030d315 0xe36e64901c7ccffd 0x7b8db9924071f33f

def z790 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc7078e303fff33f 0xff71c1e38c0fffcc

def z791 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x4091fffc1c7ffffd 0xfd0247fff071ffff

def z792 : W := mkw 0x0ffd7ed90240003d 0x003ff5fb64090000 0xffffffff03f3f037 0xfffffffffc0fcfc0

def z793 : W := mkw 0x147fa8f14bfd53b9 0xcc51fea3c52ff54e 0x207f80f003fc03d0 0x3081fe03c00ff00f

def z794 : W := mkw 0x01064410618b0a88 0xa404191041862c2a 0xe36e0410e38f0ffb 0x3b8db810438e3c3f

def z795 : W := mkw 0x0002000041080000 0x8000080001042000 0xe36e0000e38c0ffb 0x3b8db800038e303f

def z796 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xafeffffc00000000 0xeabfbffff0000000

def z797 : W := mkw 0x0022208041890220 0x8000888201062408 0xe36e6490e38f0ffb 0x7b8db992438e3c3f

def z798 : W := mkw 0x0fdd5e580000001c 0x003f757960000000 0x6f9f9ffc00000000 0xfdbe7e7ff0000000

def z799 : W := mkw 0x1126fedbdb6c003f 0xc0449bfb6f6db000 0x10007ffffffc001f 0xc04001fffffff000

def z800 : W := mkw 0x0000800008240000 0x0000020000209000 0x409187fc1c7c0ffd 0xfd02461ff071f03f

def z801 : W := mkw 0x0ffd7eda9000203e 0x103ff5fb6a400080 0xffffffff00003000 0xfffffffffc0000c0

def z802 : W := mkw 0x90028127ff7eed43 0xfa400a049ffdfbb5 0x10000003ffffffff 0x004000000fffffff

def z803 : W := mkw 0x01266cd0618b0ab8 0xa40499b341862c2a 0xe36e7cf0e38f0ffb 0xfb8db9f3c38e3c3f

def z804 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff80fffffc001f 0x3ffffe03fffff000

def z805 : W := mkw 0x047d28f902d1533d 0x0811f4a3e40b454c 0xfc7e78e303f3f337 0xd7f1f9e38c0fcfcc

def z806 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f03fc0fffff 0xcf7e01fc0ff03fff

def z807 : W := mkw 0x0ffd7ed902c1123d 0x003ff5fb640b0448 0xffffffff03833333 0xfffffffffc0e0ccc

def z808 : W := mkw 0x0fdd5e580000001c 0x003f757960000000 0xef9fff7c00000000 0xefbe7ffdf0000000

def z809 : W := mkw 0x0ffd7eda9000003e 0x003ff5fb6a400000 0xfffffffffc03f02f 0xfffffffffff00fc0

def z810 : W := mkw 0x01064410610a0888 0xa404191041842822 0xe36e0490e38c0ffb 0x7b8db812438e303f

def z811 : W := mkw 0x9edb0127d758c543 0xca7b6c049f5d6315 0xbf6e07ffe380cfe2 0xc2fdb81fff8e033f

def z812 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0xa36e0000e38f0ffb 0x028db800038e3c3f

def z813 : W := mkw 0x05564c71635a5999 0xac155931c58d6966 0x3f1e1c73e07cfccc 0xacfc7871cf81f3f3

def z814 : W := mkw 0x057d6cd80000003c 0x0015f5b360000000 0xe3ffe7fc00000000 0xff8fff9ff0000000

def z815 : W := mkw 0x0459000000000000 0x0011640000000000 0x60ff87fc00000000 0xfd83fe1ff0000000

def z816 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7ccfdc 0xbc02461ff071f33f

def z817 : W := mkw 0x0ffd7ed82002083c 0x203ff5fb60800820 0xeffffffce0000c08 0xffbffffff3800030

def z818 : W := mkw 0x000d00180000000c 0x0000340060000000 0x609f87fc00000000 0xfd827e1ff0000000

def z819 : W := mkw 0x057d7ed80000003c 0x0015f5fb60000000 0x60fffffc00000000 0xfd83fffff0000000

def z820 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7ccffd 0x3802461ff071f33f

def z821 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xc0f187fc1ffccfff 0xff03c61ff07ff33f

def z822 : W := mkw 0x0ffd7ed8200208bc 0x243ff5fb60800822 0xeffffffc00000cc0 0xffbffffff0000033

def z823 : W := mkw 0x1edb9203db6c2003 0xd07b6e480f6db080 0xffff9803fffc301f 0x3ffffe600ffff0c0

def z824 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc70780303f3f337 0x1771c1e00c0fcfcc

def z825 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8493fffc001f 0x7ffffe124ffff000

def z826 : W := mkw 0x0b8d571ab402ac0e 0x302e355c6ad00ab0 0xff8e7f03fc03fc2f 0xcffe39fc0ff00ff0

def z827 : W := mkw 0x0fdd5e580000001c 0x003f757960000000 0xefff9f7c00000000 0xbfbffe7df0000000

def z828 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xffffffff0000f004 0xfffffffffc0003c0

def z829 : W := mkw 0x1edb9203db6c0003 0xc07b6e480f6db000 0xffff9b03fffc001f 0xbffffe6c0ffff000

def z830 : W := mkw 0x0b8d571ab402ac0e 0x302e355c6ad00ab0 0xff9ffffffc03fc2f 0xfffe7ffffff00ff0

def z831 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdcf1f8e303f3f337 0xff73c7e38c0fcfcc

def z832 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x5c919fff1c7cfffd 0xfd72467ffc71f3ff

def z833 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf907f03fc73fc3f 0xdf7e41fc0ff1cff0

def z834 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffffe003ffff003f 0x7fffff800ffffc00

def z835 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x636e0490e38c0ff9 0x798db812438e303f

def z836 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc000c03d0 0xffbffffff000300f

def z837 : W := mkw 0x0ff07fe3b6d3ff33 0x383fc1ff8edb4ffc 0x03f007e0fff00f18 0x180fc01f83ffc03c

def z838 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc00700015 0xffbffffff001c000

def z839 : W := mkw 0x8b80d626b8366942 0x3a2e03589ae0d9a5 0x9f11f8ffe07f33d2 0x327c47e3ff81fccf

def z840 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807b03fc03fc2f 0x867e01ec0ff00ff0

def z841 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc707fff03f3f337 0xd771c1fffc0fcfcc

def z842 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff836ffffc001f 0xbffffe0dbffff000

def z843 : W := mkw 0x0ed9000000000000 0x003b640000000000 0xefff836c00000000 0xbfbffe0db0000000

def z844 : W := mkw 0x01266cd0618b1ab8 0xa40499b341862c6a 0xe36e7c90e38f3ffb 0x7b8db9f2438e3cff

def z845 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xefff87fc00000000 0x3fbffe1ff0000000

def z846 : W := mkw 0x10028003db6c0003 0xc0400a000f6db000 0xb36e0003fffc001f 0x02cdb8000ffff000

def z847 : W := mkw 0x0fdd5e580000001c 0x003f757960000000 0x239f877c00000000 0x288e7e1df0000000

def z848 : W := mkw 0x90028127dffdd743 0xca400a049f7ff75d 0x10000003ffffffff 0x004000000fffffff

def z849 : W := mkw 0x047428f102d15339 0x0811d0a3c40b454c 0xfc7e78f303f3f337 0xf7f1f9e3cc0fcfcc

def z850 : W := mkw 0x0b84571ab402ac0e 0x302e115c6ad00ab0 0xdf807f1ffc03fc2f 0xcf7e01fc7ff00ff0

def z851 : W := mkw 0x0a89000000000000 0x002a240000000000 0x639f87fc00000000 0xfd8e7e1ff0000000

def z852 : W := mkw 0x0000000290000002 0x000000000a400000 0xdc007803fc03f02f 0xc77001e00ff00fc0

def z853 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x3fff8003fffc001c 0x3cfffe000ffff000

def z854 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6490e38f0fea 0x6a8db992438e3c3f

def z855 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6090e38f0ffb 0x328db982438e3c3f

def z856 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfff8003fffc000e 0x2efffe000ffff000

def z857 : W := mkw 0x0470208102c10221 0x0011c082040b0408 0xdc70788303f3f337 0xd771c1e20c0fcfcc

def z858 : W := mkw 0x1aaba8e2d9bd5332 0xc86aaea38b66f54c 0x238ff8e0fc0ff328 0xe88e3fe383f03fcc

def z859 : W := mkw 0x0104441000000008 0x0004111040000000 0x639f87fc00000000 0xfd8e7e1ff0000000

def z860 : W := mkw 0x800281244dbdc7c0 0x8e000a049136f71f 0x000000001ffccffd 0x00000000007ff33f

def z861 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8703fffc001f 0xfffffe1c0ffff000

def z862 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbf6e0003fff00006 0x02fdb8000fffc000

def z863 : W := mkw 0x81247ffc2493cffc 0x2e0491fff0924f3f 0x00007ffc0003cfe0 0xc00001fff0000f3f

def z864 : W := mkw 0x1edb0003d3480003 0xc07b6c000f4d2000 0xfffe0003fff0001f 0x1ffff8000fffc000

def z865 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c6078e303f3f337 0xc27181e38c0fcfcc

def z866 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807f03fc03fc2f 0x0a7e01fc0ff00ff0

def z867 : W := mkw 0x0fd9560000000000 0x003f655800000000 0xeffffffc00000000 0xffbffffff0000000

def z868 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0x2cff9b6c00000000 0xb4b3fe6db0000000

def z869 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdfe07f03ff83fc3f 0xdf7f81fc0ffe0ff0

def z870 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x1c7078e303f3f334 0xd471c1e38c0fcfcc

def z871 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x236e6490e38f0ff8 0x788db992438e3c3f

def z872 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7ccff4 0xf402461ff071f33f

def z873 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xff6e7c93e38f3ffb 0x7bfdb9f24f8e3cff

def z874 : W := mkw 0x9ed99b6f9e74c557 0x4a7b666dbe79d315 0x1c919b6f1c70c004 0x8472466dbc71c300

def z875 : W := mkw 0x800281256fffdfc1 0xae000a0495bfff7f 0x10000003ffffffff 0x004000000fffffff

def z876 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc70786303f3f027 0xc771c1e18c0fcfc0

def z877 : W := mkw 0x057d7ed80000003c 0x0015f5fb60000000 0xe37ffffc00000000 0xfb8dfffff0000000

def z878 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6490e38fcfff 0xff8db992438e3f3f

def z879 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdf7078e3e3f3f33f 0xdf7dc1e38f8fcfcc

def z880 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c60780303f3f006 0x027181e00c0fcfc0

def z881 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e0490e38c0fdb 0x3b8db812438e303f

def z882 : W := mkw 0x8b86d716fd2eacca 0xb62e1b5c5bf4bab3 0x238f871cfc0c0cc8 0x288e3e1c73f03033

def z883 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xffffffff00000007 0xfffffffffc000000

def z884 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6080e38f0ffb 0x538db982038e3c3f

def z885 : W := mkw 0x81246df42493dff8 0x2e0491b7d0924f7f 0x00007ffc0003ffe0 0xc00001fff0000fff

def z886 : W := mkw 0x047928e902d15335 0x0811e4a3a40b454c 0xdc71f8ef03f3f337 0xd771c7e3bc0fcfcc

def z887 : W := mkw 0x047028c102c11231 0x0011c0a3040b0448 0xdc70780303f3f037 0xd771c1e00c0fcfc0

def z888 : W := mkw 0x0000000102400001 0x0000000004090000 0xdc00780303f3f037 0xc77001e00c0fcfc0

def z889 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7ccffd 0xc402461ff071f33f

def z890 : W := mkw 0x045280014b6c0001 0x80114a00052db000 0xffff8003fffc001f 0x3ffffe000ffff000

def z891 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdcf1ffff03ffffff 0xff73c7fffc0fffff

def z892 : W := mkw 0x0ffd7ed820830abc 0x243ff5fb60820c2a 0xeffffffc00030000 0xffbffffff0000c00

def z893 : W := mkw 0x047428f902d1533d 0x0811d0a3e40b454c 0xdc7078ff03f3f337 0xd771c1e3fc0fcfcc

def z894 : W := mkw 0x002020a000914320 0x080080828002450c 0xdc7078e303f3f337 0xd771c1e38c0fcfcc

def z895 : W := mkw 0x0100450024028c00 0x2004011400900a30 0xdf807f03fc03fc2f 0xcf7e01fc0ff00ff0

def z896 : W := mkw 0x0ffd7eda9000003e 0x003ff5fb6a400000 0xeffffffcfc000008 0xffbffffff3f00000

def z897 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807b03fc03f00f 0x8f7e01ec0ff00fc0

def z898 : W := mkw 0x0bad7ed80000003c 0x002eb5fb60000000 0xef8ffffc00000000 0xefbe3ffff0000000

def z899 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0xef9ffffc00000000 0xffbe7ffff0000000

def z900 : W := mkw 0x9ed989679e74d553 0x4a7b66259e79d355 0x1c919b6f1c70f004 0x8472466dbc71c3c0

def z901 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807f03fc03fc26 0xc67e01fc0ff00ff0

def z902 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf907fe3fc03fc2f 0xdf7e41ff8ff00ff0

def z903 : W := mkw 0x0a801302b402ac02 0x302a004c0ad00ab0 0xdc807b03fc03fc2f 0xc77201ec0ff00ff0

def z904 : W := mkw 0x1a8b8002d92c0002 0xc06a2e000b64b000 0xe3ff8000fffc001f 0x3f8ffe0003fff000

def z905 : W := mkw 0x002020a102d15321 0x08008082840b454c 0xdc60788303f3f337 0xd77181e20c0fcfcc

def z906 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xe3ff8000fffc001b 0x3b8ffe0003fff000

def z907 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c7078e303f3f316 0x9671c1e38c0fcfcc

def z908 : W := mkw 0x1edb884bdb6c0017 0xc07b6e212f6db000 0xffff806ffffc001f 0x3ffffe01bffff000

def z909 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3ff87fc00000000 0xff8ffe1ff0000000

def z910 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x509187ff1c7fffff 0xfd42461ffc71ffff

def z911 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e67fce38f0ffb 0xfb8db99ff38e3c3f

def z912 : W := mkw 0x057d7ed80000003c 0x0015f5fb60000000 0xec7ffffc00000000 0xf7b1fffff0000000

def z913 : W := mkw 0x0ed20003d3480003 0x803b48000f4d2000 0xfffe0003fffc001f 0x3ffff8000ffff000

def z914 : W := mkw 0x01004502b402ac02 0x300401140ad00ab0 0xdf007c03fc03fc2f 0xcf7c01f00ff00ff0

def z915 : W := mkw 0x00028000492c0000 0x80000a000124b000 0xe36e0000fffc001f 0x3b8db80003fff000

def z916 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6490e38f0fda 0x3a8db992438e3c3f

def z917 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbf7f8003fffc001f 0x32fdfe000ffff000

def z918 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf91fffffc0fffff 0xff7e47fffff03fff

def z919 : W := mkw 0x01247ed80000003c 0x000491fb60000000 0xe3fffffc00000000 0xff8ffffff0000000

def z920 : W := mkw 0x0bad7ed80000003c 0x002eb5fb60000000 0x639ffffc00000000 0xfd8e7ffff0000000

def z921 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdcf078e31ff3f33f 0xdf73c1e38c7fcfcc

def z922 : W := mkw 0x01267ed8618b0abc 0xa40499fb61862c2a 0xe3fffffce38f0ffb 0xff8ffffff38e3c3f

def z923 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdcf1fbef03f3f337 0xd773c7efbc0fcfcc

def z924 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fffcc03f 0xfffffe000ffff300

def z925 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8413fffc0cdf 0x3ffffe104ffff033

def z926 : W := mkw 0x01267690618b0aa8 0xa40499da41862c2a 0xe36e7f90e38f0ffb 0xfb8db9fe438e3c3f

def z927 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x1c807f03fc03fc2f 0xc47201fc0ff00ff0

def z928 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0xefff9ffc00000000 0xffbffe7ff0000000

def z929 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc71f8ff03f3f337 0xf771c7e3fc0fcfcc

def z930 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xc39187fcfc7ccfff 0xff0e461ff3f1f33f

def z931 : W := mkw 0x0edb8000492c0000 0x803b6e000124b000 0xefff8000fffc001f 0x3fbffe0003fff000

def z932 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f93fc03fc2f 0xff7e01fe4ff00ff0

def z933 : W := mkw 0x8476a8f54bfd53f9 0x8e11daa3d52ff54f 0x207f80fc03fc03d0 0x3081fe03f00ff00f

def z934 : W := mkw 0x1edb8843db6c1013 0xc07b6e210f6db040 0xffff9803fffc301f 0x3ffffe600ffff0c0

def z935 : W := mkw 0x00262090418902a8 0x840098824106240a 0xe36e0490e38c0ffb 0x7b8db812438e303f

def z936 : W := mkw 0x00222080618b0aa0 0xa400888201862c2a 0xe36e6080e38f0ffb 0x7b8db982038e3c3f

def z937 : W := mkw 0x0ffd7ed80081123c 0x003ff5fb60020448 0xeffffffc00033000 0xffbffffff0000cc0

def z938 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8093fffc03df 0x3ffffe024ffff00f

def z939 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfff8003fffc001f 0x06fffe000ffff000

def z940 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc000c0cc8 0xffbffffff0003033

def z941 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fff0000f 0x0ffffe000fffc000

def z942 : W := mkw 0x047928e102d15331 0x0811e4a3840b454c 0xfc7ff8e303f3f337 0xf7f1ffe38c0fcfcc

def z943 : W := mkw 0x047d3ad80000003c 0x0011f4eb60000000 0x207f9bfc00000000 0xb081fe6ff0000000

def z944 : W := mkw 0x900281254f7cc541 0xca400a04953df315 0x000000001ffccffd 0x00000000007ff33f

def z945 : W := mkw 0x0efd3ad80000003c 0x003bf4eb60000000 0x6cff9ffc00000000 0xfdb3fe7ff0000000

def z946 : W := mkw 0x10028003db6c0003 0xc0400a000f6db000 0xf3ff8003fffc001f 0x3fcffe000ffff000

def z947 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaffffffc00000000 0x3abffffff0000000

def z948 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0xecfffffc00000000 0xffb3fffff0000000

def z949 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6490e38f0ff2 0x728db992438e3c3f

def z950 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff87fffffc0fff 0xfffffe1ffffff03f

def z951 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xcc91fffc1c7ccffd 0xff3247fff071f33f

def z952 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x009187fc1c7ccfec 0xec02461ff071f33f

def z953 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xe3ffe7fc00000000 0x7b8fff9ff0000000

def z954 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc0003f020 0xffbffffff0000fc0

def z955 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfef8003fffc001f 0x2affbe000ffff000

def z956 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f03fc03f006 0xcf7e01fc0ff00fc0

def z957 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff9803fffcf01f 0xbffffe600ffff3c0

def z958 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc000c0019 0xffbffffff0003000

def z959 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe37e64f0e38f0ffb 0xff8df993c38e3c3f

def z960 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x2f9ffffc00000000 0xecbe7ffff0000000

def z961 : W := mkw 0x0ffd7edab002283e 0x303ff5fb6ac008a0 0xfffffffffc03300f 0xfffffffffff00cc0

def z962 : W := mkw 0x01247ff02493ffb8 0x3c0491ffc0924ffe 0x00007ff00003ffe0 0xc00001ffc0000fff

def z963 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff871ffffc001f 0x3ffffe1c7ffff000

def z964 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xdc9187ff1c7ccfff 0xff72461ffc71f33f

def z965 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0x239f877c00000000 0xac8e7e1df0000000

def z966 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfff8003fffc001a 0x3afffe000ffff000

def z967 : W := mkw 0x0fdd56180000000c 0x003f755860000000 0xefff87fc00000000 0xffbffe1ff0000000

def z968 : W := mkw 0x0ffd7ed820830abc 0x243ff5fb60820c2a 0xeffffffc000f0ff9 0xffbffffff0003c3f

def z969 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xfffff803ffff301f 0x3fffffe00ffffcc0

def z970 : W := mkw 0x0ffd7ed820830a3c 0x203ff5fb60820c28 0xeffffffce3830f3b 0xffbffffff38e0c3c

def z971 : W := mkw 0x0edd1a580000001c 0x003b746960000000 0x2c9f9b7c00000000 0xa4b27e6df0000000

def z972 : W := mkw 0x01024400618b0a80 0xa404091001862c2a 0xe36e6400e38f0ffb 0x7b8db990038e3c3f

def z973 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xff7e78e303f3f337 0xfffdf9e38c0fcfcc

def z974 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaf7ffffc00000000 0xf2bdfffff0000000

def z975 : W := mkw 0x0ffd7ed902c1123d 0x003ff5fb640b0448 0xffffffff0383f027 0xfffffffffc0e0fc0

def z976 : W := mkw 0x0126649041080028 0x8004999241042000 0xe36e6490e38c0ffb 0x7b8db992438e303f

def z977 : W := mkw 0x812477b42493efe8 0x3e0491ded0924fbf 0x00007ffc0003ffe0 0xc00001fff0000fff

def z978 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc60780303f3f337 0xc77181e00c0fcfcc

def z979 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f007f03fc03fc2f 0xc27c01fc0ff00ff0

def z980 : W := mkw 0x0ffd7ed80081023c 0x003ff5fb60020408 0xffffffff0383f337 0xfffffffffc0e0fcc

def z981 : W := mkw 0x0ffd7ed90240003d 0x003ff5fb64090000 0xffffffff00700004 0xfffffffffc01c000

def z982 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffce000000b 0xffbffffff3800000

def z983 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf91ff6ffc03fc2f 0xcf7e47fdbff00ff0

def z984 : W := mkw 0x0ed9000392400003 0x003b64000e490000 0xffff8003fff0001f 0x3ffffe000fffc000

def z985 : W := mkw 0x0efd3ad80000003c 0x003bf4eb60000000 0xefff9bfc00000000 0xbfbffe6ff0000000

def z986 : W := mkw 0x0fd95e4800000014 0x003f657920000000 0xefffff6c00000000 0xffbffffdb0000000

def z987 : W := mkw 0x00000102b402ac02 0x300000040ad00ab0 0xdc807f03fc03fc2f 0xcf7201fc0ff00ff0

def z988 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe3ee6790e38f0ffb 0xff8fb99e438e3c3f

def z989 : W := mkw 0x9ed993279e74e543 0x5a7b664c9e79d395 0x1c919b6f1c70f004 0x8472466dbc71c3c0

def z990 : W := mkw 0x0bad76980000002c 0x002eb5da60000000 0xe3ffe7fc00000000 0xff8fff9ff0000000

def z991 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8403fffc0c3f 0x7ffffe100ffff030

def z992 : W := mkw 0x0efd3ad80000003c 0x003bf4eb60000000 0xecfffbfc00000000 0xf7b3ffeff0000000

def z993 : W := mkw 0x047d28d80000003c 0x0011f4a360000000 0x20ff83fc00000000 0xb483fe0ff0000000

def z994 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x63ff87fc00000000 0xfd8ffe1ff0000000

def z995 : W := mkw 0x0450002102504101 0x0811400084094104 0xdc7078e303f3f337 0xd771c1e38c0fcfcc

def z996 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xafffff7c00000000 0xaebffffdf0000000

def z997 : W := mkw 0x0a828002d92c0002 0x802a0a000b64b000 0xffff8003fffc001f 0x3ffffe000ffff000

def z998 : W := mkw 0x0b895702b402ac02 0x302e255c0ad00ab0 0xff8fff03fc03fc2f 0xeffe3ffc0ff00ff0

def z999 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe37fe4fce38f0ffb 0x7b8dff93f38e3c3f

def z1000 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6000e38f0ffb 0x3b8db980038e3c3f

def z1001 : W := mkw 0x0ffd7ed80081023c 0x003ff5fb60020408 0xeffffffc00030320 0xffbffffff0000c0c

def z1002 : W := mkw 0x1edb9a4bdb6c0017 0xc07b6e692f6db000 0xffff9803fffc001f 0x3ffffe600ffff000

def z1003 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6490e38f0ffb 0x428db992438e3c3f

def z1004 : W := mkw 0x0ffd7edbb2c33a3f 0x303ff5fb6ecb0ce8 0xffffffffe3833002 0xffffffffff8e0cc0

def z1005 : W := mkw 0x0ffd7ed82002283c 0x303ff5fb608008a0 0xeffffffc00033000 0xffbffffff0000cc0

def z1006 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8083fffc033f 0x7ffffe020ffff00c

def z1007 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x1f807f03fc03fc2c 0xcc7e01fc0ff00ff0

def z1008 : W := mkw 0x0ffd7edab002083e 0x203ff5fb6ac00820 0xfffffffffc030c2f 0xfffffffffff00c30

def z1009 : W := mkw 0x1b8fd71afd2eac0e 0xf06e3f5c6bf4bab0 0x238f871cfc0c0c08 0x288e3e1c73f03030

def z1010 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc7078e303f3f006 0xd771c1e38c0fcfc0

def z1011 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xefffff6c00000000 0xcfbffffdb0000000

def z1012 : W := mkw 0x90028127ffffcfc3 0xee400a049fffff3f 0x10000003ffffcfff 0x004000000fffff3f

def z1013 : W := mkw 0x0ffd7ed80081023c 0x003ff5fb60020408 0xeffffffc03830002 0xffbffffff00e0c00

def z1014 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc60788303f3f337 0x537181e20c0fcfcc

def z1015 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc1c00000d 0xffbffffff0700000

def z1016 : W := mkw 0x0b8d5e580000001c 0x002e357960000000 0x238f9f7c00000000 0xa88e3e7df0000000

def z1017 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf81ff1ffc03fc2f 0xef7e07fc7ff00ff0

def z1018 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807803fc03fc2f 0x0f7e01e00ff00ff0

def z1019 : W := mkw 0x01266cd8618b0abc 0xa40499b361862c2a 0xe36e64fce38f0ffb 0x7b8db993f38e3c3f

def z1020 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc00030023 0xffbffffff0000c00

def z1021 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0xe36e0490e38f0ffb 0x7b8db812438e3c3f

def z1022 : W := mkw 0x145b8003db6c0003 0xc0516e000f6db000 0xf37f8003fffc001f 0x3bcdfe000ffff000

def z1023 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c7078e303f3f326 0xc671c1e38c0fcfcc

def z1024 : W := mkw 0x812465b42493cfe8 0x2e049196d0924f3f 0x000064900003cfe0 0x4000019240000f3f

def z1025 : W := mkw 0x01247ff82493ff3c 0x380491ffe0924ffc 0x00007ffc0003ff20 0xc00001fff0000ffc

def z1026 : W := mkw 0x9b8bd706fd2eac42 0xf26e2f5c1bf4bab1 0x238f871cfc0c0cc8 0x288e3e1c73f03033

def z1027 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc00000fe0 0xffbffffff000003f

def z1028 : W := mkw 0x14528003db6c0003 0xc0514a000f6db000 0xff7e0003fffc001f 0x3ffdf8000ffff000

def z1029 : W := mkw 0x800281244d3cc540 0x8a000a049134f315 0x00000000fffccfff 0x0000000003fff33f

def z1030 : W := mkw 0x847028e502d15371 0x0a11c0a3940b454d 0xdc7078ff03f3f3f7 0xd771c1e3fc0fcfcf

def z1031 : W := mkw 0x0b845712b402ac8a 0x342e115c4ad00ab2 0xdf807f13fc03fcef 0xcf7e01fc4ff00ff3

def z1032 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf007803fc03fc2f 0xc77c01e00ff00ff0

def z1033 : W := mkw 0x0bad7ed80000003c 0x002eb5fb60000000 0x238f87fc00000000 0x288e3e1ff0000000

def z1034 : W := mkw 0x0b8d56180000000c 0x002e355860000000 0x239f87fc00000000 0x388e7e1ff0000000

def z1035 : W := mkw 0x9ed981279e74c543 0x4a7b66049e79d315 0x1c9180031c70c004 0x047246000c71c300

def z1036 : W := mkw 0x0bad7ed80000003c 0x002eb5fb60000000 0xe3effffc00000000 0xfb8fbffff0000000

def z1037 : W := mkw 0x0450086102505111 0x0811402184094144 0xdc70786303f3f037 0xd771c1e18c0fcfc0

def z1038 : W := mkw 0x800201244518c540 0x8a00080491146315 0xe36e07fce38ccffb 0xfb8db81ff38e333f

def z1039 : W := mkw 0x0124e49028a70aa8 0x2404939240a29c2a 0x4091e4901c7f0ffd 0x7d0247924071fc3f

def z1040 : W := mkw 0x0ed91a4800000014 0x003b646920000000 0x2f9f9b6c00000000 0xacbe7e6db0000000

def z1041 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xc091e7fc1c7fcfff 0xff02479ff071ff3f

def z1042 : W := mkw 0x002028e102d15331 0x080080a3840b454c 0xdc0078e303f3f337 0xc77001e38c0fcfcc

def z1043 : W := mkw 0x0b845712b402ac0a 0x302e115c4ad00ab0 0xff8e7f13fc03fc2f 0xeffe39fc4ff00ff0

def z1044 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807b03fc03f027 0xc77e01ec0ff00fc0

def z1045 : W := mkw 0x1fff7edbf3cb0abf 0xe47ffdfb6fcf2c2a 0xbf6e7803e3830002 0x02fdb9e00f8e0c00

def z1046 : W := mkw 0x0ffd7ed90240103d 0x003ff5fb64090040 0xffffffff00003000 0xfffffffffc0000c0

def z1047 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc70786303f3f017 0x9771c1e18c0fcfc0

def z1048 : W := mkw 0x90028126dd3cc542 0xca400a049b74f315 0x00000000fc7ccffd 0x0000000003f1f33f

def z1049 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe3ee6490ff8f0fff 0x7f8fb99243fe3c3f

def z1050 : W := mkw 0x1b82d702fd2eac02 0xf06e0b5c0bf4bab0 0x03800700fc0c0c08 0x080e001c03f03030

def z1051 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e7c90e38ffffb 0xfb8db9f2438e3fff

def z1052 : W := mkw 0x0ffd7edb9240003f 0x003ff5fb6e490000 0xfffffffffff0001f 0xffffffffffffc000

def z1053 : W := mkw 0x01005702b402ac02 0x3004015c0ad00ab0 0xdc007f03fc03fc2f 0xc77001fc0ff00ff0

def z1054 : W := mkw 0x00020000618b0a80 0xa400080001862c2a 0x409187fce38f0ffb 0xfd02461ff38e3c3f

def z1055 : W := mkw 0x0ffd7ed902c1123d 0x003ff5fb640b0448 0xeffffffc03800000 0xffbffffff00e0000

def z1056 : W := mkw 0x0024209000000028 0x0000908240000000 0x60ff87fc00000000 0xfd83fe1ff0000000

def z1057 : W := mkw 0x0ef93ac800000034 0x003be4eb20000000 0xeffffbec00000000 0xffbfffefb0000000

def z1058 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0xe3ff87fc1c7ccffd 0xff8ffe1ff071f33f

def z1059 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f007803fc03f006 0x027c01e00ff00fc0

def z1060 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffb6c00000000 0xbfbfffedb0000000

def z1061 : W := mkw 0x0ffd7ed80081023c 0x003ff5fb60020408 0xeffffffc03800310 0xffbffffff00e000c

def z1062 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c70786303f3f337 0x8671c1e18c0fcfcc

def z1063 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe37e6490e3ff0fff 0x7f8df992438ffc3f

def z1064 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc00000331 0xffbffffff000000c

def z1065 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0x236e0490e38f0ffb 0x388db812438e3c3f

def z1066 : W := mkw 0x012d7ed80000003c 0x0004b5fb60000000 0x200ffffc00000000 0xe0803ffff0000000

def z1067 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f03fc0ffc3f 0xff7e01fc0ff03ff0

def z1068 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf007c03fc03fc2f 0x4b7c01f00ff00ff0

def z1069 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xbfff8003fffc0016 0x36fffe000ffff000

def z1070 : W := mkw 0x0ffd7ed82002083c 0x203ff5fb60800820 0xeffffffce0030002 0xffbffffff3800c00

def z1071 : W := mkw 0x01024400610a0800 0xa004091001842820 0xe36e6490e38f0ffb 0x7b8db992438e3c3f

def z1072 : W := mkw 0x800281246d3ecdc0 0xae000a0491b4fb37 0x00000000fc7ccffd 0x0000000003f1f33f

def z1073 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409187fc1c7c0fd8 0xfd02461ff071f03f

def z1074 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fff00006 0x3ffffe000fffc000

def z1075 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xefff8000fffc0018 0x3fbffe0003fff000

def z1076 : W := mkw 0x800081240c34c540 0x0a0002049030d315 0x409187fc1c7c0ff9 0x7902461ff071f03f

def z1077 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0x33ff8003fffc001f 0x38cffe000ffff000

def z1078 : W := mkw 0x0a800102b402ac02 0x302a00040ad00ab0 0xdf807803fc03fc2f 0xcf7e01e00ff00ff0

def z1079 : W := mkw 0x0b805602b0022802 0x302e01580ac008a0 0xdf807803fc03f02f 0xcf7e01e00ff00fc0

def z1080 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xdf807f83fc03ff3f 0xdf7e01fe0ff00ffc

def z1081 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xeffffffc03800013 0xffbffffff00e0000

def z1082 : W := mkw 0x0ffd7edab002283e 0x303ff5fb6ac008a0 0xffffffffe003f027 0xffffffffff800fc0

def z1083 : W := mkw 0x1a8b8003db6c0003 0xc06a2e000f6db000 0xf3ef8003fffc001f 0x3bcfbe000ffff000

def z1084 : W := mkw 0x947ba8e54bfd5371 0xca51eea3952ff54d 0x207f80fc03fc03d0 0x3081fe03f00ff00f

def z1085 : W := mkw 0x1edb920bdb6c0007 0xc07b6e482f6db000 0xffff830ffffc001f 0x3ffffe0c3ffff000

def z1086 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff80e3fffc001f 0xfffffe038ffff000

def z1087 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xe36e6490e38c0fd8 0x7b8db992438e303f

def z1088 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0x9f807f03fc03fc2a 0xca7e01fc0ff00ff0

def z1089 : W := mkw 0x0ffd7ed902c1123d 0x003ff5fb640b0448 0xffffffff03f33017 0xfffffffffc0fccc0

def z1090 : W := mkw 0x0ffd7eda9000003e 0x003ff5fb6a400000 0xffffffff1c000004 0xfffffffffc700000

def z1091 : W := mkw 0x0ffd7ed820830abc 0x243ff5fb60820c2a 0xeffffffc03830ff3 0xffbffffff00e0c3f

def z1092 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x2fff9ffc00000000 0xbcbffe7ff0000000

def z1093 : W := mkw 0x1a828003db6c0003 0xc06a0a000f6db000 0xffee0003fffc001f 0x3fffb8000ffff000

def z1094 : W := mkw 0x01267690618b2aa8 0xb40499da41862caa 0xe36e7c90e38f3ffb 0x7b8db9f2438e3cff

def z1095 : W := mkw 0x0b804402b0020802 0x202e01100ac00820 0xdf807c03fc03fc2f 0xcf7e01f00ff00ff0

def z1096 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x2cfffffc00000000 0xf4b3fffff0000000

def z1097 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0xaffffffc00000000 0xc6bffffff0000000

def z1098 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xff6e6493e38f0fff 0x7ffdb9924f8e3c3f

def z1099 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c7078e303f3f337 0x1271c1e38c0fcfcc

def z1100 : W := mkw 0x0b89570ab402ac06 0x302e255c2ad00ab0 0xdf81ff0ffc03fc2f 0xcf7e07fc3ff00ff0

def z1101 : W := mkw 0x047428f102d153b9 0x0c11d0a3c40b454e 0xdc7078f303f3f3f7 0xd771c1e3cc0fcfcf

def z1102 : W := mkw 0x0b805702b402ac02 0x302e015c0ad00ab0 0xffee7f03fc03fc2f 0xffffb9fc0ff00ff0

def z1103 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0xdc707cf303f3fff7 0xd771c1f3cc0fcfff

def z1104 : W := mkw 0x0a8013029400a402 0x102a004c0a500290 0xdf807b03fc03f02f 0xcf7e01ec0ff00fc0

def z1105 : W := mkw 0x80028126fdbfefc2 0xbe000a049bf6ffbf 0x10000003ffffffff 0x004000000fffffff

def z1106 : W := mkw 0x0ffd7ed80081023c 0x003ff5fb60020408 0xeffffffc038f0ffb 0xffbffffff00e3c3f

def z1107 : W := mkw 0x0ffd7ed820830abc 0x243ff5fb60820c2a 0xeffffffce0030feb 0xffbffffff3800c3f

def z1108 : W := mkw 0x047028e102d15331 0x0811c0a3840b454c 0x9c7078e303f3f332 0xd271c1e38c0fcfcc

def z1109 : W := mkw 0x1edb8003db6c0003 0xc07b6e000f6db000 0xffff8003fffc0fff 0x3ffffe000ffff03f

def z1110 : W := mkw 0x0ffd7ed80000003c 0x003ff5fb60000000 0x23fffffc00000000 0xf88ffffff0000000

def z1111 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xa36e6410e38f0ffb 0x2a8db990438e3c3f

def z1112 : W := mkw 0x01266490618b0aa8 0xa404999241862c2a 0xef6e7c90e38f0ffb 0xffbdb9f2438e3c3f

def z1113 : W := mkw 0x047028c102400031 0x0011c0a304090000 0xdc7078e303f3f037 0xd771c1e38c0fcfc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z8,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z10]),(0,[z1,z11,z2,z3,z4,z9,z6]),(0,[z12,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z13,z3,z4,z9,z6])],[(0,[z14,z1,z2,z3,z4,z9,z6]),(0,[z15,z1,z2,z3,z4,z9,z6]),(0,[z16,z1,z2,z3,z4,z9,z6])],[],[(0,[z17,z1,z2,z3,z4,z9,z6]),(0,[z1,z18,z2,z3,z4,z9,z6])],[(0,[z19,z2,z3,z4,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z21,z6]),(1,[z22,z1,z2,z3,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z23]),(0,[z24,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z25,z6]),(0,[z26,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z27,z9,z6]),(0,[z2,z3,z4,z28,z9,z29,z6]),(0,[z1,z2,z3,z4,z9,z6,z30]),(0,[z1,z2,z3,z31,z4,z9,z6]),(1,[z32,z2,z3,z4,z9,z6])],[(0,[z33,z1,z2,z3,z4,z9,z6]),(0,[z34,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z4,z9,z6]),(0,[z36,z1,z2,z37,z4,z9,z6])]],
   [[(0,[z38,z2,z3,z4,z9,z29,z6]),(0,[z0,z1,z2,z3,z4,z9,z39]),(0,[z40,z1,z2,z3,z4,z9,z6]),(0,[z1,z41,z2,z3,z4,z9,z6]),(0,[z2,z3,z4,z9,z6,z42,z43]),(1,[z1,z2,z3,z44,z9,z6])],[(0,[z1,z2,z3,z45,z4,z9,z6]),(0,[z1,z2,z46,z3,z4,z9,z6]),(0,[z1,z47,z2,z3,z4,z9,z6]),(0,[z1,z2,z48,z3,z4,z9,z6]),(1,[z49,z1,z2,z3,z4,z6]),(0,[z49,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z4,z50,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z51]),(0,[z52,z1,z2,z3,z4,z9,z6]),(1,[z1,z53,z3,z54,z9,z6]),(0,[z55,z1,z2,z3,z4,z9,z6]),(0,[z56,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z57,z3,z9,z58,z6]),(0,[z1,z2,z3,z59,z4,z9,z6])],[(0,[z1,z11,z2,z3,z4,z60,z6])],[(0,[z1,z2,z3,z4,z61,z9,z6]),(0,[z62,z1,z2,z3,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z63,z6]),(0,[z0,z1,z11,z3,z4,z9,z6]),(0,[z64,z1,z2,z3,z4,z9,z6])],[(0,[z65,z1,z2,z3,z4,z9,z6]),(0,[z66,z1,z2,z3,z67,z9,z6]),(0,[z1,z2,z3,z68,z4,z9,z6]),(0,[z1,z2,z69,z4,z9,z70,z6])],[(0,[z71,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z72,z9,z6])],[(0,[z73,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z74,z3,z4,z9,z6]),(0,[z75,z1,z2,z3,z4,z9,z6]),(0,[z1,z76,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z77,z9,z6])]],
   [[(0,[z1,z2,z3,z78,z4,z9,z6]),(0,[z1,z2,z3,z8,z79,z9,z6]),(0,[z80,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z81,z6]),(0,[z1,z57,z82,z3,z4,z9,z6]),(0,[z1,z2,z3,z83,z4,z9,z6])],[(0,[z1,z2,z84,z3,z4,z9,z6]),(0,[z36,z62,z1,z2,z3,z9,z6]),(0,[z85,z1,z2,z86,z4,z9,z6]),(0,[z1,z2,z3,z87,z9,z88,z6]),(0,[z1,z32,z2,z3,z4,z9,z6])],[(0,[z89,z1,z2,z3,z4,z9,z6]),(0,[z1,z90,z2,z3,z4,z9,z6]),(0,[z91,z1,z2,z3,z4,z9,z6]),(0,[z92,z1,z93,z3,z4,z9,z6]),(1,[z1,z2,z3,z94,z9,z6]),(0,[z1,z11,z3,z4,z9,z95,z6]),(0,[z1,z2,z69,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z4,z9,z6])],[(0,[z96,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z97,z6]),(0,[z1,z2,z3,z4,z9,z98,z6])],[(0,[z2,z3,z4,z20,z28,z9,z6]),(0,[z1,z2,z3,z99,z4,z9,z6]),(0,[z7,z1,z2,z3,z54,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z100])],[(0,[z1,z101,z2,z3,z4,z9,z6]),(0,[z1,z102,z2,z103,z4,z9,z6])],[(0,[z104,z1,z105,z3,z4,z9,z6]),(0,[z106,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z107,z4,z9,z6]),(0,[z36,z1,z2,z3,z9,z6,z108])],[(0,[z109,z62,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z110,z4,z9,z6]),(0,[z1,z2,z3,z111,z4,z9,z6]),(0,[z1,z102,z2,z4,z112,z9,z6]),(0,[z1,z2,z3,z8,z9,z58,z6])]],
   [[(0,[z113,z1,z2,z3,z4,z9,z6]),(0,[z114,z2,z105,z3,z4,z9,z6]),(0,[z1,z115,z2,z3,z4,z9,z6]),(0,[z116,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z117,z6]),(0,[z118,z1,z2,z3,z4,z9,z6]),(0,[z1,z3,z4,z9,z119,z6,z120]),(0,[z85,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z121,z9,z6]),(0,[z1,z2,z3,z4,z58,z6,z43]),(0,[z122,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z123,z4,z9,z6,z124]),(0,[z92,z2,z3,z4,z9,z6,z125]),(0,[z126,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z127,z3,z4,z9,z6])],[(0,[z1,z2,z3,z110,z9,z6,z108]),(1,[z128,z2,z3,z4,z9,z6]),(1,[z129,z1,z2,z3,z130,z6])],[(0,[z1,z2,z3,z4,z9,z131,z6]),(0,[z1,z2,z3,z4,z132,z9,z6]),(0,[z133,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z134,z6]),(0,[z1,z2,z3,z4,z9,z135,z6])],[(0,[z1,z2,z3,z4,z136,z9,z6]),(0,[z7,z1,z2,z3,z8,z9,z6]),(0,[z1,z2,z137,z3,z4,z9,z6])],[(0,[z1,z2,z3,z138,z4,z9,z6]),(0,[z0,z1,z2,z3,z4,z139,z6]),(0,[z1,z2,z3,z4,z140,z9,z6]),(0,[z1,z53,z3,z4,z54,z9,z6]),(0,[z1,z141,z2,z3,z4,z9,z6]),(0,[z129,z142,z2,z3,z4,z9,z6])],[(0,[z143,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z54,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z144])]],
   [[(0,[z145,z1,z2,z3,z4,z9,z6]),(0,[z146,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z28,z147,z6]),(0,[z1,z2,z148,z3,z4,z9,z6]),(0,[z149,z1,z2,z3,z4,z9,z6]),(1,[z150,z1,z3,z4,z9,z6])],[(0,[z1,z2,z151,z3,z4,z9,z6]),(0,[z1,z2,z152,z3,z4,z9,z6]),(1,[z1,z2,z69,z4,z9,z70]),(0,[z1,z2,z3,z87,z4,z130,z6]),(0,[z1,z2,z3,z4,z9,z6,z153])],[(0,[z154,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z155,z9,z6])],[(0,[z109,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z54,z9,z6]),(0,[z1,z2,z3,z4,z9,z156,z6]),(1,[z1,z2,z3,z4,z147,z135])],[(0,[z66,z1,z2,z123,z4,z9,z6]),(0,[z1,z2,z3,z4,z157,z9,z6]),(0,[z92,z19,z2,z3,z4,z9,z6]),(1,[z1,z2,z158,z4,z9,z6]),(1,[z159,z2,z3,z4,z9,z6]),(0,[z160,z1,z2,z3,z4,z9,z6])],[(0,[z161,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z162,z9,z6]),(0,[z1,z2,z3,z4,z9,z163,z6]),(0,[z1,z2,z3,z4,z164,z9,z6]),(0,[z1,z2,z165,z3,z4,z9,z6])],[(0,[z166,z1,z2,z3,z4,z9,z120]),(0,[z167,z1,z2,z3,z4,z9,z6]),(0,[z1,z168,z2,z3,z4,z9,z6])],[(1,[z169,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z1,z170,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z88,z6,z108])]],
   [[(1,[z1,z2,z3,z111,z9,z6]),(0,[z171,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z172,z3,z4,z9,z6]),(0,[z173,z1,z2,z3,z4,z9,z6])],[(0,[z104,z2,z3,z174,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z175,z6]),(0,[z1,z2,z3,z4,z9,z176,z6]),(0,[z1,z2,z3,z4,z177,z9,z6]),(0,[z1,z2,z3,z4,z178,z9,z6]),(0,[z166,z1,z3,z4,z9,z6,z120]),(0,[z1,z179,z2,z3,z4,z9,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z87,z4,z58,z6]),(0,[z180,z1,z2,z3,z4,z9,z6])],[(0,[z104,z114,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z181,z6]),(0,[z62,z1,z2,z3,z110,z9,z6]),(0,[z1,z2,z3,z4,z182,z9,z6]),(0,[z1,z2,z3,z4,z183,z9,z6]),(0,[z184,z1,z2,z3,z4,z9,z6]),(0,[z1,z185,z2,z3,z186,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z187]),(0,[z1,z2,z3,z4,z9,z6,z188]),(0,[z1,z2,z3,z4,z189,z9,z6]),(0,[z1,z2,z57,z3,z9,z88,z6]),(0,[z1,z2,z190,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z191])],[(0,[z92,z1,z2,z3,z4,z9,z192]),(1,[z1,z2,z3,z9,z6,z193]),(0,[z7,z1,z53,z3,z4,z9,z6])],[(0,[z194,z1,z2,z3,z195,z9,z6]),(0,[z196,z1,z2,z3,z4,z9,z6]),(0,[z92,z1,z2,z3,z4,z163,z6]),(0,[z0,z85,z1,z2,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z197,z6]),(0,[z198,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z199,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z88,z6])],[(0,[z1,z2,z200,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z201]),(0,[z1,z2,z3,z4,z9,z202,z6]),(0,[z203,z1,z2,z3,z4,z9,z6])],[(0,[z204,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z205]),(0,[z1,z2,z3,z4,z9,z6,z206]),(0,[z1,z207,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z54,z79,z9,z6]),(0,[z1,z2,z3,z4,z208,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z209])],[(0,[z36,z109,z1,z2,z3,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z193]),(0,[z1,z2,z3,z4,z9,z210,z6]),(0,[z1,z2,z3,z4,z9,z6,z211])],[(0,[z212,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z213])],[(0,[z1,z2,z3,z4,z29,z6,z43]),(0,[z1,z2,z3,z4,z9,z70,z120]),(0,[z129,z1,z2,z3,z79,z9,z6]),(0,[z1,z2,z3,z4,z214,z9,z6]),(0,[z215,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z216,z6]),(0,[z217,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z218,z4,z9,z95,z6])],[(0,[z1,z2,z3,z4,z219,z9,z6]),(0,[z1,z2,z3,z4,z9,z220,z6]),(0,[z1,z102,z2,z99,z4,z9,z6]),(0,[z1,z2,z221,z3,z4,z9,z6])],[(0,[z1,z2,z3,z222,z4,z9,z6]),(0,[z19,z1,z2,z3,z4,z9,z6]),(0,[z223,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z224,z6])],[(0,[z1,z2,z3,z4,z9,z6,z225]),(0,[z1,z2,z3,z4,z9,z226,z6]),(0,[z1,z2,z3,z227,z4,z9,z6]),(0,[z228,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z54,z9,z58,z6]),(1,[z7,z1,z3,z8,z9,z6]),(0,[z1,z2,z3,z4,z229,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z230])]],
   [[(0,[z194,z1,z2,z3,z4,z9,z6]),(0,[z173,z38,z1,z2,z3,z4,z6]),(0,[z231,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z8,z9,z88,z6]),(0,[z1,z2,z3,z4,z232,z9,z6])],[(0,[z233,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z234,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z235]),(0,[z36,z1,z2,z3,z4,z9,z88])],[(0,[z236,z1,z2,z3,z4,z9,z6]),(1,[z237,z2,z123,z4,z9,z6]),(0,[z237,z1,z2,z123,z4,z9,z6]),(1,[z1,z11,z3,z4,z95,z6]),(0,[z1,z2,z3,z4,z9,z6,z238]),(0,[z1,z2,z3,z87,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z239]),(0,[z1,z2,z3,z4,z240,z9,z6])],[(0,[z109,z1,z2,z3,z20,z9,z6]),(1,[z1,z241,z3,z4,z9,z6]),(0,[z1,z2,z242,z3,z4,z9,z6]),(0,[z1,z2,z3,z243,z4,z9,z6])],[(0,[z244,z1,z2,z3,z4,z130,z6]),(0,[z1,z2,z245,z3,z4,z9,z6]),(0,[z1,z2,z86,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z246,z6]),(0,[z247,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z248,z9,z6]),(0,[z249,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z250]),(0,[z1,z251,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z158,z4,z9,z6]),(0,[z19,z1,z2,z3,z4,z9,z192]),(1,[z0,z1,z99,z4,z9,z6]),(0,[z1,z2,z3,z252,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z253]),(0,[z1,z2,z3,z4,z130,z147,z6])],[(0,[z1,z2,z254,z3,z4,z9,z6]),(0,[z1,z2,z3,z255,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z256])]],
   [[(0,[z257,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z258,z3,z4,z9,z6]),(0,[z259,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z260,z9,z6])],[(0,[z261,z1,z2,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z54,z9,z6]),(0,[z1,z2,z3,z4,z9,z262,z6]),(0,[z166,z1,z185,z3,z4,z9,z6]),(0,[z1,z263,z2,z3,z4,z9,z6])],[(0,[z1,z2,z264,z3,z4,z9,z6]),(0,[z129,z1,z2,z3,z8,z9,z6]),(0,[z1,z2,z3,z4,z248,z9,z6]),(0,[z1,z2,z3,z4,z9,z265,z6])],[(0,[z1,z266,z2,z3,z4,z9,z6])],[(0,[z1,z267,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z268,z6]),(0,[z1,z2,z269,z3,z4,z270,z6])],[(0,[z1,z2,z3,z4,z9,z271,z6]),(0,[z1,z2,z3,z4,z9,z272,z6])],[(0,[z1,z2,z3,z4,z9,z273,z6]),(0,[z1,z2,z3,z110,z54,z9,z6]),(1,[z1,z2,z218,z4,z9,z6]),(0,[z1,z2,z274,z3,z4,z9,z6]),(0,[z150,z1,z2,z3,z4,z9,z6]),(0,[z1,z275,z3,z4,z9,z270,z6]),(0,[z1,z2,z3,z4,z9,z6,z276]),(0,[z1,z2,z277,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z278]),(0,[z36,z279,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z147,z9,z43])]],
   [[(0,[z1,z2,z3,z280,z4,z9,z6]),(0,[z1,z103,z3,z4,z54,z9,z6]),(0,[z1,z2,z281,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z282,z9,z6]),(0,[z1,z2,z3,z283,z4,z9,z6])],[(0,[z284,z1,z2,z3,z4,z9,z6]),(0,[z129,z1,z2,z3,z87,z9,z6])],[(0,[z1,z2,z285,z3,z4,z9,z6]),(1,[z1,z2,z286,z4,z9,z6]),(0,[z36,z1,z2,z3,z8,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z287]),(1,[z1,z2,z137,z3,z9,z6]),(0,[z34,z1,z2,z3,z4,z112,z6])],[(0,[z1,z2,z3,z4,z9,z288,z6]),(0,[z85,z1,z102,z2,z4,z9,z6]),(0,[z166,z1,z2,z3,z4,z9,z119]),(0,[z1,z2,z3,z4,z289,z9,z6]),(0,[z1,z2,z3,z4,z290,z9,z6])],[(0,[z291,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z292]),(0,[z1,z2,z3,z4,z293,z9,z6]),(0,[z294,z1,z2,z3,z4,z9,z6]),(0,[z34,z1,z2,z269,z4,z9,z6])],[(0,[z295,z1,z2,z3,z4,z9,z6]),(0,[z7,z1,z103,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z296])],[(0,[z1,z2,z297,z3,z4,z9,z6])],[(0,[z1,z2,z3,z298,z4,z9,z6]),(0,[z34,z1,z2,z4,z112,z9,z6])]],
   [[(0,[z299,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z300]),(0,[z1,z2,z3,z301,z4,z9,z6])],[(0,[z1,z302,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z303,z4,z9,z6]),(0,[z36,z1,z2,z3,z87,z9,z6])],[(0,[z1,z2,z3,z4,z28,z6,z43]),(0,[z1,z2,z3,z4,z9,z304,z6]),(0,[z1,z2,z3,z4,z9,z6,z305]),(1,[z1,z2,z3,z9,z6,z100])],[],[(0,[z85,z1,z2,z4,z9,z6,z124]),(0,[z150,z1,z57,z3,z4,z9,z6]),(0,[z306,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z69,z3,z4,z9,z70]),(0,[z1,z2,z3,z4,z307,z9,z6]),(0,[z1,z2,z3,z308,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z309])],[(0,[z1,z2,z3,z94,z4,z9,z6]),(0,[z85,z1,z2,z57,z4,z9,z6])],[(0,[z1,z2,z310,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z4,z9,z6]),(0,[z1,z2,z3,z311,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z312,z6]),(0,[z1,z185,z2,z3,z4,z9,z120]),(0,[z1,z2,z3,z4,z313,z9,z6])],[(0,[z109,z2,z3,z4,z28,z9,z6]),(0,[z19,z2,z3,z4,z9,z192,z6]),(0,[z1,z2,z3,z4,z314,z9,z6]),(0,[z315,z1,z2,z3,z4,z9,z6]),(0,[z249,z1,z2,z3,z4,z9,z124]),(0,[z1,z2,z3,z130,z9,z58,z6])]],
   [[(0,[z1,z316,z2,z3,z4,z9,z6]),(0,[z92,z2,z3,z4,z28,z9,z6]),(0,[z36,z1,z2,z317,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z43])],[(0,[z1,z2,z3,z318,z4,z9,z6]),(0,[z92,z1,z2,z3,z319,z9,z6]),(0,[z166,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z320,z4,z9,z6])],[(0,[z321,z1,z2,z3,z4,z9,z6]),(0,[z109,z1,z2,z3,z110,z9,z6]),(0,[z0,z1,z2,z3,z4,z9,z322]),(0,[z1,z2,z4,z9,z70,z6,z124]),(0,[z1,z2,z3,z4,z9,z6,z108])],[(0,[z1,z2,z3,z4,z323,z9,z6]),(0,[z1,z2,z324,z3,z4,z9,z6])],[(0,[z109,z2,z3,z4,z9,z6,z125]),(0,[z1,z2,z3,z4,z9,z6,z325]),(0,[z1,z326,z2,z3,z4,z9,z6])],[(0,[z327,z1,z2,z3,z4,z9,z6])],[(0,[z1,z328,z2,z3,z4,z9,z6]),(0,[z1,z2,z329,z69,z3,z9,z6]),(0,[z1,z2,z3,z4,z9,z330,z6])],[(0,[z1,z2,z331,z3,z4,z9,z6]),(0,[z1,z332,z2,z3,z4,z9,z6]),(0,[z333,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z334,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z335,z4,z9,z6]),(0,[z1,z2,z3,z283,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z336,z6]),(0,[z1,z2,z3,z337,z4,z9,z6])],[(0,[z1,z2,z3,z338,z4,z9,z6]),(0,[z1,z2,z3,z339,z4,z9,z6]),(1,[z1,z2,z3,z4,z340,z6]),(0,[z1,z2,z3,z4,z341,z9,z6]),(0,[z92,z1,z2,z3,z4,z177,z6]),(0,[z1,z11,z2,z3,z342,z9,z6]),(1,[z173,z1,z2,z3,z4,z43])],[(1,[z1,z2,z3,z157,z9,z6]),(0,[z343,z1,z2,z3,z4,z9,z6]),(1,[z92,z2,z3,z4,z9,z125]),(1,[z1,z82,z3,z4,z9,z6])],[(0,[z1,z2,z344,z3,z4,z9,z6]),(0,[z345,z1,z3,z4,z60,z9,z6]),(0,[z1,z2,z269,z3,z248,z9,z6]),(1,[z1,z2,z269,z4,z270,z6])],[(1,[z1,z2,z346,z4,z9,z6]),(0,[z85,z1,z2,z69,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z347,z6])],[(0,[z348,z1,z2,z3,z4,z9,z6]),(0,[z169,z1,z2,z3,z4,z9,z6]),(0,[z1,z53,z2,z3,z4,z9,z6]),(1,[z166,z1,z3,z4,z9,z120])],[(0,[z109,z19,z2,z3,z4,z9,z6]),(0,[z38,z1,z2,z3,z4,z130,z6]),(0,[z1,z2,z3,z4,z349,z9,z6]),(0,[z1,z2,z350,z3,z4,z9,z6]),(0,[z129,z1,z2,z57,z3,z9,z6]),(0,[z1,z2,z3,z4,z9,z351,z6]),(0,[z1,z2,z3,z4,z9,z70,z6])],[(0,[z1,z2,z3,z4,z9,z352,z6]),(0,[z353,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z354]),(1,[z1,z2,z3,z178,z9,z6]),(0,[z355,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z356,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z357]),(0,[z1,z2,z3,z4,z9,z6,z358])],[(0,[z1,z2,z3,z4,z359,z9,z6]),(0,[z360,z1,z2,z3,z4,z9,z6]),(0,[z1,z11,z103,z3,z4,z9,z6]),(0,[z1,z2,z69,z4,z79,z9,z6]),(0,[z361,z1,z2,z3,z4,z9,z6])],[(0,[z362,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z363]),(0,[z364,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z5,z9,z6]),(0,[z173,z1,z2,z3,z4,z9,z135])],[(0,[z1,z2,z3,z4,z9,z365,z6]),(0,[z1,z2,z3,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z366,z6]),(0,[z1,z2,z3,z20,z130,z9,z6]),(0,[z367,z1,z2,z3,z4,z9,z6]),(0,[z368,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z147,z58,z6])],[(0,[z369,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z370,z4,z9,z6]),(0,[z0,z1,z2,z269,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z371,z6]),(0,[z1,z275,z2,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z4,z216,z6])],[(0,[z1,z2,z123,z69,z4,z9,z6]),(0,[z0,z1,z2,z103,z4,z9,z6]),(1,[z345,z1,z3,z4,z60,z6]),(0,[z1,z2,z329,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z20,z9,z6]),(1,[z1,z185,z3,z4,z9,z119]),(0,[z372,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z373,z9,z6]),(0,[z36,z1,z172,z3,z4,z9,z6])],[(0,[z194,z1,z105,z3,z4,z9,z6]),(0,[z38,z1,z2,z3,z4,z58,z6]),(0,[z0,z1,z3,z99,z4,z9,z6]),(0,[z0,z1,z2,z4,z112,z9,z6]),(0,[z1,z374,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z375,z6]),(0,[z376,z1,z2,z3,z4,z9,z6]),(1,[z36,z1,z2,z3,z9,z108]),(0,[z1,z2,z3,z4,z9,z377,z6]),(0,[z1,z2,z3,z283,z4,z9,z88])]],
   [[(0,[z66,z1,z2,z3,z157,z9,z6]),(0,[z2,z3,z110,z4,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z378,z6]),(0,[z1,z2,z4,z379,z9,z95,z6]),(0,[z1,z2,z3,z380,z4,z9,z6])],[(1,[z194,z105,z3,z4,z9,z6])],[(0,[z1,z159,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z381,z9,z6])],[(0,[z1,z2,z3,z4,z382,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z383]),(0,[z1,z2,z3,z4,z9,z6,z384]),(1,[z1,z2,z3,z283,z9,z88])],[(0,[z1,z2,z3,z4,z9,z385,z6]),(0,[z1,z2,z3,z386,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z387])],[(0,[z237,z1,z2,z3,z4,z9,z6]),(0,[z388,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z39]),(0,[z1,z2,z3,z4,z9,z389,z6]),(0,[z1,z2,z390,z3,z4,z9,z6]),(1,[z34,z1,z2,z4,z112,z6]),(0,[z1,z2,z3,z4,z9,z391,z6]),(0,[z173,z1,z2,z3,z4,z147,z6])],[(0,[z1,z2,z3,z79,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z392,z6]),(0,[z1,z2,z3,z393,z4,z9,z6]),(1,[z1,z2,z3,z232,z9,z6])],[(0,[z244,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z394,z9,z6]),(0,[z395,z1,z2,z3,z4,z9,z6]),(0,[z396,z1,z2,z3,z4,z9,z6]),(0,[z397,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z398,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z399]),(0,[z1,z400,z2,z3,z4,z9,z6]),(1,[z401,z1,z2,z4,z9,z6]),(0,[z1,z2,z3,z4,z95,z270,z6]),(0,[z1,z2,z3,z4,z379,z9,z6]),(0,[z1,z2,z402,z3,z4,z9,z6]),(0,[z249,z1,z2,z4,z9,z6,z124]),(0,[z1,z2,z3,z130,z9,z88,z6])],[(0,[z1,z2,z3,z4,z9,z403,z6]),(0,[z1,z404,z2,z3,z4,z9,z6]),(0,[z405,z1,z2,z3,z4,z9,z6]),(0,[z406,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z407,z9,z6]),(0,[z1,z2,z3,z4,z9,z408,z6]),(0,[z1,z3,z4,z60,z9,z95,z6]),(0,[z1,z2,z3,z4,z9,z6,z409]),(0,[z1,z2,z3,z410,z4,z9,z6]),(0,[z36,z1,z168,z3,z4,z9,z6]),(0,[z411,z1,z2,z3,z4,z9,z6]),(0,[z412,z1,z2,z3,z4,z9,z6]),(0,[z413,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z414,z3,z4,z9,z6]),(0,[z401,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z415,z3,z4,z9,z6])],[(0,[z1,z416,z2,z3,z4,z9,z6]),(0,[z1,z185,z2,z3,z417,z9,z6]),(0,[z1,z2,z3,z4,z147,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z418])],[],[(0,[z0,z1,z2,z3,z419,z9,z6]),(0,[z0,z1,z2,z4,z79,z9,z6]),(0,[z1,z2,z3,z346,z4,z9,z6]),(0,[z420,z1,z2,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z79,z9,z6]),(0,[z1,z2,z421,z3,z4,z9,z6])],[(0,[z422,z1,z2,z3,z4,z9,z6]),(0,[z38,z1,z2,z3,z4,z9,z6]),(0,[z1,z11,z2,z3,z94,z9,z6]),(0,[z423,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z424]),(0,[z249,z1,z2,z3,z4,z9,z70])]],
   [[(0,[z1,z2,z3,z4,z9,z6,z425])],[(1,[z1,z2,z3,z4,z6,z426]),(0,[z1,z427,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z60,z270,z6]),(0,[z1,z2,z3,z4,z9,z428,z6]),(1,[z1,z275,z3,z4,z9,z6])],[(1,[z1,z93,z3,z4,z9,z6])],[(0,[z1,z2,z429,z3,z4,z9,z6]),(0,[z1,z2,z3,z110,z79,z9,z6]),(0,[z1,z2,z3,z4,z9,z430,z6]),(0,[z1,z2,z3,z4,z9,z431,z6]),(0,[z1,z2,z3,z4,z432,z9,z6]),(0,[z1,z2,z3,z4,z9,z433,z6]),(0,[z1,z2,z3,z4,z434,z9,z6]),(0,[z1,z2,z3,z4,z435,z9,z6])],[(0,[z104,z1,z114,z3,z4,z9,z6]),(0,[z1,z2,z3,z436,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z437]),(0,[z1,z185,z3,z4,z9,z119,z6]),(0,[z36,z32,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z54,z9,z6]),(0,[z1,z185,z3,z4,z54,z9,z6]),(0,[z85,z1,z2,z3,z79,z9,z6]),(0,[z1,z438,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z439,z4,z9,z6]),(1,[z1,z2,z3,z417,z9,z6])],[(0,[z1,z2,z3,z440,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z441]),(0,[z442,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z443,z6]),(1,[z2,z3,z4,z9,z6,z42]),(0,[z444,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z62,z1,z2,z3,z9,z88,z6]),(0,[z244,z1,z2,z3,z4,z58,z6]),(0,[z92,z1,z241,z3,z4,z9,z6]),(0,[z1,z2,z3,z445,z4,z9,z6]),(0,[z1,z2,z446,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z447,z9,z6])],[(1,[z1,z2,z3,z195,z9,z6]),(0,[z1,z2,z448,z3,z4,z9,z6]),(0,[z1,z185,z2,z3,z4,z9,z6]),(1,[z1,z2,z37,z4,z9,z6])],[],[(0,[z1,z2,z3,z449,z4,z9,z6]),(1,[z1,z2,z3,z4,z139,z6])],[(0,[z1,z102,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z450,z6]),(0,[z1,z2,z3,z4,z9,z6,z451])],[(0,[z1,z2,z3,z4,z9,z452,z6]),(0,[z1,z2,z453,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z454,z9,z6])],[(0,[z1,z2,z3,z455,z4,z9,z6]),(0,[z1,z2,z3,z456,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z457,z6])]],
   [[(0,[z1,z2,z69,z174,z4,z9,z6]),(0,[z458,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z459,z9,z6]),(1,[z38,z2,z3,z4,z29,z6]),(0,[z1,z2,z3,z460,z4,z9,z6]),(0,[z1,z3,z4,z454,z9,z270,z6])],[(0,[z38,z2,z3,z4,z20,z9,z6]),(0,[z1,z2,z3,z20,z9,z6,z108]),(0,[z1,z2,z3,z4,z461,z9,z6])],[(0,[z0,z7,z1,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z462]),(0,[z1,z2,z3,z4,z9,z463,z6]),(0,[z1,z2,z3,z4,z9,z464,z6]),(0,[z1,z2,z3,z4,z9,z6,z42])],[(0,[z1,z2,z86,z4,z79,z9,z6])],[(1,[z1,z2,z3,z4,z9,z6]),(0,[z1,z53,z2,z3,z54,z9,z6]),(0,[z1,z2,z3,z4,z465,z9,z6]),(0,[z1,z2,z3,z466,z4,z9,z6])],[(0,[z1,z2,z3,z87,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z467]),(0,[z1,z2,z3,z4,z9,z6,z125]),(0,[z0,z1,z3,z4,z60,z9,z6]),(0,[z1,z2,z468,z3,z4,z9,z6]),(0,[z1,z469,z2,z3,z4,z9,z6]),(0,[z1,z2,z37,z3,z4,z9,z6])],[(0,[z1,z2,z3,z110,z4,z97,z6]),(0,[z470,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z471,z3,z4,z9,z6]),(0,[z1,z2,z57,z3,z4,z9,z6]),(0,[z472,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z317,z4,z9,z6])]],
   [[(0,[z473,z1,z2,z3,z4,z9,z6]),(0,[z244,z1,z2,z3,z4,z9,z6]),(0,[z474,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z120,z124]),(1,[z1,z3,z4,z454,z9,z6])],[(1,[z1,z2,z3,z323,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z475])],[(0,[z194,z104,z2,z3,z4,z9,z6]),(0,[z1,z2,z82,z3,z4,z9,z6])],[(0,[z109,z2,z3,z110,z4,z9,z6]),(0,[z1,z2,z3,z54,z9,z88,z6]),(0,[z1,z2,z3,z4,z9,z70,z119]),(0,[z1,z2,z476,z3,z4,z9,z6])],[(0,[z194,z2,z105,z3,z4,z9,z6]),(0,[z237,z66,z2,z3,z4,z9,z6]),(0,[z1,z2,z477,z3,z4,z9,z6]),(0,[z478,z1,z2,z3,z4,z9,z6]),(0,[z479,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z120]),(0,[z1,z2,z3,z4,z9,z480,z6]),(0,[z1,z2,z3,z481,z4,z9,z6]),(0,[z1,z2,z482,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z483]),(0,[z244,z1,z2,z3,z323,z9,z6]),(0,[z1,z53,z2,z3,z8,z9,z6]),(0,[z36,z1,z2,z3,z4,z9,z108])],[(0,[z484,z1,z2,z3,z4,z9,z6]),(0,[z485,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z119,z124]),(0,[z1,z2,z3,z486,z4,z9,z6])],[(0,[z1,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z487,z6]),(0,[z1,z2,z3,z4,z488,z9,z6]),(1,[z249,z1,z2,z4,z9,z124]),(0,[z489,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z194,z1,z2,z3,z490,z9,z6]),(0,[z1,z2,z3,z4,z491,z9,z6]),(1,[z62,z2,z3,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z492,z6])],[(0,[z38,z1,z2,z3,z4,z28,z6]),(1,[z1,z2,z4,z379,z9,z6])],[(0,[z66,z1,z2,z3,z4,z9,z6]),(0,[z2,z123,z3,z174,z4,z9,z6]),(0,[z493,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z494,z4,z9,z6]),(0,[z22,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z495,z6]),(0,[z1,z2,z3,z496,z4,z9,z6])],[(0,[z244,z1,z2,z3,z4,z29,z6]),(0,[z1,z2,z3,z8,z4,z9,z6]),(0,[z497,z1,z2,z3,z4,z9,z6]),(0,[z1,z498,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z499,z4,z9,z6]),(0,[z129,z1,z2,z3,z130,z9,z6])],[(0,[z1,z2,z3,z500,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z340,z6]),(0,[z1,z2,z3,z4,z9,z501,z6]),(0,[z502,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z270,z6]),(0,[z1,z2,z3,z4,z9,z6,z124]),(0,[z1,z2,z3,z4,z503,z9,z6])],[(0,[z1,z2,z504,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z505,z6]),(0,[z506,z1,z2,z3,z4,z9,z6]),(0,[z173,z1,z2,z3,z4,z6,z43])]],
   [[(0,[z507,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z419,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z508]),(0,[z1,z2,z86,z3,z79,z9,z6]),(1,[z142,z2,z3,z4,z9,z6])],[(0,[z66,z2,z3,z174,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z509])],[(0,[z1,z2,z510,z3,z4,z9,z6])],[(0,[z1,z2,z3,z511,z4,z9,z6]),(0,[z1,z512,z2,z3,z4,z9,z6]),(0,[z513,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z174,z4,z9,z6,z124])],[(0,[z514,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z515,z9,z6]),(0,[z1,z2,z516,z3,z4,z9,z6]),(0,[z0,z1,z102,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z517,z6]),(0,[z1,z518,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z87,z9,z58,z6]),(0,[z36,z1,z2,z3,z130,z9,z6])],[(0,[z1,z519,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z520]),(0,[z1,z2,z3,z521,z4,z9,z6]),(0,[z129,z1,z2,z3,z4,z130,z6])],[(0,[z1,z2,z57,z3,z20,z9,z6]),(0,[z1,z2,z522,z3,z4,z9,z6])]],
   [[(0,[z523,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z39]),(0,[z1,z2,z3,z4,z524,z9,z6]),(0,[z525,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z526,z4,z9,z6]),(0,[z36,z1,z2,z57,z3,z9,z6]),(0,[z1,z527,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z317,z4,z9,z6]),(0,[z173,z1,z2,z3,z4,z9,z43])],[(0,[z1,z2,z3,z195,z4,z9,z6]),(0,[z1,z2,z3,z110,z130,z9,z6]),(0,[z1,z2,z3,z4,z528,z9,z6]),(0,[z529,z1,z2,z3,z4,z9,z6]),(0,[z530,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z269,z4,z9,z270,z6])],[(0,[z1,z105,z3,z4,z9,z6,z120]),(0,[z531,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z532,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z533,z9,z6]),(0,[z401,z1,z2,z8,z4,z9,z6]),(0,[z1,z2,z3,z4,z112,z9,z6]),(0,[z1,z142,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z130,z6,z43]),(0,[z1,z2,z3,z4,z9,z6,z534])],[(0,[z1,z2,z535,z3,z4,z9,z6]),(0,[z1,z2,z3,z87,z110,z9,z6]),(0,[z92,z1,z2,z158,z4,z9,z6]),(0,[z1,z536,z2,z3,z4,z9,z6]),(0,[z537,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z538,z9,z6]),(0,[z1,z539,z2,z3,z4,z9,z6])],[(0,[z7,z1,z3,z4,z9,z6,z120]),(0,[z1,z2,z3,z4,z9,z540,z6]),(0,[z1,z2,z541,z3,z4,z9,z6]),(0,[z542,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z543,z6])],[(0,[z1,z2,z3,z4,z342,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z544])],[(0,[z1,z2,z3,z4,z112,z95,z6]),(0,[z545,z1,z2,z3,z4,z9,z6]),(1,[z85,z1,z2,z57,z9,z6]),(0,[z129,z1,z2,z3,z4,z58,z6])]],
   [[(0,[z92,z1,z2,z3,z111,z9,z6]),(0,[z546,z1,z2,z3,z4,z9,z6]),(0,[z85,z1,z2,z57,z3,z9,z6])],[(0,[z547,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z548,z3,z4,z9,z6]),(0,[z1,z2,z93,z3,z4,z9,z6]),(0,[z1,z103,z3,z4,z60,z9,z6]),(0,[z549,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z550]),(0,[z1,z2,z269,z3,z4,z9,z6]),(0,[z551,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z552])],[(0,[z1,z2,z3,z553,z4,z9,z6]),(0,[z1,z114,z3,z4,z9,z6,z120]),(0,[z554,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z555]),(0,[z1,z556,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z557,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z558]),(0,[z1,z559,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z8,z20,z9,z6]),(0,[z1,z2,z3,z417,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z560,z6])],[(0,[z561,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z112,z60,z6]),(0,[z1,z2,z3,z4,z147,z9,z135])],[(0,[z1,z2,z3,z4,z490,z9,z6]),(1,[z1,z2,z3,z436,z9,z6]),(0,[z1,z562,z2,z3,z4,z9,z6]),(0,[z563,z1,z2,z3,z4,z9,z6]),(0,[z1,z185,z2,z3,z4,z9,z119]),(0,[z1,z2,z3,z4,z564,z9,z6]),(0,[z26,z2,z3,z4,z9,z6,z43]),(0,[z565,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z147,z135,z6])],[(0,[z1,z566,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z567,z9,z6]),(0,[z1,z568,z2,z3,z4,z9,z6]),(0,[z1,z2,z569,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z105,z3,z4,z9,z6]),(0,[z1,z185,z105,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z192,z6]),(0,[z1,z2,z3,z4,z570,z9,z6]),(0,[z1,z2,z3,z4,z571,z9,z6])],[(0,[z572,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z573,z9,z6]),(0,[z574,z1,z2,z3,z4,z9,z6]),(0,[z575,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z576,z9,z6])],[(0,[z1,z2,z577,z3,z4,z9,z6]),(0,[z38,z1,z2,z3,z4,z135,z6]),(0,[z244,z1,z2,z3,z436,z9,z6]),(0,[z1,z2,z3,z578,z4,z9,z6]),(0,[z1,z11,z2,z3,z4,z95,z6]),(0,[z1,z2,z218,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z79,z9,z6]),(0,[z1,z2,z3,z4,z9,z579,z6])],[(0,[z62,z2,z3,z4,z20,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z580]),(0,[z1,z2,z581,z3,z4,z9,z6]),(1,[z1,z2,z3,z87,z58,z6])],[(0,[z1,z2,z3,z582,z4,z9,z6]),(0,[z1,z2,z3,z583,z4,z9,z6])],[(0,[z49,z1,z2,z3,z4,z6,z125]),(0,[z1,z2,z3,z4,z9,z6,z584]),(0,[z1,z2,z137,z269,z3,z9,z6]),(0,[z1,z585,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z586,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z426]),(0,[z587,z1,z2,z3,z4,z9,z6]),(0,[z588,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z57,z3,z54,z9,z6]),(0,[z1,z2,z3,z589,z4,z9,z6])],[(0,[z1,z2,z3,z419,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z322]),(0,[z590,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z119,z6]),(0,[z129,z1,z2,z3,z4,z9,z6])]],
   [[],[(1,[z1,z2,z3,z319,z9,z6]),(0,[z1,z2,z591,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z58,z6]),(1,[z279,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z44,z4,z9,z6])],[(0,[z1,z2,z3,z67,z4,z9,z6]),(0,[z1,z2,z3,z4,z147,z29,z6]),(0,[z592,z1,z2,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z283,z9,z6]),(0,[z36,z1,z2,z3,z4,z50,z6])],[(0,[z593,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z594,z6]),(0,[z249,z1,z2,z69,z4,z9,z6]),(0,[z595,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z44,z9,z6,z43])],[(0,[z1,z2,z2,z3,z4,z9,z6]),(0,[z244,z2,z3,z4,z28,z9,z6]),(0,[z1,z2,z596,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z597,z6]),(0,[z1,z2,z3,z4,z598,z9,z6])],[(0,[z599,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z600,z4,z9,z6]),(0,[z7,z1,z185,z3,z4,z9,z6]),(1,[z26,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z601,z4,z9,z6]),(0,[z1,z2,z57,z3,z110,z9,z6]),(0,[z38,z1,z2,z3,z4,z29,z6]),(1,[z244,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z319,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z602]),(0,[z1,z2,z3,z110,z283,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z6]),(0,[z1,z2,z57,z3,z8,z9,z6]),(0,[z1,z603,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z604,z6]),(0,[z1,z2,z286,z3,z4,z9,z6]),(0,[z2,z3,z4,z9,z192,z6,z125]),(0,[z1,z2,z3,z4,z9,z139,z6]),(0,[z0,z1,z2,z99,z4,z9,z6]),(0,[z1,z2,z605,z3,z4,z9,z6]),(0,[z128,z129,z2,z3,z4,z9,z6])],[(0,[z606,z1,z2,z3,z4,z9,z6]),(0,[z92,z38,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z177,z6]),(0,[z1,z102,z2,z269,z4,z9,z6]),(0,[z1,z2,z3,z79,z9,z58,z6])],[(0,[z1,z2,z607,z3,z4,z9,z6])],[(0,[z1,z114,z185,z3,z4,z9,z6]),(0,[z608,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z28,z9,z6]),(0,[z1,z2,z8,z346,z4,z9,z6]),(0,[z1,z2,z3,z283,z4,z9,z108])],[(0,[z609,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z610,z6]),(0,[z1,z2,z3,z4,z9,z611,z6]),(0,[z1,z612,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z613,z9,z6]),(0,[z34,z1,z2,z3,z4,z270,z6])],[(0,[z2,z105,z3,z174,z4,z9,z6]),(0,[z1,z2,z3,z4,z614,z9,z6]),(0,[z1,z2,z3,z4,z615,z9,z6])],[(0,[z2,z3,z4,z20,z9,z6,z125]),(0,[z38,z109,z2,z3,z4,z9,z6]),(0,[z616,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z617,z9,z6]),(0,[z1,z2,z3,z4,z9,z618,z6])],[(0,[z1,z2,z3,z4,z619,z9,z6]),(0,[z237,z104,z2,z3,z4,z9,z6]),(0,[z1,z103,z3,z99,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z620]),(0,[z621,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z622])]],
   [[(0,[z623,z1,z2,z3,z4,z9,z6])],[(0,[z237,z2,z105,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z9,z6])],[(0,[z38,z244,z2,z3,z4,z9,z6]),(0,[z92,z1,z2,z286,z4,z9,z6]),(0,[z624,z1,z2,z3,z4,z9,z6]),(0,[z345,z1,z11,z3,z4,z9,z6])],[(0,[z1,z2,z3,z625,z4,z9,z6]),(0,[z1,z2,z3,z8,z110,z9,z6]),(0,[z244,z1,z2,z3,z4,z135,z6])],[(0,[z1,z2,z3,z4,z9,z626,z6]),(0,[z1,z2,z3,z283,z9,z88,z6])],[(0,[z194,z1,z114,z3,z4,z9,z6]),(0,[z66,z1,z2,z174,z4,z9,z6]),(0,[z1,z3,z8,z4,z54,z9,z6]),(0,[z1,z2,z3,z4,z9,z95,z6])],[(0,[z1,z2,z3,z4,z627,z9,z6]),(0,[z1,z2,z3,z9,z6,z193,z125]),(0,[z628,z1,z2,z3,z4,z9,z6])],[(0,[z104,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z123,z3,z4,z9,z6]),(1,[z109,z2,z3,z110,z9,z6]),(0,[z1,z2,z3,z4,z9,z629,z6]),(1,[z19,z2,z3,z4,z9,z192]),(0,[z1,z2,z3,z4,z9,z6,z630]),(0,[z631,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z6,z632]),(1,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z4,z79,z9,z6,z124]),(0,[z1,z2,z3,z4,z633,z9,z6])],[(0,[z2,z3,z4,z28,z9,z192,z6]),(0,[z92,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z634,z3,z4,z9,z6]),(0,[z1,z2,z3,z635,z4,z9,z6]),(0,[z1,z2,z636,z3,z4,z9,z6])],[(0,[z22,z1,z2,z3,z9,z6,z125]),(0,[z1,z2,z3,z4,z9,z6,z637]),(0,[z1,z2,z3,z4,z9,z6,z638])],[(0,[z38,z2,z3,z4,z9,z192,z6]),(0,[z1,z639,z2,z3,z4,z9,z6]),(0,[z1,z102,z2,z4,z79,z9,z6]),(0,[z1,z2,z3,z4,z640,z9,z6]),(0,[z1,z641,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z642])],[(0,[z643,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z110,z4,z340,z6]),(0,[z1,z2,z3,z4,z97,z9,z6]),(0,[z1,z2,z3,z4,z644,z9,z6])],[(0,[z1,z2,z3,z4,z9,z29,z6]),(0,[z645,z1,z2,z3,z4,z9,z6]),(0,[z7,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z646,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z647,z9,z6]),(0,[z1,z2,z648,z3,z4,z9,z6]),(0,[z173,z244,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z426,z125]),(0,[z649,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z650])]],
   [[(0,[z651,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z174,z4,z9,z6]),(0,[z1,z2,z3,z652,z4,z9,z6]),(0,[z653,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z69,z3,z4,z9,z124])],[(0,[z654,z1,z2,z3,z4,z9,z6]),(0,[z1,z655,z2,z3,z4,z9,z6]),(0,[z92,z1,z2,z3,z4,z9,z125])],[(0,[z1,z114,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z656,z4,z9,z6])],[],[(0,[z657,z1,z2,z3,z4,z9,z6]),(0,[z658,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z659,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z660]),(0,[z1,z2,z57,z4,z79,z9,z6]),(1,[z1,z2,z3,z4,z216,z6])],[(0,[z1,z2,z3,z4,z661,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z322,z6]),(0,[z662,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z4,z112,z9,z270,z6]),(1,[z1,z172,z3,z4,z9,z6])],[(0,[z1,z2,z663,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z664,z9,z6]),(0,[z665,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z103,z3,z4,z9,z6]),(0,[z1,z2,z3,z666,z4,z9,z6]),(0,[z1,z2,z667,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z130,z9,z6])],[(0,[z668,z1,z2,z3,z4,z9,z6]),(0,[z669,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z57,z86,z3,z9,z6]),(0,[z1,z2,z3,z79,z9,z88,z6])],[(0,[z1,z2,z3,z4,z670,z9,z6]),(0,[z671,z1,z2,z3,z4,z9,z6]),(0,[z237,z1,z2,z174,z4,z9,z6]),(0,[z1,z672,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z673,z4,z9,z6]),(1,[z1,z2,z3,z186,z9,z6])],[(0,[z1,z2,z3,z4,z674,z9,z6]),(0,[z62,z1,z2,z3,z4,z9,z6]),(0,[z1,z102,z103,z3,z4,z9,z6]),(1,[z1,z2,z3,z342,z9,z6]),(0,[z1,z2,z3,z4,z675,z9,z6]),(0,[z1,z2,z3,z676,z4,z9,z6]),(0,[z1,z2,z3,z677,z4,z9,z6]),(0,[z1,z2,z69,z3,z232,z9,z6])],[(0,[z678,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z679,z6]),(0,[z1,z2,z680,z3,z4,z9,z6]),(0,[z345,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z681,z6])],[(1,[z66,z2,z174,z4,z9,z6]),(0,[z1,z2,z3,z4,z682,z9,z6]),(0,[z683,z1,z2,z3,z4,z9,z6]),(0,[z129,z1,z2,z3,z54,z9,z6])],[(0,[z1,z2,z3,z4,z9,z684,z6]),(0,[z1,z2,z3,z4,z60,z9,z6]),(0,[z1,z2,z3,z685,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z686,z6]),(0,[z1,z687,z2,z3,z4,z9,z6]),(0,[z279,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z237,z2,z123,z3,z4,z9,z6]),(0,[z688,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z186,z9,z6]),(1,[z1,z2,z86,z79,z9,z6]),(0,[z689,z1,z2,z3,z4,z9,z6]),(0,[z128,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z6,z100,z43])],[(0,[z1,z2,z3,z4,z690,z9,z6]),(0,[z1,z691,z2,z3,z4,z9,z6]),(0,[z1,z241,z2,z3,z4,z9,z6]),(0,[z692,z1,z2,z3,z4,z9,z6]),(0,[z345,z1,z2,z3,z4,z95,z6]),(0,[z1,z2,z693,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z694]),(0,[z109,z1,z2,z3,z9,z88,z6]),(0,[z0,z159,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z178,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z695])],[(1,[z1,z2,z329,z3,z9,z6]),(1,[z1,z168,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z135,z6,z43])],[(1,[z1,z2,z3,z490,z9,z6]),(0,[z1,z2,z3,z4,z9,z696,z6]),(0,[z19,z1,z2,z3,z4,z9,z125]),(0,[z1,z3,z4,z54,z9,z6,z120]),(0,[z1,z2,z697,z3,z4,z9,z6]),(0,[z1,z698,z2,z3,z4,z9,z6]),(0,[z699,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z700]),(0,[z0,z169,z2,z3,z4,z9,z6]),(0,[z1,z2,z269,z3,z4,z112,z6]),(0,[z1,z2,z701,z3,z4,z9,z6]),(0,[z1,z2,z3,z702,z4,z9,z6])],[(0,[z703,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z704,z6]),(0,[z705,z1,z2,z3,z4,z9,z6])],[(1,[z1,z2,z3,z67,z9,z6]),(0,[z345,z1,z2,z3,z4,z60,z6]),(0,[z706,z1,z2,z3,z4,z9,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z194,z105,z3,z490,z9,z6]),(0,[z26,z2,z3,z4,z29,z6]),(0,[z1,z2,z707,z4,z9,z6]),(0,[z1,z2,z708,z4,z9,z6])],[(0,[z2,z709,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z710,z6]),(0,[z244,z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z712,z9,z6]),(0,[z1,z3,z713,z4,z9,z6]),(0,[z1,z2,z3,z54,z216,z6]),(0,[z714,z1,z2,z417,z9,z6])],[(0,[z1,z2,z3,z715,z9,z6]),(0,[z1,z2,z3,z419,z9,z322]),(0,[z1,z2,z3,z716,z9,z6]),(0,[z1,z2,z3,z4,z147,z347])],[(0,[z2,z3,z4,z9,z717,z125]),(0,[z1,z2,z3,z4,z9,z718]),(0,[z150,z85,z1,z57,z9,z6])],[(0,[z150,z1,z3,z4,z9,z6]),(0,[z7,z401,z1,z8,z9,z6]),(0,[z719,z2,z3,z4,z9,z6])],[(0,[z1,z720,z3,z4,z9,z6]),(0,[z1,z2,z286,z111,z9,z6]),(0,[z1,z2,z3,z721,z9,z6]),(0,[z1,z2,z69,z4,z9,z70])],[(0,[z109,z2,z3,z110,z9,z6]),(0,[z1,z722,z3,z4,z9,z6]),(0,[z19,z2,z3,z4,z9,z192])],[(0,[z7,z1,z3,z4,z9,z39]),(0,[z1,z2,z3,z496,z58,z6]),(0,[z142,z2,z3,z8,z9,z6]),(0,[z1,z2,z3,z723,z9,z6]),(0,[z1,z2,z724,z3,z9,z6]),(0,[z1,z2,z3,z725,z9,z6])]],
   [[(0,[z1,z2,z3,z726,z9,z6]),(0,[z1,z2,z3,z727,z9,z6]),(0,[z1,z2,z4,z728,z9,z6])],[(0,[z2,z3,z4,z20,z97,z6]),(0,[z259,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z729,z9,z6]),(0,[z1,z730,z3,z4,z9,z6])],[(0,[z1,z2,z3,z731,z9,z6]),(0,[z732,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z733,z6]),(0,[z1,z585,z3,z8,z9,z6]),(0,[z1,z2,z3,z8,z216,z6]),(0,[z1,z2,z37,z4,z216,z6])],[(0,[z401,z1,z2,z79,z9,z6]),(0,[z36,z1,z2,z3,z50,z108]),(0,[z2,z3,z9,z6,z100,z42])],[(0,[z1,z2,z3,z111,z9,z6]),(0,[z1,z172,z37,z4,z9,z6])],[(0,[z1,z734,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z6,z735]),(0,[z401,z1,z4,z54,z9,z6]),(0,[z1,z2,z736,z4,z9,z6])],[(0,[z1,z737,z3,z4,z9,z6]),(0,[z0,z1,z4,z112,z60,z6]),(0,[z1,z2,z57,z37,z9,z6]),(0,[z142,z2,z3,z87,z9,z6])],[(0,[z1,z2,z3,z4,z738,z6]),(0,[z1,z11,z218,z4,z9,z6]),(0,[z714,z1,z2,z4,z9,z6]),(0,[z739,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z740,z6])],[(0,[z1,z2,z3,z741,z9,z6]),(0,[z1,z2,z3,z742,z9,z6]),(0,[z1,z2,z3,z9,z743,z6]),(0,[z0,z1,z2,z248,z9,z6]),(0,[z744,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z87,z216,z6]),(0,[z1,z2,z745,z3,z9,z6])],[(0,[z126,z2,z3,z20,z9,z6]),(0,[z109,z22,z2,z3,z9,z6]),(0,[z1,z2,z3,z4,z147,z629])],[(0,[z1,z746,z3,z4,z9,z6]),(0,[z1,z11,z218,z4,z95,z6])],[(0,[z1,z2,z3,z747,z9,z6]),(0,[z1,z748,z3,z4,z9,z6]),(0,[z1,z2,z3,z749,z9,z6]),(0,[z1,z2,z3,z750,z9,z6]),(0,[z1,z2,z751,z218,z9,z6]),(0,[z1,z168,z3,z417,z9,z6]),(0,[z752,z2,z3,z4,z9,z6])],[(0,[z1,z2,z69,z4,z9,z226]),(0,[z36,z32,z2,z3,z9,z108])],[(0,[z561,z2,z3,z110,z9,z6]),(0,[z26,z2,z3,z4,z28,z6]),(0,[z0,z169,z99,z4,z9,z6]),(0,[z753,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z754,z9,z6])],[(0,[z1,z2,z3,z4,z755,z6]),(0,[z0,z1,z589,z4,z9,z6]),(0,[z1,z172,z3,z4,z9,z6]),(0,[z1,z168,z37,z4,z9,z6])]],
   [[(0,[z7,z1,z3,z417,z9,z6]),(0,[z1,z2,z317,z4,z216,z6])],[(0,[z92,z2,z158,z4,z9,z125]),(0,[z22,z1,z2,z3,z6,z426]),(0,[z1,z2,z329,z37,z9,z6])],[(0,[z1,z2,z756,z4,z9,z6]),(1,[z2,z3,z731,z9,z6]),(0,[z1,z2,z3,z4,z757,z6]),(0,[z1,z2,z3,z186,z9,z6]),(0,[z758,z1,z3,z4,z9,z6]),(0,[z1,z2,z3,z759,z9,z6])],[(0,[z36,z1,z2,z3,z9,z630])],[(0,[z1,z2,z3,z4,z760,z6]),(0,[z0,z1,z3,z342,z9,z6]),(0,[z1,z2,z37,z79,z9,z6]),(0,[z1,z2,z3,z761,z9,z6])],[(0,[z1,z2,z3,z4,z762,z6]),(0,[z1,z2,z3,z6,z193,z426]),(0,[z1,z82,z3,z9,z88,z6])],[(0,[z109,z2,z3,z731,z9,z6]),(0,[z159,z2,z3,z178,z9,z6]),(0,[z0,z1,z600,z4,z9,z6]),(0,[z1,z263,z3,z54,z9,z6]),(0,[z763,z1,z329,z3,z9,z6]),(0,[z1,z2,z4,z764,z9,z6])],[(0,[z1,z241,z3,z4,z9,z6]),(0,[z244,z2,z3,z436,z28,z6]),(0,[z1,z2,z346,z9,z88,z6]),(0,[z1,z185,z3,z4,z9,z765]),(0,[z1,z2,z766,z3,z9,z6])]],
   [[(0,[z1,z2,z767,z4,z9,z6]),(0,[z1,z2,z3,z768,z9,z6]),(0,[z1,z2,z3,z4,z9,z769]),(0,[z397,z1,z2,z4,z9,z124]),(0,[z36,z279,z2,z3,z9,z108])],[(0,[z1,z2,z3,z770,z9,z6]),(0,[z169,z2,z3,z178,z9,z6])],[(0,[z1,z168,z3,z4,z9,z6]),(0,[z1,z2,z329,z3,z9,z6]),(0,[z1,z2,z324,z79,z9,z6]),(0,[z32,z2,z37,z4,z9,z6])],[(0,[z1,z2,z3,z130,z340,z6]),(0,[z2,z3,z4,z9,z711,z6]),(0,[z333,z1,z3,z4,z9,z120]),(0,[z1,z2,z3,z771,z9,z6])],[(0,[z1,z2,z3,z178,z5,z6]),(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z773,z3,z4,z9,z6])],[(0,[z1,z168,z317,z4,z9,z6]),(0,[z1,z2,z3,z283,z9,z774])],[(0,[z1,z2,z3,z67,z9,z6]),(0,[z1,z3,z4,z775,z9,z6]),(0,[z565,z2,z3,z4,z28,z6]),(0,[z1,z53,z3,z713,z9,z6]),(0,[z34,z1,z2,z4,z776,z6])],[(0,[z1,z2,z777,z3,z9,z6]),(0,[z1,z2,z3,z778,z9,z6]),(0,[z1,z2,z57,z3,z340,z6])]],
   [[(0,[z514,z105,z3,z4,z9,z6]),(0,[z92,z49,z2,z3,z4,z125]),(0,[z1,z207,z3,z54,z9,z6]),(0,[z1,z2,z4,z9,z6,z779]),(0,[z1,z2,z766,z79,z9,z6])],[(0,[z1,z2,z3,z780,z9,z6]),(0,[z1,z2,z781,z4,z9,z6]),(0,[z1,z2,z3,z4,z6,z782]),(0,[z1,z2,z3,z4,z783,z6]),(0,[z1,z2,z784,z4,z9,z6])],[(0,[z49,z22,z1,z2,z3,z6]),(0,[z1,z2,z218,z4,z9,z6]),(0,[z1,z2,z3,z785,z9,z6]),(0,[z1,z2,z3,z786,z9,z6]),(0,[z787,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z774])],[(0,[z129,z1,z82,z3,z9,z6]),(0,[z1,z329,z788,z3,z9,z6]),(0,[z173,z1,z2,z3,z100,z43])],[(0,[z22,z1,z2,z3,z9,z6]),(0,[z159,z2,z3,z4,z9,z39]),(0,[z0,z1,z4,z140,z9,z6])],[(0,[z1,z2,z3,z9,z6,z789]),(0,[z32,z2,z3,z4,z9,z6]),(0,[z1,z790,z3,z4,z9,z6]),(0,[z1,z2,z3,z319,z177,z6]),(0,[z1,z2,z3,z4,z9,z791]),(0,[z1,z275,z3,z792,z9,z6])],[(1,[z1,z3,z713,z9,z6]),(0,[z1,z2,z137,z3,z9,z6])],[(0,[z1,z2,z4,z793,z9,z6]),(0,[z169,z2,z3,z4,z9,z39]),(0,[z794,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z44,z9,z6]),(0,[z795,z2,z3,z4,z9,z6])]],
   [[(0,[z49,z1,z2,z3,z4,z6]),(0,[z1,z3,z713,z54,z9,z6]),(0,[z1,z2,z3,z4,z50,z6]),(0,[z32,z2,z317,z4,z9,z6])],[(0,[z1,z2,z3,z796,z9,z6]),(0,[z797,z2,z3,z4,z9,z6]),(0,[z128,z129,z2,z3,z130,z6]),(0,[z32,z2,z3,z9,z6,z108])],[(0,[z1,z2,z3,z798,z9,z6]),(0,[z1,z2,z3,z4,z5,z39]),(0,[z1,z3,z4,z9,z765,z120]),(0,[z129,z1,z2,z3,z799,z6])],[(0,[z800,z1,z2,z3,z4,z9]),(0,[z19,z2,z3,z319,z9,z6]),(0,[z150,z1,z3,z54,z9,z6]),(0,[z1,z2,z269,z248,z270,z6]),(0,[z36,z1,z2,z3,z9,z239])],[(0,[z1,z2,z3,z801,z9,z6]),(0,[z92,z93,z3,z4,z9,z125]),(0,[z1,z2,z3,z9,z6,z802])],[],[(0,[z38,z2,z3,z4,z567,z6]),(0,[z803,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z804,z6])],[(0,[z1,z2,z3,z4,z9,z765]),(0,[z26,z2,z3,z4,z135,z6])]],
   [[(0,[z38,z2,z3,z4,z682,z6]),(0,[z0,z1,z99,z178,z9,z6]),(0,[z1,z805,z3,z4,z9,z6])],[(0,[z2,z3,z20,z647,z9,z6]),(0,[z62,z32,z2,z3,z9,z6]),(0,[z22,z2,z3,z20,z9,z6]),(0,[z1,z93,z158,z4,z9,z6]),(0,[z1,z2,z3,z214,z9,z88])],[(0,[z1,z2,z3,z4,z97,z6]),(0,[z1,z2,z806,z4,z9,z6]),(0,[z1,z2,z3,z807,z9,z6]),(0,[z7,z1,z3,z419,z9,z6]),(0,[z1,z2,z190,z79,z9,z6])],[(0,[z1,z2,z3,z808,z9,z6]),(0,[z129,z1,z2,z3,z382,z6]),(0,[z1,z2,z218,z809,z9,z6]),(0,[z810,z2,z3,z4,z9,z6]),(0,[z142,z2,z3,z79,z9,z6])],[(0,[z2,z709,z174,z4,z9,z6]),(0,[z1,z2,z3,z319,z163,z6]),(0,[z150,z1,z3,z8,z9,z6]),(1,[z1,z2,z3,z4,z811]),(0,[z812,z2,z3,z4,z9,z6])],[(0,[z194,z813,z3,z4,z9,z6]),(0,[z1,z2,z814,z3,z9,z6]),(0,[z1,z93,z3,z111,z9,z6]),(0,[z1,z218,z4,z60,z9,z6]),(0,[z1,z815,z2,z3,z9,z6])],[(0,[z1,z2,z3,z4,z9,z816]),(0,[z1,z2,z3,z817,z9,z6]),(0,[z1,z2,z3,z79,z216,z6])],[(0,[z818,z1,z2,z3,z9,z6]),(0,[z1,z2,z819,z3,z9,z6])]],
   [[(0,[z26,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z4,z9,z820]),(0,[z1,z103,z3,z342,z9,z6]),(0,[z1,z2,z701,z79,z9,z6]),(1,[z1,z2,z4,z776,z6])],[(0,[z1,z2,z3,z4,z9,z821]),(0,[z1,z2,z3,z822,z9,z6]),(0,[z1,z2,z3,z4,z823,z6]),(0,[z38,z2,z3,z4,z679,z6]),(0,[z1,z824,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z774,z108])],[(0,[z1,z2,z3,z4,z825,z6]),(0,[z159,z2,z3,z4,z139,z6]),(0,[z0,z1,z666,z4,z9,z6]),(0,[z1,z2,z826,z4,z9,z6]),(0,[z129,z1,z2,z3,z130,z6])],[(0,[z1,z2,z3,z827,z9,z6]),(0,[z1,z2,z3,z828,z9,z6])],[],[(0,[z1,z2,z3,z4,z829,z6]),(0,[z169,z2,z3,z4,z139,z6]),(0,[z0,z1,z446,z4,z9,z6]),(0,[z129,z1,z2,z346,z9,z6]),(0,[z1,z2,z830,z4,z9,z6]),(0,[z1,z831,z3,z4,z9,z6]),(0,[z173,z1,z2,z3,z4,z43])],[(0,[z1,z2,z3,z4,z9,z832]),(0,[z1,z2,z3,z157,z9,z6]),(0,[z92,z2,z3,z4,z9,z125]),(0,[z0,z1,z99,z4,z9,z39]),(0,[z1,z82,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z9,z296]),(0,[z1,z2,z833,z4,z9,z6])],[(0,[z1,z2,z3,z4,z834,z6]),(0,[z1,z2,z3,z9,z88,z51]),(0,[z835,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z836,z9,z6])],[(0,[z1,z3,z837,z4,z9,z6]),(0,[z1,z2,z3,z838,z9,z6]),(1,[z1,z2,z4,z9,z839])],[(0,[z1,z2,z840,z4,z9,z6]),(0,[z85,z1,z2,z766,z9,z6]),(0,[z1,z841,z3,z4,z9,z6]),(0,[z279,z2,z3,z4,z216,z6]),(0,[z1,z2,z3,z4,z147,z135])],[(0,[z159,z2,z3,z4,z9,z6]),(0,[z1,z2,z158,z4,z9,z6]),(0,[z1,z2,z3,z4,z842,z6]),(0,[z1,z2,z3,z843,z9,z6])],[(0,[z2,z3,z319,z9,z6,z125]),(0,[z844,z2,z3,z4,z9,z6]),(0,[z279,z172,z3,z4,z9,z6])],[(0,[z1,z2,z3,z845,z9,z6])],[(0,[z169,z2,z3,z4,z9,z6]),(0,[z295,z2,z3,z20,z9,z6]),(0,[z109,z2,z3,z4,z97,z6]),(0,[z1,z2,z3,z4,z846,z6])],[(0,[z1,z2,z3,z847,z9,z6]),(0,[z1,z2,z3,z9,z6,z848]),(0,[z1,z2,z3,z4,z799,z6])]],
   [[(0,[z1,z849,z3,z4,z9,z6]),(0,[z1,z2,z850,z4,z9,z6]),(0,[z1,z2,z851,z3,z9,z6]),(0,[z852,z1,z2,z4,z9,z6])],[(0,[z1,z2,z3,z4,z853,z6]),(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z168,z3,z54,z9,z6]),(0,[z345,z1,z3,z4,z60,z6]),(0,[z854,z2,z3,z4,z9,z6])],[(0,[z1,z185,z3,z4,z9,z119]),(0,[z855,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z856,z6]),(0,[z1,z2,z3,z9,z6,z193]),(0,[z1,z102,z2,z248,z9,z6])],[(0,[z1,z813,z3,z4,z9,z6]),(0,[z1,z857,z3,z4,z9,z6]),(0,[z2,z3,z4,z9,z192,z278])],[(0,[z813,z105,z3,z4,z9,z6]),(0,[z1,z3,z4,z54,z9,z39]),(0,[z0,z1,z99,z4,z9,z322]),(0,[z345,z1,z3,z4,z858,z6]),(0,[z1,z269,z4,z454,z270,z6])],[(0,[z859,z1,z2,z3,z9,z6]),(0,[z1,z2,z3,z9,z6,z860]),(0,[z32,z2,z3,z79,z9,z6])],[(0,[z1,z2,z3,z4,z861,z6]),(0,[z279,z168,z3,z4,z9,z6]),(0,[z1,z2,z3,z283,z9,z88])]],
   [[(0,[z1,z2,z3,z111,z163,z6])],[(0,[z1,z2,z3,z4,z862,z6]),(0,[z1,z2,z3,z4,z6,z863]),(0,[z109,z32,z2,z3,z9,z6]),(0,[z367,z38,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z9,z39]),(0,[z1,z2,z3,z4,z864,z6]),(0,[z34,z1,z2,z4,z112,z6]),(0,[z1,z865,z3,z4,z9,z6])],[(0,[z1,z168,z3,z8,z9,z6]),(0,[z1,z2,z3,z232,z9,z6])],[(0,[z150,z1,z3,z419,z9,z6]),(0,[z150,z1,z4,z79,z9,z6])],[(0,[z0,z1,z99,z4,z139,z6]),(0,[z32,z2,z3,z54,z9,z6])],[(0,[z160,z2,z123,z4,z9,z6]),(0,[z1,z2,z866,z4,z9,z6]),(0,[z1,z2,z3,z867,z9,z6]),(0,[z1,z2,z3,z868,z9,z6]),(0,[z1,z172,z317,z4,z9,z6])],[(0,[z1,z2,z869,z4,z9,z6]),(0,[z1,z870,z3,z4,z9,z6]),(0,[z180,z2,z3,z20,z9,z6]),(0,[z871,z2,z3,z4,z9,z6]),(0,[z7,z1,z3,z8,z9,z6])],[(0,[z1,z2,z3,z4,z9,z872]),(0,[z38,z2,z3,z4,z604,z6]),(0,[z1,z93,z286,z4,z9,z6]),(0,[z85,z1,z2,z4,z9,z39]),(0,[z873,z2,z3,z4,z9,z6]),(0,[z2,z3,z4,z9,z6,z874])]],
   [[(0,[z1,z2,z3,z9,z6,z875])],[(0,[z237,z2,z123,z4,z9,z6]),(0,[z1,z11,z3,z4,z95,z6]),(0,[z472,z1,z3,z4,z9,z120])],[(0,[z1,z876,z3,z4,z9,z6]),(0,[z92,z49,z2,z3,z4,z6]),(0,[z1,z837,z99,z4,z9,z6])],[(0,[z1,z2,z877,z3,z9,z6])],[(0,[z1,z2,z218,z4,z139,z6]),(0,[z878,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z248,z9,z6])],[(0,[z1,z879,z3,z4,z9,z6]),(0,[z0,z1,z99,z4,z9,z6]),(0,[z1,z2,z3,z419,z5,z6]),(0,[z32,z2,z3,z8,z9,z6]),(0,[z279,z2,z3,z4,z50,z6])],[],[(0,[z38,z2,z3,z20,z130,z6]),(0,[z1,z880,z3,z4,z9,z6]),(0,[z1,z2,z837,z4,z9,z6])]],
   [[(0,[z881,z2,z3,z4,z9,z6]),(0,[z1,z2,z37,z4,z50,z6]),(0,[z26,z2,z3,z44,z9,z6])],[(0,[z1,z3,z4,z9,z6,z882]),(0,[z1,z2,z3,z883,z9,z6]),(0,[z1,z275,z3,z4,z95,z6])],[(0,[z2,z3,z731,z4,z9,z6]),(1,[z1,z2,z3,z799,z6]),(0,[z142,z2,z3,z130,z9,z6]),(0,[z129,z142,z2,z3,z130,z6])],[(0,[z2,z3,z4,z9,z6,z42]),(0,[z1,z241,z3,z4,z163,z6]),(0,[z1,z11,z3,z4,z858,z6])],[(0,[z1,z2,z3,z652,z130,z6]),(0,[z32,z2,z3,z87,z9,z6])],[(0,[z1,z2,z3,z195,z9,z6]),(0,[z38,z2,z3,z323,z9,z6]),(0,[z884,z2,z3,z4,z9,z6]),(0,[z1,z2,z218,z4,z112,z6]),(0,[z1,z2,z3,z9,z88,z209])],[(0,[z1,z2,z3,z4,z6,z885]),(0,[z1,z886,z3,z4,z9,z6]),(0,[z109,z49,z2,z3,z4,z6]),(0,[z422,z1,z3,z8,z9,z6]),(0,[z1,z11,z4,z379,z95,z6]),(0,[z142,z2,z57,z3,z9,z6]),(0,[z1,z887,z3,z4,z9,z6]),(0,[z888,z1,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z889]),(0,[z1,z2,z3,z178,z9,z39]),(0,[z1,z275,z3,z4,z60,z6])]],
   [[(0,[z1,z890,z2,z3,z4,z6]),(0,[z1,z891,z3,z4,z9,z6]),(0,[z1,z2,z3,z892,z9,z6]),(0,[z1,z893,z3,z4,z9,z6])],[(0,[z1,z2,z286,z4,z9,z6]),(0,[z894,z1,z3,z4,z9,z6]),(0,[z1,z2,z57,z3,z216,z6]),(0,[z1,z2,z3,z130,z6,z230]),(0,[z1,z172,z3,z4,z216,z6])],[(0,[z109,z2,z3,z311,z9,z6])],[(0,[z895,z1,z2,z4,z9,z6]),(0,[z1,z2,z3,z896,z9,z6]),(0,[z1,z2,z4,z776,z270,z6])],[(0,[z38,z2,z3,z4,z29,z6]),(0,[z1,z2,z897,z4,z9,z6]),(0,[z1,z2,z3,z898,z9,z6]),(0,[z1,z2,z3,z899,z9,z6]),(0,[z2,z3,z4,z9,z6,z900]),(0,[z763,z1,z3,z4,z9,z6])],[(0,[z1,z2,z901,z4,z9,z6]),(0,[z1,z2,z902,z4,z9,z6]),(0,[z1,z41,z3,z54,z9,z6]),(0,[z1,z3,z4,z9,z119,z765])],[(0,[z154,z1,z3,z4,z9,z120]),(0,[z1,z2,z317,z4,z50,z6])],[(0,[z1,z2,z903,z4,z9,z6]),(0,[z1,z2,z3,z4,z904,z6]),(0,[z905,z1,z3,z4,z9,z6]),(0,[z1,z275,z269,z4,z270,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z906,z6]),(0,[z1,z907,z3,z4,z9,z6]),(0,[z1,z2,z709,z4,z9,z6]),(0,[z1,z2,z3,z4,z908,z6]),(0,[z909,z1,z2,z3,z9,z6]),(0,[z173,z26,z2,z3,z4,z43])],[(0,[z0,z1,z99,z419,z9,z6]),(0,[z1,z3,z4,z60,z371,z6]),(0,[z1,z2,z3,z9,z6,z100])],[(0,[z36,z1,z2,z3,z9,z774])],[(0,[z1,z2,z3,z4,z9,z910]),(0,[z911,z2,z3,z4,z9,z6])],[(0,[z109,z2,z3,z9,z6,z276]),(0,[z1,z3,z4,z454,z9,z6]),(0,[z1,z2,z912,z3,z9,z6]),(0,[z1,z168,z3,z4,z216,z6]),(0,[z1,z2,z3,z4,z6,z811])],[(0,[z1,z2,z3,z913,z4,z6]),(0,[z1,z2,z3,z323,z9,z6]),(0,[z1,z3,z4,z9,z6,z765])],[(0,[z914,z1,z2,z4,z9,z6]),(0,[z159,z2,z3,z4,z9,z322]),(0,[z1,z2,z3,z178,z9,z322]),(0,[z166,z1,z3,z4,z9,z765]),(0,[z36,z1,z168,z3,z9,z108]),(0,[z915,z1,z2,z3,z4,z6])],[(0,[z592,z2,z3,z110,z9,z6]),(0,[z916,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z917,z6])]],
   [[(0,[z1,z2,z918,z4,z9,z6]),(0,[z919,z1,z2,z3,z9,z6]),(0,[z1,z2,z158,z319,z9,z6]),(0,[z1,z2,z3,z920,z9,z6]),(0,[z1,z2,z57,z766,z9,z6])],[(0,[z2,z813,z3,z4,z9,z6]),(0,[z2,z3,z4,z28,z6,z520]),(0,[z169,z2,z3,z4,z9,z322]),(0,[z0,z1,z54,z79,z9,z6]),(0,[z1,z921,z3,z4,z9,z6]),(0,[z922,z2,z3,z4,z9,z6])],[(0,[z12,z105,z3,z4,z9,z6]),(0,[z2,z3,z731,z20,z9,z6]),(0,[z2,z3,z110,z731,z9,z6]),(0,[z1,z923,z3,z4,z9,z6])],[(0,[z1,z172,z3,z79,z9,z6])],[(0,[z1,z2,z3,z4,z5,z322]),(0,[z1,z2,z3,z4,z924,z6])],[(0,[z1,z2,z3,z4,z925,z6]),(0,[z109,z2,z3,z110,z97,z6]),(0,[z1,z2,z3,z178,z139,z6]),(0,[z1,z2,z4,z379,z9,z6]),(0,[z1,z185,z3,z4,z9,z98]),(0,[z926,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z811,z43])],[(0,[z1,z2,z927,z4,z9,z6]),(0,[z1,z2,z3,z928,z9,z6]),(0,[z1,z2,z3,z4,z858,z6]),(1,[z1,z3,z4,z9,z765]),(0,[z1,z527,z3,z4,z9,z119]),(0,[z1,z929,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z811])],[(0,[z236,z1,z2,z4,z9,z124]),(0,[z1,z185,z3,z417,z9,z119]),(0,[z32,z2,z3,z4,z216,z6]),(0,[z173,z1,z2,z3,z4,z811])]],
   [[(0,[z66,z2,z174,z67,z9,z6]),(0,[z1,z2,z3,z4,z9,z930]),(0,[z1,z2,z3,z4,z340,z6]),(0,[z608,z1,z2,z3,z9,z108]),(0,[z1,z2,z3,z931,z4,z6]),(0,[z1,z2,z158,z4,z177,z6]),(0,[z1,z2,z3,z4,z776,z6]),(1,[z1,z2,z3,z9,z774])],[(0,[z1,z2,z932,z4,z9,z6]),(0,[z1,z2,z3,z436,z130,z6]),(0,[z92,z22,z2,z3,z9,z125]),(0,[z1,z2,z3,z4,z9,z717]),(0,[z1,z2,z3,z809,z9,z6]),(0,[z85,z1,z57,z82,z9,z6]),(0,[z32,z172,z3,z4,z9,z6]),(0,[z1,z2,z3,z44,z216,z6])],[(0,[z1,z2,z4,z9,z6,z933]),(0,[z1,z2,z3,z4,z934,z6]),(0,[z2,z3,z319,z28,z9,z6]),(0,[z1,z2,z269,z4,z270,z6]),(0,[z935,z2,z3,z4,z9,z6])],[(0,[z1,z2,z346,z4,z9,z6]),(0,[z936,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z937,z9,z6])],[(0,[z1,z2,z3,z4,z938,z6]),(0,[z1,z2,z3,z4,z939,z6]),(0,[z1,z2,z3,z111,z177,z6]),(0,[z92,z2,z3,z4,z426,z125]),(0,[z166,z1,z3,z4,z9,z120]),(0,[z1,z2,z4,z9,z70,z839]),(0,[z36,z1,z172,z3,z9,z108])],[(0,[z194,z105,z3,z195,z9,z6]),(0,[z1,z2,z3,z940,z9,z6]),(0,[z1,z698,z3,z54,z9,z6]),(0,[z7,z1,z3,z713,z9,z6]),(0,[z36,z1,z2,z37,z9,z108])],[(0,[z595,z2,z3,z110,z9,z6]),(0,[z1,z2,z3,z178,z9,z6]),(0,[z1,z2,z329,z69,z9,z70]),(0,[z1,z2,z3,z87,z799,z6])],[]],
   [[(0,[z19,z2,z3,z4,z9,z392]),(0,[z0,z159,z99,z4,z9,z6])],[(0,[z1,z2,z3,z4,z941,z6]),(0,[z92,z2,z3,z4,z9,z632]),(0,[z92,z2,z3,z4,z9,z717]),(0,[z0,z1,z4,z260,z9,z6]),(0,[z1,z942,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z839])],[(0,[z1,z2,z3,z436,z58,z6]),(0,[z92,z2,z3,z4,z163,z125]),(1,[z1,z3,z4,z858,z6]),(0,[z36,z1,z2,z317,z9,z108])],[(0,[z1,z2,z3,z4,z139,z39]),(0,[z1,z2,z3,z486,z58,z6])],[(0,[z38,z2,z3,z4,z21,z6]),(0,[z1,z2,z943,z3,z9,z6]),(0,[z32,z168,z3,z4,z9,z6])],[(0,[z1,z2,z3,z9,z6,z944])],[(0,[z1,z2,z3,z945,z9,z6]),(0,[z36,z1,z2,z3,z9,z483]),(0,[z1,z2,z3,z4,z946,z6]),(0,[z38,z2,z3,z4,z711,z6]),(0,[z2,z3,z323,z28,z9,z6]),(0,[z1,z2,z3,z947,z9,z6]),(0,[z1,z2,z948,z3,z9,z6]),(0,[z949,z2,z3,z4,z9,z6]),(0,[z36,z1,z2,z3,z9,z108])],[(0,[z49,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z950,z6]),(0,[z1,z241,z3,z319,z9,z6]),(0,[z1,z2,z158,z4,z163,z6]),(0,[z1,z11,z3,z4,z139,z6]),(0,[z1,z168,z3,z4,z50,z6])]],
   [[(0,[z194,z105,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z951])],[(0,[z1,z2,z3,z4,z9,z952])],[(0,[z489,z2,z174,z4,z9,z6]),(0,[z563,z1,z2,z4,z9,z124])],[(0,[z237,z2,z709,z4,z9,z6])],[(0,[z1,z2,z3,z953,z9,z6]),(0,[z507,z1,z2,z57,z9,z6]),(0,[z38,z2,z3,z319,z9,z6]),(0,[z1,z2,z3,z954,z9,z6])],[(0,[z1,z2,z3,z4,z955,z6])],[(0,[z66,z2,z709,z4,z9,z6]),(0,[z1,z2,z956,z4,z9,z6]),(0,[z1,z241,z3,z4,z177,z6]),(0,[z401,z1,z2,z4,z9,z6]),(0,[z1,z275,z3,z4,z139,z6])]],
   [[(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z2,z3,z958,z9,z6])],[(0,[z1,z82,z3,z20,z9,z6]),(0,[z959,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z960,z9,z6]),(0,[z1,z2,z3,z436,z9,z6]),(0,[z159,z2,z3,z419,z9,z6]),(0,[z1,z3,z419,z54,z9,z6]),(0,[z32,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z961,z9,z6])],[(0,[z962,z1,z2,z3,z4,z6]),(0,[z1,z2,z346,z20,z9,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z150,z85,z1,z4,z9,z6]),(0,[z1,z2,z3,z9,z6,z774])],[(0,[z1,z2,z3,z4,z9,z964])],[(0,[z1,z2,z3,z965,z9,z6]),(0,[z169,z2,z3,z419,z9,z6]),(0,[z1,z2,z3,z4,z966,z6]),(0,[z1,z2,z3,z967,z9,z6]),(0,[z1,z2,z3,z968,z9,z6])],[(0,[z237,z2,z200,z4,z9,z6]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z286,z319,z9,z6]),(0,[z1,z2,z3,z4,z969,z6]),(0,[z1,z2,z3,z970,z9,z6]),(0,[z1,z2,z3,z971,z9,z6]),(0,[z972,z2,z3,z4,z9,z6])],[(0,[z1,z973,z3,z4,z9,z6]),(0,[z1,z2,z3,z974,z9,z6]),(0,[z1,z2,z3,z975,z9,z6]),(0,[z1,z2,z3,z87,z58,z6])]],
   [[(0,[z66,z2,z174,z157,z9,z6]),(0,[z1,z2,z3,z4,z6,z426]),(0,[z1,z275,z3,z4,z9,z6]),(0,[z976,z2,z3,z4,z9,z6])],[(0,[z1,z93,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z6,z977])],[(0,[z1,z978,z3,z4,z9,z6]),(0,[z1,z2,z979,z4,z9,z6])],[(0,[z1,z2,z3,z980,z9,z6]),(0,[z22,z32,z2,z3,z9,z6]),(0,[z1,z2,z3,z4,z9,z322]),(0,[z0,z1,z837,z4,z9,z6])],[(0,[z1,z2,z3,z981,z9,z6]),(0,[z7,z1,z8,z346,z9,z6]),(0,[z173,z2,z3,z4,z42,z43])],[(0,[z609,z2,z174,z4,z9,z6]),(0,[z1,z2,z3,z982,z9,z6]),(0,[z2,z3,z20,z9,z6,z483]),(0,[z1,z2,z983,z4,z9,z6]),(0,[z1,z2,z3,z984,z4,z6]),(0,[z1,z2,z3,z417,z9,z6]),(0,[z1,z2,z274,z4,z9,z70])],[(0,[z1,z2,z3,z985,z9,z6]),(0,[z1,z2,z286,z4,z177,z6]),(0,[z1,z2,z4,z9,z839,z124])],[(0,[z1,z2,z3,z986,z9,z6]),(0,[z987,z1,z2,z4,z9,z6]),(0,[z988,z2,z3,z4,z9,z6]),(0,[z2,z3,z4,z9,z6,z989])]],
   [[(0,[z1,z2,z3,z990,z9,z6]),(0,[z1,z2,z3,z4,z991,z6]),(0,[z1,z2,z3,z419,z9,z39]),(0,[z1,z2,z4,z79,z9,z39]),(0,[z1,z2,z37,z4,z9,z6]),(0,[z1,z2,z3,z130,z216,z6])],[(0,[z1,z2,z3,z992,z9,z6]),(0,[z1,z2,z3,z79,z340,z6]),(0,[z1,z2,z993,z3,z9,z6]),(0,[z1,z2,z3,z994,z9,z6]),(0,[z1,z3,z4,z60,z858,z6]),(0,[z1,z2,z57,z646,z9,z6])],[(0,[z1,z2,z3,z436,z340,z6]),(0,[z1,z2,z3,z4,z139,z6]),(0,[z36,z1,z2,z346,z9,z6]),(0,[z1,z995,z3,z4,z9,z6]),(0,[z26,z2,z3,z9,z6,z100])],[(0,[z1,z2,z3,z996,z9,z6]),(0,[z1,z185,z3,z4,z9,z181]),(0,[z1,z2,z997,z3,z4,z6]),(0,[z1,z2,z3,z4,z135,z437]),(0,[z1,z241,z3,z111,z9,z6]),(0,[z1,z2,z998,z4,z9,z6]),(0,[z1,z2,z766,z86,z9,z6]),(0,[z999,z2,z3,z4,z9,z6]),(0,[z1000,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z1001,z9,z6]),(0,[z38,z2,z3,z4,z163,z6]),(0,[z49,z2,z3,z4,z192,z6])],[(0,[z1,z2,z3,z4,z1002,z6]),(0,[z1003,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z1004,z9,z6]),(0,[z1,z172,z57,z3,z9,z6]),(0,[z1,z2,z3,z1005,z9,z6])],[(0,[z1,z2,z3,z4,z1006,z6]),(0,[z1,z672,z3,z54,z9,z6]),(0,[z1,z2,z3,z54,z340,z6]),(0,[z203,z1,z2,z3,z130,z6])]],
   [[(0,[z608,z2,z3,z4,z9,z125]),(0,[z1,z3,z4,z858,z9,z6])],[(0,[z1,z2,z1007,z4,z9,z6]),(0,[z542,z2,z3,z20,z9,z6]),(0,[z2,z3,z4,z9,z6,z717]),(0,[z1,z82,z3,z9,z58,z6])],[(0,[z1,z2,z3,z1008,z9,z6])],[(0,[z1,z2,z346,z9,z58,z6])],[(0,[z1,z634,z3,z54,z9,z6]),(0,[z1,z3,z4,z858,z95,z6]),(0,[z1,z2,z766,z4,z9,z6]),(0,[z1,z3,z4,z1009,z9,z6])],[(0,[z1,z1010,z3,z4,z9,z6]),(0,[z1,z2,z286,z4,z163,z6])],[(0,[z92,z2,z3,z319,z9,z125]),(0,[z1,z2,z317,z4,z9,z6]),(0,[z1,z2,z3,z9,z88,z774])],[(0,[z1,z2,z3,z1011,z9,z6]),(0,[z1,z2,z3,z9,z6,z1012])]],
   [[(0,[z1,z2,z3,z1013,z9,z6]),(0,[z1,z2,z3,z8,z340,z6]),(0,[z1,z82,z3,z110,z9,z6]),(0,[z1,z1014,z3,z4,z9,z6]),(0,[z1,z2,z3,z1015,z9,z6])],[(0,[z1,z2,z3,z1016,z9,z6]),(0,[z1,z2,z1017,z4,z9,z6]),(0,[z1,z11,z3,z342,z95,z6]),(0,[z1,z2,z1018,z4,z9,z6])],[(0,[z1,z2,z346,z110,z9,z6]),(0,[z244,z2,z3,z4,z564,z6]),(0,[z1019,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z1020,z9,z6])],[(0,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z522,z79,z9,z6]),(0,[z1,z2,z3,z799,z58,z6]),(0,[z1021,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z1022,z6]),(0,[z529,z2,z3,z110,z9,z6]),(0,[z1,z1023,z3,z4,z9,z6]),(0,[z249,z1,z2,z4,z9,z839]),(0,[z1,z2,z3,z4,z6,z1024])],[(0,[z92,z2,z3,z4,z177,z125]),(0,[z1,z2,z3,z419,z139,z6]),(0,[z1025,z1,z2,z3,z4,z6]),(0,[z249,z1,z2,z4,z9,z124])],[(0,[z62,z2,z3,z20,z9,z6]),(0,[z1,z2,z3,z87,z340,z6]),(0,[z1,z3,z4,z9,z6,z1026])]],
   [[(0,[z1,z2,z3,z1027,z9,z6]),(0,[z129,z1,z2,z3,z189,z6]),(0,[z32,z2,z3,z130,z9,z6])],[(0,[z1,z2,z3,z4,z135,z811])],[(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z3,z9,z6,z1029]),(0,[z1,z3,z4,z9,z6,z1030]),(0,[z116,z1,z2,z3,z4,z43])],[(0,[z1,z2,z1031,z4,z9,z6]),(1,[z2,z709,z4,z9,z6]),(0,[z1,z2,z1032,z4,z9,z6]),(0,[z1,z2,z3,z1033,z9,z6]),(0,[z1,z2,z3,z1034,z9,z6]),(0,[z2,z3,z4,z9,z6,z1035])],[(0,[z1,z2,z3,z1036,z9,z6]),(0,[z1,z1037,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z6,z1038]),(0,[z1039,z1,z2,z3,z4,z6]),(0,[z19,z2,z3,z4,z9,z717]),(0,[z7,z401,z1,z4,z9,z6]),(0,[z1,z2,z3,z1040,z9,z6]),(0,[z32,z2,z57,z3,z9,z6])],[(0,[z173,z1,z2,z3,z4,z632]),(0,[z1,z2,z4,z112,z495,z6]),(0,[z1,z2,z269,z4,z776,z6])],[(0,[z1,z2,z3,z4,z9,z1041]),(0,[z104,z316,z3,z4,z9,z6]),(0,[z1,z2,z297,z79,z9,z6]),(0,[z1042,z1,z3,z4,z9,z6])],[(0,[z1,z2,z1043,z4,z9,z6]),(0,[z1,z2,z1044,z4,z9,z6]),(0,[z142,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z419,z9,z6]),(0,[z1,z172,z3,z4,z50,z6])]],
   [[(0,[z1,z2,z4,z112,z776,z6])],[(0,[z1,z2,z3,z4,z9,z1045]),(0,[z367,z1,z2,z3,z4,z43]),(0,[z1,z2,z69,z4,z9,z428])],[(0,[z1,z2,z3,z1046,z9,z6]),(0,[z1,z1047,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z6,z1048]),(0,[z1,z2,z137,z269,z270,z6]),(0,[z1049,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z216,z6]),(0,[z1,z3,z4,z1050,z9,z6])],[(0,[z109,z2,z3,z110,z340,z6]),(0,[z1051,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z1052,z9,z6]),(0,[z1053,z1,z2,z4,z9,z6]),(0,[z1,z2,z3,z44,z130,z6]),(0,[z1,z2,z3,z4,z147,z811])],[(0,[z1054,z1,z2,z3,z9,z6]),(0,[z1,z2,z3,z1055,z9,z6]),(0,[z1,z2,z3,z799,z9,z6])],[(0,[z1,z241,z286,z4,z9,z6]),(0,[z85,z1,z2,z419,z9,z6])],[(0,[z1056,z1,z2,z3,z9,z6]),(0,[z2,z3,z4,z711,z29,z6])],[(0,[z1,z2,z3,z1057,z9,z6]),(0,[z1,z2,z3,z4,z9,z1058]),(0,[z1,z2,z1059,z4,z9,z6]),(0,[z1,z2,z3,z1060,z9,z6]),(0,[z1,z788,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z1061,z9,z6]),(0,[z1,z2,z3,z342,z9,z6])],[(0,[z259,z1,z2,z3,z130,z6]),(0,[z0,z1,z445,z4,z9,z6])],[(0,[z66,z2,z174,z4,z9,z6]),(0,[z1,z1062,z3,z4,z9,z6]),(0,[z2,z3,z4,z28,z711,z6]),(0,[z92,z2,z3,z111,z9,z125]),(0,[z1,z3,z417,z54,z9,z6]),(0,[z1063,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z1064,z9,z6]),(0,[z479,z2,z3,z20,z9,z6]),(0,[z1065,z2,z3,z4,z9,z6]),(0,[z36,z1,z82,z3,z9,z6]),(0,[z26,z2,z3,z4,z130,z6])],[(0,[z109,z2,z3,z652,z9,z6]),(0,[z244,z2,z3,z4,z6,z638]),(1,[z2,z3,z4,z9,z717]),(0,[z1,z1066,z2,z3,z9,z6]),(0,[z1,z2,z86,z79,z9,z6]),(0,[z1,z2,z69,z4,z9,z839]),(0,[z1,z2,z3,z44,z58,z6])],[(0,[z1,z2,z1067,z4,z9,z6]),(0,[z1,z3,z4,z60,z139,z6])],[(0,[z1,z2,z1068,z4,z9,z6]),(0,[z1,z93,z3,z319,z9,z6]),(0,[z85,z1,z2,z57,z9,z6]),(0,[z2,z3,z44,z9,z6,z42])],[(0,[z1,z2,z3,z4,z1069,z6]),(0,[z1,z2,z158,z111,z9,z6]),(0,[z1,z2,z3,z713,z9,z6]),(0,[z1,z11,z3,z94,z95,z6])]],
   [[(0,[z1,z2,z3,z490,z9,z6])],[(0,[z1,z2,z3,z1070,z9,z6]),(0,[z1,z2,z3,z283,z9,z492]),(0,[z159,z2,z3,z4,z5,z6])],[(0,[z1071,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z9,z6,z1072]),(0,[z1,z2,z3,z4,z9,z1073]),(0,[z649,z1,z3,z4,z60,z6])],[(0,[z294,z2,z3,z20,z9,z6]),(0,[z1,z2,z3,z4,z1074,z6]),(0,[z169,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1075,z6]),(0,[z0,z231,z1,z4,z9,z6]),(0,[z26,z2,z3,z4,z58,z6])],[(0,[z1,z2,z3,z4,z9,z1076]),(0,[z1,z2,z3,z4,z1077,z6]),(0,[z1,z2,z3,z4,z139,z322]),(0,[z1,z2,z1078,z4,z9,z6]),(0,[z1,z2,z1079,z4,z9,z6]),(0,[z32,z2,z3,z283,z9,z6]),(0,[z279,z2,z37,z4,z9,z6])],[(0,[z1,z2,z1080,z4,z9,z6]),(0,[z1,z93,z3,z4,z177,z6]),(0,[z128,z2,z3,z4,z130,z6])],[(0,[z1,z2,z3,z1081,z9,z6]),(0,[z1,z2,z3,z1082,z9,z6]),(0,[z85,z1,z2,z329,z9,z6]),(0,[z1,z2,z69,z232,z9,z70])]],
   [[(0,[z1,z2,z3,z4,z1083,z6]),(0,[z1,z2,z4,z9,z6,z1084]),(0,[z1,z2,z329,z79,z9,z6])],[(0,[z1,z2,z3,z4,z1085,z6]),(0,[z1,z2,z4,z776,z9,z6])],[(0,[z1,z2,z3,z4,z1086,z6]),(0,[z1,z2,z3,z130,z799,z6])],[(0,[z1087,z2,z3,z4,z9,z6]),(0,[z1,z2,z1088,z4,z9,z6]),(0,[z688,z1,z2,z4,z112,z6]),(0,[z1,z2,z3,z1089,z9,z6])],[(0,[z1,z2,z3,z1090,z9,z6]),(0,[z1,z2,z3,z1091,z9,z6])],[(0,[z1,z2,z3,z1092,z9,z6]),(0,[z1,z2,z3,z4,z1093,z6]),(0,[z92,z241,z3,z4,z9,z125]),(0,[z49,z1,z2,z3,z6,z193]),(0,[z2,z3,z4,z9,z192,z717]),(0,[z1,z2,z317,z54,z9,z6]),(0,[z1,z2,z751,z3,z9,z6]),(0,[z1,z275,z269,z4,z9,z6]),(0,[z1094,z2,z3,z4,z9,z6])],[(0,[z1,z53,z3,z54,z9,z6]),(0,[z1,z2,z417,z830,z9,z6])],[(0,[z1,z2,z393,z79,z9,z6]),(0,[z128,z2,z3,z4,z58,z6]),(0,[z173,z26,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z1095,z4,z9,z6]),(0,[z1,z2,z3,z1096,z9,z6]),(0,[z279,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z319,z9,z6]),(0,[z1,z2,z3,z1097,z9,z6]),(0,[z1098,z2,z3,z4,z9,z6]),(0,[z1,z1099,z3,z4,z9,z6]),(0,[z1,z275,z4,z112,z9,z6]),(0,[z36,z1,z2,z3,z216,z108])],[(0,[z1,z2,z1100,z4,z9,z6])],[(0,[z1,z241,z158,z4,z9,z6]),(0,[z173,z1,z2,z3,z44,z43])],[(0,[z1,z1101,z3,z4,z9,z6]),(0,[z1,z2,z1102,z4,z9,z6]),(0,[z92,z2,z3,z9,z193,z125]),(0,[z279,z2,z317,z4,z9,z6])],[(0,[z26,z2,z3,z4,z9,z6]),(0,[z1,z1103,z3,z4,z9,z6]),(0,[z1,z185,z3,z186,z9,z119])],[(0,[z1,z2,z1104,z4,z9,z6]),(0,[z1,z2,z3,z9,z6,z1105]),(0,[z244,z2,z3,z4,z28,z6]),(0,[z1,z93,z3,z4,z163,z6]),(0,[z1,z2,z3,z1106,z9,z6]),(0,[z1,z2,z3,z1107,z9,z6]),(0,[z1,z2,z4,z9,z6,z839])],[(0,[z38,z18,z2,z3,z4,z6]),(0,[z401,z1,z2,z419,z9,z6]),(0,[z1,z2,z3,z94,z9,z6]),(0,[z1,z2,z317,z8,z9,z6])],[(0,[z1,z2,z269,z4,z139,z6]),(0,[z1,z2,z218,z4,z270,z6]),(0,[z1,z1108,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z177,z6]),(0,[z2,z3,z4,z28,z163,z6])],[(1,[z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z524,z9,z88])],[(0,[z1,z2,z3,z4,z1109,z6]),(0,[z244,z2,z3,z323,z28,z6]),(0,[z1,z2,z3,z1110,z9,z6]),(0,[z1,z2,z4,z112,z139,z6]),(0,[z1,z3,z8,z713,z9,z6])],[(0,[z2,z123,z709,z4,z9,z6]),(0,[z0,z1,z99,z4,z5,z6]),(0,[z1111,z2,z3,z4,z9,z6]),(0,[z1,z275,z3,z1033,z9,z6])],[(0,[z291,z2,z3,z20,z9,z6]),(0,[z92,z2,z286,z4,z9,z125]),(0,[z1112,z2,z3,z4,z9,z6]),(1,[z1,z2,z766,z9,z6]),(0,[z1,z1113,z3,z4,z9,z6])],[(0,[z1,z2,z419,z79,z9,z6]),(0,[z1,z2,z3,z792,z9,z6])],[(0,[z62,z2,z3,z731,z9,z6]),(0,[z142,z2,z3,z54,z9,z6])],[(0,[z128,z2,z3,z4,z9,z6]),(0,[z401,z1,z2,z57,z9,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 543) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 543).take 545) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1088)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [543, 545] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 142).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [142, 114] = true :=
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

end PEqualNP.Outside.L_meta_39243

theorem PEqualNP.Outside.L_meta_39243 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4276680840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4276680840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39243.solve