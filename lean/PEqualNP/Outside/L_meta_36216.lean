import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36216

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
  Nat.testBit (4277074664 * 2 ^ 32 + 4274845896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x34008c18d83a3188#64 ++ 0x868011831b074631#64 ++ 0xfa059c79f87a339e#64 ++ 0xff40b38f3f0f4673#64 : BitVec 256),
   (0x080822422080c233#64 ++ 0x0101044844101846#64 ++ 0xf71a6246318fc3ff#64 ++ 0xdee34c48c631f87f#64 : BitVec 256),
   (0x902380854a0c14c0#64 ++ 0x12047010a9418298#64 ++ 0xafe38387ce0c7ce5#64 ++ 0xf5fc7070f9c18f9c#64 : BitVec 256),
   (0x205c036805d06b02#64 ++ 0x240b806d00ba0d60#64 ++ 0x9ffc03f80ff07f07#64 ++ 0xb3ff807f01fe0fe0#64 : BitVec 256),
   (0xc077d4000f6f0004#64 ++ 0x380efa8001ede000#64 ++ 0x7e7ffc000fff8003#64 ++ 0x8fcfff8001fff000#64 : BitVec 256),
   (0x00ff7bf7b0000007#64 ++ 0xc01fef7ef6000000#64 ++ 0xfefffffff0000000#64 ++ 0x7fdffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff0000000 0x7fdffffffe000000

def z1 : W := mkw 0x080822422080c233 0x0101044844101846 0xf71a6246318fc3ff 0xdee34c48c631f87f

def z2 : W := mkw 0x2000000805502900 0x2400000100aa0520 0x000000000e703c00 0x0000000001ce0780

def z3 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f80ff07f07 0xb3ff807f01fe0fe0

def z4 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa059c79f87a339e 0xff40b38f3f0f4673

def z5 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xafe38387ce0c7ce5 0xf5fc7070f9c18f9c

def z6 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z7 : W := mkw 0x080000000080c230 0x0100000000101846 0x01000000018fc3ff 0x802000000031f87f

def z8 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0x9ffc03f80fffffff 0xb3ff807f01ffffff

def z9 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x08e401b80e703c00 0x211c803701ce0780

def z10 : W := mkw 0x2000000800102100 0x0400000100020420 0x0804003808703000 0x21008007010e0600

def z11 : W := mkw 0xf4ffffffff7f318f 0xfe9fffffffefe631 0xfeffffffffffb39f 0xffdffffffffff673

def z12 : W := mkw 0x1000800048081080 0x0200100009010210 0x08018001c8003000 0x2100300039000600

def z13 : W := mkw 0x0077500000000004 0x000eea0000000000 0x7e7ffc0000000000 0x0fcfff8000000000

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x05e0038006004c01 0x00bc007000c00980

def z15 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f0000000 0x7f40b38f3e000000

def z16 : W := mkw 0x0023008500000000 0x00046010a0000000 0xaee38387c0000000 0x75dc7070f8000000

def z17 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x0de38387ce047c61 0x21bc7070f9c08f8c

def z18 : W := mkw 0x1000800048081080 0x0200100009010210 0xaf038207c80c70e5 0xf5e07040f9018e1c

def z19 : W := mkw 0x0077500000000004 0x000eea0000000000 0x08659c0000000000 0x010cb38000000000

def z20 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x08e59db9c0000000 0x211cb3b738000000

def z21 : W := mkw 0x005c036000000002 0x000b806c00000000 0x9efc03f800000000 0x33df807f00000000

def z22 : W := mkw 0xc00084000f6f0000 0x3800108001ede000 0x000000000fff8003 0x8000000001fff000

def z23 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xffffff87cffffce7 0xfffffff0f9ffff9c

def z24 : W := mkw 0x005c036005c04a02 0x200b806c00b80940 0x05f8038007804c01 0x00bf007000f00980

def z25 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0xfa07fc7ff0000000 0x7f40ff8ffe000000

def z26 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x501c7c0001f38002 0x0a038f80003e7000

def z27 : W := mkw 0xb07f83ed4fdc7fc2 0x360ff07da9fb8ff8 0xbfff83ffcffc7fe7 0xf7fff07ff9ff8ffc

def z28 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff18fc3ff 0xfffffffffe31f87f

def z29 : W := mkw 0x34008408483a3188 0x0680108109074631 0x00000000087a339e 0x80000000010f4673

def z30 : W := mkw 0x00ff73e720000007 0x401fee7ce4000000 0x04fa638600000000 0x009f4c70c0000000

def z31 : W := mkw 0x080822422080c233 0x0101044844101846 0x501860403183831a 0x0a030c0806307063

def z32 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffe63fe3fffffff 0xffffcc7fc7ffffff

def z33 : W := mkw 0x982ba2c76a8cd6f3 0x13057458ed519ade 0xfffbe3c7ff8fffff 0xffff7c78fff1ffff

def z34 : W := mkw 0x20ff7bffb5d06b07 0xe41fef7ff6ba0d60 0xfffffffffff07f07 0xfffffffffffe0fe0

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0xf2000040300a039e 0xde40000806014073

def z37 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc403fff839f 0xdfcfff8807fff073

def z38 : W := mkw 0x00008400082a0000 0x0000108001054000 0x7a059c00087a0002 0x8f40b380010f4000

def z39 : W := mkw 0x080822422080c233 0x0101044844101846 0x0100020600004060 0x00200040c000080c

def z40 : W := mkw 0x080822422080c233 0x0101044844101846 0x651a6206318fc0f9 0x4ca34c40c631f81f

def z41 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x7efffdb9c0000000 0x2fdfffb738000000

def z42 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x70059c79f07a039a 0x4e00b38f3e0f4073

def z43 : W := mkw 0x4054500005410004 0x280a8a0000a82000 0x0018600001818000 0x00030c0000303000

def z44 : W := mkw 0x080822422080c233 0x0101044844101846 0x81000246300043fc 0x50200048c600087f

def z45 : W := mkw 0x080822422080c233 0x0101044844101846 0xf71a62463185c061 0x5ee34c48c630b80c

def z46 : W := mkw 0x0054000005400000 0x200a800000a80000 0x1e7c00000ff00003 0x83cf800001fe0000

def z47 : W := mkw 0xc023d4000a2f0004 0x18047a800145e000 0x6003fc00000f8000 0x0c007f800001f000

def z48 : W := mkw 0x080822422080c233 0x0101044844101846 0x051a62060185c061 0x00a34c40c030b80c

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a059c0000000000 0x0f40b38000000000

def z50 : W := mkw 0x3408ae5af83a318b 0x868115cb5f074631 0xfe1ffe7ff87a339e 0xffc3ffcfff0f4673

def z51 : W := mkw 0x0008024000804202 0x0001004800100840 0x9718024001804307 0x92e3004800300860

def z52 : W := mkw 0xf477dc9ddf7f35cc 0xbe8efb93bbefe6b9 0xffffffffffffffff 0xffffffffffffffff

def z53 : W := mkw 0x008009b590000000 0xc0100136b2000000 0x008001b9c0000000 0x2010003738000000

def z54 : W := mkw 0xb40084084a3e35c8 0x168010810947c6b9 0x010000000e7e7fff 0x8020000001cfcfff

def z55 : W := mkw 0xf477d4084f7f318c 0x3e8efa8109efe631 0x7e7ffc000fffb39f 0x8fcfff8001fff673

def z56 : W := mkw 0x340084084dfa7b88 0x2680108109bf4f71 0x010000000ffa7f9f 0x8020000001ff4ff3

def z57 : W := mkw 0x2800000805d0eb30 0x2500000100ba1d66 0x010000000fffffff 0x8020000001ffffff

def z58 : W := mkw 0x485c764225e3c237 0x290b8ec844bc7846 0xf71e7e4631ffc3ff 0xdee3cfc8c63ff87f

def z59 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0x6003fc07f0000000 0x4c007f80fe000000

def z60 : W := mkw 0x2000000805d06b00 0x2400000100ba0d60 0x010000000ff07f07 0x8020000001fe0fe0

def z61 : W := mkw 0x8023008502040440 0x10046010a0408088 0x05e2038606044c61 0x00bc4070c0c0898c

def z62 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x08e18181ce003c00 0x211c303039c00780

def z63 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0x501c7c7830000000 0x0a038f8f06000000

def z64 : W := mkw 0x900080004a0c14c0 0x1200100009418298 0x010000000e0c7ce5 0x8020000001c18f9c

def z65 : W := mkw 0x2000000800102100 0x0400000100020420 0x9a04007808703306 0xb340800f010e0660

def z66 : W := mkw 0x14008c10d82a1088 0x828011821b054211 0x00019c01c0000000 0x0000338038000000

def z67 : W := mkw 0x34008408483a3188 0x0680108109074631 0x0000000008703000 0x00000000010e0600

def z68 : W := mkw 0x3400000840103188 0x0680000108020631 0x000000000000339c 0x0000000000000673

def z69 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfffffffff1804307 0xfffffffffe300860

def z70 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffc03fe3ff07fff 0xf3ff807fc7fe0fff

def z71 : W := mkw 0x34000818d0103188 0x868001031a020631 0x80000079f000339c 0x7000000f3e000673

def z72 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0xfa1dfc79f0000000 0x7f43bf8f3e000000

def z73 : W := mkw 0xf477dc18df7f318c 0xbe8efb831befe631 0xfe7ffc79ffffb39f 0xffcfff8f3ffff673

def z74 : W := mkw 0xe077d5280f7f2904 0x3c0efaa501efe520 0x7efffdb80fffbc03 0xafdfffb701fff780

def z75 : W := mkw 0x345c8f78ddfa7b8a 0xa68b91ef1bbf4f71 0xfa1d9c79f9fa339e 0xff43b38f3f3f4673

def z76 : W := mkw 0x4077540005630004 0x280eea8000ac6000 0x7e7ffc0001f38002 0x0fcfff80003e7000

def z77 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x58fdfdf9f0000000 0x2b1fbfbf3e000000

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0xa7020206000c40e5 0xd4e04040c001881c

def z79 : W := mkw 0x0000008500000440 0x00000010a0000088 0x0180038600004c60 0x00300070c000098c

def z80 : W := mkw 0x24000c1890322108 0x8480018312064421 0x50041c783072031a 0x0a00838f060e4063

def z81 : W := mkw 0x0000200220000001 0x0000040044000000 0x6002600630000000 0x4c004c00c6000000

def z82 : W := mkw 0xc87ff6422fefc237 0x390ffec845fdf846 0xff7ffe463fffc3ff 0xdfefffc8c7fff87f

def z83 : W := mkw 0x0008224220000003 0x0001044844000000 0xf61a6246318f8003 0xdec34c48c631f000

def z84 : W := mkw 0xe87ff76a2fffeb37 0x3d0ffeed45fffd66 0xfffffffe3fffffff 0xffffffffc7ffffff

def z85 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xffe383c7fe0e7fff 0xfffc7078ffc1cfff

def z86 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffe63fe0ff5ff67 0xb3ffcc7fc1febfec

def z87 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x8fe403b80e707c05 0xb1fc807701ce0f80

def z88 : W := mkw 0x1000800048081080 0x0200100009010210 0xaa018001c8083084 0xf540300039010610

def z89 : W := mkw 0x0008224220000003 0x0001044844000000 0xf61a624630000000 0x5ec34c48c6000000

def z90 : W := mkw 0x00882bf7b0000003 0xc011057ef6000000 0x808003fff0000000 0x7010007ffe000000

def z91 : W := mkw 0xc0fffff7bf6f0007 0xf81ffffef7ede000 0xfeffffffffff8003 0xffdffffffffff000

def z92 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x501c607831f3831a 0x0a038c0f063e7063

def z93 : W := mkw 0xc023d4000a2f0004 0x18047a800145e000 0x761bfc00018f8003 0x8ec37f800031f000

def z94 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x5e7c7c000ff38003 0x8bcf8f8001fe7000

def z95 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x20038007c00c00e0 0x44007000f801801c

def z96 : W := mkw 0x0054012000000000 0x000a802400000000 0x08e401b800000000 0x211c803700000000

def z97 : W := mkw 0x080802400080c232 0x0101004800101846 0x97180240018fc3ff 0x92e300480031f87f

def z98 : W := mkw 0x0008224220804203 0x0001044844100840 0xf71a624631804307 0xdee34c48c6300860

def z99 : W := mkw 0xfc7ffe5afffff3bf 0xbf8fffcb5ffffe77 0xff7ffe7ffffff3ff 0xffefffcffffffe7f

def z100 : W := mkw 0x10000085400014c0 0x02000010a8000298 0x8fe00387ce007ce5 0xf1fc0070f9c00f9c

def z101 : W := mkw 0x207f03ed05d06b02 0x240fe07da0ba0d60 0xbfff83ffcff07f07 0xf7fff07ff9fe0fe0

def z102 : W := mkw 0x0000081090000000 0x8000010212000000 0x50041c7830000000 0x0a00838f06000000

def z103 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffffe007c05 0xffffffffffc00f80

def z104 : W := mkw 0x00ff73e725c04a07 0x601fee7ce4b80940 0x05fa638607804c01 0x00bf4c70c0f00980

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x8fe003800e007c05 0xb1fc007001c00f80

def z106 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x701ffc7ff0000000 0x4e03ff8ffe000000

def z107 : W := mkw 0x2008036800906b02 0x0401006d00120d60 0x818003f800007f04 0x3030007f00000fe0

def z108 : W := mkw 0xc077d4850f6f0444 0x380efa90a1ede088 0x7fffff860fffcc63 0x8ffffff0c1fff98c

def z109 : W := mkw 0x40ff7ff7b5630007 0xe81feffef6ac6000 0xfefffffff1f38002 0x7fdffffffe3e7000

def z110 : W := mkw 0x10000085400014c0 0x02000010a8000298 0x81800387c0007ce4 0x70300070f8000f9c

def z111 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x08659c000e700000 0x010cb38001ce0000

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x761a6000018f8003 0x8ec34c000031f000

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7020246300e43ff 0xdee04048c601c87f

def z114 : W := mkw 0x90fffbf7fa0c14c7 0xd21fff7eff418298 0xfffffffffe0c7ce5 0xffffffffffc18f9c

def z115 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x647bfc00078f8001 0x0c8f7f8000f1f000

def z116 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7e7ffc07cfff80e3 0xcfcfff80f9fff01c

def z117 : W := mkw 0x90238895da0c14c0 0x92047112bb418298 0xffe79ffffe0c7ce5 0xfffcf3ffffc18f9c

def z118 : W := mkw 0x1808a2426888d2b3 0x030114484d111a56 0xff1be247f98ff3ff 0xffe37c48ff31fe7f

def z119 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff00a039e 0xffdffffffe014073

def z120 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x0cffffbfc0000000 0x219ffff7f8000000

def z121 : W := mkw 0xb4238c9dda3e35c8 0x96847193bb47c6b9 0xafe79fbfce7c7ce5 0xf5fcf3f7f9cf8f9c

def z122 : W := mkw 0x00082a52b0000003 0x8001054a56000000 0xfe1ffe7ff0000000 0x7fc3ffcffe000000

def z123 : W := mkw 0x345c8f78ddfa7b8a 0xa68b91ef1bbf4f71 0xfffd9ff9fffa7f9f 0xffffb3ff3fff4ff3

def z124 : W := mkw 0x1000800048081080 0x0200100009010210 0x0000000008083084 0x8000000001010610

def z125 : W := mkw 0x2008036800906b02 0x0401006d00120d60 0x8fe003f80e007f05 0xb1fc007f01c00fe0

def z126 : W := mkw 0x08dc7b72b080c237 0xc11b8f6e56101846 0x501c7c783183831a 0x0a038f8f06307063

def z127 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x05e203860e0c7ce5 0x80bc4070c1c18f9c

def z128 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0x68e7fdbff0000000 0x6d1cffb7fe000000

def z129 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x1e7d9c000ff00003 0x83cfb38001fe0000

def z130 : W := mkw 0x982ba2c76a8cd6f3 0x13057458ed519ade 0xaffbe387cf8dfce5 0xf5ff7c70f9f1bf9c

def z131 : W := mkw 0x802380000a0c0000 0x1004700001418000 0x7e7be0000f8f8003 0x8fcf7c0001f1f000

def z132 : W := mkw 0x085c236225c0ca33 0x210b846c44b81946 0xf7fa63c6378fcfff 0xdeff4c78c6f1f9ff

def z133 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x09e401b80ff07f07 0xa13c803701fe0fe0

def z134 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x101c007801f00302 0x0203800f003e0060

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a04007800000000 0x3340800f00000000

def z136 : W := mkw 0x14008c10d82a1088 0x828011821b054211 0x60019c01f00a0098 0x4c0033803e014013

def z137 : W := mkw 0xb4238c18da3e3188 0x968471831b47c631 0xfe679c79fe7e339f 0xffccf38f3fcfc673

def z138 : W := mkw 0x08ff73e72080c237 0x411fee7ce4101846 0x05fa63860185c061 0x00bf4c70c030b80c

def z139 : W := mkw 0x2000000800906b00 0x0400000100120d60 0x0100000000007f04 0x0020000000000fe0

def z140 : W := mkw 0x20ff7bffb5502907 0xe41fef7ff6aa0520 0xfefffffffe703c00 0x7fdfffffffce0780

def z141 : W := mkw 0x24000c1890322108 0x8480018312064421 0x00041c3800700000 0x00008387000e0000

def z142 : W := mkw 0x24008c18983a2108 0x8480118313074421 0x7a059c78387a031a 0x8f40b38f070f4063

def z143 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xfae59df9f0000000 0x7f5cb3bf3e000000

def z144 : W := mkw 0xc077500007450004 0x380eea0000e8a000 0x7e7ffc0007858001 0x0fcfff8000f0b000

def z145 : W := mkw 0xb423848d4a3e35c8 0x16847091a947c6b9 0xafe38387ce7e7fff 0xf5fc7070f9cfcfff

def z146 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff00043fc 0x7ffffffffe00087f

def z147 : W := mkw 0xd477dc10df6f108c 0xba8efb821bede211 0x7e7ffc01ffff809b 0xcfcfff803ffff013

def z148 : W := mkw 0x0023089590000000 0x80046112b2000000 0xfee79ffff0000000 0x7fdcf3fffe000000

def z149 : W := mkw 0xb4238c9dda3e35c8 0x96847193bb47c6b9 0xffe79ffffe7e7fff 0xfffcf3ffffcfcfff

def z150 : W := mkw 0x34dcff7af83a318f 0xc69b9fef5f074631 0xfa1dfc79f87a339e 0xff43bf8f3f0f4673

def z151 : W := mkw 0x3c08ae5af8baf3bb 0x878115cb5f175e77 0xff1ffe7ff9fff3ff 0xffe3ffcfff3ffe7f

def z152 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x08059c39c8703000 0x2100b387390e0600

def z153 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x08e59d81ce703c00 0x211cb3b039ce0780

def z154 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x60019c01f87a339e 0xcc0033803f0f4673

def z155 : W := mkw 0x2000012800102900 0x0400002500020520 0x008001b800003c00 0x2010003700000780

def z156 : W := mkw 0x1c08ae52f8aad2bb 0x838115ca5f155a57 0xf71bfe47f18fc3ff 0xdee37fc8fe31f87f

def z157 : W := mkw 0x4054d4000d6b0004 0x280a9a8001ad6000 0x7a1dfc0009fb8002 0x8f43bf80013f7000

def z158 : W := mkw 0xc00084000f6f0000 0x3800108001ede000 0x761a60000fff8003 0x8ec34c0001fff000

def z159 : W := mkw 0xc07fd6400fef4206 0x380ffac801fde840 0xff7ffe400fffc307 0x9fefffc801fff860

def z160 : W := mkw 0xc0ff7bf7b7450007 0xf81fef7ef6e8a000 0xfefffffff7858001 0x7fdffffffef0b000

def z161 : W := mkw 0x34fffffff83a318f 0xc69fffffff074631 0xfefffffff87a339e 0xffdfffffff0f4673

def z162 : W := mkw 0x10000085400014c0 0x02000010a8000298 0xa7820387c00c7ce5 0xf4f04070f8018f9c

def z163 : W := mkw 0x00ff73e720000007 0x401fee7ce4000000 0x9efe63fe00000000 0x33dfcc7fc0000000

def z164 : W := mkw 0x10882bf7f00014c3 0xc211057efe000298 0x818003fff0007ce4 0x7030007ffe000f9c

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x08e001800e003c00 0x211c003001c00780

def z166 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x0c7ffc000ff58001 0x018fff8001feb000

def z167 : W := mkw 0xf477dc18df7f318c 0xbe8efb831befe631 0x7e7ffc39cfffb003 0xafcfff8739fff600

def z168 : W := mkw 0x907780854f4c14c0 0x320ef010a9e98298 0xbfff8387cffc7ce7 0xf7fff070f9ff8f9c

def z169 : W := mkw 0x90f7d9b5da0c14c4 0xd21efb36bb418298 0xafe79fbfce0c7ce5 0xf5fcf3f7f9c18f9c

def z170 : W := mkw 0x34a3fc9ff83a318d 0xc6947f93ff074631 0xfa07fc7ff87a339e 0xff40ff8fff0f4673

def z171 : W := mkw 0xc0fffff7ba2f0007 0xd81ffffef745e000 0xfefffffff00f8000 0x7fdffffffe01f000

def z172 : W := mkw 0x10fffbf7f8081087 0xc21fff7eff010210 0xfefffffff8083084 0xffdfffffff010610

def z173 : W := mkw 0x00807812b0000005 0xc0100f0256000000 0x40007c0030000000 0x08000f8006000000

def z174 : W := mkw 0x080822422080c233 0x0101044844101846 0xf3000246300a43fe 0xde600048c601487f

def z175 : W := mkw 0xe07fd7680fff6b06 0x3c0ffaed01ffed60 0xfffffff80fffff07 0xbfffffff01ffffe0

def z176 : W := mkw 0x085c23622080c233 0x010b846c44101846 0xfffe63fe318fc3ff 0xffffcc7fc631f87f

def z177 : W := mkw 0x00008400082a0000 0x0000108001054000 0x00000000087a0002 0x80000000010f4000

def z178 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffe63f80fffff07 0xbfffcc7f01ffffe0

def z179 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x85f803f807807f05 0x30bf007f00f00fe0

def z180 : W := mkw 0x8023008502040440 0x10046010a0408088 0xafe38387c6044c61 0x75fc7070f8c0898c

def z181 : W := mkw 0x005c036005c04a02 0x200b806c00b80940 0x0018000001800000 0x0003000000300000

def z182 : W := mkw 0x0077508500000004 0x000eea10a0000000 0xfeffff87c0000000 0x7fdffff0f8000000

def z183 : W := mkw 0xc80084000fefc230 0x3900108001fdf846 0x010000000fffc3ff 0x8020000001fff87f

def z184 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfefffffff00f80f8 0x7fdffffffe01f01f

def z185 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x761e7c0001ff8003 0x8ec3cf80003ff000

def z186 : W := mkw 0xc077500007450004 0x380eea0000e8a000 0x047a600007858001 0x008f4c0000f0b000

def z187 : W := mkw 0xb4fffffffa3e35cf 0xd69fffffff47c6b9 0xfffffffffe7e7fff 0xffffffffffcfcfff

def z188 : W := mkw 0x0000008500000000 0x00000010a0000000 0x80800387c0000000 0x70100070f8000000

def z189 : W := mkw 0xb07781ad4f5c3dc0 0x360ef035a9eb87b8 0x08e581b9ce703c00 0x211cb03739ce0780

def z190 : W := mkw 0x2400081890102108 0x8480010312020421 0x0000007830000318 0x0000000f06000063

def z191 : W := mkw 0x080822422080c233 0x0101044844101846 0xa7020246300c43fd 0xd4e04048c601887f

def z192 : W := mkw 0x087f72422080c237 0x010fee4844101846 0xff7ffe46318fc3ff 0xdfefffc8c631f87f

def z193 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xffe59ff9fe7a7f9f 0xfffcb3ff3fcf4ff3

def z194 : W := mkw 0x2000000800102100 0x0400000100020420 0x9fe403f80e707f07 0xb3fc807f01ce0fe0

def z195 : W := mkw 0x0023008500000000 0x00046010a0000000 0xafe38387c00c40e5 0xf5fc7070f801881c

def z196 : W := mkw 0x34000818d0103188 0x868001031a020631 0x9a040079f870339e 0xf340800f3f0e0673

def z197 : W := mkw 0x90a3f897fa0c14c5 0xd2147f12ff418298 0x6003fc07f00c00e0 0x4c007f80fe01801c

def z198 : W := mkw 0x802380000a0c0000 0x1004700001418000 0x2e6380000e0c0001 0x85cc700001c18000

def z199 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f00a039e 0xff40b38f3e014073

def z200 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x047a60000fff8003 0x808f4c0001fff000

def z201 : W := mkw 0xb87fa3ef6fdcfff3 0x370ff47dedfb9ffe 0xffffe3ffffffffff 0xfffffc7fffffffff

def z202 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x9efc03f80e703c00 0x33df807f01ce0780

def z203 : W := mkw 0x205c0b7895d06b02 0xa40b816f12ba0d60 0xfffd9ff9fff07f07 0xffffb3ff3ffe0fe0

def z204 : W := mkw 0x207f536805d06b06 0x240fea6d00ba0d60 0xfffffff80ff07f07 0xbfffffff01fe0fe0

def z205 : W := mkw 0xc05484000f6f0000 0x380a908001ede000 0x1e7c00000fff8003 0x83cf800001fff000

def z206 : W := mkw 0x802380000a0c0000 0x1004700001418000 0x086180000e000000 0x010c300001c00000

def z207 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x9a059c79c8703306 0xb340b38f390e0660

def z208 : W := mkw 0xc00084000f6f0000 0x3800108001ede000 0x7a059c000fff8003 0x8f40b38001fff000

def z209 : W := mkw 0xc0ffff72bf6f0007 0xf81fffee57ede000 0x7e7ffc783fff8003 0x8fcfff8f07fff000

def z210 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x88e59ffff0000000 0x711cb3fffe000000

def z211 : W := mkw 0x9808a2426a8cd6f3 0x130114484d519ade 0xf71a62463f8fffff 0xdee34c48c7f1ffff

def z212 : W := mkw 0x0800200220008031 0x0100040044001006 0x60026006300f80f8 0x4c004c00c601f01f

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x9200004000000306 0x9240000800000060

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e6000000e000001 0x81cc000001c00000

def z215 : W := mkw 0x34548d38dd7a3988 0xa68a91a71baf4731 0x08e59db9ce703c00 0x211cb3b739ce0780

def z216 : W := mkw 0x080000000080c230 0x0100000000101846 0x01000000000043fc 0x002000000000087f

def z217 : W := mkw 0x08082a52b080c233 0x8101054a56101846 0xff1ffe7ff18fc3ff 0xffe3ffcffe31f87f

def z218 : W := mkw 0x2000000800102100 0x0400000100020420 0x0000000008703306 0x80000000010e0660

def z219 : W := mkw 0x0008224220000003 0x0001044844000000 0xf61a6246300a039e 0xdec34c48c6014073

def z220 : W := mkw 0x3c08a64a68baf3bb 0x078114c94d175e77 0xf71a624639fff3ff 0xdee34c48c73ffe7f

def z221 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xa7038207c00c40e5 0xd4e07040f801881c

def z222 : W := mkw 0x080822422080c233 0x0101044844101846 0xfffa63c63f8fffff 0xffff4c78c7f1ffff

def z223 : W := mkw 0x00dc2bf7b0000003 0xc01b857ef6000000 0x9efc03fff0000000 0x73df807ffe000000

def z224 : W := mkw 0x0008024000804202 0x0001004800100840 0x0518020001804001 0x00a3004000300800

def z225 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff00c40e5 0xfffffffffe01881c

def z226 : W := mkw 0xb00080084fdc7fc0 0x3600100109fb8ff8 0x010000000ffc7fe7 0x8020000001ff8ffc

def z227 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x547e7c0007f78003 0x0a8fcf8000fef000

def z228 : W := mkw 0x2008024805d06b02 0x2401004900ba0d60 0x971802400ff07f07 0x92e3004801fe0fe0

def z229 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x919c03f801f07f06 0x3233807f003e0fe0

def z230 : W := mkw 0x180822c76080d6f3 0x03010458ec101ade 0xf79a63c7f18fffff 0xfef34c78fe31ffff

def z231 : W := mkw 0x007f536000000006 0x000fea6c00000000 0xfefffff800000000 0x3fdfffff00000000

def z232 : W := mkw 0x14008c10d82a1088 0x828011821b054211 0x7a059c01f87a009a 0xcf40b3803f0f4013

def z233 : W := mkw 0xc0f7ddb59f6f0004 0xf81efbb6b3ede000 0x7efffdb9cfff8003 0xafdfffb739fff000

def z234 : W := mkw 0x080822422080c233 0x0101044844101846 0xf71a6246300043fc 0x5ee34c48c600087f

def z235 : W := mkw 0x005c036005c04a02 0x200b806c00b80940 0x8ff803800f807c05 0xb1ff007001f00f80

def z236 : W := mkw 0x0008036000000002 0x0001006c00000000 0x808003f800000000 0x3010007f00000000

def z237 : W := mkw 0xc87ff6422fefc237 0x390ffec845fdf846 0x7e7ffc403fff831b 0x8fcfff8807fff063

def z238 : W := mkw 0xc0fff7e72f6f0007 0x781ffefce5ede000 0x7effff860fff8003 0x8fdffff0c1fff000

def z239 : W := mkw 0x005c036005c04a02 0x200b806c00b80940 0x9ffc03f807804c01 0x33ff807f00f00980

def z240 : W := mkw 0x0800200220008031 0x0100040044001006 0x00000006300000f8 0x40000000c600001f

def z241 : W := mkw 0x900080004a0c14c0 0x1200100009418298 0x00000000000c00e0 0x000000000001801c

def z242 : W := mkw 0x345c87684dfa7b8a 0x268b90ed09bf4f71 0x9ffc03f80ffa7f9f 0xb3ff807f01ff4ff3

def z243 : W := mkw 0x0077500000000004 0x000eea0000000000 0x047a600000000000 0x008f4c0000000000

def z244 : W := mkw 0x00d4593090000004 0xc01a8b2612000000 0x00041c3800000000 0x0000838700000000

def z245 : W := mkw 0x4000040005630000 0x2800008000ac6000 0x0000000001f38002 0x00000000003e7000

def z246 : W := mkw 0x94238c95da2e14c8 0x92847192bb45c299 0x60039c07f00e00f8 0x4c007380fe01c01f

def z247 : W := mkw 0xc0f7fc97bf6f0005 0xf81eff92f7ede000 0x7e7ffc07ffff8003 0xcfcfff80fffff000

def z248 : W := mkw 0x00008400082a0000 0x0000108001054000 0x7e1ffc0009ff8003 0x8fc3ff80013ff000

def z249 : W := mkw 0x080822422080c233 0x0101044844101846 0x0000004030000318 0x0000000806000063

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0xf200004030000000 0x5e40000806000000

def z251 : W := mkw 0x0000081090000000 0x8000010212000000 0x08059c39c0000000 0x2100b38738000000

def z252 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfefffffff183831a 0x7fdffffffe307063

def z253 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x00018001c0000000 0x0000300038000000

def z254 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x00041c0000700000 0x00008380000e0000

def z255 : W := mkw 0x2000000800102100 0x0400000100020420 0x1004007800700302 0x0200800f000e0060

def z256 : W := mkw 0x802380000a0c0000 0x1004700001418000 0xafe383800e0c7c05 0xb5fc707001c18f80

def z257 : W := mkw 0x005c036000804202 0x000b806c00100840 0x9ffc03f801804307 0xb3ff807f00300860

def z258 : W := mkw 0x8077d0000a0c0004 0x100efa0001418000 0x7e7ffc000e0c0001 0x8fcfff8001c18000

def z259 : W := mkw 0x345c8f78ddfa7b8a 0xa68b91ef1bbf4f71 0x9ffd9ff9cff07f07 0xb3ffb3ff39fe0fe0

def z260 : W := mkw 0x34008408483a3188 0x0680108109074631 0xf2000040387a339e 0xde400008070f4673

def z261 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc000e700000 0x0fcfff8001ce0000

def z262 : W := mkw 0x10008400482a1080 0x0200108009054210 0xfa059c01c87a3086 0xff40b380390f4610

def z263 : W := mkw 0x0008224220000003 0x0001044844000000 0x5018604030000000 0x0a030c0806000000

def z264 : W := mkw 0x90230085420414c0 0x12046010a8408298 0x85e20387c6047ce5 0x70bc4070f8c08f9c

def z265 : W := mkw 0x34000818d0103188 0x868001031a020631 0xfa059c79f000339c 0x7f40b38f3e000673

def z266 : W := mkw 0x2008024800906302 0x0401004900120c60 0x9f1c027809f07307 0xb3e3804f013e0e60

def z267 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x111c00780ff07f07 0x8223800f01fe0fe0

def z268 : W := mkw 0x10008810d8081080 0x820011021b010210 0xfa059c79f8083084 0xff40b38f3f010610

def z269 : W := mkw 0x3c082a5af090f3bb 0x8781054b5e121e77 0x8100027ff00073fc 0x7020004ffe000e7f

def z270 : W := mkw 0x180822c76080d6f3 0x03010458ec101ade 0x818003c7f0007ffc 0x70300078fe000fff

def z271 : W := mkw 0xc877d4000fefc234 0x390efa8001fdf846 0x7f7ffc000fffc3ff 0x8fefff8001fff87f

def z272 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xaee79fbfc0000000 0x75dcf3f7f8000000

def z273 : W := mkw 0x0054000005400000 0x200a800000a80000 0x101c000001f00002 0x02038000003e0000

def z274 : W := mkw 0xd077d0854f4d14c4 0x3a0efa10a9e9a298 0xaffbe387cf8dfce5 0xf5ff7c70f9f1bf9c

def z275 : W := mkw 0x00ff73e720000007 0x401fee7ce4000000 0xf6fa63c630000000 0x5edf4c78c6000000

def z276 : W := mkw 0xb423889dda1c35c8 0x96847113bb4386b9 0xafe383fffe0c7ffd 0xf5fc707fffc18fff

def z277 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff185c061 0x7ffffffffe30b80c

def z278 : W := mkw 0x080000000080c230 0x0100000000101846 0x000000000183831a 0x0000000000307063

def z279 : W := mkw 0x0008024000804202 0x0001004800100840 0x1018004001800302 0x0203000800300060

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0xf71a6206018fc0e7 0xdee34c40c031f81c

def z281 : W := mkw 0xe05c87680fff6b02 0x3c0b90ed01ffed60 0x9ffc03f80fffff07 0xb3ff807f01ffffe0

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0xa200000000080084 0xd440000000010010

def z283 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff18f8003 0xffdffffffe31f000

def z284 : W := mkw 0x005c036000000002 0x000b806c00000000 0x9ffc03f80e007c05 0xb3ff807f01c00f80

def z285 : W := mkw 0xc87ff6422fefc237 0x390ffec845fdf846 0x7f7ffe060fffc063 0x8fefffc0c1fff80c

def z286 : W := mkw 0xd02384854f6f14c0 0x3a047090a9ede298 0xafe38387cffffce7 0xf5fc7070f9ffff9c

def z287 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffc03f83ffa7f9f 0xffff807f07ff4ff3

def z288 : W := mkw 0xc87f724227c5c237 0x390fee4844f8b846 0x057a62060785c061 0x00af4c40c0f0b80c

def z289 : W := mkw 0x080822422080c233 0x0101044844101846 0x771a6206018fc063 0x8ee34c40c031f80c

def z290 : W := mkw 0x34008818d8183188 0x868011031b030631 0xaa018079f808339c 0xf540300f3f010673

def z291 : W := mkw 0xf4008c18df7f3188 0xbe8011831befe631 0xfa059c79ffffb39f 0xff40b38f3ffff673

def z292 : W := mkw 0x1000800048081080 0x0200100009010210 0xafe18381ce087c85 0xf5fc307039c10f90

def z293 : W := mkw 0x080822422080c233 0x0101044844101846 0xf61a62463183831a 0x5ec34c48c6307063

def z294 : W := mkw 0x14a3fc97f82a108d 0xc2947f92ff054211 0x6003fc07f00a0098 0x4c007f80fe014013

def z295 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x58059c79f872331a 0x2b00b38f3f0e4663

def z296 : W := mkw 0x2008036800906b02 0x0401006d00120d60 0x0000007800000300 0x0000000f00000060

def z297 : W := mkw 0x00882bf7b0000003 0xc011057ef6000000 0xfa859ffff0000000 0x7f50b3fffe000000

def z298 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x971c027801f04307 0x92e3804f003e0860

def z299 : W := mkw 0xb023808d4a1c35c0 0x16047011a94386b8 0xbfe783ffce7c7fe7 0xf7fcf07ff9cf8ffc

def z300 : W := mkw 0xc023d4000a2f0004 0x18047a800145e000 0x6e63fc000e0f8001 0x8dcc7f8001c1f000

def z301 : W := mkw 0xc87f724227c5c237 0x390fee4844f8b846 0xf77a6246378fc3ff 0xdeef4c48c6f1f87f

def z302 : W := mkw 0xc00084000f6f0000 0x3800108001ede000 0x000000000e700000 0x0000000001ce0000

def z303 : W := mkw 0xb023808d4fdc7fc0 0x36047011a9fb8ff8 0xafe38387cffc7fe7 0xf5fc7070f9ff8ffc

def z304 : W := mkw 0xc0f7ddb59f6f0004 0xf81efbb6b3ede000 0x08e59db9ce700000 0x211cb3b739ce0000

def z305 : W := mkw 0x00a3708720000005 0x40146e10e4000000 0x0002600600000000 0x00004c00c0000000

def z306 : W := mkw 0x00ab7ad7b0000007 0xc0156f5af6000000 0xf61bfe47f0000000 0x5ec37fc8fe000000

def z307 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x701ffc0001ff8002 0x0e03ff80003ff000

def z308 : W := mkw 0xb47f8ffddffe7fca 0xb68ff1ffbbffcff9 0xffff9ffffffe7fff 0xfffff3ffffffcfff

def z309 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0xfe7ffc01cfffb087 0xffcfff8039fff610

def z310 : W := mkw 0x205c036800102102 0x040b806d00020420 0x9efc03f808703306 0xb3df807f010e0660

def z311 : W := mkw 0x0023000000000000 0x0004600000000000 0x2e63800000000000 0x05cc700000000000

def z312 : W := mkw 0x0800200220008031 0x0100040044001006 0x0002600600058060 0x00004c00c000b00c

def z313 : W := mkw 0x0800200220008031 0x0100040044001006 0x4000600030038018 0x08000c0006007003

def z314 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x21038007ce0c7ce5 0xc4207000f9c18f9c

def z315 : W := mkw 0x2008036800906b02 0x0401006d00120d60 0x9b8403f808707f06 0xb370807f010e0fe0

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0x8a00000008003004 0xb140000001000600

def z317 : W := mkw 0x300803ed40907fc2 0x0601007da8120ff8 0x818003ffc0007fe4 0x7030007ff8000ffc

def z318 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xfffbe387cf8ffce7 0xffff7c70f9f1ff9c

def z319 : W := mkw 0x2c082e5ab0b2e33b 0x858105cb56165c67 0xf71e7e7e31ffc3ff 0xdee3cfcfc63ff87f

def z320 : W := mkw 0x882b22c72284c673 0x11056458e45098ce 0xf7fa63c6378fcfff 0xdeff4c78c6f1f9ff

def z321 : W := mkw 0x900080004a0c14c0 0x1200100009418298 0x000000000e003c00 0x0000000001c00780

def z322 : W := mkw 0xb4008c18da3e35c8 0x968011831b47c6b9 0xfb059c79fe7e7fff 0xff60b38f3fcfcfff

def z323 : W := mkw 0x1000800048081080 0x0200100009010210 0x20018001c0080080 0x4400300038010010

def z324 : W := mkw 0x080822422080c233 0x0101044844101846 0x051a6206018fc3ff 0x80a34c40c031f87f

def z325 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x89e403f80e707f04 0x313c807f01ce0fe0

def z326 : W := mkw 0xc077500007450004 0x380eea0000e8a000 0x0060000006000000 0x000c000000c00000

def z327 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xbffe03fe0ffc7fe7 0xf7ffc07fc1ff8ffc

def z328 : W := mkw 0xf07fd7ed4fff7fc6 0x3e0ffafda9ffeff8 0xffffffffcfffffe7 0xfffffffff9fffffc

def z329 : W := mkw 0x90fffbf7fa0c14c7 0xd21fff7eff418298 0xfefffffffe003c00 0x7fdfffffffc00780

def z330 : W := mkw 0x082b22c72080c233 0x01056458e4101846 0xfffbe3c7f18fc3ff 0xffff7c78fe31f87f

def z331 : W := mkw 0x0054000005400000 0x200a800000a80000 0x7e7e60000fff8003 0x8fcfcc0001fff000

def z332 : W := mkw 0x605c576805f36b06 0x2c0b8aed00be6d60 0xdffc7ff80ff3ff07 0xbbff8fff01fe7fe0

def z333 : W := mkw 0xc077d4850f6f0004 0x380efa90a1ede000 0xfeffff87cfff8003 0xffdffff0f9fff000

def z334 : W := mkw 0x0008024000804202 0x0001004800100840 0x9ff803c00f807f07 0xb3ff007801f00fe0

def z335 : W := mkw 0x14008c10d82a1088 0x828011821b054211 0xea019c01f80a309c 0xfd4033803f014613

def z336 : W := mkw 0x305c03ed45d07fc2 0x260b807da8ba0ff8 0x9ffc03ffcff07fe7 0xf3ff807ff9fe0ffc

def z337 : W := mkw 0xc808a6422fefc233 0x390114c845fdf846 0xf71a62463fffc3ff 0xdee34c48c7fff87f

def z338 : W := mkw 0xc0fffff7bf6f0007 0xf81ffffef7ede000 0xfefffffffe700000 0x7fdfffffffce0000

def z339 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x25e38387c60c4ce1 0x44bc7070f8c1899c

def z340 : W := mkw 0xc02384000f6f0000 0x3804708001ede000 0x2e6380000fff8003 0x85cc700001fff000

def z341 : W := mkw 0x0077d400082a0004 0x000efa8001054000 0x7e7ffc00087a0002 0x8fcfff80010f4000

def z342 : W := mkw 0xe0ffffffbfff6b07 0xfc1ffffff7ffed60 0xffffffffffffff07 0xffffffffffffffe0

def z343 : W := mkw 0x14008c10d82a1088 0x828011821b054211 0xf2019c41f00a039e 0xde4033883e014073

def z344 : W := mkw 0x0008036000804a02 0x0001006c00100940 0x0180038000004c00 0x0030007000000980

def z345 : W := mkw 0x802380000a0c0000 0x1004700001418000 0xaf6382060e0c40e5 0xd5ec7040c1c1881c

def z346 : W := mkw 0xc054d4000f6f0004 0x380a9a8001ede000 0x501c7c000fff8003 0x8a038f8001fff000

def z347 : W := mkw 0xb07781ad4f5c3dc0 0x360ef035a9eb87b8 0xafe783bfce7c7ce5 0xf5fcf077f9cf8f9c

def z348 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xa1838387c00c7ce4 0x74307070f8018f9c

def z349 : W := mkw 0xb0fffbffffdc7fc7 0xf61fff7ffffb8ff8 0xfffffffffffc7fe7 0xffffffffffff8ffc

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0x0502020600044061 0x00a04040c000880c

def z351 : W := mkw 0xf47fdf78dfff7b8e 0xbe8ffbef1bffef71 0xfffffff9ffffff9f 0xffffffff3ffffff3

def z352 : W := mkw 0x005c036000000002 0x000b806c00000000 0x101c007800000000 0x0203800f00000000

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x761a600000000000 0x0ec34c0000000000

def z354 : W := mkw 0x0800200220008031 0x0100040044001006 0x761a6006318f80fb 0xcec34c00c631f01f

def z355 : W := mkw 0x28ff7bffb5d0eb37 0xe51fef7ff6ba1d66 0xffffffffffffffff 0xffffffffffffffff

def z356 : W := mkw 0xc0ff73e727450007 0x781fee7ce4e8a000 0x04fa638607858001 0x009f4c70c0f0b000

def z357 : W := mkw 0x0008024000804202 0x0001004800100840 0x8100024000004304 0x1020004800000860

def z358 : W := mkw 0xc077d0000f4d0004 0x380efa0001e9a000 0x2e7be0000f8d8001 0x85cf7c0001f1b000

def z359 : W := mkw 0x8023000002040000 0x1004600000408000 0x0462000006040001 0x008c400000c08000

def z360 : W := mkw 0x2000000800102100 0x0400000100020420 0x8000007800003304 0x3000000f00000660

def z361 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0xfffe63fe3ff07f07 0xffffcc7fc7fe0fe0

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000a039e 0x8000000000014073

def z363 : W := mkw 0x8023008502040440 0x10046010a0408088 0x0002000600040060 0x00004000c000800c

def z364 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0xeee3ff87f0000000 0x7ddc7ff0fe000000

def z365 : W := mkw 0x00f77897b0000005 0xc01eef12f6000000 0x7e7ffc07f0000000 0x4fcfff80fe000000

def z366 : W := mkw 0x802380850a0c0440 0x10047010a1418088 0x2fe383860e0c4c61 0x85fc7070c1c1898c

def z367 : W := mkw 0x080822422080c233 0x0101044844101846 0xd11862463183c3fe 0x5a230c48c630787f

def z368 : W := mkw 0xc077508507450444 0x380eea10a0e8a088 0x05fa63860785cc61 0x00bf4c70c0f0b98c

def z369 : W := mkw 0x345c8f78d83a318a 0x868b91ef1b074631 0xfefd9ff9f87a339e 0xffdfb3ff3f0f4673

def z370 : W := mkw 0x34008408483a3188 0x0680108109074631 0xaa018001c87a339e 0xf5403000390f4673

def z371 : W := mkw 0x3cfffffff8baf3bf 0xc79fffffff175e77 0xfffffffff9fff3ff 0xffffffffff3ffe7f

def z372 : W := mkw 0x00802897b0000001 0xc0100512f6000000 0x00000007f0000000 0x40000000fe000000

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x041a600001858001 0x00834c000030b000

def z374 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x05f803800ff07f07 0x80bf007001fe0fe0

def z375 : W := mkw 0x080822422080c233 0x0101044844101846 0x761a6040318f831b 0x8ec34c080631f063

def z376 : W := mkw 0x3c008c18d8baf3b8 0x878011831b175e77 0xfb059c79f9fff3ff 0xff60b38f3f3ffe7f

def z377 : W := mkw 0x0000081090000000 0x8000010212000000 0x60019c01f0000000 0x4c0033803e000000

def z378 : W := mkw 0x0023500000000004 0x00046a0000000000 0x6003fc0000000000 0x0c007f8000000000

def z379 : W := mkw 0x005c0b7090000002 0x800b816e12000000 0xfefd9ff9f0000000 0x7fdfb3ff3e000000

def z380 : W := mkw 0x080822422080c233 0x0101044844101846 0x701a6046318f83fa 0x4e034c08c631f07f

def z381 : W := mkw 0x34008408483a3188 0x0680108109074631 0x7a059c00087a339e 0x8f40b380010f4673

def z382 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xafe79f87ce7c7ce5 0xf5fcf3f0f9cf8f9c

def z383 : W := mkw 0x10008085480814c0 0x02001010a9010298 0xab818387c8087ce4 0xf5703070f9010f9c

def z384 : W := mkw 0x08882bf7b080c233 0xc111057ef6101846 0x818003fff00043fc 0x7030007ffe00087f

def z385 : W := mkw 0x0000000005c04a00 0x2000000000b80940 0x0100000007804c01 0x0020000000f00980

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x72000000000a0002 0x8e40000000014000

def z387 : W := mkw 0x34fffffff83a318f 0xc69fffffff074631 0xfefffffff8703000 0x7fdfffffff0e0600

def z388 : W := mkw 0x902384854a2e14c0 0x12047090a945c298 0xffe79f87ce7e7ce7 0xfffcf3f0f9cfcf9c

def z389 : W := mkw 0xa07f03ed07d46f42 0x340fe07da0fa8de8 0x9ffe03fe0ff47f67 0xb3ffc07fc1fe8fec

def z390 : W := mkw 0x0077500000000004 0x000eea0000000000 0x7e7ffc00018f8003 0x8fcfff800031f000

def z391 : W := mkw 0x34008c18ddfa7b88 0xa68011831bbf4f71 0xfb059c79fffa7f9f 0xff60b38f3fff4ff3

def z392 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x64fbff87f0000000 0x4c9f7ff0fe000000

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000018f8003 0x800000000031f000

def z394 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x08659c000fff8003 0x810cb38001fff000

def z395 : W := mkw 0x00dc7bf7b0000007 0xc01b8f7ef6000000 0xd09c7ffff0000000 0x7a138ffffe000000

def z396 : W := mkw 0x0000000000804200 0x0000000000100840 0x0100000001804307 0x8020000000300860

def z397 : W := mkw 0x3c082a5af090f3bb 0x8781054b5e121e77 0xf71a627ff18ff3ff 0xfee34c4ffe31fe7f

def z398 : W := mkw 0x2054000805d06b00 0x240a800100ba0d60 0x1f7c00000ff07f07 0x83ef800001fe0fe0

def z399 : W := mkw 0x902b82c54a8c56c2 0x12057058a9518ad8 0xbffb83c7cf8c7fe7 0xf7ff7078f9f18ffc

def z400 : W := mkw 0xc823f4022a2f8035 0x19047e804545f006 0x6003fc06300f80f8 0x4c007f80c601f01f

def z401 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x0dfc03b80ff07c01 0x21bf807701fe0f80

def z402 : W := mkw 0x3c00ac1af83ab1b9 0x878015835f075637 0xfa07fc7ff87fb3fe 0xff40ff8fff0ff67f

def z403 : W := mkw 0x3400089dd01035c8 0x86800113ba0206b9 0x818003fff0007ffc 0x7030007ffe000fff

def z404 : W := mkw 0x00dc736220000007 0x401b8e6c44000000 0x0018600000000000 0x00030c0000000000

def z405 : W := mkw 0x34000818d0103188 0x868001031a020631 0x00000039c0003000 0x2000000738000600

def z406 : W := mkw 0x34000c18d0323188 0x868001831a064631 0xd0041c79f072339e 0x7a00838f3e0e4673

def z407 : W := mkw 0x0800000000008030 0x0100000000001006 0x00000000000f80f8 0x000000000001f01f

def z408 : W := mkw 0x0800200220008031 0x0100040044001006 0xf2026046300f83fe 0xde404c08c601f07f

def z409 : W := mkw 0xf477dc18df7f318c 0xbe8efb831befe631 0x08659c39ce703000 0x210cb38739ce0600

def z410 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x587dfc000ff38002 0x0b0fbf8001fe7000

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x010000000e007c05 0x8020000001c00f80

def z412 : W := mkw 0x0000040000220000 0x0000008000044000 0x50041c0000720002 0x0a008380000e4000

def z413 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xff079e7ff87e73ff 0xffe0f3cfff0fce7f

def z414 : W := mkw 0xf477dc18df7f318c 0xbe8efb831befe631 0xfa659c79fe7a339e 0xff4cb38f3fcf4673

def z415 : W := mkw 0x0808224220008033 0x0101044844001006 0xf61a6246300f80f8 0x5ec34c48c601f01f

def z416 : W := mkw 0x080822422080c233 0x0101044844101846 0x51186040318fc3ff 0x8a230c080631f87f

def z417 : W := mkw 0xc023d4000a2f0004 0x18047a800145e000 0x00019c0000000000 0x0000338000000000

def z418 : W := mkw 0x345c0b78d5d07b8a 0xa68b816f1aba0f71 0x9ffc03f9fff07f9f 0xf3ff807f3ffe0ff3

def z419 : W := mkw 0x2808224a2090e333 0x0501044944121c66 0xff1e627e39fff3ff 0xffe3cc4fc73ffe7f

def z420 : W := mkw 0x245c0f7895f26b0a 0xa48b81ef12be4d61 0x501c1c7831f2031a 0x0a03838f063e4063

def z421 : W := mkw 0x04000c1090220008 0x8080018212044001 0x40001c0030020018 0x0800038006004003

def z422 : W := mkw 0x24ff7fffb032210f 0xc49feffff6064421 0xfefffffff072031a 0x7fdffffffe0e4063

def z423 : W := mkw 0x2808236a2090eb33 0x0501046d44121d66 0x818003fe30007ffc 0x7030007fc6000fff

def z424 : W := mkw 0xc077dc109f6f0004 0xb80efb8213ede000 0xfe7ffc79ffff8003 0xffcfff8f3ffff000

def z425 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xffffff800ffffc07 0xbffffff001ffff80

def z426 : W := mkw 0x00008400082a0000 0x0000108001054000 0x60019c00000a0000 0x0c00338000014000

def z427 : W := mkw 0x245c0f7895f26b0a 0xa48b81ef12be4d61 0xdffc1ff83ff27f1f 0xbbff83ff07fe4fe3

def z428 : W := mkw 0x802384000a2e0000 0x100470800145c000 0x7e679c000e7e0003 0x8fccf38001cfc000

def z429 : W := mkw 0x080000000080c230 0x0100000000101846 0x771a6000018fc3ff 0x8ee34c000031f87f

def z430 : W := mkw 0x7454dc18dd7b318c 0xae8a9b831baf6631 0xfa1dfc79f9fbb39e 0xff43bf8f3f3f7673

def z431 : W := mkw 0x002b22c720000003 0x00056458e4000000 0xfefbe3c7f0000000 0x7fdf7c78fe000000

def z432 : W := mkw 0x0008224220000003 0x0001044844000000 0x041a620600000000 0x00834c40c0000000

def z433 : W := mkw 0x20f759bd95502904 0xe41eeb37b2aa0520 0x08e59db9ce703c00 0x211cb3b739ce0780

def z434 : W := mkw 0x98fffbf7fa8cd6f7 0xd31fff7eff519ade 0xffffffffff8fffff 0xfffffffffff1ffff

def z435 : W := mkw 0x10000085400014c0 0x02000010a8000298 0x00000007c00000e0 0x40000000f800001c

def z436 : W := mkw 0x900080004a0c14c0 0x1200100009418298 0xa70202060e0c7ce5 0xd4e04040c1c18f9c

def z437 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xdffc63f83ff3ff1f 0xbbff8c7f07fe7fe3

def z438 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x68059c39f87a3098 0x6d00b3873f0f4613

def z439 : W := mkw 0xc077500007450004 0x380eea0000e8a000 0x1e7e60000ff58003 0x83cfcc0001feb000

def z440 : W := mkw 0x0054000005400000 0x200a800000a80000 0x9ffc03800ff07c07 0xb3ff807001fe0f80

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000403000039c 0x5000000806000073

def z442 : W := mkw 0x00ab2bf7b0000003 0xc015657ef6000000 0xaee383fff0000000 0x75dc707ffe000000

def z443 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x80000079f87a339e 0xf000000f3f0f4673

def z444 : W := mkw 0xc8fffff7bfefc237 0xf91ffffef7fdf846 0xffffffffffffc3ff 0xfffffffffffff87f

def z445 : W := mkw 0x3c00840848baf3b8 0x0780108109175e77 0x0100000009fff3ff 0x80200000013ffe7f

def z446 : W := mkw 0x1000800048081080 0x0200100009010210 0xfa018041f80a339e 0xff4030083f014673

def z447 : W := mkw 0x080000000080c230 0x0100000000101846 0x010000000185c061 0x002000000030b80c

def z448 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0x9efd9ff9c0000000 0x33dfb3ff38000000

def z449 : W := mkw 0x902380004a0c14c0 0x1204700009418298 0x2f6380000e0c7ce5 0x85ec700001c18f9c

def z450 : W := mkw 0x085c236225c0ca33 0x210b846c44b81946 0x05fa63860785cc61 0x00bf4c70c0f0b98c

def z451 : W := mkw 0x00ff7bf7b5c04a07 0xe01fef7ef6b80940 0xfffffffff7804c01 0x7ffffffffef00980

def z452 : W := mkw 0xd0fffff7ff6f14c7 0xfa1ffffeffede298 0xfffffffffffffce7 0xffffffffffffff9c

def z453 : W := mkw 0x2808224a25d0eb33 0x2501044944ba1d66 0xf71a62463fffffff 0xdee34c48c7ffffff

def z454 : W := mkw 0x4000540000230004 0x08000a8000046000 0x40007c0000038000 0x08000f8000007000

def z455 : W := mkw 0x2008036800906b02 0x0401006d00120d60 0x979803f801807f07 0xb2f3007f00300fe0

def z456 : W := mkw 0x980080004a8cd6f0 0x1300100009519ade 0x010000000f8fffff 0x8020000001f1ffff

def z457 : W := mkw 0xf40084084f7f3188 0x3e80108109efe631 0x000000000fffb39f 0x8000000001fff673

def z458 : W := mkw 0x10230085400014c0 0x02046010a8000298 0xafe38387c0007ce4 0x75fc7070f8000f9c

def z459 : W := mkw 0x0800200220008031 0x0100040044001006 0xe7026206300fc0fd 0xdce04c40c601f81f

def z460 : W := mkw 0x34238c9dd83a3188 0x86847193bb074631 0xfee79ffff87a339e 0xffdcf3ffff0f4673

def z461 : W := mkw 0x24000c1890322108 0x8480018312064421 0xda041c783872331e 0xbb40838f070e4663

def z462 : W := mkw 0x8023008502040440 0x10046010a0408088 0x00e0018006000c00 0x001c003000c00180

def z463 : W := mkw 0xc023d4000a2f0004 0x18047a800145e000 0x7a07fc00087f8002 0x8f40ff80010ff000

def z464 : W := mkw 0x1000000040001080 0x0200000008000210 0x80000001c0003084 0x7000000038000610

def z465 : W := mkw 0xd023d4854a2f14c4 0x1a047a90a945e298 0xefe3ff87ce0ffce5 0xfdfc7ff0f9c1ff9c

def z466 : W := mkw 0x305c83684dd87b82 0x260b906d09bb0f70 0xbffd83f9cff87f87 0xf7ffb07f39ff0ff0

def z467 : W := mkw 0x80ff7bf7b2040447 0xd01fef7ef6408088 0xfffffffff6044c61 0x7ffffffffec0898c

def z468 : W := mkw 0x802380850a0c0000 0x10047010a1418000 0xaee38387ce0c0001 0xf5dc7070f9c18000

def z469 : W := mkw 0x080822422080c233 0x0101044844101846 0x851a62463185c3fd 0x50a34c48c630b87f

def z470 : W := mkw 0x64545c189573210c 0xac8a8b8312ae6421 0x501c7c7831f3831a 0x0a038f8f063e7063

def z471 : W := mkw 0x00ff7b72b0000007 0xc01fef6e56000000 0x7e7ffc7830000000 0x0fcfff8f06000000

def z472 : W := mkw 0x90fff3e76a0c14c7 0x521ffe7ced418298 0xaffbe387ce0c7ce5 0xf5ff7c70f9c18f9c

def z473 : W := mkw 0x2400040800322108 0x0480008100064421 0x000000000072031a 0x00000000000e4063

def z474 : W := mkw 0xe077d5280f7f2904 0x3c0efaa501efe520 0x08e59db80e703c00 0x211cb3b701ce0780

def z475 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9efc03f801f00302 0x33df807f003e0060

def z476 : W := mkw 0x00882b72b0000003 0xc011056e56000000 0x0000007830000000 0x0000000f06000000

def z477 : W := mkw 0xe07f536807d56b06 0x3c0fea6d00faad60 0x9ffe63f80ff5ff07 0xb3ffcc7f01febfe0

def z478 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x6867fc000e7f8000 0x0d0cff8001cff000

def z479 : W := mkw 0xd00084004f6f14c0 0x3a00108009ede298 0x010000000ffffce7 0x8020000001ffff9c

def z480 : W := mkw 0x8000000002040440 0x1000000000408088 0x0100000006044c61 0x0020000000c0898c

def z481 : W := mkw 0xc82bf6422aafc237 0x19057ec84555f846 0xf71bfe46318fc3ff 0xdee37fc8c631f87f

def z482 : W := mkw 0x08a37897b0008035 0xc1146f12f6001006 0x6003fc07f00f80f8 0x4c007f80fe01f01f

def z483 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa059c79f8703000 0x7f40b38f3f0e0600

def z484 : W := mkw 0xc07fd7600fef4a06 0x380ffaec01fde940 0x7fffff800fffcc03 0x8ffffff001fff980

def z485 : W := mkw 0x007f03e500000002 0x000fe07ca0000000 0xbeff83ffc0000000 0x77dff07ff8000000

def z486 : W := mkw 0x807780000f4c0000 0x300ef00001e98000 0x3e7f80000ffc0003 0x87cff00001ff8000

def z487 : W := mkw 0xd023d4854a2f14c4 0x1a047a90a945e298 0x6003fc07c00f80e0 0x4c007f80f801f01c

def z488 : W := mkw 0x0077581090000004 0x800eeb0212000000 0xfe7ffc79f0000000 0x7fcfff8f3e000000

def z489 : W := mkw 0xc07fd7600f6f0006 0x380ffaec01ede000 0xfefffff80fff8003 0xbfdfffff01fff000

def z490 : W := mkw 0x080822422080c233 0x0101044844101846 0x0018600001818000 0x00030c0000303000

def z491 : W := mkw 0xf423dc18da3f318c 0x9e847b831b47e631 0xfa07fc79f87fb39e 0xff40ff8f3f0ff673

def z492 : W := mkw 0xc0a3fc97ba2f0005 0xd8147f92f745e000 0x6003fc07f00f8000 0x4c007f80fe01f000

def z493 : W := mkw 0xb4238c9dda3e35c8 0x96847193bb47c6b9 0xfae59df9fe7a3f9e 0xff5cb3bf3fcf47f3

def z494 : W := mkw 0x882b22c72284c673 0x11056458e45098ce 0x05fa63860785cc61 0x00bf4c70c0f0b98c

def z495 : W := mkw 0x08ff73e72080c237 0x411fee7ce4101846 0xf7fa63c6318fc3ff 0xdeff4c78c631f87f

def z496 : W := mkw 0x34548d38dd7a3988 0xa68a91a71baf4731 0xfae59df9fe7a3f9e 0xff5cb3bf3fcf47f3

def z497 : W := mkw 0xb4238c9dda3e35c8 0x96847193bb47c6b9 0x08e59db9ce703c00 0x211cb3b739ce0780

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000403002031a 0x0a00000806004063

def z499 : W := mkw 0x08dc7b72b080c237 0xc11b8f6e56101846 0xf71e7e7e318fc3ff 0xdee3cfcfc631f87f

def z500 : W := mkw 0xd423dc10da2f108c 0x9a847b821b45e211 0x6003fc01f00f8098 0x4c007f803e01f013

def z501 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x1e7c00780ff00303 0x83cf800f01fe0060

def z502 : W := mkw 0x982380854a8cd6f0 0x13047010a9519ade 0xafe38387cf8fffff 0xf5fc7070f9f1ffff

def z503 : W := mkw 0x3c08ae5af8baf3bb 0x878115cb5f175e77 0xfb059e7ff87a73fe 0xff60b3cfff0f4e7f

def z504 : W := mkw 0x3000800848183180 0x0600100109030630 0xba058079c8783386 0xf740b00f390f0670

def z505 : W := mkw 0x00f751a500000004 0x401eea34a0000000 0x00e0018000000000 0x001c003000000000

def z506 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x28e38187ce0c3ce0 0x651c7030f9c1879c

def z507 : W := mkw 0xc000000007450000 0x3800000000e8a000 0x0000000007858001 0x0000000000f0b000

def z508 : W := mkw 0x080822422080c233 0x0101044844101846 0x81000246318fc3ff 0xd0200048c631f87f

def z509 : W := mkw 0xc077d4000a2f0004 0x180efa800145e000 0x7e7ffc00000f8000 0x0fcfff800001f000

def z510 : W := mkw 0x40dc7f72b5630007 0xe81b8fee56ac6000 0x501c7c7831f38002 0x0a038f8f063e7000

def z511 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x1efc01b80ff03c03 0xa3df803701fe0780

def z512 : W := mkw 0x900080854a0c14c0 0x12001010a9418298 0x81800387ce0c7ce5 0xf0300070f9c18f9c

def z513 : W := mkw 0x982ba2c76a8cd6f3 0x13057458ed519ade 0xafe383c7fe0c7ffd 0xf5fc7078ffc18fff

def z514 : W := mkw 0x34f7ddbdd83a318c 0xc69efbb7bb074631 0xfae59df9f87a339e 0xff5cb3bf3f0f4673

def z515 : W := mkw 0x0008224220000003 0x0001044844000000 0xf71a6246300c40e5 0xdee34c48c601881c

def z516 : W := mkw 0x080000000080c230 0x0100000000101846 0xf3000040318fc3ff 0xde6000080631f87f

def z517 : W := mkw 0x080000000080c230 0x0100000000101846 0xa7020206018fc3ff 0xd4e04040c031f87f

def z518 : W := mkw 0x902ba2c76a0c14c3 0x12057458ed418298 0xfffbe3c7fe0c7ce5 0xffff7c78ffc18f9c

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa018001c0000000 0x7540300038000000

def z520 : W := mkw 0xd87ff6c76fefd6f7 0x3b0ffed8edfdfade 0xffffffc7ffffffff 0xfffffff8ffffffff

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x20020006000c00e0 0x44004000c001801c

def z522 : W := mkw 0x0808a64228aac233 0x010114c845155846 0xff1ffe4639ffc3ff 0xdfe3ffc8c73ff87f

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x5018600001838002 0x0a030c0000307000

def z524 : W := mkw 0x24000c1890322108 0x8480018312064421 0xfa059c79f072031a 0x7f40b38f3e0e4063

def z525 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x50041c78387a339e 0x8a00838f070f4673

def z526 : W := mkw 0x2808236a2090eb33 0x0501046d44121d66 0xf79a63fe318fffff 0xfef34c7fc631ffff

def z527 : W := mkw 0xe477dc189f7f210c 0xbc8efb8313efe421 0x7e7ffc783fff831b 0x8fcfff8f07fff063

def z528 : W := mkw 0x0008024000804202 0x0001004800100840 0xb71a0246018c43e7 0xd6e34048c031887c

def z529 : W := mkw 0x982ba2c76a8cd6f3 0x13057458ed519ade 0xf71be247f18fc3ff 0xdee37c48fe31f87f

def z530 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x09e18181ce0c7ce5 0xa13c303039c18f9c

def z531 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x9ae401f80e703f06 0xb35c803f01ce07e0

def z532 : W := mkw 0x00fffff7b82a0007 0xc01ffffef7054000 0xfefffffff87a0002 0xffdfffffff0f4000

def z533 : W := mkw 0x90f7d9b5da0c14c4 0xd21efb36bb418298 0x08e59db9ce003c00 0x211cb3b739c00780

def z534 : W := mkw 0x0000800008080000 0x0000100001010000 0x2a01800008080000 0x8540300001010000

def z535 : W := mkw 0x00ff73e720000007 0x401fee7ce4000000 0xaefbe387c0000000 0x75df7c70f8000000

def z536 : W := mkw 0x20ff5bfd95d06b06 0xe41feb7fb2ba0d60 0x9ffd9ff9cff07f07 0xb3ffb3ff39fe0fe0

def z537 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x18fc01f80ff03f02 0x231f803f01fe07e0

def z538 : W := mkw 0xc00084000a2f0000 0x180010800145e000 0x00000000000f8000 0x000000000001f000

def z539 : W := mkw 0x0023008500000000 0x00046010a0000000 0x04e2038600000000 0x009c4070c0000000

def z540 : W := mkw 0x0054000005400000 0x200a800000a80000 0x086400000e700000 0x010c800001ce0000

def z541 : W := mkw 0x0023008500000000 0x00046010a0000000 0xafe38387ce007c05 0xf5fc7070f9c00f80

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0xa602020600000000 0x54c04040c0000000

def z543 : W := mkw 0x2000000800102100 0x0400000100020420 0xfa040078387a339e 0xff40800f070f4673

def z544 : W := mkw 0x0000081090000000 0x8000010212000000 0x80000079f0000000 0x7000000f3e000000

def z545 : W := mkw 0x0054500000000004 0x000a8a0000000000 0x501c7c0000000000 0x0a038f8000000000

def z546 : W := mkw 0x90ababf7fa0c14c3 0xd215757eff418298 0xafe383fffe0c7ce5 0xf5fc707fffc18f9c

def z547 : W := mkw 0x2c082e5ab0b2e33b 0x858105cb56165c67 0x501c7c7831f3831a 0x0a038f8f063e7063

def z548 : W := mkw 0x907f83e54a0c14c2 0x120ff07ca9418298 0xbfff83ffce0c7ce5 0xf7fff07ff9c18f9c

def z549 : W := mkw 0x902380004a0c1080 0x1204700009418210 0xae638001ce0c3085 0xf5cc700039c18610

def z550 : W := mkw 0x900080004a0c14c0 0x1200100009418298 0x8fe003800e0c7ce5 0xb1fc007001c18f9c

def z551 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfe1ffc79f9ffb39f 0xffc3ff8f3f3ff673

def z552 : W := mkw 0x907f83e54fcc5ec2 0x320ff07ca9f98bd8 0xaffb8387cf8c7ce5 0xf5ff7070f9f18f9c

def z553 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xaa038007c80c30e4 0xf5407000f901861c

def z554 : W := mkw 0x0000000000000000 0x0000000000000000 0xafe203860e0c7ce5 0xf5fc4070c1c18f9c

def z555 : W := mkw 0x20ff7bffb5d06b07 0xe41fef7ff6ba0d60 0xfefffffff1f00302 0x7fdffffffe3e0060

def z556 : W := mkw 0x20008408083a2100 0x0400108101074420 0xfa059c78087a3306 0xbf40b38f010f4660

def z557 : W := mkw 0x8023008502040440 0x10046010a0408088 0xa7e20386060c4ce5 0xd4fc4070c0c1899c

def z558 : W := mkw 0x007f724220000007 0x000fee4844000000 0xfe7ffe4630000000 0x5fcfffc8c6000000

def z559 : W := mkw 0x00882bf7b0000003 0xc011057ef6000000 0xf69a63fff0000000 0x7ed34c7ffe000000

def z560 : W := mkw 0x34080b78d0907b8a 0x8681016f1a120f71 0x818003f9f0007f9c 0x7030007f3e000ff3

def z561 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x84fa63fff0000000 0x709f4c7ffe000000

def z562 : W := mkw 0x0008224220000003 0x0001044844000000 0x8000024630000000 0x50000048c6000000

def z563 : W := mkw 0x00a3589590000004 0xc0146b12b2000000 0x00019c01c0000000 0x0000338038000000

def z564 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x2ee38181ce0c3c01 0xa5dc703039c18780

def z565 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xe0019c79f00a339c 0x7c00338f3e014673

def z566 : W := mkw 0x005c036005c04a02 0x200b806c00b80940 0x1ffc03800ff04c03 0x83ff807001fe0980

def z567 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7efffd81cfffbc03 0xafdfffb039fff780

def z568 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xaee38387c00c00e0 0x75dc7070f801801c

def z569 : W := mkw 0xc07f536007c54a06 0x380fea6c00f8a940 0x05fa63800785cc01 0x00bf4c7000f0b980

def z570 : W := mkw 0x005c036005400002 0x200b806c00a80000 0x9efc03f80ff00003 0xb3df807f01fe0000

def z571 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xff7ffe060fffc0e7 0xdfefffc0c1fff81c

def z572 : W := mkw 0x080822422080c233 0x0101044844101846 0xf2186040318b839e 0xde430c0806317073

def z573 : W := mkw 0x34fffffffdfa7b8f 0xe69fffffffbf4f71 0xfffffffffffa7f9f 0xffffffffffff4ff3

def z574 : W := mkw 0x24dc7f7ab032210f 0xc49b8fef56064421 0x501c7c783072031a 0x0a038f8f060e4063

def z575 : W := mkw 0x205c036800906b02 0x040b806d00120d60 0x9ffc03f800007f04 0x33ff807f00000fe0

def z576 : W := mkw 0x3c08ae5af8baf3bb 0x878115cb5f175e77 0xfa1dfc79f9fbb39e 0xff43bf8f3f3f7673

def z577 : W := mkw 0x00008400082a0000 0x0000108001054000 0xfa059c40387a039e 0xdf40b388070f4073

def z578 : W := mkw 0x90fffbf7fa0c14c7 0xd21fff7eff418298 0xfefffffff00c00e0 0x7fdffffffe01801c

def z579 : W := mkw 0x080822422080c233 0x0101044844101846 0x97180246318043ff 0xd2e30048c630087f

def z580 : W := mkw 0x34008c9dd83a35c8 0x86801193bb0746b9 0xfb859ffff87a7ffe 0xff70b3ffff0f4fff

def z581 : W := mkw 0x2000081890102100 0x8400010312020420 0xfa059c79f8703306 0xff40b38f3f0e0660

def z582 : W := mkw 0x0023008500000000 0x00046010a0000000 0x20038007c0000000 0x44007000f8000000

def z583 : W := mkw 0x10000000400014c0 0x0200000008000298 0x0100000000007ce4 0x0020000000000f9c

def z584 : W := mkw 0xbc2baedffabef7fb 0x978575dbff57deff 0xffffffffffffffff 0xffffffffffffffff

def z585 : W := mkw 0xa07f83680fdc6b02 0x340ff06d01fb8d60 0xbfff83f80ffc7f07 0xb7fff07f01ff8fe0

def z586 : W := mkw 0xd077d4004f6f14c4 0x3a0efa8009ede298 0x7f7ffc000ffffce7 0x8fefff8001ffff9c

def z587 : W := mkw 0x34008408483a3188 0x0680108109074631 0x9a040078087a339e 0xb340800f010f4673

def z588 : W := mkw 0x20ff7bffb0906b07 0xc41fef7ff6120d60 0xfffffffff0007f04 0x7ffffffffe000fe0

def z589 : W := mkw 0x08882bf7b080c233 0xc111057ef6101846 0xf79a63fff18fc3ff 0xfef34c7ffe31f87f

def z590 : W := mkw 0x605c576805f36b06 0x2c0b8aed00be6d60 0x501c7c7801f38302 0x0a038f8f003e7060

def z591 : W := mkw 0xb05c83684fdc7fc2 0x360b906d09fb8ff8 0x9ffc03f80ffc7fe7 0xb3ff807f01ff8ffc

def z592 : W := mkw 0x2008036805d06b02 0x2401006d00ba0d60 0x818003f80ff07f07 0xb030007f01fe0fe0

def z593 : W := mkw 0xb4238c9dda3e35c8 0x96847193bb47c6b9 0xfa079c7ff87e33fe 0xff40f38fff0fc67f

def z594 : W := mkw 0x3477dc18d83a318c 0x868efb831b074631 0xfe7ffc79f87a339e 0xffcfff8f3f0f4673

def z595 : W := mkw 0x08ab7ad7b080c237 0xc1156f5af6101846 0xf71bfe47f18fc3ff 0xdee37fc8fe31f87f

def z596 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x7a059c39c87a3002 0xaf40b387390f4600

def z597 : W := mkw 0x34882bfff010318b 0xc691057ffe020631 0x808003fff000339c 0x7010007ffe000673

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x81000206000040e4 0x50200040c000081c

def z599 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x88059c79f870339c 0x7100b38f3f0e0673

def z600 : W := mkw 0x10ff7bf7f00014c7 0xc21fef7efe000298 0xfffffffff0007ce4 0x7ffffffffe000f9c

def z601 : W := mkw 0x005c036000000002 0x000b806c00000000 0x04f8038000000000 0x009f007000000000

def z602 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xaee38387ce003c00 0x75dc7070f9c00780

def z603 : W := mkw 0x34088f78d8ba7b8a 0x868111ef1b174f71 0xfb859ff9f87a7f9e 0xff70b3ff3f0f4ff3

def z604 : W := mkw 0x24000c1890322108 0x8480018312064421 0xf2041c78307a039e 0xde40838f060f4073

def z605 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x2e638007ce0c00e1 0xc5cc7000f9c1801c

def z606 : W := mkw 0x2054000805502100 0x240a800100aa0420 0x9e7c00780ff03307 0xb3cf800f01fe0660

def z607 : W := mkw 0x0023008500000000 0x00046010a0000000 0x08e18181c0000000 0x211c303038000000

def z608 : W := mkw 0x2000000805d06b00 0x2400000100ba0d60 0x9b0400780ff07f07 0xb360800f01fe0fe0

def z609 : W := mkw 0x9823a0876a0c94f1 0x13047410ed41929e 0xefe3e387fe0ffcfd 0xfdfc7c70ffc1ff9f

def z610 : W := mkw 0x802380000a0c0000 0x1004700001418000 0x20038000000c0000 0x0400700000018000

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000000300a0098 0x4c00000006014013

def z612 : W := mkw 0x080822422080c233 0x0101044844101846 0x971a62460185c367 0x92e34c48c030b86c

def z613 : W := mkw 0x080822422080c233 0x0101044844101846 0xd71862403183c31f 0x9ae30c4806307863

def z614 : W := mkw 0x20882bffb0906b03 0xc411057ff6120d60 0x818003fff0007f04 0x7030007ffe000fe0

def z615 : W := mkw 0xe077d4080fff6b04 0x3c0efa8101ffed60 0x7f7ffc000fffff07 0x8fefff8001ffffe0

def z616 : W := mkw 0x0008024000804202 0x0001004800100840 0xf7180240318a439f 0xdee3004806314873

def z617 : W := mkw 0xc07ff6422f6f0007 0x380ffec845ede000 0xfe7ffe463fff8003 0xdfcfffc8c7fff000

def z618 : W := mkw 0xe077d4080f7f2104 0x3c0efa8101efe420 0xfe7ffc780fffb307 0xbfcfff8f01fff660

def z619 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x89e18387ce007ce4 0x713c3070f9c00f9c

def z620 : W := mkw 0xe07fd7680fff6b06 0x3c0ffaed01ffed60 0x9ffd9ff80ff07f07 0xb3ffb3ff01fe0fe0

def z621 : W := mkw 0x20ff73ef25d06b07 0x641fee7de4ba0d60 0x9ffe63fe0ff07f07 0xb3ffcc7fc1fe0fe0

def z622 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x8fe18381ce007c05 0xb1fc307039c00f80

def z623 : W := mkw 0x00ab7bf7b0000007 0xc0156f7ef6000000 0xe083fffff0000000 0x7c107ffffe000000

def z624 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x2e679c000e7c0001 0x85ccf38001cf8000

def z625 : W := mkw 0x0054000005400000 0x200a800000a80000 0x0478000007800001 0x008f000000f00000

def z626 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xaae18181ce083c84 0xf55c303039c10790

def z627 : W := mkw 0x005c024005c04202 0x200b804800b80840 0x9f7c02400ff04307 0x93ef804801fe0860

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x60026000000f8000 0x0c004c000001f000

def z629 : W := mkw 0xe00084080fff6b00 0x3c00108101ffed60 0x010000000fffff07 0x8020000001ffffe0

def z630 : W := mkw 0x14008400482a1088 0x0280108009054211 0x00000000000a0098 0x0000000000014013

def z631 : W := mkw 0x34088e58d8ba738a 0x868111cb1b174e71 0xff1d9e79f9fa739f 0xffe3b3cf3f3f4e73

def z632 : W := mkw 0x00ff73e720000007 0x401fee7ce4000000 0x7effff8600000000 0x0fdffff0c0000000

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x26020000000c0001 0x84c0400000018000

def z634 : W := mkw 0x0008024000804202 0x0001004800100840 0xf71a6240018fc307 0x9ee34c480031f860

def z635 : W := mkw 0x008823e720000003 0x4011047ce4000000 0x0080038600000000 0x00100070c0000000

def z636 : W := mkw 0x3c5caf7afdfafbbb 0xa78b95ef5fbf5f77 0xffffffffffffffff 0xffffffffffffffff

def z637 : W := mkw 0x0008024000000002 0x0001004800000000 0x9618024000000000 0x12c3004800000000

def z638 : W := mkw 0x085c224225c0c233 0x210b844844b81846 0xff7e62463fffc3ff 0xdfefcc48c7fff87f

def z639 : W := mkw 0x0077500005400004 0x200eea0000a80000 0x7e7ffc000ff00003 0x8fcfff8001fe0000

def z640 : W := mkw 0x00ff7bf7b5400007 0xe01fef7ef6a80000 0xfefffffffff00003 0xffdffffffffe0000

def z641 : W := mkw 0x0000000005400000 0x2000000000a80000 0x000000000ff00003 0x8000000001fe0000

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x8ee0038000000000 0x31dc007000000000

def z643 : W := mkw 0x0054000000000000 0x000a800000000000 0x1e7c000000000000 0x03cf800000000000

def z644 : W := mkw 0x900080004a0c14c0 0x1200100009418298 0xab018001ce0c7ce5 0xf560300039c18f9c

def z645 : W := mkw 0x485c764225e3c237 0x290b8ec844bc7846 0x501c7c4031f3831a 0x0a038f88063e7063

def z646 : W := mkw 0x3488affff83a318b 0xc69115ffff074631 0xfa859ffff87a339e 0xff50b3ffff0f4673

def z647 : W := mkw 0x9823a0876a0c94f1 0x13047410ed41929e 0x6003e007f00f80f8 0x4c007c00fe01f01f

def z648 : W := mkw 0x205c87680dfa6b02 0x240b90ed01bf4d60 0xfffd9ff80ffa7f07 0xbfffb3ff01ff4fe0

def z649 : W := mkw 0x1023808548081080 0x02047010a9010210 0xaee38387c8083084 0xf5dc7070f9010610

def z650 : W := mkw 0x34f7ddbdd83a318c 0xc69efbb7bb074631 0x08e59db9c8703000 0x211cb3b7390e0600

def z651 : W := mkw 0x005c236220000003 0x000b846c44000000 0xfefe63fe30000000 0x7fdfcc7fc6000000

def z652 : W := mkw 0x14fffff7f82a108f 0xc29ffffeff054211 0xfefffffff00a0098 0x7fdffffffe014013

def z653 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x54fe7ffe30000000 0x0a9fcfffc6000000

def z654 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9a1c007809f03306 0xb343800f013e0660

def z655 : W := mkw 0x14000810d0001088 0x828001021a000211 0x00000001f0000098 0x400000003e000013

def z656 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0xf61e7e7e30000000 0x5ec3cfcfc6000000

def z657 : W := mkw 0x080822422080c233 0x0101044844101846 0x551a62463187c37b 0x0aa34c48c630f86f

def z658 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7a659c000e7a0002 0x8f4cb38001cf4000

def z659 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xaa059c39c8783084 0xf540b387390f0610

def z660 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x0004003800700000 0x00008007000e0000

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a04000008700002 0x83408000010e0000

def z662 : W := mkw 0x80fffbf7ba0c0007 0xd01fff7ef7418000 0xfefffffffe0c0001 0xffdfffffffc18000

def z663 : W := mkw 0x2000000805d06b00 0x2400000100ba0d60 0x8fe003800ff07f07 0xb1fc007001fe0fe0

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0x1618000001800003 0x82c3000000300000

def z665 : W := mkw 0x20ff7bffb0102107 0xc41fef7ff6020420 0xfefffffff8703306 0xffdfffffff0e0660

def z666 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x15fc03f807f04f03 0x02bf807f00fe09e0

def z667 : W := mkw 0x94238c95da2e14c8 0x92847192bb45c299 0xefe39f87fe0e7cfd 0xfdfc73f0ffc1cf9f

def z668 : W := mkw 0x0054012005400800 0x200a802400a80100 0x00e0018006000c00 0x001c003000c00180

def z669 : W := mkw 0x807f03e507c44e42 0x300fe07ca0f889c8 0x05fa038607844c61 0x00bf4070c0f0898c

def z670 : W := mkw 0x080822422080c233 0x0101044844101846 0xa71a6206018dc0e5 0xd4e34c40c031b81c

def z671 : W := mkw 0x1c00ac12f82a90b9 0x838015825f055217 0x6003fc07f00f80f8 0x4c007f80fe01f01f

def z672 : W := mkw 0xb07f83ed4fdc7fc2 0x360ff07da9fb8ff8 0x9ffd83f9cff07f07 0xb3ffb07f39fe0fe0

def z673 : W := mkw 0xe07fd7680fff6b06 0x3c0ffaed01ffed60 0x7e7ffc780fff8303 0x8fcfff8f01fff060

def z674 : W := mkw 0x20dc7b7ab5d06b07 0xe41b8f6f56ba0d60 0x501c7c7831f00302 0x0a038f8f063e0060

def z675 : W := mkw 0x800080000a0c0000 0x1000100001418000 0x000000000e0c0001 0x8000000001c18000

def z676 : W := mkw 0x20dc7b7ab5d06b07 0xe41b8f6f56ba0d60 0xdffc7ff83ff07f07 0xbbff8fff07fe0fe0

def z677 : W := mkw 0xc023500002050004 0x18046a000040a000 0x0002600000058000 0x00004c000000b000

def z678 : W := mkw 0x8023008502040440 0x10046010a0408088 0x8fe203860e047c65 0xb1fc4070c1c08f8c

def z679 : W := mkw 0xc077500007450004 0x380eea0000e8a000 0x767a6000078f8003 0x8ecf4c0000f1f000

def z680 : W := mkw 0x005484000d6a0000 0x200a908001ad4000 0x7e7d9c000ffa0003 0x8fcfb38001ff4000

def z681 : W := mkw 0xc877f4022f6f8035 0x390efe8045edf006 0x7e7ffc063fff80fb 0xcfcfff80c7fff01f

def z682 : W := mkw 0x2000000805d06b00 0x2400000100ba0d60 0x0000000001f00302 0x00000000003e0060

def z683 : W := mkw 0x20dc2bffb5d06b03 0xe41b857ff6ba0d60 0x9ffc03fffff07f07 0xf3ff807ffffe0fe0

def z684 : W := mkw 0xb02b83ed4a9c7fc2 0x1605707da9538ff8 0xafe383ffce0c7fe5 0xf5fc707ff9c18ffc

def z685 : W := mkw 0x34ff7bfff010318f 0xc69fef7ffe020631 0xfefffffff000339c 0x7fdffffffe000673

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000000000c40e5 0x802000000001881c

def z687 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x08059c39c87a339e 0xa100b387390f4673

def z688 : W := mkw 0x90a3f897fa0c14c5 0xd2147f12ff418298 0xefe3ff87fe0c7ce5 0xfdfc7ff0ffc18f9c

def z689 : W := mkw 0x9077d0854a0c14c4 0x120efa10a9418298 0xffffff87ce0c7ce5 0xfffffff0f9c18f9c

def z690 : W := mkw 0x080822422080c233 0x0101044844101846 0xe1026246300fc3fc 0x5c204c48c601f87f

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0xf61a6040318f839f 0xdec34c080631f073

def z692 : W := mkw 0x00008c10982a0000 0x8000118213054000 0xfa059c79f87a0002 0xff40b38f3f0f4000

def z693 : W := mkw 0x882ba2422a8cc233 0x1105744845519846 0xff7be2463f8fc3ff 0xdfef7c48c7f1f87f

def z694 : W := mkw 0x005c036005c04a02 0x200b806c00b80940 0x97f803c007804f07 0x92ff007800f009e0

def z695 : W := mkw 0x34000818d0103188 0x868001031a020631 0xf2000079f00a339e 0xfe40000f3e014673

def z696 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xf71e627e31ffc3ff 0xdee3cc4fc63ff87f

def z697 : W := mkw 0x00008400082a0000 0x0000108001054000 0x08059c0008700000 0x0100b380010e0000

def z698 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0xdefc7ff830000000 0x3bdf8fff06000000

def z699 : W := mkw 0x34548c18dd7a3188 0xa68a91831baf4631 0xfe7d9c79fffa339f 0xffcfb38f3fff4673

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180038000007c04 0x3030007000000f80

def z701 : W := mkw 0x80ff73e722040447 0x501fee7ce4408088 0x05fa638606044c61 0x00bf4c70c0c0898c

def z702 : W := mkw 0x10000085400014c0 0x02000010a8000298 0x00800181c0003c00 0x2010003038000780

def z703 : W := mkw 0x14008c10d82a1088 0x828011821b054211 0xfa059c79f00a0098 0x7f40b38f3e014013

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x8700020000004005 0x90e0004000000800

def z705 : W := mkw 0x080020022080c231 0x0100040044101846 0x61026006318fc3ff 0xcc204c00c631f87f

def z706 : W := mkw 0xc023d4000f6f0004 0x38047a8001ede000 0x6003fc000fff8003 0x8c007f8001fff000

def z707 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x2de38387ce0c7ce1 0x65bc7070f9c18f9c

def z708 : W := mkw 0x00ff7bf7b5400007 0xe01fef7ef6a80000 0xfffffffffff07c07 0xfffffffffffe0f80

def z709 : W := mkw 0xf40084084f7f3188 0x3e80108109efe631 0x000000000e703000 0x0000000001ce0600

def z710 : W := mkw 0x20a3789fb5d06b05 0xe4146f13f6ba0d60 0x6103fc07fff07f07 0xcc207f80fffe0fe0

def z711 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x787ffc000fff8002 0x0f0fff8001fff000

def z712 : W := mkw 0xc00084000f6f0000 0x3800108001ede000 0x7e1ffc000fff8003 0x8fc3ff8001fff000

def z713 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa059c79f9ffb39f 0xff40b38f3f3ff673

def z714 : W := mkw 0x34008408483a3188 0x0680108109074631 0x60000000387a339e 0xcc000000070f4673

def z715 : W := mkw 0x10008400482a1080 0x0200108009054210 0xff1ffe07c9fff0e7 0xffe3ffc0f93ffe1c

def z716 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0x0dffffbfc185c061 0x21bffff7f830b80c

def z717 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffe63fe3ff5ff67 0xffffcc7fc7febfec

def z718 : W := mkw 0xc87ff6422fefc237 0x390ffec845fdf846 0x89659e463e7043fc 0x512cb3c8c7ce087f

def z719 : W := mkw 0xf4775818d755318c 0xbe8eeb031aeaa631 0x847a6079f785b39d 0x708f4c0f3ef0b673

def z720 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff1858001 0x7fdffffffe30b000

def z721 : W := mkw 0x080823622080c233 0x0101046c44101846 0xf79a63fe318fc3ff 0xfef34c7fc631f87f

def z722 : W := mkw 0x90dcfb72fa0c14c7 0xd21b9f6e5f418298 0x511c7c783e0c7ce5 0x8a238f8f07c18f9c

def z723 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xe4fbfffff0000000 0x7c9f7ffffe000000

def z724 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfefffffff1800302 0x7fdffffffe300060

def z725 : W := mkw 0x34008408483a3188 0x0680108109074631 0x010000000e7a7f9f 0x8020000001cf4ff3

def z726 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x08e401b80ff03f02 0x211c803701fe07e0

def z727 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0x9ffe63fe0ff07f07 0xb3ffcc7fc1fe0fe0

def z728 : W := mkw 0x0000081090000000 0x8000010212000000 0xff079e7ff00c40e5 0xffe0f3cffe01881c

def z729 : W := mkw 0x34008408483a3188 0x0680108109074631 0x00000000007a039a 0x00000000000f4073

def z730 : W := mkw 0xb40084084a3e35c8 0x168010810947c6b9 0x000000000e703c00 0x0000000001ce0780

def z731 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xe8059c79f87a339c 0x7d00b38f3f0f4673

def z732 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xda059c79f872331e 0xbb40b38f3f0e4663

def z733 : W := mkw 0x28dc7b7ab5d0eb37 0xe51b8f6f56ba1d66 0x501c7c7831f3831a 0x0a038f8f063e7063

def z734 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc0001ff8002 0x0fcfff80003ff000

def z735 : W := mkw 0x34008408483a3188 0x0680108109074631 0x8fe003800e7a7f9f 0xb1fc007001cf4ff3

def z736 : W := mkw 0x2854212a2550a931 0x250a842544aa1526 0x68e661be3e7fbcf8 0x6d1ccc37c7cff79f

def z737 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffd9ff80ff07f07 0xbfffb3ff01fe0fe0

def z738 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x721c7c0001fb8002 0x8e438f80003f7000

def z739 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfefffffff0000318 0x7fdffffffe000063

def z740 : W := mkw 0xc077d4850f6f0444 0x380efa90a1ede088 0x7e7ffc060fff8063 0x8fcfff80c1fff00c

def z741 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0x48e5fdb9f0000000 0x291cbfb73e000000

def z742 : W := mkw 0x3408a64a683a318b 0x068114c94d074631 0xf61a6246387a339e 0xdec34c48c70f4673

def z743 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfb059c79fe7a7f9f 0xff60b38f3fcf4ff3

def z744 : W := mkw 0xd077d4854f6f1084 0x3a0efa90a9ede210 0xfeffff87cfffb087 0xffdffff0f9fff610

def z745 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xd8fdfffff0000000 0x7b1fbffffe000000

def z746 : W := mkw 0x902384854a2e14c0 0x12047090a945c298 0xffffff87cffffce7 0xfffffff0f9ffff9c

def z747 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x7a059c79f87a039a 0xcf40b38f3f0f4073

def z748 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff183c31f 0xfffffffffe307863

def z749 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x0cfffdb9c0000000 0x219fffb738000000

def z750 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff18fc0e7 0xfffffffffe31f81c

def z751 : W := mkw 0x982ba2c76a8cd6f3 0x13057458ed519ade 0x58f9e1c1ff83bf1a 0x2b1f3c383ff077e3

def z752 : W := mkw 0x5054d4004d6b1084 0x2a0a9a8009ad6210 0xfa1dfc01c9fbb086 0xff43bf80393f7610

def z753 : W := mkw 0x080020022080c231 0x0100040044101846 0x771a6006318fc3ff 0xcee34c00c631f87f

def z754 : W := mkw 0xd023d4854a2f14c4 0x1a047a90a945e298 0xafe39f87ce0c7ce5 0xf5fc73f0f9c18f9c

def z755 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfae59df9fe7a3f9e 0xff5cb3bf3fcf47f3

def z756 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfa1ffc7ff0000000 0x7f43ff8ffe000000

def z757 : W := mkw 0x00008c10982a0000 0x8000118213054000 0xfa059c79f87a039e 0xff40b38f3f0f4073

def z758 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffc03fe3fffffff 0xf3ff807fc7ffffff

def z759 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xfeffffbfc0000000 0x7fdffff7f8000000

def z760 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0xe003fc7ff0000000 0x7c007f8ffe000000

def z761 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xe8e7fffff0000000 0x7d1cfffffe000000

def z762 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc000fff8087 0xdfcfff8001fff010

def z763 : W := mkw 0x08a37897b0008035 0xc1146f12f6001006 0xfa07fc7ff00f83fe 0xff40ff8ffe01f07f

def z764 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc000ff38002 0x0fcfff8001fe7000

def z765 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff1800003 0xffdffffffe300000

def z766 : W := mkw 0x28882bffb090eb33 0xc511057ff6121d66 0x818003fff0007ffc 0x7030007ffe000fff

def z767 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x0de38387ce0c7ce5 0xa1bc7070f9c18f9c

def z768 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa079c7ff87e33fe 0xff40f38fff0fc67f

def z769 : W := mkw 0x00ff7bf7b5c04207 0xe01fef7ef6b80840 0xfffffffffff04307 0xfffffffffffe0860

def z770 : W := mkw 0x08dc7b72b080c237 0xc11b8f6e56101846 0xfa1dfc79f18b839e 0xff43bf8f3e317073

def z771 : W := mkw 0xb4008c18da3e35c8 0x968011831b47c6b9 0xfa059c79fe7a3f9e 0xff40b38f3fcf47f3

def z772 : W := mkw 0x08f759b59080c234 0xc11eeb36b2101846 0x09e59db9c18fc3ff 0xa13cb3b73831f87f

def z773 : W := mkw 0x9023d0854a0c14c4 0x12047a10a9418298 0xefe3ff87ce0c7ce5 0xfdfc7ff0f9c18f9c

def z774 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xffffffc7ffffffff 0xfffffff8ffffffff

def z775 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x9efc01f80ff03f07 0xb3df803f01fe07e0

def z776 : W := mkw 0xd023d4854a2f14c4 0x1a047a90a945e298 0xffe7ff87ce7ffce7 0xfffcfff0f9cfff9c

def z777 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff1838002 0x7fdffffffe307000

def z778 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffe63fe0fffffff 0xb3ffcc7fc1ffffff

def z779 : W := mkw 0x08ff7bf7b5c0ca37 0xe11fef7ef6b81946 0xfffffffff785cc61 0x7ffffffffef0b98c

def z780 : W := mkw 0x2008036800906b02 0x0401006d00120d60 0x9fe403f80e707f07 0xb3fc807f01ce0fe0

def z781 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x587dfc000fff8003 0x8b0fbf8001fff000

def z782 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff00f8000 0x7fdffffffe01f000

def z783 : W := mkw 0x080822422080c233 0x0101044844101846 0x851a6246318fc3ff 0xd0a34c48c631f87f

def z784 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0xf21c7c4031fb839e 0xde438f88063f7073

def z785 : W := mkw 0x0023089590000000 0x80046112b2000000 0xaee79fbfc0000000 0x75dcf3f7f8000000

def z786 : W := mkw 0x0023089590000000 0x80046112b2000000 0xfae59df9f0000000 0x7f5cb3bf3e000000

def z787 : W := mkw 0xa4230c9d92362548 0x94846193b246c4a9 0x55e61ffe36764f7b 0x0abcc3ffc6cec9ef

def z788 : W := mkw 0xc054d4000f6f0004 0x380a9a8001ede000 0x5e7c7c000fff8003 0x8bcf8f8001fff000

def z789 : W := mkw 0x24008c18983a2108 0x8480118313074421 0xfa059c79f87a031a 0xff40b38f3f0f4063

def z790 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x0c7ffc000fff8003 0x818fff8001fff000

def z791 : W := mkw 0x90230085420414c0 0x12046010a8408298 0x81e00387c6007ce4 0x703c0070f8c00f9c

def z792 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff6004c01 0x7ffffffffec00980

def z793 : W := mkw 0x0000081090000000 0x8000010212000000 0x70059c79f0000000 0x4e00b38f3e000000

def z794 : W := mkw 0xc077d5200f6f0804 0x380efaa401ede100 0x7efffd800fff8c03 0x8fdfffb001fff180

def z795 : W := mkw 0xc8ff7bf7b7c5c237 0xf91fef7ef6f8b846 0xfffffffff785c061 0x7ffffffffef0b80c

def z796 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x09e401b80e707f04 0x213c803701ce0fe0

def z797 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x501e7c0001f78002 0x0a03cf80003ef000

def z798 : W := mkw 0x3c08ae5af8baf3bb 0x878115cb5f175e77 0x0d1ffe3fc9f5f061 0x21a3ffc7f93ebe0c

def z799 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x68e59db9f0000000 0x6d1cb3b73e000000

def z800 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x501dfc79f0000000 0x0a03bf8f3e000000

def z801 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0x701ffc7ff18f83fa 0x4e03ff8ffe31f07f

def z802 : W := mkw 0x00ab7bf7b0000007 0xc0156f7ef6000000 0x80819ffff0000000 0x701033fffe000000

def z803 : W := mkw 0x50545485456314c4 0x2a0a8a90a8ac6298 0xd19c7f87c1f3fce6 0x7a338ff0f83e7f9c

def z804 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x8fe59fb9ce007c05 0xb1fcb3f739c00f80

def z805 : W := mkw 0x345c87684dfa7b8a 0x268b90ed09bf4f71 0x05f803800ffa7f9f 0x80bf007001ff4ff3

def z806 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x8ffc03b80ff07c05 0xb1ff807701fe0f80

def z807 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xbfe783ffce0c7ce5 0xf7fcf07ff9c18f9c

def z808 : W := mkw 0x34008408483a3188 0x0680108109074631 0x00000000000a339c 0x0000000000014673

def z809 : W := mkw 0xb40084084a3e3188 0x168010810947c631 0x000000000e7e339f 0x8000000001cfc673

def z810 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x5e7c7c0001f38002 0x0bcf8f80003e7000

def z811 : W := mkw 0x3c0084084dfafbb8 0x2780108109bf5f77 0x010000000fffffff 0x8020000001ffffff

def z812 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff187c37b 0x7ffffffffe30f86f

def z813 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x9efc03f80ff03c03 0xb3df807f01fe0780

def z814 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f00a0098 0x7f40b38f3e014013

def z815 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfb859ff9f87a7f9e 0xff70b3ff3f0f4ff3

def z816 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0xfffc03f83fffffff 0xffff807f07ffffff

def z817 : W := mkw 0x145c8f70ddea5a8a 0xa28b91ee1bbd4b51 0x65f99f81f78a4c99 0x4cbf33f03ef14993

def z818 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xffe79ffffe7e7fff 0xfffcf3ffffcfcfff

def z819 : W := mkw 0x80f759b592040444 0xd01eeb36b2408088 0x08e59db9c6000c00 0x211cb3b738c00180

def z820 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xaffbe387cf8dfce5 0xf5ff7c70f9f1bf9c

def z821 : W := mkw 0x0077d400082a0004 0x000efa8001054000 0x7e7ffc0009ff8003 0x8fcfff80013ff000

def z822 : W := mkw 0x00a3589590000004 0xc0146b12b2000000 0xfa059c79f0000000 0x7f40b38f3e000000

def z823 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0x7e7ffc000fffb087 0x8fcfff8001fff610

def z824 : W := mkw 0x4077548505630004 0x280eea90a0ac6000 0xfeffff87c1f38002 0x7fdffff0f83e7000

def z825 : W := mkw 0x2008024800906302 0x0401004900120c60 0x9ffc03f80ff07f07 0xb3ff807f01fe0fe0

def z826 : W := mkw 0xb07f83ed4fdc7fc2 0x360ff07da9fb8ff8 0x301f807fc1fc03e2 0x4603f00ff83f807c

def z827 : W := mkw 0x00ab2bf7b0000003 0xc015657ef6000000 0xfee79ffff0000000 0x7fdcf3fffe000000

def z828 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffc03f83ff07f1f 0xb3ff807f07fe0fe3

def z829 : W := mkw 0x34008408483a3188 0x0680108109074631 0x000000000872331a 0x00000000010e4663

def z830 : W := mkw 0xf477d4084f7f318c 0x3e8efa8109efe631 0x047a60000fffb39f 0x808f4c0001fff673

def z831 : W := mkw 0xe02bd7680abf6b06 0x1c057aed0157ed60 0xe183fff8000fff04 0x3c307fff0001ffe0

def z832 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x5e7dfc000ff38003 0x8bcfbf8001fe7000

def z833 : W := mkw 0x942384854a2e14c8 0x12847090a945c299 0xafe38387ce0e7cfd 0xf5fc7070f9c1cf9f

def z834 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0xfffe63f80fffffff 0xbfffcc7f01ffffff

def z835 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x09e403b80e707c00 0x213c807701ce0f80

def z836 : W := mkw 0x80f759b592040444 0xd01eeb36b2408088 0x0de79fbfc6044c61 0x21bcf3f7f8c0898c

def z837 : W := mkw 0x08ab7bf7b080c237 0xc1156f7ef6101846 0xf79bfffff18fc3ff 0xfef37ffffe31f87f

def z838 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc403fff8003 0xdfcfff8807fff000

def z839 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0x9ffc03fe3ff07f07 0xf3ff807fc7fe0fe0

def z840 : W := mkw 0xc088aff7bf6f0003 0xf81115fef7ede000 0x808003ffffff8003 0xf010007ffffff000

def z841 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xdefdfff9f0000000 0x3bdfbfff3e000000

def z842 : W := mkw 0x080822422080c233 0x0101044844101846 0xff1be247f18fc3ff 0xffe37c48fe31f87f

def z843 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc000fff839f 0x8fcfff8001fff073

def z844 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x9effffffc0000000 0x33dffffff8000000

def z845 : W := mkw 0x4054d4000d6b0004 0x280a9a8001ad6000 0x581dfc0009f38002 0x0b03bf80013e7000

def z846 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0xfe7ffc41ffffb39f 0xffcfff883ffff673

def z847 : W := mkw 0x2000000800102100 0x0400000100020420 0x9ae401f80e703f06 0xb35c803f01ce07e0

def z848 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0x88e59ff9c0000000 0x311cb3ff38000000

def z849 : W := mkw 0x24000c1890322108 0x8480018312064421 0x70059c79f072031a 0x4e00b38f3e0e4063

def z850 : W := mkw 0x2808224a2090e333 0x0501044944121c66 0xfffe63fe3fffffff 0xffffcc7fc7ffffff

def z851 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xafe38387ce0e7fff 0xf5fc7070f9c1cfff

def z852 : W := mkw 0x90230085420414c0 0x12046010a8408298 0xafe38387c6047ce5 0x75fc7070f8c08f9c

def z853 : W := mkw 0x08ff7bf7b5c0c237 0xe11fef7ef6b81846 0xffffffffffffc3ff 0xfffffffffffff87f

def z854 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0xf71e7e0601ffc0e7 0xdee3cfc0c03ff81c

def z855 : W := mkw 0x00ff7bf7b5c04a07 0xe01fef7ef6b80940 0xfefffffff1800000 0x7fdffffffe300000

def z856 : W := mkw 0x90230085420414c0 0x12046010a8408298 0x8fe20387ce047ce5 0xf1fc4070f9c08f9c

def z857 : W := mkw 0x0077500005400004 0x200eea0000a80000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z858 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x7e7ffc0007f78003 0x0fcfff8000fef000

def z859 : W := mkw 0x00ff7bf7b5400007 0xe01fef7ef6a80000 0xfefffffff1f00002 0x7fdffffffe3e0000

def z860 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xffe383c7fe0c7ce5 0xfffc7078ffc18f9c

def z861 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x7e7e7c000fff8003 0x8fcfcf8001fff000

def z862 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x7a1dfc0001f38002 0x0f43bf80003e7000

def z863 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7efffd800fffbc03 0xafdfffb001fff780

def z864 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x647bfc000fff8003 0x8c8f7f8001fff000

def z865 : W := mkw 0x902384854a2e14c0 0x12047090a945c298 0xafe38387ce7e7ce7 0xf5fc7070f9cfcf9c

def z866 : W := mkw 0x0077581090000004 0x800eeb0212000000 0x7e7ffc39c0000000 0x2fcfff8738000000

def z867 : W := mkw 0xf40084084f7f3188 0x3e80108109efe631 0x000000000e7a339e 0x8000000001cf4673

def z868 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfefffffff18b839e 0xffdffffffe317073

def z869 : W := mkw 0x4077540005630004 0x280eea8000ac6000 0x547e7c0001f38002 0x0a8fcf80003e7000

def z870 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x7effffbfc0000000 0x2fdffff7f8000000

def z871 : W := mkw 0x0000089590000000 0x80000112b2000000 0xfa859ffff0000000 0x7f50b3fffe000000

def z872 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7e7ffc01cfff8003 0x8fcfff8039fff000

def z873 : W := mkw 0x34008408483a3188 0x0680108109074631 0x72000000087a339e 0x8e400000010f4673

def z874 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0x08e7fdbfc0000000 0x211cffb7f8000000

def z875 : W := mkw 0xbc08a64a6abef7fb 0x178114c94d57deff 0xf71a62463fffffff 0xdee34c48c7ffffff

def z876 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x89e403f80ff07f07 0xb13c807f01fe0fe0

def z877 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xffe79f87ce0c7ce5 0xfffcf3f0f9c18f9c

def z878 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xfefffd81cfffbc87 0xffdfffb039fff790

def z879 : W := mkw 0x08ff73e725c0ca37 0x611fee7ce4b81946 0x05fa63860785cc61 0x00bf4c70c0f0b98c

def z880 : W := mkw 0x0000081090000000 0x8000010212000000 0xfee59ff9f0000000 0x7fdcb3ff3e000000

def z881 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x9ffc03f80e707c05 0xb3ff807f01ce0f80

def z882 : W := mkw 0x34000818d0103188 0x868001031a020631 0xfa059c79f870339e 0xff40b38f3f0e0673

def z883 : W := mkw 0x20dc736a25d06b07 0x641b8e6d44ba0d60 0x9ffc63f80ff07f07 0xb3ff8c7f01fe0fe0

def z884 : W := mkw 0x34008408483a3188 0x0680108109074631 0xa2000000087a339e 0xd4400000010f4673

def z885 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x15fc03f80ff07f07 0x82bf807f01fe0fe0

def z886 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff00c00e0 0x7fdffffffe01801c

def z887 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xfee79ffff0000000 0x7fdcf3fffe000000

def z888 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x08fdfdb9c0000000 0x211fbfb738000000

def z889 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa059c79f870339c 0x7f40b38f3f0e0673

def z890 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xafe38387ce047c61 0x75fc7070f9c08f8c

def z891 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x0cfc03b80e703c00 0x219f807701ce0780

def z892 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfefffffff18f83fa 0x7fdffffffe31f07f

def z893 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfe659c79fe7a339f 0xffccb38f3fcf4673

def z894 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff18dc0e5 0xfffffffffe31b81c

def z895 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xbfe383c7ce0c7fe7 0xf7fc7078f9c18ffc

def z896 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x8fe18387ce007ce5 0xf1fc3070f9c00f9c

def z897 : W := mkw 0x3c08a64a68baf3bb 0x078114c94d175e77 0x5018604039fbb39e 0x8a030c08073f7673

def z898 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0xfefd9ff9f0000000 0x7fdfb3ff3e000000

def z899 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff0004060 0x7ffffffffe00080c

def z900 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xffffffffff8fffff 0xfffffffffff1ffff

def z901 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0xbeff9fffc0000000 0x77dff3fff8000000

def z902 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x58fdfd81cff3bc02 0x2b1fbfb039fe7780

def z903 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffc03f83ff07f07 0xffff807f07fe0fe0

def z904 : W := mkw 0x08082a52b080c233 0x8101054a56101846 0xff1ffe7ff185c061 0x7fe3ffcffe30b80c

def z905 : W := mkw 0xc054540007670004 0x380a8a8000ece000 0x501c7c0007f78003 0x0a038f8000fef000

def z906 : W := mkw 0x4054d4000d6b0004 0x280a9a8001ad6000 0x7e7dfc000ffb8003 0x8fcfbf8001ff7000

def z907 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0xff7ffe07cffff0e7 0xffefffc0f9fffe1c

def z908 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x88e59df9f0000000 0x711cb3bf3e000000

def z909 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f0000306 0xff40b38f3e000060

def z910 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xff059e79f87a739f 0xffe0b3cf3f0f4e73

def z911 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x99fc03f80ff07f06 0x333f807f01fe0fe0

def z912 : W := mkw 0x0000040000220000 0x0000008000044000 0x501c7c0001f38002 0x0a038f80003e7000

def z913 : W := mkw 0x007f53e500000006 0x000fea7ca0000000 0xfeffffffc0000000 0x7fdffffff8000000

def z914 : W := mkw 0xc054d4000f6f0004 0x380a9a8001ede000 0x501c7c000ff38002 0x0a038f8001fe7000

def z915 : W := mkw 0xb4008c18da3e35c8 0x968011831b47c6b9 0xfa059c79f87e33fe 0xff40b38f3f0fc67f

def z916 : W := mkw 0xc077d4850f6f0004 0x380efa90a1ede000 0xffffff87cffffc07 0xfffffff0f9ffff80

def z917 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x001c7c0001f18000 0x00038f80003e3000

def z918 : W := mkw 0x90230085420414c0 0x12046010a8408298 0x05e20387c6047c61 0x20bc4070f8c08f8c

def z919 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffe63f80ff07f07 0xbfffcc7f01fe0fe0

def z920 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xbfe78387ce7c7ce7 0xf7fcf070f9cf8f9c

def z921 : W := mkw 0x00080a5090000002 0x8001014a12000000 0xfe1d9e79f0000000 0x7fc3b3cf3e000000

def z922 : W := mkw 0xc0ff7bf7b7450447 0xf81fef7ef6e8a088 0xfffffffff785cc61 0x7ffffffffef0b98c

def z923 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xbffd83f9cff07f07 0xf7ffb07f39fe0fe0

def z924 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0x7efffdbff0000000 0x6fdfffb7fe000000

def z925 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x28e79dbfc0000000 0x651cf3b7f8000000

def z926 : W := mkw 0xd077d4004f6f14c4 0x3a0efa8009ede298 0xff7ffe060ffffce7 0xdfefffc0c1ffff9c

def z927 : W := mkw 0x00882bf7b0000003 0xc011057ef6000000 0x88859ffff0000000 0x7110b3fffe000000

def z928 : W := mkw 0x0000081090000000 0x8000010212000000 0xfe079e7ff0000000 0x7fc0f3cffe000000

def z929 : W := mkw 0x80ff7bf7b2040447 0xd01fef7ef6408088 0xfefffffff0040060 0x7fdffffffe00800c

def z930 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x08e401f80e703f00 0x211c803f01ce07e0

def z931 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x25e38387ce0c7ce5 0xc4bc7070f9c18f9c

def z932 : W := mkw 0x34008408483a3188 0x0680108109074631 0x761a600009ffb39f 0x8ec34c00013ff673

def z933 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x89e18387ce0c7ce5 0xf13c3070f9c18f9c

def z934 : W := mkw 0x94238c95da2e14c8 0x92847192bb45c299 0x00019c01c0000000 0x0000338038000000

def z935 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x587c7c000ff38002 0x0b0f8f8001fe7000

def z936 : W := mkw 0x34008408483a3188 0x0680108109074631 0x01000000087e73ff 0x80200000010fce7f

def z937 : W := mkw 0x008009b590000000 0xc0100136b2000000 0xfa859df9f0000000 0x7f50b3bf3e000000

def z938 : W := mkw 0x34008408483a3188 0x0680108109074631 0x00000000087a3098 0x00000000010f4613

def z939 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x89e403fe3e707ffc 0x713c807fc7ce0fff

def z940 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x58fdfdb9c0000000 0x2b1fbfb738000000

def z941 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x9ae401f80e703c00 0x335c803f01ce0780

def z942 : W := mkw 0x9c2baed7faaed6fb 0x938575daff55dadf 0xf71bfe47f18fc3ff 0xdee37fc8fe31f87f

def z943 : W := mkw 0xd423dc95da2f14cc 0x9a847b92bb45e299 0x6003fc07f00f80f8 0x4c007f80fe01f01f

def z944 : W := mkw 0xc8ff7bf7b7c5c237 0xf91fef7ef6f8b846 0xfffffffff78fc3ff 0xfffffffffef1f87f

def z945 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff18043ff 0xfffffffffe30087f

def z946 : W := mkw 0x2008036805d06b02 0x2401006d00ba0d60 0x8fe003f80ff07f07 0xb1fc007f01fe0fe0

def z947 : W := mkw 0x0000081090000000 0x8000010212000000 0x68059c39f0000000 0x6d00b3873e000000

def z948 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc000fffb007 0xbfcfff8001fff600

def z949 : W := mkw 0x902384854a2e14c0 0x12047090a945c298 0xefe39f87ce0e7ce5 0xfdfc73f0f9c1cf9c

def z950 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x8ae401b80e703c04 0xb15c803701ce0780

def z951 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff0007c04 0x7ffffffffe000f80

def z952 : W := mkw 0x0023081090000000 0x8004610212000000 0xfe679c79f0000000 0x7fccf38f3e000000

def z953 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xafffff87cffdfce5 0xf5fffff0f9ffbf9c

def z954 : W := mkw 0x80ff7bf7b2040447 0xd01fef7ef6408088 0xfffffffffe047c65 0xffffffffffc08f8c

def z955 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfee59ff9f87a339e 0xffdcb3ff3f0f4673

def z956 : W := mkw 0x080822422080c233 0x0101044844101846 0x651a6206318fc3ff 0xcca34c40c631f87f

def z957 : W := mkw 0xd054d4004f6f14c4 0x3a0a9a8009ede298 0x511c7c000ffffce7 0x8a238f8001ffff9c

def z958 : W := mkw 0x34008408483a3188 0x0680108109074631 0x50000040387a339e 0x8a000008070f4673

def z959 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xff7ffe07cfffc0e7 0xdfefffc0f9fff81c

def z960 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfefffffff0038018 0x7fdffffffe007003

def z961 : W := mkw 0x00080b7090000002 0x8001016e12000000 0xfa859ff9f0000000 0x7f50b3ff3e000000

def z962 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x18fc01b80ff03c02 0x231f803701fe0780

def z963 : W := mkw 0x08082a52b080c233 0x8101054a56101846 0xfa1dfc79f183831a 0x7f43bf8f3e307063

def z964 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xafe38387ce007ce4 0x75fc7070f9c00f9c

def z965 : W := mkw 0x080822422080c233 0x0101044844101846 0xff1e627e318fc3ff 0xffe3cc4fc631f87f

def z966 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f83ff07f9f 0xf3ff807f07fe0ff3

def z967 : W := mkw 0x34008408483a3188 0x0680108109074631 0x80000040387a339e 0xd0000008070f4673

def z968 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x88059c79f87a339e 0xf100b38f3f0f4673

def z969 : W := mkw 0x005c036005400002 0x200b806c00a80000 0x9ffc03f80ff07c07 0xb3ff807f01fe0f80

def z970 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x547e7c000fff8003 0x8a8fcf8001fff000

def z971 : W := mkw 0x08f779b7b0008035 0xc11eef36f6001006 0x68e7fdbff00f80f8 0x6d1cffb7fe01f01f

def z972 : W := mkw 0x4077540005630004 0x280eea8000ac6000 0x701ffc0001f38002 0x0e03ff80003e7000

def z973 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff00040e4 0x7ffffffffe00081c

def z974 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x74fffffff0000000 0x4e9ffffffe000000

def z975 : W := mkw 0x00ff7bf7b0000447 0xc01fef7ef6000088 0xfffffffff0004c60 0x7ffffffffe00098c

def z976 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x8ee403b80e703c00 0x31dc807701ce0780

def z977 : W := mkw 0x10000085400014c0 0x02000010a8000298 0xafe20387ce0c7ce5 0xf5fc4070f9c18f9c

def z978 : W := mkw 0xc8ff73e727c5c237 0x791fee7ce4f8b846 0x05fa63860785c061 0x00bf4c70c0f0b80c

def z979 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7f7ffc000ffffc07 0x8fefff8001ffff80

def z980 : W := mkw 0x00ff7bf7b5400007 0xe01fef7ef6a80000 0xfeffffffffff8003 0xffdffffffffff000

def z981 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x7e7ffc7ff0000000 0x4fcfff8ffe000000

def z982 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xfae59df9f00a039e 0xff5cb3bf3e014073

def z983 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc000ff58001 0x0fcfff8001feb000

def z984 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x7efffdb9c18f8003 0xafdfffb73831f000

def z985 : W := mkw 0x0800200220008031 0x0100040044001006 0xf61a6046318f83ff 0xdec34c08c631f07f

def z986 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x1efd9db9c0000000 0x23dfb3b738000000

def z987 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0x581dfc79f0000000 0x2b03bf8f3e000000

def z988 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x08e59df9f0000000 0x211cb3bf3e000000

def z989 : W := mkw 0xc077d4850f6f0004 0x380efa90a1ede000 0x7effff860fff8003 0x8fdffff0c1fff000

def z990 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xefe38387fe0e7cfd 0xfdfc7070ffc1cf9f

def z991 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff00a0098 0x7fdffffffe014013

def z992 : W := mkw 0xd077d4004f6f14c4 0x3a0efa8009ede298 0xffffff800ffffce7 0xbffffff001ffff9c

def z993 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xa9e38387ce0c7ce4 0x753c7070f9c18f9c

def z994 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfae59ffff0000000 0x7f5cb3fffe000000

def z995 : W := mkw 0x34008408483a3188 0x0680108109074631 0x0000000009ffb39f 0x80000000013ff673

def z996 : W := mkw 0x88ff7bf7b284c677 0xd11fef7ef65098ce 0xfffffffff785cc61 0x7ffffffffef0b98c

def z997 : W := mkw 0x40ff7bf7b5410007 0xe81fef7ef6a82000 0xfefffffff1818000 0x7fdffffffe303000

def z998 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x2ee79db9c0000000 0x25dcf3b738000000

def z999 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0x7007fc7ff0000000 0x4e00ff8ffe000000

def z1000 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xdffc63f80ff3ff07 0xbbff8c7f01fe7fe0

def z1001 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffc03f80ffa7f07 0xbfff807f01ff4fe0

def z1002 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9be403f80e707f06 0xb37c807f01ce0fe0

def z1003 : W := mkw 0xc077d4850f6f0004 0x380efa90a1ede000 0x7e7ffc07cfff8003 0xcfcfff80f9fff000

def z1004 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x1ffc01b80ff07f07 0xa3ff803701fe0fe0

def z1005 : W := mkw 0xd077d4004f6f14c4 0x3a0efa8009ede298 0xff7ffc01cffffce7 0xffefff8039ffff9c

def z1006 : W := mkw 0xc077d4850f6f0444 0x380efa90a1ede088 0xffffff87cfffcc63 0xfffffff0f9fff98c

def z1007 : W := mkw 0x00ab7bf7b0000007 0xc0156f7ef6000000 0xeee3fffff0000000 0x7ddc7ffffe000000

def z1008 : W := mkw 0x10000085400014c0 0x02000010a8000298 0x89e00387ce007ce4 0x713c0070f9c00f9c

def z1009 : W := mkw 0xb423848d4a3e35c8 0x16847091a947c6b9 0x05e203860e7e7fff 0x80bc4070c1cfcfff

def z1010 : W := mkw 0x0023008500000000 0x00046010a0000000 0xafe38387ce0c7ce5 0xf5fc7070f9c18f9c

def z1011 : W := mkw 0x2000000805d06b00 0x2400000100ba0d60 0x9fe403f80ff07f07 0xb3fc807f01fe0fe0

def z1012 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xaae59db9c0000000 0x755cb3b738000000

def z1013 : W := mkw 0x2000000800102100 0x0400000100020420 0xffe603fe3e7e7fff 0xfffcc07fc7cfcfff

def z1014 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xfeffff87cfff80e3 0xffdffff0f9fff01c

def z1015 : W := mkw 0x0000081090000000 0x8000010212000000 0x88059c79f0000000 0x7100b38f3e000000

def z1016 : W := mkw 0xc023d4000f6f0004 0x38047a8001ede000 0x761bfc000fff8003 0x8ec37f8001fff000

def z1017 : W := mkw 0xbc0084084abef7f8 0x178010810957deff 0x010000000fffffff 0x8020000001ffffff

def z1018 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x767e7c0007ff8003 0x8ecfcf8000fff000

def z1019 : W := mkw 0xc054d4000f6f0004 0x380a9a8001ede000 0x7a1dfc000fff8003 0x8f43bf8001fff000

def z1020 : W := mkw 0x00ff7bf7b5400007 0xe01fef7ef6a80000 0xfefffffffe700000 0x7fdfffffffce0000

def z1021 : W := mkw 0x340084084dfa7b88 0x2680108109bf4f71 0x010000000ff07f07 0x8020000001fe0fe0

def z1022 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x5a1c7c0009f38002 0x8b438f80013e7000

def z1023 : W := mkw 0x2854012805d0eb30 0x250a802500ba1d66 0x09e401b80fffffff 0xa13c803701ffffff

def z1024 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xbffe03f80ffc7f07 0xb7ffc07f01ff8fe0

def z1025 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0xfee7fffff0000000 0x7fdcfffffe000000

def z1026 : W := mkw 0xb4008c18da3e3188 0x968011831b47c631 0xfa059c79fe7e339f 0xff40b38f3fcfc673

def z1027 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfffffffff1804001 0x7ffffffffe300800

def z1028 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x08e401b80ff03c03 0xa11c803701fe0780

def z1029 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x507c7c0007f38002 0x0a0f8f8000fe7000

def z1030 : W := mkw 0x00ff7bf7b0804a07 0xc01fef7ef6100940 0xfffffffff0004c00 0x7ffffffffe000980

def z1031 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xfffbe3c7ff8fffff 0xffff7c78fff1ffff

def z1032 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x9ffc03b80ff07c07 0xb3ff807701fe0f80

def z1033 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x1ffc03b80ff07c03 0xa3ff807701fe0f80

def z1034 : W := mkw 0x34008408483a3188 0x0680108109074631 0x00000000087a3002 0x80000000010f4600

def z1035 : W := mkw 0x3c008408483ab1b8 0x0780108109075637 0x00000000087fb3fe 0x80000000010ff67f

def z1036 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfe1ffc79f87a339e 0xffc3ff8f3f0f4673

def z1037 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x9efc03f80e703f06 0xb3df807f01ce07e0

def z1038 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7a1ffc0009ff8002 0x8f43ff80013ff000

def z1039 : W := mkw 0x007f0bf590000002 0x800fe17eb2000000 0xfeff9ffff0000000 0x7fdff3fffe000000

def z1040 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x701ffc07c1ff80e2 0x4e03ff80f83ff01c

def z1041 : W := mkw 0x005484000d6a0000 0x200a908001ad4000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z1042 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xafe79fbfc00c40e5 0xf5fcf3f7f801881c

def z1043 : W := mkw 0x34008408483a3188 0x0680108109074631 0x000000000870339c 0x00000000010e0673

def z1044 : W := mkw 0x00ff7bf7b5c04a07 0xe01fef7ef6b80940 0xfffffffff7804f07 0xfffffffffef009e0

def z1045 : W := mkw 0xd077d4004f6f14c4 0x3a0efa8009ede298 0x7e7ffc000fffbc03 0x8fcfff8001fff780

def z1046 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x1ae401b80e703c02 0xa35c803701ce0780

def z1047 : W := mkw 0x2000081890102100 0x8400010312020420 0xfa059c79f87a339e 0xff40b38f3f0f4673

def z1048 : W := mkw 0xc023d4000a2f0004 0x18047a800145e000 0x7e1ffc0009ff8003 0x8fc3ff80013ff000

def z1049 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x58059c79f87a339e 0xab00b38f3f0f4673

def z1050 : W := mkw 0x34008c18d83a35c8 0x868011831b0746b9 0xfb059c79f87a7ffe 0xff60b38f3f0f4fff

def z1051 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffc03fe0ff07f67 0xb3ff807fc1fe0fec

def z1052 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7fffff87cfffcce3 0xcffffff0f9fff99c

def z1053 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xfffbe387ce0c7ce5 0xffff7c70f9c18f9c

def z1054 : W := mkw 0x24000c1890322108 0x8480018312064421 0xfa059c79f07a039e 0xff40b38f3e0f4073

def z1055 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x85e20387ce0c7ce5 0xf0bc4070f9c18f9c

def z1056 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f80ffa7f9f 0xb3ff807f01ff4ff3

def z1057 : W := mkw 0xc077d4850f6f0004 0x380efa90a1ede000 0x7efffd81cfff8003 0xafdfffb039fff000

def z1058 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff0000306 0xffdffffffe000060

def z1059 : W := mkw 0x0054093090000000 0x800a812612000000 0xfae59df9f0000000 0x7f5cb3bf3e000000

def z1060 : W := mkw 0x00dc2bf7b0000003 0xc01b857ef6000000 0xfefd9ffff0000000 0x7fdfb3fffe000000

def z1061 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xbffe63fe0ffdffe7 0xf7ffcc7fc1ffbffc

def z1062 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x68e7fdb9c0000000 0x2d1cffb738000000

def z1063 : W := mkw 0x00ab7ad7b0000007 0xc0156f5af6000000 0xfe1ffe7ff0000000 0x7fc3ffcffe000000

def z1064 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc403fff831b 0x8fcfff8807fff063

def z1065 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f8003004 0xff40b38f3f000600

def z1066 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffe63fe0fffffe7 0xffffcc7fc1fffffc

def z1067 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x7a059c79f87a331a 0xaf40b38f3f0f4663

def z1068 : W := mkw 0x0808a64228aac233 0x010114c845155846 0xfb059e46387a43fe 0xdf60b3c8c70f487f

def z1069 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfefffffff18f831b 0xffdffffffe31f063

def z1070 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x0dfc03b80ff07f07 0xa1bf807701fe0fe0

def z1071 : W := mkw 0x080822422080c233 0x0101044844101846 0xe51a6246318fc3fd 0x5ca34c48c631f87f

def z1072 : W := mkw 0x0023089590000000 0x80046112b2000000 0xfa079c7ff0000000 0x7f40f38ffe000000

def z1073 : W := mkw 0x08002812b0008031 0x8100050256001006 0xfa07fc7ff00f80f8 0x7f40ff8ffe01f01f

def z1074 : W := mkw 0x00ab7bf7b0000007 0xc0156f7ef6000000 0xf69bfffff0000000 0x7ed37ffffe000000

def z1075 : W := mkw 0x08dc7b72b080c237 0xc11b8f6e56101846 0xff1ffe7ff18fc3ff 0xffe3ffcffe31f87f

def z1076 : W := mkw 0x2054012805502900 0x240a802500aa0520 0xafe603be0e7c7ce5 0xf5fcc077c1cf8f9c

def z1077 : W := mkw 0x080822422080c233 0x0101044844101846 0xf79a63c6318fffff 0xfef34c78c631ffff

def z1078 : W := mkw 0x3c00840848baf3b8 0x0780108109175e77 0x01000000087a73fe 0x80200000010f4e7f

def z1079 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f80ff07c01 0x33ff807f01fe0f80

def z1080 : W := mkw 0x345484084d7a3188 0x268a908109af4631 0x1e7c00000ffa339f 0x83cf800001ff4673

def z1081 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x9a059c79f870339e 0xf340b38f3f0e0673

def z1082 : W := mkw 0xd077d4004f6f14c4 0x3a0efa8009ede298 0x7e7ffc000fff80e3 0x8fcfff8001fff01c

def z1083 : W := mkw 0x34008408483a3188 0x0680108109074631 0x92000040087a339e 0x92400008010f4673

def z1084 : W := mkw 0x00008400082a0000 0x0000108001054000 0x7a1dfc0009fb8002 0x8f43bf80013f7000

def z1085 : W := mkw 0x087f7a52b080c237 0x810fef4a56101846 0xff7ffe7ff18fc3ff 0xffefffcffe31f87f

def z1086 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x09e401b80e707c05 0xa13c803701ce0f80

def z1087 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xf61ffe7ff0000000 0x5ec3ffcffe000000

def z1088 : W := mkw 0x2054000805502100 0x240a800100aa0420 0x9ffc03f80ff07f07 0xb3ff807f01fe0fe0

def z1089 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffe03fe0ff47f67 0xb3ffc07fc1fe8fec

def z1090 : W := mkw 0x00802897b0000001 0xc0100512f6000000 0xfa059c7ff0000000 0x7f40b38ffe000000

def z1091 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0x9ffc03f80ff3ff1f 0xb3ff807f01fe7fe3

def z1092 : W := mkw 0x080822422080c233 0x0101044844101846 0x711a6046318fc3ff 0xce234c08c631f87f

def z1093 : W := mkw 0x8023008502040440 0x10046010a0408088 0xafe38387ce047c65 0xf5fc7070f9c08f8c

def z1094 : W := mkw 0xc077d4850f6f0444 0x380efa90a1ede088 0x7efffd800fff8c03 0x8fdfffb001fff180

def z1095 : W := mkw 0x0077581090000004 0x800eeb0212000000 0xfa659c79f0000000 0x7f4cb38f3e000000

def z1096 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffffe000001 0xffdfffffffc00000

def z1097 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x6cffffbff0000000 0x6d9ffff7fe000000

def z1098 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff00c43fd 0xfffffffffe01887f

def z1099 : W := mkw 0x080822422080c233 0x0101044844101846 0x551a6246318fc3ff 0x8aa34c48c631f87f

def z1100 : W := mkw 0x205c036800102102 0x040b806d00020420 0x9ffc03f80e707f07 0xb3ff807f01ce0fe0

def z1101 : W := mkw 0xd477d4004f6f108c 0x3a8efa8009ede211 0x7e7ffc000fff809b 0x8fcfff8001fff013

def z1102 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffe63f83fffff1f 0xbfffcc7f07ffffe3

def z1103 : W := mkw 0x10230085400014c0 0x02046010a8000298 0xafe38387ce007ce5 0xf5fc7070f9c00f9c

def z1104 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7fffff860ffffce7 0x8ffffff0c1ffff9c

def z1105 : W := mkw 0xd023d4854a2f14c4 0x1a047a90a945e298 0xfffbff87cf8ffce7 0xffff7ff0f9f1ff9c

def z1106 : W := mkw 0x2c5c2f7ab5f2eb3b 0xa58b85ef56be5d67 0x501c7c7831f3831a 0x0a038f8f063e7063

def z1107 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xbffe03fe0ff07f07 0xf7ffc07fc1fe0fe0

def z1108 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xbffb8387cf8c7ce7 0xf7ff7070f9f18f9c

def z1109 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfefffffff00000f8 0x7fdffffffe00001f

def z1110 : W := mkw 0xfc0084084ffff3b8 0x3f80108109fffe77 0x010000000ffff3ff 0x8020000001fffe7f

def z1111 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x1efc01f80ff03f03 0xa3df803f01fe07e0

def z1112 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x501c7c4031f3831a 0x0a038f88063e7063

def z1113 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7f7ffe060fffc063 0x8fefffc0c1fff80c

def z1114 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xffffffffff807f07 0xfffffffffff00fe0

def z1115 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x18fc01f80e703c00 0x231f803f01ce0780

def z1116 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffc63f80ff1ff07 0xb3ff8c7f01fe3fe0

def z1117 : W := mkw 0x34000c18d0323188 0x868001831a064631 0xfa059c79f072339e 0x7f40b38f3e0e4673

def z1118 : W := mkw 0x00082a52b0000003 0x8001054a56000000 0xfa059e7ff0000000 0x7f40b3cffe000000

def z1119 : W := mkw 0x00d4593090000004 0xc01a8b2612000000 0xfa059c79f0000000 0x7f40b38f3e000000

def z1120 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff00fc3fc 0x7ffffffffe01f87f

def z1121 : W := mkw 0x3c08a64a6dfafbbb 0x278114c94dbf5f77 0xf71a62463fffffff 0xdee34c48c7ffffff

def z1122 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xffffff860ffffce7 0xfffffff0c1ffff9c

def z1123 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0x58fdfdf9f183831a 0x2b1fbfbf3e307063

def z1124 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x0de403b80e707c01 0x21bc807701ce0f80

def z1125 : W := mkw 0x0000081090000000 0x8000010212000000 0xfe1ffc79f18f8003 0xffc3ff8f3e31f000

def z1126 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfefffffff1818000 0x7fdffffffe303000

def z1127 : W := mkw 0x080822422080c233 0x0101044844101846 0xf7fa63c6378fcfff 0xdeff4c78c6f1f9ff

def z1128 : W := mkw 0x080822422080c233 0x0101044844101846 0xff1ffe46318fc3ff 0xdfe3ffc8c631f87f

def z1129 : W := mkw 0x00a37897b0000005 0xc0146f12f6000000 0x6807fc3ff0000000 0x6d00ff87fe000000

def z1130 : W := mkw 0x9c23ac97fa2e94f9 0x93847592ff45d29f 0x6003fc07f00f80f8 0x4c007f80fe01f01f

def z1131 : W := mkw 0xd023d0854a0d14c4 0x1a047a10a941a298 0xafe3e387ce0dfce5 0xf5fc7c70f9c1bf9c

def z1132 : W := mkw 0x0077589590000004 0x800eeb12b2000000 0xfefffffff0000000 0x7fdffffffe000000

def z1133 : W := mkw 0x00a379b7b0000005 0xc0146f36f6000000 0x6083fdbff0000000 0x6c107fb7fe000000

def z1134 : W := mkw 0x34fff7ef683a318f 0x469ffefded074631 0x04fa6386087a339e 0x809f4c70c10f4673

def z1135 : W := mkw 0x34008408483a3188 0x0680108109074631 0x0000000008783084 0x80000000010f0610

def z1136 : W := mkw 0xfc08a64a6ffff3bb 0x3f8114c94dfffe77 0xf71a62463ffff3ff 0xdee34c48c7fffe7f

def z1137 : W := mkw 0x0000081090000000 0x8000010212000000 0xaa059c39c0000000 0x7540b38738000000

def z1138 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xbffe03fe3ffc7fff 0xf7ffc07fc7ff8fff

def z1139 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0xfffe63fe3ffa7f9f 0xffffcc7fc7ff4ff3

def z1140 : W := mkw 0x00ab7bf7b0000007 0xc0156f7ef6000000 0xfa87fffff0000000 0x7f50fffffe000000

def z1141 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0xfefffff9c0000000 0x3fdfffff38000000

def z1142 : W := mkw 0xf40084084f7f35c8 0x3e80108109efe6b9 0x010000000fffffff 0x8020000001ffffff

def z1143 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0xbffe03fe0fffffff 0xf7ffc07fc1ffffff

def z1144 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x541e7c0001f78003 0x0a83cf80003ef000

def z1145 : W := mkw 0xc0ff7bf7b7450007 0xf81fef7ef6e8a000 0xfefffffffff58003 0xffdffffffffeb000

def z1146 : W := mkw 0x080822422080c233 0x0101044844101846 0x751a6246318fc3fb 0x4ea34c48c631f87f

def z1147 : W := mkw 0x00ff5bf595c04a06 0xe01feb7eb2b80940 0x0dfd9fb9c7804c01 0x21bfb3f738f00980

def z1148 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffe63f80ff5ff07 0xb3ffcc7f01febfe0

def z1149 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc400fff8307 0x9fcfff8801fff060

def z1150 : W := mkw 0x00f759b595400004 0xe01eeb36b2a80000 0x08e59db9ce700000 0x211cb3b739ce0000

def z1151 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x08fc01b80ff03c00 0x211f803701fe0780

def z1152 : W := mkw 0x34008408483a3188 0x0680108109074631 0x0000000008703306 0x80000000010e0660

def z1153 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x50059c79f072031a 0x0a00b38f3e0e4063

def z1154 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x58e59df9f0000000 0x2b1cb3bf3e000000

def z1155 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x0ce79fbfc0000000 0x219cf3f7f8000000

def z1156 : W := mkw 0x34008408483a35c8 0x06801081090746b9 0x01000000087a7ffe 0x80200000010f4fff

def z1157 : W := mkw 0x00f759b595400004 0xe01eeb36b2a80000 0x1efd9db9cff00003 0xa3dfb3b739fe0000

def z1158 : W := mkw 0x4077d4000d6b0004 0x280efa8001ad6000 0x7e7ffc0009fb8002 0x8fcfff80013f7000

def z1159 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7a7dfc000ffb8002 0x8f4fbf8001ff7000

def z1160 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xdffe63fe3ff7ff7f 0xbbffcc7fc7feffef

def z1161 : W := mkw 0xc0f7d5a50f6f0004 0x781efab4a1ede000 0x7efffd800fff8003 0x8fdfffb001fff000

def z1162 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x0dfe63be0ff5fc61 0x21bfcc77c1febf8c

def z1163 : W := mkw 0x4077540005630004 0x280eea8000ac6000 0x7e7ffc0001ff8003 0x8fcfff80003ff000

def z1164 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0x9ffc03f80ff07fff 0xb3ff807f01fe0fff

def z1165 : W := mkw 0x4077540005630004 0x280eea8000ac6000 0x7e7ffc000ff38003 0x8fcfff8001fe7000

def z1166 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0x0cfd9fb9c0000000 0x219fb3f738000000

def z1167 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f8700002 0xff40b38f3f0e0000

def z1168 : W := mkw 0x0054081090000000 0x800a810212000000 0xfe7d9c79f0000000 0x7fcfb38f3e000000

def z1169 : W := mkw 0x3c882bfff090f3bb 0xc791057ffe121e77 0x818003fff00073fc 0x7030007ffe000e7f

def z1170 : W := mkw 0x0000081090000000 0x8000010212000000 0x58059c79f0000000 0x2b00b38f3e000000

def z1171 : W := mkw 0x3c082a5af090f3bb 0x8781054b5e121e77 0x80000079f000339c 0x7000000f3e000673

def z1172 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x5e7e7c000ff78003 0x8bcfcf8001fef000

def z1173 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa1dfc79f9fbb39e 0xff43bf8f3f3f7673

def z1174 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x747ffc0007ff8003 0x0e8fff8000fff000

def z1175 : W := mkw 0xd02384854a2f14c0 0x1a047090a945e298 0xafe38387ce0ffce5 0xf5fc7070f9c1ff9c

def z1176 : W := mkw 0x00882b72b0000003 0xc011056e56000000 0xfa059c79f0000000 0x7f40b38f3e000000

def z1177 : W := mkw 0x94238c95da2e14c8 0x92847192bb45c299 0x20039c07c00c00e0 0x44007380f801801c

def z1178 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff18fc0f9 0x7ffffffffe31f81f

def z1179 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x88e59fbfc0000000 0x711cb3f7f8000000

def z1180 : W := mkw 0x0023089590000000 0x80046112b2000000 0x08e59db9c0000000 0x211cb3b738000000

def z1181 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffe63fe3ff3ff1f 0xffffcc7fc7fe7fe3

def z1182 : W := mkw 0x3c082b7af090fbbb 0x8781056f5e121f77 0x818003fff0007ffc 0x7030007ffe000fff

def z1183 : W := mkw 0xc0ff7bf7b2050007 0xd81fef7ef640a000 0xfefffffff0058000 0x7fdffffffe00b000

def z1184 : W := mkw 0x10000085400014c0 0x02000010a8000298 0x85e00387c6007ce5 0x70bc0070f8c00f9c

def z1185 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfe079c79f87e339f 0xffc0f38f3f0fc673

def z1186 : W := mkw 0x2054012805502900 0x240a802500aa0520 0xfae401f83e7a3f9e 0xff5c803f07cf47f3

def z1187 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x8cfffffff0000000 0x719ffffffe000000

def z1188 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0xeee7ffbff0000000 0x7ddcfff7fe000000

def z1189 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xd8059c79f872339e 0x7b00b38f3f0e4673

def z1190 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x58fc61f83ff3bf1a 0x2b1f8c3f07fe77e3

def z1191 : W := mkw 0x002b2ad7b0000003 0x8005655af6000000 0xfefffffff0000000 0x7fdffffffe000000

def z1192 : W := mkw 0xc077548507670444 0x380eea90a0ece088 0x55fe7f8607f7cc63 0x0abfcff0c0fef98c

def z1193 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa07fc79f87fb39e 0xff40ff8f3f0ff673

def z1194 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0xfefffdf9f0000000 0x7fdfffbf3e000000

def z1195 : W := mkw 0x00a3589590000004 0xc0146b12b2000000 0x08059c39c0000000 0x2100b38738000000

def z1196 : W := mkw 0x0000000000000000 0x0000000000000000 0xf71a6246318fc3ff 0xdee34c48c631f87f

def z1197 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff18fc063 0xfffffffffe31f80c

def z1198 : W := mkw 0x1000800048081080 0x0200100009010210 0xafe38387ce0c7ce5 0xf5fc7070f9c18f9c

def z1199 : W := mkw 0x00ab7bf7b0000007 0xc0156f7ef6000000 0x6003fc7ff0000000 0x4c007f8ffe000000

def z1200 : W := mkw 0x0000081090000000 0x8000010212000000 0xffe59ff9fe007c05 0xfffcb3ff3fc00f80

def z1201 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xabe18387ce087ce4 0xf57c3070f9c10f9c

def z1202 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfb059e7ff87a73fe 0xff60b3cfff0f4e7f

def z1203 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa059c79f872331a 0x7f40b38f3f0e4663

def z1204 : W := mkw 0x3c00a40a683ab1b9 0x078014814d075637 0x60026006387fb3fe 0xcc004c00c70ff67f

def z1205 : W := mkw 0x802384000a2e0000 0x100470800145c000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z1206 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff00e43ff 0xfffffffffe01c87f

def z1207 : W := mkw 0x00a359b590000004 0xc0146b36b2000000 0x00819db9c0000000 0x201033b738000000

def z1208 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x78fffdfff0000000 0x6f1fffbffe000000

def z1209 : W := mkw 0x902384854a2e14c0 0x12047090a945c298 0xafe79f87ce7c7ce5 0xf5fcf3f0f9cf8f9c

def z1210 : W := mkw 0xc0ff7bf7b7c54a07 0xf81fef7ef6f8a940 0xfffffffff785cc01 0x7ffffffffef0b980

def z1211 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7fffff87cffffc63 0xaffffff0f9ffff8c

def z1212 : W := mkw 0x3400840848ba7b88 0x0680108109174f71 0x01000000087a7f9e 0x80200000010f4ff3

def z1213 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xafe38387cf8ffce7 0xf5fc7070f9f1ff9c

def z1214 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xf2059c79f07a039e 0xde40b38f3e0f4073

def z1215 : W := mkw 0x740084084d7b3188 0x2e80108109af6631 0x0000000009fbb39e 0x80000000013f7673

def z1216 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x8fe403b80ff07f07 0xb1fc807701fe0fe0

def z1217 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc060fff80e3 0xcfcfff80c1fff01c

def z1218 : W := mkw 0x00882bf7b0000003 0xc011057ef6000000 0xfe9ffffff0000000 0x7fd3fffffe000000

def z1219 : W := mkw 0x007f5b7090000006 0x800feb6e12000000 0xfefffff9f0000000 0x7fdfffff3e000000

def z1220 : W := mkw 0x00ff7bf7b5c04a07 0xe01fef7ef6b80940 0xffffffffff807c05 0xfffffffffff00f80

def z1221 : W := mkw 0x005c0b7090804202 0x800b816e12100840 0xfffd9ff9f18a439f 0xffffb3ff3e314873

def z1222 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x5c7ffc000ff78003 0x0b8fff8001fef000

def z1223 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x08e401b80e703f06 0xa11c803701ce07e0

def z1224 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfffffffff18fc307 0xfffffffffe31f860

def z1225 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x00059c39c0000000 0x0000b38738000000

def z1226 : W := mkw 0xc077d4000f6f0444 0x380efa8001ede088 0x7f7ffc000fffcc63 0x8fefff8001fff98c

def z1227 : W := mkw 0x340084084dfa7b88 0x2680108109bf4f71 0x0000000009fa339e 0x80000000013f4673

def z1228 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0xffffff81cffffc87 0xfffffff039ffff90

def z1229 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfe079e7ff87a339e 0xffc0f3cfff0f4673

def z1230 : W := mkw 0x80ff7bf7b2040447 0xd01fef7ef6408088 0xfefffffff6000c00 0x7fdffffffec00180

def z1231 : W := mkw 0xb40084084a3e35c8 0x168010810947c6b9 0x010000000e7c7ce5 0x8020000001cf8f9c

def z1232 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xaa059c79f878339c 0xf540b38f3f0f0673

def z1233 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff8003004 0xffdfffffff000600

def z1234 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff18f839f 0xffdffffffe31f073

def z1235 : W := mkw 0x8023089592040440 0x90046112b2408088 0xffe79ffff6044c61 0x7ffcf3fffec0898c

def z1236 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xafe383c7fe0c7ffd 0xf5fc7078ffc18fff

def z1237 : W := mkw 0x34000818d0103188 0x868001031a020631 0xf61a6079f18fb39f 0xfec34c0f3e31f673

def z1238 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0xfefdfff9f0000000 0x7fdfbfff3e000000

def z1239 : W := mkw 0x4054d4000d6b0004 0x280a9a8001ad6000 0x501c7c0009fb8002 0x8a038f80013f7000

def z1240 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f80fffff07 0xb3ff807f01ffffe0

def z1241 : W := mkw 0xc077d5200f6f0004 0x380efaa401ede000 0x7efffdb80fff8003 0xafdfffb701fff000

def z1242 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x08059c79f8703318 0x2100b38f3f0e0663

def z1243 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7f7ffc000fffc0e7 0x8fefff8001fff81c

def z1244 : W := mkw 0xd0a3fc97fa2f14c5 0xda147f92ff45e298 0x6003fc07f00f80e0 0x4c007f80fe01f01c

def z1245 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffffe0c7ce5 0xffffffffffc18f9c

def z1246 : W := mkw 0x085c2b72b080c233 0x810b856e56101846 0xfffffffff18fc3ff 0xfffffffffe31f87f

def z1247 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x6c7ffc000fff8001 0x0d8fff8001fff000

def z1248 : W := mkw 0x0023581090000004 0x80046b0212000000 0xfa07fc79f0000000 0x7f40ff8f3e000000

def z1249 : W := mkw 0x0054581090000004 0x800a8b0212000000 0xfa1dfc79f0000000 0x7f43bf8f3e000000

def z1250 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x8fe38387ce047c65 0xb1fc7070f9c08f8c

def z1251 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffe63fe3ff07fff 0xffffcc7fc7fe0fff

def z1252 : W := mkw 0x08882bf7b080c233 0xc111057ef6101846 0xfb859ffff00a43fe 0xff70b3fffe01487f

def z1253 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfefffffff00f83fe 0xffdffffffe01f07f

def z1254 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x561c7c0001f38003 0x8ac38f80003e7000

def z1255 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x8ee59fb9c0000000 0x31dcb3f738000000

def z1256 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x8fe403f80e707f05 0xb1fc807f01ce0fe0

def z1257 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc01cfff8003 0xffcfff8039fff000

def z1258 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0x6007fc3ff0000000 0x4c00ff87fe000000

def z1259 : W := mkw 0x605c536805d16b06 0x2c0b8a6d00ba2d60 0x9ffc63f80ff1ff07 0xb3ff8c7f01fe3fe0

def z1260 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfb059c79f87e73ff 0xff60b38f3f0fce7f

def z1261 : W := mkw 0x2000000800102100 0x0400000100020420 0x8fe403b80e707c05 0xb1fc807701ce0f80

def z1262 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff00c0001 0xffdffffffe018000

def z1263 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f000039c 0x7f40b38f3e000073

def z1264 : W := mkw 0xc0f759b597450004 0xf81eeb36b2e8a000 0x0cfffdb9c7858001 0x219fffb738f0b000

def z1265 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xefe3e387ce0ffce5 0xfdfc7c70f9c1ff9c

def z1266 : W := mkw 0x00807812b0000005 0xc0100f0256000000 0xfa05fc79f0000000 0x7f40bf8f3e000000

def z1267 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x08e59fbfc0000000 0x211cb3f7f8000000

def z1268 : W := mkw 0x4077540005630004 0x280eea8000ac6000 0x587dfc0001f38002 0x0b0fbf80003e7000

def z1269 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0x89e59ffff00043fc 0x713cb3fffe00087f

def z1270 : W := mkw 0x00ff5bf590000006 0xc01feb7eb2000000 0x18fd9df9c0000000 0x231fb3bf38000000

def z1271 : W := mkw 0x00ff5bf590804206 0xc01feb7eb2100840 0x9ffd9ff9c1804307 0xb3ffb3ff38300860

def z1272 : W := mkw 0x24000c1890322108 0x8480018312064421 0xfa059c79f872331e 0xff40b38f3f0e4663

def z1273 : W := mkw 0xf00084084fff7fc0 0x3e00108109ffeff8 0x010000000fffffe7 0x8020000001fffffc

def z1274 : W := mkw 0x34008408483a3188 0x0680108109074631 0x8a000000087a339e 0xb1400000010f4673

def z1275 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x7ae59db9c0000000 0x2f5cb3b738000000

def z1276 : W := mkw 0x900080854a0c14c0 0x12001010a9418298 0x8fe00387ce0c7ce5 0xf1fc0070f9c18f9c

def z1277 : W := mkw 0x3400840848ba7388 0x0680108109174e71 0x0100000009fa739f 0x80200000013f4e73

def z1278 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x8dfc03f80ff07f05 0x31bf807f01fe0fe0

def z1279 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x9fe403f80e707f07 0xb3fc807f01ce0fe0

def z1280 : W := mkw 0x005c0b7090000002 0x800b816e12000000 0xfa1d9c79f0000000 0x7f43b38f3e000000

def z1281 : W := mkw 0xc077d4850f6f0004 0x380efa90a1ede000 0xffffff87cfffc0e7 0xfffffff0f9fff81c

def z1282 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x7efffdf9f0000000 0x2fdfffbf3e000000

def z1283 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xaee79ffff0000000 0x75dcf3fffe000000

def z1284 : W := mkw 0x00882bf7b0000003 0xc011057ef6000000 0xe0819ffff0000000 0x7c1033fffe000000

def z1285 : W := mkw 0xf4008c18da3f3188 0x9e8011831b47e631 0xfa059c79f87fb39e 0xff40b38f3f0ff673

def z1286 : W := mkw 0x80ff7bf7b2040447 0xd01fef7ef6408088 0xfffffffff60c4ce5 0xfffffffffec1899c

def z1287 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x09e401b80ff07c01 0x213c803701fe0f80

def z1288 : W := mkw 0xc0ff7bf7b7450007 0xf81fef7ef6e8a000 0xfefffffff78f8003 0xffdffffffef1f000

def z1289 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f002031a 0x7f40b38f3e004063

def z1290 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xff7ffe463fffc3ff 0xdfefffc8c7fff87f

def z1291 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0xfffe63fe3ffc7fe7 0xffffcc7fc7ff8ffc

def z1292 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0xdffc7f800ff3fc07 0xbbff8ff001fe7f80

def z1293 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0xfae7fdfff0000000 0x7f5cffbffe000000

def z1294 : W := mkw 0x340084084d7a3988 0x2680108109af4731 0x000000000e7a3f9e 0x8000000001cf47f3

def z1295 : W := mkw 0xc077540007670004 0x380eea8000ece000 0x047e7c0007f58001 0x008fcf8000feb000

def z1296 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x88e401f80e703f04 0x311c803f01ce07e0

def z1297 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x547c7c0007f38003 0x0a8f8f8000fe7000

def z1298 : W := mkw 0x24000c1890322108 0x8480018312064421 0x58059c79f072031a 0x2b00b38f3e0e4063

def z1299 : W := mkw 0x080822422080c233 0x0101044844101846 0xfffa63c6318fc3ff 0xffff4c78c631f87f

def z1300 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xaeffffbfc0000000 0x75dffff7f8000000

def z1301 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfafdfdf9f0000000 0x7f5fbfbf3e000000

def z1302 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfffffffff18c43e7 0xfffffffffe31887c

def z1303 : W := mkw 0x008009b590000000 0xc0100136b2000000 0x08859db9c0000000 0x2110b3b738000000

def z1304 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfffffffff0004304 0x7ffffffffe000860

def z1305 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x2fe38387ce0c7c61 0xa5fc7070f9c18f8c

def z1306 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0x701dfc79f0000000 0x4e03bf8f3e000000

def z1307 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f80ffc7fe7 0xb3ff807f01ff8ffc

def z1308 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xff1ffe7ff9fff3ff 0xffe3ffcfff3ffe7f

def z1309 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9afc01f80ff03f06 0xb35f803f01fe07e0

def z1310 : W := mkw 0x340886484dfa7b8a 0x268110c909bf4f71 0xf71802403ffa7f9f 0xdee3004807ff4ff3

def z1311 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff185c3fd 0x7ffffffffe30b87f

def z1312 : W := mkw 0x00ff7bf7b5c04a07 0xe01fef7ef6b80940 0xfffffffffff04c03 0xfffffffffffe0980

def z1313 : W := mkw 0xc077d4850f6f0444 0x380efa90a1ede088 0xffffff860fffcce7 0xdffffff0c1fff99c

def z1314 : W := mkw 0x205c236a25502903 0x240b846d44aa0520 0xfefe63fe3e703c00 0x7fdfcc7fc7ce0780

def z1315 : W := mkw 0x0000081090000000 0x8000010212000000 0xfe1ffc79f0000000 0x7fc3ff8f3e000000

def z1316 : W := mkw 0x08ab7ad7b080c237 0xc1156f5af6101846 0xff1ffe7ff18fc3ff 0xffe3ffcffe31f87f

def z1317 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x761e7c0001f38002 0x0ec3cf80003e7000

def z1318 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0x7e7ffc01cfff8083 0xcfcfff8039fff010

def z1319 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xa5e38387c60c7ce5 0x74bc7070f8c18f9c

def z1320 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x89e403b80e707c04 0x313c807701ce0f80

def z1321 : W := mkw 0x3c08a64a68baf3bb 0x078114c94d175e77 0x051a620609fff3ff 0x80a34c40c13ffe7f

def z1322 : W := mkw 0xc077500007450004 0x380eea0000e8a000 0x7e7ffc000ff58003 0x8fcfff8001feb000

def z1323 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0xfffe63fe3fffff07 0xffffcc7fc7ffffe0

def z1324 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xbffc03f80ff87f87 0xf7ff807f01ff0ff0

def z1325 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff8700002 0xffdfffffff0e0000

def z1326 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x761ffc0001ff8003 0x8ec3ff80003ff000

def z1327 : W := mkw 0x080822422080c233 0x0101044844101846 0xf11a6246318fc3fe 0x5e234c48c631f87f

def z1328 : W := mkw 0x0077581090000004 0x800eeb0212000000 0xfe7ffc79f18f839f 0xffcfff8f3e31f073

def z1329 : W := mkw 0x00080a5090804202 0x8001014a12100840 0xff1d9e79f1804307 0xffe3b3cf3e300860

def z1330 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff185c367 0xfffffffffe30b86c

def z1331 : W := mkw 0x2c082a5ab090e33b 0x8581054b56121c67 0x0000007830000318 0x0000000f06000063

def z1332 : W := mkw 0xc0f759b597450004 0xf81eeb36b2e8a000 0x08e59db9c6000000 0x211cb3b738c00000

def z1333 : W := mkw 0x205c536805d06b06 0x240b8a6d00ba0d60 0xdffc7ff80ff07f07 0xbbff8fff01fe0fe0

def z1334 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffc03fe3ffa7fff 0xffff807fc7ff4fff

def z1335 : W := mkw 0x205c236a25d06b03 0x240b846d44ba0d60 0xdffc63f83ff07f07 0xbbff8c7f07fe0fe0

def z1336 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff0004005 0xfffffffffe000800

def z1337 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f0080084 0xff40b38f3e010010

def z1338 : W := mkw 0xc054d4000f6f0004 0x380a9a8001ede000 0x501c7c0001ff8002 0x0a038f80003ff000

def z1339 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffe060fff8003 0xdfcfffc0c1fff000

def z1340 : W := mkw 0x285c036805d0eb32 0x250b806d00ba1d66 0x9ffc03f80ff5ff67 0xb3ff807f01febfec

def z1341 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9efc03f80ff03f02 0x33df807f01fe07e0

def z1342 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xfe7ffc07cfffb0e7 0xffcfff80f9fff61c

def z1343 : W := mkw 0x080822422080c233 0x0101044844101846 0x761a6046318f83fb 0xcec34c08c631f07f

def z1344 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffffe003c00 0x7fdfffffffc00780

def z1345 : W := mkw 0x080822422080c233 0x0101044844101846 0xf71a62463f8fffff 0xdee34c48c7f1ffff

def z1346 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x85f803f80ff07f07 0xb0bf007f01fe0fe0

def z1347 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfe7ffc780fff8003 0xbfcfff8f01fff000

def z1348 : W := mkw 0x080822422080c233 0x0101044844101846 0xff1e624639ffc3ff 0xdfe3cc48c73ff87f

def z1349 : W := mkw 0x00f77897b0000005 0xc01eef12f6000000 0xfe7ffc7ff0000000 0x7fcfff8ffe000000

def z1350 : W := mkw 0xc0ff7bf7b7450007 0xf81fef7ef6e8a000 0xfefffffff6000000 0x7fdffffffec00000

def z1351 : W := mkw 0xf40084084f7f3188 0x3e80108109efe631 0x000000000fffb003 0x8000000001fff600

def z1352 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x9ae59df9c0000000 0x335cb3bf38000000

def z1353 : W := mkw 0xb40084084a3e35c8 0x168010810947c6b9 0xf70202463e7e7fff 0xdee04048c7cfcfff

def z1354 : W := mkw 0x0077581090000004 0x800eeb0212000000 0x08659c39c0000000 0x210cb38738000000

def z1355 : W := mkw 0x0000081090000000 0x8000010212000000 0xfa059c79f00a0002 0xff40b38f3e014000

def z1356 : W := mkw 0x10008085480814c0 0x02001010a9010298 0xafe18387ce087ce5 0xf5fc3070f9c10f9c

def z1357 : W := mkw 0x00dc7bf7b0000007 0xc01b8f7ef6000000 0xfa9dfffff0000000 0x7f53bffffe000000

def z1358 : W := mkw 0xf40084084f7f3188 0x3e80108109efe631 0xf61a60403fffb39f 0xdec34c0807fff673

def z1359 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xff7ffe000fffc007 0x9fefffc001fff800

def z1360 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffe03fe3ffe7fff 0xffffc07fc7ffcfff

def z1361 : W := mkw 0x005c0b7095c04a02 0xa00b816e12b80940 0xfffd9ff9f7804c01 0x7fffb3ff3ef00980

def z1362 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x0dffff87cff5fc61 0x21bffff0f9febf8c

def z1363 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xdffc63f83fffffff 0xbbff8c7f07ffffff

def z1364 : W := mkw 0xb40084084a3e35c8 0x168010810947c6b9 0x000000000e7a3f9e 0x8000000001cf47f3

def z1365 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x501dfc0001f38002 0x0a03bf80003e7000

def z1366 : W := mkw 0x007f7a52b0000007 0x800fef4a56000000 0xfe7ffe7ff0000000 0x7fcfffcffe000000

def z1367 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xf0059c79f07a339e 0x7e00b38f3e0f4673

def z1368 : W := mkw 0xb4008c18da3e35c8 0x968011831b47c6b9 0xffe59ff9fe7e7fff 0xfffcb3ff3fcfcfff

def z1369 : W := mkw 0x3c08aa5af898f3bb 0x8781154b5f131e77 0xaf03827ff80c73fd 0xf5e0704fff018e7f

def z1370 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7f7ffc07cffffce7 0xcfefff80f9ffff9c

def z1371 : W := mkw 0x0000081090000000 0x8000010212000000 0xe0019c79f0000000 0x7c00338f3e000000

def z1372 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0x9ffe63fe3ff5ffff 0xf3ffcc7fc7febfff

def z1373 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfe1d9c79f9fa339f 0xffc3b38f3f3f4673

def z1374 : W := mkw 0x005c2b72b0000003 0x800b856e56000000 0xfefffffff0000000 0x7fdffffffe000000

def z1375 : W := mkw 0x00ff7bf7b5400807 0xe01fef7ef6a80100 0xfefffffff6000c00 0x7fdffffffec00180

def z1376 : W := mkw 0x4054d4000d6b0004 0x280a9a8001ad6000 0x701dfc0001fb8002 0x0e03bf80003f7000

def z1377 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03fe0ff07fe7 0xf3ff807fc1fe0ffc

def z1378 : W := mkw 0x0000040000220000 0x0000008000044000 0x761e7c0001ff8003 0x8ec3cf80003ff000

def z1379 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x501c7c0001ff8003 0x8a038f80003ff000

def z1380 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x1e7ffc000ff58003 0x83cfff8001feb000

def z1381 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x9efd9ffff0000000 0x73dfb3fffe000000

def z1382 : W := mkw 0xb40084084ffe7fc8 0x3680108109ffcff9 0x010000000ffe7fff 0x8020000001ffcfff

def z1383 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffc63f83ffbff9f 0xffff8c7f07ff7ff3

def z1384 : W := mkw 0x3c08a64a68baf3bb 0x078114c94d175e77 0x81000246387a73fe 0xd0200048c70f4e7f

def z1385 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x9ffc03f80e707f04 0x33ff807f01ce0fe0

def z1386 : W := mkw 0x08082a52b080c233 0x8101054a56101846 0xfb059e7ff00043fc 0x7f60b3cffe00087f

def z1387 : W := mkw 0x0000081090000000 0x8000010212000000 0x7a059c39c0000000 0x2f40b38738000000

def z1388 : W := mkw 0x3408864848ba738a 0x068110c909174e71 0x9718024009fa739f 0x92e30048013f4e73

def z1389 : W := mkw 0xbc2baadffa9cf7fb 0x9785755bff539eff 0xafe383fffe0c7ffd 0xf5fc707fffc18fff

def z1390 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0xfeffff800fff8003 0xbfdffff001fff000

def z1391 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x70059c79f87a339e 0xce00b38f3f0f4673

def z1392 : W := mkw 0x08ab7bf7b080c237 0xc1156f7ef6101846 0xe183fffff00fc3fc 0x7c307ffffe01f87f

def z1393 : W := mkw 0x902384854a2e14c0 0x12047090a945c298 0xffe79fc7fe7e7fff 0xfffcf3f8ffcfcfff

def z1394 : W := mkw 0x00ff7bf7b0804207 0xc01fef7ef6100840 0xfffffffff18a439f 0xfffffffffe314873

def z1395 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x09e18387ce007c60 0x213c3070f9c00f8c

def z1396 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7efffd87cfffbce3 0xefdfffb0f9fff79c

def z1397 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfefffffff18f80fb 0xffdffffffe31f01f

def z1398 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x7efe61b80fffbc03 0xafdfcc3701fff780

def z1399 : W := mkw 0x00002812b0000001 0x8000050256000000 0xfa07fc7ff0000000 0x7f40ff8ffe000000

def z1400 : W := mkw 0x00f779b7b0000005 0xc01eef36f6000000 0x08e59dbff0000000 0x611cb3b7fe000000

def z1401 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x2e7ffc000ffd8001 0x85cfff8001ffb000

def z1402 : W := mkw 0x08ff7bf7b5c0ca37 0xe11fef7ef6b81946 0xfffffffff78fcfff 0xfffffffffef1f9ff

def z1403 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff000039c 0x7fdffffffe000073

def z1404 : W := mkw 0x080822422080c233 0x0101044844101846 0xff1a6246398ff3ff 0xffe34c48c731fe7f

def z1405 : W := mkw 0x00ff7bf7b5400007 0xe01fef7ef6a80000 0xfefffffff7800001 0x7fdffffffef00000

def z1406 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xdffc03f83ff27f1f 0xbbff807f07fe4fe3

def z1407 : W := mkw 0x00082a52b0000003 0x8001054a56000000 0xfa1dfc79f0000000 0x7f43bf8f3e000000

def z1408 : W := mkw 0x205c036805502902 0x240b806d00aa0520 0x88e403f80e703c00 0x311c807f01ce0780

def z1409 : W := mkw 0x80ff7bf7b2040007 0xd01fef7ef6408000 0xfefffffff6040001 0x7fdffffffec08000

def z1410 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff00a43fe 0xfffffffffe01487f

def z1411 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x087dfc000ff18000 0x010fbf8001fe3000

def z1412 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0xfffe63f83fffff9f 0xffffcc7f07fffff3

def z1413 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x0cfc01b80ff03c01 0x219f803701fe0780

def z1414 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0xffe38387ce0e7ce7 0xfffc7070f9c1cf9c

def z1415 : W := mkw 0x4054d4000d6b0004 0x280a9a8001ad6000 0x7e1ffc0009ff8003 0x8fc3ff80013ff000

def z1416 : W := mkw 0x00ff7b72b0000007 0xc01fef6e56000000 0xfe7ffc79f0000000 0x7fcfff8f3e000000

def z1417 : W := mkw 0xc054d4000f6f0004 0x380a9a8001ede000 0x761e7c000fff8003 0x8ec3cf8001fff000

def z1418 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xfeffff87cfffbc03 0xffdffff0f9fff780

def z1419 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0xfa059c79f07a039a 0x7f40b38f3e0f4073

def z1420 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7fffff800fffcc03 0x8ffffff001fff980

def z1421 : W := mkw 0x2054012805d06b00 0x240a802500ba0d60 0x9be401f80ff07f07 0xb37c803f01fe0fe0

def z1422 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0x7ffffd81cffffce7 0xafffffb039ffff9c

def z1423 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0x5cfffffff0000000 0x2b9ffffffe000000

def z1424 : W := mkw 0x0054081095400000 0xa00a810212a80000 0xfe7d9c79fff00003 0xffcfb38f3ffe0000

def z1425 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x701ffc000fff8003 0x8e03ff8001fff000

def z1426 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff002031a 0x7fdffffffe004063

def z1427 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x1efc01b80e703c00 0x23df803701ce0780

def z1428 : W := mkw 0x080823622080ca33 0x0101046c44101946 0xf79a63c6318fcfff 0xdef34c78c631f9ff

def z1429 : W := mkw 0x005c0b7090000002 0x800b816e12000000 0x9efd9ff9c0000000 0x33dfb3ff38000000

def z1430 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x701e7c0001ff8002 0x0e03cf80003ff000

def z1431 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xdffc63fe3ff3ffff 0xfbff8c7fc7fe7fff

def z1432 : W := mkw 0x88ff7bf7b284c677 0xd11fef7ef65098ce 0xfffffffff78fcfff 0xfffffffffef1f9ff

def z1433 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xf09ffffff0000000 0x7e13fffffe000000

def z1434 : W := mkw 0x34008408483a3188 0x0680108109074631 0xa7020206087e73ff 0xd4e04040c10fce7f

def z1435 : W := mkw 0x94238c95da2e14c8 0x92847192bb45c299 0x60019c01f00a0098 0x4c0033803e014013

def z1436 : W := mkw 0xf477dc9ddf7f35cc 0xbe8efb93bbefe6b9 0x08e59db9ce703c00 0x211cb3b739ce0780

def z1437 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x19fc01f80ff07f07 0xa33f803f01fe0fe0

def z1438 : W := mkw 0x3c00840848baf3b8 0x0780108109175e77 0x0000000009fbb39e 0x80000000013f7673

def z1439 : W := mkw 0x2c082a5ab090e33b 0x8581054b56121c67 0x8100027e300043fc 0x5020004fc600087f

def z1440 : W := mkw 0xd077d4854f6f14c4 0x3a0efa90a9ede298 0xffffff81cffffc07 0xbffffff039ffff80

def z1441 : W := mkw 0x3c082adff090f7fb 0x8781055bfe121eff 0x818003fff0007ffc 0x7030007ffe000fff

def z1442 : W := mkw 0xc077d4850f6f0444 0x380efa90a1ede088 0xffffff860ffffc67 0xbffffff0c1ffff8c

def z1443 : W := mkw 0x080822422080c233 0x0101044844101846 0xff7a62463f8fc3ff 0xdfef4c48c7f1f87f

def z1444 : W := mkw 0xd077d4004f6f1084 0x3a0efa8009ede210 0x7e7ffc01cfffb003 0xafcfff8039fff600

def z1445 : W := mkw 0x08882bf7b080c233 0xc111057ef6101846 0xff9ffffff18fc3ff 0xfff3fffffe31f87f

def z1446 : W := mkw 0x340084084d7a3988 0x2680108109af4731 0x000000000e703c00 0x0000000001ce0780

def z1447 : W := mkw 0x94a3fc97fa2e14cd 0xd2947f92ff45c299 0x6003fc07f00e00f8 0x4c007f80fe01c01f

def z1448 : W := mkw 0x902380854a0c14c0 0x12047010a9418298 0x8de38387ce047ce5 0x71bc7070f9c08f9c

def z1449 : W := mkw 0x00f759b590000004 0xc01eeb36b2000000 0x08e59db9ce003c00 0x211cb3b739c00780

def z1450 : W := mkw 0x0054093090000000 0x800a812612000000 0x08e59db9c0000000 0x211cb3b738000000

def z1451 : W := mkw 0x080822422080c233 0x0101044844101846 0xf61a6246318f83fa 0x5ec34c48c631f07f

def z1452 : W := mkw 0xf40084084a3f3188 0x1e8010810947e631 0x00000000087fb39e 0x80000000010ff673

def z1453 : W := mkw 0x0000081090000000 0x8000010212000000 0x9a059c79c0000000 0x3340b38f38000000

def z1454 : W := mkw 0x082b2ad7b080c233 0x8105655af6101846 0xfffffffff18fc3ff 0xfffffffffe31f87f

def z1455 : W := mkw 0xc077d4000f6f0004 0x380efa8001ede000 0x7e7ffc003fff809b 0xcfcfff8007fff013

def z1456 : W := mkw 0x2000000800102100 0x0400000100020420 0x08e401b80e703c00 0x211c803701ce0780

def z1457 : W := mkw 0xc077581097450004 0xb80eeb0212e8a000 0xfe7ffc79f7858001 0x7fcfff8f3ef0b000

def z1458 : W := mkw 0x34008c18d83a3188 0x868011831b074631 0x78059c79f87a339a 0x6f00b38f3f0f4673

def z1459 : W := mkw 0xb40084084a3e35c8 0x168010810947c6b9 0x00000000087e33fe 0x80000000010fc67f

def z1460 : W := mkw 0xb4008c18da3e35c8 0x968011831b47c6b9 0xff079e7ffe7e7fff 0xffe0f3cfffcfcfff

def z1461 : W := mkw 0x34008408483a3188 0x0680108109074631 0x1a040000087a339e 0x83408000010f4673

def z1462 : W := mkw 0x00d4593090000004 0xc01a8b2612000000 0x08059c39c0000000 0x2100b38738000000

def z1463 : W := mkw 0x0023089590000000 0x80046112b2000000 0xffe79ffff00e43ff 0xfffcf3fffe01c87f

def z1464 : W := mkw 0x080008109080c230 0x8100010212101846 0xfb059c79f18fc3ff 0xff60b38f3e31f87f

def z1465 : W := mkw 0x4054540005630004 0x280a8a8000ac6000 0x501c7c000ff38003 0x8a038f8001fe7000

def z1466 : W := mkw 0x205c036805d06b02 0x240b806d00ba0d60 0x1dfc03f80ff07f03 0x23bf807f01fe0fe0

def z1467 : W := mkw 0x90230085420414c0 0x12046010a8408298 0xa7e20387c60c7ce5 0xf4fc4070f8c18f9c

def z1468 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff0080084 0xffdffffffe010010

def z1469 : W := mkw 0x80ff7bf7b7c44e47 0xf01fef7ef6f889c8 0xfffffffff7844c61 0x7ffffffffef0898c

def z1470 : W := mkw 0x00dc7b72b0000007 0xc01b8f6e56000000 0xfe1ffe7ff0000000 0x7fc3ffcffe000000

def z1471 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfefffffff0058060 0x7fdffffffe00b00c

def z1472 : W := mkw 0xf40084084fff7b88 0x3e80108109ffef71 0x010000000fffff9f 0x8020000001fffff3

def z1473 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xf71ffe7ff18fc3ff 0xdee3ffcffe31f87f

def z1474 : W := mkw 0x08ff7bf7b0008037 0xc11fef7ef6001006 0xfffffffff00fc0fd 0xfffffffffe01f81f

def z1475 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x18e401f80e703f02 0x231c803f01ce07e0

def z1476 : W := mkw 0x00f759b595400804 0xe01eeb36b2a80100 0x08e59db9c6000c00 0x211cb3b738c00180

def z1477 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfffffffff0044061 0x7ffffffffe00880c

def z1478 : W := mkw 0x340084084d7a3188 0x2680108109af4631 0x000000000ffa339f 0x8000000001ff4673

def z1479 : W := mkw 0x08ff7bf7b080c237 0xc11fef7ef6101846 0xfffffffff183c3fe 0x7ffffffffe30787f

def z1480 : W := mkw 0x080822422080c233 0x0101044844101846 0xf21a6046318f83fe 0xde434c08c631f07f

def z1481 : W := mkw 0x00ff7bf7b0000007 0xc01fef7ef6000000 0xfefffffff00a0002 0xffdffffffe014000

def z1482 : W := mkw 0x94238c95da2e14c8 0x92847192bb45c299 0xf7039e47f00e43ff 0xdee073c8fe01c87f

def z1483 : W := mkw 0x285c236a25d0eb33 0x250b846d44ba1d66 0xfffe63fe0fffff67 0xbfffcc7fc1ffffec

def z1484 : W := mkw 0x2054012805502900 0x240a802500aa0520 0x0ee401b80e703c01 0xa1dc803701ce0780

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z8,z4,z5,z6]),(0,[z0,z1,z9,z9,z4,z5,z6]),(0,[z0,z1,z10,z9,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z11]),(0,[z0,z1,z12,z3,z4,z5,z6])],[(0,[z13,z0,z1,z9,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z6])],[(0,[z15,z16,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z18,z3,z4,z5,z6])],[(0,[z19,z20,z1,z3,z4,z5,z6]),(0,[z21,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z22,z23]),(0,[z24,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z27]),(0,[z0,z1,z3,z4,z5,z23,z23])],[(0,[z1,z28,z3,z29,z4,z5,z6]),(0,[z30,z0,z1,z3,z4,z5,z6]),(0,[z31,z1,z3,z29,z4,z5,z6]),(1,[z0,z32,z4,z5,z33,z6])],[(0,[z0,z1,z3,z34,z4,z5,z23]),(0,[z35,z0,z1,z9,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z37]),(0,[z38,z0,z1,z3,z4,z26,z5]),(1,[z0,z1,z3,z4,z5,z23])],[(0,[z0,z39,z1,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z5,z6])],[(0,[z41,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z42,z4,z5,z6]),(0,[z0,z1,z3,z4,z43,z5,z6])],[(0,[z15,z44,z1,z3,z4,z5,z6]),(0,[z45,z1,z3,z29,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z47])],[(0,[z15,z48,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z50,z5,z6]),(0,[z51,z0,z1,z9,z4,z5,z6]),(0,[z0,z31,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z6,z52])],[(0,[z53,z0,z1,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z54,z6])],[(0,[z1,z3,z29,z4,z5,z6,z55]),(0,[z0,z1,z3,z56,z4,z5,z6])],[(0,[z0,z1,z57,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z58,z5,z6])],[(0,[z59,z0,z1,z60,z4,z5,z6]),(0,[z0,z1,z3,z4,z61,z62,z6])]],
   [[(0,[z0,z1,z9,z4,z5,z27,z6]),(0,[z0,z1,z3,z4,z5,z47,z6])],[(0,[z63,z1,z3,z4,z64,z5,z6]),(1,[z0,z1,z32,z4,z5,z23]),(0,[z24,z0,z1,z65,z4,z5,z6])],[(0,[z0,z1,z3,z29,z4,z26,z5]),(0,[z0,z1,z66,z3,z4,z5,z6])],[(0,[z1,z28,z3,z67,z4,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z6]),(0,[z0,z69,z1,z3,z4,z5,z6]),(1,[z0,z1,z70,z4,z5,z6]),(0,[z0,z1,z3,z71,z4,z26,z5])],[(0,[z20,z1,z3,z4,z62,z5,z6]),(0,[z0,z1,z3,z4,z61,z33,z6]),(1,[z72,z1,z3,z4,z5,z6])],[(1,[z1,z28,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z5,z6,z73]),(0,[z0,z1,z9,z4,z5,z6,z74]),(0,[z0,z1,z3,z4,z75,z5,z6])],[(0,[z1,z28,z3,z4,z5,z33,z6]),(1,[z0,z1,z3,z4,z76,z5])],[(0,[z0,z1,z9,z4,z64,z5,z6]),(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z62,z6]),(0,[z79,z0,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z80,z4,z5,z6]),(0,[z0,z1,z32,z4,z26,z5,z6]),(0,[z0,z1,z10,z3,z4,z5,z6])],[(0,[z81,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z6,z82]),(0,[z83,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z6,z84]),(0,[z36,z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z86,z4,z5,z6]),(0,[z0,z1,z87,z3,z4,z5,z6]),(0,[z0,z1,z88,z3,z4,z5,z23])],[(0,[z15,z89,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z91]),(0,[z0,z1,z92,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z93,z6]),(0,[z0,z1,z3,z4,z94,z95,z5])],[(0,[z1,z3,z34,z29,z4,z5,z6]),(0,[z96,z0,z1,z9,z4,z5,z6])],[(0,[z20,z44,z1,z3,z4,z5,z6]),(0,[z0,z97,z1,z3,z4,z5,z6]),(0,[z0,z31,z3,z32,z4,z5,z6]),(0,[z72,z0,z1,z3,z4,z5,z6])],[(0,[z20,z1,z65,z3,z4,z5,z6])],[(0,[z98,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z99]),(1,[z0,z1,z100,z3,z4,z6])],[(0,[z0,z1,z3,z101,z4,z5,z6])]],
   [[(0,[z102,z0,z1,z3,z4,z5,z6])],[(1,[z103,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z52])],[],[],[(0,[z0,z1,z9,z4,z95,z5,z6])],[(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z32,z4,z5,z6]),(0,[z105,z106,z1,z3,z4,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z6])],[(0,[z59,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z61,z5,z108]),(0,[z0,z1,z3,z4,z109,z5,z6])],[(0,[z0,z1,z110,z9,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z111,z6]),(0,[z112,z0,z3,z4,z5,z6,z82]),(0,[z113,z0,z1,z3,z4,z5,z6])],[(0,[z35,z0,z1,z32,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z114,z6]),(0,[z16,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z115,z6]),(0,[z0,z1,z3,z4,z5,z6,z116]),(0,[z38,z0,z1,z3,z4,z5,z73])],[(0,[z90,z59,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z117,z6]),(0,[z0,z1,z118,z3,z4,z5,z6])],[(0,[z24,z20,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z22]),(1,[z119,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z42,z5,z6])],[(0,[z15,z0,z1,z3,z4,z5,z23]),(1,[z120,z1,z3,z4,z5,z6]),(1,[z77,z1,z3,z4,z5,z6]),(0,[z0,z1,z110,z3,z4,z61,z6])],[(0,[z1,z28,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z121,z6]),(1,[z0,z44,z3,z4,z5,z111])],[(0,[z122,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z82]),(0,[z0,z1,z3,z4,z123,z5,z6])]],
   [[(0,[z0,z1,z124,z3,z4,z5,z6]),(0,[z0,z1,z107,z32,z4,z5,z6]),(0,[z0,z1,z125,z3,z4,z26,z5])],[(1,[z15,z1,z3,z80,z5,z6])],[(0,[z1,z126,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z127,z5,z6]),(0,[z51,z128,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z129,z6]),(0,[z0,z1,z3,z4,z5,z130,z6])],[(0,[z0,z1,z3,z4,z5,z6,z91]),(0,[z0,z1,z3,z4,z131,z5,z6]),(1,[z41,z1,z3,z4,z5,z6]),(0,[z0,z1,z132,z3,z4,z5,z6])],[(0,[z89,z0,z1,z133,z4,z5,z6]),(0,[z1,z28,z134,z3,z4,z5,z6]),(0,[z135,z15,z1,z3,z4,z5,z6]),(0,[z24,z0,z1,z136,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z137,z6])],[(0,[z59,z1,z28,z3,z4,z5,z6]),(1,[z0,z31,z3,z4,z62,z6])],[(0,[z0,z1,z138,z3,z4,z5,z6]),(0,[z0,z1,z139,z3,z4,z5,z6]),(0,[z0,z1,z9,z140,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z85,z6]),(0,[z0,z1,z3,z141,z4,z5,z6]),(0,[z0,z44,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z142,z4,z5,z6])],[(0,[z63,z1,z3,z29,z4,z5,z6]),(0,[z143,z0,z1,z3,z4,z5,z6])],[(0,[z89,z0,z1,z3,z4,z5,z23]),(1,[z13,z1,z3,z4,z5,z91]),(0,[z105,z0,z1,z134,z4,z5,z6])],[(0,[z15,z24,z1,z3,z4,z5,z6]),(0,[z15,z46,z1,z3,z4,z5,z6]),(0,[z1,z9,z3,z29,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z144,z6]),(0,[z0,z1,z3,z4,z5,z145,z6]),(0,[z0,z1,z32,z4,z5,z6,z91]),(0,[z44,z1,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z147]),(0,[z148,z1,z3,z4,z5,z149,z6])],[(0,[z0,z1,z32,z4,z5,z27,z6]),(0,[z0,z119,z1,z3,z4,z5,z6])],[(0,[z1,z134,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z150,z5,z6]),(0,[z0,z1,z3,z32,z4,z26,z5]),(1,[z36,z0,z3,z151,z5,z6]),(0,[z0,z48,z1,z3,z152,z5,z6]),(0,[z105,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z153])],[(0,[z15,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z154,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z155,z9,z4,z5,z6]),(0,[z0,z1,z156,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z23])],[(0,[z20,z1,z3,z4,z5,z114,z6]),(0,[z0,z1,z9,z29,z4,z5,z6]),(0,[z38,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z157,z5,z6])],[],[(0,[z20,z1,z3,z4,z5,z158,z6]),(0,[z0,z1,z3,z4,z5,z6,z159]),(0,[z0,z1,z3,z4,z5,z6,z160]),(1,[z0,z1,z110,z3,z4,z26])]],
   [[(0,[z20,z1,z60,z3,z4,z5,z6]),(1,[z15,z1,z3,z4,z26,z5]),(0,[z15,z0,z1,z3,z161,z5,z6]),(0,[z0,z1,z162,z3,z4,z5,z6]),(0,[z163,z0,z1,z3,z4,z5,z6])],[(0,[z21,z1,z3,z34,z4,z5,z6]),(0,[z0,z1,z32,z4,z64,z5,z6]),(0,[z112,z38,z0,z1,z3,z4,z5]),(0,[z0,z1,z134,z3,z4,z26,z5])],[(0,[z20,z1,z88,z3,z4,z5,z6]),(1,[z1,z3,z56,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z116])],[(0,[z0,z44,z1,z70,z4,z5,z6])],[(0,[z15,z7,z1,z3,z4,z5,z6]),(0,[z0,z1,z164,z3,z4,z5,z6]),(0,[z165,z0,z1,z9,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z166]),(0,[z0,z1,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z4,z5,z168,z6]),(1,[z0,z1,z3,z80,z61,z6])],[(0,[z0,z44,z1,z3,z4,z5,z111])],[(0,[z105,z0,z1,z32,z4,z5,z6]),(0,[z105,z0,z1,z110,z3,z4,z6])],[(0,[z89,z1,z28,z3,z4,z5,z6]),(0,[z53,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z169,z6]),(0,[z0,z1,z3,z4,z170,z5,z6]),(0,[z1,z3,z80,z29,z4,z5,z6]),(1,[z1,z3,z29,z4,z26,z5]),(0,[z0,z1,z65,z3,z123,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z171]),(0,[z0,z1,z172,z3,z4,z5,z6])],[(0,[z173,z0,z1,z3,z4,z5,z6]),(1,[z69,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z32,z4,z5,z6])],[(0,[z63,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z80,z152,z5,z6]),(1,[z0,z1,z87,z4,z5,z6]),(0,[z0,z174,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z6,z23]),(0,[z0,z1,z9,z4,z5,z149,z6])],[(0,[z20,z1,z3,z4,z5,z6,z175]),(0,[z0,z1,z176,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z161,z5,z6]),(0,[z177,z1,z3,z29,z4,z5,z6])],[(0,[z15,z0,z1,z3,z29,z5,z6]),(0,[z0,z1,z110,z134,z3,z4,z6]),(0,[z0,z1,z3,z61,z5,z149,z6])],[(0,[z0,z1,z9,z4,z5,z6,z73])],[(0,[z0,z1,z32,z4,z95,z5,z6]),(0,[z0,z1,z9,z4,z5,z33,z6]),(0,[z112,z0,z1,z178,z4,z5,z6]),(0,[z0,z1,z179,z3,z4,z5,z6])],[]],
   [[(0,[z0,z1,z3,z4,z180,z5,z6]),(0,[z181,z0,z1,z3,z4,z5,z6]),(0,[z182,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z183])],[(0,[z15,z1,z136,z3,z4,z5,z6]),(0,[z0,z1,z184,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z6])],[(0,[z15,z1,z3,z4,z5,z186,z6]),(1,[z90,z1,z3,z4,z5,z22])],[(0,[z15,z1,z3,z152,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z187,z6]),(0,[z188,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z189,z6]),(0,[z0,z1,z3,z190,z4,z5,z23]),(0,[z0,z191,z1,z3,z4,z26,z5])],[(0,[z1,z28,z3,z4,z5,z149,z6]),(0,[z13,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z192,z3,z4,z5,z6]),(0,[z105,z0,z1,z3,z193,z5,z6]),(1,[z0,z1,z194,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z6])],[(0,[z195,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z84]),(0,[z0,z1,z3,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z186])],[(0,[z0,z1,z3,z4,z5,z197,z6]),(0,[z0,z1,z3,z4,z5,z114,z23])],[(0,[z0,z1,z9,z134,z4,z5,z6]),(0,[z0,z1,z194,z4,z5,z149,z6]),(0,[z0,z1,z3,z4,z198,z5,z6])],[(0,[z199,z0,z1,z3,z4,z5,z6]),(0,[z35,z20,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z200,z6]),(0,[z0,z1,z3,z4,z5,z201,z6]),(0,[z0,z1,z107,z3,z4,z5,z175])],[(1,[z0,z1,z202,z4,z5,z6]),(0,[z1,z60,z3,z29,z4,z5,z6]),(0,[z0,z1,z60,z3,z4,z5,z23]),(0,[z0,z1,z3,z203,z4,z5,z6]),(0,[z0,z1,z3,z204,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z205,z6]),(0,[z0,z1,z9,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z206,z5,z6]),(0,[z105,z0,z1,z65,z4,z5,z6])],[(0,[z0,z1,z3,z207,z4,z5,z6]),(0,[z165,z0,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z6,z82]),(0,[z0,z1,z3,z4,z5,z208,z6]),(0,[z0,z1,z3,z4,z5,z6,z209]),(0,[z13,z0,z1,z3,z4,z5,z6])],[(0,[z51,z20,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z64,z6]),(0,[z0,z1,z32,z4,z198,z5,z6]),(0,[z112,z210,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z211,z6]),(0,[z0,z1,z32,z4,z5,z201,z6]),(0,[z0,z212,z1,z3,z4,z26,z5]),(0,[z36,z0,z1,z3,z4,z17,z6]),(0,[z78,z0,z1,z3,z4,z33,z6])]],
   [[(0,[z20,z48,z1,z3,z4,z5,z6])],[(0,[z35,z0,z1,z3,z4,z5,z6]),(0,[z213,z0,z1,z3,z4,z5,z6]),(0,[z214,z0,z1,z3,z4,z5,z6])],[(0,[z36,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z215,z5,z6]),(0,[z0,z1,z3,z71,z4,z5,z6])],[(0,[z0,z216,z1,z3,z4,z5,z6]),(0,[z0,z1,z217,z3,z4,z5,z6]),(0,[z1,z218,z3,z29,z4,z5,z6]),(0,[z38,z0,z1,z3,z71,z5,z6])],[(0,[z219,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z220,z5,z6]),(0,[z0,z1,z9,z4,z221,z5,z6]),(0,[z0,z1,z222,z3,z4,z5,z6]),(0,[z223,z0,z1,z3,z4,z5,z6])],[(0,[z20,z1,z136,z3,z4,z5,z6])],[(0,[z51,z0,z1,z3,z4,z5,z6]),(0,[z224,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z32,z4,z5,z6]),(0,[z36,z0,z1,z3,z152,z5,z6]),(0,[z0,z225,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z185,z5]),(0,[z112,z0,z1,z3,z71,z4,z5]),(0,[z0,z1,z3,z4,z5,z226,z6]),(0,[z0,z1,z3,z4,z5,z227,z6])],[(0,[z0,z1,z228,z3,z4,z5,z6]),(0,[z1,z3,z67,z29,z4,z5,z6]),(0,[z0,z1,z32,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z22]),(0,[z212,z1,z184,z3,z4,z5,z6])],[(0,[z15,z90,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z71,z4,z5,z6]),(0,[z0,z1,z9,z4,z61,z5,z6]),(0,[z38,z0,z44,z1,z3,z4,z5]),(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z0,z1,z230,z3,z4,z5,z6])],[(0,[z1,z3,z4,z64,z5,z114,z6]),(0,[z0,z1,z194,z3,z4,z5,z6])],[(0,[z231,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z232,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z6,z233]),(0,[z63,z0,z1,z3,z4,z64,z6]),(0,[z0,z234,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z47,z6]),(1,[z0,z1,z178,z4,z5,z6]),(0,[z0,z1,z110,z3,z4,z198,z6])],[(0,[z235,z0,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z80,z4,z5,z6]),(0,[z236,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z237])],[(0,[z0,z1,z3,z4,z5,z6,z238]),(0,[z239,z0,z1,z3,z4,z5,z6]),(0,[z0,z240,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z241,z5,z6]),(0,[z1,z3,z29,z4,z242,z5,z6]),(0,[z1,z3,z29,z4,z4,z5,z6])],[(0,[z36,z1,z28,z3,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z6]),(0,[z51,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z149])],[(1,[z1,z9,z29,z4,z5,z6]),(1,[z38,z0,z1,z3,z5,z73])],[(0,[z1,z28,z3,z4,z61,z5,z6]),(0,[z244,z20,z1,z3,z4,z5,z6]),(1,[z15,z1,z3,z5,z149,z6]),(0,[z16,z0,z1,z9,z4,z5,z6])],[(1,[z1,z3,z4,z5,z6,z160])],[(0,[z0,z1,z3,z4,z245,z5,z6]),(1,[z0,z1,z4,z5,z246,z6])],[(0,[z105,z20,z1,z3,z4,z5,z6]),(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z78,z1,z3,z29,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z6,z23])],[(0,[z0,z1,z3,z4,z5,z6,z247]),(1,[z15,z1,z9,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z6,z73]),(0,[z248,z0,z1,z3,z4,z151,z5]),(0,[z0,z1,z3,z4,z5,z27,z6])],[(1,[z0,z212,z9,z4,z5,z6]),(0,[z0,z249,z1,z3,z4,z5,z6])],[(0,[z250,z15,z1,z3,z4,z5,z6]),(0,[z251,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z252,z3,z4,z5,z6]),(1,[z0,z1,z65,z123,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z108])],[(0,[z0,z1,z3,z4,z26,z64,z5]),(0,[z0,z1,z3,z4,z253,z5,z6]),(0,[z0,z48,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z254,z5,z6]),(0,[z0,z1,z255,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z6])],[(0,[z257,z0,z1,z3,z4,z5,z6]),(0,[z244,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z258,z5,z6]),(0,[z0,z1,z3,z4,z259,z5,z6]),(0,[z78,z225,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z260,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z74]),(1,[z210,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z261,z6]),(0,[z0,z1,z3,z4,z157,z61,z5]),(0,[z0,z1,z262,z3,z4,z5,z23])],[(0,[z263,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z5,z6]),(1,[z0,z1,z3,z4,z264,z6])],[(0,[z1,z3,z29,z4,z62,z5,z6]),(0,[z0,z1,z3,z265,z4,z5,z6]),(0,[z0,z1,z266,z3,z4,z5,z6]),(0,[z0,z31,z1,z3,z4,z62,z6]),(0,[z0,z1,z136,z3,z4,z5,z23]),(0,[z0,z1,z125,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z267,z3,z4,z5,z6]),(0,[z0,z1,z268,z3,z4,z5,z6]),(0,[z63,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z32,z4,z253,z5,z6]),(0,[z0,z1,z3,z4,z269,z151,z5]),(1,[z105,z0,z1,z3,z4,z23])],[(0,[z15,z1,z107,z3,z4,z5,z6]),(0,[z0,z1,z270,z3,z4,z5,z6])],[(0,[z48,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z271]),(1,[z143,z1,z3,z4,z5,z6]),(1,[z272,z1,z3,z4,z5,z6]),(0,[z0,z1,z110,z3,z4,z5,z6])],[(0,[z20,z0,z1,z3,z4,z5,z23]),(0,[z15,z59,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z71,z151,z5,z6]),(1,[z0,z1,z3,z4,z269,z5]),(0,[z273,z0,z1,z3,z4,z26,z5])],[(0,[z21,z0,z1,z34,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z111,z6]),(0,[z0,z31,z1,z3,z4,z33,z6]),(0,[z0,z1,z3,z4,z5,z6,z274])],[(0,[z120,z0,z1,z3,z4,z5,z6]),(0,[z275,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z276,z6])],[(0,[z0,z1,z277,z3,z4,z5,z6])],[(0,[z0,z278,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z117,z6]),(0,[z279,z0,z1,z3,z4,z5,z6]),(1,[z1,z184,z3,z4,z5,z6]),(0,[z280,z0,z1,z3,z4,z5,z6])],[(0,[z59,z1,z3,z4,z5,z6,z91]),(0,[z0,z1,z3,z4,z5,z6,z281]),(0,[z282,z0,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z80,z4,z5,z23])],[(0,[z36,z120,z1,z3,z4,z5,z6])],[(0,[z0,z283,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z123,z5,z6]),(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z95,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z285]),(0,[z0,z1,z3,z4,z26,z58,z5])],[(0,[z0,z1,z3,z4,z5,z6,z286]),(0,[z0,z1,z110,z32,z4,z5,z6]),(0,[z36,z0,z1,z287,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z288]),(0,[z148,z0,z1,z3,z4,z5,z6]),(0,[z0,z289,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z290,z4,z26,z5])],[(0,[z15,z1,z3,z4,z127,z5,z6]),(0,[z30,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z6,z291]),(0,[z0,z1,z292,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z6,z91]),(0,[z0,z293,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z91,z23]),(0,[z0,z1,z3,z4,z5,z186,z111])]],
   [[(0,[z38,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z294,z3,z4,z5,z6]),(0,[z0,z1,z32,z32,z4,z5,z6]),(1,[z0,z1,z9,z4,z26,z5]),(0,[z78,z0,z1,z3,z295,z5,z6]),(0,[z0,z1,z296,z3,z4,z5,z6]),(1,[z297,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z6,z23])],[(0,[z1,z3,z29,z4,z151,z5,z6]),(1,[z0,z1,z86,z4,z5,z6]),(0,[z0,z31,z1,z87,z4,z5,z6]),(0,[z0,z1,z298,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z299,z6]),(0,[z0,z1,z3,z123,z5,z149,z6]),(0,[z0,z1,z3,z4,z5,z300,z6]),(1,[z0,z1,z3,z4,z5,z108])],[(0,[z20,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z301])],[(0,[z0,z1,z3,z4,z5,z302,z6]),(0,[z0,z1,z3,z4,z5,z303,z6]),(0,[z0,z1,z3,z4,z198,z6,z23])],[(0,[z0,z1,z3,z4,z5,z6,z304])],[(0,[z21,z0,z1,z3,z4,z5,z23]),(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z306,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z6,z82]),(1,[z0,z1,z3,z4,z5,z307]),(0,[z0,z1,z3,z4,z26,z61,z5])],[(0,[z16,z0,z1,z32,z4,z5,z6]),(0,[z0,z212,z1,z9,z4,z5,z6])],[(0,[z0,z1,z155,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z308,z6]),(0,[z0,z1,z3,z4,z5,z6,z309])],[(1,[z1,z217,z3,z4,z5,z6]),(0,[z0,z1,z310,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z22,z6]),(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z311,z0,z1,z3,z4,z5,z6]),(0,[z0,z312,z1,z3,z4,z5,z6]),(0,[z0,z313,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z314,z5,z6]),(1,[z1,z3,z4,z220,z5,z6]),(0,[z0,z1,z3,z4,z5,z47,z23]),(0,[z38,z0,z1,z3,z4,z5,z186]),(0,[z0,z1,z315,z3,z4,z5,z6])],[(0,[z20,z7,z1,z3,z4,z5,z6]),(0,[z316,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z317,z4,z5,z6])],[(0,[z1,z28,z3,z34,z4,z5,z6]),(1,[z225,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z318,z6])],[(0,[z135,z0,z1,z3,z4,z5,z6]),(1,[z1,z32,z29,z4,z5,z6]),(0,[z0,z1,z134,z4,z95,z5,z6]),(0,[z0,z1,z3,z319,z4,z5,z6]),(0,[z0,z1,z3,z4,z320,z5,z6])],[(0,[z30,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z321,z5,z6]),(0,[z0,z1,z3,z140,z4,z5,z6])],[(1,[z1,z28,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z322,z6]),(0,[z122,z1,z3,z4,z151,z5,z6])],[(0,[z0,z1,z323,z3,z4,z5,z6])]],
   [[(0,[z20,z1,z3,z4,z5,z6,z23]),(0,[z0,z324,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z325,z4,z5,z6])],[(0,[z20,z1,z3,z4,z161,z5,z6]),(0,[z30,z0,z1,z3,z161,z5,z6]),(0,[z0,z1,z3,z4,z5,z326,z6]),(0,[z0,z1,z3,z327,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z307,z6]),(0,[z0,z1,z3,z4,z5,z6,z328])],[(0,[z20,z1,z1,z3,z4,z5,z6]),(0,[z36,z0,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z329,z6])],[(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z63,z0,z1,z32,z4,z5,z6]),(0,[z38,z0,z1,z32,z4,z5,z6]),(0,[z331,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z149,z6]),(0,[z0,z1,z3,z4,z332,z5,z6])],[(0,[z21,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z29,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z5,z333]),(0,[z334,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z335,z3,z4,z5,z6]),(0,[z0,z1,z3,z336,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z337]),(0,[z0,z1,z3,z4,z5,z6,z338]),(0,[z0,z1,z3,z4,z339,z5,z6]),(1,[z0,z1,z3,z4,z5,z227])],[(0,[z16,z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z340,z6]),(0,[z0,z1,z3,z71,z4,z5,z186])],[],[(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z90,z1,z3,z29,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z95,z6]),(1,[z0,z1,z3,z4,z26,z5])],[(0,[z20,z1,z3,z4,z5,z186,z6])],[(0,[z20,z1,z3,z152,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z342]),(0,[z0,z1,z343,z9,z4,z5,z6]),(0,[z344,z0,z1,z3,z4,z5,z6])],[(0,[z7,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z28,z3,z4,z5,z23]),(0,[z177,z0,z1,z3,z4,z5,z6]),(0,[z0,z212,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z345,z5,z6])],[(0,[z30,z0,z1,z3,z29,z5,z6]),(1,[z0,z1,z3,z4,z5,z346]),(0,[z0,z1,z9,z4,z5,z347,z6]),(0,[z0,z1,z3,z4,z348,z5,z6])],[(0,[z0,z1,z3,z4,z5,z349,z6]),(0,[z331,z0,z1,z32,z4,z5,z6]),(1,[z1,z252,z3,z4,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z23])],[(0,[z105,z0,z222,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z309])]],
   [[(0,[z350,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z295,z5,z6]),(0,[z41,z44,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z351])],[(0,[z96,z20,z1,z3,z4,z5,z6]),(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z26,z5,z6]),(0,[z0,z31,z3,z4,z62,z5,z6]),(0,[z0,z1,z3,z4,z5,z149,z6])],[(0,[z353,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z4,z5,z6]),(0,[z78,z15,z1,z3,z4,z5,z6]),(0,[z0,z354,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z355,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z6,z356]),(0,[z357,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z32,z4,z26,z5]),(0,[z0,z1,z3,z4,z5,z358,z6]),(0,[z0,z1,z3,z4,z359,z5,z6])],[(0,[z0,z7,z1,z3,z4,z5,z23]),(0,[z112,z15,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z198,z5,z6]),(0,[z46,z1,z3,z29,z4,z5,z6]),(0,[z210,z0,z1,z3,z4,z5,z6]),(0,[z0,z44,z1,z3,z71,z4,z5]),(0,[z0,z1,z360,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z73])],[(0,[z0,z1,z3,z361,z4,z5,z6]),(0,[z362,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z33,z6]),(0,[z0,z1,z3,z4,z363,z5,z6]),(0,[z364,z0,z1,z3,z4,z5,z6]),(0,[z365,z0,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z203,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z6,z175])],[(0,[z15,z1,z9,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z149,z6]),(0,[z0,z1,z3,z4,z366,z5,z6]),(0,[z0,z367,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z328]),(0,[z0,z1,z3,z4,z5,z368,z6])],[(0,[z0,z1,z3,z4,z369,z5,z6]),(0,[z0,z1,z3,z370,z4,z5,z6])],[(0,[z1,z28,z3,z4,z371,z5,z6]),(0,[z372,z0,z1,z3,z4,z5,z6]),(0,[z212,z1,z3,z29,z4,z5,z6]),(0,[z0,z212,z1,z32,z4,z5,z6]),(0,[z373,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z318,z6])],[(0,[z90,z0,z1,z3,z4,z26,z5])],[(0,[z0,z1,z374,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z161,z5,z23]),(0,[z112,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z33,z6]),(1,[z1,z277,z3,z4,z5,z6]),(0,[z0,z375,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z376,z5,z6])],[(0,[z15,z30,z1,z3,z4,z5,z6]),(0,[z24,z0,z1,z3,z4,z5,z23])],[(0,[z377,z15,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z71,z4,z5,z6]),(1,[z0,z1,z325,z4,z5,z6])],[(0,[z378,z0,z1,z3,z4,z5,z6]),(0,[z15,z1,z217,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z6,z82]),(0,[z78,z0,z1,z9,z4,z5,z6]),(1,[z283,z1,z3,z4,z5,z6]),(1,[z379,z1,z3,z4,z5,z6])]],
   [[(0,[z15,z0,z1,z3,z80,z5,z6]),(0,[z105,z0,z380,z3,z4,z5,z6])],[(0,[z21,z0,z1,z60,z4,z5,z6]),(0,[z0,z1,z3,z381,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z382])],[(0,[z20,z1,z3,z4,z5,z47,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z383,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z62,z5,z6]),(0,[z1,z384,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z23])],[(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z386,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z387,z5,z6]),(0,[z0,z1,z3,z152,z4,z5,z23]),(0,[z38,z0,z1,z3,z4,z388,z6])],[],[(0,[z16,z20,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z4,z5,z389,z6])],[(0,[z390,z0,z1,z3,z4,z5,z6])],[(0,[z59,z0,z1,z3,z4,z26,z5]),(1,[z0,z1,z3,z5,z322,z6])],[],[(0,[z0,z1,z3,z4,z391,z5,z6]),(0,[z392,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z73])],[(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z221,z5,z6]),(0,[z36,z119,z1,z3,z4,z5,z6])],[(0,[z1,z28,z65,z3,z4,z5,z6]),(0,[z24,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z175])],[(0,[z0,z1,z3,z4,z5,z394,z6]),(0,[z63,z1,z3,z34,z4,z5,z6]),(0,[z0,z1,z3,z32,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z26,z5])],[(0,[z16,z0,z1,z3,z4,z5,z6]),(0,[z395,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z61,z5,z6])]],
   [[(0,[z396,z0,z1,z3,z4,z5,z6])],[(0,[z379,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z88,z3,z4,z149,z6]),(0,[z0,z1,z3,z4,z397,z5,z6])],[(1,[z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z76,z5,z6])],[(0,[z63,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z34,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z27,z6]),(0,[z0,z1,z398,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z399,z6]),(1,[z0,z48,z3,z152,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z400]),(0,[z0,z1,z134,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z26,z198,z5])],[(0,[z1,z28,z3,z4,z151,z5,z6]),(0,[z0,z1,z32,z4,z61,z5,z6]),(0,[z78,z0,z31,z3,z4,z5,z6])],[(1,[z0,z1,z401,z4,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z47])],[(0,[z20,z1,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z402,z5,z6]),(0,[z0,z1,z3,z403,z4,z5,z6])],[(0,[z0,z1,z65,z4,z123,z5,z6])],[(0,[z251,z20,z1,z3,z4,z5,z6]),(1,[z1,z3,z29,z4,z5,z6]),(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z405,z4,z5,z6]),(0,[z0,z1,z65,z3,z4,z26,z5]),(1,[z24,z0,z1,z136,z5,z6]),(0,[z0,z1,z3,z406,z4,z5,z6]),(0,[z182,z0,z1,z3,z4,z5,z23])],[(0,[z20,z1,z3,z4,z5,z111,z6]),(0,[z0,z1,z3,z8,z4,z5,z6]),(0,[z0,z407,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z64,z5,z6]),(0,[z0,z408,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z80,z123,z5,z6])],[(0,[z1,z28,z3,z4,z5,z22,z6]),(0,[z0,z1,z100,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z409]),(0,[z0,z1,z3,z290,z4,z5,z6])],[(1,[z15,z1,z32,z4,z5,z6]),(0,[z16,z63,z1,z3,z4,z5,z6])],[(0,[z15,z1,z110,z3,z4,z5,z6]),(0,[z0,z1,z134,z32,z4,z5,z6])],[(1,[z0,z1,z9,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z5,z410]),(1,[z0,z1,z3,z4,z26,z23])]],
   [[(0,[z411,z0,z1,z3,z4,z5,z6]),(0,[z143,z48,z1,z3,z4,z5,z6]),(0,[z412,z0,z1,z3,z4,z26,z5])],[(0,[z250,z0,z1,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z123,z5,z6]),(0,[z251,z0,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z413,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z414])],[(0,[z0,z415,z1,z3,z4,z5,z6]),(0,[z15,z38,z1,z3,z4,z5,z6]),(1,[z51,z0,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z151,z26,z5])],[(1,[z20,z1,z3,z4,z26,z5]),(0,[z0,z416,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z417,z6]),(0,[z0,z1,z3,z4,z418,z5,z6])],[(0,[z112,z283,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z419,z4,z5,z6]),(0,[z0,z1,z3,z420,z4,z5,z6]),(0,[z0,z421,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z422,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z6,z91]),(0,[z0,z1,z423,z32,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z424]),(0,[z13,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z6,z425]),(0,[z0,z191,z1,z3,z4,z5,z6])],[(1,[z1,z3,z67,z4,z5,z6]),(0,[z15,z1,z3,z4,z95,z5,z6]),(0,[z426,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z427,z4,z5,z6])],[(0,[z0,z1,z126,z3,z4,z5,z6]),(0,[z272,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z428,z5,z6])],[(0,[z0,z429,z1,z3,z4,z5,z6])],[(0,[z35,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z26,z430,z5]),(0,[z0,z1,z3,z4,z26,z5,z5])],[(0,[z0,z1,z3,z34,z4,z26,z5]),(0,[z1,z3,z29,z4,z5,z114,z6]),(0,[z0,z1,z3,z92,z4,z5,z6]),(0,[z431,z0,z1,z3,z4,z5,z6])],[(0,[z432,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z433,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z434,z6]),(0,[z0,z1,z3,z4,z26,z5,z111]),(0,[z0,z1,z435,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z436,z5,z6]),(0,[z0,z1,z3,z437,z4,z5,z6]),(1,[z105,z0,z1,z4,z27,z6])],[(0,[z1,z28,z60,z3,z4,z5,z6]),(0,[z0,z1,z3,z438,z4,z5,z6]),(0,[z51,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z439,z6]),(0,[z0,z1,z88,z3,z80,z5,z6]),(0,[z440,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z55]),(0,[z306,z0,z1,z3,z4,z5,z6]),(0,[z441,z0,z1,z3,z4,z5,z6]),(0,[z248,z0,z1,z3,z4,z5,z6]),(0,[z0,z31,z1,z3,z4,z26,z5])],[(0,[z199,z1,z28,z3,z4,z5,z6]),(0,[z1,z28,z88,z3,z4,z5,z6]),(0,[z90,z0,z1,z9,z4,z5,z6]),(0,[z0,z212,z1,z3,z4,z5,z6]),(0,[z442,z0,z1,z3,z4,z26,z5])],[],[(0,[z0,z1,z3,z443,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z6,z444]),(0,[z0,z1,z3,z4,z5,z111,z23])],[(0,[z13,z1,z28,z3,z4,z5,z6]),(0,[z1,z3,z4,z445,z151,z5,z6]),(0,[z0,z1,z446,z3,z4,z5,z6]),(0,[z297,z0,z1,z3,z4,z5,z6])],[(0,[z0,z447,z1,z3,z4,z5,z6]),(0,[z448,z212,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z5,z82])],[(0,[z0,z1,z3,z4,z76,z64,z5])],[(0,[z0,z1,z3,z4,z5,z6,z333]),(0,[z0,z1,z3,z4,z149,z6,z23])],[(0,[z35,z1,z28,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z169,z6]),(0,[z59,z1,z3,z29,z4,z5,z6]),(0,[z15,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z269,z5,z6]),(0,[z78,z0,z1,z327,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z82,z23])],[(0,[z1,z28,z3,z4,z5,z6,z175])],[(0,[z1,z3,z32,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z449,z5,z6]),(0,[z0,z1,z9,z4,z62,z5,z6]),(0,[z0,z3,z4,z5,z111,z6,z82]),(0,[z0,z1,z3,z4,z123,z5,z23]),(0,[z0,z1,z88,z3,z4,z5,z227])],[(0,[z44,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z60,z3,z4,z26,z5]),(0,[z15,z324,z1,z3,z4,z5,z6]),(0,[z0,z1,z450,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z82]),(0,[z0,z451,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z452])],[(0,[z0,z1,z3,z453,z4,z5,z6]),(0,[z46,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z80,z4,z149,z6]),(0,[z0,z1,z3,z4,z454,z26,z5])],[(0,[z51,z1,z28,z3,z4,z5,z6]),(0,[z0,z45,z1,z3,z4,z5,z6]),(0,[z0,z1,z455,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z425]),(0,[z0,z1,z88,z3,z4,z26,z5])],[(0,[z59,z0,z1,z9,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z410])]],
   [[(0,[z15,z1,z3,z29,z4,z5,z6]),(1,[z0,z31,z32,z4,z5,z6])],[(1,[z0,z1,z3,z413,z5,z6]),(0,[z0,z1,z3,z4,z5,z456,z6]),(0,[z0,z249,z1,z3,z4,z5,z23])],[(0,[z15,z0,z1,z3,z5,z149,z6]),(0,[z0,z1,z3,z4,z5,z6,z457])],[(1,[z0,z1,z3,z4,z62,z23]),(0,[z0,z1,z3,z5,z186,z6,z73])],[(0,[z1,z124,z3,z29,z4,z5,z6]),(0,[z0,z1,z458,z3,z4,z5,z6]),(0,[z112,z0,z1,z9,z4,z5,z6]),(1,[z0,z1,z3,z4,z149,z23])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z48,z1,z86,z4,z5,z6]),(0,[z0,z1,z88,z3,z4,z5,z309])],[(0,[z0,z1,z343,z3,z4,z5,z6]),(0,[z0,z459,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z460,z5,z6]),(0,[z0,z1,z450,z32,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z461,z4,z5,z6])],[(0,[z0,z1,z3,z4,z462,z5,z6]),(1,[z0,z1,z3,z4,z33,z23]),(0,[z0,z1,z3,z4,z5,z463,z6])],[(0,[z90,z0,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z198,z5,z6]),(0,[z0,z1,z3,z4,z61,z6,z23])],[(0,[z89,z1,z3,z29,z4,z5,z6]),(1,[z20,z7,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z6,z23]),(0,[z46,z0,z1,z107,z4,z5,z6]),(0,[z1,z3,z4,z5,z54,z149,z6])],[(0,[z1,z3,z29,z4,z161,z5,z6])],[(0,[z20,z1,z9,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z149,z6]),(0,[z0,z1,z9,z4,z151,z5,z6]),(0,[z0,z1,z464,z3,z4,z5,z6])],[(0,[z24,z0,z1,z136,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z6,z23]),(1,[z0,z1,z3,z4,z6,z465]),(0,[z0,z1,z3,z466,z4,z5,z6])],[(0,[z0,z1,z3,z4,z467,z5,z6])]],
   [[(0,[z15,z1,z3,z4,z5,z6,z73]),(1,[z0,z1,z3,z4,z5,z333]),(0,[z0,z1,z3,z4,z468,z5,z6]),(0,[z0,z1,z65,z9,z4,z5,z6]),(0,[z24,z0,z1,z3,z123,z5,z6])],[(1,[z59,z1,z60,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z33,z6]),(0,[z0,z469,z1,z3,z4,z5,z6])],[(0,[z78,z20,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z136,z3,z80,z5,z6]),(0,[z0,z1,z3,z4,z470,z5,z6]),(0,[z471,z0,z1,z3,z4,z5,z6])],[(0,[z20,z30,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z472,z6])],[(0,[z20,z1,z3,z71,z4,z5,z6]),(0,[z1,z3,z473,z29,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z186,z6]),(0,[z90,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z22,z6]),(0,[z0,z1,z3,z4,z5,z6,z474])],[(0,[z1,z3,z29,z152,z4,z5,z6]),(0,[z0,z1,z475,z3,z4,z5,z6]),(0,[z0,z1,z32,z355,z4,z5,z6]),(0,[z273,z0,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z6])],[(0,[z105,z1,z28,z3,z4,z5,z6]),(0,[z362,z0,z1,z3,z4,z5,z6]),(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z477])],[(0,[z15,z1,z374,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z478,z6]),(0,[z0,z1,z3,z4,z5,z479,z23])],[(0,[z20,z1,z228,z3,z4,z5,z6]),(1,[z0,z1,z327,z4,z5,z6])],[(1,[z20,z1,z9,z4,z5,z6]),(0,[z36,z0,z3,z4,z151,z5,z6]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z413,z5,z6])],[(0,[z0,z1,z3,z4,z480,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z22]),(0,[z0,z44,z1,z3,z4,z26,z5])],[(0,[z0,z1,z3,z4,z5,z144,z6]),(1,[z63,z1,z3,z4,z64,z6]),(0,[z0,z48,z1,z3,z4,z26,z5]),(0,[z112,z0,z1,z3,z4,z5,z6])],[(0,[z89,z0,z1,z3,z4,z26,z5]),(0,[z1,z28,z3,z80,z4,z5,z6]),(0,[z0,z1,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z481])],[(0,[z0,z1,z482,z3,z4,z5,z6]),(0,[z0,z1,z3,z483,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z484]),(0,[z485,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z486,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z487])],[]],
   [[(0,[z46,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z488,z1,z3,z4,z5,z6,z73])],[(0,[z0,z1,z3,z4,z5,z6,z489]),(0,[z30,z0,z1,z3,z80,z5,z6]),(0,[z0,z1,z3,z473,z4,z5,z6]),(0,[z13,z90,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z26,z5,z23])],[(1,[z20,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z272,z31,z1,z3,z4,z5,z6]),(0,[z105,z103,z1,z3,z4,z5,z6])],[(0,[z0,z490,z1,z3,z4,z5,z6])],[(1,[z106,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z491]),(0,[z0,z1,z3,z4,z198,z5,z23])],[(0,[z20,z0,z1,z3,z4,z26,z5]),(0,[z78,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z32,z4,z62,z5,z6])],[(0,[z377,z0,z1,z3,z4,z5,z6])],[(0,[z112,z0,z1,z32,z4,z5,z6]),(0,[z0,z31,z1,z9,z4,z5,z6]),(0,[z0,z1,z9,z3,z4,z5,z23])],[(0,[z0,z1,z3,z4,z5,z6,z492]),(0,[z48,z1,z277,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z493,z6])],[(0,[z20,z1,z3,z4,z5,z27,z6]),(0,[z15,z1,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z452]),(0,[z0,z1,z3,z4,z17,z5,z6]),(0,[z0,z1,z3,z4,z494,z5,z6])],[(0,[z0,z1,z495,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z47,z6,z175])],[(0,[z15,z1,z3,z4,z61,z5,z6]),(0,[z0,z1,z9,z4,z496,z5,z6]),(0,[z0,z1,z3,z4,z5,z497,z6])],[(0,[z498,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z361,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z47,z6]),(0,[z0,z1,z499,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z500]),(0,[z0,z1,z501,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z21,z59,z1,z3,z4,z5,z6]),(0,[z36,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z503,z5,z6]),(0,[z0,z1,z3,z504,z4,z5,z6]),(0,[z0,z1,z3,z71,z4,z5,z23])],[(0,[z1,z28,z3,z4,z5,z114,z6]),(0,[z505,z20,z1,z3,z4,z5,z6]),(0,[z15,z1,z134,z3,z4,z5,z6])]],
   [[(0,[z38,z1,z28,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z64,z5,z6]),(0,[z0,z1,z3,z4,z506,z5,z6]),(0,[z0,z1,z107,z4,z5,z47,z6])],[(0,[z195,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z6,z23]),(1,[z451,z1,z3,z4,z5,z6]),(0,[z0,z1,z88,z3,z5,z149,z6])],[(1,[z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z507,z6]),(0,[z0,z508,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z6,z175]),(0,[z36,z0,z1,z401,z4,z5,z6]),(0,[z0,z1,z3,z71,z152,z5,z6]),(0,[z0,z1,z3,z4,z5,z318,z6])],[(0,[z15,z21,z1,z3,z4,z5,z6]),(0,[z1,z60,z3,z34,z4,z5,z6]),(0,[z0,z1,z60,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z509,z6])],[(0,[z20,z1,z110,z3,z4,z5,z6]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z510,z5,z6]),(0,[z0,z1,z511,z3,z4,z5,z6]),(0,[z0,z1,z65,z4,z95,z5,z6])],[(0,[z36,z1,z3,z29,z4,z5,z6]),(0,[z0,z3,z32,z4,z5,z33,z6]),(0,[z0,z1,z88,z9,z4,z5,z6])],[(0,[z0,z1,z3,z4,z512,z5,z6]),(0,[z0,z1,z3,z4,z5,z513,z6])],[(0,[z0,z1,z3,z4,z514,z5,z6]),(0,[z505,z0,z1,z3,z4,z5,z6]),(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z151,z5,z6]),(1,[z1,z3,z4,z5,z6,z457])],[(0,[z0,z516,z1,z3,z4,z5,z6]),(0,[z0,z517,z1,z3,z4,z5,z6])],[],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z518,z6]),(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z519,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z520])],[(0,[z521,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z166,z6]),(0,[z0,z1,z88,z3,z4,z61,z6])],[(0,[z0,z1,z136,z65,z3,z5,z6]),(0,[z0,z1,z522,z3,z4,z5,z6]),(0,[z523,z0,z1,z3,z4,z26,z5])],[(1,[z20,z1,z32,z4,z5,z6]),(0,[z20,z1,z3,z4,z95,z5,z6])],[(0,[z90,z1,z3,z34,z4,z5,z6]),(1,[z30,z1,z3,z29,z5,z6]),(0,[z0,z1,z3,z524,z64,z5,z6]),(0,[z0,z1,z32,z4,z5,z22,z6])],[(0,[z0,z1,z3,z525,z4,z5,z6]),(0,[z0,z1,z3,z526,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z527])]],
   [[(0,[z528,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z95,z6]),(0,[z0,z1,z3,z4,z5,z529,z6]),(0,[z0,z1,z3,z4,z5,z368,z23])],[(0,[z1,z28,z28,z3,z4,z5,z6]),(0,[z31,z1,z28,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z6,z424]),(0,[z105,z0,z1,z3,z4,z27,z6])],[(0,[z0,z1,z3,z4,z530,z5,z6]),(0,[z51,z0,z3,z32,z4,z5,z6]),(1,[z0,z1,z531,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z27,z23]),(0,[z0,z532,z1,z3,z4,z5,z6])],[(0,[z90,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z533,z6]),(0,[z0,z44,z1,z3,z4,z5,z82]),(0,[z0,z1,z3,z4,z5,z6,z465]),(0,[z534,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z467,z5,z6])],[(0,[z1,z3,z34,z4,z5,z114,z6]),(0,[z1,z3,z29,z4,z5,z111,z6]),(1,[z0,z1,z32,z4,z5,z6]),(1,[z46,z0,z1,z4,z5,z175])],[(0,[z48,z1,z3,z29,z4,z5,z6]),(0,[z535,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z536,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z537,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z4,z5,z434,z6]),(0,[z0,z1,z3,z4,z5,z538,z6]),(0,[z15,z0,z1,z9,z4,z5,z6]),(1,[z128,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z47]),(1,[z0,z1,z3,z71,z5,z186]),(0,[z0,z1,z3,z71,z5,z186,z6])],[(0,[z539,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z5,z23]),(0,[z0,z31,z1,z32,z4,z5,z6]),(0,[z540,z0,z1,z9,z4,z5,z6])],[(0,[z0,z7,z1,z202,z4,z5,z6])],[(0,[z1,z3,z29,z4,z123,z5,z6])],[(0,[z541,z0,z1,z3,z4,z5,z6]),(0,[z15,z212,z1,z3,z4,z5,z6]),(0,[z448,z0,z1,z3,z4,z5,z6]),(1,[z25,z1,z3,z4,z5,z6])],[(0,[z0,z1,z28,z3,z4,z26,z5]),(0,[z15,z13,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z423,z4,z5,z6]),(0,[z0,z1,z110,z3,z4,z5,z23])],[(0,[z542,z0,z1,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z5,z6,z23]),(0,[z0,z1,z543,z3,z4,z5,z6])]],
   [[(0,[z1,z28,z3,z4,z161,z5,z6]),(0,[z46,z20,z1,z3,z4,z5,z6]),(0,[z544,z15,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z6,z91]),(0,[z0,z1,z3,z4,z47,z6,z465]),(0,[z0,z1,z3,z4,z5,z23,z520])],[(0,[z545,z0,z1,z3,z4,z26,z5])],[(0,[z0,z1,z3,z355,z4,z5,z6]),(1,[z0,z1,z8,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z546,z6]),(0,[z0,z44,z1,z9,z4,z5,z6]),(1,[z1,z146,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z242,z5,z6]),(0,[z0,z48,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z547,z4,z5,z6]),(0,[z280,z0,z1,z3,z4,z5,z23])],[(0,[z89,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z548,z6]),(0,[z15,z51,z1,z3,z4,z5,z6]),(0,[z1,z65,z3,z29,z4,z5,z6]),(0,[z1,z107,z3,z29,z4,z5,z6]),(0,[z16,z1,z3,z4,z5,z114,z6]),(0,[z0,z1,z136,z3,z5,z149,z6]),(1,[z0,z1,z3,z193,z5,z6]),(0,[z0,z1,z3,z4,z549,z5,z6])],[(0,[z1,z482,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z550,z5,z6]),(0,[z0,z1,z9,z80,z4,z5,z6])],[(0,[z257,z1,z28,z3,z4,z5,z6]),(0,[z20,z1,z3,z29,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z145,z6]),(0,[z0,z1,z3,z4,z551,z5,z6]),(0,[z0,z1,z3,z4,z5,z552,z6]),(0,[z0,z1,z3,z4,z553,z5,z6])],[(0,[z1,z28,z136,z3,z4,z5,z6]),(0,[z112,z20,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z347,z6]),(0,[z0,z1,z3,z4,z95,z5,z23]),(0,[z0,z1,z3,z4,z26,z95,z5])],[(0,[z1,z28,z3,z4,z5,z186,z6]),(0,[z0,z1,z3,z4,z371,z5,z6]),(0,[z15,z1,z3,z4,z5,z6,z82]),(0,[z554,z0,z1,z3,z4,z5,z6]),(0,[z105,z0,z1,z136,z4,z5,z6]),(0,[z0,z1,z3,z555,z4,z5,z6]),(0,[z0,z1,z556,z3,z4,z5,z6])],[(0,[z1,z28,z3,z152,z4,z5,z6]),(0,[z0,z1,z3,z4,z557,z5,z6])],[(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z543,z32,z4,z5,z6]),(0,[z558,z0,z1,z3,z4,z5,z6]),(0,[z559,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z560,z5,z6])],[(0,[z0,z1,z3,z4,z94,z5,z6]),(0,[z0,z1,z110,z3,z4,z26,z6])],[(0,[z20,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z6,z175]),(0,[z0,z212,z9,z3,z4,z5,z6]),(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z296,z3,z4,z5,z23])],[(0,[z20,z1,z3,z4,z436,z5,z6]),(0,[z0,z1,z3,z4,z161,z26,z5])],[(0,[z562,z0,z1,z3,z4,z5,z6])],[(0,[z563,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z564,z5,z6]),(0,[z0,z1,z3,z565,z4,z5,z6]),(0,[z566,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z20,z212,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z567])],[(0,[z1,z28,z2,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z30,z1,z3,z29,z4,z5,z6])],[(0,[z0,z1,z3,z4,z568,z5,z6]),(1,[z1,z3,z29,z4,z5,z23]),(0,[z0,z1,z3,z4,z62,z5,z6]),(0,[z112,z0,z1,z3,z551,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z569])],[(0,[z20,z1,z3,z4,z5,z149,z6]),(0,[z30,z0,z1,z3,z5,z149,z6]),(0,[z554,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z33]),(0,[z0,z1,z136,z4,z123,z5,z6])],[(0,[z0,z1,z218,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z445,z5,z6]),(0,[z0,z1,z136,z3,z4,z26,z5])],[(0,[z59,z0,z1,z32,z4,z5,z6]),(0,[z570,z0,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z5,z571]),(0,[z0,z572,z1,z3,z4,z5,z6])],[(0,[z16,z1,z28,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z6,z73]),(0,[z0,z1,z3,z4,z573,z5,z6]),(0,[z0,z1,z3,z574,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z91]),(1,[z448,z1,z3,z4,z5,z6]),(1,[z0,z1,z437,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z33,z6]),(0,[z0,z1,z9,z4,z5,z114,z6])],[(0,[z1,z138,z28,z3,z4,z5,z6]),(0,[z21,z1,z3,z29,z4,z5,z6])],[],[(0,[z0,z1,z575,z3,z4,z5,z6]),(0,[z563,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z576,z5,z6]),(0,[z577,z0,z1,z3,z4,z5,z6])],[(0,[z0,z31,z1,z437,z4,z5,z6]),(0,[z0,z1,z65,z3,z4,z5,z6])],[(0,[z15,z0,z1,z32,z4,z5,z6]),(1,[z0,z1,z3,z4,z94,z5])],[(0,[z1,z3,z29,z4,z180,z5,z6]),(0,[z1,z3,z71,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z5,z6]),(0,[z0,z1,z3,z80,z4,z26,z5])],[(1,[z15,z1,z3,z161,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z91]),(0,[z0,z1,z3,z4,z5,z578,z6]),(0,[z0,z579,z1,z3,z4,z5,z6])],[(0,[z0,z1,z401,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z580,z5,z6])]],
   [[(0,[z7,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z29,z4,z5,z23]),(0,[z105,z0,z1,z3,z42,z5,z6])],[(0,[z1,z28,z3,z4,z5,z47,z6]),(0,[z0,z1,z581,z3,z4,z5,z6])],[(0,[z1,z3,z29,z4,z26,z5,z6]),(0,[z412,z0,z1,z3,z4,z5,z6])],[(0,[z63,z1,z28,z3,z4,z5,z6]),(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z30,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z583,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z584,z6]),(0,[z0,z1,z3,z4,z5,z585,z6])],[(0,[z0,z1,z3,z4,z64,z5,z586]),(0,[z51,z69,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z151,z5,z6]),(0,[z0,z1,z4,z5,z246,z149,z6])],[(0,[z1,z3,z29,z4,z198,z5,z6]),(0,[z0,z44,z1,z32,z4,z5,z6])],[(0,[z0,z1,z65,z32,z4,z5,z6]),(0,[z0,z1,z3,z287,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z457,z73]),(0,[z0,z1,z3,z4,z43,z26,z5])],[],[(0,[z0,z1,z3,z587,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z567]),(0,[z112,z0,z44,z3,z4,z5,z6])],[(0,[z0,z1,z3,z588,z4,z5,z6])],[(0,[z21,z0,z1,z3,z4,z26,z5]),(0,[z0,z212,z1,z3,z4,z5,z23])],[(0,[z0,z1,z3,z4,z5,z22,z6]),(0,[z0,z1,z589,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z590,z5,z6]),(0,[z0,z1,z3,z80,z61,z5,z6])],[(0,[z0,z1,z136,z4,z95,z5,z6]),(1,[z0,z380,z3,z4,z5,z6]),(0,[z0,z1,z100,z3,z4,z47,z6]),(1,[z488,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z591,z6]),(0,[z0,z1,z592,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z149,z23])],[(0,[z36,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z295,z4,z5,z6])],[(0,[z20,z1,z3,z32,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z22,z6]),(0,[z0,z1,z110,z3,z4,z62,z6]),(0,[z0,z1,z3,z4,z5,z593,z6])]],
   [[(1,[z0,z1,z3,z551,z5,z6])],[(0,[z20,z1,z3,z4,z61,z5,z6]),(0,[z1,z3,z29,z4,z220,z5,z6]),(0,[z0,z1,z3,z4,z5,z33,z23])],[(1,[z251,z1,z3,z4,z5,z6]),(0,[z0,z31,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z153,z23])],[(1,[z1,z28,z3,z4,z26,z5]),(0,[z442,z0,z1,z3,z4,z5,z6])],[(1,[z21,z1,z34,z4,z5,z6]),(0,[z0,z1,z3,z4,z594,z5,z6])],[(0,[z0,z1,z28,z9,z4,z5,z6]),(0,[z20,z1,z134,z3,z4,z5,z6]),(0,[z0,z1,z595,z3,z4,z5,z6])],[(0,[z1,z28,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z114])],[(0,[z0,z1,z9,z4,z5,z6,z23]),(0,[z0,z1,z3,z596,z4,z5,z6])],[(0,[z89,z0,z7,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z161,z5,z6]),(0,[z0,z1,z3,z190,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z111,z6]),(0,[z0,z1,z3,z4,z597,z5,z6]),(0,[z598,z0,z1,z3,z4,z5,z6])],[(1,[z122,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z599,z5,z6]),(0,[z0,z1,z600,z3,z4,z5,z6])],[(0,[z1,z136,z3,z29,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z6,z91]),(1,[z78,z0,z3,z4,z33,z6])],[(0,[z1,z88,z3,z29,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z175])],[(0,[z0,z1,z3,z4,z5,z158,z6])],[(0,[z0,z1,z60,z3,z4,z5,z6]),(0,[z601,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z602,z5,z6]),(0,[z0,z1,z3,z57,z4,z5,z6]),(0,[z0,z1,z3,z4,z454,z5,z6]),(0,[z0,z1,z3,z4,z603,z5,z6])]],
   [[(0,[z1,z28,z3,z4,z123,z5,z6]),(0,[z20,z0,z7,z3,z4,z5,z6]),(0,[z24,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z186,z6]),(0,[z0,z3,z152,z4,z151,z5,z6]),(0,[z0,z1,z88,z3,z4,z5,z6])],[(0,[z0,z1,z32,z4,z5,z114,z6]),(0,[z0,z1,z9,z152,z4,z5,z6]),(0,[z0,z1,z3,z604,z4,z5,z6]),(0,[z0,z1,z3,z4,z605,z5,z6])],[(0,[z0,z1,z3,z4,z496,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z37])],[(0,[z0,z1,z3,z4,z5,z6,z444]),(0,[z0,z1,z3,z4,z95,z5,z116]),(0,[z0,z1,z107,z3,z4,z26,z5])],[(0,[z1,z28,z3,z4,z5,z6,z91]),(0,[z0,z1,z384,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z27,z6]),(0,[z0,z1,z606,z3,z4,z5,z6])],[(0,[z607,z20,z1,z3,z4,z5,z6]),(0,[z59,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z608,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z609,z6]),(0,[z0,z1,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z610,z5,z6])],[(0,[z15,z1,z3,z34,z4,z5,z6]),(0,[z611,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z5,z307])],[(0,[z0,z612,z1,z3,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z27,z6]),(0,[z0,z613,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z614,z4,z5,z6]),(0,[z0,z380,z1,z3,z4,z5,z6])],[(0,[z0,z7,z1,z3,z4,z26,z5]),(0,[z0,z1,z60,z32,z4,z5,z6]),(0,[z0,z1,z80,z32,z4,z5,z6]),(0,[z0,z1,z3,z32,z4,z5,z23]),(1,[z1,z3,z4,z445,z5,z6]),(0,[z0,z1,z3,z152,z5,z149,z6]),(0,[z0,z1,z3,z4,z5,z6,z175]),(0,[z38,z0,z1,z3,z4,z264,z6])],[(0,[z563,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z615])],[(0,[z1,z3,z29,z4,z64,z5,z6]),(0,[z0,z1,z88,z32,z4,z5,z6]),(0,[z0,z1,z136,z9,z4,z5,z6]),(0,[z0,z1,z3,z70,z4,z5,z6]),(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z61,z5,z23])],[(0,[z0,z1,z3,z4,z5,z6,z617]),(0,[z15,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z152,z5,z6,z73])],[(0,[z607,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z6,z23]),(0,[z0,z1,z3,z4,z5,z6,z618]),(0,[z0,z1,z3,z4,z123,z26,z5]),(0,[z0,z1,z3,z4,z5,z487,z23])],[(1,[z15,z1,z3,z4,z5,z23]),(1,[z0,z1,z511,z4,z5,z6])],[(0,[z89,z0,z28,z3,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z5,z23])]],
   [[(0,[z0,z1,z3,z4,z62,z5,z567])],[(0,[z36,z0,z1,z32,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z619,z6]),(0,[z0,z1,z3,z4,z5,z6,z620])],[(0,[z89,z0,z1,z361,z4,z5,z6]),(0,[z390,z1,z28,z3,z4,z5,z6]),(0,[z49,z15,z1,z3,z4,z5,z6]),(0,[z519,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z621,z4,z5,z6]),(0,[z0,z1,z3,z4,z622,z5,z6]),(0,[z24,z0,z1,z3,z4,z26,z5]),(0,[z46,z623,z1,z3,z4,z5,z6])],[(0,[z78,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z624,z6])],[],[(0,[z540,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z166])],[],[(0,[z89,z20,z1,z3,z4,z5,z6]),(0,[z20,z0,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z410,z6]),(0,[z625,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z157,z5])],[(0,[z1,z3,z29,z4,z95,z5,z6]),(1,[z0,z1,z3,z599,z5,z6])],[(0,[z0,z1,z9,z4,z5,z47,z6]),(0,[z0,z1,z3,z4,z626,z5,z6]),(0,[z0,z1,z3,z152,z4,z26,z5]),(0,[z105,z0,z1,z3,z4,z26,z5]),(1,[z0,z1,z3,z4,z388,z6])],[(0,[z1,z3,z34,z4,z5,z6,z91]),(0,[z30,z0,z1,z9,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z37]),(0,[z627,z0,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z3,z4,z5,z6]),(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z80,z4,z61,z6])],[(1,[z0,z1,z9,z4,z5,z23])],[(0,[z59,z63,z1,z3,z4,z5,z6]),(0,[z628,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z629])],[(0,[z0,z1,z630,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z631,z5,z6]),(0,[z0,z44,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z6,z82]),(0,[z0,z48,z1,z3,z4,z5,z6]),(0,[z0,z1,z531,z3,z4,z5,z6]),(0,[z0,z3,z4,z62,z5,z33,z6]),(1,[z0,z222,z3,z4,z5,z6]),(0,[z632,z0,z1,z3,z4,z5,z6])],[(0,[z89,z0,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z4,z5,z6]),(0,[z633,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z175])]],
   [[(0,[z0,z1,z34,z32,z4,z5,z6]),(1,[z0,z9,z32,z4,z5,z6]),(0,[z78,z0,z1,z537,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z571])],[(0,[z21,z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z6,z23]),(0,[z634,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z61,z23]),(0,[z0,z1,z262,z3,z4,z5,z6])],[(0,[z78,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z161,z5,z6]),(0,[z635,z0,z1,z3,z4,z5,z6]),(0,[z128,z0,z1,z3,z4,z5,z6])],[(0,[z15,z63,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z636,z5,z6]),(0,[z0,z1,z9,z4,z5,z93,z6]),(0,[z0,z1,z136,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z430,z5,z6])],[(0,[z637,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z346,z6]),(0,[z0,z1,z638,z3,z4,z5,z6]),(0,[z488,z0,z1,z3,z4,z5,z6])],[],[(0,[z1,z28,z3,z4,z26,z5,z6]),(0,[z639,z0,z1,z3,z4,z5,z6]),(0,[z35,z15,z1,z3,z4,z5,z6]),(0,[z0,z212,z3,z4,z5,z33,z6]),(0,[z0,z48,z3,z152,z4,z5,z6]),(0,[z0,z1,z3,z4,z619,z5,z6])],[(0,[z20,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z151,z5,z6]),(0,[z0,z48,z1,z531,z4,z5,z6])],[(0,[z102,z15,z1,z3,z4,z5,z6]),(0,[z544,z0,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z198,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z233]),(0,[z13,z1,z3,z29,z4,z5,z6]),(0,[z0,z48,z1,z32,z4,z5,z6]),(0,[z0,z1,z32,z4,z636,z5,z6]),(0,[z1,z3,z56,z4,z123,z5,z6]),(0,[z0,z640,z1,z3,z4,z5,z6])],[(0,[z89,z0,z1,z32,z4,z5,z6]),(1,[z1,z28,z9,z4,z5,z6]),(0,[z641,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z186,z6]),(0,[z0,z1,z3,z4,z5,z111,z73])],[(0,[z1,z3,z67,z152,z4,z5,z6]),(0,[z440,z0,z1,z3,z4,z5,z23])],[(0,[z1,z28,z9,z3,z4,z5,z6]),(0,[z642,z0,z1,z3,z4,z5,z6]),(0,[z643,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z644,z5,z6]),(0,[z0,z1,z3,z80,z4,z5,z6])],[(1,[z15,z1,z3,z29,z5,z6]),(0,[z35,z1,z3,z29,z4,z5,z6]),(1,[z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z645,z5,z6])],[(0,[z15,z1,z3,z4,z62,z5,z6]),(0,[z0,z1,z3,z4,z646,z5,z6]),(0,[z0,z1,z136,z32,z4,z5,z6])],[(1,[z0,z1,z133,z4,z5,z6]),(0,[z0,z1,z3,z151,z5,z6,z73]),(0,[z0,z1,z3,z4,z5,z647,z6]),(1,[z0,z1,z3,z4,z619,z6]),(0,[z0,z1,z3,z4,z5,z82,z73]),(0,[z0,z1,z3,z648,z4,z5,z6])]],
   [[(0,[z44,z1,z3,z29,z4,z5,z6])],[(0,[z0,z1,z649,z3,z4,z5,z6]),(0,[z1,z3,z29,z29,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z111,z6])],[(0,[z20,z0,z1,z32,z4,z5,z6]),(0,[z51,z1,z3,z29,z4,z5,z6])],[(0,[z1,z28,z3,z71,z4,z5,z6]),(1,[z248,z0,z1,z3,z4,z5]),(0,[z0,z1,z110,z3,z4,z149,z6]),(0,[z0,z1,z3,z4,z26,z26,z5])],[(1,[z199,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z650,z5,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z599,z4,z5,z6]),(0,[z0,z1,z652,z3,z4,z5,z6]),(0,[z653,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z654,z3,z4,z5,z6])],[],[(0,[z0,z1,z655,z3,z4,z5,z6])],[(0,[z15,z1,z65,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z22,z6,z91]),(0,[z0,z1,z110,z3,z4,z33,z6]),(1,[z623,z1,z3,z4,z5,z6])],[(0,[z0,z1,z9,z4,z123,z5,z6]),(1,[z0,z1,z3,z4,z5,z571])],[(0,[z19,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z3,z4,z26,z5]),(0,[z656,z0,z1,z3,z4,z5,z6]),(0,[z46,z640,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z260,z4,z5,z6]),(0,[z0,z1,z107,z9,z4,z5,z6]),(0,[z78,z77,z1,z3,z4,z5,z6]),(0,[z0,z657,z1,z3,z4,z5,z6])],[(0,[z239,z1,z3,z29,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z4,z264,z5,z6])],[(0,[z0,z1,z3,z64,z5,z322,z6]),(0,[z0,z1,z9,z4,z5,z6,z91]),(0,[z0,z1,z3,z4,z5,z658,z6]),(0,[z0,z1,z3,z4,z26,z332,z5])],[(0,[z30,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z659,z4,z5,z6])],[(0,[z1,z3,z29,z4,z5,z149,z6]),(0,[z0,z1,z3,z4,z5,z114,z6]),(0,[z523,z0,z1,z3,z4,z5,z6]),(0,[z0,z44,z1,z511,z4,z5,z6])],[(0,[z651,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z660,z9,z4,z5,z6]),(0,[z0,z48,z1,z3,z151,z5,z6]),(0,[z661,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z662,z5,z6]),(0,[z35,z0,z1,z3,z4,z26,z5])]],
   [[(0,[z0,z7,z1,z9,z4,z5,z6]),(0,[z15,z1,z3,z4,z151,z5,z6]),(0,[z0,z1,z663,z3,z4,z5,z6]),(0,[z0,z1,z3,z524,z4,z5,z6]),(1,[z0,z1,z537,z4,z5,z6]),(1,[z0,z1,z134,z3,z4,z23])],[(0,[z36,z20,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z6,z73]),(0,[z664,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z82]),(0,[z0,z1,z3,z665,z4,z5,z6]),(0,[z0,z1,z666,z3,z4,z5,z6])],[(0,[z59,z0,z1,z34,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z33,z6]),(0,[z0,z1,z3,z4,z26,z109,z5])],[(0,[z105,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z47,z6]),(0,[z0,z1,z3,z4,z5,z667,z6])],[(0,[z21,z0,z1,z32,z4,z5,z6]),(0,[z51,z0,z1,z3,z4,z26,z5]),(0,[z668,z0,z1,z9,z4,z5,z6]),(0,[z251,z1,z3,z152,z4,z5,z6]),(0,[z0,z1,z3,z4,z669,z5,z6]),(0,[z0,z670,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z61,z467,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z586]),(0,[z90,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z671,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z672,z6]),(0,[z0,z1,z3,z4,z5,z6,z673])],[],[(0,[z15,z1,z3,z4,z5,z22,z6]),(1,[z0,z1,z3,z524,z5,z6])],[(0,[z1,z28,z3,z4,z5,z27,z6]),(0,[z1,z630,z3,z29,z4,z5,z6]),(0,[z25,z0,z1,z3,z4,z5,z6])],[(0,[z24,z0,z1,z9,z4,z5,z6])],[(0,[z0,z1,z3,z674,z4,z5,z6]),(0,[z105,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z66,z32,z4,z5,z6]),(0,[z31,z1,z252,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z675,z5,z6])],[],[(1,[z1,z28,z32,z4,z5,z6]),(0,[z0,z1,z3,z676,z4,z5,z6]),(0,[z0,z1,z3,z80,z151,z5,z6]),(0,[z0,z1,z3,z4,z5,z677,z6]),(0,[z0,z1,z3,z4,z678,z5,z6])],[(0,[z15,z31,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z679,z6]),(0,[z680,z0,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z64,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z681]),(0,[z78,z0,z3,z4,z5,z33,z6]),(0,[z0,z1,z3,z4,z5,z388,z6])]],
   [[(0,[z0,z1,z28,z3,z4,z5,z6]),(0,[z59,z1,z3,z4,z5,z114,z6]),(0,[z105,z0,z1,z9,z4,z5,z6])],[(0,[z0,z1,z682,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z23]),(1,[z0,z1,z107,z4,z5,z47])],[(0,[z476,z0,z1,z3,z4,z5,z23])],[(1,[z89,z28,z3,z4,z5,z6]),(0,[z1,z28,z110,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z151,z5,z6]),(0,[z59,z1,z60,z3,z4,z5,z6]),(0,[z545,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z245,z26,z5])],[(0,[z90,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z185,z62,z5]),(1,[z0,z1,z88,z3,z149,z6])],[(0,[z0,z1,z3,z683,z4,z5,z6]),(0,[z0,z44,z3,z4,z5,z111,z6])],[(0,[z1,z110,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z684,z6]),(0,[z72,z1,z3,z4,z61,z5,z6]),(0,[z0,z1,z3,z4,z685,z5,z6])],[(0,[z0,z1,z660,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z62,z5]),(0,[z0,z1,z3,z4,z26,z5,z73]),(0,[z297,z1,z3,z4,z5,z186,z6]),(0,[z0,z1,z3,z4,z5,z6,z479])],[(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z0,z1,z2,z9,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z5,z23]),(0,[z24,z451,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z254,z26,z5])],[(0,[z0,z1,z133,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z514,z5,z6]),(0,[z686,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z325,z3,z4,z5,z6])],[(0,[z0,z1,z3,z687,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z22,z6]),(0,[z0,z1,z3,z4,z5,z688,z6]),(0,[z15,z1,z60,z3,z4,z5,z6])],[(0,[z0,z1,z28,z32,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z111,z6]),(0,[z0,z1,z3,z4,z62,z5,z23])],[(0,[z1,z28,z3,z4,z95,z5,z6]),(0,[z20,z1,z3,z34,z4,z5,z6]),(0,[z15,z1,z88,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z61,z5,z6]),(0,[z0,z1,z3,z4,z5,z689,z6]),(0,[z668,z0,z1,z3,z4,z5,z6]),(0,[z0,z103,z1,z3,z4,z5,z6]),(0,[z0,z690,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z4,z5,z6,z175])],[(1,[z0,z1,z3,z4,z5,z586])],[(0,[z0,z1,z9,z4,z26,z5,z6]),(1,[z0,z1,z287,z4,z5,z6]),(1,[z640,z1,z3,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z23])],[(0,[z0,z1,z3,z4,z161,z5,z6]),(0,[z1,z3,z68,z29,z4,z5,z6]),(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z693,z5,z6])]],
   [[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z46,z1,z28,z3,z4,z5,z6]),(0,[z105,z0,z1,z4,z5,z27,z6]),(1,[z0,z1,z3,z4,z198,z23]),(0,[z0,z1,z110,z3,z4,z26,z5])],[(0,[z20,z31,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z198,z5,z6]),(0,[z694,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z695,z4,z5,z6]),(0,[z24,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z696,z4,z5,z6])],[(0,[z20,z20,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z123,z5,z6]),(0,[z697,z0,z1,z3,z4,z5,z6])],[(0,[z0,z7,z1,z32,z4,z5,z6]),(0,[z698,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z699,z5,z6])],[(0,[z1,z28,z3,z4,z5,z302,z6]),(0,[z38,z1,z3,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z149,z6]),(0,[z0,z1,z3,z178,z4,z5,z6]),(0,[z0,z1,z65,z3,z4,z5,z23]),(0,[z0,z1,z3,z71,z4,z5,z73])],[(0,[z212,z1,z28,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z6,z175]),(1,[z112,z0,z3,z4,z5,z82])],[],[(0,[z112,z1,z28,z3,z4,z5,z6]),(1,[z16,z1,z3,z4,z114,z6]),(0,[z112,z0,z1,z3,z4,z5,z111]),(0,[z0,z1,z3,z4,z5,z186,z6])],[(0,[z0,z1,z3,z152,z4,z5,z6]),(0,[z700,z0,z1,z3,z4,z5,z6]),(1,[z148,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z536,z4,z5,z6]),(0,[z0,z1,z4,z95,z5,z27,z6]),(0,[z38,z0,z1,z3,z5,z6,z73])],[(0,[z1,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z701,z5,z6])],[(0,[z0,z1,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z71,z4,z5,z6]),(0,[z0,z1,z702,z3,z4,z5,z6]),(0,[z379,z1,z3,z4,z123,z5,z6]),(0,[z1,z3,z4,z5,z186,z6,z160])],[(0,[z24,z0,z1,z32,z4,z5,z6])],[(0,[z0,z1,z703,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z200,z6]),(0,[z704,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z151,z5,z23]),(0,[z0,z1,z3,z4,z5,z246,z6])],[(0,[z1,z28,z3,z4,z321,z5,z6]),(1,[z20,z1,z3,z4,z5,z23]),(0,[z16,z0,z1,z3,z4,z5,z346]),(0,[z0,z1,z32,z152,z4,z5,z6]),(1,[z1,z3,z4,z5,z54,z6])],[(1,[z1,z3,z260,z4,z5,z6]),(0,[z0,z705,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z706,z6]),(0,[z51,z0,z212,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z5,z149,z6]),(0,[z105,z0,z1,z3,z4,z5,z425])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z15,z24,z1,z136,z5,z6]),(0,[z0,z110,z32,z4,z33,z6]),(0,[z0,z1,z88,z32,z149,z6]),(0,[z0,z222,z3,z4,z26,z5])],[(0,[z390,z1,z3,z4,z5,z444]),(0,[z1,z28,z3,z4,z5,z116]),(0,[z0,z1,z3,z4,z602,z23]),(0,[z0,z595,z32,z4,z5,z6]),(0,[z1,z703,z3,z29,z5,z6]),(0,[z0,z1,z3,z4,z707,z6]),(0,[z708,z1,z3,z4,z5,z23])],[(0,[z1,z3,z4,z5,z6,z709]),(0,[z46,z20,z1,z4,z5,z175]),(0,[z1,z710,z34,z4,z5,z6]),(0,[z15,z1,z531,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z711])],[(0,[z1,z28,z3,z80,z61,z6]),(0,[z0,z1,z3,z4,z5,z712]),(0,[z0,z1,z3,z713,z5,z6]),(0,[z15,z1,z3,z161,z26,z5]),(0,[z1,z3,z29,z551,z5,z6]),(0,[z38,z488,z1,z3,z5,z73])],[(0,[z1,z3,z714,z4,z5,z6]),(0,[z0,z1,z715,z3,z4,z5])],[(0,[z1,z716,z3,z4,z5,z6]),(0,[z1,z717,z29,z4,z5,z6]),(0,[z0,z1,z327,z4,z5,z410]),(0,[z0,z3,z4,z5,z6,z718]),(0,[z0,z1,z194,z4,z5,z23])],[(0,[z0,z1,z9,z4,z5,z6]),(0,[z0,z1,z660,z3,z4,z23]),(0,[z0,z1,z88,z194,z149,z6]),(0,[z0,z1,z3,z5,z6,z719]),(0,[z0,z1,z3,z4,z26,z23])],[(0,[z45,z28,z3,z4,z5,z6]),(0,[z20,z7,z8,z4,z5,z6]),(0,[z119,z1,z287,z4,z5,z6]),(0,[z720,z1,z3,z4,z5,z6]),(0,[z0,z1,z327,z413,z5,z6]),(0,[z0,z1,z4,z95,z667,z6])],[(0,[z1,z28,z87,z4,z5,z6]),(0,[z251,z1,z3,z80,z5,z6]),(0,[z0,z721,z3,z4,z5,z6]),(1,[z1,z3,z4,z722,z6]),(0,[z723,z1,z3,z4,z5,z6])],[(0,[z51,z0,z32,z4,z5,z6]),(0,[z1,z3,z4,z445,z269,z5])],[(0,[z0,z1,z202,z4,z5,z23]),(0,[z30,z1,z9,z29,z5,z6]),(0,[z724,z1,z3,z4,z5,z6]),(0,[z1,z3,z725,z193,z5,z6])],[(0,[z105,z15,z1,z4,z27,z6]),(0,[z0,z1,z3,z644,z149,z6]),(0,[z0,z1,z726,z4,z5,z6]),(0,[z63,z1,z32,z4,z64,z6]),(0,[z0,z1,z3,z599,z318,z6]),(0,[z41,z44,z3,z4,z5,z111]),(0,[z0,z1,z3,z4,z299,z23]),(0,[z0,z1,z3,z4,z300,z23])],[(0,[z51,z28,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z722,z6]),(0,[z0,z1,z450,z136,z5,z6])],[(0,[z0,z1,z727,z4,z5,z6]),(0,[z59,z1,z57,z4,z5,z6]),(0,[z554,z0,z1,z4,z201,z6]),(0,[z225,z1,z3,z4,z5,z571])],[(0,[z728,z1,z3,z4,z5,z6]),(0,[z1,z3,z729,z4,z5,z6]),(0,[z1,z3,z4,z157,z467,z5])],[(0,[z105,z1,z28,z3,z4,z23]),(0,[z1,z3,z4,z5,z730,z6]),(0,[z15,z1,z3,z29,z26,z5]),(0,[z122,z1,z3,z5,z149,z6]),(0,[z0,z1,z3,z4,z557,z23])]],
   [[(0,[z0,z1,z3,z731,z5,z6]),(0,[z0,z1,z3,z732,z5,z6]),(0,[z0,z1,z325,z599,z5,z6]),(0,[z0,z1,z107,z4,z5,z487])],[(0,[z0,z1,z3,z733,z4,z6]),(0,[z0,z1,z3,z4,z5,z734]),(0,[z15,z1,z3,z406,z5,z6]),(0,[z1,z3,z735,z4,z5,z6]),(0,[z0,z1,z736,z4,z5,z6]),(0,[z212,z184,z9,z4,z5,z6]),(0,[z283,z1,z3,z599,z5,z6]),(0,[z0,z380,z3,z4,z26,z5]),(0,[z488,z1,z3,z4,z26,z5])],[(0,[z519,z1,z3,z4,z117,z6]),(0,[z0,z1,z737,z4,z5,z6]),(0,[z44,z3,z29,z4,z5,z111]),(0,[z1,z124,z3,z4,z145,z6]),(0,[z0,z1,z3,z4,z738,z5]),(0,[z1,z739,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z740])],[(0,[z15,z1,z3,z193,z5,z6]),(0,[z0,z1,z3,z76,z5,z322]),(0,[z741,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z742,z5,z6]),(0,[z1,z28,z194,z4,z5,z6]),(0,[z105,z0,z1,z336,z4,z6]),(0,[z38,z1,z3,z5,z457,z73])],[(0,[z451,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z743,z5,z6]),(0,[z15,z1,z3,z580,z5,z6]),(0,[z0,z1,z3,z4,z5,z744]),(0,[z745,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z551,z26,z5]),(0,[z1,z3,z4,z26,z5,z54]),(0,[z0,z1,z194,z3,z4,z23]),(1,[z0,z1,z3,z5,z719]),(0,[z0,z1,z3,z290,z5,z186])],[(0,[z1,z9,z4,z445,z5,z6]),(0,[z36,z0,z287,z151,z5,z6])],[(0,[z251,z1,z3,z4,z26,z5]),(0,[z1,z60,z710,z4,z5,z6]),(0,[z0,z1,z3,z4,z151,z746]),(0,[z0,z1,z3,z747,z5,z6]),(0,[z1,z748,z3,z4,z5,z6]),(0,[z0,z1,z4,z246,z149,z23]),(0,[z749,z1,z3,z4,z5,z6]),(0,[z750,z1,z3,z4,z5,z6])],[(0,[z0,z1,z92,z32,z4,z23]),(0,[z0,z3,z4,z751,z33,z6]),(0,[z0,z1,z3,z4,z359,z23]),(0,[z0,z1,z3,z4,z752,z23])],[(0,[z1,z28,z202,z4,z5,z6]),(0,[z0,z753,z3,z4,z5,z6]),(0,[z21,z1,z34,z4,z26,z5]),(0,[z0,z1,z3,z4,z6,z754]),(0,[z0,z1,z9,z755,z5,z6]),(0,[z25,z1,z9,z4,z5,z6]),(0,[z78,z225,z3,z4,z33,z6]),(0,[z756,z1,z3,z4,z5,z6])],[(0,[z757,z1,z28,z3,z5,z6]),(0,[z469,z28,z3,z4,z5,z6]),(0,[z63,z1,z3,z4,z436,z6]),(0,[z21,z1,z433,z4,z5,z6]),(0,[z15,z1,z511,z4,z5,z6]),(0,[z0,z1,z3,z4,z752,z61])],[(0,[z1,z3,z4,z5,z6,z457]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z759,z1,z3,z4,z5,z6]),(0,[z760,z1,z3,z4,z5,z6])],[(0,[z38,z1,z3,z29,z5,z73]),(0,[z761,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z733,z4,z6]),(0,[z119,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z5,z762]),(0,[z0,z1,z178,z4,z5,z23])],[(0,[z1,z763,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z425])],[(0,[z20,z1,z3,z4,z5,z410]),(0,[z0,z1,z3,z4,z5,z764]),(0,[z1,z146,z9,z4,z5,z6]),(0,[z0,z1,z298,z3,z4,z23])],[(0,[z20,z31,z32,z4,z5,z6]),(0,[z528,z0,z32,z4,z5,z6]),(0,[z119,z1,z3,z4,z5,z23]),(0,[z122,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z42,z5,z23]),(0,[z0,z1,z3,z4,z388,z73])]],
   [[(0,[z20,z1,z3,z413,z5,z6]),(0,[z765,z1,z3,z4,z5,z6]),(0,[z451,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z193,z5,z6]),(0,[z112,z0,z1,z3,z4,z388])],[(0,[z1,z28,z3,z766,z4,z5]),(0,[z15,z1,z3,z4,z767,z6]),(0,[z0,z1,z3,z768,z5,z6]),(0,[z31,z252,z3,z4,z62,z6]),(0,[z769,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z465,z23]),(0,[z0,z1,z229,z3,z4,z23])],[(0,[z1,z770,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z771,z6]),(0,[z20,z1,z3,z4,z62,z23]),(0,[z20,z772,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z773,z6]),(0,[z1,z9,z29,z4,z5,z23]),(0,[z0,z1,z3,z4,z85,z774]),(0,[z0,z1,z3,z295,z5,z571])],[(0,[z20,z1,z3,z4,z149,z23]),(0,[z15,z1,z3,z461,z5,z6]),(0,[z15,z1,z3,z5,z149,z23]),(0,[z15,z1,z3,z4,z157,z5]),(0,[z0,z32,z4,z693,z5,z6]),(0,[z0,z1,z775,z4,z5,z6]),(0,[z0,z3,z4,z5,z751,z6])],[(0,[z15,z1,z3,z599,z5,z6]),(0,[z0,z1,z32,z4,z6,z754]),(0,[z0,z1,z3,z4,z6,z776]),(0,[z777,z1,z3,z4,z26,z5])],[(0,[z1,z28,z3,z4,z185,z5]),(0,[z15,z1,z3,z5,z593,z6]),(0,[z15,z1,z3,z4,z388,z6]),(0,[z0,z1,z778,z4,z5,z6]),(0,[z1,z779,z32,z4,z5,z6]),(0,[z0,z1,z780,z4,z26,z5])],[(0,[z0,z1,z3,z4,z5,z781]),(0,[z15,z1,z3,z4,z5,z37]),(0,[z0,z1,z3,z4,z5,z410]),(0,[z1,z3,z4,z26,z467,z5]),(0,[z412,z0,z1,z3,z430,z5])],[(0,[z20,z1,z3,z4,z33,z23]),(0,[z15,z324,z32,z4,z5,z6]),(0,[z15,z1,z9,z4,z5,z23]),(0,[z0,z31,z32,z4,z5,z6]),(0,[z782,z1,z3,z4,z5,z6]),(0,[z0,z1,z325,z4,z619,z6]),(0,[z46,z0,z1,z3,z4,z465]),(0,[z0,z191,z3,z4,z254,z5])],[(0,[z15,z783,z3,z4,z5,z6]),(0,[z1,z3,z4,z467,z5,z6]),(0,[z0,z32,z4,z33,z149,z6]),(0,[z0,z212,z9,z4,z5,z23]),(0,[z0,z1,z3,z4,z784,z5]),(0,[z0,z1,z3,z413,z5,z6]),(0,[z785,z1,z3,z4,z5,z6]),(0,[z78,z0,z3,z295,z33,z6]),(0,[z0,z31,z87,z4,z62,z6]),(0,[z786,z1,z3,z4,z5,z6]),(0,[z283,z1,z3,z4,z619,z6]),(0,[z0,z1,z3,z787,z149,z6])],[(0,[z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z788]),(0,[z306,z1,z60,z4,z5,z6]),(0,[z36,z3,z29,z151,z5,z6]),(0,[z0,z1,z3,z789,z5,z6]),(0,[z0,z1,z65,z123,z5,z23])],[(0,[z15,z1,z3,z4,z5,z790]),(0,[z15,z222,z3,z4,z5,z6]),(0,[z15,z1,z3,z594,z5,z6]),(0,[z1,z3,z29,z4,z157,z5]),(0,[z0,z1,z3,z4,z791,z6]),(0,[z24,z451,z1,z136,z5,z6]),(0,[z792,z1,z3,z4,z5,z6]),(0,[z0,z1,z100,z107,z4,z47])],[(0,[z1,z28,z178,z4,z5,z6]),(0,[z793,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z599,z5,z6]),(0,[z554,z0,z1,z4,z27,z6]),(0,[z0,z1,z3,z4,z149,z23])],[(0,[z15,z9,z32,z4,z5,z6]),(0,[z1,z3,z29,z4,z388,z6]),(0,[z210,z1,z3,z4,z5,z23])],[(0,[z128,z1,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z6,z465]),(0,[z1,z3,z29,z4,z5,z37]),(0,[z0,z1,z3,z4,z5,z794]),(0,[z1,z3,z4,z5,z6,z795]),(0,[z0,z1,z3,z71,z5,z186])],[(0,[z1,z28,z3,z42,z5,z6]),(0,[z20,z1,z8,z4,z5,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z1,z32,z4,z467,z5,z6]),(0,[z1,z3,z4,z445,z26,z5]),(0,[z0,z1,z3,z4,z5,z797]),(0,[z0,z1,z3,z4,z264,z23])],[(0,[z20,z1,z3,z4,z5,z333]),(0,[z1,z511,z29,z4,z5,z6]),(0,[z0,z1,z134,z32,z4,z23]),(0,[z0,z3,z4,z798,z5,z6]),(0,[z0,z1,z3,z4,z33,z23]),(0,[z799,z1,z3,z4,z5,z6])]],
   [[],[(0,[z199,z1,z65,z3,z5,z6]),(0,[z0,z1,z32,z4,z5,z410]),(0,[z800,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z457])],[(0,[z20,z7,z3,z4,z5,z6]),(0,[z1,z801,z3,z4,z5,z6]),(0,[z802,z1,z3,z4,z5,z6]),(0,[z448,z1,z9,z4,z5,z6]),(0,[z0,z1,z9,z4,z388,z6]),(0,[z143,z1,z3,z4,z5,z23]),(0,[z272,z1,z3,z4,z5,z23]),(0,[z0,z1,z110,z3,z4,z803])],[(0,[z804,z1,z3,z4,z5,z6]),(0,[z15,z248,z1,z3,z4,z5]),(0,[z1,z3,z4,z805,z5,z6]),(0,[z30,z1,z3,z5,z54,z6]),(0,[z0,z1,z32,z413,z5,z6]),(0,[z0,z1,z806,z4,z5,z6])],[(0,[z1,z28,z4,z5,z246,z6]),(0,[z15,z1,z3,z4,z807,z6]),(0,[z1,z3,z29,z4,z61,z23])],[(0,[z1,z3,z808,z4,z5,z6])],[(0,[z0,z1,z8,z4,z5,z6]),(0,[z1,z146,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z149,z23]),(0,[z0,z1,z3,z4,z26,z168]),(0,[z1,z3,z4,z5,z809,z6])],[(0,[z0,z1,z3,z4,z810,z5]),(0,[z15,z1,z3,z4,z5,z567]),(0,[z0,z1,z3,z4,z5,z333]),(0,[z1,z184,z3,z4,z5,z23]),(0,[z0,z222,z9,z4,z5,z6])],[(0,[z1,z28,z65,z123,z5,z6]),(0,[z20,z1,z327,z4,z5,z6]),(0,[z59,z1,z60,z4,z5,z6]),(0,[z128,z1,z32,z4,z5,z6]),(0,[z0,z1,z32,z71,z5,z186]),(0,[z1,z3,z4,z811,z5,z6]),(0,[z0,z1,z9,z4,z94,z5]),(0,[z1,z812,z3,z4,z5,z6])],[(0,[z0,z1,z813,z4,z5,z6]),(0,[z563,z1,z57,z4,z5,z6]),(0,[z814,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z815,z5,z6]),(0,[z0,z1,z3,z4,z590,z23])],[(0,[z105,z1,z28,z4,z27,z6]),(0,[z1,z138,z3,z29,z5,z6]),(0,[z15,z1,z450,z32,z5,z6]),(0,[z15,z1,z9,z161,z5,z6]),(0,[z0,z1,z816,z4,z5,z6]),(0,[z0,z1,z32,z4,z33,z23]),(0,[z0,z1,z100,z32,z4,z6]),(0,[z0,z1,z817,z123,z5,z6]),(0,[z103,z1,z3,z42,z5,z6])],[(0,[z15,z1,z3,z4,z619,z6]),(0,[z15,z380,z3,z4,z5,z6]),(0,[z0,z1,z3,z818,z5,z6]),(0,[z1,z3,z4,z819,z5,z6])],[(0,[z195,z1,z3,z4,z114,z6]),(0,[z800,z1,z32,z4,z5,z6]),(0,[z25,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z820,z6])],[(0,[z1,z28,z3,z4,z264,z6]),(0,[z20,z7,z32,z4,z5,z6]),(0,[z802,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z599,z26,z5]),(0,[z105,z0,z380,z3,z4,z23]),(0,[z0,z1,z88,z3,z149,z309]),(0,[z476,z1,z3,z4,z5,z479])],[(0,[z821,z1,z28,z3,z4,z5]),(0,[z20,z1,z3,z4,z5,z712]),(0,[z822,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z551,z5,z82])],[(0,[z0,z1,z3,z4,z5,z823]),(0,[z0,z1,z3,z4,z824,z5]),(0,[z0,z1,z825,z4,z5,z6]),(0,[z105,z0,z1,z4,z826,z6]),(0,[z827,z1,z3,z4,z5,z6]),(0,[z0,z1,z828,z4,z5,z23])]],
   [[(0,[z1,z3,z29,z4,z85,z6]),(0,[z0,z1,z327,z4,z5,z6]),(0,[z1,z3,z829,z295,z5,z6]),(0,[z105,z0,z222,z3,z4,z23]),(0,[z0,z1,z4,z5,z826,z6]),(0,[z640,z1,z3,z4,z26,z5]),(0,[z297,z1,z3,z4,z5,z23]),(0,[z523,z0,z3,z4,z58,z5])],[(0,[z1,z3,z4,z5,z6,z830]),(0,[z1,z146,z32,z4,z5,z6]),(0,[z0,z1,z86,z4,z5,z23]),(1,[z0,z1,z4,z5,z831])],[(0,[z1,z28,z3,z4,z269,z5]),(0,[z1,z537,z29,z4,z5,z6]),(0,[z1,z3,z29,z4,z619,z6]),(0,[z1,z3,z473,z4,z180,z6]),(0,[z0,z1,z32,z4,z5,z333]),(0,[z0,z1,z3,z4,z5,z832])],[(0,[z63,z1,z3,z4,z64,z6]),(1,[z0,z1,z817,z5,z6])],[(0,[z0,z1,z3,z4,z833,z6]),(0,[z15,z1,z3,z4,z5,z571]),(0,[z1,z327,z29,z4,z5,z6]),(0,[z0,z1,z834,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z567]),(0,[z0,z1,z835,z4,z5,z6])],[(0,[z1,z3,z4,z836,z5,z6]),(0,[z0,z9,z32,z4,z26,z5]),(0,[z0,z612,z32,z4,z5,z6]),(0,[z280,z0,z3,z4,z33,z23]),(0,[z1,z837,z3,z4,z5,z6]),(0,[z72,z1,z3,z80,z61,z6])],[(0,[z0,z1,z3,z4,z5,z838]),(0,[z0,z1,z839,z4,z5,z6]),(0,[z15,z1,z9,z29,z5,z6]),(0,[z1,z3,z4,z5,z840,z91]),(0,[z0,z1,z458,z3,z4,z26]),(0,[z0,z1,z32,z818,z5,z6]),(0,[z0,z1,z107,z3,z4,z465])],[(0,[z607,z1,z3,z4,z169,z6]),(0,[z15,z577,z1,z3,z5,z6]),(0,[z841,z1,z3,z4,z5,z6]),(0,[z0,z222,z4,z5,z27,z6])],[(0,[z1,z217,z3,z4,z5,z23]),(0,[z15,z842,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z843]),(0,[z90,z1,z3,z4,z5,z840]),(0,[z0,z32,z4,z61,z33,z6]),(0,[z634,z0,z32,z4,z5,z6]),(0,[z844,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z622,z23]),(0,[z488,z1,z9,z4,z5,z6]),(0,[z0,z380,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z845,z5]),(0,[z0,z1,z3,z4,z5,z846]),(0,[z0,z1,z847,z4,z5,z6]),(0,[z0,z1,z134,z4,z487,z23]),(0,[z848,z1,z3,z4,z5,z6])],[(0,[z20,z28,z3,z4,z5,z6]),(0,[z1,z3,z4,z220,z5,z23]),(0,[z0,z132,z9,z4,z5,z6]),(1,[z0,z3,z4,z751,z6])],[(0,[z448,z1,z3,z4,z5,z6]),(0,[z199,z1,z3,z80,z5,z6]),(0,[z251,z1,z3,z5,z149,z6]),(0,[z0,z1,z3,z849,z5,z6]),(0,[z1,z134,z3,z29,z4,z23]),(0,[z0,z1,z437,z4,z5,z6]),(0,[z0,z1,z3,z4,z61,z567]),(0,[z0,z1,z850,z4,z5,z6])],[(0,[z28,z32,z4,z5,z111,z6]),(0,[z0,z1,z3,z4,z851,z6]),(0,[z106,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z571]),(0,[z0,z1,z3,z4,z852,z6]),(0,[z225,z1,z3,z4,z5,z23])],[(0,[z20,z1,z361,z4,z5,z6]),(0,[z1,z853,z3,z4,z5,z6]),(0,[z1,z32,z29,z4,z5,z23]),(0,[z31,z3,z29,z4,z62,z6]),(0,[z0,z1,z9,z551,z5,z6]),(0,[z0,z1,z3,z151,z149,z23]),(0,[z0,z1,z3,z4,z854,z62]),(0,[z855,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z856,z6])],[(0,[z0,z1,z3,z4,z399,z23])],[(0,[z857,z1,z28,z3,z4,z5]),(0,[z251,z1,z9,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z858]),(0,[z16,z1,z3,z4,z114,z346]),(0,[z334,z0,z1,z3,z4,z23]),(0,[z0,z1,z446,z3,z149,z6]),(0,[z112,z0,z178,z4,z5,z82]),(0,[z859,z1,z3,z4,z5,z6])],[(0,[z1,z28,z9,z4,z26,z5]),(0,[z1,z482,z2,z4,z5,z6]),(0,[z15,z1,z3,z4,z860,z6]),(0,[z0,z1,z3,z4,z861,z5]),(0,[z72,z1,z3,z4,z5,z108])]],
   [[(0,[z1,z28,z86,z4,z5,z6]),(0,[z199,z24,z1,z3,z5,z6]),(0,[z1,z28,z3,z4,z5,z108]),(0,[z15,z1,z3,z4,z862,z5]),(0,[z0,z1,z9,z4,z5,z863]),(0,[z0,z1,z3,z4,z94,z5])],[(0,[z0,z1,z3,z4,z5,z864]),(0,[z0,z1,z3,z4,z865,z6]),(0,[z0,z1,z9,z4,z5,z571]),(0,[z280,z0,z3,z4,z5,z82])],[(0,[z0,z87,z32,z4,z5,z6])],[(0,[z15,z1,z3,z524,z5,z6]),(0,[z0,z32,z4,z215,z5,z6]),(0,[z866,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z131,z23]),(0,[z1,z3,z4,z5,z6,z867]),(0,[z440,z0,z1,z4,z5,z175]),(0,[z1,z868,z3,z4,z5,z6])],[(0,[z0,z1,z361,z4,z5,z6]),(0,[z0,z1,z133,z4,z26,z5]),(0,[z20,z28,z32,z4,z5,z6]),(0,[z1,z28,z3,z4,z5,z307]),(0,[z0,z1,z3,z4,z869,z5]),(0,[z651,z1,z355,z4,z5,z6]),(0,[z0,z1,z543,z123,z5,z6]),(0,[z870,z1,z3,z4,z5,z6]),(0,[z871,z1,z3,z4,z5,z6])],[(0,[z448,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z872])],[(0,[z15,z1,z3,z80,z149,z6]),(0,[z63,z1,z3,z4,z127,z6]),(0,[z106,z1,z32,z4,z5,z6]),(0,[z122,z1,z9,z4,z5,z6]),(0,[z1,z3,z873,z4,z5,z6]),(0,[z38,z0,z1,z3,z551,z5]),(0,[z0,z222,z3,z4,z5,z425])],[(0,[z90,z1,z3,z4,z5,z205]),(0,[z212,z9,z29,z4,z5,z6]),(0,[z78,z0,z9,z4,z33,z6]),(0,[z874,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z875,z6]),(0,[z72,z1,z3,z80,z5,z6])],[(0,[z225,z1,z537,z4,z5,z6]),(0,[z0,z1,z194,z123,z5,z6])],[(0,[z20,z1,z3,z4,z5,z6]),(0,[z199,z1,z3,z4,z26,z5]),(0,[z59,z1,z663,z4,z5,z6]),(0,[z38,z0,z1,z3,z430,z5])],[(0,[z0,z1,z876,z4,z5,z6]),(0,[z0,z1,z3,z4,z877,z6]),(0,[z0,z1,z32,z4,z861,z5]),(0,[z165,z0,z1,z4,z347,z6]),(0,[z0,z1,z3,z4,z5,z878]),(0,[z148,z1,z4,z5,z246,z6])],[(0,[z0,z1,z879,z3,z5,z6]),(0,[z15,z1,z110,z3,z149,z6]),(0,[z0,z1,z32,z4,z94,z5]),(0,[z112,z0,z522,z3,z4,z5]),(0,[z880,z1,z3,z193,z5,z6]),(0,[z442,z1,z3,z4,z245,z5])],[(0,[z0,z1,z881,z4,z5,z6]),(0,[z104,z1,z3,z29,z5,z6]),(0,[z0,z1,z3,z882,z5,z6]),(0,[z0,z1,z883,z4,z5,z6]),(0,[z1,z3,z884,z4,z5,z6]),(0,[z0,z1,z3,z4,z345,z23]),(0,[z623,z1,z3,z4,z26,z5])],[(0,[z15,z1,z885,z4,z5,z6]),(0,[z1,z779,z3,z4,z5,z6]),(0,[z886,z1,z3,z4,z5,z6]),(0,[z887,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z71,z503,z5]),(0,[z0,z1,z100,z3,z4,z307]),(0,[z888,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z889,z5,z6]),(0,[z1,z3,z29,z4,z890,z6]),(0,[z63,z1,z3,z4,z722,z6]),(0,[z1,z252,z3,z4,z5,z23]),(0,[z0,z31,z3,z4,z751,z6])],[(0,[z239,z1,z34,z4,z5,z6]),(0,[z0,z1,z891,z4,z5,z6]),(0,[z0,z1,z3,z5,z322,z586]),(0,[z0,z1,z3,z4,z493,z23]),(0,[z380,z892,z3,z4,z5,z6])]],
   [[(0,[z15,z1,z88,z3,z149,z6]),(0,[z488,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z64,z145,z6]),(0,[z0,z1,z32,z4,z5,z872]),(0,[z0,z1,z3,z4,z751,z6]),(0,[z0,z1,z3,z893,z5,z6]),(0,[z1,z894,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z176,z9,z4,z5,z6]),(0,[z272,z31,z3,z4,z62,z6])],[(0,[z20,z1,z531,z4,z5,z6]),(0,[z222,z3,z29,z4,z5,z6]),(0,[z1,z3,z4,z5,z22,z55]),(0,[z0,z1,z3,z4,z895,z6]),(0,[z616,z0,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z896,z6])],[(0,[z1,z3,z4,z897,z5,z6]),(0,[z0,z660,z32,z4,z5,z6]),(0,[z898,z1,z3,z4,z5,z6]),(0,[z1,z899,z3,z4,z5,z6])],[(0,[z20,z1,z32,z4,z5,z6]),(0,[z1,z900,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z5,z227]),(0,[z563,z1,z60,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z166]),(0,[z15,z1,z3,z646,z5,z6]),(0,[z1,z3,z29,z701,z5,z6]),(0,[z0,z118,z32,z4,z5,z6]),(0,[z901,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z551,z5,z6]),(0,[z0,z1,z3,z4,z5,z902])],[(0,[z0,z1,z903,z4,z5,z6]),(0,[z1,z904,z3,z4,z5,z6]),(0,[z30,z1,z3,z29,z5,z6]),(0,[z0,z1,z3,z4,z5,z905]),(0,[z0,z1,z537,z4,z26,z5]),(0,[z0,z1,z3,z4,z906,z5]),(0,[z0,z1,z136,z817,z5,z6]),(0,[z106,z1,z3,z193,z5,z6])],[(0,[z668,z0,z1,z343,z5,z6]),(0,[z0,z1,z3,z4,z5,z907]),(0,[z908,z1,z3,z4,z5,z6])],[(0,[z28,z3,z4,z650,z5,z6]),(0,[z0,z1,z32,z4,z5,z567]),(0,[z0,z380,z3,z4,z5,z425])],[(0,[z199,z1,z3,z67,z5,z6]),(0,[z24,z1,z28,z136,z5,z6]),(0,[z21,z1,z34,z4,z5,z6]),(0,[z15,z1,z3,z4,z127,z23]),(0,[z909,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z910,z5,z6]),(0,[z0,z1,z3,z4,z5,z863]),(0,[z0,z1,z401,z4,z5,z166]),(0,[z0,z1,z911,z4,z5,z6]),(0,[z105,z0,z380,z4,z27,z6]),(0,[z0,z1,z4,z5,z246,z23])],[(0,[z0,z1,z3,z4,z318,z23])],[(0,[z15,z1,z3,z196,z5,z6]),(0,[z1,z110,z3,z29,z4,z26]),(0,[z0,z1,z531,z4,z5,z6]),(0,[z912,z0,z1,z3,z4,z5]),(0,[z0,z174,z3,z4,z5,z111])],[(0,[z515,z28,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z166]),(0,[z488,z1,z32,z4,z5,z6]),(0,[z0,z367,z32,z4,z5,z6]),(0,[z1,z277,z3,z4,z5,z23]),(0,[z913,z1,z3,z4,z5,z23])],[(0,[z1,z28,z3,z4,z5,z914]),(0,[z1,z28,z3,z4,z5,z346]),(0,[z0,z433,z32,z4,z5,z6]),(0,[z0,z1,z3,z5,z915,z6]),(0,[z59,z1,z374,z4,z5,z6]),(0,[z15,z1,z3,z4,z198,z23]),(0,[z0,z1,z3,z524,z26,z5]),(0,[z46,z0,z1,z4,z5,z175])],[(0,[z0,z1,z3,z4,z5,z916]),(0,[z105,z1,z3,z29,z4,z23]),(0,[z0,z1,z401,z4,z5,z37]),(0,[z0,z1,z537,z295,z5,z6]),(0,[z0,z1,z3,z4,z549,z23])],[(0,[z15,z1,z3,z50,z5,z6]),(0,[z122,z1,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z5,z309]),(0,[z0,z1,z3,z4,z917,z5]),(0,[z0,z1,z325,z4,z5,z23]),(0,[z0,z1,z3,z4,z918,z6]),(0,[z0,z1,z136,z3,z149,z23])],[(0,[z0,z1,z919,z4,z5,z6]),(0,[z15,z1,z3,z5,z54,z6]),(0,[z0,z1,z32,z551,z5,z6]),(0,[z105,z0,z1,z4,z347,z6]),(0,[z283,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z920,z6]),(0,[z379,z1,z3,z4,z5,z23])]],
   [[(0,[z15,z1,z3,z4,z61,z23]),(0,[z30,z1,z32,z29,z5,z6]),(0,[z921,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z318]),(0,[z1,z3,z4,z5,z6,z922])],[(0,[z0,z1,z3,z4,z518,z23]),(0,[z15,z1,z923,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z166])],[(0,[z1,z28,z32,z4,z26,z5]),(0,[z1,z202,z29,z4,z5,z6]),(0,[z15,z1,z194,z5,z149,z6]),(0,[z924,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z193,z5,z6]),(0,[z1,z3,z29,z4,z198,z23]),(0,[z0,z1,z9,z4,z157,z5]),(0,[z0,z1,z3,z413,z5,z571]),(0,[z925,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z926]),(0,[z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z599,z5,z6]),(0,[z0,z1,z3,z755,z5,z6]),(0,[z927,z1,z3,z4,z5,z6]),(0,[z928,z1,z3,z413,z5,z6]),(0,[z1,z3,z4,z929,z5,z6]),(0,[z0,z1,z930,z4,z5,z6])],[(0,[z21,z1,z536,z4,z5,z6]),(0,[z1,z8,z29,z4,z5,z6]),(0,[z15,z1,z3,z4,z931,z6]),(0,[z1,z3,z932,z4,z5,z6]),(0,[z0,z156,z32,z4,z5,z6]),(0,[z272,z1,z87,z4,z5,z6])],[(0,[z822,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z37]),(0,[z0,z1,z88,z3,z149,z227])],[(0,[z96,z1,z34,z4,z5,z6]),(0,[z15,z217,z32,z4,z5,z6]),(0,[z1,z3,z4,z5,z722,z6]),(0,[z640,z1,z9,z4,z5,z6]),(0,[z78,z0,z3,z4,z33,z410])],[(0,[z0,z1,z3,z4,z933,z6]),(0,[z89,z28,z3,z4,z26,z5]),(0,[z1,z28,z3,z4,z318,z6]),(0,[z0,z415,z9,z4,z5,z6]),(0,[z15,z1,z3,z525,z5,z6]),(0,[z0,z1,z3,z5,z322,z23]),(0,[z0,z1,z4,z5,z934,z6]),(0,[z0,z1,z107,z4,z5,z93]),(0,[z0,z354,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z111])],[(0,[z122,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z4,z935,z5]),(0,[z78,z0,z3,z413,z33,z6]),(1,[z0,z3,z4,z5,z718])],[(0,[z1,z3,z936,z413,z5,z6]),(0,[z937,z1,z3,z4,z5,z6])],[(0,[z772,z28,z3,z4,z5,z6]),(0,[z1,z3,z938,z4,z5,z6]),(0,[z0,z1,z939,z4,z5,z6]),(0,[z0,z1,z3,z193,z5,z6])],[(0,[z1,z9,z260,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z926]),(0,[z15,z1,z3,z4,z85,z6]),(0,[z0,z9,z736,z4,z5,z6]),(0,[z106,z222,z3,z4,z5,z6]),(0,[z940,z1,z3,z4,z26,z5])],[(0,[z1,z28,z325,z4,z5,z6]),(0,[z212,z217,z3,z4,z5,z6]),(0,[z15,z1,z941,z4,z5,z6]),(0,[z0,z1,z9,z4,z61,z23]),(0,[z181,z0,z1,z3,z4,z23]),(0,[z0,z1,z4,z5,z942,z6]),(0,[z0,z1,z4,z5,z6,z943])],[(0,[z15,z1,z133,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z944]),(0,[z1,z945,z3,z4,z5,z6]),(0,[z0,z1,z946,z4,z26,z5])],[(0,[z651,z1,z34,z4,z5,z6]),(0,[z947,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z17,z6]),(0,[z120,z1,z3,z4,z26,z5]),(0,[z0,z1,z18,z3,z149,z6]),(0,[z691,z0,z3,z4,z5,z82]),(0,[z0,z1,z3,z4,z5,z948]),(0,[z0,z1,z3,z4,z949,z6]),(0,[z105,z0,z1,z134,z4,z23]),(0,[z0,z1,z950,z4,z5,z6])]],
   [[(0,[z21,z1,z355,z4,z5,z6]),(0,[z248,z20,z1,z3,z4,z5]),(0,[z0,z1,z401,z4,z85,z6])],[(0,[z59,z1,z398,z4,z5,z6]),(0,[z15,z32,z4,z5,z33,z6]),(0,[z951,z1,z3,z4,z5,z6]),(0,[z952,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z23]),(0,[z0,z1,z511,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z953]),(0,[z1,z3,z4,z954,z5,z6])],[(0,[z1,z3,z265,z29,z5,z6]),(0,[z1,z32,z4,z445,z5,z6]),(0,[z0,z1,z287,z4,z26,z5]),(0,[z0,z1,z401,z4,z17,z6]),(0,[z0,z48,z3,z152,z5,z23])],[(0,[z96,z1,z536,z4,z5,z6]),(0,[z0,z1,z3,z955,z5,z6]),(0,[z1,z268,z3,z29,z5,z6]),(0,[z0,z1,z817,z3,z5,z6])],[(0,[z20,z1,z437,z4,z5,z6]),(0,[z15,z956,z3,z4,z5,z6]),(1,[z15,z1,z3,z149,z23])],[(0,[z1,z3,z29,z4,z17,z6]),(0,[z0,z1,z32,z193,z5,z6]),(0,[z0,z1,z401,z4,z5,z23])],[(0,[z1,z28,z3,z5,z322,z6]),(0,[z1,z3,z829,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z957]),(0,[z0,z1,z3,z4,z254,z23]),(0,[z1,z3,z958,z4,z5,z6])],[(0,[z0,z32,z4,z5,z189,z6]),(0,[z0,z1,z9,z4,z5,z959]),(0,[z105,z0,z1,z65,z4,z23]),(0,[z0,z1,z3,z190,z5,z368])],[(0,[z0,z1,z3,z4,z767,z6]),(0,[z1,z3,z29,z4,z5,z23]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z85,z6]),(0,[z0,z1,z3,z4,z339,z23]),(0,[z24,z0,z1,z136,z5,z23]),(0,[z961,z1,z3,z4,z5,z6]),(0,[z0,z1,z962,z4,z5,z6])],[],[(0,[z28,z118,z3,z4,z5,z6]),(0,[z78,z20,z3,z4,z33,z6]),(0,[z20,z1,z3,z4,z94,z5]),(0,[z1,z963,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z619,z6]),(0,[z0,z1,z327,z4,z5,z571]),(0,[z44,z146,z3,z4,z5,z111]),(0,[z0,z1,z3,z4,z157,z5]),(0,[z1,z88,z3,z54,z149,z6]),(0,[z1,z3,z4,z26,z5,z160])],[(0,[z199,z1,z3,z5,z149,z6]),(0,[z0,z1,z3,z4,z964,z6]),(0,[z15,z965,z3,z4,z5,z6]),(0,[z0,z1,z3,z599,z5,z6]),(0,[z0,z1,z966,z4,z5,z6]),(0,[z105,z0,z1,z136,z4,z23]),(0,[z0,z1,z3,z4,z58,z23])],[(0,[z251,z1,z3,z514,z5,z6]),(0,[z15,z1,z32,z4,z5,z23]),(0,[z1,z3,z967,z4,z5,z6]),(0,[z106,z380,z3,z4,z5,z6]),(0,[z148,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z4,z388,z6])],[(0,[z38,z0,z1,z32,z5,z73]),(0,[z248,z0,z1,z9,z4,z5]),(1,[z0,z222,z3,z4,z23])],[(0,[z0,z1,z3,z968,z5,z6]),(0,[z83,z28,z3,z4,z5,z6]),(0,[z15,z1,z537,z4,z5,z6]),(0,[z15,z1,z70,z4,z5,z6]),(0,[z15,z1,z134,z3,z4,z23]),(0,[z0,z324,z32,z4,z5,z6]),(0,[z0,z222,z134,z4,z5,z6]),(0,[z969,z0,z1,z4,z5,z23]),(0,[z280,z0,z3,z4,z5,z520])]],
   [[(0,[z199,z1,z9,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z970]),(0,[z0,z783,z3,z4,z5,z6])],[(0,[z1,z3,z29,z4,z180,z23]),(0,[z78,z0,z327,z4,z33,z6]),(0,[z1,z3,z4,z5,z922,z23])],[(0,[z0,z1,z3,z4,z5,z790]),(0,[z1,z971,z3,z4,z5,z6]),(0,[z1,z3,z29,z483,z5,z6]),(0,[z0,z1,z3,z4,z972,z5]),(0,[z1,z88,z3,z29,z149,z6]),(0,[z0,z222,z3,z4,z5,z6]),(0,[z973,z1,z3,z4,z5,z6]),(0,[z210,z1,z178,z4,z5,z6])],[(0,[z0,z32,z4,z5,z211,z6]),(0,[z623,z1,z9,z4,z5,z6]),(0,[z974,z1,z3,z4,z5,z6]),(0,[z975,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z23,z943])],[(0,[z1,z3,z260,z4,z26,z5]),(0,[z0,z9,z32,z4,z5,z6]),(0,[z0,z1,z4,z5,z47,z831])],[(0,[z1,z28,z401,z4,z5,z6]),(0,[z15,z1,z3,z161,z5,z6]),(0,[z0,z1,z976,z4,z5,z6]),(0,[z0,z1,z977,z32,z4,z6]),(0,[z0,z1,z3,z71,z4,z318])],[(0,[z31,z28,z32,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z978]),(0,[z0,z1,z32,z4,z157,z5]),(0,[z0,z1,z3,z4,z26,z382])],[(0,[z1,z3,z67,z4,z5,z23]),(0,[z20,z1,z3,z4,z5,z567]),(0,[z0,z1,z3,z4,z5,z979]),(0,[z0,z1,z32,z599,z5,z6])],[(0,[z0,z1,z32,z4,z388,z6]),(0,[z980,z1,z3,z4,z5,z6])],[(0,[z1,z3,z29,z4,z76,z5]),(0,[z0,z1,z32,z4,z5,z37]),(0,[z0,z1,z155,z4,z5,z93]),(0,[z72,z1,z3,z5,z149,z6]),(0,[z273,z0,z1,z4,z332,z5])],[(0,[z1,z879,z28,z3,z5,z6]),(0,[z15,z1,z3,z33,z149,z6]),(0,[z15,z1,z100,z3,z4,z6]),(0,[z0,z736,z32,z4,z5,z6]),(0,[z0,z657,z32,z4,z5,z6]),(0,[z1,z146,z511,z4,z5,z6]),(0,[z981,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z264,z73])],[(0,[z982,z1,z3,z4,z5,z6]),(0,[z20,z380,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z983]),(0,[z0,z1,z450,z66,z5,z6]),(0,[z112,z0,z3,z4,z318,z82]),(0,[z0,z1,z65,z193,z5,z6])],[(0,[z984,z1,z3,z4,z5,z6]),(0,[z0,z985,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z274])],[(0,[z0,z222,z32,z4,z5,z6]),(0,[z0,z222,z110,z3,z4,z6])],[(0,[z1,z28,z9,z4,z5,z6]),(0,[z1,z28,z3,z4,z26,z23]),(0,[z0,z1,z110,z32,z4,z26]),(0,[z105,z0,z1,z4,z27,z23]),(0,[z986,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z551,z5,z6]),(0,[z0,z1,z10,z496,z5,z6]),(0,[z987,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z567]),(0,[z988,z1,z3,z4,z5,z6])]],
   [[(0,[z89,z772,z3,z4,z5,z6]),(0,[z15,z1,z107,z4,z5,z47]),(0,[z15,z1,z32,z161,z5,z6]),(0,[z0,z1,z3,z4,z5,z989]),(0,[z0,z1,z32,z4,z61,z23]),(0,[z0,z1,z3,z4,z990,z6]),(0,[z0,z1,z3,z4,z5,z959]),(0,[z112,z0,z325,z4,z5,z82])],[(0,[z380,z28,z3,z4,z5,z6]),(0,[z15,z1,z3,z29,z5,z6]),(0,[z0,z230,z32,z4,z5,z6]),(0,[z991,z1,z3,z4,z5,z6]),(0,[z1,z252,z87,z4,z5,z6])],[(0,[z13,z1,z3,z4,z5,z233]),(0,[z0,z1,z3,z4,z5,z992]),(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z1,z3,z80,z557,z6])],[(0,[z0,z1,z9,z524,z5,z6]),(0,[z0,z380,z3,z4,z5,z6]),(0,[z980,z1,z32,z4,z5,z6]),(0,[z994,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z295,z5,z23]),(0,[z0,z1,z3,z4,z619,z6]),(0,[z1,z3,z995,z4,z5,z6]),(0,[z103,z1,z3,z4,z5,z307]),(0,[z0,z1,z296,z4,z5,z487])],[(0,[z1,z3,z5,z54,z322,z6]),(0,[z1,z3,z4,z996,z5,z6]),(0,[z1,z3,z4,z997,z5,z6]),(0,[z759,z1,z3,z4,z5,z23])],[(0,[z0,z1,z3,z4,z26,z286]),(0,[z0,z1,z222,z3,z4,z23]),(0,[z0,z1,z3,z4,z497,z23]),(0,[z998,z1,z3,z4,z5,z6])],[(0,[z1,z32,z260,z4,z5,z6]),(0,[z0,z1,z100,z9,z4,z6]),(0,[z999,z1,z3,z4,z5,z6]),(0,[z0,z1,z1000,z4,z26,z5])],[(0,[z0,z1,z1001,z4,z5,z6]),(0,[z248,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z502,z23]),(0,[z0,z1,z1002,z4,z5,z6]),(0,[z0,z572,z3,z4,z62,z6]),(0,[z0,z1,z70,z4,z26,z5])],[(0,[z251,z1,z3,z4,z5,z6]),(0,[z1,z28,z3,z733,z4,z6]),(0,[z0,z1,z3,z4,z5,z1003]),(0,[z1,z531,z29,z4,z5,z6]),(0,[z235,z0,z1,z136,z5,z6]),(0,[z72,z1,z3,z4,z26,z5])],[(0,[z0,z1,z1004,z4,z5,z6]),(0,[z1,z28,z3,z4,z26,z5]),(0,[z15,z44,z3,z4,z5,z111]),(0,[z1,z3,z71,z29,z5,z186])],[(0,[z0,z1,z3,z4,z5,z1005]),(0,[z1,z3,z29,z4,z5,z1006]),(0,[z331,z0,z1,z4,z5,z175]),(0,[z0,z9,z419,z4,z5,z6]),(0,[z0,z1,z3,z4,z746,z6]),(0,[z1007,z1,z3,z4,z26,z5])],[(0,[z15,z1,z32,z29,z5,z6]),(0,[z15,z1,z3,z4,z5,z586]),(0,[z0,z1,z32,z4,z85,z6]),(0,[z0,z1,z3,z4,z5,z571]),(0,[z0,z222,z3,z193,z5,z6]),(0,[z0,z1,z3,z80,z787,z6])],[(0,[z30,z1,z3,z260,z5,z6]),(0,[z15,z1,z287,z4,z5,z6]),(0,[z1,z401,z29,z4,z5,z6]),(0,[z0,z1,z1008,z9,z4,z6]),(0,[z120,z1,z401,z4,z5,z6]),(0,[z928,z1,z3,z4,z5,z6])],[(0,[z1,z3,z5,z1009,z149,z6]),(0,[z16,z1,z3,z4,z722,z6]),(0,[z0,z1,z32,z4,z619,z6]),(0,[z334,z0,z32,z4,z5,z6]),(0,[z0,z380,z32,z4,z5,z6]),(0,[z105,z0,z222,z4,z27,z6]),(0,[z0,z1,z3,z42,z5,z307])],[(0,[z89,z28,z9,z4,z5,z6]),(0,[z0,z1,z88,z9,z149,z6]),(0,[z0,z408,z9,z4,z5,z6])]],
   [[(0,[z59,z1,z710,z4,z5,z6]),(0,[z0,z842,z3,z4,z5,z6]),(0,[z0,z31,z32,z4,z5,z23]),(0,[z691,z0,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z513,z23])],[(0,[z15,z31,z3,z4,z62,z6]),(0,[z16,z1,z3,z4,z114,z333]),(0,[z36,z0,z3,z269,z151,z5])],[(0,[z1,z28,z3,z295,z5,z6]),(0,[z1010,z0,z1,z3,z4,z6]),(0,[z0,z1,z1011,z4,z5,z6]),(0,[z78,z0,z3,z4,z33,z6]),(0,[z0,z222,z65,z4,z5,z6]),(0,[z1012,z1,z3,z4,z5,z6])],[(0,[z1,z3,z29,z4,z5,z586]),(0,[z0,z1,z1013,z4,z5,z6]),(0,[z0,z40,z9,z4,z5,z6]),(0,[z1,z3,z936,z4,z5,z6])],[(0,[z20,z176,z3,z4,z5,z6]),(0,[z251,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1014]),(0,[z1,z3,z4,z722,z114,z6])],[(0,[z78,z28,z3,z4,z33,z6]),(0,[z1,z70,z29,z4,z5,z6]),(0,[z105,z1,z29,z4,z27,z6]),(1,[z0,z3,z798,z5,z6]),(0,[z0,z1,z3,z4,z62,z108])],[(0,[z1015,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z1016]),(0,[z120,z1,z9,z4,z5,z6]),(0,[z1,z3,z4,z5,z1017,z6]),(0,[z0,z1,z3,z4,z5,z1018]),(0,[z777,z1,z3,z4,z5,z6]),(0,[z103,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z193,z6,z23]),(0,[z0,z1,z88,z3,z787,z6])],[(0,[z0,z1,z3,z4,z860,z6]),(0,[z0,z1,z3,z4,z5,z1019]),(0,[z0,z1,z32,z4,z5,z571]),(0,[z1,z892,z3,z4,z5,z6]),(0,[z0,z1,z780,z4,z5,z6]),(0,[z1,z3,z80,z61,z467,z6])],[(0,[z0,z1,z3,z4,z862,z5]),(0,[z1020,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z152,z149,z23])],[(0,[z0,z1,z9,z4,z5,z586]),(0,[z1,z3,z1021,z4,z5,z6]),(0,[z577,z0,z1,z3,z5,z73]),(0,[z0,z1,z3,z4,z1022,z5])],[(0,[z15,z1,z9,z80,z5,z6]),(0,[z697,z0,z1,z3,z5,z73]),(0,[z0,z1,z3,z4,z33,z108])],[(0,[z0,z1,z1023,z4,z5,z6]),(0,[z0,z1,z3,z524,z5,z6]),(0,[z362,z3,z4,z220,z5,z6]),(0,[z24,z1,z136,z29,z5,z6]),(0,[z14,z0,z1,z3,z4,z23])],[(0,[z41,z1,z9,z4,z5,z6]),(0,[z0,z1,z9,z4,z198,z23]),(0,[z36,z119,z3,z151,z5,z6]),(0,[z0,z1,z537,z4,z5,z410]),(0,[z0,z1,z1024,z4,z5,z6]),(0,[z1025,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z425]),(0,[z20,z1,z511,z4,z5,z6]),(0,[z0,z1,z3,z5,z1026,z6]),(0,[z1027,z1,z3,z4,z5,z6]),(0,[z78,z0,z32,z4,z33,z6]),(0,[z143,z1,z86,z4,z5,z6]),(0,[z0,z44,z3,z4,z397,z5]),(0,[z0,z380,z3,z193,z5,z6])],[(0,[z20,z192,z3,z4,z5,z6]),(0,[z0,z1,z1028,z4,z5,z6]),(0,[z1,z9,z4,z5,z54,z6]),(0,[z0,z1,z3,z4,z5,z1029]),(0,[z0,z1,z537,z413,z5,z6]),(0,[z0,z1,z3,z71,z551,z5]),(0,[z1030,z1,z3,z4,z5,z6])],[(0,[z28,z3,z4,z5,z211,z6]),(0,[z1,z384,z3,z4,z5,z22]),(0,[z20,z324,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z890,z6]),(0,[z0,z1,z88,z3,z26,z149]),(0,[z0,z1,z3,z5,z719,z73]),(0,[z0,z1,z3,z4,z1031,z6]),(0,[z0,z1,z1032,z4,z5,z23])]],
   [[(0,[z1,z28,z3,z413,z5,z6]),(0,[z1,z3,z4,z445,z5,z6]),(0,[z0,z1,z65,z496,z5,z6]),(0,[z0,z1,z1033,z4,z5,z6])],[(0,[z59,z1,z60,z4,z5,z23]),(0,[z1,z3,z1034,z4,z5,z6]),(0,[z1,z3,z4,z1035,z5,z6]),(0,[z112,z0,z9,z4,z5,z82]),(0,[z119,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z42,z26,z5])],[(0,[z0,z1,z3,z1036,z5,z6]),(0,[z48,z28,z32,z4,z5,z6]),(0,[z1,z28,z3,z4,z62,z23]),(0,[z77,z1,z3,z4,z26,z5]),(0,[z0,z31,z3,z4,z185,z62]),(0,[z0,z1,z3,z80,z61,z108]),(0,[z0,z1,z3,z4,z157,z23])],[(0,[z0,z1,z1037,z4,z5,z6]),(0,[z16,z1,z9,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z1038])],[(0,[z28,z3,z4,z220,z5,z6]),(0,[z20,z1,z3,z4,z5,z166]),(0,[z1,z9,z29,z4,z26,z5]),(0,[z148,z1,z9,z4,z5,z6]),(0,[z1039,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1040])],[(0,[z15,z1,z87,z4,z5,z6]),(0,[z15,z1,z3,z5,z1009,z6]),(0,[z0,z1,z885,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z116]),(0,[z1041,z0,z1,z3,z4,z5])],[(0,[z28,z9,z32,z4,z5,z6]),(0,[z20,z1,z3,z4,z157,z5]),(0,[z15,z1,z3,z80,z26,z5]),(0,[z691,z0,z3,z151,z5,z6]),(0,[z0,z1,z3,z4,z854,z23])],[(0,[z89,z28,z3,z4,z5,z6]),(0,[z1042,z1,z3,z4,z5,z6]),(0,[z20,z1,z3,z599,z5,z6]),(0,[z1,z3,z1043,z4,z5,z6]),(0,[z1044,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z388,z6]),(0,[z41,z1,z3,z4,z26,z5]),(0,[z0,z3,z4,z5,z111,z718]),(0,[z0,z1,z88,z3,z149,z6])],[(0,[z1,z28,z3,z4,z5,z1045]),(0,[z20,z1,z3,z4,z5,z37]),(0,[z63,z1,z3,z64,z322,z6]),(0,[z182,z1,z3,z4,z5,z91]),(0,[z0,z1,z327,z4,z5,z23]),(0,[z103,z1,z3,z4,z5,z425]),(0,[z0,z1,z1046,z4,z5,z6])],[(0,[z1,z28,z1047,z3,z5,z6]),(0,[z20,z1,z9,z4,z5,z23]),(0,[z7,z772,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z1048]),(0,[z77,z1,z3,z295,z5,z6]),(0,[z0,z1,z3,z4,z43,z388])],[(0,[z0,z1,z3,z1049,z5,z6]),(0,[z51,z32,z29,z4,z5,z6]),(0,[z1,z178,z29,z4,z5,z6]),(0,[z940,z1,z3,z4,z5,z6])],[(0,[z20,z217,z3,z4,z5,z6]),(0,[z251,z324,z3,z4,z5,z6]),(0,[z63,z1,z3,z4,z64,z23]),(0,[z0,z1,z3,z1050,z5,z6]),(0,[z0,z1,z3,z4,z546,z23]),(0,[z0,z1,z3,z4,z506,z23]),(0,[z0,z1,z3,z4,z609,z23]),(0,[z0,z1,z3,z4,z5,z166]),(0,[z0,z1,z1051,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1052]),(0,[z1,z194,z4,z5,z54,z6])],[(0,[z0,z1,z3,z4,z1053,z6]),(0,[z1,z28,z3,z1054,z5,z6]),(0,[z1,z28,z3,z4,z6,z465]),(0,[z20,z222,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z1055,z6]),(0,[z15,z1,z3,z381,z5,z6]),(0,[z0,z222,z3,z4,z6,z23])],[(0,[z0,z1,z3,z4,z5,z1016]),(0,[z90,z1,z3,z4,z5,z158]),(0,[z0,z1,z1056,z4,z5,z6]),(0,[z113,z0,z3,z4,z33,z6])],[(0,[z1,z28,z3,z4,z5,z333]),(0,[z20,z9,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1057]),(0,[z0,z1,z9,z4,z17,z6]),(0,[z0,z1,z178,z4,z318,z6])]],
   [[(0,[z20,z1,z3,z4,z61,z23]),(0,[z0,z1,z3,z4,z127,z23]),(0,[z1058,z1,z3,z4,z5,z6]),(0,[z0,z32,z4,z320,z5,z6]),(0,[z36,z0,z3,z151,z26,z5]),(0,[z0,z191,z3,z4,z5,z111])],[(0,[z15,z1,z194,z4,z5,z6]),(0,[z0,z469,z32,z4,z5,z6]),(0,[z1059,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z37]),(0,[z1060,z1,z3,z4,z5,z6]),(0,[z0,z1,z1061,z4,z5,z6]),(0,[z0,z1,z3,z4,z388,z186])],[(0,[z1,z772,z3,z4,z5,z6]),(0,[z89,z28,z32,z4,z5,z6]),(0,[z640,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z23]),(0,[z0,z1,z3,z4,z854,z5]),(0,[z1062,z1,z3,z4,z5,z6])],[(0,[z1063,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1064]),(0,[z0,z1,z3,z4,z5,z718]),(0,[z24,z25,z1,z136,z5,z6])],[(0,[z46,z1,z28,z4,z5,z175]),(0,[z0,z1,z3,z4,z935,z5]),(0,[z1065,z1,z3,z4,z5,z6]),(0,[z106,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z149,z309]),(0,[z0,z1,z3,z4,z198,z23]),(0,[z0,z1,z1066,z4,z5,z6])],[(0,[z250,z217,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z76,z5]),(0,[z51,z0,z32,z4,z5,z23]),(0,[z0,z1,z3,z1067,z5,z6]),(0,[z0,z1,z1068,z3,z4,z5]),(0,[z1,z1069,z3,z4,z5,z6])],[(0,[z248,z0,z1,z3,z4,z746]),(0,[z0,z1,z107,z4,z47,z465])],[(0,[z15,z1,z1070,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z166]),(0,[z0,z375,z3,z4,z62,z6]),(0,[z0,z1071,z3,z4,z5,z6]),(0,[z1,z3,z56,z4,z26,z5]),(0,[z1072,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z54,z149,z23]),(0,[z1,z3,z4,z61,z467,z23])],[(0,[z1,z28,z327,z4,z5,z6]),(0,[z1073,z1,z3,z4,z5,z6]),(0,[z1074,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z61,z23]),(0,[z1,z1075,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z470,z23])],[(0,[z0,z1,z923,z4,z5,z6]),(0,[z45,z3,z67,z4,z5,z6]),(0,[z0,z1076,z32,z4,z5,z6]),(0,[z105,z0,z1,z3,z193,z23]),(0,[z0,z1077,z3,z4,z5,z6])],[(0,[z15,z1,z3,z5,z137,z6]),(0,[z0,z1,z4,z826,z27,z6])],[(1,[z217,z32,z4,z5,z6]),(0,[z1,z217,z3,z80,z5,z6]),(0,[z16,z1,z3,z4,z114,z6]),(0,[z1,z3,z4,z1078,z5,z6]),(0,[z0,z1,z3,z5,z186,z719])],[(0,[z20,z1,z3,z4,z85,z6]),(0,[z0,z1,z1079,z4,z5,z6]),(0,[z1,z3,z4,z1080,z5,z6]),(0,[z0,z330,z32,z4,z5,z6]),(0,[z90,z1,z9,z4,z5,z22]),(0,[z24,z0,z1,z817,z5,z6]),(0,[z0,z1,z3,z4,z1040,z23])],[(0,[z0,z1,z3,z4,z931,z6]),(0,[z69,z1,z3,z4,z26,z5]),(0,[z640,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z1081,z5,z6])],[(0,[z20,z1,z133,z4,z5,z6]),(0,[z20,z1,z3,z4,z619,z6]),(0,[z0,z1,z3,z4,z5,z1082]),(0,[z0,z1,z87,z4,z26,z5]),(0,[z1,z739,z3,z4,z5,z23])],[(0,[z0,z1,z3,z4,z807,z6]),(0,[z15,z1,z3,z5,z145,z6]),(0,[z0,z217,z32,z4,z5,z6]),(0,[z692,z1,z3,z29,z5,z6]),(0,[z1,z3,z1083,z4,z5,z6]),(0,[z0,z1,z32,z4,z198,z23]),(0,[z105,z0,z1,z32,z4,z23]),(0,[z210,z1,z3,z4,z318,z6])]],
   [[(0,[z63,z1,z3,z524,z64,z6]),(0,[z72,z1,z9,z4,z5,z6]),(0,[z1084,z0,z1,z3,z4,z5]),(0,[z1,z1085,z3,z4,z5,z6])],[(0,[z15,z1,z3,z150,z5,z6]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z451,z1,z3,z4,z5,z23])],[(0,[z15,z1,z3,z4,z185,z5]),(0,[z0,z1,z9,z4,z76,z5]),(0,[z0,z1,z3,z4,z5,z746]),(0,[z379,z1,z65,z123,z5,z6])],[(0,[z1,z3,z260,z4,z5,z6]),(0,[z0,z3,z736,z4,z5,z6]),(0,[z1087,z1,z9,z4,z5,z6]),(0,[z0,z1,z86,z4,z26,z5]),(0,[z0,z1,z1088,z4,z5,z6]),(0,[z750,z1,z3,z4,z5,z23])],[(0,[z1,z133,z29,z4,z5,z6]),(0,[z390,z1,z3,z4,z5,z91]),(0,[z1,z325,z29,z4,z5,z6]),(0,[z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z1089,z4,z5,z6]),(0,[z210,z1,z325,z4,z5,z6]),(0,[z46,z623,z1,z4,z5,z175]),(0,[z1090,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1091,z4,z5,z6]),(0,[z0,z1092,z3,z4,z5,z6]),(0,[z0,z1,z941,z4,z5,z6]),(0,[z1,z3,z29,z4,z1093,z6]),(0,[z0,z1,z3,z4,z5,z1094]),(0,[z1095,z1,z3,z4,z5,z6]),(0,[z1096,z1,z3,z4,z5,z6])],[(0,[z0,z1,z133,z4,z5,z6]),(0,[z16,z1,z32,z4,z114,z6])],[(0,[z20,z1,z3,z4,z5,z571]),(0,[z1097,z1,z3,z4,z5,z6]),(0,[z148,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z26,z17]),(0,[z0,z1,z262,z3,z5,z52]),(0,[z1,z1098,z3,z4,z26,z5])],[(0,[z15,z1099,z3,z4,z5,z6]),(0,[z15,z1,z178,z4,z5,z6]),(0,[z0,z1,z1100,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z1101]),(0,[z1,z32,z4,z5,z54,z6]),(0,[z0,z1,z1102,z4,z5,z6])],[(0,[z15,z1,z3,z260,z5,z6]),(0,[z1,z3,z29,z4,z185,z5]),(0,[z63,z1,z3,z4,z76,z64]),(0,[z0,z32,z4,z5,z33,z6]),(0,[z1059,z1,z3,z4,z5,z6]),(0,[z1,z3,z995,z551,z5,z6]),(0,[z0,z1,z3,z551,z619,z6]),(0,[z148,z1,z3,z4,z149,z23])],[(0,[z0,z1,z3,z4,z5,z23]),(0,[z522,z28,z3,z4,z5,z6]),(0,[z0,z705,z9,z4,z5,z6]),(0,[z0,z1,z1103,z3,z4,z6]),(0,[z0,z1,z194,z4,z26,z5]),(0,[z0,z1,z3,z4,z430,z23])],[(0,[z199,z1,z3,z4,z5,z6]),(0,[z1,z126,z3,z4,z321,z6]),(0,[z217,z3,z152,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z1104]),(0,[z78,z15,z3,z4,z33,z6]),(0,[z15,z1,z3,z42,z5,z6]),(0,[z0,z1,z9,z4,z6,z1105])],[(0,[z0,z1,z3,z4,z5,z843]),(0,[z0,z1,z3,z4,z26,z85]),(0,[z36,z3,z445,z151,z5,z6]),(0,[z0,z44,z3,z4,z5,z718])],[(0,[z20,z1,z32,z4,z5,z23]),(0,[z0,z956,z3,z4,z5,z6]),(0,[z15,z1,z3,z170,z5,z6]),(0,[z51,z128,z32,z4,z5,z6]),(0,[z0,z1,z3,z1106,z4,z6]),(0,[z103,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z584,z23])],[(0,[z623,z1,z3,z4,z5,z6]),(0,[z30,z1,z3,z29,z5,z23]),(0,[z1,z65,z56,z123,z5,z6])],[(0,[z0,z1,z1107,z4,z5,z6]),(0,[z20,z1,z537,z4,z5,z6]),(0,[z20,z1,z134,z3,z4,z23]),(0,[z0,z1,z202,z4,z26,z5]),(0,[z0,z1,z3,z4,z1108,z6]),(0,[z0,z1,z9,z4,z185,z5]),(0,[z119,z1,z401,z4,z5,z6]),(1,[z0,z1,z3,z4,z803])]],
   [[(0,[z1,z1109,z3,z4,z5,z6]),(0,[z1074,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1110]),(0,[z77,z1,z327,z4,z5,z6]),(0,[z0,z1,z1111,z4,z5,z6]),(1,[z0,z1,z194,z4,z23])],[(0,[z0,z1,z3,z4,z1112,z5]),(0,[z0,z1,z3,z4,z5,z1113]),(0,[z1114,z1,z3,z4,z5,z6])],[(0,[z1,z3,z29,z42,z5,z6]),(0,[z0,z1,z3,z4,z5,z858]),(0,[z0,z1,z3,z4,z180,z23]),(0,[z0,z1,z1115,z4,z5,z6]),(0,[z0,z1,z32,z4,z17,z6]),(0,[z0,z1,z3,z151,z5,z37]),(0,[z0,z1,z1116,z4,z5,z6])],[(0,[z0,z1,z3,z1117,z5,z6]),(0,[z165,z0,z1,z9,z4,z23]),(0,[z0,z1,z531,z4,z5,z23]),(0,[z0,z3,z4,z33,z153,z23]),(0,[z1118,z1,z3,z4,z5,z6])],[(0,[z28,z3,z4,z5,z6,z304]),(0,[z0,z965,z3,z4,z5,z6]),(0,[z0,z1,z3,z413,z5,z23]),(0,[z1119,z1,z3,z4,z5,z6]),(0,[z1,z1120,z3,z4,z5,z6]),(0,[z1,z3,z4,z467,z5,z23])],[(0,[z112,z20,z3,z4,z5,z82]),(0,[z15,z1,z65,z123,z5,z6]),(0,[z0,z1,z32,z4,z5,z23]),(0,[z554,z0,z1,z32,z4,z23]),(0,[z0,z1,z1000,z4,z5,z6]),(0,[z1,z3,z4,z1121,z5,z6])],[(0,[z199,z1,z32,z4,z5,z6]),(0,[z20,z1,z3,z524,z5,z6]),(0,[z63,z1,z3,z4,z64,z586]),(0,[z0,z1,z3,z4,z5,z1122]),(0,[z1,z277,z86,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z388])],[(0,[z1,z1123,z3,z4,z5,z6]),(0,[z0,z1,z537,z4,z5,z6]),(0,[z0,z1,z70,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z23]),(0,[z0,z1,z1124,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z970]),(0,[z72,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z1106,z4,z6]),(0,[z119,z1,z9,z4,z5,z6]),(0,[z0,z1,z9,z42,z5,z6])],[(0,[z1,z28,z3,z4,z5,z6]),(0,[z1125,z1,z3,z4,z5,z6]),(0,[z1,z437,z29,z4,z5,z6]),(0,[z128,z1,z3,z4,z5,z23]),(0,[z623,z1,z32,z4,z5,z6]),(0,[z77,z1,z9,z4,z5,z6]),(0,[z1,z1126,z3,z4,z5,z6]),(0,[z0,z1127,z3,z4,z5,z6])],[(0,[z20,z1,z100,z3,z4,z6]),(0,[z15,z1,z3,z4,z117,z23]),(0,[z15,z1128,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z264,z6]),(0,[z15,z1,z3,z5,z187,z6]),(0,[z0,z44,z9,z4,z5,z111]),(0,[z38,z0,z1,z9,z5,z73]),(0,[z1129,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z80,z127,z6]),(0,[z9,z32,z29,z4,z5,z6]),(0,[z1,z3,z4,z26,z997,z5])],[(0,[z0,z1,z4,z5,z1130,z6]),(0,[z0,z1,z3,z4,z26,z318])],[(0,[z89,z28,z361,z4,z5,z6]),(0,[z1,z28,z3,z5,z771,z6]),(0,[z15,z1,z3,z142,z5,z6]),(0,[z248,z0,z1,z3,z5,z73]),(0,[z78,z0,z3,z4,z33,z571]),(0,[z0,z1,z3,z4,z6,z1131]),(0,[z25,z1,z3,z4,z5,z23]),(0,[z0,z1,z88,z246,z149,z6]),(0,[z0,z1,z930,z4,z5,z23])],[(0,[z20,z7,z3,z4,z5,z23]),(0,[z15,z1,z110,z3,z4,z26]),(0,[z36,z0,z401,z151,z5,z6]),(0,[z1132,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z269,z5]),(0,[z143,z48,z3,z152,z5,z6]),(0,[z1133,z1,z3,z4,z5,z6])]],
   [[(0,[z20,z1,z107,z4,z5,z47]),(0,[z1,z3,z729,z42,z5,z6]),(0,[z0,z1,z3,z4,z26,z803])],[(0,[z1,z28,z3,z4,z5,z410]),(0,[z15,z1,z3,z4,z5,z116]),(0,[z30,z1,z3,z1134,z5,z6]),(0,[z1,z3,z1135,z4,z5,z6]),(0,[z1,z3,z29,z4,z264,z6]),(0,[z0,z1,z32,z4,z5,z1122]),(0,[z0,z1,z178,z4,z26,z5]),(0,[z1,z3,z4,z5,z6,z1136])],[(0,[z1,z28,z531,z4,z5,z6]),(0,[z0,z1,z8,z4,z5,z23]),(0,[z15,z1,z450,z3,z5,z6]),(0,[z1137,z1,z3,z4,z5,z6]),(0,[z1,z9,z56,z4,z5,z6]),(0,[z1,z146,z3,z4,z5,z23]),(0,[z379,z1,z3,z80,z5,z6]),(0,[z0,z1,z100,z3,z4,z6])],[(0,[z20,z1,z88,z3,z149,z6]),(0,[z15,z1,z3,z80,z61,z6]),(0,[z72,z1,z32,z4,z5,z6]),(0,[z0,z1,z1138,z4,z26,z5])],[(0,[z1,z28,z32,z4,z5,z6]),(0,[z1,z3,z260,z151,z5,z6]),(0,[z0,z1,z1139,z4,z5,z6]),(0,[z13,z1,z9,z4,z5,z91]),(0,[z0,z31,z3,z4,z26,z62]),(0,[z1140,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z193,z5,z23])],[(0,[z28,z3,z4,z5,z6,z337]),(0,[z0,z293,z32,z4,z5,z6]),(0,[z0,z1,z32,z4,z76,z5]),(0,[z0,z1,z3,z151,z85,z6])],[(0,[z1,z28,z3,z4,z149,z23]),(0,[z15,z1,z3,z62,z149,z6]),(0,[z1,z3,z29,z4,z269,z5]),(0,[z1141,z1,z3,z4,z5,z6]),(0,[z0,z9,z526,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z23]),(0,[z1,z3,z4,z5,z23,z1142])],[(0,[z0,z9,z453,z4,z5,z6]),(0,[z0,z1,z1143,z4,z5,z6]),(0,[z0,z32,z4,z5,z399,z6]),(0,[z36,z0,z9,z151,z5,z6]),(0,[z0,z1,z9,z4,z264,z6]),(0,[z0,z1,z3,z4,z1144,z5]),(0,[z1,z3,z4,z5,z6,z1145]),(0,[z105,z0,z1,z42,z27,z6])],[(0,[z0,z1,z107,z4,z5,z47])],[(0,[z20,z1,z3,z4,z5,z1016]),(0,[z0,z212,z87,z4,z5,z6]),(0,[z0,z1,z1008,z3,z4,z6]),(0,[z0,z1146,z3,z4,z5,z6]),(0,[z222,z900,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z33,z23]),(0,[z20,z1,z3,z4,z5,z1057]),(0,[z1147,z1,z3,z4,z5,z6]),(0,[z0,z31,z1076,z4,z5,z6]),(0,[z0,z1,z110,z9,z4,z26]),(0,[z0,z1,z1148,z4,z5,z6]),(0,[z0,z1,z3,z4,z667,z23])],[(0,[z1,z361,z29,z4,z5,z6]),(0,[z20,z97,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1149]),(0,[z248,z1,z3,z4,z445,z5]),(0,[z1150,z1,z3,z4,z5,z6])],[(0,[z199,z1,z3,z151,z5,z6]),(0,[z20,z330,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z586]),(0,[z15,z1,z9,z4,z26,z5]),(0,[z0,z1,z3,z4,z5,z1006]),(0,[z0,z3,z32,z4,z33,z23]),(0,[z0,z1,z3,z4,z462,z23]),(0,[z0,z1,z1151,z4,z5,z6]),(0,[z0,z1,z3,z61,z787,z6]),(0,[z0,z249,z3,z4,z5,z153])],[(0,[z20,z1,z287,z4,z5,z6]),(0,[z15,z1,z86,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z108]),(0,[z1,z3,z1152,z4,z5,z6]),(0,[z16,z1,z3,z4,z26,z114]),(0,[z63,z1,z3,z524,z5,z6]),(0,[z0,z1,z32,z1153,z5,z6]),(0,[z0,z212,z9,z4,z26,z5]),(0,[z1,z277,z3,z4,z26,z5]),(0,[z1154,z1,z3,z4,z5,z6]),(0,[z1155,z1,z3,z4,z5,z6]),(0,[z1,z3,z1156,z4,z5,z6])],[(0,[z31,z217,z3,z4,z5,z6]),(0,[z1,z218,z4,z242,z5,z6]),(0,[z0,z1,z9,z4,z5,z116]),(0,[z0,z48,z86,z152,z5,z6]),(0,[z0,z1,z65,z123,z26,z5])],[(0,[z248,z1,z28,z3,z4,z5]),(0,[z1,z138,z3,z67,z5,z6]),(0,[z1157,z1,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z198,z23]),(0,[z1,z3,z29,z4,z145,z23]),(0,[z0,z1,z3,z798,z5,z6]),(0,[z0,z289,z3,z152,z5,z6]),(0,[z1,z146,z70,z4,z5,z6])]],
   [[(0,[z40,z28,z3,z4,z5,z6]),(0,[z20,z517,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1158,z5]),(0,[z0,z1,z946,z4,z5,z6]),(0,[z0,z32,z4,z5,z6,z409]),(0,[z103,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z80,z61,z6]),(0,[z0,z1,z3,z4,z5,z1159]),(0,[z0,z1,z1160,z4,z5,z6]),(0,[z0,z1,z3,z142,z61,z6])],[(0,[z120,z1,z3,z4,z5,z6]),(0,[z77,z1,z3,z4,z5,z6]),(0,[z1,z28,z8,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z1161]),(0,[z15,z1,z3,z4,z5,z307]),(0,[z0,z1,z1162,z4,z5,z6]),(0,[z210,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z599,z619,z6]),(0,[z273,z0,z1,z3,z4,z465])],[(0,[z0,z1,z3,z4,z1163,z5]),(0,[z0,z1,z1164,z4,z5,z6]),(0,[z31,z32,z29,z4,z5,z6]),(0,[z0,z44,z3,z4,z5,z111])],[(0,[z0,z1,z3,z4,z530,z23]),(0,[z1,z28,z3,z193,z5,z6]),(0,[z0,z1,z3,z4,z1165,z5]),(0,[z1020,z1,z3,z4,z5,z6]),(0,[z1166,z1,z3,z4,z5,z6]),(0,[z1167,z1,z3,z4,z5,z6]),(0,[z1168,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z290,z43,z5])],[(0,[z102,z1,z3,z4,z127,z6]),(0,[z1,z87,z29,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z108]),(0,[z0,z1,z3,z4,z5,z586]),(0,[z69,z1,z9,z4,z5,z6])],[(0,[z20,z28,z3,z4,z5,z23]),(0,[z15,z1,z3,z80,z5,z6]),(0,[z0,z1,z287,z4,z5,z6])],[(0,[z657,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1169,z5]),(0,[z1,z9,z4,z220,z5,z6]),(0,[z448,z1,z3,z4,z5,z23]),(0,[z1170,z1,z3,z295,z5,z6]),(0,[z0,z1,z437,z4,z5,z23]),(0,[z0,z1,z3,z4,z1171,z5]),(0,[z0,z1,z3,z4,z5,z1172]),(0,[z0,z1,z3,z1173,z26,z5])],[(0,[z41,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z26,z5,z149]),(0,[z143,z1,z3,z4,z26,z5]),(0,[z0,z3,z152,z798,z5,z6]),(0,[z272,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z4,z5,z1174]),(0,[z0,z1,z3,z42,z5,z425])],[(0,[z1,z3,z29,z4,z5,z307]),(0,[z283,z1,z178,z4,z5,z6]),(0,[z0,z1,z4,z26,z5,z246])],[(0,[z0,z1,z3,z4,z5,z1161]),(0,[z15,z1,z202,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z1175]),(0,[z77,z1,z3,z4,z5,z410]),(0,[z0,z31,z3,z4,z62,z6]),(0,[z0,z1,z3,z4,z803,z198]),(0,[z1176,z1,z3,z4,z5,z6])],[(0,[z1010,z1,z28,z3,z4,z6]),(0,[z1,z3,z473,z524,z5,z6]),(0,[z0,z459,z9,z4,z5,z6]),(0,[z0,z1,z4,z5,z1177,z6]),(0,[z1,z1178,z3,z4,z5,z6]),(0,[z1179,z1,z3,z4,z5,z6])],[(0,[z28,z32,z4,z5,z33,z6]),(0,[z1180,z1,z3,z4,z5,z6]),(0,[z0,z1,z1181,z4,z5,z6]),(0,[z0,z1,z3,z4,z1182,z5]),(0,[z77,z1,z3,z413,z5,z6]),(0,[z0,z1,z817,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1183]),(0,[z0,z1,z1184,z3,z4,z6])],[(0,[z251,z217,z3,z4,z5,z6]),(0,[z570,z1,z34,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z91]),(0,[z120,z1,z32,z4,z5,z6]),(0,[z77,z1,z32,z4,z5,z6]),(0,[z1,z184,z3,z4,z26,z5]),(0,[z112,z0,z3,z4,z5,z82])],[(0,[z15,z1,z3,z587,z5,z6]),(0,[z0,z44,z32,z4,z5,z111]),(0,[z0,z1,z3,z1185,z5,z6]),(0,[z793,z1,z3,z42,z5,z6]),(0,[z46,z0,z1,z4,z5,z831])],[(0,[z0,z97,z32,z4,z5,z6]),(0,[z177,z1,z3,z4,z5,z55]),(0,[z857,z0,z1,z32,z4,z5]),(0,[z0,z1,z1186,z4,z5,z6]),(0,[z1187,z1,z3,z4,z5,z6])],[(0,[z112,z28,z3,z4,z5,z82]),(0,[z148,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z586])]],
   [[(0,[z0,z1,z361,z4,z5,z23]),(0,[z1188,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1189,z5,z6])],[(0,[z0,z1,z3,z4,z688,z23]),(0,[z0,z1,z325,z4,z318,z6])],[(0,[z20,z1,z3,z4,z17,z6]),(0,[z41,z1,z32,z4,z5,z6])],[(0,[z0,z1,z1190,z4,z5,z6]),(0,[z1191,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1192])],[(0,[z20,z32,z4,z5,z33,z6]),(0,[z0,z31,z32,z4,z62,z6]),(0,[z0,z1,z3,z1193,z5,z6]),(0,[z1194,z1,z3,z4,z5,z6]),(0,[z1015,z1,z3,z599,z5,z6]),(0,[z0,z1,z3,z80,z26,z61])],[(0,[z20,z1,z3,z4,z5,z23]),(0,[z1,z28,z437,z4,z5,z6]),(0,[z49,z1,z3,z4,z5,z424]),(0,[z1,z3,z4,z5,z54,z6]),(0,[z0,z1,z3,z4,z5,z1048]),(0,[z0,z1,z3,z413,z62,z6]),(0,[z297,z1,z3,z4,z26,z5])],[(0,[z3,z67,z4,z220,z5,z6]),(0,[z1195,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z376,z5,z6]),(0,[z0,z429,z32,z4,z5,z6]),(0,[z0,z1,z32,z4,z1182,z5]),(0,[z1196,z0,z3,z4,z5,z6]),(0,[z1,z1197,z3,z4,z5,z6])],[(0,[z13,z1,z32,z4,z5,z91]),(0,[z0,z1,z1047,z32,z5,z6]),(0,[z112,z0,z32,z4,z5,z82]),(0,[z0,z1,z1198,z32,z4,z6]),(1,[z0,z1,z3,z193,z23]),(0,[z1199,z1,z3,z4,z5,z6])],[(0,[z1200,z1,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z227]),(0,[z0,z1,z4,z5,z831,z175])],[(0,[z15,z1,z3,z4,z5,z346]),(0,[z0,z1,z3,z4,z1201,z6]),(0,[z0,z1,z3,z1202,z5,z6])],[(0,[z0,z1,z3,z1203,z5,z6]),(0,[z1,z3,z4,z1204,z5,z6]),(0,[z0,z1,z3,z4,z1205,z5]),(0,[z0,z1,z3,z4,z26,z348]),(0,[z1206,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z94,z5]),(0,[z1207,z1,z3,z4,z5,z6]),(0,[z15,z1,z543,z32,z5,z6]),(0,[z15,z1,z3,z4,z5,z309]),(0,[z1208,z1,z3,z4,z5,z6])],[(0,[z1,z32,z56,z4,z5,z6]),(0,[z0,z1,z3,z4,z1209,z6]),(0,[z488,z1,z3,z4,z5,z23])],[(0,[z1,z217,z3,z4,z26,z5]),(0,[z0,z690,z9,z4,z5,z6]),(0,[z105,z0,z1,z4,z27,z307]),(0,[z1,z3,z4,z5,z6,z1210])],[(0,[z1,z28,z3,z5,z6,z978]),(0,[z1,z3,z4,z220,z26,z5]),(0,[z13,z1,z3,z4,z5,z840]),(0,[z1063,z1,z3,z4,z5,z6])],[(0,[z1,z28,z361,z4,z5,z6]),(0,[z1,z482,z60,z4,z5,z6]),(0,[z38,z20,z1,z3,z5,z73]),(0,[z31,z252,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1211])]],
   [[(0,[z1,z3,z29,z4,z5,z346]),(0,[z0,z1,z3,z4,z26,z689]),(0,[z225,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z551,z5,z23]),(0,[z1,z3,z1212,z4,z5,z6])],[(0,[z1,z384,z3,z4,z5,z302]),(0,[z0,z1,z3,z4,z1213,z6]),(0,[z1,z32,z29,z4,z26,z5]),(0,[z0,z1,z32,z4,z5,z116]),(0,[z0,z1,z9,z1214,z5,z6]),(0,[z1,z3,z4,z26,z1215,z5])],[(0,[z0,z1,z1216,z4,z5,z6]),(0,[z20,z1,z70,z4,z5,z6]),(0,[z15,z1,z3,z422,z5,z6]),(0,[z1,z3,z29,z4,z5,z309]),(0,[z0,z1,z3,z4,z5,z1217]),(0,[z1218,z1,z3,z4,z5,z6])],[(0,[z199,z1,z3,z371,z5,z6]),(0,[z15,z1,z3,z5,z6,z288]),(0,[z1219,z1,z3,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z116]),(0,[z1,z3,z4,z5,z6,z1142]),(0,[z1220,z1,z3,z4,z5,z6])],[(0,[z1221,z1,z3,z4,z5,z6]),(0,[z21,z1,z34,z4,z5,z23]),(0,[z1,z3,z29,z391,z5,z6]),(0,[z15,z1,z4,z5,z246,z6]),(0,[z1,z9,z4,z5,z6,z160]),(0,[z0,z1,z3,z4,z5,z1222])],[(0,[z20,z1,z3,z4,z76,z5]),(0,[z20,z508,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z318,z6]),(0,[z1,z1223,z29,z4,z5,z6]),(0,[z1,z3,z1043,z599,z5,z6]),(0,[z1224,z1,z3,z4,z5,z6]),(0,[z708,z1,z3,z4,z5,z6])],[(0,[z1225,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1226]),(0,[z0,z1,z12,z3,z149,z6]),(0,[z1,z3,z1227,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z567]),(0,[z15,z212,z9,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z22]),(0,[z69,z1,z32,z4,z5,z6]),(0,[z0,z31,z3,z4,z622,z6])],[(0,[z1,z60,z4,z242,z5,z6]),(0,[z1,z3,z4,z5,z1009,z6]),(0,[z16,z1,z3,z4,z117,z6]),(0,[z1,z1056,z29,z4,z5,z6]),(0,[z1,z3,z68,z4,z5,z144]),(0,[z442,z1,z3,z4,z5,z22]),(0,[z225,z1,z3,z295,z5,z6])],[(0,[z1,z3,z67,z4,z26,z5]),(0,[z44,z217,z3,z4,z5,z6]),(0,[z0,z1,z194,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1228]),(0,[z0,z1,z3,z4,z678,z23])],[(0,[z15,z1,z325,z4,z5,z6]),(0,[z122,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z26,z264])],[(0,[z0,z1,z3,z1229,z5,z6]),(0,[z36,z20,z3,z151,z5,z6]),(0,[z1,z3,z29,z5,z6,z291]),(0,[z1,z3,z4,z1230,z5,z6]),(0,[z1,z3,z4,z5,z1231,z6]),(0,[z0,z1,z3,z1232,z26,z5])],[(0,[z1,z3,z29,z4,z318,z6]),(0,[z0,z1,z3,z92,z4,z23]),(0,[z1233,z1,z3,z4,z5,z6]),(0,[z0,z1,z107,z4,z5,z831]),(0,[z1234,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z76,z5]),(1,[z1,z3,z4,z5,z840]),(0,[z106,z1,z3,z42,z5,z6]),(0,[z1007,z1,z3,z4,z5,z6])],[(0,[z15,z1,z3,z473,z5,z6]),(0,[z1087,z1,z3,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z1040])],[(0,[z0,z1,z1070,z4,z5,z6]),(0,[z1,z28,z3,z551,z5,z6]),(0,[z541,z0,z1,z3,z4,z23]),(0,[z15,z1,z9,z5,z149,z6]),(0,[z0,z1,z3,z551,z5,z111]),(0,[z0,z1,z262,z3,z149,z6])]],
   [[(0,[z1,z3,z4,z1235,z5,z6]),(0,[z0,z1,z3,z4,z1236,z6]),(0,[z0,z1,z3,z1237,z4,z5]),(0,[z1238,z1,z3,z4,z5,z6])],[(0,[z1,z3,z29,z4,z1239,z5])],[(0,[z0,z1,z1240,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z512]),(0,[z90,z1,z32,z4,z5,z22]),(0,[z0,z1,z537,z4,z5,z571])],[(0,[z0,z1,z9,z4,z5,z1241]),(0,[z1,z252,z3,z4,z26,z5]),(0,[z0,z1,z3,z4,z428,z23]),(0,[z0,z1,z3,z1242,z5,z6])],[(0,[z48,z28,z3,z152,z5,z6]),(0,[z28,z3,z419,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1243]),(0,[z15,z1,z3,z5,z322,z6]),(0,[z1,z3,z29,z1134,z5,z6]),(0,[z0,z1,z4,z5,z6,z1244]),(0,[z1245,z1,z3,z4,z5,z6]),(0,[z1,z277,z9,z4,z5,z6]),(0,[z1,z1246,z3,z4,z5,z6]),(0,[z379,z1,z3,z5,z149,z6])],[(0,[z0,z1,z3,z4,z5,z1247]),(0,[z0,z1,z3,z1153,z5,z6]),(0,[z0,z1,z3,z295,z26,z5]),(0,[z0,z31,z437,z4,z62,z6])],[(0,[z0,z1,z3,z4,z1093,z6]),(0,[z1,z3,z4,z5,z144,z91]),(0,[z0,z1,z3,z4,z6,z1105]),(0,[z0,z670,z3,z152,z5,z6]),(0,[z105,z0,z1,z3,z42,z23]),(0,[z1248,z1,z3,z4,z5,z6]),(0,[z0,z1,z194,z4,z149,z23]),(0,[z1249,z1,z3,z4,z26,z5]),(0,[z1,z3,z4,z1215,z5,z6])],[(0,[z0,z1,z3,z4,z1250,z6]),(0,[z248,z0,z1,z3,z4,z791]),(0,[z112,z0,z3,z599,z5,z82])],[(0,[z103,z1,z3,z4,z5,z6]),(0,[z0,z1,z1223,z4,z5,z6]),(0,[z0,z1,z1251,z4,z5,z6]),(0,[z0,z32,z4,z5,z347,z6]),(0,[z0,z32,z4,z5,z6,z474]),(0,[z210,z1,z9,z4,z5,z6]),(0,[z78,z0,z537,z4,z33,z6])],[(0,[z1,z1252,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1101]),(0,[z306,z1,z2,z4,z5,z6]),(0,[z1,z3,z4,z445,z5,z23])],[(0,[z0,z1,z3,z4,z185,z5]),(0,[z0,z1,z3,z123,z149,z23]),(0,[z1,z1253,z3,z4,z5,z6])],[(0,[z20,z1,z3,z42,z5,z6]),(0,[z1,z3,z710,z4,z5,z6]),(0,[z1,z3,z29,z5,z322,z6]),(0,[z0,z1,z3,z4,z1254,z5]),(0,[z540,z0,z1,z4,z5,z74]),(0,[z105,z0,z1,z9,z4,z23])],[(0,[z1255,z1,z3,z4,z5,z6]),(0,[z0,z1,z1256,z4,z26,z5])],[(0,[z20,z44,z3,z4,z5,z111]),(0,[z15,z1,z3,z4,z5,z1257]),(0,[z1258,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z787,z6]),(0,[z0,z1,z4,z26,z1259,z5])],[(0,[z44,z28,z3,z4,z5,z111]),(0,[z0,z1,z3,z1260,z5,z6]),(0,[z143,z1,z9,z4,z5,z6]),(0,[z272,z1,z9,z4,z5,z6]),(0,[z0,z1,z1261,z4,z5,z6]),(0,[z1262,z1,z3,z4,z5,z6]),(0,[z0,z1,z511,z4,z5,z23]),(0,[z1,z3,z4,z26,z5,z457])],[(0,[z284,z1,z34,z4,z5,z6]),(0,[z15,z48,z3,z152,z5,z6]),(0,[z46,z1,z29,z4,z5,z175]),(0,[z0,z1,z1076,z4,z5,z6]),(0,[z1245,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z4,z269,z5]),(0,[z165,z0,z1,z3,z4,z23]),(0,[z46,z0,z1,z4,z5,z74]),(0,[z0,z1,z3,z4,z85,z166]),(0,[z1263,z1,z3,z4,z5,z6])]],
   [[(0,[z112,z28,z32,z4,z5,z6]),(0,[z0,z1099,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z803,z6])],[(0,[z15,z1,z80,z32,z5,z6]),(0,[z0,z1,z9,z5,z322,z6]),(0,[z0,z32,z4,z5,z6,z481])],[(0,[z1,z3,z4,z5,z6,z1264]),(0,[z20,z7,z202,z4,z5,z6]),(0,[z0,z1,z3,z4,z1265,z6]),(0,[z0,z1,z3,z4,z185,z619])],[(0,[z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1104]),(0,[z1,z184,z9,z4,z5,z6]),(0,[z0,z1,z325,z4,z26,z5]),(0,[z0,z1,z3,z42,z5,z6]),(0,[z0,z1,z194,z193,z5,z6]),(0,[z1266,z1,z3,z4,z5,z6]),(0,[z1267,z1,z3,z4,z5,z6])],[(0,[z20,z31,z3,z4,z62,z6]),(0,[z16,z1,z3,z4,z169,z6]),(0,[z0,z1,z3,z4,z1268,z5]),(0,[z0,z1,z3,z4,z85,z37]),(0,[z283,z1,z3,z4,z26,z5]),(0,[z379,z1,z3,z4,z26,z5]),(0,[z105,z103,z1,z3,z4,z23]),(0,[z0,z1,z134,z4,z95,z23]),(0,[z0,z1,z3,z4,z320,z23])],[(0,[z1,z1269,z3,z4,z5,z6]),(0,[z112,z15,z3,z4,z5,z82]),(0,[z0,z1,z32,z4,z185,z5])],[(0,[z20,z429,z3,z4,z5,z6]),(0,[z1,z9,z29,z4,z5,z6]),(0,[z38,z0,z1,z3,z5,z73])],[(0,[z15,z1,z3,z5,z149,z6]),(0,[z554,z0,z3,z4,z33,z6]),(0,[z0,z1,z3,z4,z17,z37]),(0,[z0,z1,z3,z4,z494,z23]),(0,[z0,z31,z3,z4,z62,z567]),(0,[z1270,z1,z3,z4,z5,z6])],[(0,[z1271,z1,z3,z4,z5,z6]),(0,[z59,z1,z2,z4,z5,z6]),(0,[z0,z1,z3,z1272,z5,z6]),(0,[z0,z1,z3,z599,z5,z23]),(0,[z0,z44,z1,z3,z4,z388]),(0,[z1,z3,z4,z5,z23,z1273])],[(0,[z0,z1,z3,z4,z206,z23]),(0,[z1,z3,z1274,z4,z5,z6]),(0,[z0,z1,z3,z4,z388,z23]),(0,[z1275,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z23,z1244])],[(0,[z0,z1,z3,z4,z1276,z6]),(0,[z15,z1,z3,z4,z26,z23]),(0,[z1,z3,z1277,z4,z5,z6]),(0,[z0,z1,z1278,z4,z5,z6]),(0,[z0,z1,z1279,z4,z5,z6]),(0,[z1280,z1,z3,z4,z5,z6]),(0,[z440,z0,z1,z4,z5,z328])],[(0,[z297,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z465])],[(0,[z1,z28,z511,z4,z5,z6]),(0,[z28,z3,z453,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1281]),(0,[z1170,z1,z3,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z200]),(0,[z0,z1,z977,z3,z4,z6]),(0,[z0,z1,z9,z4,z5,z108]),(0,[z1282,z1,z3,z4,z5,z6]),(0,[z0,z1,z65,z123,z5,z6]),(0,[z1283,z1,z3,z4,z26,z5])],[(0,[z20,z1,z110,z3,z4,z26]),(0,[z15,z1,z3,z369,z5,z6]),(0,[z1,z3,z4,z5,z6,z840]),(0,[z119,z1,z32,z4,z5,z6]),(0,[z1,z32,z4,z5,z6,z160]),(0,[z0,z1,z32,z42,z5,z6]),(0,[z0,z579,z32,z4,z5,z6]),(0,[z0,z1,z3,z152,z5,z37]),(0,[z0,z1,z110,z3,z4,z185]),(0,[z1284,z1,z3,z4,z5,z6]),(0,[z0,z222,z3,z4,z5,z23])],[(0,[z0,z1,z3,z5,z6,z1285]),(0,[z1,z3,z4,z1286,z5,z6])]],
   [[(0,[z210,z1,z3,z4,z5,z6]),(0,[z21,z1,z710,z4,z5,z6]),(0,[z1,z217,z3,z5,z149,z6]),(0,[z1,z3,z29,z5,z6,z356]),(0,[z0,z9,z32,z4,z5,z23]),(0,[z0,z1,z3,z4,z684,z23])],[(0,[z20,z1,z3,z4,z5,z116]),(0,[z15,z1,z3,z161,z5,z23]),(0,[z0,z1,z1287,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z307]),(0,[z0,z1,z3,z4,z626,z23]),(0,[z1,z3,z4,z5,z6,z1288]),(0,[z1289,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1290])],[(0,[z244,z1,z3,z4,z436,z6]),(0,[z15,z1,z32,z5,z149,z6]),(0,[z0,z1,z3,z4,z117,z23]),(0,[z0,z1128,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z26,z23]),(0,[z0,z1,z1291,z4,z5,z6]),(0,[z554,z0,z32,z4,z33,z6]),(0,[z36,z0,z3,z151,z5,z6]),(0,[z112,z0,z3,z551,z5,z82]),(0,[z103,z1,z3,z193,z5,z6]),(0,[z0,z1,z3,z4,z1292,z5]),(0,[z0,z1,z3,z4,z264,z6])],[(0,[z20,z1,z3,z80,z61,z6]),(0,[z0,z1,z3,z80,z127,z6])],[(0,[z1,z9,z67,z4,z5,z6]),(0,[z1,z217,z9,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z227]),(0,[z1,z194,z29,z4,z5,z6]),(0,[z1,z3,z524,z5,z114,z6]),(0,[z1293,z1,z3,z4,z5,z6]),(0,[z0,z1,z80,z32,z61,z6]),(0,[z1,z9,z1294,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1295]),(0,[z0,z1,z1296,z4,z5,z6])],[(0,[z36,z28,z3,z151,z5,z6]),(0,[z380,z3,z29,z4,z5,z6]),(0,[z0,z32,z4,z33,z6,z23]),(0,[z0,z1,z3,z1173,z5,z6]),(0,[z283,z1,z3,z4,z318,z6]),(0,[z0,z1,z817,z65,z5,z6]),(0,[z105,z106,z1,z3,z4,z23]),(0,[z72,z1,z3,z4,z157,z5])],[(0,[z143,z1,z3,z4,z5,z6]),(0,[z272,z1,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z157,z5]),(0,[z0,z1,z3,z4,z1297,z5]),(0,[z0,z1,z110,z3,z4,z26])],[(0,[z1,z28,z3,z599,z5,z6]),(0,[z15,z1,z3,z4,z26,z5]),(0,[z225,z1,z9,z4,z5,z6]),(0,[z0,z1,z110,z194,z4,z6])],[(0,[z1,z28,z3,z4,z388,z6]),(0,[z20,z1,z87,z4,z5,z6]),(0,[z0,z1,z3,z1298,z5,z6]),(0,[z331,z0,z1,z4,z5,z84]),(0,[z0,z48,z3,z152,z26,z5])],[(0,[z1,z28,z3,z4,z5,z37]),(0,[z1,z3,z56,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z116])],[(0,[z1,z28,z9,z4,z5,z23]),(0,[z0,z1299,z3,z4,z5,z6]),(0,[z1300,z1,z3,z4,z5,z6]),(0,[z1301,z1,z3,z4,z5,z6]),(0,[z283,z1,z325,z4,z5,z6])],[(0,[z210,z1,z32,z4,z5,z6]),(0,[z0,z1,z401,z4,z26,z5]),(0,[z1302,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z80,z61,z6]),(0,[z0,z1,z3,z4,z137,z23]),(0,[z988,z1,z3,z4,z5,z23])],[(0,[z239,z1,z630,z4,z5,z6]),(0,[z0,z31,z32,z4,z33,z6]),(0,[z46,z0,z1,z4,z332,z5]),(0,[z0,z1,z1088,z4,z5,z23])],[(0,[z1303,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z29,z5,z23]),(0,[z248,z1,z3,z29,z4,z5]),(0,[z1304,z1,z3,z4,z5,z6]),(0,[z36,z0,z32,z151,z5,z6]),(0,[z0,z1,z32,z4,z264,z6]),(0,[z0,z1,z3,z4,z85,z23]),(0,[z0,z1,z3,z4,z738,z17]),(0,[z0,z1,z3,z4,z1305,z6]),(0,[z248,z122,z1,z3,z4,z5]),(0,[z0,z1,z3,z413,z33,z6]),(0,[z1306,z1,z3,z4,z5,z6])],[(0,[z1,z3,z29,z4,z26,z5]),(0,[z24,z0,z1,z136,z26,z5]),(1,[z0,z1,z3,z787,z6])],[(0,[z0,z1,z133,z4,z5,z23]),(0,[z69,z1,z3,z4,z5,z6]),(0,[z0,z1,z1307,z4,z5,z6]),(0,[z15,z1,z3,z295,z5,z6]),(0,[z272,z31,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z619,z23]),(0,[z0,z380,z3,z4,z5,z23]),(0,[z72,z1,z3,z4,z61,z23]),(0,[z0,z1,z3,z1308,z5,z6])]],
   [[(0,[z1,z28,z3,z4,z61,z23]),(0,[z1,z3,z260,z152,z5,z6]),(0,[z0,z1,z87,z4,z5,z6]),(0,[z0,z1,z1309,z4,z5,z6])],[(0,[z1,z3,z4,z1310,z5,z6]),(0,[z143,z1,z32,z4,z5,z6]),(0,[z272,z1,z32,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z227]),(0,[z0,z1,z3,z152,z85,z6])],[(0,[z15,z1,z32,z4,z26,z5]),(0,[z0,z1,z32,z4,z269,z5]),(0,[z1,z1311,z3,z4,z5,z6]),(0,[z1312,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1313])],[(0,[z0,z1,z1314,z4,z5,z6]),(0,[z234,z28,z3,z4,z5,z6]),(0,[z20,z1,z194,z4,z5,z6]),(0,[z0,z1,z9,z4,z26,z5]),(0,[z0,z32,z4,z5,z529,z6]),(0,[z1315,z1,z3,z4,z5,z6]),(0,[z1,z1316,z3,z4,z5,z6]),(0,[z0,z1,z194,z4,z6,z23])],[(0,[z0,z1,z3,z4,z1317,z5]),(0,[z251,z1,z3,z4,z5,z23]),(0,[z1,z581,z3,z29,z5,z6]),(0,[z0,z522,z32,z4,z5,z6]),(0,[z0,z1,z86,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1318]),(0,[z0,z1,z3,z4,z5,z108])],[(0,[z257,z1,z34,z4,z5,z6]),(0,[z63,z1,z3,z4,z550,z6]),(0,[z1,z3,z29,z295,z5,z6]),(0,[z1,z184,z32,z4,z5,z6]),(0,[z0,z44,z511,z4,z5,z111])],[(0,[z51,z0,z32,z4,z26,z5]),(0,[z0,z1,z9,z134,z4,z23]),(0,[z0,z1,z3,z4,z318,z82]),(0,[z0,z1,z3,z4,z1319,z6]),(0,[z0,z1,z3,z4,z75,z23]),(0,[z623,z1,z3,z4,z5,z23]),(0,[z0,z1,z1320,z4,z5,z6])],[(0,[z199,z1,z3,z152,z5,z6]),(0,[z1,z3,z4,z1321,z5,z6]),(0,[z0,z1,z3,z4,z1055,z6]),(0,[z1,z3,z29,z4,z5,z1322]),(0,[z0,z1,z1323,z4,z5,z6])],[(0,[z20,z1,z202,z4,z5,z6]),(0,[z78,z3,z29,z4,z33,z6]),(0,[z0,z1,z9,z4,z5,z346]),(0,[z36,z248,z0,z3,z151,z5]),(0,[z112,z0,z3,z4,z58,z5]),(0,[z103,z222,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z307]),(0,[z1,z1098,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z425]),(0,[z1,z252,z9,z4,z5,z6]),(0,[z0,z1,z1324,z4,z5,z6])],[(0,[z20,z416,z3,z4,z5,z6]),(0,[z59,z1,z453,z4,z5,z6]),(0,[z63,z1,z3,z4,z26,z64]),(0,[z0,z1,z9,z4,z5,z309]),(0,[z41,z1,z511,z4,z5,z6]),(0,[z1325,z1,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z85,z6]),(0,[z0,z1,z9,z295,z5,z6]),(0,[z120,z1,z3,z4,z5,z166]),(0,[z248,z0,z1,z3,z71,z5])],[(0,[z1,z3,z4,z220,z5,z6]),(0,[z15,z1,z3,z154,z5,z6]),(0,[z217,z3,z32,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z1326]),(0,[z0,z1,z3,z4,z254,z318]),(0,[z0,z1327,z3,z4,z5,z6])],[(0,[z1,z28,z133,z4,z5,z6]),(0,[z1,z28,z3,z4,z619,z6]),(0,[z1328,z1,z3,z4,z5,z6]),(0,[z1329,z1,z3,z4,z5,z6]),(0,[z78,z0,z3,z4,z33,z23]),(0,[z0,z3,z4,z5,z718,z82]),(0,[z1,z1330,z3,z4,z5,z6])],[(0,[z15,z1,z3,z4,z62,z23]),(0,[z297,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z1331,z4,z5]),(0,[z105,z103,z1,z4,z27,z6]),(0,[z1,z3,z4,z467,z5,z108]),(0,[z1,z3,z71,z5,z186,z160]),(0,[z1,z3,z4,z5,z6,z1332]),(0,[z0,z1,z1333,z4,z26,z5])]],
   [[(0,[z105,z20,z1,z3,z4,z23]),(0,[z20,z705,z3,z4,z5,z6]),(0,[z1,z32,z29,z4,z5,z6]),(0,[z15,z1,z3,z1134,z5,z6]),(0,[z0,z1,z32,z4,z5,z108]),(0,[z0,z1,z287,z4,z5,z166]),(0,[z0,z1,z537,z4,z5,z23]),(0,[z0,z1,z1334,z4,z5,z6])],[(0,[z0,z1,z202,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z425]),(0,[z120,z1,z3,z4,z5,z37]),(0,[z0,z1,z3,z4,z185,z23]),(0,[z0,z1,z3,z4,z61,z309])],[],[(0,[z0,z1,z1335,z4,z5,z6]),(0,[z1,z32,z4,z220,z5,z6]),(0,[z1336,z1,z3,z4,z5,z6]),(0,[z1337,z1,z3,z4,z5,z6]),(0,[z297,z1,z3,z71,z5,z186])],[(0,[z0,z1,z3,z4,z5,z1338]),(0,[z1,z3,z29,z413,z5,z6]),(0,[z1,z3,z4,z180,z114,z6]),(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z1,z32,z4,z5,z307]),(0,[z0,z1,z110,z3,z4,z307]),(0,[z0,z1,z3,z71,z5,z368])],[(0,[z20,z1,z3,z4,z185,z5]),(0,[z1,z65,z29,z123,z5,z6]),(0,[z1,z3,z4,z64,z722,z6]),(0,[z0,z1,z9,z4,z318,z6]),(0,[z36,z120,z3,z151,z5,z6]),(0,[z0,z1,z287,z4,z5,z37]),(0,[z1,z3,z4,z5,z6,z1273])],[(0,[z0,z1,z3,z4,z5,z1339]),(0,[z0,z1,z1340,z4,z5,z6]),(0,[z0,z1,z1341,z4,z5,z6]),(0,[z1,z3,z29,z4,z62,z23]),(0,[z148,z1,z88,z3,z149,z6]),(0,[z0,z1,z125,z3,z4,z23])],[(0,[z1,z28,z3,z4,z5,z571]),(0,[z199,z1,z3,z161,z5,z6]),(0,[z15,z1,z3,z5,z6,z491]),(0,[z0,z1,z3,z524,z5,z23]),(0,[z0,z1,z9,z4,z5,z425]),(0,[z225,z1,z3,z4,z5,z410]),(0,[z0,z1,z3,z4,z5,z1342]),(0,[z0,z1343,z3,z4,z5,z6]),(0,[z545,z1,z3,z4,z109,z5])],[(0,[z31,z28,z3,z4,z62,z6]),(0,[z21,z1,z203,z4,z5,z6]),(0,[z1344,z1,z9,z4,z5,z6])],[(0,[z0,z1,z3,z766,z4,z5]),(0,[z0,z1345,z3,z4,z5,z6]),(0,[z225,z1,z3,z413,z5,z6]),(0,[z0,z1,z3,z4,z645,z23]),(0,[z0,z1,z3,z4,z5,z831])],[(1,[z1,z710,z4,z5,z6]),(0,[z15,z1,z3,z443,z5,z6]),(0,[z15,z1,z3,z4,z6,z465]),(0,[z225,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z1232,z5,z6]),(0,[z103,z380,z3,z4,z5,z6])],[(0,[z20,z1,z178,z4,z5,z6]),(0,[z283,z1,z9,z4,z5,z6]),(0,[z379,z1,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z917,z85])],[(0,[z0,z1,z3,z1214,z5,z6])],[(0,[z89,z217,z3,z4,z5,z6]),(0,[z15,z1,z3,z80,z117,z6]),(0,[z15,z1,z1346,z4,z5,z6]),(0,[z0,z92,z32,z4,z33,z6]),(0,[z0,z1,z3,z696,z4,z23]),(0,[z0,z1,z522,z3,z5,z73])],[(0,[z1,z32,z67,z4,z5,z6]),(0,[z257,z1,z355,z4,z5,z6]),(0,[z0,z1,z710,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z1347]),(0,[z0,z416,z32,z4,z5,z6]),(0,[z0,z1348,z3,z4,z5,z6]),(0,[z1349,z1,z3,z4,z5,z6])],[(0,[z89,z28,z133,z4,z5,z6]),(0,[z1,z28,z537,z4,z5,z6]),(0,[z28,z3,z433,z4,z5,z6]),(0,[z199,z1,z3,z5,z186,z6]),(0,[z1,z28,z134,z3,z4,z23]),(0,[z20,z1,z3,z4,z1268,z5]),(0,[z15,z1,z5,z246,z149,z6])]],
   [[(0,[z1,z3,z4,z5,z6,z1350]),(0,[z1,z3,z4,z5,z6,z1351]),(0,[z1352,z1,z3,z4,z5,z6]),(0,[z105,z106,z1,z4,z27,z6]),(0,[z440,z0,z1,z134,z4,z23]),(0,[z0,z1,z262,z3,z5,z73])],[(0,[z0,z1,z3,z4,z5,z914]),(0,[z1,z3,z29,z4,z6,z465]),(0,[z0,z1,z3,z4,z5,z346])],[(0,[z1,z252,z3,z4,z5,z6]),(0,[z272,z1,z437,z4,z5,z6]),(0,[z0,z1,z3,z4,z826,z6])],[(0,[z89,z28,z3,z4,z5,z23]),(0,[z199,z1,z3,z29,z5,z6]),(0,[z20,z495,z3,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z333]),(0,[z0,z1,z879,z32,z5,z6]),(0,[z0,z1,z178,z4,z5,z6]),(0,[z0,z44,z3,z4,z5,z153]),(0,[z0,z1,z3,z4,z5,z309])],[(0,[z20,z1,z4,z5,z246,z6]),(0,[z0,z1,z32,z766,z4,z5]),(0,[z120,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z26,z619]),(0,[z0,z1,z88,z3,z149,z23]),(0,[z0,z1,z3,z4,z366,z23])],[(0,[z1,z3,z4,z5,z1353,z6]),(0,[z1354,z1,z3,z4,z5,z6]),(0,[z15,z1,z401,z4,z5,z6]),(0,[z15,z1,z327,z4,z5,z6]),(0,[z0,z31,z32,z4,z26,z5]),(0,[z0,z1,z3,z4,z17,z166]),(0,[z0,z3,z798,z151,z5,z6]),(0,[z1355,z1,z3,z4,z5,z6]),(0,[z0,z1,z1356,z3,z4,z6]),(0,[z0,z380,z3,z42,z5,z6]),(0,[z0,z1,z1138,z4,z5,z6])],[(0,[z1,z28,z3,z524,z5,z6]),(0,[z20,z1,z3,z4,z5,z1241]),(0,[z20,z499,z3,z4,z5,z6]),(0,[z24,z20,z1,z136,z5,z6]),(0,[z1,z595,z60,z4,z5,z6]),(0,[z0,z1,z3,z26,z5,z322]),(0,[z0,z1,z3,z413,z26,z5]),(0,[z0,z1,z178,z551,z5,z6]),(0,[z105,z0,z1,z4,z27,z425]),(0,[z105,z0,z1,z4,z26,z27]),(0,[z1357,z1,z3,z4,z5,z6])],[(0,[z28,z32,z4,z151,z5,z6]),(0,[z20,z212,z9,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1358]),(0,[z51,z69,z32,z4,z5,z6]),(0,[z0,z32,z4,z26,z5,z33]),(0,[z96,z1,z140,z4,z5,z6]),(0,[z78,z0,z3,z4,z26,z33]),(0,[z0,z1,z3,z4,z43,z23])],[(0,[z293,z28,z3,z4,z5,z6]),(0,[z20,z1,z65,z123,z5,z6]),(0,[z0,z1,z3,z4,z5,z1359]),(0,[z0,z1,z287,z4,z85,z6]),(0,[z0,z1,z136,z193,z5,z6]),(0,[z0,z1,z1360,z4,z5,z6])],[(0,[z251,z1,z3,z260,z5,z6])],[(0,[z1361,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1362]),(0,[z38,z0,z1,z3,z5,z719])],[(0,[z135,z1,z203,z4,z5,z6]),(0,[z36,z15,z3,z151,z5,z6]),(0,[z1,z3,z4,z5,z6,z160]),(0,[z1,z3,z29,z4,z5,z823]),(0,[z0,z1,z1363,z4,z5,z6]),(0,[z128,z1,z3,z4,z26,z5]),(0,[z0,z1,z287,z4,z17,z6]),(0,[z0,z1,z1256,z4,z5,z6]),(0,[z1,z3,z4,z5,z1364,z6]),(0,[z0,z1,z3,z149,z368,z23])],[(0,[z1,z86,z29,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z346]),(0,[z0,z1,z3,z295,z5,z410]),(0,[z0,z1,z4,z5,z246,z6]),(0,[z0,z1,z118,z3,z149,z6])],[(0,[z199,z38,z1,z3,z5,z6]),(0,[z20,z1,z3,z4,z264,z6]),(0,[z1,z252,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1365]),(0,[z1366,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z6]),(0,[z0,z1,z3,z4,z149,z567]),(0,[z0,z1,z3,z1367,z5,z6])],[(0,[z222,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1241]),(0,[z0,z1,z3,z5,z1368,z6]),(0,[z15,z1,z9,z4,z5,z6]),(0,[z15,z1,z3,z149,z6,z23]),(0,[z0,z1,z32,z4,z5,z309]),(0,[z0,z1,z287,z4,z5,z23]),(0,[z0,z1,z3,z4,z1369,z5]),(0,[z0,z222,z660,z4,z5,z6]),(0,[z0,z1,z110,z3,z193,z6]),(0,[z640,z1,z3,z4,z5,z23]),(0,[z0,z1,z125,z4,z5,z47])],[(0,[z212,z28,z9,z4,z5,z6]),(0,[z28,z3,z526,z4,z5,z6]),(0,[z1,z277,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1370]),(0,[z544,z1,z3,z4,z5,z200]),(0,[z15,z1,z3,z604,z5,z6]),(0,[z1,z29,z4,z5,z246,z6]),(0,[z0,z212,z9,z4,z5,z6]),(0,[z0,z48,z9,z152,z5,z6]),(0,[z0,z1,z3,z4,z5,z774]),(0,[z77,z1,z3,z4,z5,z571]),(0,[z0,z1,z136,z194,z5,z6]),(0,[z913,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z28,z107,z4,z5,z47]),(0,[z20,z7,z3,z4,z26,z5]),(0,[z1371,z1,z3,z4,z5,z6]),(0,[z0,z1,z1372,z4,z5,z6]),(0,[z0,z1,z1066,z4,z5,z23])],[(0,[z1,z287,z29,z4,z5,z6]),(0,[z0,z1,z3,z1373,z5,z6]),(0,[z1374,z1,z3,z4,z5,z6]),(0,[z1375,z1,z9,z4,z5,z6]),(0,[z225,z1,z327,z4,z5,z6]),(0,[z0,z3,z4,z62,z33,z23]),(0,[z112,z0,z3,z4,z619,z82]),(0,[z0,z1,z3,z4,z1376,z5]),(0,[z0,z1,z3,z4,z693,z23])],[(0,[z20,z1,z3,z4,z269,z5]),(0,[z0,z1,z3,z4,z1239,z5]),(0,[z0,z1,z325,z4,z5,z6]),(0,[z0,z613,z32,z4,z5,z6]),(0,[z0,z1,z1377,z4,z5,z6]),(0,[z1,z3,z4,z5,z160,z23]),(0,[z1176,z1,z3,z4,z5,z23])],[(0,[z1,z28,z88,z3,z149,z6]),(0,[z20,z1,z3,z1298,z5,z6]),(0,[z379,z1,z3,z4,z5,z6]),(0,[z1378,z0,z1,z3,z4,z5])],[(0,[z28,z3,z4,z5,z533,z6]),(0,[z20,z1,z3,z5,z322,z6]),(0,[z0,z1,z8,z4,z26,z5]),(0,[z0,z1,z3,z4,z1379,z5])],[(0,[z0,z1,z3,z4,z510,z23]),(0,[z0,z1,z3,z4,z5,z1380]),(0,[z1381,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z564,z23]),(0,[z1,z3,z4,z5,z1382,z6]),(0,[z1,z4,z5,z246,z54,z6])],[(0,[z59,z1,z60,z4,z26,z5]),(0,[z210,z1,z3,z551,z5,z6]),(0,[z106,z1,z3,z4,z5,z307]),(0,[z0,z1,z1383,z4,z5,z6])],[(0,[z1,z28,z3,z4,z5,z166]),(0,[z1,z3,z29,z4,z851,z6]),(0,[z16,z1,z3,z4,z114,z23]),(0,[z105,z0,z1,z3,z4,z23])],[(0,[z217,z3,z4,z5,z33,z6]),(0,[z1,z3,z4,z1384,z5,z6]),(0,[z0,z1,z32,z4,z318,z6]),(0,[z0,z1,z32,z4,z5,z1365]),(0,[z1,z277,z531,z4,z5,z6]),(0,[z0,z1,z3,z4,z121,z23]),(0,[z148,z1,z3,z4,z5,z23])],[(0,[z0,z1,z1385,z4,z5,z6]),(0,[z1,z1386,z3,z4,z5,z6]),(0,[z1387,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z571])],[(0,[z1,z28,z3,z4,z1163,z5]),(0,[z15,z1,z737,z4,z5,z6]),(0,[z1,z3,z4,z1388,z5,z6]),(0,[z1,z277,z32,z4,z5,z6]),(0,[z0,z212,z736,z4,z5,z6]),(0,[z0,z1,z660,z9,z4,z23]),(0,[z0,z1,z3,z4,z269,z5]),(1,[z0,z1,z3,z4,z746]),(0,[z0,z1,z3,z4,z5,z1389]),(0,[z0,z1,z136,z5,z593,z6]),(0,[z1225,z222,z3,z4,z5,z6])],[(0,[z105,z20,z1,z4,z27,z6]),(0,[z0,z1,z9,z4,z26,z23])],[(0,[z0,z1,z3,z4,z5,z1390]),(0,[z217,z3,z4,z5,z6,z82]),(0,[z0,z1,z3,z5,z322,z6]),(0,[z30,z0,z1,z3,z149,z23]),(0,[z1374,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z130,z23]),(0,[z1283,z1,z3,z4,z5,z6])],[(0,[z1,z28,z287,z4,z5,z6]),(0,[z0,z1,z3,z1391,z5,z6]),(0,[z15,z1,z3,z460,z5,z6]),(0,[z0,z327,z4,z5,z33,z6]),(0,[z0,z1,z3,z5,z787,z6]),(0,[z827,z1,z3,z4,z26,z5])],[(0,[z1,z28,z3,z4,z1169,z5]),(0,[z1,z184,z3,z4,z5,z6]),(0,[z1,z3,z80,z29,z61,z6]),(0,[z51,z0,z736,z4,z5,z6]),(0,[z379,z1,z32,z4,z5,z6]),(0,[z0,z1,z327,z4,z26,z5])],[(0,[z1,z1392,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z198,z23]),(0,[z1,z3,z260,z4,z5,z23]),(0,[z20,z1,z9,z4,z26,z5]),(0,[z78,z0,z3,z4,z751,z6]),(0,[z0,z1,z3,z4,z1393,z6]),(0,[z1394,z1,z3,z4,z5,z6]),(0,[z0,z222,z136,z4,z5,z6]),(0,[z0,z1,z3,z4,z1395,z6])]],
   [[(0,[z20,z1,z86,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z108]),(0,[z1,z3,z1134,z161,z5,z6])],[(0,[z15,z1,z3,z687,z5,z6]),(0,[z0,z1,z3,z524,z5,z586]),(0,[z279,z0,z32,z4,z5,z6])],[(0,[z757,z0,z1,z3,z5,z6]),(0,[z15,z46,z1,z4,z5,z175]),(0,[z143,z1,z531,z4,z5,z6]),(0,[z0,z380,z87,z4,z5,z6]),(0,[z0,z1,z3,z604,z61,z6])],[(0,[z59,z1,z228,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z23]),(0,[z0,z1,z3,z4,z5,z1396]),(0,[z0,z1,z3,z4,z17,z23]),(0,[z1,z1397,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z307]),(0,[z0,z589,z32,z4,z5,z6]),(0,[z0,z1,z1398,z4,z5,z6]),(0,[z1399,z1,z3,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z457]),(0,[z112,z0,z3,z4,z5,z718]),(0,[z1400,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1257]),(0,[z0,z32,z4,z5,z33,z23])],[(0,[z15,z1,z3,z4,z5,z6]),(0,[z0,z572,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1401]),(0,[z0,z1,z327,z295,z5,z6]),(0,[z0,z1,z828,z4,z5,z6])],[(0,[z20,z28,z3,z4,z26,z5]),(0,[z199,z1,z3,z4,z5,z23]),(0,[z1,z1402,z3,z4,z5,z6]),(0,[z297,z1,z3,z4,z5,z6]),(0,[z0,z1,z32,z5,z322,z6]),(0,[z1,z3,z4,z5,z22,z840]),(1,[z0,z736,z4,z5,z6]),(0,[z0,z48,z3,z152,z5,z6]),(0,[z1403,z1,z3,z4,z5,z6]),(0,[z122,z1,z3,z4,z269,z5]),(0,[z0,z1404,z3,z4,z5,z6])],[(0,[z7,z3,z4,z220,z5,z6]),(0,[z1405,z1,z3,z4,z5,z6])],[(0,[z1375,z1,z3,z4,z5,z6]),(0,[z0,z1,z1406,z4,z5,z6]),(0,[z106,z1,z3,z4,z26,z5])],[(0,[z1407,z1,z3,z4,z5,z6]),(0,[z1315,z1,z3,z551,z5,z6]),(0,[z0,z1,z162,z3,z4,z26])],[(0,[z273,z0,z1,z3,z4,z23])],[(0,[z0,z1,z717,z4,z5,z6]),(0,[z280,z0,z3,z4,z33,z6]),(0,[z0,z1,z3,z4,z276,z23]),(0,[z859,z1,z3,z4,z26,z5])],[(0,[z1,z3,z29,z4,z5,z6]),(0,[z15,z1,z778,z4,z5,z6]),(0,[z0,z1,z1408,z4,z5,z6]),(0,[z554,z0,z1,z3,z4,z23]),(0,[z24,z0,z1,z136,z5,z6]),(0,[z1,z3,z4,z1409,z5,z6]),(0,[z1,z1410,z3,z4,z5,z6])],[(0,[z38,z1,z28,z3,z5,z73]),(0,[z15,z1,z3,z4,z5,z410]),(0,[z119,z1,z3,z4,z5,z166]),(0,[z1,z252,z437,z4,z5,z6]),(0,[z0,z1,z178,z599,z5,z6]),(0,[z0,z1,z3,z4,z5,z1411]),(0,[z0,z1,z1412,z4,z5,z6])],[(0,[z1,z217,z3,z4,z5,z6]),(0,[z15,z31,z32,z4,z5,z6]),(0,[z24,z0,z1,z343,z5,z6]),(0,[z0,z1,z3,z695,z5,z186]),(0,[z0,z1,z3,z71,z5,z719]),(0,[z0,z1,z1413,z4,z5,z6]),(0,[z182,z1,z3,z4,z5,z452])]],
   [[(0,[z15,z1,z3,z413,z5,z6]),(0,[z0,z48,z531,z152,z5,z6]),(0,[z214,z0,z1,z3,z4,z23])],[(0,[z15,z1,z32,z4,z5,z6]),(0,[z1,z9,z4,z467,z5,z6])],[(0,[z0,z1,z361,z4,z26,z5]),(0,[z1,z28,z3,z4,z17,z6]),(0,[z225,z1,z3,z4,z5,z6]),(0,[z541,z1,z3,z4,z114,z6]),(0,[z0,z48,z32,z152,z5,z6]),(0,[z0,z1,z3,z4,z1414,z6]),(0,[z0,z1,z3,z71,z5,z679])],[(0,[z15,z1,z3,z4,z149,z23]),(0,[z969,z0,z1,z4,z5,z6]),(0,[z119,z1,z3,z4,z5,z37]),(0,[z0,z1,z3,z4,z1415,z5]),(0,[z0,z1,z70,z4,z5,z23]),(0,[z0,z1,z292,z3,z149,z6]),(0,[z1416,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z1417]),(0,[z20,z1,z3,z4,z5,z227]),(0,[z0,z1,z3,z4,z5,z1418]),(0,[z0,z1,z3,z1419,z5,z6]),(0,[z0,z1,z3,z4,z5,z1420]),(0,[z46,z640,z1,z4,z5,z175]),(0,[z72,z1,z3,z4,z5,z23])],[(0,[z0,z1,z1421,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1422]),(0,[z1,z28,z3,z4,z5,z23]),(0,[z1,z3,z29,z4,z5,z410]),(0,[z120,z1,z287,z4,z5,z6]),(0,[z1423,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z388,z73])],[(0,[z451,z1,z3,z4,z26,z5])],[(0,[z20,z1,z3,z4,z26,z5]),(0,[z53,z1,z3,z4,z5,z158]),(0,[z36,z217,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z33,z23]),(0,[z1424,z1,z3,z4,z5,z6]),(0,[z0,z222,z3,z42,z5,z6])],[(0,[z36,z3,z4,z220,z5,z6]),(0,[z0,z212,z3,z4,z33,z23]),(0,[z0,z1,z262,z3,z149,z23])],[(0,[z0,z1,z3,z4,z5,z1425]),(0,[z32,z29,z4,z5,z33,z6]),(0,[z1426,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z674,z4,z23]),(0,[z1,z217,z32,z4,z5,z6]),(0,[z1,z100,z3,z29,z4,z6]),(0,[z1,z3,z29,z4,z149,z23]),(0,[z0,z1,z1427,z4,z5,z6]),(0,[z0,z638,z9,z4,z5,z6]),(0,[z0,z1428,z3,z4,z5,z6]),(0,[z1132,z1,z3,z4,z5,z23]),(0,[z0,z1,z125,z4,z454,z5])],[(0,[z1,z3,z67,z4,z5,z6]),(0,[z21,z1,z140,z4,z5,z6]),(0,[z13,z1,z3,z4,z109,z5]),(0,[z448,z212,z9,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z410]),(0,[z1,z3,z1294,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1417]),(0,[z20,z516,z3,z4,z5,z6]),(0,[z20,z1,z3,z4,z5,z346]),(0,[z0,z1,z3,z80,z678,z6]),(0,[z106,z1,z3,z4,z5,z425]),(0,[z0,z1,z3,z4,z5,z227]),(0,[z0,z1,z3,z1242,z5,z23])],[(0,[z0,z1,z524,z32,z5,z6]),(0,[z0,z1,z9,z413,z5,z6]),(0,[z36,z0,z3,z151,z5,z166]),(0,[z122,z1,z3,z80,z5,z6]),(0,[z1429,z1,z3,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z309]),(0,[z15,z1,z8,z4,z5,z6]),(0,[z15,z1,z3,z5,z493,z6]),(0,[z1,z3,z29,z4,z33,z23]),(0,[z0,z1,z1333,z4,z5,z6]),(0,[z0,z1,z32,z4,z26,z23]),(0,[z0,z1,z3,z4,z1430,z5]),(0,[z210,z1,z3,z599,z5,z6]),(0,[z0,z1,z100,z3,z4,z23]),(0,[z0,z1,z1431,z4,z5,z6])],[(0,[z0,z1,z3,z4,z26,z5]),(0,[z1,z3,z4,z1432,z5,z6]),(0,[z20,z1,z3,z295,z5,z6]),(0,[z13,z1,z3,z4,z5,z424]),(0,[z15,z1,z3,z4,z5,z333]),(0,[z0,z1,z9,z4,z62,z23]),(0,[z1433,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z28,z32,z4,z5,z23]),(0,[z639,z1,z3,z4,z5,z91]),(0,[z1,z3,z1434,z4,z5,z6]),(0,[z0,z1,z9,z4,z149,z23])],[(0,[z1,z107,z29,z4,z5,z47]),(0,[z0,z1,z4,z5,z1435,z6]),(0,[z103,z1,z3,z4,z5,z23]),(0,[z1255,z380,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1436])],[(0,[z0,z1,z1437,z4,z5,z6]),(0,[z1,z28,z70,z4,z5,z6]),(0,[z20,z1,z32,z4,z26,z5]),(0,[z128,z1,z9,z4,z5,z6]),(0,[z0,z1,z9,z4,z5,z794]),(0,[z0,z1,z9,z71,z5,z186]),(0,[z36,z0,z3,z151,z5,z37]),(0,[z0,z3,z4,z62,z751,z6]),(0,[z105,z0,z1,z4,z27,z6])],[(0,[z30,z1,z3,z29,z26,z5]),(0,[z1,z3,z4,z1438,z5,z6]),(0,[z0,z1,z3,z1439,z4,z5])],[(0,[z1,z126,z3,z4,z64,z6]),(0,[z1,z3,z524,z29,z5,z6]),(0,[z0,z1,z9,z4,z33,z23]),(0,[z78,z77,z3,z4,z33,z6])],[(0,[z98,z28,z3,z4,z5,z6]),(0,[z1,z28,z3,z4,z76,z5]),(0,[z0,z1,z178,z4,z619,z6])],[(0,[z821,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z468,z23]),(0,[z0,z1,z3,z4,z5,z1440]),(0,[z119,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z1441,z5]),(0,[z0,z1,z3,z4,z5,z1442]),(0,[z0,z1,z3,z193,z5,z307])],[(0,[z20,z7,z9,z4,z5,z6]),(0,[z1,z3,z29,z193,z5,z6]),(0,[z0,z1,z32,z4,z5,z227]),(0,[z0,z1,z3,z295,z5,z6]),(0,[z0,z1443,z3,z4,z5,z6]),(0,[z0,z1,z4,z1259,z5,z6])],[(0,[z20,z1,z3,z4,z318,z6]),(0,[z0,z1,z543,z636,z5,z6]),(0,[z0,z1,z3,z4,z5,z1326]),(0,[z0,z1,z531,z4,z26,z5]),(0,[z0,z48,z3,z798,z5,z6]),(0,[z0,z1,z3,z4,z5,z1444]),(0,[z0,z1,z3,z4,z307,z23]),(0,[z0,z1,z3,z4,z605,z23]),(0,[z1,z1445,z3,z4,z5,z6]),(0,[z1249,z1,z3,z4,z5,z6])],[(0,[z1,z3,z1446,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1322]),(0,[z0,z1,z4,z5,z1447,z6]),(0,[z0,z1,z3,z4,z803,z23])],[(0,[z0,z1,z3,z524,z76,z5]),(0,[z0,z1,z32,z4,z26,z5]),(0,[z0,z1,z9,z4,z6,z465]),(0,[z120,z1,z3,z4,z17,z6])],[(0,[z0,z1,z3,z4,z1448,z6]),(0,[z1449,z1,z3,z4,z5,z6])],[(0,[z1450,z1,z3,z4,z5,z6]),(0,[z1,z176,z34,z4,z5,z6]),(0,[z0,z1451,z3,z4,z5,z6]),(0,[z3,z152,z4,z220,z5,z6]),(0,[z0,z1,z9,z4,z5,z333])],[(0,[z1,z28,z100,z3,z4,z6]),(0,[z20,z1,z325,z4,z5,z6]),(0,[z15,z1,z3,z514,z5,z6]),(0,[z98,z0,z32,z4,z5,z6]),(0,[z120,z1,z3,z4,z5,z23]),(0,[z77,z1,z3,z4,z5,z23])],[(0,[z15,z1,z3,z4,z5,z838]),(0,[z1,z1079,z29,z4,z5,z6]),(0,[z1,z32,z4,z5,z6,z457]),(0,[z1,z3,z4,z5,z6,z1452])],[(0,[z563,z1,z228,z4,z5,z6]),(0,[z15,z1,z3,z370,z5,z6]),(0,[z248,z0,z1,z32,z4,z5]),(0,[z112,z283,z3,z4,z5,z82])]],
   [[(0,[z1453,z1,z3,z4,z5,z6]),(0,[z105,z15,z1,z3,z4,z23]),(1,[z0,z32,z4,z33,z23]),(0,[z1,z1454,z3,z4,z5,z6]),(0,[z0,z1,z3,z80,z157,z61]),(0,[z0,z1,z383,z3,z4,z26])],[(0,[z15,z1,z3,z80,z5,z23]),(0,[z0,z1,z423,z4,z5,z47]),(0,[z0,z1,z3,z4,z752,z5])],[(0,[z51,z20,z32,z4,z5,z6]),(0,[z15,z1,z437,z4,z5,z6]),(0,[z0,z1,z32,z295,z5,z6]),(0,[z25,z1,z3,z4,z26,z5]),(0,[z0,z1,z3,z4,z5,z425])],[(1,[z772,z3,z4,z5,z6]),(0,[z112,z3,z29,z4,z5,z82]),(0,[z1,z3,z29,z4,z833,z6]),(0,[z1344,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z551,z318,z6]),(0,[z41,z1,z3,z4,z5,z23]),(0,[z105,z0,z1,z3,z4,z116])],[(0,[z19,z1,z3,z4,z5,z233]),(0,[z20,z589,z3,z4,z5,z6]),(1,[z1,z3,z1134,z5,z6]),(0,[z0,z1,z3,z4,z5,z1455]),(0,[z0,z1,z1456,z4,z5,z6])],[(0,[z1,z3,z4,z5,z1457,z6]),(0,[z0,z1,z3,z1458,z5,z6]),(0,[z0,z375,z32,z4,z5,z6]),(0,[z36,z0,z3,z151,z85,z6]),(0,[z36,z122,z3,z151,z5,z6]),(0,[z0,z31,z3,z4,z62,z23]),(0,[z210,z1,z3,z4,z619,z6]),(0,[z1,z3,z4,z5,z1459,z6]),(0,[z0,z1,z3,z4,z803,z5])],[(0,[z283,z1,z3,z4,z5,z6]),(0,[z857,z0,z1,z3,z4,z5]),(0,[z20,z1,z3,z5,z1460,z6]),(0,[z1,z3,z1461,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z23])],[(0,[z0,z772,z3,z4,z5,z6]),(0,[z1462,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z23]),(0,[z1,z146,z3,z4,z26,z5]),(0,[z0,z3,z4,z5,z23,z1436])],[(0,[z1463,z1,z3,z4,z5,z6]),(0,[z1464,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1465,z5]),(0,[z15,z1,z3,z4,z94,z5]),(0,[z0,z1,z3,z1134,z5,z6]),(0,[z15,z0,z1,z3,z149,z23]),(0,[z63,z1,z9,z4,z64,z6]),(0,[z0,z1,z3,z4,z449,z23]),(0,[z0,z1,z1466,z4,z5,z6]),(0,[z36,z0,z3,z151,z17,z6]),(0,[z0,z1,z3,z4,z1467,z6]),(0,[z0,z1,z325,z551,z5,z6])],[(0,[z15,z1,z3,z4,z5,z864]),(0,[z0,z1,z423,z4,z5,z417]),(0,[z283,z1,z3,z551,z5,z6]),(0,[z0,z1,z3,z193,z26,z5]),(0,[z0,z1,z4,z5,z6,z831])],[(0,[z1,z3,z29,z4,z852,z6]),(0,[z90,z1,z3,z4,z5,z479]),(0,[z1010,z0,z1,z32,z4,z6]),(0,[z48,z277,z3,z152,z5,z6]),(0,[z77,z1,z537,z4,z5,z6]),(0,[z0,z1,z3,z61,z149,z23])],[(0,[z415,z28,z3,z4,z5,z6]),(0,[z1468,z1,z3,z4,z5,z6]),(0,[z36,z0,z3,z151,z5,z23]),(0,[z0,z44,z70,z4,z5,z111]),(0,[z1,z3,z4,z1469,z5,z6])],[(0,[z15,z1,z361,z4,z5,z6]),(0,[z105,z0,z1,z4,z299,z6]),(0,[z105,z0,z1,z193,z27,z6])],[(0,[z0,z1,z32,z4,z5,z425]),(0,[z113,z0,z3,z151,z5,z6]),(0,[z0,z1,z3,z413,z5,z410]),(0,[z0,z222,z3,z4,z5,z307])],[(0,[z20,z28,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1045]),(0,[z20,z595,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z1460,z6])],[(0,[z1,z28,z3,z4,z5,z586]),(0,[z0,z1,z1047,z3,z5,z6]),(0,[z1,z3,z29,z4,z94,z5]),(0,[z0,z1,z1198,z3,z4,z6]),(0,[z36,z0,z3,z798,z5,z6]),(0,[z1470,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z550,z23]),(0,[z1,z3,z29,z4,z865,z6]),(0,[z1,z1471,z3,z4,z5,z6]),(0,[z106,z1,z9,z4,z5,z6]),(0,[z41,z1,z70,z4,z5,z6]),(0,[z0,z1,z511,z4,z26,z5]),(0,[z1,z3,z4,z5,z6,z1472]),(0,[z1,z1473,z3,z4,z5,z6]),(0,[z1,z3,z725,z4,z5,z6]),(0,[z1,z1474,z3,z4,z5,z6])],[(0,[z377,z1,z374,z4,z5,z6]),(0,[z283,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z571]),(0,[z1,z3,z4,z5,z54,z23]),(0,[z0,z1,z1475,z4,z5,z6])],[(0,[z0,z1,z3,z1054,z5,z6]),(0,[z15,z1,z3,z4,z877,z6]),(0,[z0,z1,z32,z4,z62,z23]),(0,[z1,z3,z56,z4,z5,z23]),(0,[z0,z1,z3,z4,z6,z465]),(0,[z1196,z0,z3,z4,z5,z23])],[(0,[z15,z1,z543,z3,z5,z6]),(0,[z1,z3,z4,z1134,z5,z6]),(0,[z0,z1,z1032,z4,z5,z6]),(0,[z1199,z1,z3,z4,z5,z23])],[(0,[z1476,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z80,z61,z23]),(0,[z0,z1,z3,z4,z5,z719])],[(0,[z1,z28,z3,z4,z5,z1281]),(0,[z505,z1,z3,z260,z5,z6]),(0,[z20,z1,z401,z4,z5,z6]),(0,[z0,z1,z1346,z4,z5,z6]),(0,[z1477,z1,z3,z4,z5,z6]),(0,[z0,z1,z292,z3,z4,z23]),(0,[z0,z1,z3,z420,z4,z23])],[(0,[z0,z1,z3,z4,z5,z1347]),(0,[z1,z3,z1478,z4,z5,z6]),(0,[z0,z1,z3,z4,z157,z264])],[(0,[z1,z3,z29,z4,z5,z983]),(0,[z148,z1,z194,z4,z5,z6]),(0,[z0,z1,z962,z4,z26,z5])],[(0,[z69,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z17,z1211]),(0,[z112,z210,z3,z4,z5,z82]),(0,[z0,z1,z3,z1308,z5,z23])],[(0,[z0,z1,z87,z4,z5,z23]),(0,[z1,z1479,z3,z4,z5,z6])],[(0,[z195,z1,z3,z4,z434,z6]),(0,[z15,z38,z1,z3,z5,z73])],[(0,[z1,z3,z29,z4,z5,z567]),(0,[z1,z32,z4,z811,z5,z6]),(0,[z448,z1,z3,z4,z26,z5]),(0,[z0,z9,z696,z4,z5,z6]),(0,[z0,z31,z327,z4,z5,z6]),(0,[z0,z1,z437,z4,z26,z5]),(0,[z0,z1480,z3,z4,z5,z6]),(0,[z0,z1,z110,z3,z4,z157])],[(0,[z219,z28,z3,z4,z5,z6]),(0,[z15,z1,z3,z551,z5,z6]),(0,[z0,z1,z3,z193,z5,z425]),(0,[z0,z1,z100,z3,z4,z26])],[(0,[z15,z1,z903,z4,z5,z6]),(0,[z15,z1,z3,z574,z5,z6]),(0,[z0,z1,z401,z4,z5,z6]),(0,[z1041,z0,z1,z32,z4,z5]),(0,[z0,z1,z32,z4,z6,z465]),(0,[z451,z1,z9,z4,z5,z6]),(0,[z1481,z1,z3,z4,z5,z6]),(0,[z248,z0,z1,z3,z551,z5])],[(0,[z20,z1,z9,z4,z5,z6]),(0,[z354,z28,z3,z4,z5,z6]),(0,[z1,z28,z110,z3,z4,z26]),(0,[z20,z1,z3,z4,z26,z23]),(0,[z15,z51,z32,z4,z5,z6]),(0,[z0,z1,z4,z5,z1482,z6]),(0,[z0,z380,z3,z4,z5,z307]),(0,[z880,z1,z3,z4,z5,z6]),(0,[z0,z1,z1483,z4,z5,z6])],[(0,[z0,z1,z654,z3,z4,z23]),(0,[z0,z1,z1484,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 466) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 466).take 465) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 931).take 474) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1405).take 338) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1743)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [466, 465, 474, 338] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 80).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 174).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 257).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 349).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 426).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [80, 94, 83, 92, 77, 86] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_36216

theorem PEqualNP.Outside.L_meta_36216 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4274845896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274845896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36216.solve