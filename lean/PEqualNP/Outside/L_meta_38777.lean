import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38777

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x9001041031014294#64 ++ 0xa40041040c4050a5#64 ++ 0xee033cf1f103c7fd#64 ++ 0xfb80cf3c7c40f1ff#64 : BitVec 256),
   (0x600c5146806c9949#64 ++ 0x18031451a01b2652#64 ++ 0xde1cd34e81fcf9cf#64 ++ 0xf78734d3a07f3e73#64 : BitVec 256),
   (0x4060a28b06162c62#64 ++ 0x501828a2c1858b18#64 ++ 0xbfe0e38f1e1f3e73#64 ++ 0xeff838e3c787cf9c#64 : BitVec 256),
   (0x81b703f01ba03780#64 ++ 0x606dc0fc06e80de0#64 ++ 0x7dff03f01fe03f83#64 ++ 0x5f7fc0fc07f80fe0#64 : BitVec 256),
   (0x02dbfc001ddbc003#64 ++ 0x80b6ff000776f000#64 ++ 0xfbfffc001fffc003#64 ++ 0x3effff0007fff000#64 : BitVec 256),
   (0x00fefbedc0000000#64 ++ 0x003fbefb70000000#64 ++ 0xf8ffffffe0000000#64 ++ 0xfe3ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0048f80dc0000000 0x00123e0370000000 0x8000fc0fe0000000 0xa0003f03f8000000

def z1 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc001fffc003 0x3effff0007fff000

def z2 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0e38f1e1f3e73 0xeff838e3c787cf9c

def z3 : W := mkw 0x40fefbefc6162c62 0x503fbefbf1858b18 0xfffffffffe1f3e73 0xffffffffff87cf9c

def z4 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cd34e81fcf9cf 0xf78734d3a07f3e73

def z5 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff03f01fe03f83 0x5f7fc0fc07f80fe0

def z6 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xee033cf1f103c7fd 0xfb80cf3c7c40f1ff

def z7 : W := mkw 0x00f2aaa946122422 0x403caaaa51848908 0x21e32cb17e030630 0x0878cb2c5f80c18c

def z8 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z9 : W := mkw 0x02ffffe01ddbc003 0x80bffff80776f000 0xfbfffff01fffc003 0x7efffffc07fff000

def z10 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x11fc03000ee03802 0x047f00c003b80e00

def z11 : W := mkw 0x81fffbfddba03780 0x607ffeff76e80de0 0xfdffffffffe03f83 0xff7ffffffff80fe0

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0xce0010408100c1cd 0xf380041020403073

def z13 : W := mkw 0xf00d5556b16ddbdd 0xbc035555ac5b76f7 0xfe1ffffff1ffffff 0xff87fffffc7fffff

def z14 : W := mkw 0xf0050556b1255bdc 0xbc014155ac4956f7 0xee033ffff103fffd 0xfb80cffffc40ffff

def z15 : W := mkw 0x02fefbedccda8003 0x00bfbefb7336a000 0xf9ffffffeefc0002 0xfe7ffffffbbf0000

def z16 : W := mkw 0x00fefbedc6122422 0x403fbefb71848908 0xf9fffffffe030630 0xfe7fffffff80c18c

def z17 : W := mkw 0xd020029b22042ef4 0x740800a6c8810bbd 0x040003ffe0003ffc 0xc10000fff8000fff

def z18 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x31ff03b01ee03e02 0x0c7fc0ec07b80f80

def z19 : W := mkw 0x0048f80dc0000000 0x00123e0370000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z20 : W := mkw 0x00daf80000488001 0x0036be0000122000 0xfafffc0001fcc003 0x3ebfff00007f3000

def z21 : W := mkw 0x02feffedc45bc003 0x80bfbffb7116f000 0xfaffffffe01fc000 0xfebffffff807f000

def z22 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x11fcc0000efc0002 0x047f300003bf0000

def z23 : W := mkw 0x6004014680241948 0x18010051a0090652 0xce00134e8100f9cd 0xf38004d3a0403e73

def z24 : W := mkw 0xc12403fb02243fe0 0x704900fec0890ff8 0x040003ff00003ff0 0xc10000ffc0000ffc

def z25 : W := mkw 0xc1f7a3fb1fb63fe2 0x707de8fec7ed8ff8 0xffffe3ff1fff3ff3 0xfffff8ffc7ffcffc

def z26 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xdbfcd0000ffcc003 0x36ff340003ff3000

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8033cf1e0000000 0xfa00cf3c78000000

def z28 : W := mkw 0x02ffffeddddbc003 0x80bffffb7776f000 0xfbffffffffffc003 0xfefffffffffff000

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0xee033cf1f0030671 0xfb80cf3c7c00c19c

def z30 : W := mkw 0x810100101ba03780 0x6040400406e80de0 0x050000001fe03f83 0x0140000007f80fe0

def z31 : W := mkw 0x0008500000488001 0x0002140000122000 0xda1cd00001fcc003 0x36873400007f3000

def z32 : W := mkw 0x00fefbedc0488001 0x003fbefb70122000 0xfaffffffe1fcc003 0xfebffffff87f3000

def z33 : W := mkw 0x81b703fddba03780 0x606dc0ff76e80de0 0x7dff03ffffe03f83 0xdf7fc0fffff80fe0

def z34 : W := mkw 0x60000002006c9949 0x18000000801b2652 0x0600000001fcf9cf 0x01800000007f3e73

def z35 : W := mkw 0x90b707f031014294 0xa42dc1fc0c4050a5 0xfeff3ff1f103c7fd 0xffbfcffc7c40f1ff

def z36 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x78ff03f000000000 0x5e3fc0fc00000000

def z37 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff3ff1ffe3ffff 0xffffcffc7ff8ffff

def z38 : W := mkw 0x4020028b02042c60 0x500800a2c0810b18 0x0400038f00003e70 0xc10000e3c0000f9c

def z39 : W := mkw 0x0093000019800000 0x0024c00006600000 0x79ff00001fe00003 0x1e7fc00007f80000

def z40 : W := mkw 0x812403f002203780 0x604900fc00880de0 0x040003f000003f80 0x410000fc00000fe0

def z41 : W := mkw 0x00daf80dc0000000 0x0036be0370000000 0xf8fffc0fe0000000 0xbe3fff03f8000000

def z42 : W := mkw 0x00fefbedc2002400 0x403fbefb70800900 0xfdfffffffe003e03 0xff7fffffff800f80

def z43 : W := mkw 0x60000002004c8849 0x1800000080132212 0x02000000001cc04c 0x0080000000073013

def z44 : W := mkw 0x00be5bedc0000000 0x002f96fb70000000 0x401f1fffe0000000 0xd007c7fff8000000

def z45 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x441c134e81e0f9cc 0xd10704d3a0783e73

def z46 : W := mkw 0x83fffff01ffbf783 0xe0fffffc07fefde0 0xfffffff01fffff83 0x7ffffffc07ffffe0

def z47 : W := mkw 0x0020028002002400 0x400800a000800900 0x3de003801e003e03 0x4f7800e007800f80

def z48 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z49 : W := mkw 0x4040a00b04160862 0x10102802c1058218 0x8200e00f001f0070 0xa0803803c007c01c

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z51 : W := mkw 0x02f3aea95d934002 0x80bcebaa5764d000 0x21e32cb17e030000 0x0878cb2c5f80c000

def z52 : W := mkw 0x90fffffdf1014294 0xa43fffff7c4050a5 0xfefffffff103c7fd 0xffbffffffc40f1ff

def z53 : W := mkw 0x0004014000000000 0x0001005000000000 0x581c034000000000 0x560700d000000000

def z54 : W := mkw 0x02d3ac001d934002 0x80b4eb000764d000 0x21e32c001e030000 0x0878cb000780c000

def z55 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff2ff17fe33fb3 0x5f7fcbfc5ff8cfec

def z56 : W := mkw 0x4040a00b04160862 0x10102802c1058218 0xae00e08f101f0671 0xeb803823c407c19c

def z57 : W := mkw 0x4060a28b00040840 0x101828a2c0010210 0xbee0e38f001c3843 0xefb838e3c0070e10

def z58 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xc2033c71e103c1fc 0xb080cf1c7840f07f

def z59 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x11e0c30e0e1c3802 0x047830c383870e00

def z60 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x40031c70e100c18c 0x1000c71c38403063

def z61 : W := mkw 0x0004014000201100 0x0001005000080440 0x5c1c034001e03983 0x570700d000780e60

def z62 : W := mkw 0xe1bf53f69becbfc9 0x786fd4fda6fb2ff2 0xffffd3fe9ffcffcf 0xfffff4ffa7ff3ff3

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000040800001cc 0xc100001020000073

def z64 : W := mkw 0x0008500000488001 0x0002140000122000 0xde1cd04081fcc1cf 0xf7873410207f3073

def z65 : W := mkw 0x606cf3cf867ebd6b 0x581b3cf3e19faf5a 0xfffcf3cf9fffffff 0xffff3cf3e7ffffff

def z66 : W := mkw 0x002403c002203500 0x400900f000880d40 0x7dfc03c01fe03f83 0x5f7f00f007f80fe0

def z67 : W := mkw 0x009e5964c0000000 0x0027965930000000 0xd81fdf7ee0000000 0xf607f7dfb8000000

def z68 : W := mkw 0x8197017019a01380 0x2065c05c066804e0 0x6c1f00f011e00781 0x5b07c03c047801e0

def z69 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe0f3cf9f1fffff 0xfff83cf3e7c7ffff

def z70 : W := mkw 0x0060a28006122402 0x401828a001848900 0xbfe0e3801e1f3e03 0x6ff838e00787cf80

def z71 : W := mkw 0xf2dffd56bdffdbdf 0xbcb7ff55af7ff6f7 0xffffffffffffffff 0xffffffffffffffff

def z72 : W := mkw 0x000c514480000000 0x0003145120000000 0x101cc30e00000000 0x040730c380000000

def z73 : W := mkw 0x60fefbefc0241948 0x183fbefbf0090652 0xfcffffffe00039cc 0xff3ffffff8000e73

def z74 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x61ff00f01fe00780 0x187fc03c07f801e0

def z75 : W := mkw 0x4000000200040840 0x1000000080010210 0x06000000001c3843 0x0180000000070e10

def z76 : W := mkw 0x020104001ddbc003 0x808041000776f000 0x030000001fffc003 0x00c0000007fff000

def z77 : W := mkw 0x009e5964c0000000 0x0027965930000000 0x401f1c70e0000000 0x1007c71c38000000

def z78 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x10fcc30e00000000 0x043f30c380000000

def z79 : W := mkw 0x60fefbefc06c9949 0x183fbefbf01b2652 0xfeffffffe1fcf9cf 0xffbffffff87f3e73

def z80 : W := mkw 0x810501501ba03780 0x6041405406e80de0 0x5d1c03401fe03f83 0x574700d007f80fe0

def z81 : W := mkw 0x0040a00004120002 0x0010280001048000 0xbbe0e0001e1f0003 0x2ef838000787c000

def z82 : W := mkw 0x42fbfe8b1fdfec63 0xd0beffa2c7f7fb18 0xffffff8f1ffffe73 0xffffffe3c7ffff9c

def z83 : W := mkw 0x200c514480689109 0x08031451201a2442 0x401c104081e0c18c 0x1007041020783063

def z84 : W := mkw 0x4040a00b04160862 0x10102802c1058218 0x0000c00e001c0000 0x0000300380070000

def z85 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x20032cb170030630 0x0800cb2c5c00c18c

def z86 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0x20e32cb160000000 0x0838cb2c58000000

def z87 : W := mkw 0x80b703f011000280 0x202dc0fc044000a0 0x7cff03f011000781 0x5f3fc0fc044001e0

def z88 : W := mkw 0x0248fc00045bc003 0x80923f000116f000 0x8200fc00001fc000 0x20803f000007f000

def z89 : W := mkw 0x9000001020000294 0x24000004080000a5 0x040000f1e00007fc 0xc100003c780001ff

def z90 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffc70ffffc18f 0x3effff1c3ffff063

def z91 : W := mkw 0x002403edc0000000 0x000900fb70000000 0x000003ffe0000000 0xc00000fff8000000

def z92 : W := mkw 0x00daf80000000000 0x0036be0000000000 0xf8fffc0000000000 0x3e3fff0000000000

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x680300f000000000 0x5a00c03c00000000

def z94 : W := mkw 0x81fffbfddba03780 0x607ffeff76e80de0 0x7dffc3fe1fe03f83 0x5f7ff0ff87f80fe0

def z95 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfefffffff0030671 0xffbffffffc00c19c

def z96 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x3dfc03801ee03e03 0x4f7f00e007b80f80

def z97 : W := mkw 0x01fefbedcaa03500 0x407fbefb72a80d40 0xf9ffffffeee03802 0xfe7ffffffbb80e00

def z98 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0x79ffc0001ffc0003 0x1e7ff00007ff0000

def z99 : W := mkw 0x1000040020014014 0x8400010008005005 0x82003c01e003c07c 0xa0800f007800f01f

def z100 : W := mkw 0x42fafa8b0edeac63 0x50bebea2c3b7ab18 0x11fcc30e0efc3802 0x047f30c383bf0e00

def z101 : W := mkw 0x00fefbedc0201100 0x003fbefb70080440 0xfcffffffe1e03983 0xff3ffffff8780e60

def z102 : W := mkw 0x0248fc0dc45bc003 0x80923f037116f000 0x8200fc0fe01fc000 0xa0803f03f807f000

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000010030671 0x018000000400c19c

def z104 : W := mkw 0x6248fc06845fc84b 0x98923f01a117f212 0x8200fc0e801fc04c 0xa0803f03a007f013

def z105 : W := mkw 0x62dffd469dffd94b 0x98b7ff51a77ff652 0xffffff4e9ffff9cf 0xffffffd3a7fffe73

def z106 : W := mkw 0x4000000200040840 0x1000000080010210 0x9e00c30e001c3843 0xe78030c380070e10

def z107 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffcb17fffc633 0x3effff2c5ffff18c

def z108 : W := mkw 0xc061a29b17162ee2 0x701868a6c5c58bb8 0xffe3e3ff1f1f3ff3 0xfff8f8ffc7c7cffc

def z109 : W := mkw 0x8001041011014280 0xa0004104044050a0 0xee033cf01103c781 0x7b80cf3c0440f1e0

def z110 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0x93fcfc000effc002 0x24ff3f0003bff000

def z111 : W := mkw 0x8001001011000280 0x20004004044000a0 0x6c0300f011000781 0x5b00c03c044001e0

def z112 : W := mkw 0x10feffede0014014 0x843fbffb78005005 0xfaffffffe003c07c 0xfebffffff800f01f

def z113 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x060000001103c7fd 0x018000000440f1ff

def z114 : W := mkw 0x0008500000488001 0x0002140000122000 0x8200d000001cc000 0x2080340000073000

def z115 : W := mkw 0xe12403f682243fc8 0x784900fda0890ff2 0x040003fe80003fcc 0xc10000ffa0000ff3

def z116 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x161cc30e01fcf9cf 0x058730c3807f3e73

def z117 : W := mkw 0x020000000cda8003 0x008000000336a000 0x010000000efc0002 0x0040000003bf0000

def z118 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xce031c70e100c1cd 0xf380c71c38403073

def z119 : W := mkw 0x8197017019a01380 0x2065c05c066804e0 0x401f007001e00180 0x1007c01c00780060

def z120 : W := mkw 0x4000000200040840 0x1000000080010210 0xde00d34e811cf9cf 0xf78034d3a0473e73

def z121 : W := mkw 0x0060a28906122422 0x401828a241848908 0x21e020811e030630 0x087808204780c18c

def z122 : W := mkw 0x0060a28900000000 0x001828a240000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z123 : W := mkw 0x1000040020014014 0x8400010008005005 0xce003c41e103c1fd 0xf3800f107840f07f

def z124 : W := mkw 0x0248f800045a8003 0x00923e000116a000 0x0000c000001c0000 0x0000300000070000

def z125 : W := mkw 0x4000000206162c62 0x5000000081858b18 0x070000001e1f3e73 0x01c000000787cf9c

def z126 : W := mkw 0x6004014680241948 0x18010051a0090652 0x0400034e800039cc 0xc10000d3a0000e73

def z127 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0xffff3ff01fe3ff83 0x7fffcffc07f8ffe0

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00004001000181 0x5300001000400060

def z129 : W := mkw 0x03ffffe01ffbf503 0xc0fffff807fefd40 0xfbffff001ffff803 0x3effffc007fffe00

def z130 : W := mkw 0x0020028000000000 0x000800a000000000 0x38e0038000000000 0x4e3800e000000000

def z131 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xfdff3ff1ffe03f83 0xff7fcffc7ff80fe0

def z132 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x9e1cc30e00fc3843 0xe78730c3803f0e10

def z133 : W := mkw 0xc1b703f21fb63fe2 0x706dc0fc87ed8ff8 0x7fff03f01fff3ff3 0x5fffc0fc07ffcffc

def z134 : W := mkw 0x8104017000201380 0x2041005c000804e0 0x0000007000000180 0x0000001c00000060

def z135 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x15fc03f00ee03f82 0x457f00fc03b80fe0

def z136 : W := mkw 0x60085006804c8849 0x18021401a0132212 0x8200d00e801cc04c 0xa0803403a0073013

def z137 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc811fffc673 0xffffff2047fff19c

def z138 : W := mkw 0x00fafaadc0000000 0x003ebeab70000000 0xa0e3fcbfe0000000 0xa838ff2ff8000000

def z139 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x10fc030000000000 0x043f00c000000000

def z140 : W := mkw 0x4060a28b04160862 0x101828a2c1058218 0xbae0e38f001f0070 0xeeb838e3c007c01c

def z141 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xbbfce0001eff0003 0x2eff380007bfc000

def z142 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xa3e3fc001e1fc000 0x28f8ff000787f000

def z143 : W := mkw 0x0092000008800000 0x0024800002200000 0x11fc00000ee00002 0x047f000003b80000

def z144 : W := mkw 0xd061a69b37176ef6 0xf41869a6cdc5dbbd 0xffe3ffffff1fffff 0xfff8ffffffc7ffff

def z145 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x101cc30e00fc3802 0x040730c3803f0e00

def z146 : W := mkw 0x42ffffefdfdfec63 0xd0bffffbf7f7fb18 0xfffffffffffffe73 0xffffffffffffff9c

def z147 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x10fcc3ffe0000000 0xc43f30fff8000000

def z148 : W := mkw 0x91b306b03b816694 0xe46cc1ac0ee059a5 0x21e32cb17e030630 0x0878cb2c5f80c18c

def z149 : W := mkw 0x4000000204160862 0x1000000081058218 0x02000000001f0070 0x008000000007c01c

def z150 : W := mkw 0x000c514480000000 0x0003145120000000 0xd81cd34e80000000 0xf60734d3a0000000

def z151 : W := mkw 0x9249fc10355bc297 0xa4927f040d56f0a5 0xee03fcf1f11fc7fd 0xfb80ff3c7c47f1ff

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0xae00208110030671 0xeb8008204400c19c

def z153 : W := mkw 0x029b5c001ddbc003 0x80a6d7000776f000 0x431f1c001fffc003 0x10c7c70007fff000

def z154 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffcf1ffffc003 0xfeffff3c7ffff000

def z155 : W := mkw 0xc1b703f21ba43fc0 0x706dc0fc86e90ff0 0xffffc3fe1ffc3fc3 0xfffff0ff87ff0ff0

def z156 : W := mkw 0x83dffd701dfbd383 0xa0f7ff5c077ef4e0 0xfbfffc701fffc183 0x3effff1c07fff060

def z157 : W := mkw 0x6068f28f865eac6b 0x581a3ca3e197ab1a 0xbfe0f38f9e1ffe7f 0xeff83ce3e787ff9f

def z158 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfffffcf01fffc783 0x7fffff3c07fff1e0

def z159 : W := mkw 0x60def946806c9949 0x1837be51a01b2652 0xfeffff4e81fcf9cf 0xffbfffd3a07f3e73

def z160 : W := mkw 0x2000000000689109 0x08000000001a2442 0x0000000001e0c18c 0x0000000000783063

def z161 : W := mkw 0x602c53cf826cbd69 0x580b14f3e09b2f5a 0xde1cd3cf81fcffff 0xf78734f3e07f3fff

def z162 : W := mkw 0xc10100121fb63fe2 0x7040400487ed8ff8 0x070000001fff3ff3 0x01c0000007ffcffc

def z163 : W := mkw 0x9197057039a15394 0xa465c15c0e6854e5 0x401f1c70e1e0c18c 0x1007c71c38783063

def z164 : W := mkw 0x0064a3edc0000000 0x001928fb70000000 0xb8e0e3ffe0000000 0xee3838fff8000000

def z165 : W := mkw 0x9000001020000294 0x24000004080000a5 0xce0010f1e100c7fd 0xf380043c784031ff

def z166 : W := mkw 0x00ffffedd1014000 0x803ffffb74405000 0xfafffffff103c001 0xfebffffffc40f000

def z167 : W := mkw 0x93fffff03ffbf797 0xe4fffffc0ffefde5 0xfffffff1ffffffff 0xfffffffc7fffffff

def z168 : W := mkw 0x00b603e002002400 0x402d80f800800900 0x7dff03f01e003e03 0x5f7fc0fc07800f80

def z169 : W := mkw 0x812102901ba03780 0x604840a406e80de0 0x3de003801fe03f83 0x4f7800e007f80fe0

def z170 : W := mkw 0x02085c000049c001 0x8082170000127000 0x00001c000000c000 0x0000070000003000

def z171 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xea033c70f103c18d 0x3a80cf1c3c40f063

def z172 : W := mkw 0xc1fffbffdfb63fe2 0x707ffefff7ed8ff8 0xffffffffffff3ff3 0xffffffffffffcffc

def z173 : W := mkw 0x830104101ffbf783 0xe0c0410407fefde0 0x070000001fffff83 0x01c0000007ffffe0

def z174 : W := mkw 0x0060a28900000000 0x001828a240000000 0xb8e0e38f00000000 0xee3838e3c0000000

def z175 : W := mkw 0x9000001020000294 0x24000004080000a5 0x00000070e000018c 0x0000001c38000063

def z176 : W := mkw 0x620104021dffd94b 0x98804100877ff652 0x070000001ffff9cf 0x01c0000007fffe73

def z177 : W := mkw 0x81b302b01b802680 0x606cc0ac06e009a0 0x21e300b01e000600 0x0878c02c07800180

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000f1e0000000 0xc000003c78000000

def z179 : W := mkw 0x02f3ae891f936422 0xc0bceba247e4d908 0x21e32c811e030630 0x0878cb204780c18c

def z180 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0x7dff03f1ffe03fff 0xdf7fc0fc7ff80fff

def z181 : W := mkw 0x000c514480000000 0x0003145120000000 0x401c104080000000 0x1007041020000000

def z182 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xe8033cf1e100c18c 0xfa00cf3c78403063

def z183 : W := mkw 0x0001040011014000 0x8000410004405000 0xea033c001103c001 0x3a80cf000440f000

def z184 : W := mkw 0x90fffffdf1014294 0xa43fffff7c4050a5 0xf8ffffffe100c18c 0xfe3ffffff8403063

def z185 : W := mkw 0xe3fffff69fffffcb 0xf8fffffda7fffff2 0xfffffffe9fffffcf 0xffffffffa7fffff3

def z186 : W := mkw 0x4020028b02042c60 0x500800a2c0810b18 0x0000030e00003800 0x000000c380000e00

def z187 : W := mkw 0x4040a00b04160862 0x10102802c1058218 0x9e00e30f001f3873 0xe78038c3c007ce1c

def z188 : W := mkw 0x1248fc00245bc017 0x84923f000916f005 0x8200fc01e01fc07c 0xa0803f007807f01f

def z189 : W := mkw 0x00b603e000201100 0x002d80f800080440 0x7cff03f001e03983 0x5f3fc0fc00780e60

def z190 : W := mkw 0x0001040011014000 0x8000410004405000 0xee033c409103c1cd 0xfb80cf102440f073

def z191 : W := mkw 0x0040a00004120002 0x0010280001048000 0x11e0c0000e1c0002 0x0478300003870000

def z192 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x6e0300f01103c7fd 0x5b80c03c0440f1ff

def z193 : W := mkw 0x600d5546916dd949 0x98035551a45b7652 0xfe1fff4e91fff9cf 0xff87ffd3a47ffe73

def z194 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x5dfc03400fe03983 0x577f00d003f80e60

def z195 : W := mkw 0x60000002006c9949 0x18000000801b2652 0x9e00c30e01fcf9cf 0xe78030c3807f3e73

def z196 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x44031cf1e100c7fc 0xd100c73c784031ff

def z197 : W := mkw 0x029b5c0019c9c001 0x80a6d70006727000 0x401f1c0001e0c000 0x1007c70000783000

def z198 : W := mkw 0x02930c0019814000 0x80a4c30006605000 0x00030c0000000000 0x0000c30000000000

def z199 : W := mkw 0x900954103149c295 0xa40255040c5270a5 0xfe1ffcf1f1ffc7ff 0xff87ff3c7c7ff1ff

def z200 : W := mkw 0x0240ac0004134002 0x80902b000104d000 0x00002c0000030000 0x00000b000000c000

def z201 : W := mkw 0x006cf3cd80000000 0x001b3cf360000000 0xf8fcf3cf80000000 0xfe3f3cf3e0000000

def z202 : W := mkw 0x029b5c0019c9c001 0x80a6d70006727000 0xea1f3c0011e3c001 0x3a87cf000478f000

def z203 : W := mkw 0x9041a41035134296 0xa41069040d44d0a5 0xffe3fcf1ff1fc7ff 0xfff8ff3c7fc7f1ff

def z204 : W := mkw 0x00b302801b802400 0x402cc0a006e00900 0x7dff03801fe03e03 0x5f7fc0e007f80f80

def z205 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff13f09fe0ffcf 0xffffc4fc27f83ff3

def z206 : W := mkw 0x902403fde0000294 0x240900ff780000a5 0x040003ffe00007fc 0xc10000fff80001ff

def z207 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x61ff3c001fe3c000 0x187fcf0007f8f000

def z208 : W := mkw 0x00d3a0001d920002 0x0034e80007648000 0xfbffe0001fff0003 0x3efff80007ffc000

def z209 : W := mkw 0xc164a3fb06363fe2 0x705928fec18d8ff8 0xbfe0e3ff1e1f3ff3 0xeff838ffc787cffc

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000208110030630 0x080008204400c18c

def z211 : W := mkw 0x81f3a2b91f9226a2 0x607ce8ae47e489a8 0x21e320b11e030630 0x0878c82c4780c18c

def z212 : W := mkw 0x41f6a3eb0eb63d62 0x507da8fac3ad8f58 0x11fcc30e0efc3802 0x047f30c383bf0e00

def z213 : W := mkw 0x02dbfc0019c9c001 0x80b6ff0006727000 0xf8fffc0001e0c000 0x3e3fff0000783000

def z214 : W := mkw 0x012403e002203500 0x404900f800880d40 0x0000030000003800 0x000000c000000e00

def z215 : W := mkw 0x42fafa8b0edeac63 0x50bebea2c3b7ab18 0xbffce38f1eff3e73 0xefff38e3c7bfcf9c

def z216 : W := mkw 0x40fefbefc6162c62 0x503fbefbf1858b18 0xf9ffffffee1c3802 0xfe7ffffffb870e00

def z217 : W := mkw 0x60be53e6806c9949 0x182f94f9a01b2652 0xfeffd3fe81fcf9cf 0xffbff4ffa07f3e73

def z218 : W := mkw 0x9000041020014294 0xa4000104080050a5 0x86003cf1e003c7fc 0xe1800f3c7800f1ff

def z219 : W := mkw 0x00fefbe000000000 0x003fbef800000000 0xf8fffff000000000 0x7e3ffffc00000000

def z220 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff23f11fe33ff3 0xffffc8fc47f8cffc

def z221 : W := mkw 0xd001041237176ef6 0xf40041048dc5dbbd 0x070000001f1fffff 0x01c0000007c7ffff

def z222 : W := mkw 0xb00d5554b169d39d 0xac0355552c5a74e7 0x401f1c70e1e0c18c 0x1007c71c38783063

def z223 : W := mkw 0x60040142006c9949 0x18010050801b2652 0x5e1c034001fcf9cf 0x578700d0007f3e73

def z224 : W := mkw 0x0060a28906122422 0x401828a241848908 0xb9e0e38f1e030630 0xee7838e3c780c18c

def z225 : W := mkw 0xd001041231054ad4 0xb40041048c4152b5 0xfe03fffff11fffff 0xff80fffffc47ffff

def z226 : W := mkw 0x9005055031215394 0xa40141540c4854e5 0xfe1f3ff1f1e3ffff 0xff87cffc7c78ffff

def z227 : W := mkw 0xf0010412316ddbdd 0xbc0041048c5b76f7 0x0600000011ffffff 0x01800000047fffff

def z228 : W := mkw 0x819701701ba03780 0x6065c05c06e80de0 0x451f00701fe03f83 0x1147c01c07f80fe0

def z229 : W := mkw 0x01b202a00a802400 0x406c80a802a00900 0x01e000000e000000 0x0078000003800000

def z230 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x000000000100c18c 0x0000000000403063

def z231 : W := mkw 0x602403efc0241948 0x180900fbf0090652 0x040003ffe00039cc 0xc10000fff8000e73

def z232 : W := mkw 0x4068f28b065eac63 0x501a3ca2c197ab18 0xfffcf38f1ffffe73 0xffff3ce3c7ffff9c

def z233 : W := mkw 0xc1f7a3fb1fb63fe2 0x707de8fec7ed8ff8 0x7dffc3fe1ffc3f83 0x5f7ff0ff87ff0fe0

def z234 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x9fe0c30e0e1c3843 0xe7f830c383870e10

def z235 : W := mkw 0x0020028002002400 0x400800a000800900 0x0400038000003e00 0x410000e000000f80

def z236 : W := mkw 0x60085002006c9949 0x18021400801b2652 0xde1cd00001fcf9cf 0x37873400007f3e73

def z237 : W := mkw 0x20fefbedc0689109 0x083fbefb701a2442 0xf8ffffffe1e0c18c 0xfe3ffffff8783063

def z238 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xd8fcd34e80000000 0xf63f34d3a0000000

def z239 : W := mkw 0xe10d51569becbfc9 0x78435455a6fb2ff2 0xdf1cd34e9ffcffcf 0xf7c734d3a7ff3ff3

def z240 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x25e303f01e003f80 0x4978c0fc07800fe0

def z241 : W := mkw 0x81b703f019a01380 0x206dc0fc066804e0 0x78ff03f001e00180 0x5e3fc0fc00780060

def z242 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x60033cf1f103c7bc 0x1800cf3c7c40f1ef

def z243 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff1ff0ffe0ff8f 0x5f7fc7fc3ff83fe3

def z244 : W := mkw 0x4040a00b06162c62 0x50102802c1858b18 0x8700e00f1e1f3e73 0xa1c03803c787cf9c

def z245 : W := mkw 0x0004014000201100 0x0001005000080440 0x401c004001e00180 0x1007001000780060

def z246 : W := mkw 0x00b703e019800000 0x002dc0f806600000 0x79ff03f01fe00003 0x5e7fc0fc07f80000

def z247 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x79ff03001fe03803 0x1e7fc0c007f80e00

def z248 : W := mkw 0x9021069033016694 0xe40841a40cc059a5 0xffe33ff1ff03ffff 0xfff8cffc7fc0ffff

def z249 : W := mkw 0x0004014000201100 0x0001005000080440 0xde1c134081e0f9cf 0xf78704d020783e73

def z250 : W := mkw 0x90dbfc1031014294 0xa436ff040c4050a5 0xfefffcf1f103c7fd 0xffbfff3c7c40f1ff

def z251 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x51ff03700fe03982 0x147fc0dc03f80e60

def z252 : W := mkw 0x2004014480201108 0x0801005120080442 0x000000408000018c 0x0000001020000063

def z253 : W := mkw 0xd060a29b26162ef6 0x741828a6c9858bbd 0xbfe0e3fffe1f3fff 0xeff838ffff87cfff

def z254 : W := mkw 0x6000000200241948 0x1800000080090652 0x04000000000039cc 0x0100000000000e73

def z255 : W := mkw 0x00f6abedc0000000 0x003daafb70000000 0x20e32fffe0000000 0xc838cbfff8000000

def z256 : W := mkw 0xb00d5554b169d39d 0xac0355552c5a74e7 0xee1f3cf1f1e3c7fd 0xfb87cf3c7c78f1ff

def z257 : W := mkw 0x62dbfc069ddfc84b 0x98b6ff01a777f212 0xfbfffc0e9fffc04f 0xbeffff03a7fff013

def z258 : W := mkw 0xf0095416b14dcadd 0xbc025505ac5372b7 0xee03fcfff11fc7fd 0xfb80ff3ffc47f1ff

def z259 : W := mkw 0x81bf53f49ba03780 0x606fd4fd26e80de0 0xfdffd3fe9fe03f83 0xff7ff4ffa7f80fe0

def z260 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffc001fffc7ff 0x3fffff0007fff1ff

def z261 : W := mkw 0x200c514480689109 0x08031451201a2442 0x5c1c134081e0f98f 0x570704d020783e63

def z262 : W := mkw 0x0060a28906122422 0x401828a241848908 0x3de023811e033e33 0x4f7808e04780cf8c

def z263 : W := mkw 0xd1f7a7fb3fb77ff6 0xf47de9fecfeddffd 0xffffffffffffffff 0xffffffffffffffff

def z264 : W := mkw 0x00be5be4c0000000 0x002f96f930000000 0x78ff1ff0e0000000 0x5e3fc7fc38000000

def z265 : W := mkw 0x81fffbfdd9a01380 0x207ffeff766804e0 0xf8ffffffe1e00180 0xfe3ffffff8780060

def z266 : W := mkw 0x600c5146867ebd6b 0x58031451a19faf5a 0xdf1cd34e9fffffff 0xf7c734d3a7ffffff

def z267 : W := mkw 0x6048f80fc04c8849 0x18123e03f0132212 0x8200fc0fe01cc04c 0xa0803f03f8073013

def z268 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xe8033cf1f0030630 0xfa00cf3c7c00c18c

def z269 : W := mkw 0x6064a3cf86363d6a 0x581928f3e18d8f5a 0xbfe0e3cf9e1f3fff 0xeff838f3e787cfff

def z270 : W := mkw 0x002403edc0000000 0x000900fb70000000 0xe8033fffe0000000 0xfa00cffff8000000

def z271 : W := mkw 0x0020028002002400 0x400800a000800900 0x21e000801e000600 0x0878002007800180

def z272 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x30ffefbf60000000 0x0c3ffbefd8000000

def z273 : W := mkw 0xd061a69b37176ef6 0xf41869a6cdc5dbbd 0xbfe0e38f1f1fffff 0xeff838e3c7c7ffff

def z274 : W := mkw 0x81f7a3f01fb23782 0x607de8fc07ec8de0 0xffffe3f01fff3f83 0x7ffff8fc07ffcfe0

def z275 : W := mkw 0x606cf3cf867ebd6b 0x581b3cf3e19faf5a 0xdffcd34e8ffcf9cf 0xf7ff34d3a3ff3e73

def z276 : W := mkw 0x0001040011014000 0x8000410004405000 0xea033cf1f103c001 0xfa80cf3c7c40f000

def z277 : W := mkw 0xd0fffffff7176ef6 0xf43ffffffdc5dbbd 0xffffffffff1fffff 0xffffffffffc7ffff

def z278 : W := mkw 0x1000040020014014 0x8400010008005005 0xea033cf1e003c07c 0xfa80cf3c7800f01f

def z279 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x6c031cf0f100c78d 0x5b00c73c3c4031e3

def z280 : W := mkw 0x80fffbfdd1000280 0x203ffeff744000a0 0xfcfffffff1000781 0xff3ffffffc4001e0

def z281 : W := mkw 0x609e5966c06c9949 0x18279659b01b2652 0xde1fdf7ee1fcf9cf 0xf787f7dfb87f3e73

def z282 : W := mkw 0x624cfd46847fd94b 0x98933f51a11ff652 0xde1cff4e81fff9cf 0xf7873fd3a07ffe73

def z283 : W := mkw 0xf0fffffff16ddbdd 0xbc3ffffffc5b76f7 0xfefffffff1ffffff 0xffbffffffc7fffff

def z284 : W := mkw 0x81b302b01b802680 0x606cc0ac06e009a0 0x6de300f01f000781 0x5b78c03c07c001e0

def z285 : W := mkw 0x912403f022203794 0x644900fc08880de5 0x040003f1e0003ffc 0xc10000fc78000fff

def z286 : W := mkw 0x81b302b01ba03780 0x606cc0ac06e80de0 0x25e300b01fe03f83 0x0978c02c07f80fe0

def z287 : W := mkw 0x83fffbf01ffab783 0x60fffefc07feade0 0x7dffc3f01ffc3f83 0x5f7ff0fc07ff0fe0

def z288 : W := mkw 0x0048f000045a8003 0x00123c000116a000 0xfbfcf0001fffc003 0x3eff3c0007fff000

def z289 : W := mkw 0x8193003019800280 0x2064c00c066000a0 0x0003003000000000 0x0000c00c00000000

def z290 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x79ff03f00ee03802 0x5e7fc0fc03b80e00

def z291 : W := mkw 0x0060a28906122422 0x401828a241848908 0xbbe0e0811e1f0633 0x2ef838204787c18c

def z292 : W := mkw 0x406cf3cf86162c62 0x501b3cf3e1858b18 0xfffcf3cf9e1f3e73 0xffff3cf3e787cf9c

def z293 : W := mkw 0x61be53e68aecbd49 0x586f94f9a2bb2f52 0x11fcc30e0efc3802 0x047f30c383bf0e00

def z294 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x78ffc3fe00000000 0x5e3ff0ff80000000

def z295 : W := mkw 0x00daf80004120002 0x0036be0001048000 0xfbfffc001e1f0003 0x3effff000787c000

def z296 : W := mkw 0x60fefbefc67ebd6b 0x583fbefbf19faf5a 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x00be53e480000000 0x002f94f920000000 0xf8ffd3fe80000000 0xfe3ff4ffa0000000

def z298 : W := mkw 0x002002a940000000 0x000800aa50000000 0x000000b160000000 0x0000002c58000000

def z299 : W := mkw 0x209e5964c0689109 0x08279659301a2442 0x401f1c70e1e0c18c 0x1007c71c38783063

def z300 : W := mkw 0x0040a80940000000 0x00102a0250000000 0x00002c0160000000 0x00000b0058000000

def z301 : W := mkw 0xf00c5156a06c9bdd 0x3c031455a81b26f7 0xde1cd3ffe1fcffff 0xf78734fff87f3fff

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x80003c01e0000000 0xa0000f0078000000

def z303 : W := mkw 0x4000000200040840 0x1000000080010210 0x8200c00e001c0040 0xa080300380070010

def z304 : W := mkw 0x42dbfc0b1ddfc863 0x90b6ff02c777f218 0xfbfffc0f1fffc073 0xbeffff03c7fff01c

def z305 : W := mkw 0x4000000b00040860 0x10000002c0010218 0x0000000f00000070 0x80000003c000001c

def z306 : W := mkw 0x8000001000000280 0x20000004000000a0 0x040000f000000780 0x4100003c000001e0

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200200100030070 0xa08008004000c01c

def z308 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x0000000010030630 0x000000000400c18c

def z309 : W := mkw 0xf06df7dfb77fffff 0xfc1b7df7eddfffff 0xffffffffffffffff 0xffffffffffffffff

def z310 : W := mkw 0x819300101ba03780 0x6064c00406e80de0 0x7dff00001fe03f83 0x1f7fc00007f80fe0

def z311 : W := mkw 0x0001040011014000 0x8000410004405000 0x020000001103c001 0x008000000440f000

def z312 : W := mkw 0x62def9468cfe994b 0x18b7be51a33fa652 0xdffcd34e8ffcf9cf 0xf7ff34d3a3ff3e73

def z313 : W := mkw 0x00def96dc0000000 0x0037be5b70000000 0xc01ffc7fe0000000 0xb007ff1ff8000000

def z314 : W := mkw 0x83dbfc101ffbf783 0xe0f6ff0407fefde0 0xfffffc001fffff83 0x3fffff0007ffffe0

def z315 : W := mkw 0x00fefbedc4120002 0x003fbefb71048000 0xfbfffffffe1f0003 0xfeffffffff87c000

def z316 : W := mkw 0x812503f013203780 0x604940fc04c80de0 0x6c0303f011003f81 0x5b00c0fc04400fe0

def z317 : W := mkw 0x8100001002203780 0x6040000400880de0 0x0400000000003f80 0x0100000000000fe0

def z318 : W := mkw 0x81fffbfddb802680 0x607ffeff76e009a0 0xf9fffffffe000600 0xfe7fffffff800180

def z319 : W := mkw 0x4000000200040840 0x1000000080010210 0xbe00e38f101f3e73 0xef8038e3c407cf9c

def z320 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfbfffc01ffffc07f 0xbeffff007ffff01f

def z321 : W := mkw 0x0040a00900000000 0x0010280240000000 0x8000e00f00000000 0xa0003803c0000000

def z322 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x17e0c30e1e1f3e73 0x05f830c38787cf9c

def z323 : W := mkw 0x812002b002002680 0x604800ac008009a0 0x000000b000000600 0x0000002c00000180

def z324 : W := mkw 0x812403fdc2203780 0x604900ff70880de0 0x040003ffe0003f80 0xc10000fff8000fe0

def z325 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x51ffdc000ffcc002 0x147ff70003ff3000

def z326 : W := mkw 0x02dbfc0ddddbc003 0x80b6ff037776f000 0xfbfffc0fffffc003 0xbeffff03fffff000

def z327 : W := mkw 0x0093000019800000 0x0024c00006600000 0x401f000001e00000 0x1007c00000780000

def z328 : W := mkw 0x83fbfeb01fdbe683 0xe0feffac07f6f9a0 0xfbfffcb01fffc603 0x3effff2c07fff180

def z329 : W := mkw 0x0008500000000000 0x0002140000000000 0xd81cd00000000000 0x3607340000000000

def z330 : W := mkw 0x02fbfe891ddbc003 0x80beffa24776f000 0xfbffff8f1fffc003 0xfeffffe3c7fff000

def z331 : W := mkw 0x4000000206162c62 0x5000000081858b18 0xaf0020811e1f3e73 0xebc008204787cf9c

def z332 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x501cd34e81fcf98e 0x140734d3a07f3e63

def z333 : W := mkw 0x4060a28b02042c60 0x501828a2c0810b18 0xbce0e38f00003e70 0xef3838e3c0000f9c

def z334 : W := mkw 0x604cf94fc06c9949 0x18133e53f01b2652 0xde1cff4fe1fcf9cf 0xf7873fd3f87f3e73

def z335 : W := mkw 0xc1b703fb1ba43fe0 0x706dc0fec6e90ff8 0x7dff03ff1fe03ff3 0xdf7fc0ffc7f80ffc

def z336 : W := mkw 0xa19f517499e89389 0x2867d45d267a24e2 0x401f107081e0c18c 0x1007c41c20783063

def z337 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x15e0c38f0e1c3e72 0xc57830e3c3870f9c

def z338 : W := mkw 0x0241a4001ddbc003 0x809069000776f000 0xbbe0e0001fffc003 0x2ef8380007fff000

def z339 : W := mkw 0x4020028b02042c60 0x500800a2c0810b18 0xae00238f10033e71 0xeb8008e3c400cf9c

def z340 : W := mkw 0x81f7a3f91fb237a2 0x607de8fe47ec8de8 0x7dff23f11fe33fb3 0x5f7fc8fc47f8cfec

def z341 : W := mkw 0x9001001031000294 0x240040040c4000a5 0x6c0300f1f10007fd 0xdb00c03c7c4001ff

def z342 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00000000000041 0xe380000000000010

def z343 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc409fffc1cf 0xffffff1027fff073

def z344 : W := mkw 0x606cf3cf867ebd6b 0x581b3cf3e19faf5a 0xbffce38f1eff3e73 0xefff38e3c7bfcf9c

def z345 : W := mkw 0x4000000202042c60 0x5000000080810b18 0x0400000000003e70 0x0100000000000f9c

def z346 : W := mkw 0x00040164c0000000 0x0001005930000000 0x00000070e0000000 0x0000001c38000000

def z347 : W := mkw 0x5040a40b24174876 0x94102902c905d21d 0x8200fc0fe01fc07c 0xa0803f03f807f01f

def z348 : W := mkw 0x8093001019800280 0x2024c004066000a0 0x7dff00f01fe00783 0x5f7fc03c07f801e0

def z349 : W := mkw 0x8197017019a01380 0x2065c05c066804e0 0x5c1f037001e03983 0x5707c0dc00780e60

def z350 : W := mkw 0x8001001011000280 0x20004004044000a0 0x4003007001000180 0x1000c01c00400060

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x20032cb160000000 0x0800cb2c58000000

def z352 : W := mkw 0x02dafc00045bc003 0x80b6bf000116f000 0xfafffc00001fc000 0x3ebfff000007f000

def z353 : W := mkw 0x0008500000488001 0x0002140000122000 0x101cc00000fc0002 0x04073000003f0000

def z354 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xc21cd04e81fcc1cc 0xb0873413a07f3073

def z355 : W := mkw 0x029a580008c88001 0x00a6960002322000 0x001c000000e00000 0x0007000000380000

def z356 : W := mkw 0x009b500019c88001 0x0026d40006722000 0xfbffd0001ffcc003 0x3efff40007ff3000

def z357 : W := mkw 0x90f3aeb971014294 0xa43cebae5c4050a5 0xeee33cf1f103c7fd 0xfbb8cf3c7c40f1ff

def z358 : W := mkw 0x910104103ba17794 0xe44041040ee85de5 0xef033cf1ffe3ffff 0xfbc0cf3c7ff8ffff

def z359 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7fff03f01fe3ffff 0x5fffc0fc07f8ffff

def z360 : W := mkw 0x9000001020000294 0x24000004080000a5 0xae0020f1f00307fd 0xeb80083c7c00c1ff

def z361 : W := mkw 0x0000040000014000 0x8000010000005000 0x82003c000003c000 0x20800f000000f000

def z362 : W := mkw 0x6048f00f845e886b 0x18123c03e117a21a 0x8200f00f801fc07c 0xa0803c03e007f01f

def z363 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfeffffffe100c1cd 0xffbffffff8403073

def z364 : W := mkw 0x02d3ac001d934002 0x80b4eb000764d000 0xebe33c001f03c001 0x3af8cf0007c0f000

def z365 : W := mkw 0x03fefbe00efab503 0x40ffbef803bead40 0x11fcc3000efc3802 0x047f30c003bf0e00

def z366 : W := mkw 0x4020028b02042c60 0x500800a2c0810b18 0x3de0038f1e003e73 0xcf7800e3c7800f9c

def z367 : W := mkw 0x029b5c0019c9c001 0x80a6d70006727000 0xda1fdc0001fcc003 0x3687f700007f3000

def z368 : W := mkw 0xe19f517699ec9bc9 0x3867d45da67b26f2 0xde1fd37e81fcf9cf 0xf787f4dfa07f3e73

def z369 : W := mkw 0x0248fc00045bc003 0x80923f000116f000 0xda1cfc0001ffc003 0x36873f00007ff000

def z370 : W := mkw 0x0000000000488001 0x0000000000122000 0x0200000001fcc003 0x00800000007f3000

def z371 : W := mkw 0xc161a29b1fb63fe2 0x705868a6c7ed8ff8 0xbfe0e38f1fff3ff3 0xeff838e3c7ffcffc

def z372 : W := mkw 0x4040a00b04160862 0x10102802c1058218 0xbbe0e00f1e1f0073 0xaef83803c787c01c

def z373 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x3de0c38e1e1c3e03 0x4f7830e387870f80

def z374 : W := mkw 0x0092000000000000 0x0024800000000000 0x78ff000000000000 0x1e3fc00000000000

def z375 : W := mkw 0x0000000dc0000000 0x0000000370000000 0x0000000fe0000000 0x80000003f8000000

def z376 : W := mkw 0x604cf146847e994b 0x18133c51a11fa652 0xfffcf34e9ffff9cf 0xffff3cd3a7fffe73

def z377 : W := mkw 0x819f5974d9a01380 0x2067d65d366804e0 0x401f1c70e1e00180 0x1007c71c38780060

def z378 : W := mkw 0x02ffffeddd934002 0x80bffffb7764d000 0xf9fffffffe030000 0xfe7fffffff80c000

def z379 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0xb8e3efbf60000000 0xee38fbefd8000000

def z380 : W := mkw 0x4064a3efc6162c62 0x501928fbf1858b18 0xbfe0e3fffe1f3e73 0xeff838ffff87cf9c

def z381 : W := mkw 0x0001000011000000 0x0000400004400000 0x6803000011000001 0x1a00c00004400000

def z382 : W := mkw 0x602403cf82243d68 0x580900f3e0890f5a 0x040003cf80003ffc 0xc10000f3e0000fff

def z383 : W := mkw 0x02fbfe801fdbe403 0xc0beffa007f6f900 0xffffff801ffffe03 0x7fffffe007ffff80

def z384 : W := mkw 0x62dffd469dffd94b 0x98b7ff51a77ff652 0xfbffff0e1ffff803 0x3effffc387fffe00

def z385 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x46031c70f103c7fd 0x1180c71c3c40f1ff

def z386 : W := mkw 0x8001001011000280 0x20004004044000a0 0xec033cf1f1000781 0xfb00cf3c7c4001e0

def z387 : W := mkw 0x0040a00004120002 0x0010280001048000 0xbfe0e0811e1f0673 0xeff838204787c19c

def z388 : W := mkw 0x8001001011000280 0x20004004044000a0 0x0400000011000781 0x01000000044001e0

def z389 : W := mkw 0x629f5d4699edd949 0x98a7d751a67b7652 0xde1fdf4e81fcf9cf 0xf787f7d3a07f3e73

def z390 : W := mkw 0x8197017019a01380 0x2065c05c066804e0 0x79ff00701fe00183 0x1e7fc01c07f80060

def z391 : W := mkw 0x40fefbefc4160862 0x103fbefbf1058218 0xfaffffffe01f0070 0xfebffffff807c01c

def z392 : W := mkw 0x400c514680040840 0x10031451a0010210 0xde1cd34e801c3843 0xf78734d3a0070e10

def z393 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x15fc03001fe03f83 0x057f00c007f80fe0

def z394 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x24032cf1f00307fc 0xc900cb3c7c00c1ff

def z395 : W := mkw 0x83f7aff01fb37782 0xe0fdebfc07ecdde0 0x7dff2ff01fe33f83 0x5f7fcbfc07f8cfe0

def z396 : W := mkw 0x9093041039814294 0xa424c1040e6050a5 0xffff3cf1ffe3c7ff 0xffffcf3c7ff8f1ff

def z397 : W := mkw 0x4048f80fc4160862 0x10123e03f1058218 0x8200fc0fe01f0070 0xa0803f03f807c01c

def z398 : W := mkw 0x42f3ae8b1f976c62 0xd0bceba2c7e5db18 0xbfe3ef8f1e1f3e73 0xeff8fbe3c787cf9c

def z399 : W := mkw 0x812403f002203780 0x604900fc00880de0 0x5c1c03f001e03f83 0x570700fc00780fe0

def z400 : W := mkw 0x40f6a3eb06162c62 0x503da8fac1858b18 0xffffe3ff1e1f3e73 0xfffff8ffc787cf9c

def z401 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xa3e0e08f1e1f0670 0xa8f83823c787c19c

def z402 : W := mkw 0x0000000006122422 0x4000000001848908 0x010000001e030630 0x004000000780c18c

def z403 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x86003c01f103c7fd 0xa1800f007c40f1ff

def z404 : W := mkw 0x1000040020014014 0x8400010008005005 0xae003c81f003c67d 0xeb800f207c00f19f

def z405 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x31ffec001eff0002 0x0c7ffb0007bfc000

def z406 : W := mkw 0x81f7a3f91ba03780 0x607de8fe46e80de0 0xfdffe3ff1fe03f83 0xff7ff8ffc7f80fe0

def z407 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x8600d34e801cf9cc 0xe18034d3a0073e73

def z408 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8ffff0e00000000 0x3e3fffc380000000

def z409 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xae0020811103c7fd 0xeb8008204440f1ff

def z410 : W := mkw 0xd021069b33056ef4 0xf40841a6ccc15bbd 0xee033ffff103fffd 0xfb80cffffc40ffff

def z411 : W := mkw 0x0020028902002420 0x400800a240800908 0x0000008100000630 0x000000204000018c

def z412 : W := mkw 0x006cfbedc0000000 0x001b3efb70000000 0x8000ffffe0000000 0xe0003ffff8000000

def z413 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1cf3cf91ffffff 0xff873cf3e47fffff

def z414 : W := mkw 0x81f3aab95b802680 0x607ceaae56e009a0 0x21e32cb17e000600 0x0878cb2c5f800180

def z415 : W := mkw 0x92d3ac103d934296 0xa4b4eb040f64d0a5 0x21e32cb17e030630 0x0878cb2c5f80c18c

def z416 : W := mkw 0x009a580000000000 0x0026960000000000 0x401f1c0000000000 0x1007c70000000000

def z417 : W := mkw 0x02fefbedccda8003 0x00bfbefb7336a000 0x11fcc30e0efc0002 0x047f30c383bf0000

def z418 : W := mkw 0x900d5554b1014294 0xa40355552c4050a5 0xfe1ffffff103c7fd 0xff87fffffc40f1ff

def z419 : W := mkw 0x4020028206162c62 0x500800a081858b18 0x3fe003801e1f3e73 0x4ff800e00787cf9c

def z420 : W := mkw 0x6060a28b067ebd6b 0x581828a2c19faf5a 0xbfe0e38f1fffffff 0xeff838e3c7ffffff

def z421 : W := mkw 0x6004014680241948 0x18010051a0090652 0x0000030e00003800 0x000000c380000e00

def z422 : W := mkw 0x200c514480689109 0x08031451201a2442 0x001c000000e00000 0x0007000000380000

def z423 : W := mkw 0x0041a40015134002 0x801069000544d000 0xfbe3fc001f1fc003 0x3ef8ff0007c7f000

def z424 : W := mkw 0x910104103ba17794 0xe44041040ee85de5 0x070000001fe3ffff 0x01c0000007f8ffff

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8033c0000000000 0x3a00cf0000000000

def z426 : W := mkw 0x000c514480201100 0x0003145120080440 0xdc1cd34e81e03983 0xf70734d3a0780e60

def z427 : W := mkw 0x00fffbedd9800000 0x003ffefb76600000 0xf9ffffffffe00003 0xfe7ffffffff80000

def z428 : W := mkw 0x00fafa8900000000 0x003ebea240000000 0xf8ffff8f00000000 0xfe3fffe3c0000000

def z429 : W := mkw 0xd2fbfe9b3fdfeef7 0xf4beffa6cff7fbbd 0xffffffffffffffff 0xffffffffffffffff

def z430 : W := mkw 0x229f5d4499e9d109 0x88a7d751267a7442 0x401f1c4081e0c18c 0x1007c71020783063

def z431 : W := mkw 0x0004014000201100 0x0001005000080440 0x0400034000003980 0x410000d000000e60

def z432 : W := mkw 0xe1fff3ff9ffebfeb 0x787ffcffe7ffaffa 0xfffff3ff9fffffff 0xfffffcffe7ffffff

def z433 : W := mkw 0xf00d5556b16ddbdd 0xbc035555ac5b76f7 0xde1fdf7ee1fcf9cf 0xf787f7dfb87f3e73

def z434 : W := mkw 0x4268fe8b065fec63 0xd09a3fa2c197fb18 0xbfe0ff8f1e1ffe73 0xeff83fe3c787ff9c

def z435 : W := mkw 0x020954001ddbc003 0x808255000776f000 0xdb1cd0001fffc003 0x36c7340007fff000

def z436 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00008010000601 0x4b00002004000180

def z437 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x13fcc0001fffc003 0x04ff300007fff000

def z438 : W := mkw 0x02fbfea95ddbc003 0x80beffaa5776f000 0xfbfffcb17fffc003 0x3effff2c5ffff000

def z439 : W := mkw 0x70085406a04dc85d 0x9c021501a8137217 0x8200fc0fe01fc07c 0xa0803f03f807f01f

def z440 : W := mkw 0x41f6a3eb0eb63d62 0x507da8fac3ad8f58 0xbffce38f1eff3e73 0xefff38e3c7bfcf9c

def z441 : W := mkw 0x402403efc2042c60 0x500900fbf0810b18 0x040003ffe0003e70 0xc10000fff8000f9c

def z442 : W := mkw 0x6004014680241948 0x18010051a0090652 0x9e00c34e801c39cf 0xe78030d3a0070e73

def z443 : W := mkw 0x0040a00004120002 0x0010280001048000 0x8200e000001f0000 0x208038000007c000

def z444 : W := mkw 0xf00d5556b16ddbdd 0xbc035555ac5b76f7 0xde1cd34e91ffffff 0xf78734d3a47fffff

def z445 : W := mkw 0x600c5146804c8849 0x18031451a0132212 0xda1cd34e801cc04c 0xf68734d3a0073013

def z446 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x921cd30e80fcf84e 0xa48734c3a03f3e13

def z447 : W := mkw 0x60040146806c9949 0x18010051a01b2652 0x0600034e81fcf9cf 0xc18000d3a07f3e73

def z448 : W := mkw 0x029f5d64d9c9c001 0x80a7d75936727000 0x401f1c70e1e0c000 0x1007c71c38783000

def z449 : W := mkw 0x606cf3cf806c9949 0x181b3cf3e01b2652 0xfefcf3cf81fcf9cf 0xffbf3cf3e07f3e73

def z450 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x90fcff0fe0000000 0xa43f3fc3f8000000

def z451 : W := mkw 0x020104001d934002 0x808041000764d000 0x010000001e030000 0x004000000780c000

def z452 : W := mkw 0x81fefbfdc2203780 0x607fbeff70880de0 0xfcffffffe0003f80 0xff3ffffff8000fe0

def z453 : W := mkw 0x0249fc00155bc003 0x80927f000556f000 0xea03fc00111fc001 0x3a80ff000447f000

def z454 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe3fffffe1f3e73 0xfff8ffffff87cf9c

def z455 : W := mkw 0x0040a00004120002 0x0010280001048000 0x21e020001e030000 0x087808000780c000

def z456 : W := mkw 0x00dbf80019800000 0x0036fe0006600000 0xf9fffc001fe00003 0x3e7fff0007f80000

def z457 : W := mkw 0x40fefbefc6162c62 0x503fbefbf1858b18 0xbffce38f1e1f3e73 0xefff38e3c787cf9c

def z458 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xd81cd34e80fc3802 0xf60734d3a03f0e00

def z459 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x6c032cf1710307b1 0x5b00cb3c5c40c1ec

def z460 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0xe8e33cf1e0000000 0xfa38cf3c78000000

def z461 : W := mkw 0x60085006806c9949 0x18021401a01b2652 0x8600d00e81fcf9cf 0xa1803403a07f3e73

def z462 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbbe0e30e1e1f3803 0x2ef838c38787ce00

def z463 : W := mkw 0x60085006804c8849 0x18021401a0132212 0xce00d04e811cc1cd 0xf3803413a0473073

def z464 : W := mkw 0x0060a28900000000 0x001828a240000000 0x20e0208100000000 0x0838082040000000

def z465 : W := mkw 0x00def94480000000 0x0037be5120000000 0xf8ffff4e80000000 0xfe3fffd3a0000000

def z466 : W := mkw 0x000c514000689101 0x00031450001a2440 0xde1cd34001fcf983 0x778734d0007f3e60

def z467 : W := mkw 0x61be53e68aecbd49 0x586f94f9a2bb2f52 0xdffcd34e8ffcf9cf 0xf7ff34d3a3ff3e73

def z468 : W := mkw 0x4248fc0b045fc863 0x90923f02c117f218 0x8200fc0f001fc070 0xa0803f03c007f01c

def z469 : W := mkw 0x40fefbefc0040840 0x103fbefbf0010210 0xfeffffffe01c3843 0xffbffffff8070e10

def z470 : W := mkw 0x60085006804c8849 0x18021401a0132212 0x0000c00e001c0000 0x0000300380070000

def z471 : W := mkw 0x0040a00000000000 0x0010280000000000 0xb8e0e00000000000 0x2e38380000000000

def z472 : W := mkw 0xf0040156a0241bdc 0x3c010055a80906f7 0x040003ffe0003ffc 0xc10000fff8000fff

def z473 : W := mkw 0x5060a68b26176c76 0xd41829a2c985db1d 0xbfe0ff8ffe1ffe7f 0xeff83fe3ff87ff9f

def z474 : W := mkw 0x002403e000000000 0x000900f800000000 0x000003f000000000 0x400000fc00000000

def z475 : W := mkw 0x920104103ddbc297 0xa48041040f76f0a5 0xef033cf1ffffc7ff 0xfbc0cf3c7ffff1ff

def z476 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x461c104081fcf9cf 0x11870410207f3e73

def z477 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xb9e0e38f0e1c3802 0xee7838e3c3870e00

def z478 : W := mkw 0x40085002004c8841 0x1002140080132210 0xde1cd30e01fcf843 0xf78734c3807f3e10

def z479 : W := mkw 0x83b707f01ffbf783 0xe0edc1fc07fefde0 0x7fff03f01fffff83 0x5fffc0fc07ffffe0

def z480 : W := mkw 0x02dffd449ddbc003 0x80b7ff512776f000 0xfbffff4e9fffc003 0xfeffffd3a7fff000

def z481 : W := mkw 0x929b5c1039c9c295 0xa4a6d7040e7270a5 0x401f1c70e1e0c18c 0x1007c71c38783063

def z482 : W := mkw 0x8101001019a01380 0x20404004066804e0 0x0000000001e00180 0x0000000000780060

def z483 : W := mkw 0x000c514480000000 0x0003145120000000 0xde1cd34e8100c1cd 0xf78734d3a0403073

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x400010408100c18c 0x1000041020403063

def z485 : W := mkw 0x4000000206162c62 0x5000000081858b18 0x010000000e1c3802 0x0040000003870e00

def z486 : W := mkw 0x8001001011000280 0x20004004044000a0 0x200300b010000600 0x0800c02c04000180

def z487 : W := mkw 0x81fffbf01ba03780 0x607ffefc06e80de0 0xfdfffff01fe03f83 0x7f7ffffc07f80fe0

def z488 : W := mkw 0x81b703f01b802680 0x606dc0fc06e009a0 0x79ff03f01e000600 0x5e7fc0fc07800180

def z489 : W := mkw 0x0060a28902002400 0x401828a240800900 0xbde0e38f1e003e03 0xef7838e3c7800f80

def z490 : W := mkw 0xa1bf53f49be8b789 0x686fd4fd26fa2de2 0x7dff13f09fe0ff8f 0x5f7fc4fc27f83fe3

def z491 : W := mkw 0x8001001011000280 0x20004004044000a0 0xee0310f09100c7cd 0xfb80c43c244031f3

def z492 : W := mkw 0x00f6abe940000000 0x003daafa50000000 0x78ff2ff160000000 0x5e3fcbfc58000000

def z493 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0x00e0000000000000 0x0038000000000000

def z494 : W := mkw 0x00b603e000000000 0x002d80f800000000 0xf8ff3ff1e0000000 0xfe3fcffc78000000

def z495 : W := mkw 0x02d2a8000c920002 0x00b4aa0003248000 0x01e000000e000000 0x0078000003800000

def z496 : W := mkw 0x42fbfe8b1fdfec63 0xd0beffa2c7f7fb18 0xfbffff0e1ffff803 0x3effffc387fffe00

def z497 : W := mkw 0x020104001ddbc003 0x808041000776f000 0xeb033c001fffc003 0x3ac0cf0007fff000

def z498 : W := mkw 0x700c5546a06dd95d 0x9c031551a81b7657 0xde1cff4fe1fff9ff 0xf7873fd3f87ffe7f

def z499 : W := mkw 0x90f3aeb971014294 0xa43cebae5c4050a5 0x20e32cb170030630 0x0838cb2c5c00c18c

def z500 : W := mkw 0x902507fdf1014294 0xa40941ff7c4050a5 0xee033ffff103c7fd 0xfb80cffffc40f1ff

def z501 : W := mkw 0x4020028b02042c60 0x500800a2c0810b18 0x9e00c38f001c3e73 0xe78030e3c0070f9c

def z502 : W := mkw 0x60fefbefc06c9949 0x183fbefbf01b2652 0xf8ffffffe0fc3802 0xfe3ffffff83f0e00

def z503 : W := mkw 0x60fefbefc06c9949 0x183fbefbf01b2652 0x10fcc30e00fc3802 0x043f30c3803f0e00

def z504 : W := mkw 0x0001040011014000 0x8000410004405000 0x20032c0010030000 0x0800cb000400c000

def z505 : W := mkw 0x02dffd401dfbd103 0x80b7ff50077ef440 0xffffff401ffff983 0x7fffffd007fffe60

def z506 : W := mkw 0x00daf80000000000 0x0036be0000000000 0x10fcc00000000000 0x043f300000000000

def z507 : W := mkw 0x029304001ddbc003 0x80a4c1000776f000 0x7bff00001fffc003 0x1effc00007fff000

def z508 : W := mkw 0x010000000aa03500 0x4040000002a80d40 0x010000000ee03802 0x0040000003b80e00

def z509 : W := mkw 0x929b5c1039c9c295 0xa4a6d7040e7270a5 0xee1f3cf1f1e3c7fd 0xfb87cf3c7c78f1ff

def z510 : W := mkw 0x00f6a3e900000000 0x003da8fa40000000 0xf8ffe3ff00000000 0xfe3ff8ffc0000000

def z511 : W := mkw 0x02ffffedd9c9c001 0x80bffffb76727000 0xf8ffffffe1e0c000 0xfe3ffffff8783000

def z512 : W := mkw 0x92d3ac103d934296 0xa4b4eb040f64d0a5 0xefe33cf1ff03c7fd 0xfbf8cf3c7fc0f1ff

def z513 : W := mkw 0x000c514480000000 0x0003145120000000 0xf81fffffe0000000 0xfe07fffff8000000

def z514 : W := mkw 0x4020028202042c40 0x500800a080810b10 0xbfe0c38e1e1c3e43 0xeff830e387870f90

def z515 : W := mkw 0x02ffffeddddbc003 0x80bffffb7776f000 0xfbffff0e1fffc003 0x3effffc387fff000

def z516 : W := mkw 0xc3fffffb1fffffe3 0xf0fffffec7fffff8 0xffffffff1ffffff3 0xffffffffc7fffffc

def z517 : W := mkw 0x812403f002203780 0x604900fc00880de0 0x3de003f01e003f83 0x4f7800fc07800fe0

def z518 : W := mkw 0x002c53edc0000000 0x000b14fb70000000 0xd81cd3ffe0000000 0xf60734fff8000000

def z519 : W := mkw 0x92fffffdfddbc297 0xa4bfffff7f76f0a5 0xffffffffffffc7ff 0xfffffffffffff1ff

def z520 : W := mkw 0x9061a699371366b6 0xe41869a64dc4d9ad 0x21e32cb17e030630 0x0878cb2c5f80c18c

def z521 : W := mkw 0x62def9468cfe994b 0x18b7be51a33fa652 0x11fcc30e0efc3802 0x047f30c383bf0e00

def z522 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1fffffe1fcf9cf 0xff87fffff87f3e73

def z523 : W := mkw 0xd041a41b35174af6 0xb4106906cd45d2bd 0xee03fcfff11fc7fd 0xfb80ff3ffc47f1ff

def z524 : W := mkw 0x0093000019800000 0x0024c00006600000 0x21e300001e000000 0x0878c00007800000

def z525 : W := mkw 0x81b302b01b802680 0x606cc0ac06e009a0 0x79ff00b01fe00603 0x1e7fc02c07f80180

def z526 : W := mkw 0x6000000680040848 0x18000001a0010212 0x0000000e8000004c 0x80000003a0000013

def z527 : W := mkw 0xe1b703f21becbfc9 0x786dc0fc86fb2ff2 0x7fff03f01ffcffcf 0x5fffc0fc07ff3ff3

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x581c000001e00003 0x1607000000780000

def z529 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xa2033cb1f003c67c 0xa880cf2c7c00f19f

def z530 : W := mkw 0x0000000004120002 0x0000000001048000 0x030000001e1f0003 0x00c000000787c000

def z531 : W := mkw 0x812503f01ba03780 0x604940fc06e80de0 0x050003f01fe03f83 0x414000fc07f80fe0

def z532 : W := mkw 0x602c53efc06c9949 0x180b14fbf01b2652 0xde1cd3ffe1fcf9cf 0xf78734fff87f3e73

def z533 : W := mkw 0x0092082040000000 0x0024820810000000 0x00030c3060000000 0x0000c30c18000000

def z534 : W := mkw 0x8005015011201380 0x20014054044804e0 0x7c1f03f011e03f83 0x5f07c0fc04780fe0

def z535 : W := mkw 0x0060a28900000000 0x001828a240000000 0x10e0c30e00000000 0x043830c380000000

def z536 : W := mkw 0x91fffffdfba17794 0xe47fffff7ee85de5 0xffffffffffe3ffff 0xfffffffffff8ffff

def z537 : W := mkw 0x9061a699371366b6 0xe41869a64dc4d9ad 0xefe33cf1ff03c7fd 0xfbf8cf3c7fc0f1ff

def z538 : W := mkw 0x00daf80000000000 0x0036be0000000000 0xf8fffcf1e0000000 0xfe3fff3c78000000

def z539 : W := mkw 0x000954001149c001 0x8002550004527000 0xfa1ffc0011ffc003 0x3e87ff00047ff000

def z540 : W := mkw 0x0060a28904120002 0x001828a241048000 0xbbe0e38f1e1f0003 0xeef838e3c787c000

def z541 : W := mkw 0x0020028002002400 0x400800a000800900 0x11e003000e003802 0x047800c003800e00

def z542 : W := mkw 0x62ffffcf9ffffd6b 0xd8bffff3e7ffff5a 0xffffffcf9fffffff 0xfffffff3e7ffffff

def z543 : W := mkw 0x00b603edc0000000 0x002d80fb70000000 0x78ff03ffe0000000 0xde3fc0fff8000000

def z544 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xda1cd30e01fcf803 0x368734c3807f3e00

def z545 : W := mkw 0x60085006804c8849 0x18021401a0132212 0x9e00d30e801cf84f 0xe78034c3a0073e13

def z546 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x25e0238f1e033e70 0xc97808e3c780cf9c

def z547 : W := mkw 0x9000001020000294 0x24000004080000a5 0xec033cf1e00007fc 0xfb00cf3c780001ff

def z548 : W := mkw 0x81bf5bf4dba03780 0x606fd6fd36e80de0 0x7dff1ff0ffe03f83 0x5f7fc7fc3ff80fe0

def z549 : W := mkw 0xd001041237176ef6 0xf40041048dc5dbbd 0xef033cf1ff1fffff 0xfbc0cf3c7fc7ffff

def z550 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x31e0e38f1e1f3e32 0x0c7838e3c787cf8c

def z551 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xb8fce38f00000000 0xee3f38e3c0000000

def z552 : W := mkw 0x40f2aaab46162c62 0x503caaaad1858b18 0xbfe3efbf7e1f3e73 0xeff8fbefdf87cf9c

def z553 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xf9fffc000efc0002 0x3e7fff0003bf0000

def z554 : W := mkw 0x420104021fdfec63 0xd080410087f7fb18 0x070000001ffffe73 0x01c0000007ffff9c

def z555 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x60ff3cf1e0000000 0x183fcf3c78000000

def z556 : W := mkw 0x4040a00206162c62 0x5010280081858b18 0xbfe0e0001e1f3e73 0x2ff838000787cf9c

def z557 : W := mkw 0x912507f033217794 0xe44941fc0cc85de5 0xee033ff1f103fffd 0xfb80cffc7c40ffff

def z558 : W := mkw 0x90fefbfde0000294 0x243fbeff780000a5 0xfcffffffe00007fc 0xff3ffffff80001ff

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0xee0030c19103c7fd 0xfb800c306440f1ff

def z560 : W := mkw 0x0020028002002400 0x400800a000800900 0xbfe023811e033e73 0xeff808e04780cf9c

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x39e000001e000003 0x0e78000007800000

def z562 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xc21ffc0001ffc000 0x3087ff00007ff000

def z563 : W := mkw 0x0201040019c9c001 0x8080410006727000 0x0000000001e0c000 0x0000000000783000

def z564 : W := mkw 0x0040a00904120022 0x0010280241048008 0x0000200100030030 0x000008004000c00c

def z565 : W := mkw 0x1000000020000014 0x0400000008000005 0x00000001e000007c 0x800000007800001f

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800208100000000 0xea00082040000000

def z567 : W := mkw 0x8001001011000280 0x20004004044000a0 0xee0320f1110307f1 0xfb80c83c4440c1fc

def z568 : W := mkw 0x000c514480488001 0x0003145120122000 0xda1cd34e81fcc003 0xf68734d3a07f3000

def z569 : W := mkw 0x600c514680241948 0x18031451a0090652 0xdc1cd34e800039cc 0xf70734d3a0000e73

def z570 : W := mkw 0x01fefbedcaa03500 0x407fbefb72a80d40 0x11fcc30e0ee03802 0x047f30c383b80e00

def z571 : W := mkw 0x81bf53f01be8b781 0x606fd4fc06fa2de0 0xffffd3f01ffcff83 0x7ffff4fc07ff3fe0

def z572 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x00030c3060000000 0x0000c30c18000000

def z573 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xee033c001103c7fd 0x3b80cf000440f1ff

def z574 : W := mkw 0x002403edc0000000 0x000900fb70000000 0x0000030e00000000 0x000000c380000000

def z575 : W := mkw 0x4064a3cb06363d62 0x501928f2c18d8f58 0xfffce3cf1fff3ff3 0xffff38f3c7ffcffc

def z576 : W := mkw 0x83fffffddffbf783 0xe0ffffff77fefde0 0xffffffffffffff83 0xffffffffffffffe0

def z577 : W := mkw 0x9000001020000294 0x24000004080000a5 0x04000000000007fc 0x01000000000001ff

def z578 : W := mkw 0x42dbfc021ddfc843 0x90b6ff008777f210 0xffffff0e1ffff843 0xffffffc387fffe10

def z579 : W := mkw 0x200c514480689109 0x08031451201a2442 0xd81cd34e81e0c18c 0xf60734d3a0783063

def z580 : W := mkw 0x4000000206162c62 0x5000000081858b18 0x9f00c30e1e1f3e73 0xe7c030c38787cf9c

def z581 : W := mkw 0x0097014019a01100 0x0025c05006680440 0x7dff03401fe03983 0x5f7fc0d007f80e60

def z582 : W := mkw 0x0248fc00045bc003 0x80923f000116f000 0xbbe0fc001e1fc003 0x2ef83f000787f000

def z583 : W := mkw 0x4261a68b1fdfec63 0xd09869a2c7f7fb18 0xbfe0e38f1ffffe73 0xeff838e3c7ffff9c

def z584 : W := mkw 0x0001040011014000 0x8000410004405000 0xee033c811103c671 0xfb80cf204440f19c

def z585 : W := mkw 0x0008500000488001 0x0002140000122000 0x401c100001e0c000 0x1007040000783000

def z586 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x93e0e30f0e1f3872 0xa4f838c3c387ce1c

def z587 : W := mkw 0x60000002006c9949 0x18000000801b2652 0x0000000000fc3802 0x00000000003f0e00

def z588 : W := mkw 0x0093040019814000 0x8024c10006605000 0xfbff3c001fe3c003 0x3effcf0007f8f000

def z589 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xea033cb17103c631 0x3a80cf2c5c40f18c

def z590 : W := mkw 0xe1bf53f69becbfc9 0x786fd4fda6fb2ff2 0x7dffc3fe1ffc3f83 0x5f7ff0ff87ff0fe0

def z591 : W := mkw 0x9000001020000294 0x24000004080000a5 0x000000b160000630 0x0000002c5800018c

def z592 : W := mkw 0x0004014000201100 0x0001005000080440 0x101c030000e03802 0x040700c000380e00

def z593 : W := mkw 0x02d3ac001d934002 0x80b4eb000764d000 0xbbe3ec001e1f0003 0x2ef8fb000787c000

def z594 : W := mkw 0x609f514699ec9949 0x1827d451a67b2652 0xffffd34e9ffcf9cf 0xfffff4d3a7ff3e73

def z595 : W := mkw 0x839f5d7019e9d381 0xa0e7d75c067a74e0 0x401f1c7001e0c180 0x1007c71c00783060

def z596 : W := mkw 0x0196016008a01100 0x0065805802280440 0x001c000000e00000 0x0007000000380000

def z597 : W := mkw 0x0060a28906122422 0x401828a241848908 0x01e000000e000000 0x0078000003800000

def z598 : W := mkw 0x0060a28900000000 0x001828a240000000 0xbee0e38f10030671 0xefb838e3c400c19c

def z599 : W := mkw 0x40fefbefc6162c62 0x503fbefbf1858b18 0x11fcc30e0e1c3802 0x047f30c383870e00

def z600 : W := mkw 0x9049fc1df1014294 0xa4127f077c4050a5 0xee03fcfff103c7fd 0xfb80ff3ffc40f1ff

def z601 : W := mkw 0x4068fa8fc6162c62 0x501a3ea3f1858b18 0xbfe0ff8ffe1f3e73 0xeff83fe3ff87cf9c

def z602 : W := mkw 0x4000000200040840 0x1000000080010210 0x0400030e00003840 0xc10000c380000e10

def z603 : W := mkw 0x6004014680241948 0x18010051a0090652 0x5c1c034e81e039cf 0xd70700d3a0780e73

def z604 : W := mkw 0x22dffd449dfbd10b 0x88b7ff51277ef442 0xfbfffc409fffc18f 0x3effff1027fff063

def z605 : W := mkw 0x81b302b01b802680 0x606cc0ac06e009a0 0x3de303b01e003e03 0x4f78c0ec07800f80

def z606 : W := mkw 0x0000000002002400 0x4000000000800900 0x050000001e003e03 0x0140000007800f80

def z607 : W := mkw 0x4000000200040840 0x1000000080010210 0x1000c30e001c3802 0x040030c380070e00

def z608 : W := mkw 0xf1bf57f6bbedffdd 0xfc6fd5fdaefb7ff7 0xffffffffffffffff 0xffffffffffffffff

def z609 : W := mkw 0x1000040020014014 0x8400010008005005 0x00002c0160030030 0x00000b005800c00c

def z610 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x5c1cc34e01fc3983 0x570730d3807f0e60

def z611 : W := mkw 0x029b5c0019c9c001 0x80a6d70006727000 0x79ff1c001fe0c003 0x1e7fc70007f83000

def z612 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x060000f1f103c7fd 0xc180003c7c40f1ff

def z613 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x50ffdf7ee0000000 0x143ff7dfb8000000

def z614 : W := mkw 0x0249fc001ddbc003 0x80927f000776f000 0x8300fc001fffc003 0x20c03f0007fff000

def z615 : W := mkw 0x4061a68b17176c62 0xd01869a2c5c5db18 0xffe3ff8f1f1ffe73 0xfff8ffe3c7c7ff9c

def z616 : W := mkw 0xc1f3a2bb1f962ee2 0x707ce8aec7e58bb8 0xbfe3e3bf1e1f3e73 0xeff8f8efc787cf9c

def z617 : W := mkw 0x40fafa8b06162c62 0x503ebea2c1858b18 0xffffff8f1e1f3e73 0xffffffe3c787cf9c

def z618 : W := mkw 0xe1b703f69ba43fc8 0x786dc0fda6e90ff2 0x7dff03fe9fe03fcf 0xdf7fc0ffa7f80ff3

def z619 : W := mkw 0x920104103ddbc297 0xa48041040f76f0a5 0x070000001fffc7ff 0x01c0000007fff1ff

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x820010008000c04c 0xa080040020003013

def z621 : W := mkw 0x0020028900000000 0x000800a240000000 0x0000038f00000000 0xc00000e3c0000000

def z622 : W := mkw 0x0000000000201100 0x0000000000080440 0x0400000001e03983 0x0100000000780e60

def z623 : W := mkw 0x602c53c6826cbd49 0x580b14f1a09b2f52 0xfffcd3ce9ffcffcf 0xffff34f3a7ff3ff3

def z624 : W := mkw 0x90fffffdf1014294 0xa43fffff7c4050a5 0xf8fffffff0030630 0xfe3ffffffc00c18c

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800c30e00000000 0xe60030c380000000

def z626 : W := mkw 0x0096016000000000 0x0025805800000000 0x401f007000000000 0x1007c01c00000000

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x40031c70e0000000 0x1000c71c38000000

def z628 : W := mkw 0x909f5d74f1014294 0xa427d75d3c4050a5 0x401f1c70e100c18c 0x1007c71c38403063

def z629 : W := mkw 0x40f3a28b1f962c62 0x503ce8a2c7e58b18 0xffffe38f1fff3e73 0xfffff8e3c7ffcf9c

def z630 : W := mkw 0x02d3ac001d934002 0x80b4eb000764d000 0x79ff2c001fe30003 0x1e7fcb0007f8c000

def z631 : W := mkw 0x0048f80dc0000000 0x00123e0370000000 0x0000c00e00000000 0x0000300380000000

def z632 : W := mkw 0x60fefbefc06c9949 0x183fbefbf01b2652 0xdefcd34e81fcf9cf 0xf7bf34d3a07f3e73

def z633 : W := mkw 0x02fbfe891fdbe423 0xc0beffa247f6f908 0xfbfffc811fffc633 0x3effff2047fff18c

def z634 : W := mkw 0x0048f80000000000 0x00123e0000000000 0x8000fc0000000000 0x20003f0000000000

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa00200010030001 0x2a8008000400c000

def z636 : W := mkw 0x60085006804c8849 0x18021401a0132212 0xda1cd00e81fcc04f 0xb6873403a07f3013

def z637 : W := mkw 0x60fefbefc04c8849 0x183fbefbf0132212 0xfaffffffe01cc04c 0xfebffffff8073013

def z638 : W := mkw 0x81f7abf95ba03780 0x607deafe56e80de0 0x7dff2ff17fe03f83 0x5f7fcbfc5ff80fe0

def z639 : W := mkw 0x0001040011014000 0x8000410004405000 0x40031c000100c000 0x1000c70000403000

def z640 : W := mkw 0x2008500480488009 0x0802140120122002 0x000010008000c00c 0x0000040020003003

def z641 : W := mkw 0x009e5964c0000000 0x0027965930000000 0xe81f3cf1e0000000 0xfa07cf3c78000000

def z642 : W := mkw 0x810100101ba03780 0x6040400406e80de0 0x6d0300f01fe03f83 0x5b40c03c07f80fe0

def z643 : W := mkw 0x83bf5ff01be9f781 0xe0efd7fc06fa7de0 0x7dff1ff01fe0ff83 0x5f7fc7fc07f83fe0

def z644 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xce0010409103c7fd 0xf38004102440f1ff

def z645 : W := mkw 0x4004014200241940 0x1001005080090650 0xde1cc34e01fc39c3 0xf78730d3807f0e70

def z646 : W := mkw 0x004cf94dc0000000 0x00133e5370000000 0xd81cff4fe0000000 0xf6073fd3f8000000

def z647 : W := mkw 0x9061a69931014294 0xa41869a64c4050a5 0xfee3fffff103c7fd 0xffb8fffffc40f1ff

def z648 : W := mkw 0x1000040020014014 0x8400010008005005 0x020000000003c07c 0x008000000000f01f

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400008100000670 0xc10000204000019c

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0xca0010000100c001 0x3280040000403000

def z651 : W := mkw 0x00fafaa940000000 0x003ebeaa50000000 0xf8fffcb160000000 0x3e3fff2c58000000

def z652 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x27e020811e1f3e73 0x09f808204787cf9c

def z653 : W := mkw 0x0000000000000000 0x0000000000000000 0xee033cf1e100c1cd 0xfb80cf3c78403073

def z654 : W := mkw 0x4040a00204160842 0x1010280081058210 0xbfe0e30e1e1f3843 0xeff838c38787ce10

def z655 : W := mkw 0x9197057039a15394 0xa465c15c0e6854e5 0xee1f3cf1f1e3c7fd 0xfb87cf3c7c78f1ff

def z656 : W := mkw 0x02000400045bc003 0x808001000116f000 0x02000000001fc000 0x008000000007f000

def z657 : W := mkw 0x60000002006c9949 0x18000000801b2652 0xce00104081fcf9cf 0xf3800410207f3e73

def z658 : W := mkw 0xe12c53f6826cbfc9 0x784b14fda09b2ff2 0xde1cd3fe81fcffcf 0xf78734ffa07f3ff3

def z659 : W := mkw 0x1001040031014014 0x840041000c405005 0xea033c01f103c07d 0xba80cf007c40f01f

def z660 : W := mkw 0x604cf14f847e996b 0x18133c53e11fa65a 0xde1cf34f81fff9ff 0xf7873cd3e07ffe7f

def z661 : W := mkw 0x8021029013002680 0x600840a404c009a0 0x7de303f01f003f83 0x5f78c0fc07c00fe0

def z662 : W := mkw 0x0001000019800000 0x0000400006600000 0x010000001fe00003 0x0040000007f80000

def z663 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x8600e38f001f3e70 0xe18038e3c007cf9c

def z664 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x141cc34e80fc39ce 0xc50730d3a03f0e73

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c00030000003803 0x470000c000000e00

def z666 : W := mkw 0x909f5d74f1014294 0xa427d75d3c4050a5 0xee1f3cf1f103c7fd 0xfb87cf3c7c40f1ff

def z667 : W := mkw 0x0004014480000000 0x0001005120000000 0x0000034e80000000 0xc00000d3a0000000

def z668 : W := mkw 0x00dbfc0011014000 0x8036ff0004405000 0xfafffc001103c001 0x3ebfff000440f000

def z669 : W := mkw 0x00d2a80000000000 0x0034aa0000000000 0x20e32c0000000000 0x0838cb0000000000

def z670 : W := mkw 0x00b202a000000000 0x002c80a800000000 0x20e300b000000000 0x0838c02c00000000

def z671 : W := mkw 0x1000040020014014 0x8400010008005005 0x00001c00e000c00c 0x0000070038003003

def z672 : W := mkw 0xd061a69b37176ef6 0xf41869a6cdc5dbbd 0xbfe3efbf7e1f3e73 0xeff8fbefdf87cf9c

def z673 : W := mkw 0x40fefbefc2042c60 0x503fbefbf0810b18 0xfcffffffe0003e70 0xff3ffffff8000f9c

def z674 : W := mkw 0x91b306b03b816694 0xe46cc1ac0ee059a5 0xefe33cf1ff03c7fd 0xfbf8cf3c7fc0f1ff

def z675 : W := mkw 0x0060a28906122422 0x401828a241848908 0xafe020811e030671 0xebf808204780c19c

def z676 : W := mkw 0x009e5964c0000000 0x0027965930000000 0x001c000000000000 0x0007000000000000

def z677 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x26032cb17103c7fd 0x0980cb2c5c40f1ff

def z678 : W := mkw 0x620d55469dffd94b 0x98835551a77ff652 0xdf1cd34e9ffff9cf 0xf7c734d3a7fffe73

def z679 : W := mkw 0x00085804c0000000 0x0002160130000000 0x00001c00e0000000 0x0000070038000000

def z680 : W := mkw 0x810100101b802680 0x6040400406e009a0 0x010000001e000600 0x0040000007800180

def z681 : W := mkw 0xe10100121becbfc9 0x7840400486fb2ff2 0x070000001ffcffcf 0x01c0000007ff3ff3

def z682 : W := mkw 0xe00d5156916c9bc9 0x38035455a45b26f2 0xfe1fd3fe91fcffcf 0xff87f4ffa47f3ff3

def z683 : W := mkw 0x4020028b06162c62 0x500800a2c1858b18 0x0700038f1e1f3e73 0xc1c000e3c787cf9c

def z684 : W := mkw 0x81b603f002203780 0x606d80fc00880de0 0x7cff03f000003f80 0x5f3fc0fc00000fe0

def z685 : W := mkw 0x42dbfc021fdfec63 0xd0b6ff0087f7fb18 0xfffffc001ffffe73 0x3fffff0007ffff9c

def z686 : W := mkw 0x1048fc0de0014014 0x84123f0378005005 0x8200fc0fe003c07c 0xa0803f03f800f01f

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a00c000001c0003 0x2680300000070000

def z688 : W := mkw 0xe1fffbffdbecbfc9 0x787ffefff6fb2ff2 0xfffffffffffcffcf 0xffffffffffff3ff3

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000000100c1cd 0x0180000000403073

def z690 : W := mkw 0xf0010412316ddbdd 0xbc0041048c5b76f7 0xee033cf1f1ffffff 0xfb80cf3c7c7fffff

def z691 : W := mkw 0x0068fa8dc0000000 0x001a3ea370000000 0xb8e0ff8fe0000000 0xee383fe3f8000000

def z692 : W := mkw 0x200c514480689109 0x08031451201a2442 0xce1c104081e0c1cd 0xf387041020783073

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800104080000000 0xf200041020000000

def z694 : W := mkw 0x62dbfc021dffd94b 0x98b6ff00877ff652 0xfffffc001ffff9cf 0x3fffff0007fffe73

def z695 : W := mkw 0x200c514480689109 0x08031451201a2442 0xda1cd04081fcc18f 0x36873410207f3063

def z696 : W := mkw 0x83f3aeb01f936682 0xe0fcebac07e4d9a0 0x21e32cb01e030600 0x0878cb2c0780c180

def z697 : W := mkw 0x02d3ac001ddbc003 0x80b4eb000776f000 0x23e32c001fffc003 0x08f8cb0007fff000

def z698 : W := mkw 0x00def964c0000000 0x0037be5930000000 0xf8fffc70e0000000 0x3e3fff1c38000000

def z699 : W := mkw 0x62ffffefddffd94b 0x98bffffbf77ff652 0xfffffffffffff9cf 0xfffffffffffffe73

def z700 : W := mkw 0x02dbfc001d934002 0x80b6ff000764d000 0xf9fffc001e030000 0x3e7fff000780c000

def z701 : W := mkw 0x60000002067ebd6b 0x58000000819faf5a 0x070000001fffffff 0x01c0000007ffffff

def z702 : W := mkw 0x0008500480000000 0x0002140120000000 0x8000d00e80000000 0xa0003403a0000000

def z703 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x441f03f001e03f80 0x5107c0fc00780fe0

def z704 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xae032cb170030671 0xeb80cb2c5c00c19c

def z705 : W := mkw 0x02dffd64dddbc003 0x80b7ff593776f000 0xfbfffc70ffffc003 0x3effff1c3ffff000

def z706 : W := mkw 0x606cf3cf867ebd6b 0x581b3cf3e19faf5a 0x11fcc30e0efc3802 0x047f30c383bf0e00

def z707 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x11fc03700ee03982 0x047f00dc03b80e60

def z708 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0x20e32fbf60000000 0xc838cbefd8000000

def z709 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x3dfc03f01ee03f83 0x4f7f00fc07b80fe0

def z710 : W := mkw 0x01fefbedca802400 0x407fbefb72a00900 0xf9ffffffee000000 0xfe7ffffffb800000

def z711 : W := mkw 0xb29f5d54b9e9d39d 0xaca7d7552e7a74e7 0x401f1c70e1e0c18c 0x1007c71c38783063

def z712 : W := mkw 0x009e5964c0000000 0x0027965930000000 0xf81fffffe0000000 0xfe07fffff8000000

def z713 : W := mkw 0x009e5964c0000000 0x0027965930000000 0x501fdf7ee0000000 0x1407f7dfb8000000

def z714 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff03f1ffe03f83 0xdf7fc0fc7ff80fe0

def z715 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z716 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xb3e0e38f1e1f3e72 0xacf838e3c787cf9c

def z717 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xc01fffffe0000000 0xf007fffff8000000

def z718 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xc6033cf1e103c7fc 0xf180cf3c7840f1ff

def z719 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cd3cf81fcffff 0xf78734f3e07f3fff

def z720 : W := mkw 0xf02403dfa2243ffc 0x7c0900f7e8890fff 0x040003ffe0003ffc 0xc10000fff8000fff

def z721 : W := mkw 0x009b500019c88001 0x0026d40006722000 0x79ffc0001ffc0003 0x1e7ff00007ff0000

def z722 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x7bffc0001fffc003 0x1efff00007fff000

def z723 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfaffffffe000c04c 0xfebffffff8003013

def z724 : W := mkw 0x00fafaadc0000000 0x003ebeab70000000 0x20e3ecbf60000000 0x0838fb2fd8000000

def z725 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfffffcf1ffffc783 0xffffff3c7ffff1e0

def z726 : W := mkw 0xd001041233056ef4 0xf40041048cc15bbd 0x060000001103fffd 0x018000000440ffff

def z727 : W := mkw 0x7248fc06a45fc85f 0x9c923f01a917f217 0x8200fc0fe01fc07c 0xa0803f03f807f01f

def z728 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xffffff001ffff803 0x7fffffc007fffe00

def z729 : W := mkw 0xe12403f682243fc8 0x784900fda0890ff2 0x040003fe00003f80 0x410000ff80000fe0

def z730 : W := mkw 0x4248fc02045fc863 0x90923f008117f218 0x8200fc00001fc070 0x20803f000007f01c

def z731 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x51ff03700ee03802 0x147fc0dc03b80e00

def z732 : W := mkw 0xe1bb52b69bccaec9 0x786ed4ada6f32bb2 0xa3e3d0be9e1cc64c 0xa8f8f42fa7873193

def z733 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xfdff3ff1ffe0ff8f 0xff7fcffc7ff83fe3

def z734 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff03f09fe03fcf 0xdf7fc0fc27f80ff3

def z735 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x55ff03f00fe03f82 0x557fc0fc03f80fe0

def z736 : W := mkw 0x819701501ba03780 0x6065c05406e80de0 0x7dff03401fe03f83 0x5f7fc0d007f80fe0

def z737 : W := mkw 0x81b703fddba03780 0x606dc0ff76e80de0 0x7dff03fe1fe03f83 0x5f7fc0ff87f80fe0

def z738 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x79ff03b01fe03e03 0x1e7fc0ec07f80f80

def z739 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff23f11fe3ffff 0xffffc8fc47f8ffff

def z740 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff2ff17fe03f83 0x5f7fcbfc5ff80fe0

def z741 : W := mkw 0x00fefbedc4120002 0x003fbefb71048000 0xf9ffffffee1c0002 0xfe7ffffffb870000

def z742 : W := mkw 0x00def94480000000 0x0037be5120000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z743 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0x31ffc0001efc0002 0x0c7ff00007bf0000

def z744 : W := mkw 0xb19f5574b9e9d39d 0xac67d55d2e7a74e7 0x401f1c70e1e0c18c 0x1007c71c38783063

def z745 : W := mkw 0x00b202800a802400 0x402c80a002a00900 0x11fc03000ee03802 0x047f00c003b80e00

def z746 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfbfffcb01fffc603 0x3effff2c07fff180

def z747 : W := mkw 0xe12403f202243fc8 0x784900fc80890ff2 0x040003f000003fcc 0x410000fc00000ff3

def z748 : W := mkw 0x00fafaa940000000 0x003ebeaa50000000 0xf8ffffbf60000000 0xfe3fffefd8000000

def z749 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe0f38f1f1ffe73 0xfff83ce3c7c7ff9c

def z750 : W := mkw 0x00f6abedc0000000 0x003daafb70000000 0x20e32fbf60000000 0x0838cbefd8000000

def z751 : W := mkw 0xd061a69b37176ef6 0xf41869a6cdc5dbbd 0x51e3df7eef1cf98e 0x1478f7dfbbc73e63

def z752 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xfbfffc000ffcc003 0x3effff0003ff3000

def z753 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8fffffff0030630 0xfe3ffffffc00c18c

def z754 : W := mkw 0x02d3ac001d934002 0x80b4eb000764d000 0xfbffec001fff0003 0x3efffb0007ffc000

def z755 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x5dff03700fe03983 0x577fc0dc03f80e60

def z756 : W := mkw 0x0096014008a01100 0x0025805002280440 0x5dfc03400fe03983 0x577f00d003f80e60

def z757 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffcf1ffffc633 0xfeffff3c7ffff18c

def z758 : W := mkw 0x8149f81ddba03780 0x60527e0776e80de0 0x8500fc0fffe03f83 0xa1403f03fff80fe0

def z759 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xbffce0811eff0673 0xefff382047bfc19c

def z760 : W := mkw 0xe12503f693243fc8 0x784940fda4c90ff2 0xee0313fe9100ffcd 0xfb80c4ffa4403ff3

def z761 : W := mkw 0x0048f000045a8003 0x00123c000116a000 0xbbfce0001eff0003 0x2eff380007bfc000

def z762 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1fff4e81fcf9cf 0xff87ffd3a07f3e73

def z763 : W := mkw 0x9061a69931014294 0xa41869a64c4050a5 0xbee0e38f1103c7fd 0xefb838e3c440f1ff

def z764 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xb8ffefbf60000000 0xee3ffbefd8000000

def z765 : W := mkw 0x81b70bf05ba03780 0x606dc2fc16e80de0 0x7dff0ff07fe03f83 0x5f7fc3fc1ff80fe0

def z766 : W := mkw 0x00b703c01ba03500 0x402dc0f006e80d40 0x7dff03c01fe03f83 0x5f7fc0f007f80fe0

def z767 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbbe0e38f1e1f3e33 0x2ef838e3c787cf8c

def z768 : W := mkw 0x60000002006c9949 0x18000000801b2652 0xee033cf1e1fcf9cf 0xfb80cf3c787f3e73

def z769 : W := mkw 0x00be5bedc0000000 0x002f96fb70000000 0xe81f3fffe0000000 0xfa07cffff8000000

def z770 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xfe1f3cf1f1e3c7ff 0xff87cf3c7c78f1ff

def z771 : W := mkw 0x00be5bedc0000000 0x002f96fb70000000 0x401f1f7ee0000000 0x1007c7dfb8000000

def z772 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cd34e91ffffff 0xf78734d3a47fffff

def z773 : W := mkw 0x0004014000201100 0x0001005000080440 0x7dfc03401fe03983 0x5f7f00d007f80e60

def z774 : W := mkw 0x02fefbedcc920002 0x00bfbefb73248000 0xf9ffffffee000000 0xfe7ffffffb800000

def z775 : W := mkw 0x0093000019800000 0x0024c00006600000 0x7dff03001fe03803 0x5f7fc0c007f80e00

def z776 : W := mkw 0x11b607e02aa17514 0xc46d81f80aa85d45 0x93fc3f01eee3f87e 0xa4ff0fc07bb8fe1f

def z777 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xfdff13f09fe03f83 0xff7fc4fc27f80fe0

def z778 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x65ff03f01fe03f80 0x597fc0fc07f80fe0

def z779 : W := mkw 0x00d2a0000c920002 0x0034a80003248000 0xbbfce0001eff0003 0x2eff380007bfc000

def z780 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x71fffc001fffc002 0x1c7fff0007fff000

def z781 : W := mkw 0xf00d5556b16ddbdd 0xbc035555ac5b76f7 0x301fefbf70ff3e32 0x0c07fbefdc3fcf8c

def z782 : W := mkw 0x022507eddddbc003 0x808941fb7776f000 0x030003ffffffc003 0xc0c000fffffff000

def z783 : W := mkw 0xc12403ffc2243fe0 0x704900fff0890ff8 0x040003ffe0003ff0 0xc10000fff8000ffc

def z784 : W := mkw 0x029b54001ddbc003 0x80a6d5000776f000 0xfbffd0001fffc003 0x3efff40007fff000

def z785 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x51ff03000fe03802 0x147fc0c003f80e00

def z786 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffc307fffc003 0x3effff0c1ffff000

def z787 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xc61cd34e81fcf9cc 0xf18734d3a07f3e73

def z788 : W := mkw 0x01b707e01ba17500 0xc06dc1f806e85d40 0xfbff3f001fe3f803 0x3effcfc007f8fe00

def z789 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x11fc03001fe03803 0x047f00c007f80e00

def z790 : W := mkw 0x909b541039c9c295 0xa426d5040e7270a5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z791 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x5dfc03401fe03f83 0x577f00d007f80fe0

def z792 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8ffffbf60000000 0x3e3fffefd8000000

def z793 : W := mkw 0xc12403f202243fc0 0x704900fc80890ff0 0x040003fe00003fc0 0xc10000ff80000ff0

def z794 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe3e3ff1e1f3e73 0xfff8f8ffc787cf9c

def z795 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xbbffec001eff0003 0x2efffb0007bfc000

def z796 : W := mkw 0xd12507fb33257ff4 0xf44941feccc95ffd 0xee033ffff103fffd 0xfb80cffffc40ffff

def z797 : W := mkw 0x002403c002203500 0x400900f000880d40 0x3dfc03801ee03e03 0x4f7f00e007b80f80

def z798 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0xffff13f1ffe0ffff 0xffffc4fc7ff83fff

def z799 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x51fcd0000ffcc002 0x147f340003ff3000

def z800 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe0e3cf1f1f3ff3 0xfff838f3c7c7cffc

def z801 : W := mkw 0x81b703f91ba03780 0x606dc0fe46e80de0 0x7dff03ff1fe03f83 0xdf7fc0ffc7f80fe0

def z802 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x7dff03f01ee03e03 0x5f7fc0fc07b80f80

def z803 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe0f3cf9e1f3e73 0xfff83cf3e787cf9c

def z804 : W := mkw 0xd249fc1b355fcaf7 0xb4927f06cd57f2bd 0xee03fcfff11fc7fd 0xfb80ff3ffc47f1ff

def z805 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0x7dff2ff01fe33f83 0x5f7fcbfc07f8cfe0

def z806 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x31fc03801ee03e02 0x0c7f00e007b80f80

def z807 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8ffffffe100c18c 0xfe3ffffff8403063

def z808 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xfdff3ff01fe03f83 0x7f7fcffc07f80fe0

def z809 : W := mkw 0x60f2aaab406c9949 0x183caaaad01b2652 0x26e32cb161fcf9cf 0x09b8cb2c587f3e73

def z810 : W := mkw 0x00daf80dc0000000 0x0036be0370000000 0xf8fffcffe0000000 0xfe3fff3ff8000000

def z811 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfbfffc001fffc07f 0x3effff0007fff01f

def z812 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x17fc03001fe3ffff 0x05ff00c007f8ffff

def z813 : W := mkw 0x0064a3edc0000000 0x001928fb70000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z814 : W := mkw 0x00fefbedc2002400 0x403fbefb70800900 0xfcffffffe0003e00 0xff3ffffff8000f80

def z815 : W := mkw 0x02dbfc0ddddbc003 0x80b6ff037776f000 0xfbfffc0e1fffc003 0x3effff0387fff000

def z816 : W := mkw 0xc12403f202243fe0 0x704900fc80890ff8 0x040003f000003ff0 0x410000fc00000ffc

def z817 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7fff03f01fe33ff3 0x5fffc0fc07f8cffc

def z818 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x35e0e38f1e1f3e72 0xcd7838e3c787cf9c

def z819 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x9bfcc0000efc0003 0x26ff300003bf0000

def z820 : W := mkw 0x4248fc0b045fc863 0x90923f02c117f218 0x8200fc0e001fc000 0x20803f038007f000

def z821 : W := mkw 0xe12403ffc2243fc8 0x784900fff0890ff2 0x040003ffe0003fcc 0xc10000fff8000ff3

def z822 : W := mkw 0x00fefbedc4120022 0x003fbefb71048008 0xf8ffffffe0030030 0xfe3ffffff800c00c

def z823 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x101cc30e01fcf98e 0x040730c3807f3e63

def z824 : W := mkw 0x02d3a4001ddbc003 0x80b4e9000776f000 0xfbffe0001fffc003 0x3efff80007fff000

def z825 : W := mkw 0xf12403f6a2243fdc 0x7c4900fda8890ff7 0x040003ffe0003ffc 0xc10000fff8000fff

def z826 : W := mkw 0x819300101ba03780 0x6064c00406e80de0 0x7dff00f01fe03f83 0x5f7fc03c07f80fe0

def z827 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x7dff03401fe03983 0x5f7fc0d007f80e60

def z828 : W := mkw 0x00f6abedc0000000 0x003daafb70000000 0xb8e3efffe0000000 0xee38fbfff8000000

def z829 : W := mkw 0x409e5966c6162c62 0x50279659b1858b18 0x471f1c70fe1f3e73 0x11c7c71c3f87cf9c

def z830 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff3ff1ffe0ffcf 0xffffcffc7ff83ff3

def z831 : W := mkw 0x4040a00204160842 0x1010280081058210 0xbfe0e38f1e1f3e73 0xeff838e3c787cf9c

def z832 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xfdff3ff1ffe33fb3 0xff7fcffc7ff8cfec

def z833 : W := mkw 0x92daf8102cda8297 0x24b6be040b36a0a5 0x15fcc0f1eefc07fe 0xc57f303c7bbf01ff

def z834 : W := mkw 0x20fefbedc0689109 0x083fbefb701a2442 0xfcffffffe1e0f98f 0xff3ffffff8783e63

def z835 : W := mkw 0x00fefbedc4120002 0x003fbefb71048000 0xfffffffffe1f0673 0xffffffffff87c19c

def z836 : W := mkw 0x019300001ba03500 0x4064c00006e80d40 0x79ff00001fe03803 0x1e7fc00007f80e00

def z837 : W := mkw 0x929304103ddbc297 0xa4a4c1040f76f0a5 0x7fff00f01fffc7ff 0x5fffc03c07fff1ff

def z838 : W := mkw 0x81b703f95ba03780 0x606dc0fe56e80de0 0x7dff03f17fe03f83 0x5f7fc0fc5ff80fe0

def z839 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff03f01fe03fc3 0xffffc0fc07f80ff0

def z840 : W := mkw 0x02fefbedccda8003 0x00bfbefb7336a000 0xfbffffffeffcc003 0xfefffffffbff3000

def z841 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfffffcf09fffc7cf 0xffffff3c27fff1f3

def z842 : W := mkw 0xd10104123fb77ff6 0xf44041048feddffd 0x070000001fffffff 0x01c0000007ffffff

def z843 : W := mkw 0x029304001ddbc003 0x80a4c1000776f000 0x13fc00001fffc003 0x04ff000007fff000

def z844 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x11fcc0001eff0002 0x047f300007bfc000

def z845 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x35ff03b01fe03f83 0x0d7fc0ec07f80fe0

def z846 : W := mkw 0x009b540019c9c001 0x8026d50006727000 0xfbfffc001fffc003 0x3effff0007fff000

def z847 : W := mkw 0x0093000019c88001 0x0024c00006722000 0x7bff00001ffcc003 0x1effc00007ff3000

def z848 : W := mkw 0x02fefbedc8c88001 0x00bfbefb72322000 0xf8ffffffe0e00000 0xfe3ffffff8380000

def z849 : W := mkw 0x83dbfc301ddbc283 0xa0f6ff0c0776f0a0 0xfbfffc301fffc003 0x3effff0c07fff000

def z850 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0xdbfcfc000fffc003 0x36ff3f0003fff000

def z851 : W := mkw 0x01fefbedc2203500 0x407fbefb70880d40 0xf8ffffffe0003800 0xfe3ffffff8000e00

def z852 : W := mkw 0xc1d7a17b1db61be2 0x3075e85ec76d86f8 0xc21fe07f01ff01f0 0xb087f81fc07fc07c

def z853 : W := mkw 0x12dafc002cdbc017 0x84b6bf000b36f005 0x93fcfc01eeffc07e 0xa4ff3f007bbff01f

def z854 : W := mkw 0x02d3ac001ddbc003 0x80b4eb000776f000 0x7bff2c001fffc003 0x1effcb0007fff000

def z855 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x7dff03801fe03e03 0x5f7fc0e007f80f80

def z856 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0x7dff1ff01fe0ff83 0x5f7fc7fc07f83fe0

def z857 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xd81cd34e81fcf98e 0xf60734d3a07f3e63

def z858 : W := mkw 0x00b603e002203500 0x402d80f800880d40 0x7dff03f01fe03f83 0x5f7fc0fc07f80fe0

def z859 : W := mkw 0x900d5554b1014294 0xa40355552c4050a5 0xde1cd34e9103c7fd 0xf78734d3a440f1ff

def z860 : W := mkw 0x6248fc0f845fc86b 0x98923f03e117f21a 0x8200fc0f801fc07c 0xa0803f03e007f01f

def z861 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff2ff17fe33ff3 0xffffcbfc5ff8cffc

def z862 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xf9fffc000ffcc002 0x3e7fff0003ff3000

def z863 : W := mkw 0x92f3ae993f9366b6 0xe4bceba64fe4d9ad 0x21e32cb17e030630 0x0878cb2c5f80c18c

def z864 : W := mkw 0x20fefbedc0689109 0x083fbefb701a2442 0xfaffffffe1fcc18f 0xfebffffff87f3063

def z865 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x10ffcf3e60000000 0x043ff3cf98000000

def z866 : W := mkw 0x4000000206162c62 0x5000000081858b18 0xef033cf1fe1f3e73 0xfbc0cf3c7f87cf9c

def z867 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffcb17fffc7ff 0x3fffff2c5ffff1ff

def z868 : W := mkw 0x01fefbedcaa03500 0x407fbefb72a80d40 0xfdffffffefe03983 0xff7ffffffbf80e60

def z869 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0xffff3ff1ffe3ff83 0xffffcffc7ff8ffe0

def z870 : W := mkw 0x206cf3cd867ab52b 0x481b3cf3619ead4a 0x61fc30c19fe3c7bc 0x187f0c3067f8f1ef

def z871 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0e3fffe1f3e73 0xeff838ffff87cf9c

def z872 : W := mkw 0x6048f00f845e886b 0x18123c03e117a21a 0xee00f0cf911fc7fd 0xfb803c33e447f1ff

def z873 : W := mkw 0xc12403fb02243fe0 0x704900fec0890ff8 0x040003fe00003f80 0x410000ff80000fe0

def z874 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x3de0e38f1e1f3e33 0x4f7838e3c787cf8c

def z875 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffc01ffffc7ff 0xbfffff007ffff1ff

def z876 : W := mkw 0x00fefbedc2203500 0x403fbefb70880d40 0xfdffffffffe03f83 0xff7ffffffff80fe0

def z877 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xd0ffff7fe0000000 0xb43fffdff8000000

def z878 : W := mkw 0x819701701ba03780 0x6065c05c06e80de0 0x7dff00701fe03f83 0x1f7fc01c07f80fe0

def z879 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc001fffc1cf 0x3fffff0007fff073

def z880 : W := mkw 0x0048f000045a8003 0x00123c000116a000 0x11fcc0000efc0002 0x047f300003bf0000

def z881 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x91fcfc000efc0002 0x247f3f0003bf0000

def z882 : W := mkw 0x82dbf8101dda8283 0x20b6fe040776a0a0 0x7dffc0f01ffc0783 0x5f7ff03c07ff01e0

def z883 : W := mkw 0x002c53edc0000000 0x000b14fb70000000 0xf81fffffe0000000 0xfe07fffff8000000

def z884 : W := mkw 0x002403edc0000000 0x000900fb70000000 0x40031fffe0000000 0xd000c7fff8000000

def z885 : W := mkw 0x62d7ad469db7594a 0x98b5eb51a76dd652 0x25e32f4e9e0339cc 0xc978cbd3a780ce73

def z886 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffcf01fffc7ff 0x7fffff3c07fff1ff

def z887 : W := mkw 0x01b603edcaa03500 0x406d80fb72a80d40 0x11fc030e0ee03802 0x047f00c383b80e00

def z888 : W := mkw 0x9001041039814294 0xa40041040e6050a5 0xef033cf1ffe3c7ff 0xfbc0cf3c7ff8f1ff

def z889 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0xffff3ff09fe3ffcf 0xffffcffc27f8fff3

def z890 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffc409fffc7ff 0xffffff1027fff1ff

def z891 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfcffffffe0000670 0xff3ffffff800019c

def z892 : W := mkw 0x00d2a0000c920002 0x0034a80003248000 0x11fcc0000efc0002 0x047f300003bf0000

def z893 : W := mkw 0x412403eb02243d60 0x504900fac0890f58 0x0400038f00003e70 0xc10000e3c0000f9c

def z894 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfafffffff0030001 0xfebffffffc00c000

def z895 : W := mkw 0x20fefbedc0488009 0x083fbefb70122002 0xf8ffffffe000c00c 0xfe3ffffff8003003

def z896 : W := mkw 0x6249fc06955fc84b 0x98927f01a557f212 0xee03fc4e911fc1cd 0xfb80ff13a447f073

def z897 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x11fc03b00ee03e02 0x047f00ec03b80f80

def z898 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xd21cd34e81fcf9ce 0xb48734d3a07f3e73

def z899 : W := mkw 0x612403e682243d48 0x584900f9a0890f52 0x0000030e00003800 0x000000c380000e00

def z900 : W := mkw 0x0249f4001ddbc003 0x80927d000776f000 0xfbfcf0001fffc003 0x3eff3c0007fff000

def z901 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffcb17fffc003 0x3effff2c5ffff000

def z902 : W := mkw 0x00fefbedc0488001 0x003fbefb70122000 0xf8ffffffe0fc0002 0xfe3ffffff83f0000

def z903 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffcf0ffffc78f 0x7fffff3c3ffff1e3

def z904 : W := mkw 0x602403c682243d48 0x580900f1a0890f52 0x040003ce80003fcc 0xc10000f3a0000ff3

def z905 : W := mkw 0x6248f806845e884b 0x18923e01a117a212 0x0000c00e001c0000 0x0000300380070000

def z906 : W := mkw 0x02dbfc091ddbc023 0x80b6ff024776f008 0xfbfffc011fffc033 0x3effff0047fff00c

def z907 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0xdffc13408fe0f9cf 0xf7ff04d023f83e73

def z908 : W := mkw 0x412403eb02243d60 0x504900fac0890f58 0x0000030e00003800 0x000000c380000e00

def z909 : W := mkw 0x20fefbedc0689109 0x083fbefb701a2442 0xfeffffffe1e0c1cd 0xffbffffff8783073

def z910 : W := mkw 0x00fafa8900000000 0x003ebea240000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z911 : W := mkw 0x00f6abedc0000000 0x003daafb70000000 0xe8e33fffe0000000 0xfa38cffff8000000

def z912 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xfe03fffff103c7fd 0xff80fffffc40f1ff

def z913 : W := mkw 0x602403efc2243d68 0x580900fbf0890f5a 0x040003ffe0003ffc 0xc10000fff8000fff

def z914 : W := mkw 0x819300101ba03780 0x6064c00406e80de0 0x15fc00001fe03f83 0x057f000007f80fe0

def z915 : W := mkw 0x4020028202042c40 0x500800a080810b10 0xbfe0e38f1e1f3e73 0xeff838e3c787cf9c

def z916 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x79ffec001fff0003 0x1e7ffb0007ffc000

def z917 : W := mkw 0x029b5c001ddbc003 0x80a6d7000776f000 0x7bff1c001fffc003 0x1effc70007fff000

def z918 : W := mkw 0x42bb5e8b1bcdec61 0xd0aed7a2c6f37b18 0x441f1f8f01e0fe70 0xd107c7e3c0783f9c

def z919 : W := mkw 0x836cfff0067bf783 0xe0db3ffc019efde0 0x8600fff0001fff80 0x61803ffc0007ffe0

def z920 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff23f11fe33fb3 0x5f7fc8fc47f8cfec

def z921 : W := mkw 0xf0010412377fffff 0xfc0041048ddfffff 0x070000001fffffff 0x01c0000007ffffff

def z922 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x5c1cd34e81fcf98f 0x570734d3a07f3e63

def z923 : W := mkw 0x90fffffdf1014294 0xa43fffff7c4050a5 0x16fcc30e1103c7fd 0x05bf30c38440f1ff

def z924 : W := mkw 0x00fefbedc2002420 0x403fbefb70800908 0xf8ffffffe0000630 0xfe3ffffff800018c

def z925 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x37e0e38f1e1f3e73 0x0df838e3c787cf9c

def z926 : W := mkw 0x80b302901b802680 0x602cc0a406e009a0 0x7dff03f01fe03f83 0x5f7fc0fc07f80fe0

def z927 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xfbfcf0001fffc003 0x3eff3c0007fff000

def z928 : W := mkw 0x81b703fddba03780 0x606dc0ff76e80de0 0xfdff3fffffe03f83 0xff7fcffffff80fe0

def z929 : W := mkw 0x0040a00900000000 0x0010280240000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z930 : W := mkw 0x02dbfc0ddddbc003 0x80b6ff037776f000 0xfbfffcffffffc003 0xfeffff3ffffff000

def z931 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfbfffcf1ffffc07f 0xfeffff3c7ffff01f

def z932 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xe0fffcffe0000000 0xb83fff3ff8000000

def z933 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xd3fffc000fffc002 0x34ffff0003fff000

def z934 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1cd3ce91fcffcf 0xff8734f3a47f3ff3

def z935 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x5dfc03f00fe03f83 0x577f00fc03f80fe0

def z936 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x59fcc0000ffc0003 0x167f300003ff0000

def z937 : W := mkw 0x00fefbedc0488001 0x003fbefb70122000 0xf8ffffffe1e0c000 0xfe3ffffff8783000

def z938 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x93fcfc001fffc003 0x24ff3f0007fff000

def z939 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xfdff23f11fe03f83 0xff7fc8fc47f80fe0

def z940 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0x13fcc0000effc002 0x04ff300003bff000

def z941 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7fff1ff0ffe3ffff 0x5fffc7fc3ff8ffff

def z942 : W := mkw 0x7048f40fa45fc87f 0x9c123d03e917f21f 0x8200fc0fe01fc07c 0xa0803f03f807f01f

def z943 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffcf17fffc7b3 0x7fffff3c5ffff1ec

def z944 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc01ffffc003 0xbeffff007ffff000

def z945 : W := mkw 0x009e596dc0000000 0x0027965b70000000 0x401f1c7fe0000000 0x9007c71ff8000000

def z946 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffc001fffc18f 0x3effff0007fff063

def z947 : W := mkw 0xe12403ff82243fe8 0x784900ffe0890ffa 0x040003ff80003ffc 0xc10000ffe0000fff

def z948 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc811fffc633 0x3effff2047fff18c

def z949 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0xf9ff3ff1eee03802 0xfe7fcffc7bb80e00

def z950 : W := mkw 0x92dbfc1dfddbc297 0xa4b6ff077f76f0a5 0xfffffcffffffc7ff 0xffffff3ffffff1ff

def z951 : W := mkw 0x6048f00f845e886b 0x18123c03e117a21a 0x8200e00f001f0070 0xa0803803c007c01c

def z952 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x53ffdc001fffc003 0x14fff70007fff000

def z953 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf9fffffffe000003 0xfe7fffffff800000

def z954 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbffff0e1fffc003 0xfeffffc387fff000

def z955 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x79ff03f00fe03982 0x5e7fc0fc03f80e60

def z956 : W := mkw 0x00be5bedc0000000 0x002f96fb70000000 0x78ff1fffe0000000 0xde3fc7fff8000000

def z957 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xa7e0e38f1e1f3e70 0xe9f838e3c787cf9c

def z958 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cd3ffe1fcf9cf 0xf78734fff87f3e73

def z959 : W := mkw 0x009e5964c0000000 0x0027965930000000 0x401f1f7ee0000000 0xd007c7dfb8000000

def z960 : W := mkw 0x0048f000045a8003 0x00123c000116a000 0xdbfcd0000ffcc003 0x36ff340003ff3000

def z961 : W := mkw 0x60040142006c9949 0x18010050801b2652 0xde1cc34e01fcf9cf 0xf78730d3807f3e73

def z962 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfffcd34e9ffcf9cf 0xffff34d3a7ff3e73

def z963 : W := mkw 0x80d3a0101d920282 0x2034e804076480a0 0xffffe0f11fff07f3 0xfffff83c47ffc1fc

def z964 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff3ff1ffe3ffbf 0x5f7fcffc7ff8ffef

def z965 : W := mkw 0xf049f41fb55fcaff 0xbc127d07ed57f2bf 0xee03fcfff11fc7fd 0xfb80ff3ffc47f1ff

def z966 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffffc3f01ffc3f83 0x7ffff0fc07ff0fe0

def z967 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc401fffc183 0x7fffff1007fff060

def z968 : W := mkw 0x029304001ddbc003 0x80a4c1000776f000 0xfbff3c001fffc003 0x3effcf0007fff000

def z969 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc70ffffc003 0x3effff1c3ffff000

def z970 : W := mkw 0x00fefbedc8800000 0x003fbefb72200000 0xf9ffffffeee00002 0xfe7ffffffbb80000

def z971 : W := mkw 0x00fafaadc0000000 0x003ebeab70000000 0xe8e3fcffe0000000 0xfa38ff3ff8000000

def z972 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x79ffdc001ffcc003 0x1e7ff70007ff3000

def z973 : W := mkw 0x600c5166c06c9949 0x18031459b01b2652 0xde1cd37ee1fcf9cf 0xf78734dfb87f3e73

def z974 : W := mkw 0xf20104123dffdbdf 0xbc8041048f7ff6f7 0x070000001fffffff 0x01c0000007ffffff

def z975 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xfe033ff1f103ffff 0xff80cffc7c40ffff

def z976 : W := mkw 0x0097014019a01100 0x0025c05006680440 0x79ff03001fe03803 0x1e7fc0c007f80e00

def z977 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1fd3fe81fcf9cf 0xff87f4ffa07f3e73

def z978 : W := mkw 0xd001041235174af6 0xb40041048d45d2bd 0x06000000111fc7fd 0x018000000447f1ff

def z979 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x7dff03f00ee03f82 0x5f7fc0fc03b80fe0

def z980 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x9fe0c30e1e1f3e73 0xe7f830c38787cf9c

def z981 : W := mkw 0x6248f806845e884b 0x18923e01a117a212 0x8200d00e801cc04c 0xa0803403a0073013

def z982 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc409fffc18f 0x3effff1027fff063

def z983 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x51ffdc000efc0002 0x147ff70003bf0000

def z984 : W := mkw 0x00fefbedc2002400 0x403fbefb70800900 0xfffffffffe033e73 0xffffffffff80cf9c

def z985 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7fff2ff17fe3ffff 0x5fffcbfc5ff8ffff

def z986 : W := mkw 0x4248f80b045e8863 0x10923e02c117a218 0x8200e00f001f0070 0xa0803803c007c01c

def z987 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffcf1ffffc1cf 0xffffff3c7ffff073

def z988 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x50ffdfffe0000000 0xd43ff7fff8000000

def z989 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0xffff23f1ffe33fff 0xffffc8fc7ff8cfff

def z990 : W := mkw 0x602403cf82243d68 0x580900f3e0890f5a 0x0000030e00003800 0x000000c380000e00

def z991 : W := mkw 0x006cf3cd80000000 0x001b3cf360000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z992 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc801fffc603 0x7fffff2007fff180

def z993 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc001fffc673 0x3fffff0007fff19c

def z994 : W := mkw 0xd12403fb22243ff4 0x744900fec8890ffd 0x040003ffe0003ffc 0xc10000fff8000fff

def z995 : W := mkw 0x02dbfc091ddbc003 0x80b6ff024776f000 0xfbfffc0f1fffc003 0xbeffff03c7fff000

def z996 : W := mkw 0x01b603edcaa03500 0x406d80fb72a80d40 0x11fc03ffeee03802 0xc47f00fffbb80e00

def z997 : W := mkw 0x0097054019a15100 0x8025c15006685440 0xffff3f409fe3f9cf 0xffffcfd027f8fe73

def z998 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe3ffffff1fffff 0xfff8ffffffc7ffff

def z999 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0x51ffc0000ffc0002 0x147ff00003ff0000

def z1000 : W := mkw 0x0048f80dc0000000 0x00123e0370000000 0xa003fcbfe0000000 0xa800ff2ff8000000

def z1001 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x70ffffffe0000000 0x1c3ffffff8000000

def z1002 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xd8ffdf7ee0000000 0xf63ff7dfb8000000

def z1003 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cf34f81fff9ff 0xf7873cd3e07ffe7f

def z1004 : W := mkw 0x00dbf80019c88001 0x0036fe0006722000 0xfbfffc001ffcc003 0x3effff0007ff3000

def z1005 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0x11fcc0001ffc0003 0x047f300007ff0000

def z1006 : W := mkw 0x00b60bedc0000000 0x002d82fb70000000 0x00030fffe0000000 0xc000c3fff8000000

def z1007 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfeffffffe0000041 0xffbffffff8000010

def z1008 : W := mkw 0xd001041231054ad4 0xb40041048c4152b5 0x06000000111fffff 0x018000000447ffff

def z1009 : W := mkw 0x009a500008c88001 0x0026940002322000 0xdbfcd0000ffcc003 0x36ff340003ff3000

def z1010 : W := mkw 0x81b302901ba03780 0x606cc0a406e80de0 0x7dff03801fe03f83 0x5f7fc0e007f80fe0

def z1011 : W := mkw 0x4048f00b045e8863 0x10123c02c117a218 0x8200f00f001fc070 0xa0803c03c007f01c

def z1012 : W := mkw 0x802503d013203780 0x600940f404c80de0 0x7dff03f01fe03f83 0x5f7fc0fc07f80fe0

def z1013 : W := mkw 0xf0010412316ddbdd 0xbc0041048c5b76f7 0x0600000001fcf9cf 0x01800000007f3e73

def z1014 : W := mkw 0x8097015019a01380 0x2025c054066804e0 0x7dff03f01fe03f83 0x5f7fc0fc07f80fe0

def z1015 : W := mkw 0x0020028002002400 0x400800a000800900 0x7dfc03801fe03e03 0x5f7f00e007f80f80

def z1016 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x31ffec000efc0002 0x0c7ffb0003bf0000

def z1017 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x63ff3c001fffc003 0x18ffcf0007fff000

def z1018 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8ffffffe1e00003 0xfe3ffffff8780000

def z1019 : W := mkw 0x002403c002203500 0x400900f000880d40 0xfffc33c19fe3ffff 0xffff0cf067f8ffff

def z1020 : W := mkw 0x01fefbedcaa03500 0x407fbefb72a80d40 0xfdfffffffee03e03 0xff7fffffffb80f80

def z1021 : W := mkw 0x60085002006c9949 0x18021400801b2652 0xde1cd30e01fcf9cf 0xf78734c3807f3e73

def z1022 : W := mkw 0x00fefbedc0488001 0x003fbefb70122000 0xfeffffffe1fcc1cf 0xffbffffff87f3073

def z1023 : W := mkw 0x009a500008c88001 0x0026940002322000 0x11fcc0000efc0002 0x047f300003bf0000

def z1024 : W := mkw 0x00fefbedc0488001 0x003fbefb70122000 0xfaffffffe01cc000 0xfebffffff8073000

def z1025 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x15fc03400ee03982 0x457f00d003b80e60

def z1026 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x9e1cc30e01fcf9cf 0xe78730c3807f3e73

def z1027 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffcc19fffc7ff 0xffffff3067fff1ff

def z1028 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x51fc03400fe03982 0x147f00d003f80e60

def z1029 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffc70ffffc1cf 0xffffff1c3ffff073

def z1030 : W := mkw 0x019200000aa03500 0x4064800002a80d40 0x11fc00000ee03802 0x047f000003b80e00

def z1031 : W := mkw 0x612403e682243d48 0x584900f9a0890f52 0x0400034e800039cc 0xc10000d3a0000e73

def z1032 : W := mkw 0x00fefbedc6122402 0x403fbefb71848900 0xfffffffffe1f3e03 0xffffffffff87cf80

def z1033 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x51ff1f70efe0f98e 0x147fc7dc3bf83e63

def z1034 : W := mkw 0x6248fc06845fc84b 0x98923f01a117f212 0x8200fc0e001fc000 0x20803f038007f000

def z1035 : W := mkw 0x00fefbedc0201100 0x003fbefb70080440 0xfeffffffe1e0f9cf 0xffbffffff8783e73

def z1036 : W := mkw 0x00be53e480000000 0x002f94f920000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1037 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x561cd34e81fcf9cf 0x158734d3a07f3e73

def z1038 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x15fc03000fe03983 0x057f00c003f80e60

def z1039 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x31ff2fb17ee33e32 0x0c7fcbec5fb8cf8c

def z1040 : W := mkw 0x6048f80fc45e886b 0x18123e03f117a21a 0x8200fc0fe01fc07c 0xa0803f03f807f01f

def z1041 : W := mkw 0x602403cf82243d68 0x580900f3e0890f5a 0x0400038f00003e70 0xc10000e3c0000f9c

def z1042 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff1ff1ffe0ffff 0xdf7fc7fc7ff83fff

def z1043 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xa6033cf1f003c7fc 0xe980cf3c7c00f1ff

def z1044 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0xfdff3ff1ffe03fff 0xff7fcffc7ff80fff

def z1045 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x15fc03800ee03e02 0x457f00e003b80f80

def z1046 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xe2033cf1f103c7fc 0xb880cf3c7c40f1ff

def z1047 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xffe3ff8f1e1f3e73 0xfff8ffe3c787cf9c

def z1048 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xb0ffffbfe0000000 0xac3fffeff8000000

def z1049 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff03001fe03f83 0x1f7fc0c007f80fe0

def z1050 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x39fc03800ee03802 0x4e7f00e003b80e00

def z1051 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffcf1ffffc18f 0xfeffff3c7ffff063

def z1052 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1cf3cf81fcf9cf 0xff873cf3e07f3e73

def z1053 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xf9fffcf1eefc0002 0xfe7fff3c7bbf0000

def z1054 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfffffc001fffc783 0x3fffff0007fff1e0

def z1055 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x30ffefffe0000000 0xcc3ffbfff8000000

def z1056 : W := mkw 0x00b603edc0000000 0x002d80fb70000000 0xf8ff3fffe0000000 0xfe3fcffff8000000

def z1057 : W := mkw 0x0068fa8dc0000000 0x001a3ea370000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z1058 : W := mkw 0x00def96dc0000000 0x0037be5b70000000 0xd81fff7fe0000000 0xf607ffdff8000000

def z1059 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7fff03f1ffe3ffff 0xdfffc0fc7ff8ffff

def z1060 : W := mkw 0x00b306801b816400 0xc02cc1a006e05900 0xffff3f811fe3fe73 0xffffcfe047f8ff9c

def z1061 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffc70ffffc7ff 0x3fffff1c3ffff1ff

def z1062 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x33ffec001fffc003 0x0cfffb0007fff000

def z1063 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xfe03fcf1f11fc7ff 0xff80ff3c7c47f1ff

def z1064 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0x17fcc0001fffc7ff 0x05ff300007fff1ff

def z1065 : W := mkw 0x029300001dda8003 0x00a4c0000776a000 0x79ff00001ffc0003 0x1e7fc00007ff0000

def z1066 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff33f19fe3ffff 0xffffccfc67f8ffff

def z1067 : W := mkw 0x00f6abe940000000 0x003daafa50000000 0xf8ffefff60000000 0xfe3ffbffd8000000

def z1068 : W := mkw 0x81b703f91ba037a0 0x606dc0fe46e80de8 0x7dff03f11fe03fb3 0x5f7fc0fc47f80fec

def z1069 : W := mkw 0x00daf82dc0000000 0x0036be0b70000000 0x8003fc3fe0000000 0xa000ff0ff8000000

def z1070 : W := mkw 0x0093000019a01100 0x0024c00006680440 0x7dff00001fe03983 0x1f7fc00007f80e60

def z1071 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0e38f1f1fffff 0xeff838e3c7c7ffff

def z1072 : W := mkw 0x60fefbefc67ebd6b 0x583fbefbf19faf5a 0x11fcc30e0efc3802 0x047f30c383bf0e00

def z1073 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff03f01fe0ff8f 0x5f7fc0fc07f83fe3

def z1074 : W := mkw 0x9049f410355bc297 0xa4127d040d56f0a5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z1075 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0f38f9e1ffe7f 0xeff83ce3e787ff9f

def z1076 : W := mkw 0x02dbfc205ddbc003 0x80b6ff081776f000 0xfbfffc307fffc003 0x3effff0c1ffff000

def z1077 : W := mkw 0x02daf80dccda8003 0x00b6be037336a000 0x11fcc00e0efc0002 0x047f300383bf0000

def z1078 : W := mkw 0x902507d033217794 0xe40941f40cc85de5 0xffff3ff1ffe3ffff 0xffffcffc7ff8ffff

def z1079 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x7dfc03c01fe03f83 0x5f7f00f007f80fe0

def z1080 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xfbfffc001eff0003 0x3effff0007bfc000

def z1081 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x13fcc0000ffcc003 0x04ff300003ff3000

def z1082 : W := mkw 0x609e5966c06c9949 0x18279659b01b2652 0x461f1c70e1fcf9cf 0x1187c71c387f3e73

def z1083 : W := mkw 0x809b501019c88281 0x2026d404067220a0 0xffffd0f09ffcc7cf 0xfffff43c27ff31f3

def z1084 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0xa0e3ecbf60000000 0xa838fb2fd8000000

def z1085 : W := mkw 0x00fafaadc0000000 0x003ebeab70000000 0xb8e3ffbfe0000000 0xee38ffeff8000000

def z1086 : W := mkw 0x02fefbedc45a8003 0x00bfbefb7116a000 0xf8ffffffe01c0000 0xfe3ffffff8070000

def z1087 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x31ff03b00ee03802 0x0c7fc0ec03b80e00

def z1088 : W := mkw 0x919304103ba17794 0xe464c1040ee85de5 0xffff3c001fe3ffff 0x3fffcf0007f8ffff

def z1089 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffcf1ffffc673 0xffffff3c7ffff19c

def z1090 : W := mkw 0x00b202800a802400 0x402c80a002a00900 0x3dfc03801ee03e03 0x4f7f00e007b80f80

def z1091 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xdbffdc000ffcc003 0x36fff70003ff3000

def z1092 : W := mkw 0x8197017019a01380 0x2065c05c066804e0 0x7dff03701fe03983 0x5f7fc0dc07f80e60

def z1093 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0x11fcec000eff0002 0x047f3b0003bfc000

def z1094 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xf8ffff7ee0000000 0x3e3fffdfb8000000

def z1095 : W := mkw 0x006cfbedc0000000 0x001b3efb70000000 0xe803ffffe0000000 0xfa00fffff8000000

def z1096 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xdffcd0408ffcc1cf 0xf7ff341023ff3073

def z1097 : W := mkw 0x0000000000000000 0x0000000000000000 0xf803ffffe0000000 0xfe00fffff8000000

def z1098 : W := mkw 0x00fefbedc4120002 0x003fbefb71048000 0xf9fffffffe030000 0xfe7fffffff80c000

def z1099 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff3ff1ffe33ff3 0xffffcffc7ff8cffc

def z1100 : W := mkw 0xf001041231255bdc 0xbc0041048c4956f7 0x060000001103fffd 0x018000000440ffff

def z1101 : W := mkw 0x600c5946c06c9949 0x18031651b01b2652 0xde1cdf4ee1fcf9cf 0xf78737d3b87f3e73

def z1102 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfaffffffe01c0003 0xfebffffff8070000

def z1103 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe3efbf7e1f3e73 0xeff8fbefdf87cf9c

def z1104 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0xfbffe0001fff0003 0x3efff80007ffc000

def z1105 : W := mkw 0x4004014200241940 0x1001005080090650 0xde1cd34e81fcf9cf 0xf78734d3a07f3e73

def z1106 : W := mkw 0x00dbf0001dda8003 0x0036fc000776a000 0xfbfff0001fffc003 0x3efffc0007fff000

def z1107 : W := mkw 0x00fefbedc6122422 0x403fbefb71848908 0xfffffffffe030671 0xffffffffff80c19c

def z1108 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0ff8ffe1f3e73 0xeff83fe3ff87cf9c

def z1109 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfffffc001fffc043 0xffffff0007fff010

def z1110 : W := mkw 0xc12503fb13243fe0 0x704940fec4c90ff8 0xee0323ff11033ff1 0xfb80c8ffc440cffc

def z1111 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x79ff03f01ee03e02 0x5e7fc0fc07b80f80

def z1112 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfcfffffff0000601 0xff3ffffffc000180

def z1113 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x65ff00f01fe03f83 0x197fc03c07f80fe0

def z1114 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x541cd34e81fcf9ce 0xd50734d3a07f3e73

def z1115 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0e3cf9e1f3fff 0xeff838f3e787cfff

def z1116 : W := mkw 0x81b302b01ba03780 0x606cc0ac06e80de0 0x7dff00b01fe03f83 0x1f7fc02c07f80fe0

def z1117 : W := mkw 0x9000041020014294 0xa4000104080050a5 0xee033cf1e003c7fc 0xfb80cf3c7800f1ff

def z1118 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc009fffc04f 0xbeffff0027fff013

def z1119 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x15fc03001ee03e03 0x057f00c007b80f80

def z1120 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x79ff03f01fe03803 0x5e7fc0fc07f80e00

def z1121 : W := mkw 0x40085002004c8841 0x1002140080132210 0xde1cd34e81fcf9cf 0xf78734d3a07f3e73

def z1122 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x79ff03000ee03802 0x1e7fc0c003b80e00

def z1123 : W := mkw 0x4248fc0fc45fc863 0x90923f03f117f218 0x8200fc0fe01fc070 0xa0803f03f807f01c

def z1124 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x60ff3fffe0000000 0xd83fcffff8000000

def z1125 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfcffffffe0003803 0xff3ffffff8000e00

def z1126 : W := mkw 0x4020028206162c62 0x500800a081858b18 0xbfe0c38e1e1f3e73 0xeff830e38787cf9c

def z1127 : W := mkw 0x00b302801b802400 0x402cc0a006e00900 0x79ff03001fe03803 0x1e7fc0c007f80e00

def z1128 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x39fc03001ee03803 0x0e7f00c007b80e00

def z1129 : W := mkw 0x0048f80dc0000000 0x00123e0370000000 0xc003fc7fe0000000 0xb000ff1ff8000000

def z1130 : W := mkw 0x22dbfc049ddbc00b 0x88b6ff012776f002 0xfbfffc009fffc00f 0x3effff0027fff003

def z1131 : W := mkw 0x90d3a4103d934296 0xa434e9040f64d0a5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z1132 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x55ff03701fe03f83 0x157fc0dc07f80fe0

def z1133 : W := mkw 0x02dbfc049ddbc003 0x80b6ff012776f000 0xfbfffc0e9fffc003 0xbeffff03a7fff000

def z1134 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfaffffffe100c001 0xfebffffff8403000

def z1135 : W := mkw 0x00fefbedc45a8003 0x003fbefb7116a000 0xfbffffffffffc003 0xfefffffffffff000

def z1136 : W := mkw 0x03fefbedcefab503 0x40ffbefb73bead40 0xf9ffffffeefc3802 0xfe7ffffffbbf0e00

def z1137 : W := mkw 0x91b603f02aa03794 0x646d80fc0aa80de5 0x15fc03f1eee03ffe 0xc57f00fc7bb80fff

def z1138 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc811fffc003 0xfeffff2047fff000

def z1139 : W := mkw 0x009300001b802400 0x4024c00006e00900 0x7dff00001fe03e03 0x1f7fc00007f80f80

def z1140 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc011fffc073 0xbeffff0047fff01c

def z1141 : W := mkw 0x0060a28900000000 0x001828a240000000 0xb8e3efbf60000000 0xee38fbefd8000000

def z1142 : W := mkw 0x812503d01ba03780 0x604940f406e80de0 0x7dfc03c01fe03f83 0x5f7f00f007f80fe0

def z1143 : W := mkw 0x0020028900000000 0x000800a240000000 0xe8033fffe0000000 0xfa00cffff8000000

def z1144 : W := mkw 0x00fefbedc6122422 0x403fbefb71848908 0xfdfffffffe033e33 0xff7fffffff80cf8c

def z1145 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0x11fcdc000efcc002 0x047f370003bf3000

def z1146 : W := mkw 0x929304103ddbc297 0xa4a4c1040f76f0a5 0xffff3cf1ffffc7ff 0xffffcf3c7ffff1ff

def z1147 : W := mkw 0x02fefbedccda8003 0x00bfbefb7336a000 0xfbfffffffeff0003 0xfeffffffffbfc000

def z1148 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x11fc03000fe03982 0x047f00c003f80e60

def z1149 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x15fc03f01fe03f83 0x457f00fc07f80fe0

def z1150 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x3dfc03801fe03f83 0x4f7f00e007f80fe0

def z1151 : W := mkw 0x0096014008a01100 0x0025805002280440 0x11fc03000ee03802 0x047f00c003b80e00

def z1152 : W := mkw 0x00f2aaa940000000 0x003caaaa50000000 0x30e3efbf60000000 0x0c38fbefd8000000

def z1153 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1ffffff1ffffff 0xff87fffffc7fffff

def z1154 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff03f01fe33fb3 0x5f7fc0fc07f8cfec

def z1155 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfcffffffe1000181 0xff3ffffff8400060

def z1156 : W := mkw 0x00fefbedc0201100 0x003fbefb70080440 0xf8ffffffe0e03802 0xfe3ffffff8380e00

def z1157 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0xfbffd0001ffcc003 0x3efff40007ff3000

def z1158 : W := mkw 0x00def96dc0000000 0x0037be5b70000000 0x401fdc7ee0000000 0x1007f71fb8000000

def z1159 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x31fce0001eff0002 0x0c7f380007bfc000

def z1160 : W := mkw 0x91f3a6b93f9366b6 0xe47ce9ae4fe4d9ad 0x21e32cb17e030630 0x0878cb2c5f80c18c

def z1161 : W := mkw 0x81b302b01b802680 0x606cc0ac06e009a0 0x7dff03b01fe03e03 0x5f7fc0ec07f80f80

def z1162 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffcf01fffc003 0x7effff3c07fff000

def z1163 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xf9fffc001eff0002 0x3e7fff0007bfc000

def z1164 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x11fcc0000ffcc002 0x047f300003ff3000

def z1165 : W := mkw 0x02dbfc095ddbc003 0x80b6ff025776f000 0xfbfffc017fffc003 0x3effff005ffff000

def z1166 : W := mkw 0x6048f006845e884b 0x18123c01a117a212 0x8200f00e801fc04c 0xa0803c03a007f013

def z1167 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff0ff07fe03f83 0x5f7fc3fc1ff80fe0

def z1168 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0xffe33cf1ff03c7ff 0xfff8cf3c7fc0f1ff

def z1169 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffcf1ffffc7bf 0x3effff3c7ffff1ef

def z1170 : W := mkw 0x402403cb02243d60 0x500900f2c0890f58 0x040003cf00003ff0 0xc10000f3c0000ffc

def z1171 : W := mkw 0x009300001d920002 0x0024c00007648000 0x7bff00001fff0003 0x1effc00007ffc000

def z1172 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xfe1cf34e91fff9cf 0xff873cd3a47ffe73

def z1173 : W := mkw 0x5248fc0b245fc877 0x94923f02c917f21d 0x8200fc0fe01fc07c 0xa0803f03f807f01f

def z1174 : W := mkw 0x6048f00f845e886b 0x18123c03e117a21a 0x0000c00e001c0000 0x0000300380070000

def z1175 : W := mkw 0x81b603f00aa03780 0x606d80fc02a80de0 0x15fc03000ee03f82 0x057f00c003b80fe0

def z1176 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffcb17fffc673 0xffffff2c5ffff19c

def z1177 : W := mkw 0x00fefbedc2002400 0x403fbefb70800900 0xf9fffffffe000600 0xfe7fffffff800180

def z1178 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xd9fcd0000efc0002 0x367f340003bf0000

def z1179 : W := mkw 0x00fefbedc0201100 0x003fbefb70080440 0xf8ffffffe1e00180 0xfe3ffffff8780060

def z1180 : W := mkw 0xf10104123bedffdd 0xfc4041048efb7ff7 0x070000001fffffff 0x01c0000007ffffff

def z1181 : W := mkw 0x00be5bedc0000000 0x002f96fb70000000 0xd81fdfffe0000000 0xf607f7fff8000000

def z1182 : W := mkw 0x00def96dc0000000 0x0037be5b70000000 0xe81ffcffe0000000 0xfa07ff3ff8000000

def z1183 : W := mkw 0x0248fc00045bc003 0x80923f000116f000 0xfbfcfc001fffc003 0x3eff3f0007fff000

def z1184 : W := mkw 0x029b5c0019c9c001 0x80a6d70006727000 0xfbffdc001ffcc003 0x3efff70007ff3000

def z1185 : W := mkw 0x00fefbedc2002400 0x403fbefb70800900 0xf9ffffffee003802 0xfe7ffffffb800e00

def z1186 : W := mkw 0xf02507dfb3257ffc 0xfc0941f7ecc95fff 0xee033ffff103fffd 0xfb80cffffc40ffff

def z1187 : W := mkw 0x002403c002203500 0x400900f000880d40 0x11fc03000ee03802 0x047f00c003b80e00

def z1188 : W := mkw 0x20fefbedc0689109 0x083fbefb701a2442 0xf8ffffffe0e00000 0xfe3ffffff8380000

def z1189 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x35ff03f01ee03f82 0x4d7fc0fc07b80fe0

def z1190 : W := mkw 0x01b703e01ba03500 0x406dc0f806e80d40 0x31ff03001ee03802 0x0c7fc0c007b80e00

def z1191 : W := mkw 0x00b703e019a01100 0x002dc0f806680440 0x7dff03f01fe03983 0x5f7fc0fc07f80e60

def z1192 : W := mkw 0x81b703f4dba03780 0x606dc0fd36e80de0 0x7dff03f0ffe03f83 0x5f7fc0fc3ff80fe0

def z1193 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xfbfffc409fffc003 0xfeffff1027fff000

def z1194 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff03f11fe03ff3 0xdf7fc0fc47f80ffc

def z1195 : W := mkw 0x00fefbedc6122422 0x403fbefb71848908 0xfbfffffffe1f0633 0xfeffffffff87c18c

def z1196 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x78ffdffee0000000 0x5e3ff7ffb8000000

def z1197 : W := mkw 0x12dbfc0dfddbc017 0x84b6ff037f76f005 0xfbfffc0fffffc07f 0xbeffff03fffff01f

def z1198 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfffffcf11fffc7f3 0xffffff3c47fff1fc

def z1199 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x97e0e30f1e1f3e73 0xa5f838c3c787cf9c

def z1200 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0x7dff2ff1ffe33fff 0xdf7fcbfc7ff8cfff

def z1201 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xe3fffc001fffc000 0x38ffff0007fff000

def z1202 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffc001fffc633 0x3effff0007fff18c

def z1203 : W := mkw 0x002403edc0000000 0x000900fb70000000 0x20032fffe0000000 0xc800cbfff8000000

def z1204 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x11e0c30e1e1f3e32 0x047830c38787cf8c

def z1205 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x17e0c38f1e1f3e73 0xc5f830e3c787cf9c

def z1206 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff13f09fe0ff8f 0x5f7fc4fc27f83fe3

def z1207 : W := mkw 0x002403c002203500 0x400900f000880d40 0x5dfc03400fe03983 0x577f00d003f80e60

def z1208 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0xb9fce0000efc0002 0x2e7f380003bf0000

def z1209 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfefffffff103c7fd 0xffbffffffc40f1ff

def z1210 : W := mkw 0x602403cf82243d68 0x580900f3e0890f5a 0xee0033cf9103fffd 0xfb800cf3e440ffff

def z1211 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1fdf7ee1fcf9cf 0xf787f7dfb87f3e73

def z1212 : W := mkw 0xd001041237176ef6 0xf40041048dc5dbbd 0x070000001e1f3e73 0x01c000000787cf9c

def z1213 : W := mkw 0xd20104123fdfeef7 0xf48041048ff7fbbd 0x070000001fffffff 0x01c0000007ffffff

def z1214 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff3ff17fe3ffb3 0x7fffcffc5ff8ffec

def z1215 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x64033cf1f103c7fc 0xd900cf3c7c40f1ff

def z1216 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x79ff03701fe03983 0x1e7fc0dc07f80e60

def z1217 : W := mkw 0x91b707fdfba17794 0xe46dc1ff7ee85de5 0xffff3fffffe3ffff 0xffffcffffff8ffff

def z1218 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xdbfcd0001fffc003 0x36ff340007fff000

def z1219 : W := mkw 0x6248fc02045fc84b 0x98923f008117f212 0x8200fc00001fc04c 0x20803f000007f013

def z1220 : W := mkw 0x812403f002203780 0x604900fc00880de0 0x7dfc03f01fe03f83 0x5f7f00fc07f80fe0

def z1221 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfbfffc00ffffc00f 0x3effff003ffff003

def z1222 : W := mkw 0x00def96dc0000000 0x0037be5b70000000 0xf8fffc7fe0000000 0xbe3fff1ff8000000

def z1223 : W := mkw 0x40f2aaab46162c62 0x503caaaad1858b18 0x27e32cb17e1f3e73 0x09f8cb2c5f87cf9c

def z1224 : W := mkw 0x0000000000000000 0x0000000000000000 0xee033cf1f103c7fd 0xfb80cf3c7c40f1ff

def z1225 : W := mkw 0x4249fc0b155fc863 0x90927f02c557f218 0xee03fc8f111fc671 0xfb80ff23c447f19c

def z1226 : W := mkw 0x00d3a0001d920002 0x0034e80007648000 0x79ffc0001ffc0003 0x1e7ff00007ff0000

def z1227 : W := mkw 0x4248fc02045fc843 0x90923f008117f210 0x8200fc0e001fc040 0xa0803f038007f010

def z1228 : W := mkw 0x6048f00f845e886b 0x18123c03e117a21a 0x8200d00e801cc04c 0xa0803403a0073013

def z1229 : W := mkw 0x4060a2ab46162c62 0x501828aad1858b18 0xbfe0e3bf7e1f3e73 0xeff838efdf87cf9c

def z1230 : W := mkw 0x029200000cda8003 0x00a480000336a000 0x11fc00000efc0002 0x047f000003bf0000

def z1231 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0xfbfffc000effc002 0x3effff0003bff000

def z1232 : W := mkw 0x02dafc000cdbc003 0x80b6bf000336f000 0xbbfcfc001effc003 0x2eff3f0007bff000

def z1233 : W := mkw 0x81b703f49ba03780 0x606dc0fd26e80de0 0x7dff03fe9fe03f83 0xdf7fc0ffa7f80fe0

def z1234 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7dff1ff0ffe03f83 0x5f7fc7fc3ff80fe0

def z1235 : W := mkw 0x9001041031014294 0xa40041040c4050a5 0x66033cf1f103c7fd 0x1980cf3c7c40f1ff

def z1236 : W := mkw 0x00def964c0000000 0x0037be5930000000 0xf8ffff7ee0000000 0xfe3fffdfb8000000

def z1237 : W := mkw 0x00f6a3e900000000 0x003da8fa40000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1238 : W := mkw 0x00f6abedc0000000 0x003daafb70000000 0x78ff2fffe0000000 0xde3fcbfff8000000

def z1239 : W := mkw 0x0004014480000000 0x0001005120000000 0xe8033fffe0000000 0xfa00cffff8000000

def z1240 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfbfffc017fffc033 0x3effff005ffff00c

def z1241 : W := mkw 0x6248fc0fc45fc84b 0x98923f03f117f212 0x8200fc0fe01fc04c 0xa0803f03f807f013

def z1242 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff3ff01fe3ffff 0x7fffcffc07f8ffff

def z1243 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff13f09fe3ffff 0xffffc4fc27f8ffff

def z1244 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff23f01fe33f83 0x7fffc8fc07f8cfe0

def z1245 : W := mkw 0x02daf80dccda8003 0x00b6be037336a000 0x91fcfc0feefc0002 0xa47f3f03fbbf0000

def z1246 : W := mkw 0x00b703e01b802400 0x402dc0f806e00900 0x7dff03f01fe03e03 0x5f7fc0fc07f80f80

def z1247 : W := mkw 0x4248f80b045e8863 0x10923e02c117a218 0x0000c00e001c0000 0x0000300380070000

def z1248 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x7fff03f01fe0ffcf 0x5fffc0fc07f83ff3

def z1249 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0x51ffdc70effcc18e 0x147ff71c3bff3063

def z1250 : W := mkw 0x602403cf82243d68 0x580900f3e0890f5a 0x0400034e800039cc 0xc10000d3a0000e73

def z1251 : W := mkw 0x00f2aaadc0000000 0x003caaab70000000 0x20e32cbfe0000000 0x8838cb2ff8000000

def z1252 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0x31ffecb17eff0632 0x0c7ffb2c5fbfc18c

def z1253 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xbbfce0001fffc003 0x2eff380007fff000

def z1254 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff3ff0ffe3ff8f 0x7fffcffc3ff8ffe3

def z1255 : W := mkw 0x00daf800045a8003 0x0036be000116a000 0xfbfffc001fffc003 0x3effff0007fff000

def z1256 : W := mkw 0x919304103ba17794 0xe464c1040ee85de5 0xffff3cf1ffe3ffff 0xffffcf3c7ff8ffff

def z1257 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x93fce0000eff0002 0x24ff380003bfc000

def z1258 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfffffc81ffffc67f 0xffffff207ffff19f

def z1259 : W := mkw 0x004cf94dc0000000 0x00133e5370000000 0xf81fffffe0000000 0xfe07fffff8000000

def z1260 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x11ff03300ee03802 0x047fc0cc03b80e00

def z1261 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfaffffffe0030070 0xfebffffff800c01c

def z1262 : W := mkw 0x01fefbedc8a01100 0x007fbefb72280440 0xf8ffffffe0e00000 0xfe3ffffff8380000

def z1263 : W := mkw 0x4040a00206162c62 0x5010280081858b18 0xbfe0e30e1e1f3e73 0xeff838c38787cf9c

def z1264 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x3dff03b01ee03e03 0x4f7fc0ec07b80f80

def z1265 : W := mkw 0x0049f400155bc003 0x80127d000556f000 0xfbfffc001fffc003 0x3effff0007fff000

def z1266 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0xbffc23811ee33e73 0xefff08e047b8cf9c

def z1267 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0x7dff03f0ffe03f8f 0x5f7fc0fc3ff80fe3

def z1268 : W := mkw 0x009e5964c0000000 0x0027965930000000 0xc01fdc7ee0000000 0xb007f71fb8000000

def z1269 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xbfe0e30e1e1f3e73 0x2ff838c38787cf9c

def z1270 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x71ff03f01fe03f82 0x1c7fc0fc07f80fe0

def z1271 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffc71ffffc1ff 0xbeffff1c7ffff07f

def z1272 : W := mkw 0x00fefbedc0201100 0x003fbefb70080440 0xfcffffffe0003980 0xff3ffffff8000e60

def z1273 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0x7fff03f01fe3ff83 0x5fffc0fc07f8ffe0

def z1274 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x13fcc0001eff0003 0x04ff300007bfc000

def z1275 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0x3fe0c38e1e1f3e73 0x4ff830e38787cf9c

def z1276 : W := mkw 0x4060aa8b46162c62 0x50182aa2d1858b18 0xbfe0ef8f7e1f3e73 0xeff83be3df87cf9c

def z1277 : W := mkw 0x00be5be4c0000000 0x002f96f930000000 0xf8ffdffee0000000 0xfe3ff7ffb8000000

def z1278 : W := mkw 0x00d3a4001d934002 0x8034e9000764d000 0xfbfffc001fffc003 0x3effff0007fff000

def z1279 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x11fc03f00ee03802 0x447f00fc03b80e00

def z1280 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xffff13f01fe0ff83 0x7fffc4fc07f83fe0

def z1281 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cff4fe1fcf9cf 0xf7873fd3f87f3e73

def z1282 : W := mkw 0x20fefbedc0201108 0x083fbefb70080442 0xf8ffffffe000018c 0xfe3ffffff8000063

def z1283 : W := mkw 0x00fafaadc0000000 0x003ebeab70000000 0xf8fffcbfe0000000 0xbe3fff2ff8000000

def z1284 : W := mkw 0xf0010412314dcadd 0xbc0041048c5372b7 0x06000000111fc7fd 0x018000000447f1ff

def z1285 : W := mkw 0x0000000dc0000000 0x0000000370000000 0xe8033cffe0000000 0xfa00cf3ff8000000

def z1286 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xfcffffffe00001cc 0xff3ffffff8000073

def z1287 : W := mkw 0x02dbfc04dddbc003 0x80b6ff013776f000 0xfbfffc00ffffc003 0x3effff003ffff000

def z1288 : W := mkw 0x0048f000045a8003 0x00123c000116a000 0xfffcf0c19fffc7ff 0xffff3c3067fff1ff

def z1289 : W := mkw 0xf12507f6b3257fdc 0xfc4941fdacc95ff7 0xee033ffff103fffd 0xfb80cffffc40ffff

def z1290 : W := mkw 0x0008500480000000 0x0002140120000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z1291 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfffffc811fffc7ff 0xffffff2047fff1ff

def z1292 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xde1cd30e01fcf9cf 0x378734c3807f3e73

def z1293 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0x11fc03001ee03e02 0x047f00c007b80f80

def z1294 : W := mkw 0x02dbf8001dda8003 0x00b6fe000776a000 0xf9fffc001ffc0003 0x3e7fff0007ff0000

def z1295 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0xda1cd34e81fcf98f 0x368734d3a07f3e63

def z1296 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x79ffc0000efc0002 0x1e7ff00003bf0000

def z1297 : W := mkw 0x00dbf8001d920002 0x0036fe0007648000 0xfbfffc001fff0003 0x3effff0007ffc000

def z1298 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xb9e0e38f1e1f3e32 0xee7838e3c787cf8c

def z1299 : W := mkw 0x83b70ff01ba17780 0xe0edc3fc06e85de0 0x7dff0ff01fe03f83 0x5f7fc3fc07f80fe0

def z1300 : W := mkw 0x9097055039a15394 0xa425c1540e6854e5 0xffff3ff1ffe3ffff 0xffffcffc7ff8ffff

def z1301 : W := mkw 0xf249fc16b55fcadf 0xbc927f05ad57f2b7 0xee03fcfff11fc7fd 0xfb80ff3ffc47f1ff

def z1302 : W := mkw 0x82dbfc101ddbc283 0xa0b6ff040776f0a0 0xfbfffc701fffc183 0x3effff1c07fff060

def z1303 : W := mkw 0x00fefbedc6122422 0x403fbefb71848908 0xf9ffffffee000000 0xfe7ffffffb800000

def z1304 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0xb3fffc001effc002 0x2cffff0007bff000

def z1305 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x39fcc0001efc0003 0x0e7f300007bf0000

def z1306 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0xa0e3ffffe0000000 0xe838fffff8000000

def z1307 : W := mkw 0xa1b703f49ba03788 0x686dc0fd26e80de2 0x7dff03f09fe03f8f 0x5f7fc0fc27f80fe3

def z1308 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x5e1cc34e01fcf9cf 0x578730d3807f3e73

def z1309 : W := mkw 0x0008500000488001 0x0002140000122000 0xfbfcd0001ffcc003 0x3eff340007ff3000

def z1310 : W := mkw 0x02dbfc001ddbc003 0x80b6ff000776f000 0x11ffcc000efc0002 0x047ff30003bf0000

def z1311 : W := mkw 0x81b707f01ba17780 0xe06dc1fc06e85de0 0xffff3ff11fe3fff3 0xffffcffc47f8fffc

def z1312 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0x7dff03f17fe03fb3 0x5f7fc0fc5ff80fec

def z1313 : W := mkw 0x00fefbedc0689101 0x003fbefb701a2440 0xfeffffffe1fcf983 0xffbffffff87f3e60

def z1314 : W := mkw 0x91b703fdfba03794 0x646dc0ff7ee80de5 0x7dff03ffffe03fff 0xdf7fc0fffff80fff

def z1315 : W := mkw 0x00fefbedc4120002 0x003fbefb71048000 0xfaffffffe01f0000 0xfebffffff807c000

def z1316 : W := mkw 0x0093000019800000 0x0024c00006600000 0xfbffc0001ffc0003 0x3efff00007ff0000

def z1317 : W := mkw 0x0040a00004120002 0x0010280001048000 0xfbfce0001fff0003 0x3eff380007ffc000

def z1318 : W := mkw 0x90b306903b816694 0xe42cc1a40ee059a5 0xffff3ff1ffe3ffff 0xffffcffc7ff8ffff

def z1319 : W := mkw 0x02daf8000cda8003 0x00b6be000336a000 0x93fcd0000efcc002 0x24ff340003bf3000

def z1320 : W := mkw 0x92dbfc103ddbc297 0xa4b6ff040f76f0a5 0xfbfffcb1ffffc67f 0xbeffff2c7ffff19f

def z1321 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x59fc03400ee03802 0x567f00d003b80e00

def z1322 : W := mkw 0x12dbfc003ddbc017 0x84b6ff000f76f005 0xfffffc41ffffc1ff 0xffffff107ffff07f

def z1323 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x961cd30e81fcf9cf 0xa58734c3a07f3e73

def z1324 : W := mkw 0x81b703f01ba03780 0x606dc0fc06e80de0 0xfdffc3fe1fe03f83 0xff7ff0ff87f80fe0

def z1325 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x7dff03f00fe03983 0x5f7fc0fc03f80e60

def z1326 : W := mkw 0x000c514480000000 0x0003145120000000 0xd81fdf7ee0000000 0xf607f7dfb8000000

def z1327 : W := mkw 0x600c5146806c9949 0x18031451a01b2652 0x161cc34e81fcf9cf 0xc58730d3a07f3e73

def z1328 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x1dfc03000ee03803 0x477f00c003b80e00

def z1329 : W := mkw 0x4060a28b06162c62 0x501828a2c1858b18 0xfffce38f1fff3e73 0xffff38e3c7ffcf9c

def z1330 : W := mkw 0x01b603e00aa03500 0x406d80f802a80d40 0x59fc03000fe03803 0x167f00c003f80e00

def z1331 : W := mkw 0x00fefbedc0000000 0x003fbefb70000000 0x78ffefff60000000 0x5e3ffbffd8000000

def z1332 : W := mkw 0x91b703f03ba03794 0x646dc0fc0ee80de5 0x7dff03f01fe03fff 0x5f7fc0fc07f80fff

def z1333 : W := mkw 0x91b707f03ba17794 0xe46dc1fc0ee85de5 0xffff1ff0ffe0ffcf 0xffffc7fc3ff83ff3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z9,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z11,z6]),(0,[z12,z8,z1,z2,z4,z5,z13])],[(0,[z8,z1,z2,z4,z5,z6,z14]),(1,[z1,z15,z2,z4,z5,z6]),(1,[z16,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z17]),(0,[z12,z8,z1,z2,z4,z18,z6]),(0,[z19,z10,z1,z2,z4,z5,z6])],[(0,[z20,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z21,z2,z4,z5,z6]),(0,[z8,z22,z2,z23,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z24,z25]),(0,[z8,z26,z1,z2,z4,z5,z6])],[(0,[z27,z1,z28,z2,z4,z5,z6]),(0,[z29,z8,z1,z2,z4,z5,z6]),(0,[z0,z8,z1,z2,z4,z30,z6]),(0,[z31,z32,z1,z2,z4,z5,z6])],[(1,[z8,z1,z2,z4,z33,z6]),(0,[z27,z1,z2,z34,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z35]),(0,[z36,z8,z1,z2,z4,z6,z37]),(0,[z8,z22,z38,z2,z4,z5,z6]),(0,[z39,z8,z1,z2,z4,z40,z6]),(0,[z41,z8,z1,z2,z4,z5,z6]),(0,[z8,z42,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z43,z4,z5,z6]),(0,[z44,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z45,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z46,z6]),(0,[z47,z8,z2,z4,z5,z6,z48]),(0,[z8,z22,z49,z2,z4,z5,z6]),(0,[z12,z8,z1,z2,z5,z6,z13]),(0,[z50,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z51,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z52]),(0,[z53,z8,z1,z2,z4,z5,z6]),(0,[z8,z54,z1,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z5,z6,z55]),(0,[z8,z10,z1,z56,z2,z4,z6])],[(0,[z8,z1,z57,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z5,z58,z6]),(0,[z8,z1,z59,z4,z5,z60,z6]),(1,[z61,z8,z1,z2,z6,z62])]],
   [[(0,[z63,z8,z1,z2,z4,z5,z6]),(0,[z64,z8,z2,z4,z5,z6,z48]),(0,[z8,z22,z2,z4,z5,z6,z37]),(0,[z8,z1,z2,z4,z65,z5,z6]),(0,[z66,z8,z1,z2,z4,z65,z6]),(0,[z67,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z68,z5,z6]),(0,[z12,z8,z1,z69,z4,z5,z6])],[(0,[z70,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z48,z71])],[(0,[z72,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z73,z5,z6]),(0,[z39,z8,z22,z2,z4,z5,z6]),(0,[z12,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z74,z5,z6])],[(0,[z8,z1,z75,z2,z4,z5,z6]),(0,[z36,z1,z2,z4,z5,z11,z6])],[(0,[z76,z1,z28,z2,z4,z5,z6]),(0,[z77,z78,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z79,z5,z6]),(0,[z8,z1,z2,z4,z80,z5,z6]),(0,[z39,z8,z1,z2,z4,z30,z6]),(1,[z81,z8,z82,z4,z5,z6]),(0,[z8,z1,z83,z4,z65,z5,z6]),(0,[z8,z1,z84,z2,z4,z5,z6]),(0,[z8,z1,z2,z5,z85,z6,z13])],[(0,[z86,z1,z2,z4,z5,z11,z6]),(0,[z8,z1,z2,z4,z87,z5,z6]),(0,[z39,z8,z88,z2,z4,z5,z6]),(1,[z8,z22,z2,z4,z5,z89]),(0,[z8,z2,z4,z5,z60,z6,z90]),(0,[z61,z8,z1,z2,z4,z5,z6])],[(0,[z91,z92,z1,z2,z4,z5,z6]),(0,[z93,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z94,z6]),(0,[z8,z95,z1,z2,z4,z5,z6]),(1,[z8,z96,z1,z2,z4,z6]),(0,[z10,z97,z1,z2,z4,z5,z6]),(0,[z8,z98,z99,z2,z4,z5,z6])],[(0,[z1,z28,z2,z3,z4,z5,z6]),(0,[z36,z8,z2,z4,z5,z6,z48]),(0,[z8,z2,z4,z5,z6,z52,z48]),(0,[z8,z1,z2,z100,z4,z5,z6]),(0,[z8,z22,z1,z2,z4,z5,z89]),(0,[z61,z101,z1,z2,z4,z5,z6])]],
   [[(0,[z8,z102,z1,z2,z4,z5,z6]),(0,[z27,z91,z1,z2,z4,z5,z6]),(0,[z91,z8,z2,z4,z5,z6,z48]),(0,[z103,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z104,z105,z6]),(0,[z8,z88,z1,z49,z2,z4,z6]),(0,[z8,z22,z2,z4,z5,z6,z13]),(0,[z8,z10,z1,z106,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z107]),(0,[z8,z1,z2,z4,z5,z6,z108])],[(0,[z8,z22,z2,z4,z5,z11,z6]),(0,[z8,z1,z2,z4,z109,z5,z6]),(0,[z8,z110,z2,z4,z111,z5,z6]),(0,[z8,z1,z112,z2,z4,z5,z6])],[(0,[z27,z8,z1,z2,z4,z5,z113]),(0,[z8,z1,z2,z4,z5,z6,z52]),(0,[z114,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z111,z5,z37])],[(0,[z8,z1,z15,z2,z4,z5,z6]),(0,[z8,z16,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z115,z62]),(0,[z8,z10,z97,z1,z2,z4,z6])],[(0,[z8,z1,z2,z116,z4,z5,z6]),(0,[z8,z117,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z118,z6]),(0,[z47,z8,z1,z2,z4,z6,z25]),(0,[z8,z1,z2,z4,z119,z6,z37]),(0,[z8,z1,z120,z2,z4,z5,z6])],[(0,[z27,z8,z1,z2,z4,z5,z52]),(0,[z121,z8,z2,z4,z5,z6,z48]),(0,[z8,z59,z2,z4,z5,z6,z48]),(1,[z122,z1,z2,z4,z5,z6]),(0,[z8,z1,z123,z2,z4,z5,z6]),(0,[z8,z124,z1,z2,z4,z6,z37])],[(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z81,z8,z2,z126,z4,z5,z6]),(0,[z8,z22,z2,z4,z5,z46,z6]),(1,[z8,z1,z2,z4,z127,z6]),(0,[z121,z8,z1,z83,z4,z5,z6]),(0,[z128,z8,z1,z2,z4,z5,z6]),(0,[z8,z26,z2,z4,z5,z85,z6]),(0,[z8,z10,z1,z129,z2,z4,z6])],[(0,[z130,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z131,z6]),(0,[z31,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z132,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z6,z133]),(0,[z8,z1,z2,z4,z134,z5,z6]),(0,[z8,z1,z2,z4,z46,z6,z37]),(1,[z8,z1,z2,z4,z135,z6]),(0,[z47,z8,z1,z2,z136,z4,z6]),(1,[z8,z137,z2,z4,z5,z6]),(0,[z61,z138,z1,z2,z4,z5,z6]),(0,[z139,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z1,z2,z4,z5,z6]),(0,[z78,z1,z2,z4,z79,z5,z6]),(0,[z8,z1,z140,z2,z4,z5,z6]),(1,[z8,z141,z2,z4,z5,z6]),(0,[z8,z142,z1,z2,z4,z5,z6])],[(0,[z27,z1,z2,z4,z5,z6,z52]),(0,[z64,z8,z1,z2,z4,z5,z6]),(0,[z143,z8,z10,z1,z2,z4,z6])],[(0,[z8,z28,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z5,z6,z144]),(0,[z12,z8,z1,z2,z145,z5,z6]),(0,[z8,z10,z1,z2,z4,z6,z6])],[(0,[z8,z1,z2,z146,z4,z5,z6]),(0,[z1,z2,z4,z5,z113,z6,z52]),(0,[z147,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z106,z2,z65,z5,z6]),(0,[z12,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z148,z37])],[(0,[z8,z1,z149,z2,z4,z5,z6]),(0,[z150,z8,z2,z4,z5,z6,z48]),(0,[z8,z2,z126,z4,z40,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z151]),(0,[z8,z2,z4,z5,z85,z6,z48]),(0,[z8,z10,z1,z2,z4,z89,z6]),(0,[z152,z8,z1,z4,z5,z6,z144])],[(0,[z8,z153,z1,z2,z4,z5,z6]),(0,[z27,z8,z154,z2,z4,z5,z6]),(0,[z8,z2,z136,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z5,z6,z155]),(0,[z8,z1,z2,z4,z5,z156,z6]),(0,[z8,z1,z2,z4,z157,z5,z6]),(0,[z8,z1,z2,z4,z5,z158,z6])],[(0,[z8,z1,z2,z4,z159,z5,z6]),(0,[z91,z8,z76,z2,z4,z5,z6]),(0,[z8,z1,z160,z2,z4,z5,z6]),(0,[z8,z1,z125,z4,z5,z6,z144]),(0,[z8,z1,z2,z4,z161,z5,z6]),(1,[z67,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z162]),(0,[z152,z8,z137,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z163])]],
   [[(0,[z164,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z165,z6]),(0,[z8,z166,z1,z2,z4,z5,z6]),(0,[z8,z1,z99,z2,z4,z111,z5]),(0,[z8,z1,z2,z4,z6,z37,z167]),(0,[z19,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z28,z2,z4,z6,z37]),(0,[z168,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z169,z5,z6]),(0,[z36,z8,z1,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z8,z170,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z171,z6]),(0,[z31,z8,z2,z4,z105,z5,z6]),(0,[z8,z88,z1,z2,z136,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z62]),(1,[z8,z10,z1,z2,z4,z6])],[(0,[z91,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z172]),(0,[z8,z1,z2,z34,z4,z6,z37]),(0,[z8,z1,z2,z4,z5,z173,z6])],[(0,[z174,z1,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z175,z6]),(0,[z8,z1,z2,z4,z176,z5,z6]),(0,[z8,z1,z2,z136,z4,z177,z6])],[(0,[z178,z8,z1,z2,z4,z5,z6]),(0,[z91,z77,z1,z2,z4,z5,z6]),(0,[z81,z39,z8,z2,z4,z5,z6]),(0,[z8,z1,z179,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z6,z180])],[(0,[z181,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z182,z6]),(0,[z183,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z89,z6,z180]),(1,[z47,z8,z1,z4,z6,z25]),(0,[z8,z1,z2,z4,z5,z6,z184])],[(0,[z8,z1,z2,z4,z5,z6,z185]),(0,[z8,z186,z2,z4,z5,z6,z48]),(0,[z8,z1,z187,z2,z4,z5,z6])],[(0,[z8,z1,z188,z2,z4,z5,z6]),(0,[z121,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z145,z65,z5,z6])]],
   [[(0,[z189,z8,z1,z2,z4,z5,z6]),(0,[z190,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z40,z5,z6]),(0,[z39,z8,z2,z4,z5,z6,z48]),(0,[z191,z8,z22,z2,z4,z5,z6]),(0,[z47,z8,z1,z49,z4,z5,z6]),(0,[z152,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z192,z6]),(0,[z31,z8,z54,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z193,z5,z6]),(0,[z8,z194,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z195,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z196,z6]),(0,[z8,z197,z1,z82,z4,z5,z6]),(0,[z8,z198,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z199]),(0,[z8,z200,z1,z2,z4,z5,z6]),(0,[z39,z8,z1,z49,z2,z4,z6]),(0,[z8,z2,z4,z5,z6,z48,z62]),(0,[z47,z8,z22,z2,z4,z5,z6]),(0,[z201,z8,z1,z2,z4,z5,z6]),(0,[z8,z202,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z145,z79,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z203]),(0,[z204,z8,z1,z2,z82,z4,z6]),(1,[z8,z1,z59,z4,z5,z60]),(1,[z8,z1,z2,z4,z205,z6]),(1,[z12,z8,z1,z2,z5,z13]),(0,[z8,z1,z2,z4,z5,z6,z148]),(1,[z8,z98,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z206]),(0,[z8,z2,z4,z105,z5,z6,z48]),(0,[z8,z22,z2,z4,z5,z6,z6]),(0,[z8,z10,z22,z1,z2,z4,z6]),(0,[z8,z207,z1,z2,z4,z5,z6]),(0,[z208,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z104,z5,z6]),(0,[z8,z88,z1,z2,z4,z40,z6]),(0,[z8,z1,z2,z4,z5,z6,z209]),(0,[z210,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z211,z6]),(0,[z8,z1,z2,z212,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z85,z6])],[(0,[z77,z8,z10,z1,z2,z4,z6]),(0,[z8,z213,z1,z2,z4,z5,z6]),(0,[z8,z214,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z6,z37,z48]),(0,[z8,z22,z2,z215,z4,z5,z6]),(0,[z8,z22,z2,z4,z5,z89,z6]),(0,[z8,z1,z2,z216,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z163,z37])],[(0,[z8,z1,z2,z4,z217,z5,z6]),(0,[z8,z22,z2,z126,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z218,z6]),(0,[z219,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z88,z1,z2,z4,z6]),(1,[z8,z1,z2,z4,z220,z6]),(1,[z1,z2,z4,z5,z6,z221]),(0,[z8,z1,z2,z4,z5,z6,z222])]],
   [[(0,[z174,z8,z1,z3,z4,z5,z6]),(0,[z8,z1,z2,z223,z4,z5,z6])],[(0,[z8,z76,z22,z2,z4,z5,z6]),(0,[z224,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z225]),(0,[z8,z1,z2,z4,z5,z6,z226]),(1,[z1,z2,z4,z5,z6,z227])],[(0,[z8,z1,z2,z4,z228,z5,z6]),(0,[z8,z229,z1,z2,z4,z5,z6]),(0,[z8,z1,z84,z2,z4,z6,z37])],[(0,[z8,z1,z2,z4,z5,z230,z6]),(0,[z8,z1,z2,z4,z231,z5,z6]),(0,[z8,z1,z2,z232,z4,z5,z6]),(0,[z8,z88,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z233]),(0,[z61,z8,z1,z2,z4,z6,z37]),(0,[z8,z1,z234,z2,z4,z5,z6])],[(0,[z235,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z59,z2,z4,z5,z6]),(0,[z8,z141,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z236,z4,z5,z6]),(0,[z91,z1,z2,z4,z5,z113,z6]),(1,[z1,z237,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z25]),(0,[z238,z8,z1,z2,z4,z5,z6])],[(1,[z91,z76,z2,z4,z5,z6]),(0,[z86,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z239]),(0,[z8,z1,z2,z4,z240,z5,z6]),(0,[z8,z1,z2,z4,z105,z6,z37])],[(0,[z39,z8,z76,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z241,z5,z6]),(0,[z183,z8,z1,z2,z4,z5,z48]),(0,[z8,z1,z2,z4,z5,z242,z6]),(0,[z8,z1,z2,z4,z60,z6,z243])]],
   [[(0,[z8,z1,z244,z2,z4,z5,z6]),(0,[z8,z2,z145,z4,z5,z6,z48]),(0,[z245,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z136,z177,z5,z6])],[(0,[z77,z1,z28,z2,z4,z5,z6]),(0,[z246,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z119,z5,z6,z48]),(0,[z8,z247,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z248]),(0,[z8,z1,z2,z4,z60,z6,z37]),(0,[z249,z8,z1,z2,z4,z6,z37])],[(0,[z8,z1,z2,z4,z5,z6,z250]),(0,[z77,z1,z2,z34,z4,z5,z6]),(0,[z152,z8,z1,z2,z4,z251,z6])],[(0,[z81,z8,z2,z82,z4,z5,z6]),(0,[z39,z8,z1,z2,z136,z4,z6]),(0,[z1,z2,z4,z5,z6,z221,z144]),(0,[z8,z1,z2,z136,z4,z6,z62])],[(0,[z8,z1,z252,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z253])],[(0,[z8,z1,z2,z254,z4,z5,z6]),(0,[z255,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z256]),(0,[z47,z8,z1,z2,z4,z6,z37]),(0,[z61,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z257,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z258])],[(0,[z8,z1,z28,z2,z4,z5,z6]),(0,[z8,z38,z2,z126,z4,z5,z6]),(1,[z31,z8,z2,z105,z5,z6]),(0,[z8,z2,z4,z5,z6,z48,z25])],[(0,[z8,z1,z2,z4,z5,z259,z6]),(0,[z8,z22,z2,z4,z30,z5,z6]),(1,[z8,z2,z4,z5,z6,z260]),(0,[z8,z1,z261,z2,z4,z5,z6]),(1,[z95,z1,z2,z4,z5,z6]),(0,[z262,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z78,z8,z10,z1,z2,z4,z6]),(0,[z8,z214,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z263]),(0,[z264,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z265,z6]),(0,[z8,z1,z137,z2,z4,z5,z6]),(0,[z152,z8,z1,z59,z4,z5,z6])],[(0,[z8,z1,z2,z4,z266,z5,z6]),(0,[z47,z8,z1,z2,z4,z119,z6]),(0,[z8,z1,z2,z4,z5,z6,z221])],[(0,[z8,z1,z125,z59,z4,z5,z6]),(0,[z8,z1,z2,z4,z267,z5,z6]),(0,[z8,z1,z2,z4,z5,z268,z6]),(0,[z8,z1,z2,z4,z269,z5,z6]),(1,[z270,z22,z2,z4,z5,z6]),(0,[z271,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z37,z144]),(1,[z272,z1,z2,z4,z5,z6]),(0,[z12,z8,z1,z2,z4,z6,z37])],[(0,[z92,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z273]),(0,[z8,z1,z2,z4,z5,z274,z6]),(0,[z8,z1,z2,z4,z5,z6,z71]),(0,[z8,z1,z2,z4,z275,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z227])],[(0,[z276,z8,z1,z2,z4,z5,z6]),(0,[z8,z117,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z277]),(0,[z0,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z278,z2,z4,z5,z6]),(0,[z121,z8,z1,z106,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z279,z6]),(0,[z8,z1,z2,z4,z280,z5,z6]),(1,[z8,z110,z2,z4,z5,z6]),(1,[z10,z97,z1,z2,z4,z6]),(0,[z8,z10,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z281,z5,z6]),(0,[z8,z1,z2,z4,z6,z52,z37]),(0,[z8,z1,z2,z4,z282,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z283]),(0,[z8,z197,z22,z2,z4,z5,z6]),(0,[z8,z10,z197,z1,z2,z4,z6]),(1,[z8,z1,z2,z4,z104,z6]),(0,[z8,z88,z1,z2,z4,z6,z37]),(0,[z8,z2,z4,z5,z60,z6,z48]),(0,[z8,z22,z2,z145,z4,z5,z6]),(0,[z8,z1,z59,z4,z65,z5,z6]),(0,[z152,z95,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z177,z6,z37]),(0,[z8,z1,z2,z4,z284,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z285])],[(0,[z91,z8,z28,z2,z4,z5,z6]),(0,[z8,z1,z3,z4,z5,z6,z144]),(0,[z8,z1,z2,z4,z286,z5,z6]),(1,[z8,z154,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z287,z6]),(0,[z288,z8,z2,z4,z65,z5,z6]),(0,[z8,z1,z2,z4,z289,z5,z6]),(0,[z8,z1,z237,z2,z4,z5,z6])]],
   [[(0,[z91,z8,z1,z2,z4,z6,z37]),(0,[z8,z290,z1,z2,z4,z5,z6]),(0,[z8,z2,z126,z4,z105,z5,z6]),(0,[z291,z8,z1,z2,z4,z5,z6]),(0,[z208,z8,z2,z4,z5,z6,z25]),(0,[z8,z1,z2,z4,z6,z37,z62])],[(0,[z8,z1,z2,z292,z4,z5,z6]),(0,[z86,z8,z1,z2,z4,z6,z37]),(1,[z78,z1,z2,z4,z5,z113]),(0,[z8,z1,z2,z65,z5,z6,z13]),(0,[z8,z1,z2,z4,z293,z5,z6]),(1,[z8,z10,z1,z99,z2,z4]),(0,[z294,z8,z1,z2,z4,z5,z6])],[(0,[z295,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z296,z5,z6]),(0,[z297,z8,z1,z2,z4,z5,z6])],[(0,[z298,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z299,z2,z4,z5,z6]),(0,[z300,z8,z1,z2,z4,z5,z6]),(1,[z8,z88,z2,z4,z40,z6]),(0,[z8,z1,z2,z4,z5,z6,z301]),(1,[z8,z2,z4,z5,z6,z115])],[(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z302,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z303,z2,z4,z5,z6]),(0,[z121,z8,z1,z4,z5,z6,z144]),(0,[z8,z1,z2,z304,z4,z5,z6]),(0,[z12,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z145,z5,z85,z6])],[(1,[z183,z8,z2,z4,z5,z48]),(0,[z121,z8,z1,z2,z4,z6,z37])],[(0,[z31,z81,z8,z2,z4,z5,z6]),(0,[z8,z1,z305,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z40,z6,z37]),(0,[z8,z1,z4,z119,z5,z6,z25]),(0,[z152,z8,z1,z2,z4,z5,z144])],[(0,[z8,z76,z2,z4,z5,z6,z48]),(0,[z0,z36,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z306,z5,z6]),(0,[z307,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z77,z1,z2,z4,z5,z6,z52]),(0,[z8,z1,z2,z4,z5,z308,z6]),(0,[z36,z8,z1,z2,z4,z11,z6]),(0,[z8,z22,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z309])],[(1,[z8,z1,z2,z4,z310,z6]),(0,[z311,z8,z1,z2,z4,z5,z6]),(0,[z36,z8,z10,z1,z2,z4,z6]),(0,[z81,z8,z197,z2,z4,z5,z6]),(0,[z8,z88,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z135,z5,z6]),(0,[z8,z22,z2,z4,z312,z5,z6]),(0,[z47,z313,z1,z2,z4,z5,z6])],[(0,[z91,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z314,z6]),(0,[z81,z315,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z316,z5,z6]),(0,[z8,z1,z2,z136,z4,z5,z6])],[(0,[z8,z1,z2,z4,z317,z5,z6]),(0,[z8,z1,z2,z4,z105,z5,z6]),(0,[z8,z1,z2,z4,z5,z318,z6]),(0,[z8,z1,z2,z4,z85,z6,z37])],[(0,[z86,z8,z2,z4,z5,z6,z48]),(0,[z8,z22,z2,z82,z4,z5,z6]),(0,[z8,z88,z1,z2,z4,z46,z6]),(0,[z8,z1,z319,z2,z4,z5,z6]),(0,[z8,z1,z320,z2,z4,z5,z6])],[(0,[z321,z8,z1,z2,z4,z5,z6]),(0,[z150,z8,z1,z2,z4,z6,z37]),(0,[z8,z1,z322,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z323,z5,z6]),(0,[z61,z39,z8,z1,z2,z4,z6]),(0,[z8,z2,z4,z40,z5,z46,z6]),(0,[z8,z1,z4,z65,z5,z6,z144]),(0,[z12,z8,z1,z2,z4,z5,z85])],[(0,[z92,z8,z1,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z324,z5,z6]),(1,[z8,z1,z106,z65,z5,z6]),(1,[z8,z325,z2,z4,z5,z6]),(0,[z249,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z326,z2,z4,z5,z6]),(1,[z8,z1,z322,z4,z5,z6]),(0,[z327,z8,z1,z2,z4,z5,z6]),(0,[z121,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z328,z6])]],
   [[(0,[z329,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z330,z2,z4,z5,z6]),(0,[z8,z1,z331,z2,z4,z5,z6]),(0,[z191,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z23,z4,z5,z6]),(0,[z8,z1,z49,z2,z4,z6,z25]),(1,[z8,z1,z2,z332,z5,z6])],[(0,[z8,z10,z76,z1,z2,z4,z6]),(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z79,z5,z6,z52]),(0,[z8,z2,z34,z4,z5,z6,z48]),(0,[z8,z197,z1,z2,z4,z6,z37]),(0,[z8,z49,z2,z4,z5,z6,z48]),(1,[z8,z1,z2,z4,z111,z37])],[(0,[z8,z1,z333,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z334,z5,z6]),(0,[z78,z8,z1,z2,z4,z5,z113]),(0,[z8,z1,z2,z4,z5,z6,z335]),(0,[z47,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z59,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z5,z6,z336])],[(0,[z8,z1,z337,z2,z4,z5,z6]),(0,[z47,z42,z1,z2,z4,z5,z6])],[(0,[z8,z338,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z34,z4,z6]),(0,[z8,z22,z339,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z340,z6]),(0,[z8,z1,z2,z4,z6,z37,z25]),(0,[z8,z1,z49,z2,z136,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z243]),(0,[z8,z1,z2,z4,z111,z6,z37])],[(0,[z86,z1,z125,z2,z4,z5,z6]),(0,[z78,z8,z1,z2,z4,z5,z52]),(0,[z8,z1,z2,z4,z5,z341,z6]),(0,[z183,z8,z1,z2,z4,z127,z6]),(0,[z8,z10,z1,z2,z4,z6,z48]),(0,[z342,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z343,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z344,z5,z6])],[(0,[z8,z1,z345,z2,z4,z5,z6]),(0,[z346,z8,z1,z2,z4,z5,z6]),(0,[z81,z8,z1,z82,z4,z5,z6]),(0,[z8,z1,z2,z347,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z37])],[(0,[z39,z8,z28,z2,z4,z5,z6]),(0,[z47,z39,z8,z1,z2,z4,z6]),(0,[z183,z8,z1,z2,z4,z135,z6]),(0,[z8,z1,z2,z4,z348,z5,z6]),(0,[z22,z1,z15,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z349,z5,z6]),(0,[z8,z1,z2,z4,z350,z5,z6]),(0,[z152,z8,z1,z2,z332,z5,z6])]],
   [[(0,[z351,z8,z1,z2,z4,z5,z6]),(0,[z8,z352,z1,z2,z4,z5,z6]),(0,[z39,z8,z1,z2,z4,z6,z37]),(0,[z353,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z354,z4,z5,z6]),(0,[z12,z8,z343,z2,z4,z5,z6])],[(0,[z8,z76,z1,z2,z4,z5,z6]),(0,[z92,z8,z2,z4,z5,z6,z48]),(0,[z8,z22,z125,z2,z4,z5,z6]),(0,[z31,z39,z8,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z6,z48]),(0,[z8,z355,z22,z2,z4,z5,z6]),(0,[z8,z22,z83,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z251,z5,z6]),(1,[z356,z8,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z357]),(0,[z0,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z5,z6,z358]),(0,[z8,z2,z4,z5,z113,z6,z48]),(0,[z8,z1,z2,z4,z5,z6,z359]),(0,[z8,z1,z2,z4,z5,z360,z6]),(0,[z361,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z362,z65,z6]),(1,[z363,z1,z2,z4,z5,z6]),(0,[z8,z364,z1,z2,z4,z5,z6]),(0,[z8,z229,z10,z1,z2,z4,z6])],[(0,[z8,z38,z2,z82,z4,z5,z6]),(0,[z8,z10,z1,z2,z82,z4,z6]),(0,[z8,z88,z1,z2,z4,z5,z6]),(0,[z8,z1,z365,z2,z4,z5,z6]),(0,[z8,z1,z366,z2,z4,z5,z6]),(0,[z8,z367,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z368]),(1,[z8,z2,z4,z5,z6,z90]),(0,[z8,z1,z2,z4,z177,z5,z6]),(0,[z8,z369,z1,z2,z4,z5,z6])],[(0,[z370,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z371]),(0,[z27,z8,z1,z2,z4,z131,z6]),(1,[z27,z1,z2,z4,z5,z52]),(0,[z8,z197,z2,z4,z5,z6,z48]),(0,[z8,z1,z372,z2,z4,z5,z6]),(0,[z8,z1,z373,z2,z4,z5,z6])],[(0,[z374,z8,z1,z2,z4,z5,z6]),(0,[z8,z125,z2,z4,z5,z6,z48]),(0,[z8,z325,z1,z2,z4,z5,z6]),(0,[z8,z1,z99,z2,z4,z6,z37])],[(0,[z375,z8,z1,z2,z4,z5,z6]),(0,[z86,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z376,z5,z6])],[(0,[z174,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z377,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z260]),(0,[z8,z1,z378,z2,z4,z5,z6]),(0,[z379,z1,z83,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z37,z263])]],
   [[(0,[z8,z1,z2,z380,z4,z5,z6]),(0,[z381,z8,z1,z2,z4,z5,z6]),(1,[z22,z15,z2,z4,z5,z6]),(0,[z8,z2,z4,z382,z65,z5,z6]),(0,[z8,z1,z383,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z384,z5,z6])],[(0,[z8,z1,z2,z4,z5,z385,z6]),(0,[z8,z1,z2,z4,z386,z5,z6]),(0,[z387,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z59,z2,z4,z5,z60]),(0,[z8,z2,z4,z5,z85,z6,z107])],[(0,[z8,z1,z2,z4,z388,z5,z6]),(0,[z8,z1,z2,z4,z389,z5,z6])],[(0,[z31,z8,z38,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z390,z5,z6]),(0,[z61,z8,z88,z1,z2,z4,z6]),(0,[z8,z1,z2,z391,z4,z5,z6])],[(0,[z8,z1,z392,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z393,z5,z6]),(0,[z8,z10,z1,z2,z4,z113,z6]),(0,[z8,z1,z2,z4,z5,z394,z6]),(0,[z8,z1,z2,z4,z5,z395,z6]),(0,[z8,z1,z2,z4,z5,z6,z396])],[(0,[z8,z1,z397,z2,z4,z5,z6]),(0,[z8,z1,z2,z398,z4,z5,z6]),(0,[z8,z1,z2,z4,z399,z5,z6]),(0,[z8,z97,z1,z2,z4,z5,z6])],[(0,[z91,z1,z2,z4,z79,z5,z6]),(0,[z8,z1,z2,z400,z4,z5,z6]),(0,[z39,z8,z1,z2,z4,z46,z6]),(0,[z8,z22,z2,z4,z5,z6,z48]),(0,[z8,z1,z401,z2,z4,z5,z6])],[(0,[z402,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z403,z6]),(0,[z8,z1,z154,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z48,z13]),(0,[z8,z22,z2,z4,z65,z5,z6]),(0,[z121,z8,z1,z2,z65,z5,z6]),(0,[z121,z8,z1,z59,z4,z5,z6]),(0,[z8,z1,z404,z2,z4,z5,z6])]],
   [[(0,[z92,z8,z76,z2,z4,z5,z6]),(0,[z379,z8,z1,z2,z4,z5,z6]),(1,[z8,z405,z2,z4,z5,z6]),(0,[z8,z214,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z406,z6]),(0,[z27,z8,z1,z322,z4,z5,z6]),(0,[z8,z1,z2,z407,z4,z5,z6]),(0,[z408,z8,z1,z2,z4,z5,z6]),(1,[z379,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z6,z144])],[(0,[z8,z1,z2,z3,z4,z6,z37]),(0,[z8,z1,z2,z4,z5,z409,z6]),(0,[z150,z8,z1,z2,z4,z5,z6]),(0,[z27,z8,z1,z2,z4,z393,z6]),(0,[z8,z1,z2,z4,z5,z6,z410]),(0,[z8,z88,z2,z4,z40,z5,z6]),(1,[z270,z1,z2,z4,z5,z6])],[(0,[z92,z8,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z79,z5,z6]),(0,[z411,z8,z1,z2,z4,z5,z6]),(0,[z8,z54,z1,z2,z105,z5,z6]),(0,[z412,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z413,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z115])],[(0,[z150,z77,z1,z2,z4,z5,z6]),(1,[z86,z1,z2,z34,z5,z6]),(0,[z86,z78,z1,z2,z4,z5,z6]),(0,[z0,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z414,z6]),(0,[z8,z2,z4,z5,z6,z415,z48]),(0,[z8,z363,z1,z2,z4,z5,z6])],[(0,[z416,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z417,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z418]),(0,[z8,z1,z419,z2,z4,z5,z6])],[(0,[z91,z86,z1,z2,z4,z5,z6]),(0,[z0,z77,z1,z2,z4,z5,z6]),(0,[z8,z197,z1,z2,z4,z5,z6]),(0,[z8,z1,z186,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z420,z5,z6]),(0,[z8,z1,z2,z421,z4,z5,z6]),(0,[z143,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z422,z2,z4,z5,z6])]],
   [[(0,[z91,z8,z1,z2,z4,z33,z6]),(0,[z423,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z136,z4,z6,z37]),(0,[z8,z1,z2,z4,z6,z424,z37])],[(0,[z425,z8,z1,z2,z4,z5,z6]),(1,[z174,z1,z3,z4,z5,z6]),(0,[z426,z8,z1,z2,z4,z5,z6]),(0,[z8,z427,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z362,z6]),(0,[z152,z8,z1,z2,z4,z220,z6]),(0,[z8,z1,z2,z4,z111,z5,z6])],[(0,[z81,z8,z22,z2,z4,z5,z6]),(0,[z428,z8,z1,z2,z4,z5,z6]),(0,[z31,z8,z1,z2,z105,z5,z6]),(0,[z8,z2,z4,z5,z6,z48,z429]),(0,[z8,z22,z15,z2,z4,z5,z6]),(0,[z66,z8,z1,z2,z4,z5,z6]),(0,[z121,z16,z1,z2,z4,z5,z6])],[(0,[z150,z8,z1,z2,z79,z5,z6]),(0,[z150,z1,z2,z4,z79,z5,z6]),(0,[z8,z1,z2,z4,z5,z5,z6]),(0,[z8,z1,z430,z2,z4,z5,z6]),(0,[z431,z8,z1,z2,z4,z5,z6]),(0,[z387,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z432]),(0,[z8,z1,z2,z4,z5,z6,z433])],[(1,[z8,z1,z2,z4,z6,z55])],[(0,[z8,z22,z2,z4,z5,z113,z6]),(0,[z39,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z434,z4,z5,z6])],[(0,[z8,z435,z1,z2,z4,z5,z6]),(1,[z8,z22,z2,z4,z5,z6]),(0,[z8,z22,z106,z2,z4,z5,z6]),(0,[z313,z8,z1,z2,z4,z5,z6]),(0,[z436,z8,z1,z2,z4,z5,z6]),(1,[z19,z1,z2,z4,z5,z6])],[(0,[z8,z28,z2,z4,z40,z5,z6]),(0,[z1,z83,z237,z2,z4,z5,z6])]],
   [[(0,[z27,z8,z437,z2,z4,z5,z6]),(0,[z8,z1,z38,z2,z4,z6,z37]),(0,[z8,z22,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z145,z4,z5,z13])],[(0,[z8,z1,z438,z2,z4,z5,z6]),(0,[z8,z106,z2,z4,z5,z6,z48]),(0,[z8,z1,z49,z2,z4,z6,z37])],[(0,[z8,z22,z2,z4,z5,z6,z144]),(0,[z8,z1,z2,z4,z439,z5,z6]),(0,[z8,z1,z99,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z440,z4,z6])],[(0,[z8,z1,z441,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z3,z4,z6]),(0,[z150,z86,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z442,z4,z5,z6])],[(0,[z443,z8,z1,z2,z4,z5,z6]),(0,[z183,z8,z1,z2,z4,z5,z89])],[(0,[z174,z8,z2,z4,z5,z6,z48]),(0,[z150,z1,z2,z4,z5,z113,z6]),(0,[z8,z1,z2,z4,z5,z6,z444]),(0,[z8,z1,z2,z126,z4,z5,z6]),(0,[z8,z247,z1,z2,z4,z89,z6]),(0,[z8,z1,z49,z2,z4,z119,z6]),(0,[z8,z1,z2,z4,z413,z5,z6]),(0,[z8,z1,z2,z4,z6,z37,z37])],[(0,[z8,z1,z2,z445,z4,z5,z6]),(0,[z270,z22,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z60,z6]),(0,[z8,z1,z2,z446,z4,z5,z6])],[(0,[z8,z1,z2,z447,z4,z5,z6]),(0,[z8,z448,z1,z2,z4,z5,z6]),(0,[z8,z76,z1,z2,z4,z6,z37]),(0,[z174,z8,z1,z125,z4,z5,z6]),(0,[z8,z1,z2,z4,z449,z5,z6]),(0,[z1,z2,z34,z4,z79,z5,z6]),(0,[z0,z1,z2,z4,z5,z113,z6]),(0,[z450,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z8,z451,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z452,z6]),(0,[z8,z1,z2,z332,z4,z5,z6]),(0,[z8,z453,z1,z2,z4,z5,z6])],[(0,[z27,z8,z1,z454,z4,z5,z6]),(0,[z455,z8,z1,z2,z4,z5,z6])],[(0,[z47,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z59,z2,z4,z5,z144])],[(0,[z456,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z457,z4,z5,z6]),(0,[z8,z1,z2,z458,z4,z5,z6]),(1,[z8,z247,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z459,z6]),(0,[z460,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z99,z2,z4,z5])],[(0,[z1,z28,z2,z4,z79,z5,z6]),(0,[z8,z1,z2,z461,z4,z5,z6]),(0,[z0,z1,z2,z4,z30,z5,z6]),(0,[z8,z1,z462,z2,z4,z5,z6]),(0,[z8,z1,z2,z463,z4,z5,z6])],[(0,[z464,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z131,z6]),(0,[z81,z8,z1,z2,z4,z6,z37]),(0,[z465,z8,z1,z2,z4,z5,z6]),(0,[z466,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z467,z5,z6])],[(0,[z8,z1,z2,z4,z5,z33,z6]),(0,[z8,z1,z2,z79,z5,z6,z13]),(0,[z8,z1,z2,z468,z4,z5,z6]),(0,[z8,z1,z2,z469,z4,z5,z6]),(0,[z8,z1,z2,z470,z4,z6,z37])],[(0,[z8,z2,z3,z4,z5,z6,z48]),(0,[z8,z54,z2,z126,z4,z5,z6]),(0,[z8,z2,z4,z111,z5,z6,z48]),(0,[z138,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z471,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z472]),(0,[z8,z1,z2,z473,z4,z5,z6])],[(0,[z474,z8,z1,z2,z4,z5,z6]),(0,[z1,z2,z34,z4,z5,z113,z6]),(0,[z8,z355,z1,z2,z4,z5,z6]),(1,[z255,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z475]),(0,[z8,z1,z2,z476,z4,z5,z6]),(0,[z8,z88,z1,z2,z4,z11,z6]),(0,[z8,z1,z477,z2,z4,z5,z6]),(0,[z8,z1,z478,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z37,z48])],[(0,[z8,z1,z2,z4,z5,z479,z6]),(0,[z8,z1,z480,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z481]),(1,[z8,z1,z2,z4,z18,z6]),(0,[z8,z1,z129,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z482,z5,z6]),(0,[z483,z8,z1,z2,z4,z5,z6]),(0,[z484,z8,z1,z2,z4,z5,z6])],[(0,[z86,z8,z1,z2,z34,z5,z6]),(0,[z8,z1,z2,z4,z11,z6,z37]),(0,[z8,z188,z2,z4,z5,z6,z48])],[(0,[z1,z28,z2,z4,z5,z113,z6]),(0,[z8,z1,z485,z2,z4,z5,z6]),(0,[z86,z8,z10,z1,z2,z4,z6]),(0,[z8,z2,z4,z5,z6,z481,z48]),(0,[z270,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z486,z5,z6])],[(0,[z8,z1,z2,z4,z5,z487,z6]),(0,[z174,z8,z1,z2,z4,z5,z6]),(0,[z77,z8,z1,z3,z4,z5,z6]),(0,[z8,z1,z2,z4,z488,z5,z6]),(0,[z489,z8,z1,z2,z4,z5,z6]),(1,[z8,z10,z22,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z490]),(0,[z8,z1,z2,z4,z491,z5,z6]),(0,[z492,z8,z1,z2,z4,z5,z6]),(0,[z8,z405,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z6,z37])]],
   [[(0,[z92,z8,z28,z2,z4,z5,z6]),(0,[z493,z8,z1,z2,z4,z5,z6]),(0,[z27,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z113,z6,z37]),(0,[z81,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z5,z6,z415]),(0,[z8,z22,z2,z4,z119,z5,z6]),(0,[z121,z67,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z18,z5,z6]),(0,[z494,z8,z1,z2,z4,z5,z6])],[(0,[z174,z77,z1,z2,z4,z5,z6]),(1,[z315,z1,z2,z4,z5,z6]),(0,[z8,z495,z22,z2,z4,z5,z6]),(0,[z47,z8,z1,z4,z5,z6,z25]),(0,[z8,z1,z2,z496,z4,z5,z6]),(0,[z12,z8,z1,z2,z4,z205,z6])],[(0,[z0,z8,z1,z2,z4,z6,z37]),(0,[z8,z497,z1,z2,z4,z5,z6]),(0,[z8,z99,z2,z4,z5,z6,z48]),(1,[z8,z1,z69,z4,z5,z6]),(0,[z8,z1,z2,z4,z498,z5,z6])],[(1,[z8,z1,z2,z4,z393,z6]),(0,[z8,z1,z2,z4,z5,z6,z499]),(0,[z8,z10,z1,z2,z4,z40,z6]),(0,[z8,z22,z59,z2,z4,z5,z6]),(0,[z288,z8,z1,z2,z4,z5,z6]),(0,[z272,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z113,z6,z359]),(1,[z8,z2,z4,z5,z6,z48])],[(0,[z8,z1,z2,z4,z5,z6,z500]),(0,[z1,z125,z2,z4,z5,z113,z6]),(0,[z78,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z38,z2,z4,z5,z6]),(0,[z8,z1,z501,z2,z4,z5,z6]),(0,[z8,z2,z4,z65,z5,z6,z48]),(0,[z8,z1,z2,z4,z502,z5,z6])],[(0,[z1,z2,z3,z4,z5,z11,z6]),(0,[z8,z1,z2,z4,z503,z5,z6]),(0,[z504,z8,z1,z2,z4,z5,z6]),(1,[z66,z8,z1,z2,z4,z6]),(0,[z8,z1,z49,z2,z4,z5,z6]),(0,[z8,z1,z505,z2,z4,z5,z6]),(1,[z97,z1,z2,z4,z5,z6])],[(0,[z8,z2,z4,z79,z5,z6,z48]),(1,[z204,z8,z1,z2,z4,z6]),(1,[z39,z8,z2,z4,z46,z6]),(0,[z8,z2,z4,z5,z89,z6,z48]),(0,[z506,z8,z22,z2,z4,z5,z6]),(0,[z8,z10,z1,z83,z2,z4,z6]),(0,[z8,z1,z2,z69,z4,z5,z6])]],
   [[(1,[z77,z1,z125,z4,z5,z6]),(0,[z8,z10,z1,z125,z2,z4,z6]),(0,[z8,z290,z1,z2,z4,z113,z6]),(0,[z8,z1,z83,z2,z5,z6,z13]),(0,[z152,z8,z325,z2,z4,z5,z6])],[(0,[z86,z1,z28,z2,z4,z5,z6]),(0,[z150,z8,z1,z2,z34,z5,z6]),(0,[z8,z507,z1,z2,z4,z5,z6]),(0,[z8,z508,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z509]),(0,[z8,z10,z22,z2,z4,z5,z6]),(0,[z510,z8,z1,z2,z4,z5,z6])],[(0,[z150,z8,z10,z1,z2,z4,z6]),(0,[z86,z1,z2,z34,z4,z5,z6]),(0,[z8,z2,z4,z5,z11,z6,z48]),(0,[z8,z2,z4,z30,z5,z6,z48]),(0,[z8,z2,z82,z4,z5,z6,z48]),(0,[z8,z1,z511,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z512]),(0,[z8,z10,z1,z2,z4,z65,z6]),(0,[z122,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z177,z6])],[(0,[z92,z8,z10,z1,z2,z4,z6]),(0,[z0,z8,z1,z2,z4,z11,z6]),(0,[z8,z10,z1,z2,z4,z30,z6]),(0,[z513,z1,z2,z4,z5,z6,z13]),(1,[z8,z1,z2,z145,z5,z85])],[(0,[z0,z8,z10,z1,z2,z4,z6]),(1,[z8,z22,z2,z4,z6,z37]),(1,[z288,z8,z2,z4,z5,z6]),(0,[z8,z1,z514,z2,z4,z5,z6]),(0,[z8,z99,z320,z2,z4,z5,z6])],[(0,[z8,z22,z28,z2,z4,z5,z6]),(0,[z139,z8,z1,z2,z4,z5,z6]),(0,[z0,z8,z507,z2,z4,z5,z6]),(0,[z8,z1,z515,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z516]),(0,[z8,z1,z2,z4,z517,z5,z6]),(0,[z518,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z48,z519]),(0,[z50,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z520]),(0,[z1,z2,z4,z5,z6,z227,z13])],[(0,[z8,z1,z2,z4,z310,z5,z6]),(0,[z8,z22,z2,z34,z4,z5,z6]),(0,[z8,z1,z2,z4,z521,z5,z6]),(0,[z8,z22,z1,z2,z4,z6,z37]),(1,[z8,z1,z49,z4,z119,z6]),(0,[z8,z10,z1,z2,z145,z4,z6])],[(0,[z8,z1,z2,z4,z522,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z523]),(0,[z8,z1,z2,z177,z5,z6,z62])]],
   [[(0,[z27,z150,z1,z2,z4,z5,z6]),(0,[z524,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z525,z5,z6])],[(1,[z8,z437,z2,z4,z5,z6]),(0,[z8,z54,z1,z2,z126,z5,z6]),(0,[z8,z1,z2,z526,z4,z5,z6]),(0,[z61,z47,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z13])],[(0,[z174,z1,z2,z4,z5,z113,z6]),(0,[z8,z1,z2,z4,z5,z6,z527]),(0,[z8,z1,z2,z4,z5,z11,z6]),(0,[z81,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z82,z4,z5,z6]),(0,[z528,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z529,z6])],[(0,[z8,z10,z1,z2,z4,z79,z6]),(0,[z27,z8,z1,z2,z4,z6,z37]),(0,[z8,z10,z1,z2,z4,z6,z52]),(0,[z8,z315,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z126,z4,z6,z37]),(0,[z8,z1,z2,z470,z4,z5,z6])],[(0,[z530,z8,z1,z2,z4,z5,z6]),(0,[z39,z8,z1,z2,z4,z11,z6]),(0,[z8,z1,z2,z4,z5,z6,z424])],[(0,[z8,z1,z2,z4,z531,z5,z6]),(0,[z8,z1,z2,z4,z532,z5,z6]),(0,[z39,z8,z10,z1,z2,z4,z6]),(0,[z8,z2,z4,z40,z5,z6,z48]),(1,[z121,z8,z1,z83,z5,z6]),(1,[z208,z8,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z5,z37])],[(1,[z8,z1,z2,z4,z5,z6]),(0,[z92,z1,z28,z2,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z533,z8,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z79,z5,z11,z6]),(0,[z8,z22,z2,z4,z5,z287,z6]),(0,[z8,z1,z2,z4,z5,z6,z180]),(0,[z8,z1,z2,z4,z534,z5,z6])],[(0,[z535,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z536]),(0,[z27,z8,z1,z2,z522,z5,z6]),(0,[z81,z44,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z46,z6]),(0,[z8,z1,z2,z4,z5,z6,z537])]],
   [[(0,[z36,z8,z1,z2,z4,z30,z6]),(0,[z27,z8,z1,z2,z116,z5,z6]),(0,[z31,z8,z1,z2,z126,z5,z6]),(0,[z8,z54,z22,z2,z4,z5,z6]),(0,[z538,z8,z2,z4,z5,z6,z48]),(0,[z12,z272,z1,z2,z4,z5,z6]),(0,[z539,z8,z1,z2,z4,z5,z6])],[(0,[z540,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z348,z5,z6,z48]),(0,[z541,z8,z1,z2,z4,z5,z6]),(0,[z61,z8,z1,z2,z5,z6,z62])],[(0,[z86,z8,z1,z2,z79,z5,z6]),(0,[z27,z1,z2,z4,z5,z11,z6]),(0,[z0,z8,z326,z2,z4,z5,z6]),(1,[z8,z1,z454,z4,z5,z6]),(0,[z8,z1,z2,z4,z542,z5,z6]),(0,[z543,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z544,z4,z5,z6]),(0,[z8,z1,z2,z545,z4,z5,z6])],[(0,[z8,z76,z2,z4,z40,z5,z6]),(0,[z8,z1,z546,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z126,z4,z6])],[(0,[z8,z1,z2,z4,z5,z547,z6]),(0,[z8,z1,z2,z4,z5,z548,z6]),(0,[z8,z1,z2,z4,z5,z6,z549]),(0,[z8,z1,z2,z4,z5,z6,z429]),(0,[z8,z1,z550,z2,z4,z5,z6]),(1,[z8,z194,z1,z2,z4,z6])],[(0,[z551,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z205,z6]),(0,[z8,z10,z1,z2,z463,z4,z6])],[(0,[z8,z1,z2,z552,z4,z5,z6]),(0,[z27,z8,z2,z4,z5,z6,z48]),(0,[z8,z553,z2,z4,z5,z113,z6]),(0,[z8,z1,z2,z554,z4,z5,z6]),(0,[z555,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z83,z2,z145,z5,z6])],[(0,[z8,z1,z556,z2,z4,z5,z6]),(0,[z8,z1,z2,z454,z4,z5,z6]),(0,[z31,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z557]),(0,[z8,z1,z2,z4,z5,z6,z558]),(0,[z8,z1,z83,z2,z4,z5,z6]),(0,[z559,z8,z1,z2,z4,z5,z6]),(0,[z560,z8,z1,z2,z4,z6,z37])]],
   [[(0,[z86,z1,z2,z4,z5,z6,z52]),(0,[z8,z1,z2,z34,z145,z5,z6]),(1,[z36,z1,z2,z4,z11,z6]),(0,[z561,z8,z1,z2,z4,z5,z6]),(0,[z47,z8,z88,z1,z2,z4,z6]),(0,[z8,z2,z421,z4,z5,z6,z48]),(0,[z8,z562,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z119,z6]),(0,[z50,z8,z1,z2,z4,z6,z37])],[(0,[z8,z563,z1,z2,z4,z5,z6]),(0,[z8,z553,z1,z2,z4,z5,z6]),(0,[z81,z8,z2,z4,z40,z5,z6]),(1,[z8,z54,z2,z126,z5,z6]),(1,[z138,z1,z2,z4,z5,z6]),(1,[z8,z1,z550,z4,z5,z6])],[(0,[z8,z22,z2,z4,z105,z5,z6]),(0,[z564,z8,z1,z2,z4,z5,z6]),(0,[z356,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z6,z62]),(1,[z8,z10,z1,z2,z4,z37])],[(0,[z8,z1,z2,z4,z30,z6,z37]),(0,[z78,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z4,z5,z60,z6,z144])],[(0,[z8,z22,z2,z4,z5,z6,z52]),(0,[z8,z1,z565,z2,z4,z5,z6]),(1,[z8,z26,z2,z4,z5,z6])],[(0,[z566,z8,z1,z2,z4,z5,z6]),(0,[z174,z8,z1,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z567,z5,z6]),(0,[z152,z8,z1,z2,z413,z5,z6])],[(0,[z568,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z569,z4,z5,z6]),(0,[z8,z570,z1,z2,z4,z5,z6]),(0,[z39,z8,z38,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z571,z6]),(0,[z494,z8,z1,z2,z4,z6,z37])],[(1,[z92,z28,z2,z4,z5,z6]),(0,[z27,z1,z125,z2,z4,z5,z6]),(0,[z8,z10,z2,z4,z5,z6,z48]),(0,[z8,z2,z4,z5,z6,z48,z167]),(0,[z8,z124,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z572,z6])]],
   [[(0,[z8,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z573,z6]),(0,[z8,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z5,z6]),(0,[z8,z197,z1,z38,z4,z5,z6]),(0,[z8,z38,z2,z4,z5,z6,z48]),(1,[z8,z22,z2,z4,z5,z48]),(1,[z8,z2,z4,z382,z5,z6])],[(0,[z574,z8,z2,z4,z5,z6,z48]),(0,[z8,z10,z1,z49,z2,z4,z6]),(0,[z8,z1,z2,z575,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z576,z6]),(0,[z8,z1,z2,z4,z5,z577,z6]),(0,[z8,z2,z4,z5,z113,z6,z260]),(0,[z538,z8,z1,z2,z4,z5,z6]),(0,[z8,z22,z1,z2,z4,z5,z48]),(0,[z8,z1,z2,z578,z4,z5,z6]),(1,[z152,z8,z1,z4,z5,z144]),(0,[z8,z101,z1,z2,z4,z5,z6]),(0,[z356,z8,z2,z4,z5,z6,z62]),(0,[z8,z1,z2,z145,z4,z6,z37])],[(0,[z91,z76,z1,z2,z4,z5,z6]),(0,[z8,z1,z579,z2,z4,z5,z6]),(0,[z8,z1,z580,z2,z4,z5,z6]),(0,[z581,z8,z1,z2,z4,z105,z6]),(1,[z8,z2,z4,z6,z37,z48]),(0,[z50,z8,z2,z4,z5,z6,z48])],[(0,[z8,z582,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z467,z6])],[(0,[z8,z10,z1,z28,z2,z4,z6]),(0,[z91,z8,z1,z2,z4,z310,z6]),(0,[z8,z1,z2,z4,z5,z6,z6]),(0,[z183,z8,z22,z2,z4,z5,z6])],[(0,[z8,z1,z2,z583,z4,z5,z6]),(1,[z8,z553,z2,z4,z5,z6]),(0,[z584,z8,z1,z2,z4,z5,z6]),(0,[z585,z8,z1,z2,z4,z5,z6]),(0,[z270,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z85,z6]),(0,[z8,z1,z586,z2,z4,z5,z6])],[(0,[z174,z8,z10,z1,z2,z4,z6]),(0,[z8,z1,z2,z587,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z89,z6]),(0,[z8,z1,z2,z215,z4,z5,z6]),(0,[z588,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z86,z1,z2,z4,z5,z6]),(0,[z27,z8,z1,z2,z4,z5,z6]),(0,[z152,z8,z22,z2,z4,z5,z6])],[(0,[z8,z495,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z589,z6]),(0,[z8,z1,z2,z4,z5,z6,z590])],[(1,[z32,z1,z2,z4,z5,z6]),(0,[z31,z255,z1,z2,z4,z5,z6]),(0,[z31,z8,z1,z2,z4,z6,z37]),(0,[z8,z22,z2,z4,z177,z5,z6]),(1,[z8,z2,z4,z5,z6,z24])],[(0,[z8,z1,z2,z4,z5,z591,z6]),(0,[z8,z22,z2,z4,z5,z6,z62])],[(0,[z592,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z59,z3,z4,z5,z6]),(0,[z78,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z48,z48]),(0,[z8,z593,z1,z2,z4,z5,z6])],[(0,[z77,z8,z22,z2,z4,z5,z6]),(0,[z8,z54,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z594,z5,z6]),(0,[z8,z1,z2,z4,z5,z595,z6]),(0,[z8,z10,z1,z2,z4,z6,z25]),(0,[z8,z596,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z90]),(0,[z8,z1,z56,z2,z4,z5,z6])],[(0,[z506,z8,z1,z2,z4,z5,z6]),(0,[z597,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z82,z4,z6,z37]),(0,[z39,z8,z2,z4,z5,z46,z6]),(0,[z12,z363,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z37,z13])],[(1,[z513,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z5,z6]),(0,[z8,z508,z10,z1,z2,z4,z6])],[(0,[z598,z8,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z40,z5,z6]),(1,[z8,z1,z2,z4,z6,z243]),(0,[z8,z10,z1,z2,z136,z4,z6])],[(0,[z574,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z599,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z600]),(0,[z8,z1,z2,z4,z5,z113,z6]),(0,[z353,z8,z1,z2,z4,z5,z6]),(0,[z8,z83,z2,z4,z5,z6,z48])],[(0,[z8,z1,z2,z601,z4,z5,z6]),(0,[z8,z1,z602,z2,z4,z5,z6]),(0,[z8,z1,z2,z603,z4,z5,z6]),(0,[z8,z1,z106,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z362,z5,z6]),(0,[z8,z1,z604,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z605,z5,z6]),(1,[z8,z1,z2,z4,z6,z37]),(0,[z560,z8,z1,z2,z4,z5,z6])],[(0,[z50,z8,z1,z2,z4,z5,z6]),(0,[z606,z8,z1,z2,z4,z5,z6]),(0,[z31,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z89,z6,z37]),(0,[z8,z1,z607,z2,z4,z5,z6]),(0,[z8,z1,z2,z145,z4,z5,z85])],[(0,[z1,z125,z2,z4,z79,z5,z6]),(0,[z27,z78,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z608]),(0,[z8,z1,z609,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z37,z536]),(0,[z8,z1,z2,z610,z4,z5,z6])],[(0,[z8,z22,z2,z4,z5,z85,z6]),(0,[z8,z611,z1,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z612,z6]),(0,[z8,z1,z2,z4,z30,z5,z6]),(1,[z8,z1,z2,z522,z5,z6]),(1,[z8,z1,z2,z4,z6,z359]),(0,[z183,z8,z1,z2,z4,z6,z37]),(0,[z613,z8,z1,z2,z4,z5,z6]),(0,[z8,z96,z1,z2,z4,z5,z6])],[(0,[z8,z614,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z30,z6]),(1,[z8,z1,z2,z116,z5,z6]),(0,[z8,z1,z2,z615,z4,z5,z6]),(0,[z8,z1,z49,z4,z119,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z616])],[(0,[z8,z1,z2,z617,z4,z5,z6]),(1,[z150,z1,z2,z79,z5,z6]),(0,[z1,z2,z4,z5,z11,z113,z6]),(0,[z81,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z6,z618]),(0,[z8,z2,z4,z5,z6,z619,z48]),(0,[z152,z8,z1,z2,z4,z6,z37]),(0,[z620,z8,z1,z2,z4,z5,z6]),(0,[z8,z194,z1,z2,z4,z85,z6])],[(0,[z621,z8,z1,z2,z4,z5,z6]),(0,[z622,z8,z1,z2,z4,z5,z6]),(0,[z204,z8,z1,z2,z4,z5,z6]),(0,[z8,z32,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z619]),(0,[z121,z8,z1,z83,z2,z5,z6]),(0,[z8,z1,z2,z4,z623,z5,z6]),(0,[z8,z10,z1,z2,z4,z60,z6]),(0,[z8,z10,z453,z1,z2,z4,z6])],[(0,[z8,z1,z125,z2,z4,z6,z37]),(1,[z8,z1,z2,z468,z4,z6]),(0,[z8,z1,z2,z468,z82,z4,z6]),(0,[z61,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z83,z106,z2,z5,z6]),(0,[z8,z1,z83,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z5,z6,z624])],[(0,[z61,z8,z1,z2,z4,z177,z6]),(0,[z12,z8,z405,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z519]),(0,[z625,z8,z1,z2,z4,z5,z6]),(0,[z626,z8,z1,z2,z4,z5,z6]),(1,[z8,z507,z2,z4,z5,z6]),(1,[z8,z10,z2,z4,z6,z48]),(0,[z8,z22,z2,z4,z5,z6,z25]),(0,[z8,z1,z2,z145,z4,z5,z6])]],
   [[(0,[z627,z8,z1,z2,z4,z5,z6]),(0,[z8,z437,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z628]),(0,[z78,z1,z2,z4,z5,z113,z6]),(0,[z8,z54,z1,z2,z4,z5,z6]),(0,[z581,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z629,z4,z5,z6]),(0,[z8,z22,z2,z4,z111,z5,z6]),(0,[z8,z630,z1,z2,z4,z5,z6]),(0,[z631,z8,z1,z2,z4,z6,z37])],[(0,[z77,z8,z1,z2,z4,z6,z37]),(0,[z8,z38,z2,z4,z40,z5,z6]),(0,[z8,z10,z54,z1,z2,z4,z6]),(0,[z8,z2,z4,z5,z6,z48,z144]),(0,[z541,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z632,z5,z6]),(0,[z8,z2,z4,z5,z46,z6,z48]),(0,[z8,z1,z633,z2,z4,z5,z6])],[(0,[z634,z8,z1,z2,z4,z5,z6]),(0,[z174,z1,z2,z4,z79,z5,z6]),(1,[z8,z290,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z127,z6]),(0,[z183,z8,z2,z4,z5,z6,z48]),(0,[z8,z96,z1,z2,z4,z60,z6]),(0,[z8,z10,z1,z2,z4,z111,z6])],[(0,[z635,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z636,z4,z5,z6]),(0,[z8,z141,z2,z4,z5,z60,z6]),(0,[z12,z8,z1,z550,z4,z5,z6])],[(0,[z8,z1,z2,z34,z5,z6,z13]),(0,[z8,z1,z2,z4,z637,z5,z6]),(0,[z8,z1,z2,z440,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z638,z6]),(0,[z639,z8,z1,z2,z4,z5,z6]),(0,[z152,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z106,z4,z65,z5,z6]),(0,[z8,z1,z640,z2,z4,z5,z6]),(0,[z641,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z642,z5,z6]),(0,[z8,z1,z2,z4,z5,z643,z6]),(0,[z31,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z285,z37])]],
   [[(0,[z77,z1,z2,z4,z5,z11,z6]),(0,[z8,z1,z2,z4,z5,z644,z6]),(0,[z8,z1,z2,z4,z382,z5,z6]),(1,[z313,z1,z2,z4,z5,z6]),(0,[z8,z1,z645,z2,z4,z5,z6]),(0,[z646,z8,z1,z2,z4,z5,z6]),(1,[z8,z2,z4,z5,z6,z107]),(0,[z8,z98,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z647]),(0,[z8,z1,z648,z2,z4,z5,z6]),(0,[z649,z8,z1,z2,z4,z5,z6]),(0,[z650,z8,z1,z2,z4,z5,z6]),(0,[z651,z8,z1,z2,z4,z5,z6]),(0,[z39,z8,z2,z126,z4,z5,z6]),(0,[z8,z22,z99,z2,z4,z5,z6]),(0,[z8,z2,z4,z111,z5,z158,z6]),(1,[z8,z320,z2,z4,z5,z6])],[(0,[z8,z1,z652,z2,z4,z5,z6]),(0,[z653,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z654,z2,z4,z5,z6]),(0,[z143,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z312,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z655]),(0,[z152,z8,z1,z2,z4,z5,z60])],[(0,[z8,z656,z1,z2,z4,z5,z6]),(0,[z174,z86,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z657,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z658]),(0,[z8,z1,z2,z4,z65,z6,z37])],[(0,[z77,z8,z2,z4,z5,z6,z48]),(1,[z8,z326,z2,z4,z5,z6]),(0,[z8,z1,z659,z2,z4,z5,z6]),(0,[z12,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z660,z5,z6]),(0,[z8,z1,z2,z4,z661,z5,z6])],[(0,[z662,z8,z1,z2,z4,z5,z6]),(1,[z581,z8,z1,z2,z4,z6]),(0,[z8,z1,z663,z2,z4,z5,z6]),(0,[z8,z1,z2,z664,z4,z5,z6]),(0,[z8,z22,z2,z4,z5,z60,z6]),(0,[z665,z8,z1,z2,z4,z5,z6]),(0,[z588,z8,z1,z2,z4,z6,z37])],[(0,[z8,z1,z2,z4,z5,z6,z666]),(0,[z77,z8,z1,z125,z4,z5,z6]),(0,[z8,z1,z2,z4,z119,z5,z6])],[(0,[z667,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z79,z6,z37]),(0,[z668,z8,z1,z2,z4,z5,z6]),(0,[z8,z124,z1,z2,z4,z5,z6])]],
   [[(0,[z669,z8,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z670,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z671,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z251,z6]),(0,[z19,z8,z1,z2,z4,z5,z6])],[(0,[z36,z8,z22,z2,z4,z5,z6]),(1,[z613,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z672]),(1,[z19,z10,z1,z2,z4,z6])],[(0,[z91,z8,z22,z2,z4,z5,z6]),(0,[z8,z88,z1,z2,z4,z30,z6]),(0,[z8,z1,z2,z673,z4,z5,z6]),(1,[z42,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z24]),(0,[z8,z1,z2,z4,z5,z6,z674]),(1,[z8,z343,z2,z4,z5,z6]),(0,[z675,z8,z1,z2,z4,z5,z6])],[(0,[z676,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z677,z6]),(0,[z78,z8,z1,z2,z4,z6,z37]),(1,[z101,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z678,z5,z6]),(0,[z679,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z680,z5,z6]),(0,[z1,z2,z4,z30,z5,z11,z6]),(0,[z81,z8,z1,z38,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z681]),(0,[z8,z110,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z682])],[(0,[z77,z1,z125,z2,z4,z5,z6]),(0,[z183,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z339,z2,z4,z5,z6]),(0,[z61,z8,z1,z2,z136,z5,z6])],[(0,[z8,z1,z683,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z684,z5,z6]),(0,[z8,z1,z2,z2,z4,z5,z6]),(0,[z8,z22,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z685,z4,z5,z6]),(0,[z8,z1,z686,z2,z4,z5,z6]),(1,[z44,z1,z2,z4,z5,z6]),(0,[z687,z8,z1,z2,z4,z5,z6]),(0,[z31,z8,z2,z4,z40,z5,z6]),(0,[z61,z8,z1,z2,z4,z6,z62]),(1,[z8,z2,z4,z5,z158,z6])],[(0,[z8,z1,z2,z4,z5,z6,z688]),(0,[z689,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z105,z6]),(0,[z121,z8,z22,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z6,z37])]],
   [[(0,[z27,z8,z10,z1,z2,z4,z6]),(0,[z152,z613,z1,z2,z4,z5,z6]),(0,[z152,z8,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z59,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z6,z690]),(0,[z8,z1,z2,z4,z5,z6,z167]),(0,[z691,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z692,z2,z4,z5,z6])],[(0,[z8,z1,z125,z2,z4,z5,z6]),(0,[z27,z174,z1,z2,z4,z5,z6]),(0,[z693,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z694,z5,z6]),(0,[z8,z197,z38,z2,z4,z5,z6]),(0,[z8,z1,z695,z2,z4,z5,z6]),(0,[z8,z10,z1,z38,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z696,z6]),(0,[z8,z1,z106,z2,z4,z6,z37])],[(0,[z61,z8,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z85,z6,z55])],[(0,[z8,z697,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z34,z4,z5,z6]),(0,[z698,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z126,z4,z5,z6,z48]),(0,[z8,z22,z2,z4,z316,z5,z6]),(0,[z8,z22,z2,z136,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z220,z6]),(0,[z592,z8,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z699,z5,z6]),(0,[z8,z700,z1,z2,z4,z5,z6]),(0,[z631,z8,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z177,z5,z6,z48]),(0,[z8,z1,z2,z701,z4,z5,z6]),(0,[z61,z8,z1,z49,z2,z4,z6]),(0,[z122,z1,z2,z4,z5,z6,z144]),(0,[z513,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z37,z608])],[(0,[z77,z8,z1,z2,z4,z5,z6]),(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z702,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z703,z5,z6]),(0,[z8,z1,z2,z4,z5,z704,z6]),(0,[z8,z596,z10,z1,z2,z4,z6])],[(0,[z8,z1,z705,z2,z4,z5,z6]),(0,[z150,z8,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z706,z5,z6]),(0,[z8,z10,z1,z2,z4,z6,z13]),(0,[z8,z10,z1,z99,z2,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z44,z1,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z707,z6]),(0,[z708,z1,z2,z4,z5,z6]),(0,[z32,z2,z4,z40,z5,z6])],[(0,[z8,z1,z2,z4,z709,z6]),(0,[z39,z97,z1,z2,z4,z6]),(0,[z710,z1,z2,z4,z5,z6])],[(0,[z78,z1,z2,z4,z5,z644])],[(0,[z426,z1,z2,z79,z5,z6]),(0,[z8,z69,z4,z5,z6,z48]),(0,[z8,z4,z5,z6,z48,z711]),(0,[z712,z1,z2,z4,z5,z6]),(0,[z713,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z714,z6]),(0,[z8,z1,z2,z468,z4,z6]),(0,[z47,z8,z1,z629,z4,z6]),(0,[z559,z8,z1,z4,z5,z144]),(0,[z715,z1,z2,z4,z5,z6]),(0,[z8,z1,z59,z4,z60,z37]),(0,[z8,z1,z716,z4,z5,z6])],[(0,[z27,z8,z2,z4,z37,z48]),(0,[z717,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z718]),(0,[z8,z2,z4,z5,z58,z48])],[(0,[z8,z507,z2,z4,z5,z6]),(0,[z8,z2,z4,z40,z6,z335]),(0,[z42,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z719,z5,z6]),(0,[z8,z2,z4,z220,z6,z48]),(0,[z8,z2,z4,z5,z6,z720]),(0,[z101,z10,z1,z2,z4,z6]),(0,[z721,z8,z2,z4,z5,z6])],[(0,[z8,z722,z2,z4,z5,z6]),(0,[z8,z88,z2,z4,z316,z6]),(0,[z723,z1,z2,z4,z5,z6]),(0,[z724,z1,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z725,z6]),(0,[z1,z2,z4,z5,z6,z726])],[(0,[z8,z290,z1,z2,z4,z6]),(0,[z44,z10,z1,z2,z4,z6]),(0,[z8,z22,z2,z4,z5,z199]),(0,[z39,z8,z365,z2,z4,z6]),(0,[z8,z10,z22,z2,z4,z89]),(0,[z152,z95,z1,z4,z5,z144])],[(0,[z78,z1,z2,z4,z5,z409]),(0,[z8,z22,z2,z4,z5,z203]),(0,[z8,z2,z4,z727,z6,z48]),(0,[z8,z728,z2,z4,z5,z6]),(0,[z272,z1,z2,z4,z18,z6])],[(0,[z8,z1,z2,z4,z293,z37]),(0,[z8,z2,z4,z5,z6,z729])],[(0,[z91,z10,z76,z2,z4,z6]),(0,[z78,z1,z2,z522,z5,z6]),(0,[z8,z22,z2,z4,z127,z6])],[(0,[z27,z1,z2,z4,z33,z6]),(0,[z12,z8,z2,z5,z48,z13])],[(0,[z8,z1,z2,z730,z4,z6]),(0,[z8,z22,z2,z4,z135,z6]),(0,[z8,z10,z2,z4,z6,z107])]],
   [[(0,[z8,z731,z1,z2,z4,z6]),(0,[z8,z320,z2,z4,z5,z6]),(0,[z61,z8,z1,z2,z6,z732]),(0,[z8,z10,z1,z123,z2,z4])],[(0,[z8,z1,z2,z4,z6,z733])],[(0,[z8,z10,z507,z2,z4,z6]),(0,[z190,z8,z2,z4,z5,z48]),(0,[z8,z1,z2,z4,z734,z6]),(0,[z8,z1,z56,z4,z119,z6])],[(0,[z8,z326,z2,z4,z5,z6]),(0,[z86,z1,z2,z236,z5,z6]),(0,[z8,z1,z2,z4,z735,z6]),(0,[z8,z10,z343,z2,z4,z6])],[],[(0,[z8,z1,z2,z4,z736,z6]),(0,[z77,z326,z2,z4,z5,z6]),(0,[z8,z2,z4,z737,z6,z48])],[(0,[z1,z2,z4,z33,z113,z6]),(0,[z8,z1,z2,z4,z738,z6]),(0,[z8,z110,z2,z4,z111,z37])],[(0,[z8,z1,z2,z4,z6,z739]),(0,[z8,z1,z2,z4,z740,z6]),(0,[z8,z2,z116,z5,z6,z48]),(0,[z39,z8,z2,z4,z274,z6]),(0,[z8,z10,z98,z2,z4,z6])],[(0,[z91,z437,z2,z4,z5,z6]),(0,[z27,z22,z2,z4,z5,z52]),(0,[z741,z1,z2,z4,z5,z6])],[(0,[z742,z2,z4,z5,z6,z48]),(0,[z8,z743,z2,z4,z5,z6]),(0,[z8,z1,z4,z6,z37,z744])],[(0,[z91,z76,z2,z4,z5,z6]),(0,[z745,z8,z1,z2,z4,z6]),(0,[z39,z8,z305,z2,z4,z6])],[(0,[z0,z1,z2,z4,z393,z6]),(0,[z78,z1,z2,z4,z113,z359]),(0,[z39,z8,z2,z4,z287,z6]),(0,[z8,z2,z4,z5,z746,z6])],[(0,[z8,z1,z2,z4,z386,z37]),(0,[z8,z1,z2,z4,z192,z37])],[(0,[z8,z2,z4,z5,z6,z747]),(0,[z570,z1,z2,z4,z5,z113]),(0,[z748,z1,z2,z4,z5,z6]),(0,[z8,z1,z749,z4,z5,z6]),(0,[z750,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z751]),(0,[z8,z10,z2,z4,z158,z6])],[(0,[z8,z752,z2,z4,z5,z6]),(0,[z2,z4,z5,z6,z48,z227]),(0,[z22,z15,z2,z4,z5,z89]),(0,[z753,z1,z2,z4,z5,z6])],[(0,[z27,z1,z2,z4,z5,z647]),(0,[z8,z2,z4,z5,z171,z48]),(0,[z8,z22,z2,z4,z37,z48]),(0,[z8,z754,z2,z4,z5,z6]),(0,[z12,z363,z1,z2,z5,z13])]],
   [[],[(0,[z8,z49,z4,z119,z6,z48])],[(0,[z8,z22,z59,z4,z5,z60]),(0,[z8,z1,z2,z4,z755,z6])],[(0,[z95,z1,z2,z4,z5,z6]),(0,[z756,z8,z22,z2,z4,z6])],[(0,[z8,z2,z4,z5,z6,z757]),(0,[z1,z2,z4,z758,z5,z6]),(0,[z8,z759,z2,z4,z5,z6]),(0,[z8,z194,z26,z2,z4,z6])],[(0,[z379,z22,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z760]),(0,[z761,z8,z2,z4,z5,z6])],[(0,[z8,z1,z2,z762,z5,z6]),(0,[z1,z2,z4,z5,z6,z763]),(0,[z272,z1,z2,z4,z5,z6]),(0,[z39,z8,z2,z4,z314,z6]),(0,[z270,z22,z2,z4,z5,z6]),(0,[z764,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z765,z6]),(0,[z766,z8,z1,z2,z4,z6])],[(0,[z8,z1,z767,z4,z5,z6]),(0,[z270,z117,z2,z4,z5,z6]),(0,[z513,z10,z1,z2,z4,z6]),(0,[z10,z97,z1,z2,z4,z6])],[(0,[z1,z2,z768,z4,z5,z6]),(0,[z769,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z770]),(0,[z8,z2,z4,z5,z48,z14]),(0,[z8,z1,z365,z2,z4,z37]),(0,[z10,z97,z2,z4,z6,z48]),(0,[z771,z1,z2,z4,z5,z6]),(0,[z67,z1,z2,z4,z6,z37]),(0,[z122,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z104,z6]),(0,[z8,z1,z2,z4,z242,z37]),(0,[z8,z10,z1,z2,z4,z655])],[(0,[z363,z1,z2,z4,z18,z6])],[(0,[z8,z1,z2,z772,z5,z6]),(0,[z773,z8,z1,z2,z4,z6]),(0,[z22,z774,z2,z4,z5,z6])],[(0,[z8,z22,z2,z4,z362,z6]),(0,[z775,z8,z1,z2,z4,z6]),(0,[z8,z10,z1,z99,z2,z4]),(0,[z8,z1,z99,z776,z2,z4])],[],[(0,[z8,z1,z2,z4,z777,z6]),(0,[z8,z2,z522,z5,z6,z48]),(0,[z8,z1,z2,z4,z778,z6]),(0,[z779,z8,z2,z4,z5,z6])]],
   [[(0,[z8,z780,z2,z4,z5,z6]),(1,[z8,z1,z2,z5,z781])],[(0,[z183,z8,z2,z4,z5,z48])],[(0,[z8,z2,z4,z104,z6,z48]),(0,[z363,z1,z69,z4,z5,z6])],[(1,[z782,z2,z4,z5,z6]),(0,[z8,z88,z2,z4,z257,z6])],[(0,[z8,z2,z4,z5,z6,z783]),(0,[z8,z784,z2,z4,z5,z6]),(0,[z8,z785,z1,z2,z4,z6]),(0,[z42,z88,z1,z2,z4,z6]),(0,[z15,z2,z4,z40,z5,z6]),(0,[z8,z22,z2,z4,z5,z89]),(0,[z8,z2,z4,z5,z6,z786])],[(0,[z8,z507,z2,z4,z11,z6]),(0,[z8,z10,z326,z2,z4,z6]),(0,[z8,z1,z2,z787,z5,z6]),(0,[z101,z88,z1,z2,z4,z6]),(0,[z8,z788,z1,z2,z4,z6])],[],[(0,[z8,z789,z1,z2,z4,z6])],[],[(0,[z8,z2,z4,z5,z6,z790])],[(0,[z1,z28,z2,z522,z5,z6]),(0,[z150,z1,z2,z281,z5,z6]),(0,[z8,z1,z2,z4,z791,z6]),(0,[z792,z1,z2,z4,z5,z6]),(0,[z8,z1,z106,z65,z5,z6])],[(0,[z8,z2,z4,z5,z6,z793])],[(0,[z86,z1,z2,z4,z33,z6]),(0,[z8,z1,z794,z4,z5,z6]),(0,[z8,z1,z2,z332,z5,z6]),(0,[z8,z795,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z58]),(0,[z8,z2,z4,z5,z6,z796]),(0,[z613,z1,z2,z332,z5,z6]),(0,[z797,z8,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z6,z798]),(0,[z10,z710,z1,z2,z4,z6])],[(0,[z8,z22,z2,z4,z5,z509]),(0,[z8,z799,z2,z4,z5,z6]),(0,[z8,z1,z800,z4,z5,z6])],[(0,[z91,z782,z2,z4,z5,z6]),(0,[z270,z10,z22,z2,z4,z6]),(0,[z1,z237,z2,z4,z6,z37])]],
   [[(0,[z8,z1,z2,z4,z801,z6]),(0,[z91,z76,z2,z4,z6,z37]),(0,[z8,z802,z1,z2,z4,z6]),(0,[z8,z1,z803,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z804]),(0,[z8,z1,z2,z4,z805,z6])],[(0,[z8,z22,z2,z4,z131,z6]),(0,[z8,z806,z1,z2,z4,z6]),(0,[z807,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z808,z6]),(0,[z1,z2,z809,z79,z5,z6]),(0,[z8,z278,z2,z4,z5,z48]),(0,[z810,z2,z4,z5,z6,z48]),(0,[z8,z124,z2,z4,z316,z6]),(0,[z8,z325,z2,z413,z5,z6]),(0,[z152,z8,z325,z4,z5,z144])],[(0,[z27,z437,z2,z4,z5,z52]),(0,[z379,z2,z4,z5,z6,z48]),(0,[z8,z2,z413,z5,z6,z48])],[(0,[z91,z435,z2,z4,z5,z6]),(0,[z513,z1,z2,z79,z5,z6]),(0,[z8,z811,z2,z4,z5,z6]),(0,[z270,z2,z4,z5,z6,z48])],[(0,[z8,z1,z2,z4,z6,z812]),(0,[z78,z553,z2,z4,z5,z113]),(0,[z813,z1,z2,z4,z5,z6]),(0,[z814,z1,z2,z4,z5,z6])],[(0,[z67,z1,z2,z4,z5,z6])],[(0,[z91,z1,z2,z522,z5,z6]),(0,[z8,z815,z2,z4,z5,z6]),(0,[z581,z8,z22,z2,z4,z6]),(0,[z8,z1,z49,z4,z6,z163]),(0,[z8,z10,z1,z404,z2,z4])],[(0,[z95,z1,z4,z5,z6,z144]),(0,[z12,z1,z2,z5,z227,z13])],[(0,[z8,z2,z4,z5,z6,z816]),(0,[z95,z1,z2,z4,z6,z37])],[(0,[z8,z22,z2,z4,z5,z547]),(0,[z8,z1,z2,z4,z817,z6]),(0,[z460,z1,z2,z34,z5,z6]),(0,[z8,z1,z818,z4,z5,z6]),(0,[z8,z2,z145,z5,z85,z48]),(0,[z8,z819,z2,z4,z5,z6]),(0,[z95,z137,z2,z4,z5,z6]),(0,[z8,z1,z2,z820,z4,z6]),(0,[z97,z453,z1,z2,z4,z6])],[(0,[z8,z2,z4,z5,z6,z821]),(0,[z8,z1,z2,z4,z600,z37]),(0,[z19,z10,z22,z2,z4,z6])],[(0,[z8,z22,z2,z4,z5,z396]),(0,[z270,z22,z2,z4,z6,z37]),(0,[z822,z1,z2,z4,z5,z6]),(0,[z47,z8,z1,z4,z6,z25]),(0,[z272,z1,z2,z4,z6,z37])],[(0,[z8,z1,z2,z823,z5,z6]),(0,[z8,z824,z2,z4,z5,z6]),(0,[z8,z2,z4,z6,z37,z825])],[(0,[z8,z1,z2,z4,z826,z6])],[(0,[z19,z1,z2,z4,z393,z6]),(0,[z8,z22,z2,z4,z393,z6]),(0,[z8,z827,z1,z2,z4,z6]),(0,[z8,z2,z4,z348,z46,z6])]],
   [[(0,[z1,z2,z4,z809,z5,z6]),(0,[z828,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z341,z37]),(0,[z8,z22,z2,z4,z111,z37])],[(0,[z1,z2,z829,z4,z5,z6]),(0,[z8,z1,z2,z4,z830,z6]),(0,[z270,z437,z2,z4,z5,z6]),(0,[z8,z1,z831,z4,z5,z6]),(0,[z8,z194,z22,z2,z4,z6])],[(0,[z72,z1,z2,z79,z5,z6]),(0,[z8,z1,z2,z4,z6,z832]),(0,[z8,z2,z4,z5,z6,z833])],[(0,[z270,z76,z2,z4,z5,z6]),(0,[z86,z2,z34,z5,z6,z48]),(0,[z1,z2,z4,z758,z11,z6]),(0,[z288,z8,z2,z4,z362,z6]),(0,[z1,z834,z2,z4,z5,z6]),(0,[z95,z10,z1,z2,z4,z6])],[(0,[z835,z2,z4,z5,z6,z48]),(0,[z8,z2,z4,z5,z89,z833])],[(0,[z76,z782,z2,z4,z5,z6]),(0,[z8,z570,z1,z2,z4,z37]),(0,[z8,z154,z2,z522,z5,z6]),(0,[z8,z836,z1,z2,z4,z6]),(0,[z466,z39,z8,z2,z4,z6])],[(0,[z8,z1,z2,z4,z220,z6]),(0,[z613,z1,z2,z4,z220,z6]),(0,[z272,z10,z1,z2,z4,z6])],[(0,[z8,z2,z4,z5,z6,z837])],[(0,[z8,z1,z2,z4,z838,z6]),(0,[z1,z2,z4,z5,z6,z227]),(0,[z0,z1,z2,z522,z5,z6]),(0,[z8,z1,z2,z4,z839,z6]),(0,[z559,z8,z1,z2,z5,z13])],[(0,[z8,z2,z4,z5,z48,z225]),(0,[z1,z840,z2,z4,z5,z6])],[(0,[z8,z28,z2,z4,z310,z6]),(0,[z8,z22,z49,z4,z119,z6]),(0,[z8,z2,z4,z5,z841,z6])],[(0,[z8,z2,z4,z127,z6,z48]),(0,[z1,z2,z4,z5,z6,z842]),(0,[z19,z843,z2,z4,z5,z6])],[(0,[z1,z237,z2,z4,z5,z6]),(0,[z1,z125,z4,z5,z6,z273]),(0,[z8,z844,z2,z4,z5,z6]),(0,[z8,z2,z126,z5,z6,z415])],[(0,[z8,z1,z2,z4,z845,z6])],[(0,[z66,z8,z2,z4,z382,z6]),(0,[z846,z8,z2,z4,z6,z37])],[(0,[z847,z8,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z424]),(0,[z8,z1,z2,z4,z394,z37]),(0,[z8,z1,z49,z434,z4,z6]),(0,[z152,z8,z22,z4,z5,z144]),(0,[z8,z405,z550,z4,z5,z6]),(0,[z494,z1,z2,z4,z6,z536])]],
   [[(0,[z8,z1,z106,z65,z6,z37]),(0,[z8,z325,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z6,z55]),(0,[z272,z1,z2,z4,z205,z6]),(0,[z12,z8,z343,z2,z5,z13])],[(0,[z8,z1,z322,z4,z6,z37]),(0,[z22,z848,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z849,z6]),(0,[z8,z850,z2,z4,z5,z6]),(0,[z10,z851,z1,z2,z4,z6])],[(0,[z8,z1,z4,z6,z852,z25]),(0,[z8,z1,z2,z332,z6,z37])],[(0,[z0,z290,z1,z2,z4,z6]),(0,[z8,z853,z2,z4,z5,z6]),(0,[z8,z137,z2,z332,z5,z6]),(0,[z8,z1,z69,z4,z18,z6])],[(0,[z8,z854,z2,z4,z5,z6]),(0,[z8,z855,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z856,z6])],[(0,[z8,z1,z2,z857,z5,z6]),(0,[z95,z1,z2,z4,z251,z6]),(0,[z8,z1,z59,z4,z5,z751])],[(0,[z858,z8,z1,z2,z4,z6]),(0,[z1,z2,z4,z5,z6,z859]),(0,[z8,z1,z322,z116,z5,z6]),(0,[z8,z10,z2,z4,z6,z260]),(0,[z8,z1,z2,z4,z860,z6]),(0,[z8,z1,z2,z4,z6,z861])],[(0,[z39,z8,z2,z4,z479,z6]),(0,[z8,z862,z2,z4,z5,z6])],[(0,[z8,z1,z2,z5,z6,z863]),(0,[z1,z864,z2,z4,z5,z6]),(0,[z61,z138,z1,z2,z6,z62])],[(0,[z81,z8,z629,z4,z5,z6]),(0,[z8,z2,z4,z6,z243,z48]),(0,[z865,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z825]),(0,[z8,z10,z110,z2,z4,z6])],[(0,[z1,z866,z2,z4,z5,z6]),(0,[z574,z2,z4,z5,z6,z619]),(0,[z272,z343,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z6,z867]),(0,[z86,z22,z2,z34,z5,z6]),(0,[z95,z1,z59,z4,z5,z6]),(0,[z8,z1,z2,z145,z5,z781]),(0,[z194,z868,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z869,z6]),(0,[z8,z437,z2,z4,z131,z6]),(0,[z363,z1,z2,z4,z6,z37]),(0,[z8,z10,z1,z550,z4,z6])],[(0,[z8,z22,z550,z4,z5,z6]),(0,[z8,z1,z870,z2,z5,z6]),(0,[z8,z815,z2,z4,z6,z37])],[(0,[z8,z1,z871,z4,z5,z6]),(0,[z121,z8,z83,z5,z6,z48]),(0,[z8,z1,z2,z4,z872,z6]),(0,[z8,z2,z4,z5,z6,z873]),(0,[z8,z1,z874,z4,z5,z6]),(0,[z8,z26,z2,z4,z6,z55])],[(0,[z8,z247,z1,z2,z4,z6]),(0,[z143,z8,z129,z2,z4,z6])]],
   [[(0,[z91,z76,z2,z4,z33,z6]),(0,[z8,z2,z4,z5,z6,z875]),(0,[z0,z97,z1,z2,z4,z6]),(0,[z78,z1,z2,z4,z5,z113]),(0,[z8,z247,z2,z4,z6,z48]),(0,[z876,z1,z2,z4,z5,z6]),(0,[z877,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z878,z6]),(0,[z8,z879,z2,z4,z5,z6]),(0,[z70,z39,z8,z2,z4,z6]),(0,[z880,z8,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z226])],[(0,[z8,z881,z2,z4,z5,z6]),(0,[z27,z1,z2,z522,z5,z52]),(0,[z8,z88,z2,z4,z40,z6]),(1,[z8,z2,z4,z5,z833]),(0,[z8,z2,z4,z5,z882,z6]),(0,[z883,z22,z2,z4,z5,z6]),(0,[z884,z141,z2,z4,z5,z6]),(0,[z8,z10,z2,z4,z6,z115])],[(0,[z8,z417,z2,z4,z5,z48]),(0,[z150,z1,z2,z809,z5,z6]),(0,[z8,z54,z2,z885,z5,z6])],[(0,[z1,z2,z3,z4,z33,z6])],[(0,[z19,z22,z2,z4,z5,z6])],[(0,[z150,z1,z454,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z886]),(0,[z81,z44,z82,z4,z5,z6]),(0,[z67,z10,z1,z2,z4,z6])],[(0,[z8,z887,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z888]),(0,[z8,z10,z1,z2,z332,z6])],[(0,[z8,z1,z2,z4,z310,z6]),(0,[z152,z8,z4,z5,z48,z144])],[(0,[z8,z1,z2,z4,z37,z225])],[(0,[z8,z437,z2,z4,z393,z6]),(0,[z8,z1,z2,z4,z889,z6]),(0,[z8,z141,z59,z4,z5,z60])],[(0,[z8,z2,z4,z5,z6,z890]),(0,[z891,z1,z2,z4,z5,z6]),(0,[z39,z8,z383,z2,z4,z6]),(0,[z892,z8,z2,z4,z5,z6]),(0,[z846,z8,z2,z4,z5,z6]),(0,[z139,z97,z1,z2,z4,z6])],[(0,[z8,z10,z2,z893,z4,z6])],[(0,[z894,z1,z2,z4,z5,z6]),(0,[z8,z325,z2,z4,z5,z6]),(0,[z1,z895,z2,z4,z5,z6]),(0,[z613,z325,z2,z4,z5,z6]),(0,[z8,z137,z2,z4,z220,z6]),(0,[z8,z1,z2,z413,z6,z37])],[(0,[z8,z1,z322,z4,z5,z6]),(0,[z8,z1,z69,z4,z5,z6]),(0,[z8,z1,z2,z332,z251,z6]),(0,[z8,z1,z2,z4,z459,z37])],[(0,[z8,z1,z2,z4,z896,z6]),(0,[z61,z8,z2,z6,z115,z62]),(0,[z1,z2,z4,z6,z37,z227])]],
   [[(0,[z8,z290,z22,z2,z4,z6]),(0,[z8,z1,z2,z4,z897,z6]),(0,[z8,z1,z2,z898,z5,z6])],[(0,[z8,z2,z4,z899,z5,z6]),(0,[z8,z550,z4,z5,z6,z48])],[(0,[z8,z900,z2,z4,z5,z6]),(0,[z97,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z5,z512]),(0,[z66,z8,z1,z2,z4,z6]),(0,[z1,z2,z4,z6,z37,z842])],[(0,[z174,z1,z3,z4,z6,z37]),(0,[z8,z901,z2,z4,z5,z6]),(0,[z204,z8,z1,z2,z4,z6]),(0,[z902,z1,z2,z4,z5,z6]),(0,[z39,z8,z2,z4,z46,z6]),(0,[z66,z8,z2,z4,z6,z48]),(0,[z8,z2,z4,z5,z6,z903])],[(0,[z204,z8,z2,z4,z6,z48]),(0,[z8,z214,z88,z2,z4,z6]),(0,[z8,z2,z4,z904,z5,z6])],[(0,[z8,z88,z2,z4,z324,z6]),(0,[z8,z1,z2,z4,z905,z6]),(0,[z8,z906,z2,z4,z5,z6])],[(0,[z8,z22,z2,z4,z6,z243])],[(0,[z8,z1,z49,z4,z157,z6]),(0,[z8,z907,z1,z2,z4,z6])],[(0,[z8,z2,z908,z4,z5,z6]),(0,[z1,z909,z2,z4,z5,z6])],[(0,[z363,z1,z2,z4,z5,z6]),(0,[z910,z1,z2,z4,z5,z6]),(0,[z911,z1,z2,z4,z5,z6]),(0,[z8,z59,z4,z5,z60,z90])],[(0,[z8,z2,z4,z5,z6,z90]),(0,[z363,z343,z2,z4,z5,z6]),(0,[z12,z8,z1,z2,z37,z13])],[(0,[z8,z1,z2,z4,z5,z912]),(0,[z8,z2,z4,z913,z5,z6]),(0,[z8,z2,z332,z5,z6,z48])],[(0,[z86,z1,z2,z223,z5,z6]),(0,[z543,z1,z2,z4,z11,z6]),(0,[z8,z22,z2,z522,z5,z6]),(0,[z27,z1,z2,z4,z52,z37]),(0,[z8,z22,z2,z4,z6,z359]),(0,[z81,z315,z82,z4,z5,z6]),(0,[z270,z22,z2,z4,z914,z6])],[(0,[z8,z1,z915,z4,z5,z6]),(0,[z8,z916,z2,z4,z5,z6]),(0,[z12,z8,z10,z1,z2,z13])],[(0,[z295,z28,z2,z4,z5,z6]),(0,[z8,z917,z2,z4,z5,z6]),(0,[z47,z8,z4,z6,z24,z25])],[(0,[z8,z918,z82,z4,z5,z6]),(0,[z8,z2,z4,z919,z46,z6])]],
   [[(0,[z174,z1,z829,z4,z5,z6]),(0,[z315,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z920,z6])],[(0,[z121,z8,z1,z83,z5,z6]),(0,[z1,z2,z4,z5,z6,z921]),(0,[z8,z1,z2,z922,z5,z6])],[(0,[z412,z76,z2,z4,z5,z6]),(0,[z122,z1,z3,z4,z5,z6]),(0,[z36,z2,z4,z11,z6,z48]),(0,[z27,z1,z2,z4,z5,z923]),(0,[z924,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z5,z394]),(0,[z8,z106,z382,z65,z5,z6])],[(0,[z41,z28,z2,z4,z5,z6]),(0,[z8,z1,z2,z809,z5,z6]),(0,[z8,z1,z2,z4,z758,z6]),(0,[z1,z2,z522,z5,z6,z52]),(0,[z19,z2,z4,z5,z6,z48]),(0,[z10,z22,z15,z2,z4,z6]),(0,[z560,z8,z1,z4,z6,z25])],[(0,[z8,z1,z925,z4,z5,z6]),(0,[z8,z1,z106,z362,z65,z6])],[(0,[z653,z8,z1,z2,z5,z13]),(0,[z8,z2,z4,z885,z5,z6])],[(0,[z39,z8,z2,z4,z576,z6]),(0,[z29,z1,z2,z4,z5,z52]),(0,[z8,z1,z454,z4,z5,z6]),(0,[z8,z1,z2,z4,z926,z6]),(0,[z61,z8,z2,z6,z48,z62]),(0,[z8,z927,z2,z4,z5,z6])],[],[(0,[z8,z1,z2,z4,z928,z6]),(0,[z929,z1,z2,z4,z5,z6]),(0,[z19,z10,z930,z2,z4,z6])],[(0,[z183,z8,z2,z4,z127,z48]),(0,[z8,z2,z4,z135,z6,z48]),(0,[z8,z2,z4,z348,z6,z167]),(0,[z8,z1,z2,z413,z251,z6]),(1,[z8,z1,z776,z2,z4]),(0,[z8,z2,z893,z4,z5,z6])],[(0,[z8,z931,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z48,z410]),(0,[z8,z22,z2,z145,z5,z85]),(0,[z932,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z413,z5,z6]),(0,[z8,z933,z2,z4,z5,z6]),(0,[z8,z1,z2,z934,z5,z6]),(0,[z613,z1,z2,z413,z5,z6])],[(0,[z8,z1,z2,z522,z131,z6]),(0,[z255,z1,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z935,z6]),(0,[z183,z8,z2,z4,z135,z48]),(0,[z8,z936,z2,z4,z5,z6])],[(0,[z937,z1,z2,z4,z5,z6])],[(0,[z8,z938,z2,z4,z5,z6]),(0,[z12,z272,z1,z2,z5,z13]),(0,[z8,z930,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z939,z6]),(0,[z8,z940,z2,z4,z5,z6]),(0,[z10,z97,z22,z2,z4,z6]),(0,[z8,z10,z1,z2,z4,z37])],[(0,[z290,z97,z1,z2,z4,z6])]],
   [[(0,[z92,z782,z2,z4,z5,z6]),(0,[z174,z1,z3,z4,z5,z6]),(0,[z535,z1,z3,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z941]),(0,[z78,z10,z1,z2,z4,z113]),(0,[z851,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z942,z6]),(0,[z8,z2,z4,z5,z6,z943])],[(0,[z8,z944,z2,z4,z5,z6]),(0,[z945,z1,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z6,z946]),(0,[z8,z10,z1,z2,z4,z358]),(0,[z8,z2,z4,z5,z6,z947]),(0,[z8,z948,z2,z4,z5,z6])],[(0,[z8,z949,z1,z2,z4,z6]),(0,[z8,z214,z188,z2,z4,z6]),(0,[z8,z10,z22,z99,z2,z4])],[(0,[z8,z2,z4,z5,z6,z950]),(0,[z8,z2,z4,z382,z5,z6]),(0,[z8,z2,z4,z521,z5,z48]),(0,[z8,z1,z69,z4,z6,z37])],[],[(0,[z8,z88,z2,z4,z919,z6]),(0,[z8,z1,z2,z4,z5,z833]),(0,[z8,z2,z4,z85,z37,z48]),(0,[z42,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z951,z6]),(0,[z8,z10,z1,z2,z145,z85])],[(0,[z101,z22,z2,z4,z5,z6])],[(0,[z8,z952,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z37,z151]),(0,[z97,z1,z2,z4,z6,z37])],[(0,[z8,z1,z2,z522,z393,z6]),(0,[z953,z1,z2,z4,z5,z6]),(0,[z81,z8,z10,z82,z4,z6])],[(0,[z8,z553,z2,z4,z5,z6]),(0,[z8,z954,z2,z4,z5,z6]),(0,[z77,z1,z125,z4,z6,z37]),(0,[z8,z1,z2,z4,z955,z6]),(0,[z44,z22,z2,z4,z5,z6]),(0,[z956,z1,z2,z4,z5,z6])],[(0,[z27,z1,z2,z4,z5,z418]),(0,[z249,z8,z1,z2,z6,z608])],[(0,[z8,z1,z957,z4,z5,z6]),(0,[z8,z124,z2,z4,z40,z6]),(0,[z8,z1,z870,z65,z5,z6])],[],[(0,[z8,z1,z2,z958,z5,z6]),(0,[z8,z2,z4,z6,z359,z260]),(0,[z315,z2,z4,z5,z6,z48]),(0,[z959,z1,z2,z4,z5,z6]),(0,[z10,z1,z2,z4,z6,z227])],[(0,[z782,z28,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z169,z6]),(0,[z36,z22,z2,z4,z11,z6]),(0,[z36,z97,z1,z2,z4,z6])]],
   [[(0,[z224,z1,z3,z4,z5,z6]),(0,[z8,z10,z54,z2,z126,z6]),(0,[z960,z8,z2,z4,z5,z6])],[(0,[z8,z1,z2,z961,z5,z6]),(0,[z8,z10,z1,z322,z4,z6]),(0,[z8,z2,z4,z6,z37,z90])],[(0,[z8,z1,z2,z962,z5,z6]),(0,[z8,z2,z4,z963,z5,z6]),(0,[z8,z1,z2,z4,z6,z964]),(0,[z8,z1,z2,z4,z6,z965])],[(0,[z8,z1,z915,z4,z6,z37])],[(0,[z8,z2,z4,z393,z6,z48]),(0,[z588,z8,z2,z4,z46,z6])],[(0,[z483,z1,z2,z79,z5,z6]),(0,[z8,z1,z2,z4,z966,z6]),(0,[z270,z22,z2,z4,z5,z89]),(0,[z8,z967,z2,z4,z5,z6])],[(0,[z8,z968,z2,z4,z6,z37])],[(0,[z8,z969,z2,z4,z5,z6]),(0,[z8,z437,z2,z522,z5,z6]),(0,[z970,z1,z2,z4,z5,z6]),(0,[z39,z42,z1,z2,z4,z6]),(0,[z121,z8,z1,z83,z6,z37]),(0,[z971,z1,z2,z4,z5,z6]),(0,[z12,z513,z1,z2,z5,z13])],[(0,[z8,z1,z2,z4,z6,z37]),(0,[z255,z1,z2,z4,z5,z6]),(0,[z8,z972,z2,z4,z5,z6]),(0,[z8,z1,z69,z4,z205,z6]),(0,[z8,z2,z4,z158,z6,z37])],[(0,[z39,z15,z2,z4,z5,z6]),(0,[z363,z10,z1,z2,z4,z6]),(0,[z12,z8,z1,z550,z5,z13]),(0,[z8,z2,z4,z6,z55,z107])],[(0,[z8,z1,z319,z65,z5,z6]),(0,[z152,z122,z1,z4,z5,z144]),(0,[z8,z1,z2,z4,z18,z6])],[(0,[z8,z343,z2,z4,z18,z6])],[(0,[z8,z1,z2,z973,z5,z6]),(0,[z8,z1,z454,z4,z6,z37]),(0,[z81,z8,z232,z4,z5,z6]),(0,[z8,z1,z4,z5,z6,z711]),(0,[z2,z4,z5,z6,z48,z974])],[(0,[z8,z10,z22,z2,z4,z48]),(0,[z8,z1,z2,z4,z5,z975]),(0,[z976,z8,z1,z2,z4,z6])],[(0,[z8,z2,z4,z5,z573,z48]),(0,[z8,z1,z2,z977,z5,z6]),(0,[z1,z2,z4,z5,z6,z978])],[(0,[z8,z1,z2,z4,z979,z6]),(0,[z8,z1,z980,z4,z5,z6]),(0,[z22,z2,z4,z5,z6,z227]),(0,[z8,z1,z2,z4,z981,z6]),(0,[z8,z982,z2,z4,z5,z6]),(0,[z8,z325,z2,z4,z251,z6])]],
   [[(0,[z8,z983,z2,z4,z5,z6]),(0,[z8,z454,z4,z5,z6,z48]),(0,[z183,z8,z2,z4,z5,z833])],[(0,[z8,z1,z454,z116,z5,z6]),(0,[z8,z1,z2,z212,z4,z37]),(0,[z8,z137,z2,z413,z5,z6])],[(0,[z47,z8,z22,z4,z6,z25]),(0,[z8,z343,z69,z4,z5,z6])],[(0,[z8,z54,z2,z126,z6,z37]),(0,[z22,z237,z2,z4,z5,z6]),(0,[z138,z1,z2,z4,z6,z37]),(0,[z363,z1,z2,z4,z205,z6])],[(0,[z42,z2,z4,z5,z6,z48])],[(0,[z101,z2,z4,z5,z6,z48]),(0,[z984,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z985]),(0,[z8,z22,z2,z4,z5,z360]),(0,[z8,z22,z2,z986,z4,z6]),(0,[z8,z26,z2,z4,z6,z37])],[(0,[z77,z1,z125,z4,z5,z6]),(0,[z641,z1,z125,z4,z5,z6]),(0,[z8,z987,z2,z4,z5,z6]),(0,[z10,z1,z237,z2,z4,z6]),(0,[z8,z1,z2,z145,z85,z55])],[(0,[z44,z2,z4,z5,z6,z48]),(0,[z750,z2,z4,z5,z6,z48]),(0,[z513,z22,z2,z4,z5,z6])],[(0,[z77,z125,z4,z5,z6,z48]),(0,[z988,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z40,z6,z151]),(0,[z8,z2,z4,z37,z48,z13]),(0,[z122,z22,z2,z4,z5,z6])],[(0,[z81,z204,z8,z82,z4,z6]),(0,[z8,z1,z2,z4,z6,z989]),(0,[z8,z2,z4,z990,z5,z6]),(0,[z8,z2,z4,z382,z6,z37]),(0,[z991,z1,z2,z4,z5,z6]),(0,[z8,z992,z2,z4,z5,z6]),(1,[z8,z1,z4,z6,z852])],[(0,[z8,z993,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z994])],[(0,[z313,z1,z2,z4,z5,z6]),(0,[z8,z995,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z107]),(0,[z47,z8,z1,z4,z6,z852])],[(0,[z782,z1,z2,z4,z5,z6]),(0,[z8,z996,z1,z2,z4,z6]),(0,[z387,z8,z82,z4,z5,z6]),(0,[z39,z8,z2,z4,z6,z167])],[],[(1,[z1,z2,z809,z5,z6]),(0,[z315,z2,z4,z40,z5,z6]),(0,[z997,z8,z1,z2,z4,z6])]],
   [[(0,[z1,z125,z454,z4,z5,z6]),(0,[z8,z553,z2,z4,z6,z37]),(0,[z8,z22,z2,z4,z5,z196])],[(0,[z22,z15,z2,z4,z5,z48])],[],[(0,[z8,z968,z2,z4,z5,z6]),(0,[z8,z1,z918,z4,z5,z6]),(0,[z67,z22,z2,z4,z5,z6])],[(0,[z1,z417,z2,z4,z5,z113]),(0,[z8,z1,z998,z4,z5,z6]),(0,[z8,z154,z322,z4,z5,z6]),(0,[z8,z22,z2,z468,z4,z6]),(0,[z32,z1,z2,z4,z6,z37]),(0,[z8,z999,z2,z4,z5,z6]),(0,[z1000,z194,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z6]),(0,[z613,z1,z2,z4,z5,z6]),(0,[z77,z1,z419,z4,z5,z6]),(0,[z1001,z1,z2,z4,z5,z6]),(0,[z1002,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z1003,z5,z6])],[(0,[z152,z1,z4,z5,z221,z144])],[(0,[z437,z28,z2,z4,z5,z6]),(0,[z91,z338,z2,z4,z5,z6]),(0,[z1004,z8,z2,z4,z5,z6]),(0,[z8,z1005,z2,z4,z5,z6])],[(0,[z288,z1006,z2,z4,z5,z6])],[(0,[z2,z4,z5,z6,z48,z221]),(0,[z675,z8,z1,z83,z5,z6])],[(0,[z8,z2,z4,z5,z158,z6]),(0,[z1007,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1008])],[(0,[z1009,z8,z10,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1010,z6]),(0,[z8,z1,z1011,z2,z4,z6]),(0,[z8,z1,z2,z4,z1012,z6]),(0,[z1,z2,z4,z5,z6,z1013]),(0,[z143,z97,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1014,z6])],[(0,[z1015,z8,z1,z2,z4,z6]),(0,[z8,z141,z2,z4,z6,z243])],[]],
   [[(0,[z168,z1,z2,z4,z11,z6]),(0,[z138,z1,z2,z4,z5,z6]),(0,[z8,z1016,z2,z4,z5,z6]),(0,[z8,z54,z2,z126,z5,z6]),(0,[z97,z88,z1,z2,z4,z6]),(0,[z592,z8,z1,z2,z467,z6])],[(0,[z8,z1017,z2,z4,z5,z6]),(0,[z1,z579,z2,z79,z5,z6]),(0,[z189,z1,z2,z4,z11,z6]),(0,[z1018,z1,z2,z4,z5,z6]),(0,[z8,z10,z2,z4,z382,z6]),(0,[z1019,z8,z1,z2,z4,z6]),(0,[z1020,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z1021,z5,z6]),(0,[z8,z10,z1,z2,z522,z6]),(0,[z8,z2,z4,z40,z919,z6]),(0,[z1022,z2,z4,z5,z6,z48]),(0,[z1023,z8,z2,z4,z5,z6]),(0,[z8,z1,z59,z413,z5,z6])],[(0,[z8,z1,z2,z116,z6,z37]),(0,[z1,z2,z4,z5,z923,z52]),(0,[z8,z2,z126,z161,z5,z6]),(0,[z8,z26,z2,z4,z5,z6])],[(0,[z150,z1,z2,z79,z6,z37]),(0,[z8,z88,z2,z4,z6,z557]),(0,[z8,z2,z4,z826,z6,z48]),(0,[z631,z1,z2,z4,z6,z424])],[(0,[z16,z1,z2,z4,z5,z6]),(0,[z1024,z1,z2,z4,z5,z6]),(0,[z8,z1025,z1,z2,z4,z6]),(0,[z8,z247,z22,z2,z4,z6]),(0,[z8,z194,z2,z4,z6,z107])],[(0,[z8,z1,z2,z1026,z5,z6]),(0,[z513,z2,z4,z5,z6,z48]),(0,[z8,z1027,z2,z4,z5,z6]),(0,[z47,z42,z1,z4,z6,z25])],[(0,[z78,z1,z454,z4,z5,z6]),(0,[z8,z88,z2,z304,z4,z6]),(0,[z8,z22,z2,z4,z5,z48]),(0,[z122,z2,z4,z5,z6,z48]),(0,[z8,z1028,z1,z2,z4,z6]),(0,[z19,z97,z1,z2,z4,z6]),(0,[z970,z10,z1,z2,z4,z6]),(0,[z971,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z33,z6]),(0,[z255,z10,z1,z2,z4,z6]),(0,[z741,z22,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z1029]),(0,[z272,z405,z2,z4,z5,z6])],[(0,[z86,z1,z2,z476,z5,z6]),(0,[z150,z10,z1,z2,z79,z6])],[(0,[z77,z1,z2,z4,z33,z6]),(0,[z8,z659,z2,z4,z5,z48])],[(0,[z8,z1030,z1,z2,z4,z6]),(0,[z61,z8,z1,z2,z6,z62]),(0,[z984,z1,z2,z4,z6,z37]),(0,[z8,z10,z2,z4,z1031,z6])],[(0,[z8,z154,z454,z4,z5,z6]),(0,[z8,z10,z843,z2,z4,z6])],[(0,[z1032,z1,z2,z4,z5,z6]),(0,[z288,z8,z106,z65,z5,z6]),(0,[z8,z1,z2,z4,z6,z1033]),(0,[z8,z1,z2,z4,z1034,z6]),(0,[z1035,z1,z2,z4,z6,z37]),(0,[z1036,z1,z2,z4,z6,z37])],[(0,[z8,z2,z4,z310,z6,z48]),(0,[z8,z10,z553,z2,z4,z6]),(0,[z272,z1,z550,z4,z5,z6])],[(0,[z8,z1,z2,z1037,z5,z6]),(0,[z8,z1,z59,z4,z5,z118]),(0,[z8,z1,z2,z4,z37,z523])]],
   [[(0,[z8,z1038,z1,z2,z4,z6])],[(0,[z32,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z33,z6,z48]),(0,[z27,z1,z322,z4,z5,z52]),(0,[z67,z2,z4,z5,z6,z48]),(0,[z8,z10,z2,z4,z6,z24]),(0,[z8,z1,z2,z4,z6,z1039])],[(0,[z8,z1,z2,z4,z1040,z6]),(0,[z8,z2,z4,z5,z242,z48]),(0,[z66,z8,z1,z106,z65,z6]),(0,[z313,z1,z2,z4,z6,z37]),(0,[z8,z2,z4,z6,z37,z994])],[(0,[z95,z22,z2,z4,z5,z6]),(0,[z8,z2,z4,z6,z37,z107])],[(0,[z12,z8,z1,z2,z18,z13])],[(0,[z8,z2,z4,z1041,z5,z6])],[(0,[z8,z1,z2,z4,z6,z1042]),(0,[z1,z2,z4,z5,z6,z974]),(0,[z143,z8,z2,z4,z287,z6]),(0,[z272,z22,z2,z4,z5,z6]),(0,[z249,z8,z1,z2,z6,z62])],[(0,[z8,z1,z2,z4,z5,z1043])],[(0,[z1,z2,z34,z522,z5,z6]),(0,[z66,z8,z22,z2,z4,z6]),(0,[z8,z1,z2,z4,z914,z6])],[(0,[z204,z8,z22,z2,z4,z6]),(0,[z39,z8,z505,z2,z4,z6]),(0,[z769,z22,z2,z4,z5,z6]),(0,[z121,z379,z1,z83,z5,z6])],[(0,[z8,z1,z2,z4,z6,z1044]),(0,[z8,z1045,z1,z2,z4,z6]),(0,[z8,z22,z2,z4,z104,z6])],[(0,[z8,z1,z2,z4,z5,z1046]),(0,[z66,z876,z1,z2,z4,z6]),(0,[z613,z1,z2,z4,z6,z37])],[(0,[z653,z1,z2,z4,z5,z52]),(0,[z8,z137,z2,z4,z5,z6]),(0,[z313,z10,z1,z2,z4,z6]),(0,[z8,z343,z2,z4,z6,z37])],[(0,[z8,z1,z1047,z4,z5,z6]),(0,[z78,z22,z2,z4,z5,z113]),(1,[z8,z2,z885,z5,z6]),(0,[z19,z10,z1,z99,z2,z4])],[(0,[z1048,z1,z2,z4,z5,z6]),(0,[z588,z8,z2,z4,z6,z167])],[(0,[z8,z1,z2,z4,z1049,z6]),(0,[z8,z1050,z1,z2,z4,z6]),(0,[z8,z2,z4,z5,z6,z1051])]],
   [[(0,[z8,z1,z2,z1052,z5,z6]),(0,[z77,z10,z1,z125,z4,z6]),(0,[z8,z1,z2,z116,z5,z6]),(0,[z0,z1,z2,z4,z30,z6]),(0,[z8,z1053,z2,z4,z5,z6]),(0,[z47,z8,z1,z440,z4,z6])],[(0,[z150,z1,z2,z79,z5,z6]),(0,[z8,z1,z2,z4,z567,z37])],[(0,[z8,z1,z607,z65,z5,z6]),(0,[z1,z237,z2,z5,z6,z13]),(0,[z8,z1,z59,z4,z60,z243])],[(0,[z64,z8,z2,z105,z5,z6]),(0,[z868,z1,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z1054,z6]),(0,[z1055,z1,z2,z4,z5,z6]),(0,[z61,z101,z1,z2,z6,z62])],[(0,[z8,z10,z1,z2,z4,z6]),(0,[z1056,z1,z2,z4,z5,z6]),(0,[z613,z10,z1,z2,z4,z6])],[(0,[z8,z10,z2,z4,z6,z48]),(0,[z1057,z1,z2,z4,z5,z6]),(0,[z61,z356,z8,z2,z4,z6])],[(0,[z121,z8,z22,z83,z5,z6]),(0,[z1058,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z180])],[(0,[z8,z1,z2,z4,z6,z1059]),(0,[z27,z1,z2,z4,z5,z600]),(0,[z27,z1,z454,z4,z5,z52])],[(0,[z174,z10,z1,z3,z4,z6]),(0,[z174,z1,z552,z4,z5,z6]),(0,[z1060,z8,z1,z2,z4,z6]),(0,[z8,z22,z106,z65,z5,z6]),(0,[z1036,z1,z2,z4,z5,z6]),(0,[z1035,z1,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z6,z1061]),(0,[z8,z1062,z2,z4,z5,z6]),(0,[z8,z2,z421,z5,z6,z415]),(0,[z1,z15,z2,z4,z6,z37]),(0,[z16,z1,z2,z4,z6,z37])],[(0,[z8,z1,z2,z4,z5,z1063]),(0,[z8,z22,z2,z332,z5,z6]),(0,[z8,z96,z1,z59,z4,z60])],[(0,[z8,z2,z4,z5,z6,z1064]),(0,[z8,z1065,z2,z4,z5,z6]),(0,[z8,z2,z100,z4,z5,z48]),(0,[z8,z1,z2,z4,z1066,z6]),(0,[z8,z1,z4,z5,z751,z144])],[(0,[z326,z2,z3,z4,z5,z6]),(0,[z1,z454,z34,z4,z5,z6]),(0,[z8,z1,z2,z6,z732,z62])],[(0,[z8,z98,z2,z4,z5,z6]),(0,[z8,z2,z4,z109,z5,z48]),(0,[z1067,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z205,z6])]],
   [[(0,[z138,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1068,z6]),(0,[z8,z2,z4,z5,z557,z48]),(0,[z95,z2,z4,z5,z6,z48])],[(1,[z1,z2,z4,z758,z6]),(0,[z1069,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z221]),(0,[z1070,z8,z1,z2,z4,z6]),(0,[z8,z1,z1071,z4,z5,z6])],[(0,[z1,z28,z454,z4,z5,z6]),(0,[z8,z1,z2,z4,z1072,z5]),(0,[z272,z2,z4,z5,z6,z48])],[(0,[z8,z1,z2,z4,z6,z1073]),(0,[z813,z22,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z1074]),(0,[z8,z1,z1075,z4,z5,z6])],[(0,[z8,z1076,z2,z4,z5,z6]),(0,[z81,z8,z82,z4,z6,z37]),(0,[z363,z22,z2,z4,z5,z6]),(0,[z8,z10,z137,z2,z4,z6])],[(0,[z92,z10,z28,z2,z4,z6]),(0,[z91,z15,z2,z4,z5,z6]),(0,[z8,z1077,z2,z4,z5,z6]),(0,[z78,z1,z2,z4,z113,z37]),(0,[z771,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z6,z1078]),(0,[z8,z1079,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z251,z6]),(0,[z613,z1,z2,z4,z251,z6]),(0,[z8,z1,z84,z4,z6,z163])],[(0,[z8,z1080,z2,z4,z5,z6]),(0,[z1,z237,z2,z145,z5,z6]),(0,[z8,z1,z2,z5,z781,z13])],[(0,[z8,z1081,z2,z4,z5,z6]),(0,[z8,z343,z2,z4,z5,z6]),(0,[z270,z1,z2,z4,z928,z6])],[(0,[z8,z22,z2,z4,z5,z250]),(0,[z1,z2,z4,z1082,z5,z6]),(0,[z8,z1,z322,z4,z131,z6]),(0,[z8,z2,z4,z1083,z5,z6]),(0,[z1084,z1,z2,z4,z5,z6])],[(0,[z39,z8,z2,z526,z4,z6]),(0,[z1085,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z113,z690]),(0,[z8,z2,z4,z362,z6,z48]),(0,[z8,z1,z2,z5,z85,z781])],[(0,[z568,z1,z2,z79,z5,z6])],[(0,[z77,z1,z331,z4,z5,z6]),(0,[z1,z1086,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z248,z48])],[(0,[z8,z1087,z1,z2,z4,z6]),(0,[z8,z1,z2,z145,z85,z37])]],
   [[(0,[z8,z1,z49,z4,z6,z852]),(0,[z8,z214,z453,z2,z4,z6])],[(0,[z91,z1,z454,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z1088]),(0,[z174,z3,z4,z5,z6,z48]),(0,[z8,z1089,z2,z4,z5,z6]),(0,[z204,z8,z38,z2,z4,z6]),(0,[z32,z10,z1,z2,z4,z6]),(0,[z1090,z8,z1,z2,z4,z6]),(0,[z152,z8,z1,z4,z37,z144])],[(0,[z513,z1,z2,z522,z5,z6]),(0,[z31,z8,z2,z105,z5,z6]),(0,[z31,z8,z2,z104,z105,z6]),(0,[z8,z2,z5,z6,z48,z863]),(0,[z8,z1091,z2,z4,z5,z6]),(0,[z8,z137,z2,z4,z6,z37]),(0,[z8,z10,z141,z2,z4,z6])],[(0,[z8,z2,z4,z5,z6,z260]),(0,[z8,z1,z2,z4,z1092,z6]),(0,[z8,z1093,z2,z4,z5,z6])],[(0,[z1,z454,z4,z5,z6,z52]),(0,[z1094,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z205,z6,z48]),(0,[z8,z10,z320,z2,z4,z6])],[(0,[z8,z1,z870,z106,z5,z6])],[(0,[z39,z32,z2,z4,z5,z6]),(0,[z1095,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z220,z6])],[(0,[z8,z1096,z2,z4,z5,z6]),(0,[z1097,z1,z2,z4,z5,z6]),(0,[z152,z8,z1,z4,z220,z144])],[(0,[z1,z15,z2,z4,z5,z6]),(0,[z8,z1,z322,z4,z393,z6]),(0,[z1098,z1,z2,z4,z5,z6]),(0,[z8,z1,z776,z2,z4,z5])],[(0,[z8,z1,z2,z4,z1099,z6]),(0,[z1,z2,z4,z5,z6,z1100]),(0,[z8,z2,z4,z1031,z5,z6])],[(0,[z1,z3,z4,z5,z6,z647]),(0,[z8,z1,z2,z1101,z5,z6]),(0,[z1102,z1,z2,z4,z5,z6]),(0,[z66,z288,z8,z2,z4,z6]),(0,[z121,z8,z1,z692,z5,z6])],[(0,[z8,z154,z2,z4,z5,z6]),(0,[z8,z1,z1103,z4,z5,z6]),(0,[z1,z2,z522,z5,z11,z6]),(0,[z742,z1,z2,z4,z5,z6]),(0,[z1056,z1,z2,z4,z6,z37])],[(0,[z8,z1104,z2,z4,z5,z6]),(0,[z8,z1,z1105,z2,z6,z37])],[(0,[z1106,z8,z2,z4,z5,z6]),(0,[z1107,z1,z2,z4,z5,z6])],[],[(0,[z8,z22,z2,z4,z5,z475]),(0,[z8,z1,z1108,z4,z5,z6]),(0,[z0,z1,z2,z4,z758,z6]),(0,[z8,z2,z4,z5,z6,z115]),(0,[z8,z1109,z2,z4,z5,z6]),(0,[z8,z1,z4,z5,z6,z751]),(0,[z363,z1,z2,z5,z6,z13]),(0,[z8,z10,z1,z776,z2,z4])]],
   [[(0,[z8,z1,z59,z4,z5,z182]),(0,[z78,z8,z2,z4,z37,z48]),(0,[z8,z22,z2,z4,z6,z55]),(0,[z8,z2,z4,z6,z243,z90])],[(0,[z174,z1,z2,z522,z5,z6]),(0,[z8,z1,z2,z885,z5,z6]),(0,[z8,z2,z4,z5,z833,z48]),(0,[z8,z2,z4,z5,z6,z1110])],[(0,[z8,z1,z2,z4,z1111,z6]),(0,[z0,z1,z454,z4,z5,z6]),(0,[z8,z1,z454,z4,z131,z6]),(0,[z8,z10,z1,z2,z4,z674]),(0,[z8,z10,z405,z2,z4,z6])],[(0,[z8,z10,z1,z2,z116,z6]),(0,[z81,z8,z82,z4,z5,z6]),(0,[z8,z1,z83,z870,z5,z6])],[(0,[z1,z2,z4,z79,z33,z6]),(0,[z19,z1,z2,z4,z30,z6]),(0,[z237,z2,z4,z5,z6,z48]),(0,[z363,z2,z4,z5,z6,z48]),(0,[z1112,z1,z2,z4,z5,z6])],[(0,[z91,z553,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1113,z6]),(0,[z8,z1,z2,z1114,z5,z6]),(0,[z8,z2,z4,z5,z919,z6]),(0,[z8,z96,z1,z2,z4,z6]),(0,[z8,z1,z776,z2,z4,z37]),(0,[z8,z98,z2,z4,z6,z37])],[(0,[z8,z437,z322,z4,z5,z6]),(0,[z8,z1,z1115,z4,z5,z6]),(0,[z8,z96,z2,z4,z6,z48]),(0,[z64,z8,z2,z5,z6,z71]),(0,[z1057,z10,z1,z2,z4,z6])],[],[(0,[z8,z1,z2,z4,z1116,z6]),(0,[z8,z1,z2,z4,z5,z1117]),(0,[z61,z8,z1,z2,z467,z6])],[(0,[z27,z326,z2,z4,z5,z6]),(0,[z8,z54,z2,z23,z5,z6]),(0,[z8,z1118,z2,z4,z5,z6])],[(0,[z1,z2,z4,z6,z37,z221]),(0,[z8,z1,z69,z145,z5,z6])],[(0,[z8,z1119,z1,z2,z4,z6]),(0,[z31,z255,z2,z105,z5,z6]),(0,[z8,z2,z4,z37,z48,z144])],[(0,[z8,z1120,z1,z2,z4,z6]),(0,[z8,z10,z1,z278,z2,z4]),(0,[z8,z1121,z2,z5,z6,z48])],[(0,[z8,z1122,z1,z2,z4,z6]),(0,[z8,z1,z2,z1123,z4,z6]),(0,[z1124,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z127,z6]),(0,[z1125,z1,z2,z4,z5,z6])],[(0,[z8,z1,z1126,z4,z5,z6]),(0,[z8,z137,z2,z4,z251,z6])],[(0,[z8,z1,z2,z4,z135,z6]),(0,[z506,z15,z2,z4,z5,z6]),(0,[z613,z137,z2,z4,z5,z6]),(0,[z1127,z8,z1,z2,z4,z6]),(0,[z8,z10,z98,z99,z2,z4])]],
   [[(0,[z8,z1128,z1,z2,z4,z6]),(0,[z1129,z1,z2,z4,z5,z6]),(0,[z8,z405,z69,z4,z5,z6])],[(0,[z8,z1130,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z6,z1131])],[(0,[z8,z1,z2,z4,z1132,z6]),(0,[z8,z1133,z2,z4,z5,z6]),(0,[z288,z8,z10,z2,z4,z6]),(0,[z356,z8,z10,z2,z4,z6]),(0,[z26,z840,z2,z4,z5,z6])],[(0,[z1134,z1,z2,z4,z5,z6])],[(0,[z8,z10,z1,z2,z4,z35]),(0,[z8,z10,z1,z2,z4,z218]),(0,[z1135,z1,z2,z4,z5,z6]),(0,[z1,z1086,z2,z4,z6,z37])],[(0,[z1,z1136,z2,z4,z5,z6]),(0,[z363,z1,z2,z145,z5,z6])],[(0,[z8,z2,z885,z105,z5,z6]),(0,[z8,z2,z4,z926,z6,z48]),(0,[z356,z8,z2,z136,z4,z6])],[(0,[z8,z22,z2,z4,z5,z165]),(0,[z8,z1,z2,z4,z6,z1137]),(0,[z8,z495,z2,z23,z5,z6])],[(0,[z540,z1,z3,z4,z5,z6]),(0,[z8,z22,z2,z4,z310,z6]),(0,[z27,z1,z2,z4,z5,z52]),(0,[z31,z8,z2,z105,z6,z37]),(0,[z121,z8,z10,z1,z83,z6]),(0,[z152,z613,z1,z4,z5,z144]),(0,[z12,z8,z1,z2,z5,z781])],[(0,[z8,z1138,z2,z4,z5,z6]),(0,[z8,z1,z1105,z2,z5,z6])],[(0,[z1139,z8,z1,z2,z4,z6]),(0,[z8,z2,z4,z6,z37,z260]),(0,[z8,z1140,z2,z4,z5,z6]),(0,[z884,z1,z2,z4,z5,z6]),(0,[z1141,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1142,z6]),(0,[z208,z8,z10,z2,z4,z6]),(0,[z363,z405,z2,z4,z5,z6])],[],[(0,[z1143,z1,z2,z4,z5,z6]),(0,[z39,z8,z2,z4,z919,z6]),(0,[z16,z1,z4,z5,z6,z144]),(0,[z1144,z1,z2,z4,z5,z6])],[(0,[z8,z22,z322,z4,z5,z6]),(0,[z8,z2,z4,z6,z359,z48]),(0,[z8,z22,z69,z4,z5,z6]),(0,[z8,z1145,z2,z4,z5,z6]),(0,[z8,z10,z26,z2,z4,z6]),(0,[z8,z110,z2,z4,z6,z37])],[]],
   [[(0,[z1,z299,z125,z4,z5,z6]),(0,[z81,z8,z215,z4,z5,z6]),(0,[z270,z15,z2,z4,z5,z6]),(0,[z152,z8,z1,z332,z5,z144]),(0,[z10,z97,z1,z99,z2,z4])],[(0,[z8,z154,z2,z4,z6,z37]),(0,[z363,z1,z550,z4,z5,z6])],[(0,[z97,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z852]),(0,[z8,z1,z59,z4,z5,z60]),(0,[z8,z96,z141,z2,z4,z6]),(0,[z12,z8,z1,z2,z5,z13])],[(0,[z8,z2,z4,z5,z6,z1146]),(0,[z902,z22,z2,z4,z5,z6]),(0,[z1,z1147,z2,z4,z5,z6]),(0,[z8,z343,z2,z4,z205,z6])],[(0,[z8,z1,z2,z4,z1148,z6]),(0,[z810,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1149,z6]),(0,[z379,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1150,z6]),(0,[z1,z125,z829,z4,z5,z6]),(0,[z1151,z8,z1,z2,z4,z6]),(0,[z1006,z1,z2,z4,z5,z6]),(0,[z1152,z1,z2,z4,z5,z6])],[(0,[z270,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z1153,z5,z6]),(0,[z8,z1,z2,z4,z6,z1154]),(0,[z8,z154,z2,z116,z5,z6]),(0,[z1155,z1,z2,z4,z5,z6]),(0,[z1156,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z6,z37,z115]),(0,[z1095,z10,z1,z2,z4,z6])],[(0,[z8,z10,z1,z659,z2,z4]),(0,[z8,z10,z22,z2,z4,z37]),(0,[z8,z1157,z2,z4,z5,z6]),(0,[z1158,z1,z2,z4,z6,z37])],[(0,[z16,z10,z1,z2,z4,z6]),(0,[z8,z1159,z2,z4,z5,z6])],[(0,[z191,z8,z215,z4,z5,z6]),(0,[z911,z22,z2,z4,z5,z6])],[(0,[z494,z1,z2,z4,z11,z6]),(0,[z81,z204,z8,z2,z4,z6])],[(0,[z8,z1,z2,z5,z6,z1160]),(0,[z8,z1,z2,z5,z6,z732])],[(0,[z538,z28,z2,z4,z5,z6]),(0,[z8,z1,z2,z145,z5,z268]),(0,[z8,z1,z2,z4,z1161,z6])],[(0,[z8,z1,z2,z4,z362,z6])],[(0,[z8,z1,z829,z4,z5,z6]),(0,[z143,z8,z2,z4,z46,z6]),(0,[z15,z2,z4,z316,z5,z6]),(0,[z121,z67,z1,z83,z5,z6]),(0,[z8,z10,z325,z2,z4,z6])],[(0,[z8,z1162,z2,z4,z5,z6])]],
   [[(0,[z77,z1,z829,z4,z5,z6]),(0,[z8,z1,z2,z4,z196,z37])],[(0,[z8,z1163,z2,z4,z5,z6]),(0,[z8,z365,z2,z4,z5,z48]),(0,[z61,z8,z22,z2,z6,z62])],[(0,[z8,z1164,z2,z4,z5,z6]),(0,[z78,z290,z1,z2,z4,z113])],[(0,[z8,z1165,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1166,z6]),(0,[z8,z1,z870,z4,z5,z6]),(0,[z8,z1,z2,z4,z6,z1167]),(0,[z1009,z8,z2,z4,z5,z6])],[(0,[z8,z322,z4,z5,z6,z48]),(0,[z8,z1,z322,z522,z5,z6]),(0,[z8,z1,z2,z4,z5,z1168]),(0,[z8,z2,z4,z5,z6,z1169]),(0,[z96,z1020,z1,z2,z4,z6]),(0,[z8,z1170,z2,z4,z5,z6])],[(0,[z1171,z8,z2,z4,z5,z6]),(0,[z8,z22,z454,z4,z5,z6]),(0,[z81,z8,z468,z82,z4,z6]),(0,[z835,z1,z2,z4,z5,z6])],[(0,[z86,z326,z2,z4,z5,z6]),(0,[z412,z1,z2,z4,z30,z6]),(0,[z8,z1,z2,z145,z5,z704]),(0,[z8,z1,z69,z5,z6,z13])],[(0,[z8,z1,z2,z1172,z5,z6]),(0,[z8,z2,z1173,z4,z6,z48]),(0,[z270,z22,z2,z4,z5,z48]),(0,[z8,z22,z2,z4,z928,z6]),(0,[z8,z1,z2,z4,z1174,z6])],[(0,[z8,z1,z2,z4,z1175,z6])],[(0,[z513,z1,z2,z34,z5,z6]),(0,[z8,z188,z2,z4,z40,z6]),(0,[z8,z22,z2,z413,z5,z6]),(0,[z8,z596,z1,z56,z4,z6])],[(0,[z8,z290,z2,z4,z6,z260]),(0,[z8,z110,z2,z4,z5,z6]),(0,[z152,z8,z1,z413,z5,z144]),(0,[z356,z8,z2,z4,z6,z37])],[],[(0,[z8,z2,z4,z5,z6,z1176]),(0,[z19,z930,z2,z4,z5,z6])],[(0,[z36,z1,z2,z4,z758,z6]),(0,[z1177,z1,z2,z4,z5,z6]),(0,[z19,z10,z1,z2,z4,z37])],[(0,[z1,z2,z79,z5,z6,z418]),(0,[z8,z1178,z2,z4,z5,z6]),(0,[z8,z2,z4,z382,z362,z6]),(0,[z1179,z1,z2,z4,z5,z6])]],
   [[(0,[z174,z22,z3,z4,z5,z6]),(0,[z86,z1,z2,z657,z5,z6]),(0,[z97,z2,z4,z5,z6,z48]),(0,[z16,z1,z59,z4,z5,z6])],[(0,[z8,z2,z4,z5,z500,z48]),(0,[z8,z1,z2,z4,z131,z6]),(0,[z1,z2,z4,z5,z6,z923]),(0,[z1,z2,z4,z5,z6,z1180])],[(0,[z1181,z1,z2,z4,z5,z6]),(0,[z22,z15,z2,z4,z6,z37])],[(0,[z27,z1,z2,z116,z5,z52]),(0,[z8,z88,z2,z4,z6,z285])],[(0,[z8,z247,z22,z2,z4,z89]),(0,[z1182,z1,z2,z4,z5,z6]),(0,[z1158,z1,z2,z4,z5,z6])],[(0,[z8,z76,z2,z4,z310,z6]),(0,[z8,z10,z1,z106,z65,z6])],[(0,[z8,z22,z2,z4,z5,z833]),(0,[z8,z1183,z2,z4,z5,z6]),(0,[z8,z1184,z2,z4,z5,z6])],[(0,[z910,z2,z4,z5,z6,z48]),(0,[z1185,z1,z2,z4,z5,z6])],[(0,[z92,z15,z2,z4,z5,z6]),(0,[z27,z10,z1,z2,z4,z52]),(0,[z31,z8,z2,z376,z5,z6]),(0,[z8,z2,z4,z5,z6,z1186]),(0,[z1187,z8,z1,z2,z4,z6]),(0,[z1,z1188,z2,z4,z5,z6])],[(0,[z0,z2,z4,z30,z6,z48]),(0,[z8,z1,z2,z4,z1189,z6]),(0,[z8,z1190,z1,z2,z4,z6]),(0,[z8,z10,z1,z2,z4,z248])],[(0,[z1191,z8,z1,z2,z4,z6]),(0,[z61,z8,z1,z2,z594,z6]),(0,[z353,z8,z2,z312,z5,z6]),(0,[z8,z1,z2,z4,z279,z37]),(0,[z8,z1,z413,z5,z6,z144]),(0,[z8,z405,z2,z4,z6,z37])],[(0,[z270,z28,z2,z4,z5,z6]),(0,[z8,z10,z22,z2,z4,z6]),(0,[z379,z1,z2,z4,z6,z37])],[(0,[z270,z1,z2,z4,z6,z37]),(0,[z8,z405,z2,z4,z18,z6]),(0,[z8,z194,z1,z2,z145,z85])],[(0,[z8,z1,z2,z4,z1192,z6]),(0,[z8,z1193,z2,z4,z5,z6]),(0,[z81,z8,z918,z4,z5,z6]),(0,[z8,z1,z2,z4,z1194,z6]),(0,[z1195,z1,z2,z4,z5,z6]),(0,[z1196,z1,z2,z4,z5,z6])],[(0,[z86,z1,z2,z34,z6,z37])],[(0,[z8,z1,z2,z4,z393,z6]),(0,[z1,z2,z4,z5,z113,z923]),(0,[z12,z8,z405,z2,z5,z13])]],
   [[(0,[z121,z16,z1,z83,z5,z6]),(0,[z8,z1,z2,z4,z111,z37])],[(0,[z208,z8,z49,z2,z4,z6])],[(0,[z8,z1197,z2,z4,z5,z6]),(0,[z78,z2,z4,z5,z113,z260]),(0,[z8,z2,z4,z6,z180,z48]),(0,[z8,z2,z4,z5,z1198,z6]),(0,[z8,z1,z550,z4,z18,z6]),(0,[z8,z1,z2,z6,z37,z1160])],[(0,[z8,z1,z1199,z4,z5,z6]),(0,[z8,z1,z454,z4,z393,z6]),(0,[z8,z1,z2,z4,z6,z1200]),(0,[z8,z1201,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z6,z1202]),(0,[z8,z2,z4,z5,z589,z48]),(0,[z8,z106,z65,z5,z6,z48]),(0,[z810,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z37,z258]),(0,[z1203,z1,z2,z4,z5,z6])],[(0,[z270,z10,z1,z2,z4,z6])],[(0,[z8,z1,z1204,z4,z5,z6]),(0,[z8,z2,z4,z40,z6,z618]),(0,[z47,z8,z4,z6,z48,z25]),(0,[z970,z22,z2,z4,z5,z6])],[(0,[z150,z2,z79,z5,z6,z48]),(0,[z288,z8,z2,z4,z5,z6]),(0,[z255,z22,z2,z4,z5,z6]),(0,[z356,z8,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z6,z37]),(0,[z19,z1,z2,z4,z6,z37])],[],[(0,[z8,z1,z1205,z4,z5,z6]),(0,[z8,z22,z2,z4,z18,z6]),(0,[z8,z22,z2,z4,z89,z37]),(0,[z95,z1,z2,z332,z5,z6])],[(0,[z8,z843,z2,z4,z5,z6])],[(0,[z290,z1,z2,z4,z11,z6]),(0,[z8,z2,z4,z60,z37,z48]),(0,[z8,z1,z2,z4,z1206,z6]),(0,[z12,z8,z1,z2,z205,z13])],[(0,[z121,z1,z83,z237,z5,z6]),(0,[z8,z1,z4,z119,z6,z852]),(0,[z1207,z8,z1,z2,z4,z6])],[(0,[z8,z10,z1,z2,z4,z403]),(0,[z851,z2,z4,z5,z6,z48]),(0,[z47,z313,z1,z4,z6,z25])],[(0,[z8,z22,z2,z4,z5,z612]),(0,[z8,z1208,z2,z4,z5,z6]),(0,[z22,z15,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z981,z6]),(0,[z1209,z1,z2,z4,z5,z6]),(0,[z8,z1,z776,z2,z4,z111])]],
   [[(0,[z8,z2,z4,z1210,z5,z6])],[(0,[z1,z829,z3,z4,z5,z6]),(0,[z8,z1,z2,z1211,z5,z6]),(0,[z8,z437,z454,z4,z5,z6]),(0,[z8,z553,z2,z4,z6,z359]),(0,[z208,z8,z2,z4,z5,z6])],[(0,[z8,z10,z437,z2,z4,z6]),(0,[z1,z2,z4,z5,z6,z1212])],[(0,[z1,z2,z4,z5,z6,z1213]),(0,[z1203,z26,z2,z4,z5,z6])],[(0,[z39,z8,z129,z2,z4,z6]),(0,[z143,z15,z2,z4,z5,z6])],[(0,[z326,z2,z4,z5,z113,z6]),(0,[z8,z507,z2,z4,z30,z6]),(0,[z8,z1,z2,z4,z6,z1214])],[(0,[z8,z2,z4,z5,z358,z48]),(0,[z8,z1,z2,z4,z5,z1215]),(0,[z8,z1,z2,z4,z1216,z6]),(0,[z8,z10,z1,z2,z4,z529]),(0,[z8,z2,z145,z5,z85,z107])],[(0,[z77,z22,z125,z4,z5,z6]),(0,[z27,z2,z4,z5,z52,z48]),(0,[z8,z405,z2,z4,z5,z6]),(0,[z1090,z8,z22,z2,z4,z6])],[(0,[z1,z2,z4,z6,z37,z1180])],[(0,[z8,z1,z2,z4,z6,z1217]),(0,[z8,z1,z1121,z2,z5,z6]),(0,[z31,z8,z10,z2,z105,z6])],[(1,[z1,z829,z4,z5,z6]),(0,[z8,z1218,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1219,z6])],[(0,[z86,z1,z2,z34,z5,z6]),(0,[z8,z1,z2,z4,z1220,z6]),(0,[z8,z1221,z2,z4,z5,z6])],[(0,[z8,z1,z2,z116,z131,z6]),(0,[z1222,z1,z2,z4,z5,z6]),(0,[z2,z4,z5,z6,z48,z1213]),(0,[z8,z2,z4,z1014,z6,z48]),(0,[z313,z22,z2,z4,z5,z6]),(0,[z8,z1,z776,z2,z4,z6])],[(0,[z1,z2,z1223,z4,z5,z6]),(0,[z8,z2,z126,z885,z5,z6]),(0,[z8,z1,z550,z4,z5,z6]),(0,[z47,z208,z8,z4,z6,z25])],[(0,[z27,z154,z2,z4,z5,z52]),(0,[z560,z8,z1,z4,z6,z263])],[(0,[z1224,z8,z1,z2,z4,z5]),(0,[z8,z1,z2,z1225,z4,z6]),(1,[z8,z2,z4,z919,z6])]],
   [[(0,[z1226,z8,z2,z4,z5,z6]),(0,[z1129,z96,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z6,z732])],[(0,[z489,z1,z3,z4,z5,z6]),(0,[z8,z1,z2,z1227,z4,z6])],[(0,[z883,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1228,z6])],[(0,[z92,z28,z2,z4,z5,z6]),(0,[z8,z1,z1229,z4,z5,z6]),(0,[z8,z1230,z2,z4,z5,z6]),(0,[z8,z1231,z2,z4,z5,z6]),(0,[z315,z1,z2,z4,z6,z37])],[(0,[z95,z1,z2,z4,z220,z6]),(0,[z1182,z10,z1,z2,z4,z6])],[(0,[z8,z22,z2,z4,z5,z6]),(0,[z19,z1,z2,z4,z5,z6]),(0,[z8,z38,z4,z269,z5,z6]),(0,[z613,z22,z2,z4,z5,z6])],[(0,[z255,z2,z4,z5,z6,z48]),(0,[z8,z1232,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z547,z37]),(0,[z8,z10,z99,z2,z4,z48]),(0,[z1185,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1233,z6]),(0,[z8,z1,z2,z4,z1234,z6]),(0,[z8,z2,z4,z5,z529,z48])],[(0,[z8,z1,z2,z4,z5,z1235]),(0,[z77,z1,z652,z4,z5,z6]),(0,[z1236,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z251,z6,z48])],[(0,[z8,z10,z154,z2,z4,z6]),(0,[z8,z1,z2,z116,z393,z6])],[(0,[z7,z1,z2,z34,z5,z6]),(0,[z1,z2,z4,z30,z758,z6]),(0,[z8,z96,z22,z2,z4,z6]),(0,[z1237,z1,z2,z4,z6,z37])],[(0,[z1238,z1,z2,z4,z5,z6]),(0,[z1239,z1,z2,z4,z5,z6]),(0,[z8,z10,z1,z2,z4,z396]),(0,[z183,z8,z2,z4,z37,z48]),(0,[z288,z1135,z2,z4,z5,z6]),(0,[z10,z1,z2,z4,z6,z221]),(0,[z8,z1240,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1241,z6]),(0,[z756,z8,z1,z2,z4,z6]),(0,[z8,z124,z2,z4,z6,z285])],[(0,[z8,z1,z2,z4,z6,z1242]),(0,[z8,z1,z2,z4,z6,z1243]),(0,[z8,z1,z2,z4,z1244,z6]),(0,[z8,z2,z4,z5,z6,z24]),(0,[z288,z8,z2,z4,z6,z37])],[(0,[z8,z1,z2,z4,z5,z923]),(0,[z8,z2,z126,z5,z6,z658]),(0,[z8,z2,z4,z111,z37,z48]),(0,[z8,z1,z2,z4,z5,z781])]],
   [[(0,[z8,z102,z2,z4,z40,z6]),(0,[z1,z2,z4,z393,z11,z6]),(0,[z8,z1245,z2,z4,z5,z6]),(0,[z8,z10,z1,z454,z4,z6]),(0,[z8,z1,z2,z4,z203,z37]),(0,[z8,z2,z918,z4,z5,z6]),(0,[z8,z2,z4,z6,z55,z48]),(0,[z138,z22,z2,z4,z5,z6]),(0,[z8,z10,z1,z69,z4,z6])],[(0,[z1246,z8,z1,z2,z4,z6]),(0,[z141,z1147,z2,z4,z5,z6])],[(0,[z8,z1,z2,z1247,z4,z6])],[(0,[z8,z437,z2,z4,z6,z37]),(0,[z8,z2,z4,z131,z6,z48])],[(0,[z8,z782,z2,z4,z5,z6]),(0,[z8,z1,z2,z5,z6,z781]),(0,[z8,z2,z4,z111,z158,z37])],[(0,[z8,z1,z2,z4,z1248,z6]),(0,[z8,z2,z4,z5,z6,z1249]),(0,[z16,z22,z2,z4,z5,z6]),(0,[z8,z2,z4,z1250,z5,z6])],[(0,[z8,z1,z2,z4,z6,z243]),(0,[z8,z10,z1,z2,z413,z6])],[(0,[z1251,z1,z2,z4,z5,z6]),(0,[z208,z8,z2,z4,z6,z37])],[(0,[z8,z22,z2,z4,z33,z6]),(0,[z8,z437,z2,z116,z5,z6])],[(0,[z31,z8,z2,z312,z5,z6]),(0,[z8,z2,z4,z5,z6,z1252])],[(0,[z8,z1253,z2,z4,z5,z6]),(0,[z122,z1,z454,z4,z5,z6]),(0,[z313,z2,z4,z5,z6,z48]),(0,[z8,z1,z2,z4,z491,z37])],[(0,[z8,z1,z2,z4,z6,z1254])],[(0,[z1,z454,z4,z5,z11,z6]),(0,[z8,z1,z2,z4,z6,z359]),(0,[z8,z1,z2,z4,z199,z37]),(0,[z270,z1,z2,z4,z914,z6]),(0,[z19,z10,z843,z2,z4,z6])],[(0,[z91,z76,z2,z4,z310,z6]),(0,[z86,z10,z1,z2,z34,z6]),(0,[z78,z1,z2,z4,z5,z923]),(0,[z8,z1,z2,z4,z727,z6]),(0,[z22,z2,z4,z5,z6,z221]),(0,[z8,z1,z2,z332,z220,z6])],[],[(0,[z20,z28,z2,z4,z5,z6]),(0,[z19,z508,z1,z2,z4,z6]),(0,[z8,z10,z99,z320,z2,z4])]],
   [[(0,[z315,z1,z2,z4,z5,z6]),(0,[z1255,z8,z2,z4,z5,z6]),(0,[z8,z1,z454,z522,z5,z6])],[(0,[z8,z1,z2,z4,z6,z1256]),(0,[z32,z22,z2,z4,z5,z6]),(0,[z10,z97,z1,z2,z4,z37])],[(0,[z8,z59,z4,z5,z60,z48]),(0,[z47,z208,z8,z2,z4,z6]),(0,[z8,z1257,z2,z4,z5,z6]),(0,[z8,z1258,z2,z4,z5,z6])],[(0,[z8,z2,z4,z5,z6,z48]),(0,[z613,z2,z4,z5,z6,z48]),(0,[z10,z1,z15,z2,z4,z6]),(0,[z1259,z1,z2,z4,z5,z6]),(0,[z8,z1,z550,z4,z6,z37])],[(0,[z8,z1,z2,z4,z1260,z6]),(0,[z1261,z1,z2,z4,z5,z6]),(0,[z10,z1262,z1,z2,z4,z6])],[(0,[z8,z1,z1263,z4,z5,z6]),(0,[z1,z774,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1264,z6])],[],[(0,[z8,z154,z2,z4,z131,z6]),(0,[z8,z831,z4,z5,z6,z48]),(0,[z1265,z8,z2,z4,z5,z6]),(0,[z8,z1266,z1,z2,z4,z6])],[(0,[z174,z1,z454,z4,z5,z6]),(0,[z553,z15,z2,z4,z5,z6]),(0,[z8,z290,z2,z4,z6,z48]),(0,[z8,z1,z2,z4,z6,z1267]),(0,[z8,z22,z2,z4,z914,z6]),(0,[z22,z1086,z2,z4,z5,z6]),(0,[z12,z8,z22,z2,z5,z13]),(0,[z379,z10,z1,z2,z4,z6]),(0,[z1237,z1,z2,z4,z5,z6]),(0,[z1268,z1,z2,z4,z5,z6]),(0,[z8,z10,z930,z2,z4,z6])],[(0,[z92,z28,z2,z4,z6,z37]),(0,[z8,z1,z1269,z4,z5,z6]),(0,[z1156,z10,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1270,z6]),(0,[z8,z2,z4,z5,z6,z1271]),(0,[z8,z1,z2,z145,z5,z85])],[(0,[z584,z8,z2,z4,z5,z48]),(0,[z1272,z1,z2,z4,z5,z6]),(0,[z95,z325,z2,z4,z5,z6])],[],[(0,[z8,z1,z49,z4,z119,z6]),(0,[z8,z10,z2,z4,z6,z90])],[(0,[z326,z2,z4,z79,z5,z6]),(0,[z138,z2,z4,z5,z6,z48]),(0,[z1000,z1,z2,z4,z5,z6])],[(0,[z1,z2,z34,z809,z5,z6]),(0,[z272,z1,z69,z4,z5,z6])]],
   [[(0,[z8,z437,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1273,z6]),(0,[z8,z1274,z2,z4,z5,z6]),(0,[z8,z1,z1275,z4,z5,z6]),(0,[z0,z22,z2,z4,z30,z6]),(0,[z8,z22,z2,z116,z5,z6]),(0,[z15,z2,z4,z5,z6,z48])],[(0,[z150,z22,z2,z79,z5,z6]),(0,[z8,z1,z1276,z4,z5,z6]),(0,[z581,z8,z1,z2,z4,z6]),(0,[z1277,z1,z2,z4,z5,z6]),(0,[z1278,z8,z2,z4,z5,z6]),(0,[z8,z405,z2,z4,z205,z6])],[(0,[z8,z1279,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z1280,z6]),(0,[z581,z8,z2,z4,z6,z48]),(0,[z66,z1069,z1,z2,z4,z6])],[(0,[z27,z1,z2,z4,z5,z500]),(0,[z8,z1,z2,z1281,z5,z6]),(0,[z8,z1,z2,z4,z919,z6]),(0,[z16,z2,z4,z5,z6,z48])],[(0,[z19,z1,z2,z4,z11,z6]),(0,[z1,z1282,z2,z4,z5,z6]),(0,[z1283,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1284])],[(0,[z8,z154,z2,z4,z393,z6]),(0,[z39,z8,z2,z4,z571,z6]),(0,[z1285,z1,z2,z4,z5,z6]),(0,[z1056,z22,z2,z4,z5,z6]),(0,[z47,z8,z1,z575,z4,z6]),(0,[z8,z2,z4,z6,z37,z24]),(0,[z19,z10,z1,z2,z4,z6])],[(0,[z42,z1,z2,z4,z5,z6]),(0,[z1,z2,z34,z5,z6,z444]),(0,[z8,z2,z468,z4,z6,z48]),(0,[z19,z10,z2,z4,z6,z48]),(0,[z61,z356,z8,z2,z6,z62])],[(0,[z1,z2,z4,z5,z113,z549]),(0,[z101,z1,z2,z4,z5,z6]),(0,[z387,z8,z4,z5,z6,z429]),(0,[z8,z2,z4,z5,z226,z48]),(0,[z8,z1,z4,z5,z6,z852]),(0,[z8,z1,z550,z4,z205,z6])],[(0,[z0,z1,z2,z4,z80,z6]),(0,[z1286,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z6,z180]),(0,[z8,z1,z2,z413,z220,z6]),(1,[z8,z1,z4,z5,z751]),(0,[z8,z26,z2,z145,z5,z85])],[(0,[z8,z1287,z2,z4,z5,z6]),(0,[z121,z8,z1,z870,z5,z6])],[(0,[z44,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z37,z475]),(0,[z1288,z8,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z89,z180]),(0,[z8,z2,z4,z5,z6,z1289]),(0,[z1290,z1,z2,z4,z5,z6])],[(0,[z29,z8,z1,z4,z5,z144]),(0,[z8,z2,z4,z5,z6,z1291]),(0,[z152,z8,z1,z4,z5,z751]),(0,[z8,z194,z1,z2,z4,z6]),(0,[z513,z1,z2,z4,z6,z37])],[(0,[z8,z1,z2,z1292,z5,z6]),(0,[z8,z1,z2,z4,z1293,z6]),(0,[z8,z1294,z2,z4,z5,z6]),(0,[z8,z1,z2,z1295,z5,z6]),(0,[z8,z453,z2,z4,z40,z6]),(0,[z8,z194,z2,z4,z6,z48]),(0,[z122,z1,z2,z4,z6,z37])],[(0,[z8,z1296,z2,z4,z5,z6])],[(0,[z1297,z8,z2,z4,z5,z6]),(0,[z8,z1,z1298,z4,z5,z6]),(0,[z8,z1,z2,z4,z1299,z6]),(0,[z8,z1,z2,z4,z6,z1300]),(0,[z8,z1,z2,z4,z6,z1301]),(0,[z8,z2,z4,z5,z1302,z6])],[(0,[z150,z1,z2,z522,z5,z6]),(0,[z36,z1,z2,z4,z11,z6]),(0,[z78,z2,z4,z5,z113,z48]),(0,[z32,z2,z4,z5,z6,z48]),(0,[z8,z22,z2,z4,z205,z6]),(0,[z1303,z1,z2,z4,z5,z6]),(0,[z8,z1304,z2,z4,z5,z6])]],
   [[(0,[z77,z1,z556,z4,z5,z6]),(0,[z91,z2,z4,z5,z6,z619]),(0,[z31,z8,z2,z594,z5,z6]),(0,[z8,z2,z4,z18,z6,z48]),(0,[z8,z1305,z2,z4,z5,z6]),(0,[z1262,z1,z2,z4,z5,z6]),(0,[z8,z141,z2,z4,z6,z37])],[(0,[z1306,z1,z2,z4,z5,z6]),(0,[z8,z343,z550,z4,z5,z6])],[(0,[z8,z1,z2,z522,z6,z37]),(0,[z8,z1,z2,z4,z6,z1307]),(0,[z8,z2,z4,z46,z6,z396])],[(0,[z8,z1,z2,z1308,z5,z6]),(0,[z31,z581,z8,z2,z4,z6]),(0,[z8,z1,z120,z65,z5,z6]),(0,[z1309,z8,z2,z4,z5,z6]),(0,[z152,z8,z10,z1,z4,z144])],[(0,[z27,z1,z2,z4,z131,z52]),(0,[z8,z22,z2,z4,z5,z218]),(0,[z8,z1310,z2,z4,z5,z6]),(0,[z8,z325,z2,z332,z5,z6])],[(0,[z8,z1,z2,z4,z1311,z6]),(0,[z581,z8,z2,z126,z4,z6]),(0,[z8,z1,z2,z4,z6,z1312])],[],[(0,[z86,z1,z2,z809,z5,z6]),(0,[z1313,z1,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z251,z6])],[(0,[z8,z1,z2,z4,z109,z37]),(0,[z95,z1,z2,z413,z5,z6]),(0,[z152,z8,z1,z4,z251,z144])],[(0,[z122,z1,z125,z4,z5,z6]),(0,[z8,z507,z2,z4,z6,z37]),(0,[z8,z1,z2,z4,z6,z1314]),(0,[z270,z22,z2,z4,z928,z6]),(0,[z152,z8,z1,z4,z5,z144]),(0,[z779,z8,z10,z2,z4,z6])],[(0,[z276,z8,z2,z4,z5,z48]),(0,[z8,z2,z4,z6,z37,z48])],[(1,[z1,z2,z4,z5,z923]),(0,[z39,z315,z2,z4,z5,z6]),(0,[z31,z8,z2,z885,z5,z6]),(0,[z183,z8,z10,z2,z4,z48]),(0,[z724,z1,z2,z4,z6,z37])],[(0,[z1315,z1,z2,z4,z5,z6]),(0,[z1316,z8,z2,z4,z5,z6]),(0,[z1317,z8,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z6,z1318]),(0,[z8,z1,z2,z1173,z4,z6]),(0,[z8,z1319,z2,z4,z5,z6])],[(0,[z598,z1,z3,z4,z5,z6]),(0,[z0,z507,z2,z4,z30,z6])],[(0,[z8,z2,z4,z5,z6,z1320])]],
   [[(0,[z8,z1321,z1,z2,z4,z6]),(0,[z315,z10,z1,z2,z4,z6]),(0,[z31,z581,z8,z2,z105,z6]),(0,[z8,z1,z4,z5,z60,z751]),(0,[z8,z1322,z2,z4,z5,z6])],[],[(0,[z8,z1,z2,z1323,z5,z6]),(0,[z27,z1,z2,z4,z393,z52]),(0,[z61,z8,z1,z2,z623,z6]),(0,[z8,z1,z4,z5,z6,z744])],[(0,[z553,z28,z2,z4,z5,z6]),(0,[z8,z290,z553,z2,z4,z6]),(0,[z39,z101,z1,z2,z4,z6]),(0,[z8,z1,z65,z5,z6,z225]),(0,[z8,z320,z2,z4,z6,z37]),(0,[z1259,z10,z1,z2,z4,z6])],[(0,[z8,z10,z2,z4,z37,z48]),(0,[z1022,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1324,z6]),(0,[z8,z1325,z1,z2,z4,z6]),(0,[z8,z22,z2,z4,z5,z341])],[(0,[z1,z125,z2,z522,z5,z6]),(0,[z8,z326,z2,z4,z6,z37]),(0,[z39,z8,z2,z4,z173,z6]),(0,[z1095,z22,z2,z4,z5,z6]),(0,[z8,z1,z2,z986,z4,z6])],[(0,[z8,z10,z1,z2,z4,z557]),(0,[z1278,z8,z2,z4,z6,z37])],[(0,[z513,z1,z2,z4,z5,z6]),(0,[z1326,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z1327,z5,z6]),(0,[z122,z1,z2,z4,z5,z6]),(0,[z31,z32,z2,z105,z5,z6]),(0,[z8,z1328,z1,z2,z4,z6]),(0,[z541,z8,z1,z440,z4,z6])],[(0,[z1,z848,z2,z4,z5,z6]),(0,[z152,z8,z137,z4,z5,z144])],[(0,[z0,z326,z2,z4,z30,z6]),(0,[z8,z1,z1329,z4,z5,z6]),(0,[z8,z1330,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z737,z6]),(0,[z42,z1,z2,z4,z6,z37])],[(0,[z8,z141,z2,z4,z5,z6]),(0,[z8,z22,z2,z4,z5,z151]),(0,[z538,z2,z4,z5,z6,z519]),(0,[z8,z96,z2,z4,z6,z90]),(0,[z101,z1,z2,z4,z6,z37]),(0,[z1331,z1,z2,z4,z5,z6]),(0,[z12,z8,z1,z69,z5,z13])],[(0,[z8,z1,z2,z4,z6,z1332]),(0,[z8,z325,z2,z4,z220,z6])],[(0,[z8,z1,z2,z522,z5,z6]),(1,[z8,z1,z870,z5,z6]),(0,[z8,z1,z2,z4,z6,z1333])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 506).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1018).take 410) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1428)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [506, 512, 410] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 158).take 160).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 318).take 160).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 478).take 34).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [158, 160, 160, 34] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38777

theorem PEqualNP.Outside.L_meta_38777 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38777.solve