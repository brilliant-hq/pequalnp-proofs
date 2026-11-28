import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38107

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
  Nat.testBit (4278124266 * 2 ^ 32 + 4276813512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0050000090098310#64 ++ 0x1005000009009831#64 ++ 0xeee88109f09f873b#64 ++ 0xdeee88109f09f873#64 : BitVec 256),
   (0x8120061241240860#64 ++ 0x0812006124124086#64 ++ 0xddd90e36436419ff#64 ++ 0xbddd90e36436419f#64 : BitVec 256),
   (0x0a4030458458a182#64 ++ 0x90a4030458458a18#64 ++ 0xbbbe70c78c78e1c7#64 ++ 0x7bbbe70c78c78e1c#64 : BitVec 256),
   (0x100380a80a80540c#64 ++ 0x2100380a80a80540#64 ++ 0x787f80f80f80fe0e#64 ++ 0xf787f80f80f80fe0#64 : BitVec 256),
   (0x2383db000ff60008#64 ++ 0xc2383db000ff6000#64 ++ 0x07fbff000fff0001#64 ++ 0xf07fbff000fff000#64 : BitVec 256),
   (0x3c03edff6000000f#64 ++ 0x03c03edff6000000#64 ++ 0xfffbfffff0000000#64 ++ 0x0fffbfffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f09f873b 0xdeee88109f09f873

def z1 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffef1cffcffe7ff 0xffffef1cffcffe7f

def z2 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f80fe0e 0xf787f80f80f80fe0

def z3 : W := mkw 0x1a43b0ed8ed8f58e 0xb1a43b0ed8ed8f58 0xfbfff0ff8ff8ffcf 0xffbfff0ff8ff8ffc

def z4 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000fff0001 0xf07fbff000fff000

def z5 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0000000 0x0fffbfffff000000

def z6 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e36436419ff 0xbddd90e36436419f

def z7 : W := mkw 0x0000041240000000 0x0000004124000000 0xddd90e3640000000 0x0ddd90e364000000

def z8 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c78e1c7 0x7bbbe70c78c78e1c

def z9 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff80fe0e 0xfffffffffff80fe0

def z10 : W := mkw 0x100380a80000540c 0x2100380a80000540 0x787f80f80000fe0e 0x0787f80f80000fe0

def z11 : W := mkw 0x0050000090098310 0x1005000009009831 0xe8000009f000873a 0x0e8000009f000873

def z12 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x01137e000f600000 0x201137e000f60000

def z13 : W := mkw 0x3e43fdffe458a18f 0x93e43fdffe458a18 0xfffffffffc78e1c7 0x7fffffffffc78e1c

def z14 : W := mkw 0xbd23efff6124086f 0x0bd23efff6124086 0xfffbfffff36419ff 0xbfffbfffff36419f

def z15 : W := mkw 0x0100020001240000 0x0010002000124000 0x05d90e0003640001 0xb05d90e000364000

def z16 : W := mkw 0xa3a3df124ff60868 0xca3a3df124ff6086 0xdffbff364fff19ff 0xfdffbff364fff19f

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0xccc800004004013b 0x9ccc800004004013

def z18 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87807f07f0000000 0x087807f07f000000

def z19 : W := mkw 0x8020041240000860 0x0802004124000086 0xd8590036430019fe 0xbd8590036430019f

def z20 : W := mkw 0x000000000a805400 0x2000000000a80540 0x000400000f80fe0e 0xf000400000f80fe0

def z21 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07fbff00007f0001 0x007fbff00007f000

def z22 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbfef0cf8cf8e7cf 0xffbfef0cf8cf8e7c

def z23 : W := mkw 0x100000a800005404 0x2100000a80000540 0x200400c80000e600 0x0200400c80000e60

def z24 : W := mkw 0x3f83ffff6ff6540f 0xe3f83ffff6ff6540 0xfffffffffffffe0f 0xffffffffffffffe0

def z25 : W := mkw 0x0010000010010210 0x0001000001001021 0x4440810870870638 0x8444081087087063

def z26 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x111670c60c6060c4 0x2111670c60c6060c

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0x06e8810000000000 0x006e881000000000

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88109f0000000 0x0eee88109f000000

def z29 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x111670c60c78e1c7 0x7111670c60c78e1c

def z30 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffe70c7cc7ce1ff 0xffffe70c7cc7ce1f

def z31 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x06eaf1000c9f0001 0xd06eaf1000c9f000

def z32 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x4041803803801e08 0x84041803803801e0

def z33 : W := mkw 0x8120061241240860 0x0812006124124086 0x85800e06436419ff 0xb85800e06436419f

def z34 : W := mkw 0x81700200912d8b70 0x181700200912d8b7 0xeee88109f3ff9fff 0xfeee88109f3ff9ff

def z35 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xeffbff09ffff0001 0xfeffbff09ffff000

def z36 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x04418f0003870000 0x804418f000387000

def z37 : W := mkw 0x2bc3fb458ffea18a 0xd2bc3fb458ffea18 0xbfffffc78fffe1c7 0xfbfffffc78fffe1c

def z38 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x07fbff0000000000 0x007fbff000000000

def z39 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07807f00007f0001 0x007807f00007f000

def z40 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x07ffff000ffffe0f 0xf07ffff000ffffe0

def z41 : W := mkw 0x0040000080088100 0x1004000008008810 0xaaa8000180188103 0x5aaa800018018810

def z42 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x7ffffff80ffffe0f 0xf7ffffff80ffffe0

def z43 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x202680c80c80e600 0x4202680c80c80e60

def z44 : W := mkw 0x0000000000005400 0x2000000000000540 0x000400000000fe0e 0x0000400000000fe0

def z45 : W := mkw 0x0050000090098310 0x1005000009009831 0x22208109b09b8600 0x422208109b09b860

def z46 : W := mkw 0x000000000a805400 0x2000000000a80540 0x000400000c80e600 0x4000400000c80e60

def z47 : W := mkw 0x0050000090098310 0x1005000009009831 0x06e88100009f873b 0xd06e88100009f873

def z48 : W := mkw 0x9c2024ff60000867 0x09c2024ff6000086 0xf80000fff00019fe 0x0f80000fff00019f

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x383e00c00c00e006 0x7383e00c00c00e00

def z50 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x83807007807801c1 0x083807007807801c

def z51 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffbfffff3801e08 0x8fffbfffff3801e0

def z52 : W := mkw 0x2083c9000a820008 0x42083c9000a82000 0x0000810000830000 0x0000081000083000

def z53 : W := mkw 0x2e407d57e458a183 0x92e407d57e458a18 0xbfbe7fc7fc78e1c7 0x7bfbe7fc7fc78e1c

def z54 : W := mkw 0x024010008458a180 0x9024010008458a18 0x000400000c78e1c7 0x7000400000c78e1c

def z55 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbba70c780000000 0x0bbba70c78000000

def z56 : W := mkw 0x2383df124ff60008 0xc2383df124ff6000 0xdffbff364fff0001 0xfdffbff364fff000

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x686880080080860a 0xd686880080080860

def z58 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0xfeff81f9ff9fff3f 0xffeff81f9ff9fff3

def z59 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x787f80f80c00e006 0x7787f80f80c00e00

def z60 : W := mkw 0x138392a80ff6540c 0xe138392a80ff6540 0x787f80f80ffffe0f 0xf787f80f80ffffe0

def z61 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x101700f00f007804 0x2101700f00f00780

def z62 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x303780f80f80fe04 0x6303780f80f80fe0

def z63 : W := mkw 0x2bc07b45857ea182 0xd2bc07b45857ea18 0xbfbe7fc78c7fe1c7 0x7bfbe7fc78c7fe1c

def z64 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0xeee98f39f0000000 0x0eee98f39f000000

def z65 : W := mkw 0x8120061241240860 0x0812006124124086 0x44410e3043041838 0x844410e304304183

def z66 : W := mkw 0x9d2026ff61240867 0x09d2026ff6124086 0xfdd90efff36419ff 0xbfdd90efff36419f

def z67 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x6869803803809e0a 0xd6869803803809e0

def z68 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x17fbfff600000000 0x017fbfff60000000

def z69 : W := mkw 0x8b603657c57ca9e2 0x98b603657c57ca9e 0xbbbf7ef78f78f9c7 0x7bbbf7ef78f78f9c

def z70 : W := mkw 0x2203d90004500008 0x82203d9000450000 0x07fbff000c780001 0x707fbff000c78000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x4440810870000000 0x0444081087000000

def z72 : W := mkw 0x0050000090098310 0x1005000009009831 0x00000000009f873b 0xd00000000009f873

def z73 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x3333ffffb0000000 0x03333ffffb000000

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x0440810000870000 0x8044081000087000

def z75 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0xfff98f3ff3ff9fff 0xffff98f3ff3ff9ff

def z76 : W := mkw 0x8120061241240860 0x0812006124124086 0x5c590e304304183e 0xb5c590e304304183

def z77 : W := mkw 0x024010008458a180 0x9024010008458a18 0x383e00c00c78e1c7 0x7383e00c00c78e1c

def z78 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x027bf1000f9b0000 0xf027bf1000f9b000

def z79 : W := mkw 0x912382a80ba45c6c 0x2912382a80ba45c6 0x787f80f80fe4ffff 0xf787f80f80fe4fff

def z80 : W := mkw 0x3e43fdffe458a18f 0x93e43fdffe458a18 0xfffffffffc18e000 0x4fffffffffc18e00

def z81 : W := mkw 0x1c5024fff0098317 0x11c5024fff009831 0xf80000fff000873a 0x0f80000fff000873

def z82 : W := mkw 0x3c53edfff009831f 0x13c53edfff009831 0xfffbfffff09f873b 0xdfffbfffff09f873

def z83 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0xf80000fff0000000 0x0f80000fff000000

def z84 : W := mkw 0x0050000090098310 0x1005000009009831 0x86800101f01f0131 0x086800101f01f013

def z85 : W := mkw 0x0240100084588100 0x9024010008458810 0xabba70018c788103 0x7abba70018c78810

def z86 : W := mkw 0x8120061241240860 0x0812006124124086 0xdc410e36430419fe 0x8dc410e36430419f

def z87 : W := mkw 0x0010000010010210 0x0001000001001021 0x0400010070070030 0x0040001007007003

def z88 : W := mkw 0x2000490000000000 0x0200049000000000 0x07807f0000000000 0x007807f000000000

def z89 : W := mkw 0x0050000090098310 0x1005000009009831 0xcec80101f01f013b 0x9cec80101f01f013

def z90 : W := mkw 0x8120020001240860 0x0812002000124086 0x00000000036419ff 0xb00000000036419f

def z91 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x97937ff7f0000000 0x097937ff7f000000

def z92 : W := mkw 0x8120061241240860 0x0812006124124086 0x11110e36036018c4 0x211110e36036018c

def z93 : W := mkw 0x3f83ffff6ff6000f 0xc3f83ffff6ff6000 0xfffbffffffff0001 0xffffbffffffff000

def z94 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0x7c7b8ff870000000 0x07c7b8ff87000000

def z95 : W := mkw 0x8b203657457428e2 0x88b203657457428e 0x11177ef60f6078c4 0x211177ef60f6078c

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x11100006006000c4 0x211100006006000c

def z97 : W := mkw 0x23d3db009fff8318 0xd23d3db009fff831 0xeffbff09ffff873b 0xfeffbff09ffff873

def z98 : W := mkw 0x1803a0ed0000000e 0x01803a0ed0000000 0xfbfbf0ff80000000 0x0fbfbf0ff8000000

def z99 : W := mkw 0x100000a800005404 0x2100000a80000540 0x780400f80000fe0e 0x0780400f80000fe0

def z100 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0x87fbff07f0000000 0x087fbff07f000000

def z101 : W := mkw 0x21804b0001260000 0x421804b000126000 0x04000f0000070000 0x004000f000007000

def z102 : W := mkw 0x0bc032458ffea182 0xd0bc032458ffea18 0xbbbe70c78fffe1c7 0xfbbbe70c78fffe1c

def z103 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x17fffff00fff7805 0xf17fffff00fff780

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x99980006006001c7 0x399980006006001c

def z105 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x606780f80f80fe08 0xc606780f80f80fe0

def z106 : W := mkw 0x0040000080088100 0x1004000008008810 0x8280000180180101 0x0828000018018010

def z107 : W := mkw 0x3e53fdfff459a39f 0x93e53fdfff459a39 0xfffffffffcffe7ff 0xffffffffffcffe7f

def z108 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x2222f1c9b0000000 0x02222f1c9b000000

def z109 : W := mkw 0x0050000090098310 0x1005000009009831 0x66608109f09f8638 0xc66608109f09f863

def z110 : W := mkw 0xbfa3ffff6ff6086f 0xcbfa3ffff6ff6086 0xfffbffffffff19ff 0xffffbffffffff19f

def z111 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0x000000000fff0001 0xf000000000fff000

def z112 : W := mkw 0x0050000090098310 0x1005000009009831 0xfefe81c9fc9fe73f 0xffefe81c9fc9fe73

def z113 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x787b80f800000000 0x0787b80f80000000

def z114 : W := mkw 0x0050000090098310 0x1005000009009831 0x68688008009f873b 0xd68688008009f873

def z115 : W := mkw 0x8b603657c57ca9e2 0x98b603657c57ca9e 0xdfd97e37c37c19ff 0xbdfd97e37c37c19f

def z116 : W := mkw 0x038392000ff60008 0xc038392000ff6000 0x007b80000fff0001 0xf007b80000fff000

def z117 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x939670c78c7861c5 0x2939670c78c7861c

def z118 : W := mkw 0xa3a05f1245760860 0xca3a05f124576086 0xdfd97f36437f19ff 0xbdfd97f36437f19f

def z119 : W := mkw 0x8120061241240860 0x0812006124124086 0x11110e36036419ff 0xb11110e36036419f

def z120 : W := mkw 0x912386ba4124086c 0x0912386ba4124086 0xfdfb8efe436419ff 0xbfdfb8efe436419f

def z121 : W := mkw 0x3e43fdffeed8f58f 0xb3e43fdffeed8f58 0xfffffffffff8ffcf 0xffffffffffff8ffc

def z122 : W := mkw 0x018002000ba60000 0x4018002000ba6000 0x0000000003870000 0x8000000000387000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0xddd80006406401ff 0xbddd80006406401f

def z124 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x47fbff380fff1e09 0xf47fbff380fff1e0

def z125 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x83ba70078c7801c1 0x783ba70078c7801c

def z126 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0x44418f3870000000 0x044418f387000000

def z127 : W := mkw 0x23d3db009fff8318 0xd23d3db009fff831 0x07fbff000fff873b 0xf07fbff000fff873

def z128 : W := mkw 0x000380000a800008 0x0000380000a80000 0x007b80000f800000 0xf007b80000f80000

def z129 : W := mkw 0x024010008ed8f580 0xb024010008ed8f58 0x000400000ff8ffcf 0xf000400000ff8ffc

def z130 : W := mkw 0x8920265741240862 0x0892026574124086 0xfffb7ef7c36419ff 0xbfffb7ef7c36419f

def z131 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfeff81f9ff80fe0e 0xffeff81f9ff80fe0

def z132 : W := mkw 0x8120061241240860 0x0812006124124086 0xd9110e36436019fe 0x2d9110e36436019f

def z133 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbffffff800000 0xffffbffffff80000

def z134 : W := mkw 0x3283d9a80ed2540c 0xe3283d9a80ed2540 0x2226f1c80c9be600 0x42226f1c80c9be60

def z135 : W := mkw 0x8120061241240860 0x0812006124124086 0x85800e06406401f1 0x085800e06406401f

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0x06e88100009f0001 0xd06e88100009f000

def z137 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbffef1c78cffe1c7 0xfbffef1c78cffe1c

def z138 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbff70f78f78f9cf 0xffbff70f78f78f9c

def z139 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0x7a7f81f9bf9bfe0e 0xf7a7f81f9bf9bfe0

def z140 : W := mkw 0x100000a800005404 0x2100000a80000540 0x100400f000007804 0x0100400f00000780

def z141 : W := mkw 0x120390a80ed0540c 0xa120390a80ed0540 0x7bfff0f80ff8fe0f 0xf7bfff0f80ff8fe0

def z142 : W := mkw 0x8120020001240860 0x0812002000124086 0x58590030036419ff 0xb58590030036419f

def z143 : W := mkw 0x01500200912d8310 0x101500200912d831 0xeff98f09f3ff873b 0xfeff98f09f3ff873

def z144 : W := mkw 0x124390a88ed8f58c 0xb124390a88ed8f58 0x787f80f80ff8ffcf 0xf787f80f80ff8ffc

def z145 : W := mkw 0x2bd3fb459fffa39a 0xd2bd3fb459fffa39 0xffffffcfffffe7ff 0xfffffffcfffffe7f

def z146 : W := mkw 0x8120061241240860 0x0812006124124086 0x95910e36436419f5 0x295910e36436419f

def z147 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xefe8ff0ff0000000 0x0efe8ff0ff000000

def z148 : W := mkw 0x2003c90000000008 0x02003c9000000000 0xeffbff09f0000000 0x0effbff09f000000

def z149 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xf9ff80fe0fe0ffcf 0xff9ff80fe0fe0ffc

def z150 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x13be70c60c7860c5 0x713be70c60c7860c

def z151 : W := mkw 0xbd23efff6124086f 0x0bd23efff6124086 0xdddb7ef6436419ff 0xbdddb7ef6436419f

def z152 : W := mkw 0x3183cba80ba6540c 0x63183cba80ba6540 0x7c7f8ff80f87fe0e 0xf7c7f8ff80f87fe0

def z153 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x222670c18c18e000 0x4222670c18c18e00

def z154 : W := mkw 0x0200100004500000 0x8020010000450000 0x3bbe70c00c78e007 0x73bbe70c00c78e00

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80000004000013a 0x0c80000004000013

def z156 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x797ffefe0f80fe0e 0xf797ffefe0f80fe0

def z157 : W := mkw 0xa3a3df124ff60868 0xca3a3df124ff6086 0x17fbff360fff18c5 0xf17fbff360fff18c

def z158 : W := mkw 0x0000041240000000 0x0000004124000000 0x85800e0640000000 0x085800e064000000

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0x585900300300180e 0xb585900300300180

def z160 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07a2ff000cff0001 0x407a2ff000cff000

def z161 : W := mkw 0x8b603657c57ca9e2 0x98b603657c57ca9e 0xffff7ef7cf7cf9ff 0xfffff7ef7cf7cf9f

def z162 : W := mkw 0xbd23efff6ba45c6f 0x2bd23efff6ba45c6 0xffffffffffe4ffff 0xfffffffffffe4fff

def z163 : W := mkw 0x2c506d57f0098313 0x12c506d57f009831 0xefe8ff0ff09f873b 0xdefe8ff0ff09f873

def z164 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x05d98f0003e70001 0xb05d98f0003e7000

def z165 : W := mkw 0x2bc07b45857ea182 0xd2bc07b45857ea18 0x87807f07807f01c1 0x087807f07807f01c

def z166 : W := mkw 0x8020041240000860 0x0802004124000086 0xd8000036400019fe 0x0d8000036400019f

def z167 : W := mkw 0xa1a3cf124ba60868 0x4a1a3cf124ba6086 0x44418f3043871838 0x844418f304387183

def z168 : W := mkw 0x0250100094598310 0x9025010009459831 0xeffaf109fcff873b 0xfeffaf109fcff873

def z169 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0xddd90e3643ff9fff 0xfddd90e3643ff9ff

def z170 : W := mkw 0x0040000080088100 0x1004000008008810 0xbbb80007807881c7 0x7bbb80007807881c

def z171 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbef1cfbcfbe7c7 0x7bbbef1cfbcfbe7c

def z172 : W := mkw 0x89602657c12ca9e2 0x189602657c12ca9e 0xfddd0ef7c364f9ff 0xbfddd0ef7c364f9f

def z173 : W := mkw 0x0050000090098310 0x1005000009009831 0xecc80009f004873b 0x9ecc80009f004873

def z174 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfcff80f84f84ff3f 0xffcff80f84f84ff3

def z175 : W := mkw 0x000380000a800008 0x0000380000a80000 0x06fb81000f9f0001 0xf06fb81000f9f000

def z176 : W := mkw 0x3e83f9ed2ed2000f 0xc3e83f9ed2ed2000 0x2222f1c9bc9b0000 0x42222f1c9bc9b000

def z177 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff004013b 0x9fffbfffff004013

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88109f004013b 0x9eee88109f004013

def z179 : W := mkw 0x03d012009fff8310 0xd03d012009fff831 0x000000000fff873b 0xf000000000fff873

def z180 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0x787f80f80f9fff3f 0xf787f80f80f9fff3

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x4041003003001808 0x8404100300300180

def z182 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0xfdff8efe4fe4ffff 0xffdff8efe4fe4fff

def z183 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbbe70c78c00e006 0x7bbbe70c78c00e00

def z184 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0222f1000fff0001 0xf0222f1000fff000

def z185 : W := mkw 0x0010000010010210 0x0001000001001021 0x46e88108709f0639 0xd46e88108709f063

def z186 : W := mkw 0x100000a80a805404 0x2100000a80a80540 0x780400f80f80fe0e 0xf780400f80f80fe0

def z187 : W := mkw 0x3c13edff7001021f 0x03c13edff7001021 0xfffbfffff0870638 0x8fffbfffff087063

def z188 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000f600000 0x207fbff000f60000

def z189 : W := mkw 0x03d012009fff8310 0xd03d012009fff831 0xeee88109ffff873b 0xfeee88109ffff873

def z190 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x27fbffc9b0000000 0x027fbffc9b000000

def z191 : W := mkw 0x000380000a800008 0x0000380000a80000 0x687b80080f80860a 0xf687b80080f80860

def z192 : W := mkw 0x0040000080088100 0x1004000008008810 0xeee80001c01c813b 0xdeee80001c01c813

def z193 : W := mkw 0x3283d9a80ed2540c 0xe3283d9a80ed2540 0x7a7ff1f80f9bfe0e 0xf7a7ff1f80f9bfe0

def z194 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x0222f1000c9b0000 0x40222f1000c9b000

def z195 : W := mkw 0x8120061241240860 0x0812006124124086 0xc5c10e36436419f9 0x8c5c10e36436419f

def z196 : W := mkw 0x0200100004500000 0x8020010000450000 0x03ba70000c780001 0x703ba70000c78000

def z197 : W := mkw 0x1c0024ff60005407 0x21c0024ff6000540 0xf80400fff000fe0e 0x0f80400fff000fe0

def z198 : W := mkw 0x0050000090098310 0x1005000009009831 0x86e88101f09f0131 0xd86e88101f09f013

def z199 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x3fffffc00fffe007 0xf3fffffc00fffe00

def z200 : W := mkw 0xabe3ff57cffea9ea 0xdabe3ff57cffea9e 0xfffffff7cffff9ff 0xffffffff7cffff9f

def z201 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff00019fe 0x0fffbfffff00019f

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x8480000040040131 0x0848000004004013

def z203 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x11137ef600000000 0x011137ef60000000

def z204 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x11177ef60f007804 0x211177ef60f00780

def z205 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbba70c7807801c1 0x0bbba70c7807801c

def z206 : W := mkw 0x0800204500000002 0x0080020450000000 0xfffaf1cff0000000 0x0fffaf1cff000000

def z207 : W := mkw 0x2bc3fb458ffea18a 0xd2bc3fb458ffea18 0x87fbff078fff01c1 0xf87fbff078fff01c

def z208 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x01007e0000600000 0x001007e000060000

def z209 : W := mkw 0x8120061241240860 0x0812006124124086 0xdff98f3643ff19ff 0xfdff98f3643ff19f

def z210 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff06001c7 0x3fffbfffff06001c

def z211 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e36406401f1 0x0ddd90e36406401f

def z212 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x781700f80f00fe0e 0x2781700f80f00fe0

def z213 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0xfee881fff0000000 0x0fee881fff000000

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x383a00c000000000 0x0383a00c00000000

def z215 : W := mkw 0x8120061241240860 0x0812006124124086 0xfff98f3ff36419ff 0xbfff98f3ff36419f

def z216 : W := mkw 0x0050000090098310 0x1005000009009831 0xe8688009f080873a 0xde8688009f080873

def z217 : W := mkw 0x084020458008a182 0x1084020458008a18 0xb80400c78000e1c6 0x0b80400c78000e1c

def z218 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x202280c800000000 0x0202280c80000000

def z219 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e36436018c4 0x2ddd90e36436018c

def z220 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x4041803800000000 0x0404180380000000

def z221 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x6663fff9f0000000 0x06663fff9f000000

def z222 : W := mkw 0x8120061241240860 0x0812006124124086 0x00010e3003001800 0x000010e300300180

def z223 : W := mkw 0x23d05b00957f8310 0xd23d05b00957f831 0xefe8ff09f0ff873b 0xdefe8ff09f0ff873

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x6868800800000000 0x0686880080000000

def z225 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdff0ef64f64f9ff 0xffdff0ef64f64f9f

def z226 : W := mkw 0xa1a3cf124ba60868 0x4a1a3cf124ba6086 0xddd98f3643e719ff 0xbddd98f3643e719f

def z227 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff080860a 0xdfffbfffff080860

def z228 : W := mkw 0x8020041240000860 0x0802004124000086 0x80000006400001f0 0x080000006400001f

def z229 : W := mkw 0x2b83fb450ff6208a 0xc2b83fb450ff6208 0x17ffffc60fff60c5 0xf17ffffc60fff60c

def z230 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xcffbff004fff013b 0xfcffbff004fff013

def z231 : W := mkw 0x3e03fdff6450208f 0x83e03fdff6450208 0xfffffffffc6060c4 0x2fffffffffc6060c

def z232 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7eff81f80f9ffe0f 0xf7eff81f80f9ffe0

def z233 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x782680f80c80fe0e 0x4782680f80c80fe0

def z234 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x01137e000fff0001 0xf01137e000fff000

def z235 : W := mkw 0x3413cdba7001021d 0x03413cdba7001021 0x44418f3870870638 0x844418f387087063

def z236 : W := mkw 0x3003c9a80000000c 0x03003c9a80000000 0x7ffbfff800000000 0x07ffbfff80000000

def z237 : W := mkw 0x0050000090098310 0x1005000009009831 0xc6c08109f09f0739 0x8c6c08109f09f073

def z238 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07ba7f000c7f0001 0x707ba7f000c7f000

def z239 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0xfbba70fff0000000 0x0fbba70fff000000

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0x101600c00c006004 0x2101600c00c00600

def z241 : W := mkw 0x0050000090098310 0x1005000009009831 0xfff8810ff0ff87ff 0xffff8810ff0ff87f

def z242 : W := mkw 0x8120061241240860 0x0812006124124086 0x9d980e06406401f7 0x39d980e06406401f

def z243 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xbfba7fc7f0000000 0x0bfba7fc7f000000

def z244 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x797bfefe00000000 0x0797bfefe0000000

def z245 : W := mkw 0x2193cb001ba70218 0x42193cb001ba7021 0x44418f0873870638 0x844418f087387063

def z246 : W := mkw 0x83a012000ff60860 0xc83a012000ff6086 0x000000000fff19ff 0xf000000000fff19f

def z247 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfbbe70cffc78e7ff 0x7fbbe70cffc78e7f

def z248 : W := mkw 0x8120061241240860 0x0812006124124086 0x04000e0040040030 0x004000e004004003

def z249 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07d97f00037f0001 0xb07d97f00037f000

def z250 : W := mkw 0x0200100004500000 0x8020010000450000 0x07faf1000cff0001 0xf07faf1000cff000

def z251 : W := mkw 0x000380000a800008 0x0000380000a80000 0x0041800003800000 0x8004180000380000

def z252 : W := mkw 0xbd23efff6124086f 0x0bd23efff6124086 0xfffbfffff3041838 0x8fffbfffff304183

def z253 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x3a3e70c18c18e006 0x73a3e70c18c18e00

def z254 : W := mkw 0x101380a81a81561c 0x2101380a81a81561 0x7c7f81f87f87fe3e 0xf7c7f81f87f87fe3

def z255 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0x100000f600000000 0x0100000f60000000

def z256 : W := mkw 0xa3a05f1245760860 0xca3a05f124576086 0x87807f06407f01f1 0x087807f06407f01f

def z257 : W := mkw 0x8120061241240860 0x0812006124124086 0xccc90e304304193b 0x9ccc90e304304193

def z258 : W := mkw 0x0300120005740000 0x8030012000574000 0x07fb7e000f7c0001 0xf07fb7e000f7c000

def z259 : W := mkw 0x084020458008a182 0x1084020458008a18 0x80000007800001c0 0x080000007800001c

def z260 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0xfdd90efff0000000 0x0fdd90efff000000

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z262 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xc7c1ff3ff0000000 0x0c7c1ff3ff000000

def z263 : W := mkw 0x88602457c008a9e2 0x188602457c008a9e 0xf80400f7c000f9fe 0x0f80400f7c000f9f

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0x484800000000000a 0x9484800000000000

def z265 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07e8ff0000ff0001 0xd07e8ff0000ff000

def z266 : W := mkw 0x03c012008ffea180 0xd03c012008ffea18 0x000400000fffe1c7 0xf000400000fffe1c

def z267 : W := mkw 0x3bc3fbed8ffef58e 0xf3bc3fbed8ffef58 0xffffffff8fffffcf 0xfffffffff8fffffc

def z268 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x7a7bf1f9b0000000 0x07a7bf1f9b000000

def z269 : W := mkw 0x0100020001240000 0x0010002000124000 0x5dd90e300364180f 0xb5dd90e300364180

def z270 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xbbbe70c78c6060c4 0x2bbbe70c78c6060c

def z271 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xeeeef1c9fc9fe73b 0xdeeeef1c9fc9fe73

def z272 : W := mkw 0x23d3db009fff8318 0xd23d3db009fff831 0x87fbff01ffff0131 0xf87fbff01ffff013

def z273 : W := mkw 0x038012000ff65400 0xe038012000ff6540 0x000400000ffffe0f 0xf000400000ffffe0

def z274 : W := mkw 0x0a00304504500002 0x80a0030450450000 0xbbba70c78c780001 0x7bbba70c78c78000

def z275 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f09b8600 0x4eee88109f09b860

def z276 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xb91670c78c60e1c6 0x2b91670c78c60e1c

def z277 : W := mkw 0x1c4024ffe008a187 0x11c4024ffe008a18 0xf80400fff000e1c6 0x0f80400fff000e1c

def z278 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c18e000 0x4bbbe70c78c18e00

def z279 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x5553fffe70000000 0x05553fffe7000000

def z280 : W := mkw 0x0040000080088100 0x1004000008008810 0xbabe00c18c18e107 0x7babe00c18c18e10

def z281 : W := mkw 0x3fd3ffffffff831f 0xd3fd3ffffffff831 0xfffbffffffff873b 0xffffbffffffff873

def z282 : W := mkw 0x000000000a805400 0x2000000000a80540 0x0000000003801e08 0x80000000003801e0

def z283 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x9b987007807801c7 0x39b987007807801c

def z284 : W := mkw 0x1c03a4ff6a80540f 0x21c03a4ff6a80540 0xf87f80ffff80fe0e 0xff87f80ffff80fe0

def z285 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f007804 0x2787f80f80f00780

def z286 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x07fbff000c9b0000 0x407fbff000c9b000

def z287 : W := mkw 0x140004ba60000005 0x0140004ba6000000 0x4000003870000000 0x0400000387000000

def z288 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0x2226f1c9bc9be600 0x42226f1c9bc9be60

def z289 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x6ffbff080fff860b 0xf6ffbff080fff860

def z290 : W := mkw 0x028010000ed20000 0xc028010000ed2000 0x000000000c9b0000 0x4000000000c9b000

def z291 : W := mkw 0x184020ed8008f586 0x3184020ed8008f58 0xf80400ff8000ffce 0x0f80400ff8000ffc

def z292 : W := mkw 0x0003800000000008 0x0000380000000000 0x007b800000000000 0x0007b80000000000

def z293 : W := mkw 0x0050000090098310 0x1005000009009831 0x000000000000873a 0x0000000000000873

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ee88108009f860b 0xd6ee88108009f860

def z295 : W := mkw 0x0050000090098310 0x1005000009009831 0xea208109f09b873a 0x4ea208109f09b873

def z296 : W := mkw 0x1a53b0ed9ed9f79e 0xb1a53b0ed9ed9f79 0xfffff1ffffffffff 0xffffff1fffffffff

def z297 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x06e98f00039f0001 0xd06e98f00039f000

def z298 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x383e80c80c80e606 0x7383e80c80c80e60

def z299 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x5ffbff300fff180f 0xf5ffbff300fff180

def z300 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x04418f000fff0001 0xf04418f000fff000

def z301 : W := mkw 0x000380000a800008 0x0000380000a80000 0x002280000c800000 0x4002280000c80000

def z302 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x11177ef00f607804 0x211177ef00f60780

def z303 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07937f000f7f0001 0x207937f000f7f000

def z304 : W := mkw 0x0040000080088100 0x1004000008008810 0xeee88109f0188103 0x5eee88109f018810

def z305 : W := mkw 0x3003c9a80a80540c 0x23003c9a80a80540 0x7ffffff80f80fe0e 0xf7ffffff80f80fe0

def z306 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xbbbb7ef780000000 0x0bbbb7ef78000000

def z307 : W := mkw 0x8120061241240860 0x0812006124124086 0x99990e36036019c7 0x399990e36036019c

def z308 : W := mkw 0x0040000080088100 0x1004000008008810 0xaee88101809f8103 0xdaee88101809f810

def z309 : W := mkw 0x005000009a89d710 0x3005000009a89d71 0x000400000f9fff3f 0xf000400000f9fff3

def z310 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbfbe71c7fc7fe1f7 0x7bfbe71c7fc7fe1f

def z311 : W := mkw 0xad206f5761240863 0x0ad206f576124086 0xdfd97f37f36419ff 0xbdfd97f37f36419f

def z312 : W := mkw 0xbd23efff6124086f 0x0bd23efff6124086 0x11137ef6036018c4 0x211137ef6036018c

def z313 : W := mkw 0x3c53e9edb009831f 0x13c53e9edb009831 0x2222f1c9b09b8600 0x42222f1c9b09b860

def z314 : W := mkw 0x1a43b0ed8ed8f58e 0xb1a43b0ed8ed8f58 0x2226f0c98c98e600 0x42226f0c98c98e60

def z315 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffffffffc80e600 0x4fffffffffc80e60

def z316 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xff807ffff0000000 0x0ff807ffff000000

def z317 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x333670c78c78e0c4 0x6333670c78c78e0c

def z318 : W := mkw 0x0050000090098310 0x1005000009009831 0xaea80101f01f8133 0x5aea80101f01f813

def z319 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x23be70c18c78e001 0x723be70c18c78e00

def z320 : W := mkw 0x005000009a89d710 0x3005000009a89d71 0xeeec8109ff9fff3f 0xfeeec8109ff9fff3

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x787e80c80c80e60e 0xf787e80c80c80e60

def z322 : W := mkw 0x0100061241240000 0x0010006124124000 0xddd90e3643640001 0xbddd90e364364000

def z323 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x000670c00c006000 0x0000670c00c00600

def z324 : W := mkw 0x3c53edfffa89d71f 0x33c53edfffa89d71 0xffffffffff9fff3f 0xfffffffffff9fff3

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0xd9d90036036019cf 0xbd9d90036036019c

def z326 : W := mkw 0x2c506d57f0098313 0x12c506d57f009831 0x87807f07f01f0131 0x087807f07f01f013

def z327 : W := mkw 0x004000008008a180 0x1004000008008a18 0x000400000000e1c6 0x0000400000000e1c

def z328 : W := mkw 0x917386badbaddf7c 0x3917386badbaddf7 0xffff8fffffffffff 0xfffff8ffffffffff

def z329 : W := mkw 0x23d05b00957f8310 0xd23d05b00957f831 0x87807f01f07f0131 0x087807f01f07f013

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x000400000c00e006 0x7000400000c00e00

def z331 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffffffffc00e006 0x7fffffffffc00e00

def z332 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x01007006006000c0 0x001007006006000c

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0x7879803803809e0e 0xf7879803803809e0

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x787f00f00f00f80e 0xf787f00f00f00f80

def z335 : W := mkw 0x33d3dba89fffd71c 0xf33d3dba89fffd71 0xfffffff9ffffff3f 0xffffffff9ffffff3

def z336 : W := mkw 0xa3a3df124ff60868 0xca3a3df124ff6086 0x47fbff304fff1839 0xf47fbff304fff183

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x0068800000800000 0xd006880000080000

def z338 : W := mkw 0x0800245740000002 0x0080024574000000 0xfffb7ef7c0000000 0x0fffb7ef7c000000

def z339 : W := mkw 0x8020041240000860 0x0802004124000086 0x10000036000018c4 0x010000036000018c

def z340 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0xbbbaf1cfb0000000 0x0bbbaf1cfb000000

def z341 : W := mkw 0x8b603657c57ca9e2 0x98b603657c57ca9e 0x87807e07c07c01f1 0x087807e07c07c01f

def z342 : W := mkw 0x2bc3fb458ffea18a 0xd2bc3fb458ffea18 0x27ffffc18fffe001 0xf27ffffc18fffe00

def z343 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffffffff000fe0e 0x0fffffffff000fe0

def z344 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x7ffbfff80fff0001 0xf7ffbfff80fff000

def z345 : W := mkw 0x22d3d9009edb8318 0xd22d3d9009edb831 0xeeeaf109fc9f873b 0xdeeeaf109fc9f873

def z346 : W := mkw 0x3403cdba6a80540d 0x23403cdba6a80540 0x44418f3873801e08 0x844418f3873801e0

def z347 : W := mkw 0x0a4030458ed8f582 0xb0a4030458ed8f58 0xbbbe70c78ff8ffcf 0xfbbbe70c78ff8ffc

def z348 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0x07fbff000fff19ff 0xf07fbff000fff19f

def z349 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0xf87f80f9ff80ff3e 0xff87f80f9ff80ff3

def z350 : W := mkw 0x2b83fb450ff6000a 0xc2b83fb450ff6000 0xbffbffc78fff0001 0xfbffbffc78fff000

def z351 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x784580f80380fe0e 0x8784580f80380fe0

def z352 : W := mkw 0x3453cdbaf009831d 0x13453cdbaf009831 0xeee98f39f09f873b 0xdeee98f39f09f873

def z353 : W := mkw 0x0050000090098310 0x1005000009009831 0xee800109f01f873b 0x0ee800109f01f873

def z354 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0xeee98139f39f9f3b 0xdeee98139f39f9f3

def z355 : W := mkw 0x3783dfba6ff6000d 0xc3783dfba6ff6000 0x47fbff387fff0001 0xf47fbff387fff000

def z356 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x407b80380f801e08 0xf407b80380f801e0

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x5859003000000000 0x0585900300000000

def z358 : W := mkw 0x100384ba4a80540c 0x2100384ba4a80540 0xfdff8efe4f80fe0e 0xffdff8efe4f80fe0

def z359 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x383f00f00f00f806 0x7383f00f00f00f80

def z360 : W := mkw 0x100380a80000000c 0x0100380a80000000 0xfefb81f9f0000000 0x0fefb81f9f000000

def z361 : W := mkw 0x0000041240000000 0x0000004124000000 0x44410e3040000000 0x044410e304000000

def z362 : W := mkw 0x0100020001240000 0x0010002000124000 0x0000000003640001 0xb000000000364000

def z363 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x5859803803801e0e 0xb5859803803801e0

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x580000300000180e 0x0580000300000180

def z365 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x047b8f000f870000 0xf047b8f000f87000

def z366 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x07fbff00009f0001 0xd07fbff00009f000

def z367 : W := mkw 0x0100020001240000 0x0010002000124000 0x04410e0003040000 0x804410e000304000

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000006001c7 0x300000000006001c

def z369 : W := mkw 0x8b603657c57ca9e2 0x98b603657c57ca9e 0xbfbe7ec7cc7ce1f7 0x7bfbe7ec7cc7ce1f

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x4040800800800608 0x8404080080080060

def z371 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0333ff000ffb0000 0x60333ff000ffb000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88109f080860a 0xdeee88109f080860

def z373 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x0001003003001800 0x0000100300300180

def z374 : W := mkw 0x0800204500000002 0x0080020450000000 0x222270c180000000 0x0222270c18000000

def z375 : W := mkw 0x000380000a800008 0x0000380000a80000 0x001300000f000000 0x2001300000f00000

def z376 : W := mkw 0xbd23efff6124086f 0x0bd23efff6124086 0xfffbfffff36018c4 0x2fffbfffff36018c

def z377 : W := mkw 0x0100020001240000 0x0010002000124000 0x05800e0000640001 0x005800e000064000

def z378 : W := mkw 0x2103cb0001240008 0x02103cb000124000 0x07fbff0003640001 0xb07fbff000364000

def z379 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef1cffc78e1c7 0x7fffef1cffc78e1c

def z380 : W := mkw 0x3c53edfff009831f 0x13c53edfff009831 0xfffbfffff01f0131 0x0fffbfffff01f013

def z381 : W := mkw 0x0010000010010210 0x0001000001001021 0x4000000870000638 0x0400000087000063

def z382 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0663ff000f9f0000 0xc0663ff000f9f000

def z383 : W := mkw 0x0010000010010210 0x0001000001001021 0x0000000000870638 0x8000000000087063

def z384 : W := mkw 0x0000041240000000 0x0000004124000000 0x11110e3600000000 0x011110e360000000

def z385 : W := mkw 0x0800204500000002 0x0080020450000000 0xb80000c780000000 0x0b80000c78000000

def z386 : W := mkw 0x8120020001240860 0x0812002000124086 0x00000000006401f1 0x000000000006401f

def z387 : W := mkw 0x0800204500002082 0x0080020450000208 0x100400c6000060c4 0x0100400c6000060c

def z388 : W := mkw 0x83a016124ff60860 0xc83a016124ff6086 0xddd90e364fff19ff 0xfddd90e364fff19f

def z389 : W := mkw 0x0000041240000000 0x0000004124000000 0xd800003640000000 0x0d80000364000000

def z390 : W := mkw 0x8b603245857ca9e2 0x98b603245857ca9e 0xbbbe70c78f7cf9ff 0xfbbbe70c78f7cf9f

def z391 : W := mkw 0x0050000090098310 0x1005000009009831 0x80000001f0000130 0x080000001f000013

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x04c8000000040001 0x904c800000004000

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88109f09f0001 0xdeee88109f09f000

def z394 : W := mkw 0x3e03fdff6450208f 0x83e03fdff6450208 0x11177ef60c6060c4 0x211177ef60c6060c

def z395 : W := mkw 0x3c03e9ed2a80540f 0x23c03e9ed2a80540 0x2226f1c9bc80e600 0x42226f1c9bc80e60

def z396 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x0222f10000000000 0x00222f1000000000

def z397 : W := mkw 0x3f83fbed2ff6000f 0xc3f83fbed2ff6000 0x27fbffc9bfff0001 0xf27fbffc9bfff000

def z398 : W := mkw 0x8120061241240860 0x0812006124124086 0x55510e36436418fc 0xa55510e36436418f

def z399 : W := mkw 0x110382a80ba4540c 0x2110382a80ba4540 0x7dff8ef80fe4fe0f 0xf7dff8ef80fe4fe0

def z400 : W := mkw 0x0050000090098310 0x1005000009009831 0x00000000001f0131 0x000000000001f013

def z401 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x0000800800800600 0x0000080080080060

def z402 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x00010e0003000000 0x000010e000300000

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x0059000003000000 0xb005900000300000

def z404 : W := mkw 0x2003c9000a800008 0x02003c9000a80000 0x07fbff000f800000 0xf07fbff000f80000

def z405 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x207f80c80f80e600 0xf207f80c80f80e60

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000004013b 0x9000000000004013

def z407 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe70c78cffe7ff 0xfbbbe70c78cffe7f

def z408 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0x87807107f07f01f1 0x087807107f07f01f

def z409 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e3643041838 0x8ddd90e364304183

def z410 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff300180e 0xbfffbfffff300180

def z411 : W := mkw 0x8020000000000860 0x0802000000000086 0x00000000000019fe 0x000000000000019f

def z412 : W := mkw 0x0c00245760000003 0x00c0024576000000 0x80000007f0000000 0x080000007f000000

def z413 : W := mkw 0x812006124ba45c60 0x2812006124ba45c6 0xdddd0e364fe4ffff 0xfdddd0e364fe4fff

def z414 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x101700f00f80fe0e 0xf101700f00f80fe0

def z415 : W := mkw 0x000000000a800000 0x0000000000a80000 0x000000000f800000 0xf000000000f80000

def z416 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xdfd97f37f0000000 0x0dfd97f37f000000

def z417 : W := mkw 0xb523cfba6124086d 0x0b523cfba6124086 0x44418f3873041838 0x844418f387304183

def z418 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0553ff000fe70000 0xa0553ff000fe7000

def z419 : W := mkw 0x8a603457c458a9e2 0x98a603457c458a9e 0xfbbe70f7cc78f9ff 0x7fbbe70f7cc78f9f

def z420 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0xfdd90e3ff3649fff 0xbfdd90e3ff3649ff

def z421 : W := mkw 0x3183cba80ba6540c 0x63183cba80ba6540 0x44418f3803871e08 0x844418f3803871e0

def z422 : W := mkw 0x0050000090098310 0x1005000009009831 0xa6a08109f09f8731 0x4a6a08109f09f873

def z423 : W := mkw 0x3c43edffe008810f 0x13c43edffe008810 0xfffbfffff0188103 0x5fffbfffff018810

def z424 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x04418f0000000000 0x004418f000000000

def z425 : W := mkw 0x1a03b0ed0ed0748e 0xa1a03b0ed0ed0748 0x797ff0fe0fe0fece 0xf797ff0fe0fe0fec

def z426 : W := mkw 0x084020458008a182 0x1084020458008a18 0x200400c18000e000 0x0200400c18000e00

def z427 : W := mkw 0x000000000a805400 0x2000000000a80540 0x383e00c00f80fe0e 0xf383e00c00f80fe0

def z428 : W := mkw 0x1a43b0ed8ed8f58e 0xb1a43b0ed8ed8f58 0xbbbef0cf8cf8e7c7 0x7bbbef0cf8cf8e7c

def z429 : W := mkw 0x23c3db008ffe8108 0xd23c3db008ffe810 0xaffbff018fff8103 0xfaffbff018fff810

def z430 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x393e70c60c60e0c6 0x7393e70c60c60e0c

def z431 : W := mkw 0xb3a3dfba4ff65c6c 0xeb3a3dfba4ff65c6 0xfffffffe4fffffff 0xffffffffe4ffffff

def z432 : W := mkw 0x00500412d0098310 0x100500412d009831 0xfff98f3ff09f873b 0xdfff98f3ff09f873

def z433 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0x797f8efe0fe0fece 0xf797f8efe0fe0fec

def z434 : W := mkw 0x0b403245857ca182 0x90b403245857ca18 0xbfff7ec78f7ce1c7 0xfbfff7ec78f7ce1c

def z435 : W := mkw 0x085020459009a392 0x1085020459009a39 0xf80400cff000e7fe 0x0f80400cff000e7f

def z436 : W := mkw 0x024010008458a180 0x9024010008458a18 0x00000000007801c1 0x000000000007801c

def z437 : W := mkw 0x100000a800000004 0x0100000a80000000 0x780000f800000000 0x0780000f80000000

def z438 : W := mkw 0x000000000a805400 0x2000000000a80540 0x686c80080f80fe0e 0xf686c80080f80fe0

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x03ba700000000000 0x003ba70000000000

def z440 : W := mkw 0x8020041240000860 0x0802004124000086 0xd9980036406019ff 0x3d9980036406019f

def z441 : W := mkw 0x2f83ff576ff6000b 0xc2f83ff576ff6000 0x87fbff07ffff0001 0xf87fbff07ffff000

def z442 : W := mkw 0x23c3db008ffea188 0xd23c3db008ffea18 0x07ffff000fffe1c7 0xf07ffff000fffe1c

def z443 : W := mkw 0x8020041240000860 0x0802004124000086 0x4000003040001838 0x0400000304000183

def z444 : W := mkw 0xa3a3df124ff60868 0xca3a3df124ff6086 0x87fbff064fff01f1 0xf87fbff064fff01f

def z445 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdf98e3e43e49fff 0xffdf98e3e43e49ff

def z446 : W := mkw 0x8120061241240860 0x0812006124124086 0x85d90e06436401f1 0xb85d90e06436401f

def z447 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x01137e0000000000 0x001137e000000000

def z448 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x9ffbff060fff01c7 0xf9ffbff060fff01c

def z449 : W := mkw 0x3e83fdff6ed2000f 0xc3e83fdff6ed2000 0xfffbfffffc9b0000 0x4fffbfffffc9b000

def z450 : W := mkw 0xa3f3df12dfff8b78 0xda3f3df12dfff8b7 0xfffbff3fffff9fff 0xffffbff3fffff9ff

def z451 : W := mkw 0xbf63ffffe57ca9ef 0x9bf63ffffe57ca9e 0xffffffffff7cf9ff 0xfffffffffff7cf9f

def z452 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xaaae70c18c18e103 0x5aaae70c18c18e10

def z453 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xba2670c78c18e1c6 0x4ba2670c78c18e1c

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x2828000000008002 0x5282800000000800

def z455 : W := mkw 0x0200100004500000 0x8020010000450000 0x022270000c180000 0x4022270000c18000

def z456 : W := mkw 0x084020458008a182 0x1084020458008a18 0xb83e00c78c00e1c6 0x7b83e00c78c00e1c

def z457 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x000270c000000000 0x0000270c00000000

def z458 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xaba87007807881c3 0x5aba87007807881c

def z459 : W := mkw 0x3fc3ffffeffea18f 0xd3fc3ffffeffea18 0xffffffffffffe1c7 0xfffffffffffffe1c

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x98000006000001c6 0x098000006000001c

def z461 : W := mkw 0x3583cfba6ba6000d 0x43583cfba6ba6000 0x44418f3873870000 0x844418f387387000

def z462 : W := mkw 0x1a43b0ed8ed8f58e 0xb1a43b0ed8ed8f58 0xbbbf70f78f78f9c7 0x7bbbf70f78f78f9c

def z463 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x505780f80f807e0c 0xa505780f80f807e0

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x003a00000c000000 0x7003a00000c00000

def z465 : W := mkw 0x8120061241240860 0x0812006124124086 0x44410e30436419ff 0xb44410e30436419f

def z466 : W := mkw 0x0050000090098310 0x1005000009009831 0x86800101f09f873b 0xd86800101f09f873

def z467 : W := mkw 0x1a43b0ed8458a18e 0x91a43b0ed8458a18 0xfbfff0ff8c78e1c7 0x7fbfff0ff8c78e1c

def z468 : W := mkw 0x0050000090098310 0x1005000009009831 0xfef98139f39f9f3f 0xffef98139f39f9f3

def z469 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff007804 0x2ffffffffff00780

def z470 : W := mkw 0x3f83ffff6576000f 0xc3f83ffff6576000 0xfffbfffff07f0001 0x0fffbfffff07f000

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x06800100001f0001 0x006800100001f000

def z472 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0xdddf0ef64f6479ff 0xbdddf0ef64f6479f

def z473 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xf9137efff0000000 0x0f9137efff000000

def z474 : W := mkw 0xb523cfba6124086d 0x0b523cfba6124086 0xddd98f3e736419ff 0xbddd98f3e736419f

def z475 : W := mkw 0x3c53e9edb009831f 0x13c53e9edb009831 0xeeeaf1c9f09f873b 0xdeeeaf1c9f09f873

def z476 : W := mkw 0x025010009459a390 0x9025010009459a39 0x000400000cffe7ff 0xf000400000cffe7f

def z477 : W := mkw 0x0800204500000002 0x0080020450000000 0x8380700780000000 0x0838070078000000

def z478 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff09f0001 0xdfffbfffff09f000

def z479 : W := mkw 0x1a43b0ed8ed8f58e 0xb1a43b0ed8ed8f58 0x7a7ff0f98f98fe0e 0xf7a7ff0f98f98fe0

def z480 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0xeee98f39f39f9f3b 0xdeee98f39f39f9f3

def z481 : W := mkw 0x0800204500000002 0x0080020450000000 0x111270c600000000 0x0111270c60000000

def z482 : W := mkw 0x1803a0ed0a80540e 0x21803a0ed0a80540 0xfbfff0ff8f80fe0e 0xffbfff0ff8f80fe0

def z483 : W := mkw 0x0050000090098310 0x1005000009009831 0x6a688109b09b860a 0xd6a688109b09b860

def z484 : W := mkw 0x000380000a800008 0x0000380000a80000 0x387f80c00f80e006 0xf387f80c00f80e00

def z485 : W := mkw 0x0a403457c458a182 0x90a403457c458a18 0xffff7ef7cc78e1c7 0x7ffff7ef7cc78e1c

def z486 : W := mkw 0x0000000000000000 0x0000000000000000 0x680000080000860a 0x0680000080000860

def z487 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07c1ff0003ff0001 0x807c1ff0003ff000

def z488 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x03baf1000cfb0001 0x703baf1000cfb000

def z489 : W := mkw 0x8120061241240860 0x0812006124124086 0xd8000036436419ff 0xbd8000036436419f

def z490 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x999e70c60c6061c7 0x3999e70c60c6061c

def z491 : W := mkw 0x2280590004520000 0xc228059000452000 0x02007100001b0000 0x002007100001b000

def z492 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0x44418e3843841e38 0x844418e3843841e3

def z493 : W := mkw 0x902004ba40005c64 0x2902004ba40005c6 0xf80400fe4000fffe 0x0f80400fe4000fff

def z494 : W := mkw 0x0010000010010210 0x0001000001001021 0x0000810830830600 0x0000081083083060

def z495 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0xeeee81c9fc9fe73b 0xdeeee81c9fc9fe73

def z496 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x222670c18c78e1c7 0x7222670c18c78e1c

def z497 : W := mkw 0x0000041240000000 0x0000004124000000 0xddd90e36406001c7 0x3ddd90e36406001c

def z498 : W := mkw 0x912006ba41245c64 0x2912006ba41245c6 0xfddd0efe4364ffff 0xbfddd0efe4364fff

def z499 : W := mkw 0x0040000080088100 0x1004000008008810 0xa800000180008102 0x0a80000018000810

def z500 : W := mkw 0x8130061251250a70 0x08130061251250a7 0x44418f3873871e38 0x844418f3873871e3

def z501 : W := mkw 0x2ac3f9458edaa18a 0xd2ac3f9458edaa18 0x2226f1c18c9be000 0x42226f1c18c9be00

def z502 : W := mkw 0x8020041240000860 0x0802004124000086 0xdcc80036400419ff 0x9dcc80036400419f

def z503 : W := mkw 0x0200100004502080 0x8020010000450208 0x000400000c6060c4 0x2000400000c6060c

def z504 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xb80400c78c78e1c7 0x7b80400c78c78e1c

def z505 : W := mkw 0x000380000a805408 0x2000380000a80540 0x007f80000f80fe0e 0xf007f80000f80fe0

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x02208100009b0000 0x402208100009b000

def z507 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xefe8f10ff0ff87fb 0xdefe8f10ff0ff87f

def z508 : W := mkw 0x024010008458a180 0x9024010008458a18 0x000400000c18e000 0x4000400000c18e00

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000300180e 0xb000000000300180

def z510 : W := mkw 0x2a43f9458458a18a 0x92a43f9458458a18 0xbfffffc78c78e1c7 0x7bfffffc78c78e1c

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0x1011003003001804 0x2101100300300180

def z512 : W := mkw 0x2393db001ff70218 0xc2393db001ff7021 0x47fbff087fff0639 0xf47fbff087fff063

def z513 : W := mkw 0xa123cf1241240868 0x0a123cf124124086 0xdffbff36436419ff 0xbdffbff36436419f

def z514 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xdddb7ef640000000 0x0dddb7ef64000000

def z515 : W := mkw 0x1c5024fff0098317 0x11c5024fff009831 0xfee881fff09f873b 0xdfee881fff09f873

def z516 : W := mkw 0x084020458008a182 0x1084020458008a18 0xbaac00c78018e1c7 0x5baac00c78018e1c

def z517 : W := mkw 0x3f83ffff6ff6000f 0xc3f83ffff6ff6000 0xfffbffffff600000 0x2fffbffffff60000

def z518 : W := mkw 0x0100020001240000 0x0010002000124000 0x07f98f0003ff0001 0xf07f98f0003ff000

def z519 : W := mkw 0x8120061241240860 0x0812006124124086 0x59590e36036018ce 0xb59590e36036018c

def z520 : W := mkw 0x9b63b6ffcffcfdee 0xb9b63b6ffcffcfde 0xfffffeffcffcffff 0xffffffeffcffcfff

def z521 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xa3a670c78c78e1c1 0x4a3a670c78c78e1c

def z522 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x27ffffc80fffe601 0xf27ffffc80fffe60

def z523 : W := mkw 0xbd23efff6124086f 0x0bd23efff6124086 0xfffbfffff06401f1 0x0fffbfffff06401f

def z524 : W := mkw 0x0050000090098310 0x1005000009009831 0x26e88109b09f8601 0xd26e88109b09f860

def z525 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfc418ffff0000000 0x0fc418ffff000000

def z526 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x017bfe000fe00000 0xf017bfe000fe0000

def z527 : W := mkw 0x2b83fb450ff6208a 0xc2b83fb450ff6208 0x11177ec60f6060c4 0x211177ec60f6060c

def z528 : W := mkw 0x8b703657d57dabf2 0x98b703657d57dabf 0xffffffffffffffff 0xffffffffffffffff

def z529 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x686e80c80c80e60a 0xd686e80c80c80e60

def z530 : W := mkw 0x22d3d9009edb8318 0xd22d3d9009edb831 0x2222f109bc9b8600 0x42222f109bc9b860

def z531 : W := mkw 0x100000a800005404 0x2100000a80000540 0x783e00f80c00fe0e 0x7783e00f80c00fe0

def z532 : W := mkw 0x1c03a4ff6000000f 0x01c03a4ff6000000 0xf87b80fff0000000 0x0f87b80fff000000

def z533 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xa7a2ffcff0000000 0x0a7a2ffcff000000

def z534 : W := mkw 0x3e43f9eda458a18f 0x93e43f9eda458a18 0xbbbef1cfbc78e1c7 0x7bbbef1cfbc78e1c

def z535 : W := mkw 0x0000041240000000 0x0000004124000000 0xddd90e364004013b 0x9ddd90e364004013

def z536 : W := mkw 0x3e43f9eda458a18f 0x93e43f9eda458a18 0x2226f1c9bc18e000 0x42226f1c9bc18e00

def z537 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x07fbff0003870000 0x807fbff000387000

def z538 : W := mkw 0x0000041240000000 0x0000004124000000 0xddd90e364300180e 0xbddd90e364300180

def z539 : W := mkw 0x8b203657457428e2 0x88b203657457428e 0xdddf7ef64f6479ff 0xbdddf7ef64f6479f

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x86800101f0000000 0x086800101f000000

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x8888000000000103 0x1888800000000010

def z542 : W := mkw 0x8130061251250a70 0x08130061251250a7 0xddd98f3e73e71fff 0xbddd98f3e73e71ff

def z543 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0x06e881000fff0001 0xf06e881000fff000

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x81800006006001c1 0x081800006006001c

def z545 : W := mkw 0x8120020001240860 0x0812002000124086 0x00000000036018c4 0x200000000036018c

def z546 : W := mkw 0x8120061241240860 0x0812006124124086 0xdd800e36406419ff 0x0dd800e36406419f

def z547 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x787b80f80080860a 0xd787b80f80080860

def z548 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0x47fbff3870000000 0x047fbff387000000

def z549 : W := mkw 0x83601200857ca9e0 0x983601200857ca9e 0x000400000f7cf9ff 0xf000400000f7cf9f

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x2020800800808600 0x4202080080080860

def z551 : W := mkw 0x8120061241240860 0x0812006124124086 0x01000e06006000c0 0x001000e06006000c

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x202600c00c00e000 0x4202600c00c00e00

def z553 : W := mkw 0x0040000080088100 0x1004000008008810 0xeae880098098870b 0xdeae880098098870

def z554 : W := mkw 0x0380120005760000 0xc038012000576000 0x00000000007f0001 0x000000000007f000

def z555 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0xefe88f0ff0ff87fb 0xdefe88f0ff0ff87f

def z556 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x107f80f00f807804 0xf107f80f00f80780

def z557 : W := mkw 0x24004d1260000001 0x024004d126000000 0x04000f0070000000 0x004000f007000000

def z558 : W := mkw 0x085020459009a392 0x1085020459009a39 0xfeec81cff09fe7ff 0xdfeec81cff09fe7f

def z559 : W := mkw 0x010382000ba40008 0x0010382000ba4000 0x05fb8e000fe40001 0xf05fb8e000fe4000

def z560 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbb8470c78078e1c7 0x0bb8470c78078e1c

def z561 : W := mkw 0x3403cdba6a80540d 0x23403cdba6a80540 0x7c7f8ff87f80fe0e 0xf7c7f8ff87f80fe0

def z562 : W := mkw 0x1e4034ffe458a187 0x91e4034ffe458a18 0xfbbe70fffc78e1c7 0x7fbbe70fffc78e1c

def z563 : W := mkw 0x3d83efff6ba6000f 0x43d83efff6ba6000 0xfffbfffff3870000 0x8fffbfffff387000

def z564 : W := mkw 0x000000000a805400 0x2000000000a80540 0x585d00300f80fe0e 0xf585d00300f80fe0

def z565 : W := mkw 0x0050000090098310 0x1005000009009831 0xeaa80009f018873b 0x5eaa80009f018873

def z566 : W := mkw 0x0050000090098310 0x1005000009009831 0xaaa80001809f873b 0xdaaa80001809f873

def z567 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x202680c80f80fe0e 0xf202680c80f80fe0

def z568 : W := mkw 0x2e407d57e458a183 0x92e407d57e458a18 0x87807f07f07801c1 0x087807f07f07801c

def z569 : W := mkw 0x3e03fdff6450000f 0x83e03fdff6450000 0xfffbfffffc780001 0x7fffbfffffc78000

def z570 : W := mkw 0x1843a0ed8a88f58e 0x31843a0ed8a88f58 0xf87f80ff8f80ffce 0xff87f80ff8f80ffc

def z571 : W := mkw 0x8320161245740860 0x8832016124574086 0xdffb7e364f7c19ff 0xfdffb7e364f7c19f

def z572 : W := mkw 0x1a4030ed8458f586 0xb1a4030ed8458f58 0xfbbe70ff8c78ffcf 0x7fbbe70ff8c78ffc

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8000009f0000000 0x0e8000009f000000

def z574 : W := mkw 0x0050000090098310 0x1005000009009831 0xe8000009f09f873b 0xde8000009f09f873

def z575 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0x222681c9bc9be600 0x4222681c9bc9be60

def z576 : W := mkw 0x0050000090098310 0x1005000009009831 0x00000000009b8600 0x400000000009b860

def z577 : W := mkw 0x3c53edfff009831f 0x13c53edfff009831 0xfffbfffff000873a 0x0fffbfffff000873

def z578 : W := mkw 0x0200100004500000 0x8020010000450000 0x000000000c780001 0x7000000000c78000

def z579 : W := mkw 0x0050000090098310 0x1005000009009831 0xec408109f087873a 0x8ec408109f087873

def z580 : W := mkw 0x0100020001240000 0x0010002000124000 0x9dd90e06036401c7 0xb9dd90e06036401c

def z581 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x838470078c78e1c7 0x7838470078c78e1c

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000080860a 0xd000000000080860

def z583 : W := mkw 0x0100020001240000 0x0010002000124000 0xcdd90e004364013b 0xbcdd90e004364013

def z584 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07807f000fff0001 0xf07807f000fff000

def z585 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0x7c7f8ef84f84fe3e 0xf7c7f8ef84f84fe3

def z586 : W := mkw 0x100384ba4000000c 0x0100384ba4000000 0xfdfb8efe40000000 0x0fdfb8efe4000000

def z587 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfa22f1fff0000000 0x0fa22f1fff000000

def z588 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbba70c7806001c7 0x3bbba70c7806001c

def z589 : W := mkw 0x83601612c57ca9e0 0x983601612c57ca9e 0xdddd0e364f7cf9ff 0xfdddd0e364f7cf9f

def z590 : W := mkw 0x084020458008a182 0x1084020458008a18 0xbbbe70c78000e1c6 0x0bbbe70c78000e1c

def z591 : W := mkw 0x1c0020ed20000007 0x01c0020ed2000000 0x200000c9b0000000 0x0200000c9b000000

def z592 : W := mkw 0x0840204580088102 0x1084020458008810 0xbbba70c780188103 0x5bbba70c78018810

def z593 : W := mkw 0x0a43b0458ed8a18a 0x90a43b0458ed8a18 0xbbfff0c78ff8e1c7 0xfbbfff0c78ff8e1c

def z594 : W := mkw 0x000000000a805400 0x2000000000a80540 0x000400000f007804 0x2000400000f00780

def z595 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x585f00f00f00780e 0xb585f00f00f00780

def z596 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0x000000000f600000 0x2000000000f60000

def z597 : W := mkw 0xbd73effff12d8b7f 0x1bd73effff12d8b7 0xfffbfffff3ff9fff 0xffffbfffff3ff9ff

def z598 : W := mkw 0x0200100004500000 0x8020010000450000 0x0380700000780001 0x0038070000078000

def z599 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0x11170ef60f6078c4 0x211170ef60f6078c

def z600 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0xddd98f3e70000000 0x0ddd98f3e7000000

def z601 : W := mkw 0x0040000080088100 0x1004000008008810 0x0000000000188103 0x5000000000018810

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0x22208109b0000000 0x022208109b000000

def z603 : W := mkw 0x100000a800005404 0x2100000a80000540 0x786c80f80080fe0e 0xd786c80f80080fe0

def z604 : W := mkw 0x024010008458a180 0x9024010008458a18 0xaaac00018c78e1c7 0x7aaac00018c78e1c

def z605 : W := mkw 0x80700412d0098b70 0x180700412d0098b7 0xfee8813ff09f9fff 0xdfee8813ff09f9ff

def z606 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0xddd98e3e43e41fff 0xbddd98e3e43e41ff

def z607 : W := mkw 0x0050000090098310 0x1005000009009831 0x22208109b09f873b 0xd22208109b09f873

def z608 : W := mkw 0x3e43fdffe458a18f 0x93e43fdffe458a18 0xbbbf7ef78c78e1c7 0x7bbbf7ef78c78e1c

def z609 : W := mkw 0x3e43fdffe458a18f 0x93e43fdffe458a18 0xfffbfffff07801c1 0x0fffbfffff07801c

def z610 : W := mkw 0x2ac3f9458edaa18a 0xd2ac3f9458edaa18 0xbbbef1c78cfbe1c7 0x7bbbef1c78cfbe1c

def z611 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0xeeeaf1c9f0000000 0x0eeeaf1c9f000000

def z612 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0xdfd90f37f37f19ff 0xbdfd90f37f37f19f

def z613 : W := mkw 0x0010000010010210 0x0001000001001021 0x6c6881087087863a 0xd6c6881087087863

def z614 : W := mkw 0x100000a800005404 0x2100000a80000540 0x4000003800001e08 0x04000003800001e0

def z615 : W := mkw 0x2803e9450000000a 0x02803e9450000000 0xbffbffc780000000 0x0bffbffc78000000

def z616 : W := mkw 0x2bc3fb458ffea18a 0xd2bc3fb458ffea18 0xbbbf7ec78f78e1c7 0x7bbbf7ec78f78e1c

def z617 : W := mkw 0x8120061241240860 0x0812006124124086 0x15d90e36036418c5 0xb15d90e36036418c

def z618 : W := mkw 0x0010000010010210 0x0001000001001021 0xccc881087087073b 0x9ccc881087087073

def z619 : W := mkw 0x100000a800005404 0x2100000a80000540 0x785d00f80300fe0e 0xb785d00f80300fe0

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa8000180000000 0x0aaa800018000000

def z621 : W := mkw 0x3403c9a82000000d 0x03403c9a82000000 0x0000810830000000 0x0000081083000000

def z622 : W := mkw 0x0050000090098310 0x1005000009009831 0x02000101b01b0000 0x002000101b01b000

def z623 : W := mkw 0x084020458008a182 0x1084020458008a18 0xb99c00c78060e1c7 0x3b99c00c78060e1c

def z624 : W := mkw 0x8120061241240860 0x0812006124124086 0x45d90e3043641839 0xb45d90e304364183

def z625 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x404580380f80fe0e 0xf404580380f80fe0

def z626 : W := mkw 0x3c53edfff009831f 0x13c53edfff009831 0xfffbfffff09b8600 0x4fffbfffff09b860

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0xcee88100409f013b 0xdcee88100409f013

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0xdcd900304304193f 0xbdcd900304304193

def z629 : W := mkw 0x3f83ffff6ff6000f 0xc3f83ffff6ff6000 0x17fbfff60fff0001 0xf17fbfff60fff000

def z630 : W := mkw 0x21d3cb009baf8318 0x521d3cb009baf831 0xeee98f09f39f873b 0xdeee98f09f39f873

def z631 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f000873a 0x0eee88109f000873

def z632 : W := mkw 0x0100020001240000 0x0010002000124000 0x01110e0003600000 0x201110e000360000

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x1818000000000006 0x3181800000000000

def z634 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x01007e0600000000 0x001007e060000000

def z635 : W := mkw 0x902384ba4a805c6c 0x2902384ba4a805c6 0xf87f80fe4f80fffe 0xff87f80fe4f80fff

def z636 : W := mkw 0x0050000090098310 0x1005000009009831 0xaaa88109b09b8703 0x5aaa88109b09b870

def z637 : W := mkw 0x3f83ffff6ff6000f 0xc3f83ffff6ff6000 0x11137ef60f600000 0x211137ef60f60000

def z638 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x797ffef80fe0fe0e 0xf797ffef80fe0fe0

def z639 : W := mkw 0x3c43edffe008a18f 0x13c43edffe008a18 0xfffffffff000e1c6 0x0fffffffff000e1c

def z640 : W := mkw 0xad206f5761240863 0x0ad206f576124086 0x87807f07f06401f1 0x087807f07f06401f

def z641 : W := mkw 0xa3a3df124ff60868 0xca3a3df124ff6086 0xdddb7e364f6419ff 0xbdddb7e364f6419f

def z642 : W := mkw 0x0200100004500000 0x8020010000450000 0x9bba70060c7801c7 0x79bba70060c7801c

def z643 : W := mkw 0x0200100004500000 0x8020010000450000 0x011270000c600000 0x2011270000c60000

def z644 : W := mkw 0x005380009a898318 0x1005380009a89831 0xeefb8109ff9f873b 0xfeefb8109ff9f873

def z645 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0x05d90e000fff0001 0xf05d90e000fff000

def z646 : W := mkw 0x3d03efff6124000f 0x03d03efff6124000 0xfffbfffff3640001 0xbfffbfffff364000

def z647 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x03bb7e000f780001 0x703bb7e000f78000

def z648 : W := mkw 0x2c00694520000003 0x02c0069452000000 0x02007101b0000000 0x002007101b000000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0xb9be00c60c60e1c7 0x7b9be00c60c60e1c

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x4440000040040038 0x8444000004004003

def z651 : W := mkw 0x105380a89009831c 0x1105380a89009831 0xfefb81f9f09f873b 0xdfefb81f9f09f873

def z652 : W := mkw 0x3c03e9ed2a80540f 0x23c03e9ed2a80540 0x7a7ff1f9bf80fe0e 0xf7a7ff1f9bf80fe0

def z653 : W := mkw 0x2053c90090098318 0x12053c9009009831 0xeffbff09f09f873b 0xdeffbff09f09f873

def z654 : W := mkw 0x101380a81a81561c 0x2101380a81a81561 0x4441813873871e38 0x84441813873871e3

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000009f0001 0xd00000000009f000

def z656 : W := mkw 0x23d3db009fff8318 0xd23d3db009fff831 0x27fbff09bfff8601 0xf27fbff09bfff860

def z657 : W := mkw 0x0050000090098310 0x1005000009009831 0x20000009b0008600 0x020000009b000860

def z658 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0x00010e3000000000 0x000010e300000000

def z659 : W := mkw 0x8120020001240860 0x0812002000124086 0xccc80000436419ff 0xbccc80000436419f

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0xece880084084873b 0xdece880084084873

def z661 : W := mkw 0x8120061241240860 0x0812006124124086 0xcdc80e06406401fb 0x9cdc80e06406401f

def z662 : W := mkw 0x0050000090098310 0x1005000009009831 0x44408108709f873b 0xd44408108709f873

def z663 : W := mkw 0x8120020001240860 0x0812002000124086 0x05d90e00036419ff 0xb05d90e00036419f

def z664 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0x03ba70000fff0001 0xf03ba70000fff000

def z665 : W := mkw 0x81700200912d8b70 0x181700200912d8b7 0x0000000003ff9fff 0xf0000000003ff9ff

def z666 : W := mkw 0x2f807f5765760003 0xc2f807f576576000 0x87807f07f07f0001 0x087807f07f07f000

def z667 : W := mkw 0x1a03b0ed0ed0748e 0xa1a03b0ed0ed0748 0x111770f60f6078c4 0x2111770f60f6078c

def z668 : W := mkw 0x024010008458a180 0x9024010008458a18 0x03be70000c78e1c7 0x703be70000c78e1c

def z669 : W := mkw 0x0040000080088100 0x1004000008008810 0x2220000180188000 0x4222000018018800

def z670 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787b80f803801e08 0x8787b80f803801e0

def z671 : W := mkw 0x80700412d0098b70 0x180700412d0098b7 0xf800003ff0009ffe 0x0f800003ff0009ff

def z672 : W := mkw 0x024010008458a180 0x9024010008458a18 0x999c00060c78e1c7 0x7999c00060c78e1c

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x05d90e0000000000 0x005d90e000000000

def z674 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x0200700180180000 0x0020070018018000

def z675 : W := mkw 0xa3a3df124ff60868 0xca3a3df124ff6086 0x11137e360f6018c4 0x211137e360f6018c

def z676 : W := mkw 0x2003cd1240000008 0x02003cd124000000 0xdffbff3640000000 0x0dffbff364000000

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0xccc8000040000000 0x0ccc800004000000

def z678 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x05db7e000f640001 0xb05db7e000f64000

def z679 : W := mkw 0x8120020001240860 0x0812002000124086 0x99980006036419ff 0xb99980006036419f

def z680 : W := mkw 0x100380a80a80000c 0x0100380a80a80000 0x787b80f80f800000 0xf787b80f80f80000

def z681 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0x87800f07f07f01f1 0x087800f07f07f01f

def z682 : W := mkw 0x0850204590098312 0x1085020459009831 0xfffaf1cff09f873b 0xdfffaf1cff09f873

def z683 : W := mkw 0x812002000ba45c60 0x2812002000ba45c6 0x000400000fe4ffff 0xf000400000fe4fff

def z684 : W := mkw 0x0050000090098310 0x1005000009009831 0xccc80000409f873b 0xdccc80000409f873

def z685 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x000600c00c006000 0x0000600c00c00600

def z686 : W := mkw 0x8120020001240860 0x0812002000124086 0x0000000003041838 0x8000000000304183

def z687 : W := mkw 0x105000a89009d714 0x3105000a89009d71 0xf80400f9f000ff3e 0x0f80400f9f000ff3

def z688 : W := mkw 0x020390000ed00008 0x8020390000ed0000 0x03fbf0000ff80001 0xf03fbf0000ff8000

def z689 : W := mkw 0x0010000010010210 0x0001000001001021 0xeee88109f0870638 0x8eee88109f087063

def z690 : W := mkw 0x812386124ba40868 0x0812386124ba4086 0xddfb8e364fe419ff 0xfddfb8e364fe419f

def z691 : W := mkw 0x0000041240000000 0x0000004124000000 0xfff98f3ff0000000 0x0fff98f3ff000000

def z692 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80c80e600 0x4787f80f80c80e60

def z693 : W := mkw 0x000380000a800008 0x0000380000a80000 0x587b80300f80180e 0xf587b80300f80180

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x0198000000600001 0x3019800000060000

def z695 : W := mkw 0x025010009459a390 0x9025010009459a39 0xeeec8109fcffe7ff 0xfeeec8109fcffe7f

def z696 : W := mkw 0x8020041240000860 0x0802004124000086 0xddd90e36400019fe 0x0ddd90e36400019f

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x380400c00000e006 0x0380400c00000e00

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x9998000600000000 0x0999800060000000

def z699 : W := mkw 0x105000a89009d714 0x3105000a89009d71 0xfeec81f9f09fff3f 0xdfeec81f9f09fff3

def z700 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x787b80f80300180e 0xb787b80f80300180

def z701 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x000270000c000000 0x0000270000c00000

def z702 : W := mkw 0x81600612c12c8960 0x181600612c12c896 0xfff90e37c37c99ff 0xffff90e37c37c99f

def z703 : W := mkw 0x104380a88a88d50c 0x3104380a88a88d50 0xfaff80f98f98ff0f 0xffaff80f98f98ff0

def z704 : W := mkw 0x100380a80000000c 0x0100380a80000000 0x101300f000000000 0x0101300f00000000

def z705 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f01f0131 0x0eee88109f01f013

def z706 : W := mkw 0x0000000000000000 0x0000000000000000 0x02a8000000180001 0x502a800000018000

def z707 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x010670c60c6060c0 0x0010670c60c6060c

def z708 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffbfffff0001e08 0x0fffbfffff0001e0

def z709 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xa7a6ffcffc80e600 0x4a7a6ffcffc80e60

def z710 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdd90e3ff36419ff 0xbfdd90e3ff36419f

def z711 : W := mkw 0x0050000090098310 0x1005000009009831 0xec408109f09f873b 0xdec408109f09f873

def z712 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfbbef1cffcfbe7ff 0x7fbbef1cffcfbe7f

def z713 : W := mkw 0x2000490000000000 0x0200049000000000 0x07807f00001f0001 0x007807f00001f000

def z714 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x9f987f07f0000000 0x09f987f07f000000

def z715 : W := mkw 0x3003c9a80a80540c 0x23003c9a80a80540 0x7ffffff80f9ffe0f 0xf7ffffff80f9ffe0

def z716 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffbffffff801e08 0xffffbffffff801e0

def z717 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0000006 0x3fffbfffff000000

def z718 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xbfbb7ff7f0000000 0x0bfbb7ff7f000000

def z719 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x87fbff01ffff0001 0xf87fbff01ffff000

def z720 : W := mkw 0x83f012009fff8b70 0xd83f012009fff8b7 0x000000000fff9fff 0xf000000000fff9ff

def z721 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x03007f07b0000000 0x003007f07b000000

def z722 : W := mkw 0x8120061241240860 0x0812006124124086 0xfff98f3ff3e49fff 0xffff98f3ff3e49ff

def z723 : W := mkw 0x0050000090098310 0x1005000009009831 0xa6a08109f09f873b 0xda6a08109f09f873

def z724 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffef1cffc78e7ff 0x7fffef1cffc78e7f

def z725 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x97927fc7f0000000 0x097927fc7f000000

def z726 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87e8ff07f0000000 0x087e8ff07f000000

def z727 : W := mkw 0x3c53edfff009831f 0x13c53edfff009831 0x11137ef6009f873b 0xd11137ef6009f873

def z728 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x784580f80f80fe0e 0xf784580f80f80fe0

def z729 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07807f0003ff0001 0x807807f0003ff000

def z730 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xffffffffff00f80e 0xfffffffffff00f80

def z731 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbfff0ff8ff8ffcf 0xffbfff0ff8ff8ffc

def z732 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xc7c1ff3ff3801e08 0x8c7c1ff3ff3801e0

def z733 : W := mkw 0x2c03ed576a80000b 0x02c03ed576a80000 0x87fbff07ff800000 0xf87fbff07ff80000

def z734 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0x5ffbff300fff19ff 0xf5ffbff300fff19f

def z735 : W := mkw 0x81700612d12d8b70 0x181700612d12d8b7 0x33318f3fb3fb9ec4 0x633318f3fb3fb9ec

def z736 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0x87a2ff07f0000000 0x087a2ff07f000000

def z737 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x37fbffffb0000000 0x037fbffffb000000

def z738 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x5fd97f30037f180f 0xb5fd97f30037f180

def z739 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbff70c78f78e1c7 0xfbbff70c78f78e1c

def z740 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffffffff000e600 0x0fffffffff000e60

def z741 : W := mkw 0xa2a3dd124ed20868 0xca2a3dd124ed2086 0xda22f1364c9b19fe 0x4da22f1364c9b19f

def z742 : W := mkw 0x8120061241240860 0x0812006124124086 0xd5d10e36436419fd 0xad5d10e36436419f

def z743 : W := mkw 0x29c3eb458baea18a 0x529c3eb458baea18 0xbc458fc78387e1c6 0x8bc458fc78387e1c

def z744 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xefeef1cffcffe7fb 0xdefeef1cffcffe7f

def z745 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07e8ff00007f0001 0x007e8ff00007f000

def z746 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x87817f37f0000000 0x087817f37f000000

def z747 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xeffbff09ffff013b 0xfeffbff09ffff013

def z748 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x07fbff300fff1801 0xf07fbff300fff180

def z749 : W := mkw 0x33805ba805765404 0xe33805ba80576540 0x7f847ff8007ffe0f 0x07f847ff8007ffe0

def z750 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff80e600 0xfffffffffff80e60

def z751 : W := mkw 0x3003c9a80a80540c 0x23003c9a80a80540 0x797ffef80f80fe0e 0xf797ffef80f80fe0

def z752 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x01137e000f7f0001 0x201137e000f7f000

def z753 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0xeee88109ffff0001 0xfeee88109ffff000

def z754 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee98139f39f9f3b 0xdeee98139f39f9f3

def z755 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe70c7fc78e1f7 0x7bbbe70c7fc78e1f

def z756 : W := mkw 0xb3a3dba80ff65c6c 0xeb3a3dba80ff65c6 0x7ffffff80fffffff 0xf7ffffff80ffffff

def z757 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x307f80f80f80fe04 0xf307f80f80f80fe0

def z758 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x139670c60c7860c5 0x2139670c60c7860c

def z759 : W := mkw 0x912386ba4ba45c6c 0x2912386ba4ba45c6 0xa5a68ece4ce4e7f1 0x4a5a68ece4ce4e7f

def z760 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x111670c60c78e0c4 0x6111670c60c78e0c

def z761 : W := mkw 0x2003c9000a800008 0x02003c9000a80000 0x07fbff000f9f0001 0xf07fbff000f9f000

def z762 : W := mkw 0x8120061241240860 0x0812006124124086 0x99990e36036419ff 0xb99990e36036419f

def z763 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xefeaffcff0000000 0x0efeaffcff000000

def z764 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f0ff87ff 0xfeee88109f0ff87f

def z765 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0xfffffffe0fffffcf 0xffffffffe0fffffc

def z766 : W := mkw 0x2c006d576a805403 0x22c006d576a80540 0x87847f07ff80fe0e 0xf87847f07ff80fe0

def z767 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x107f80f00f80fe0e 0xf107f80f00f80fe0

def z768 : W := mkw 0x0050000090098310 0x1005000009009831 0xeffaf109f09f873b 0xdeffaf109f09f873

def z769 : W := mkw 0x8120061241240860 0x0812006124124086 0xd9590e36436019fe 0xbd9590e36436019f

def z770 : W := mkw 0xa3a3db000ff65c68 0xea3a3db000ff65c6 0x07ffff000fffffff 0xf07ffff000ffffff

def z771 : W := mkw 0x8b703657d57dabf2 0x98b703657d57dabf 0x87807f07f07f01f1 0x087807f07f07f01f

def z772 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xdffbff360fff19cf 0xfdffbff360fff19c

def z773 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffffc000000 0x7fffbfffffc00000

def z774 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0x07fbff000fff01f1 0xf07fbff000fff01f

def z775 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff9ffe0f 0xfffffffffff9ffe0

def z776 : W := mkw 0x03d012009fff8310 0xd03d012009fff831 0x000000000fff0131 0xf000000000fff013

def z777 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x7ffbff380fff9e0f 0xf7ffbff380fff9e0

def z778 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffffffffc006000 0x0fffffffffc00600

def z779 : W := mkw 0x0050000090098310 0x1005000009009831 0xc6e88109f09f0739 0xdc6e88109f09f073

def z780 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x3fffffc80fffe607 0xf3fffffc80fffe60

def z781 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x33be70c78c78e0c5 0x733be70c78c78e0c

def z782 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x2223fff9b0000000 0x02223fff9b000000

def z783 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xb91670c78c6060c4 0x2b91670c78c6060c

def z784 : W := mkw 0xbd23ebed2124086f 0x0bd23ebed2124086 0x2222f1c9b36419ff 0xb2222f1c9b36419f

def z785 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xcffbff004fff0001 0xfcffbff004fff000

def z786 : W := mkw 0x3403c9a82a80540d 0x23403c9a82a80540 0x787f81f83f80fe0e 0xf787f81f83f80fe0

def z787 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff000860a 0x0fffbfffff000860

def z788 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x87807f01f07f0001 0x087807f01f07f000

def z789 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe70c78cfbe7c7 0x7bbbe70c78cfbe7c

def z790 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xefe8ff0ff080860a 0xdefe8ff0ff080860

def z791 : W := mkw 0x0050000090098310 0x1005000009009831 0xa6e88109f09f8731 0xda6e88109f09f873

def z792 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x07fbff00001f0001 0x007fbff00001f000

def z793 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0xfffffff9fffffe0f 0xffffffff9fffffe0

def z794 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x9f987f07f06001c7 0x39f987f07f06001c

def z795 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbffffff80860a 0xffffbffffff80860

def z796 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07fb7f000f7f0001 0xf07fb7f000f7f000

def z797 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbfbe70c7cc7ce1f7 0x7bfbe70c7cc7ce1f

def z798 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80fe0ffcf 0xf787f80f80fe0ffc

def z799 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffbfffff3809e0a 0xdfffbfffff3809e0

def z800 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x06007f01f0000000 0x006007f01f000000

def z801 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07c1ff00007f0001 0x007c1ff00007f000

def z802 : W := mkw 0xb523cfba6ba45c6d 0x2b523cfba6ba45c6 0x44418f3873841e38 0x844418f3873841e3

def z803 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0xbffbffc7f0000000 0x0bffbffc7f000000

def z804 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x9ffbff060fff0001 0xf9ffbff060fff000

def z805 : W := mkw 0x8120061241240860 0x0812006124124086 0x55510e36436419ff 0xb55510e36436419f

def z806 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07c0ff0000ff0001 0x807c0ff0000ff000

def z807 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x9bbe70c60c7861c7 0x79bbe70c60c7861c

def z808 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x7ffbfff80fff860b 0xf7ffbfff80fff860

def z809 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x01007e00007f0001 0x001007e00007f000

def z810 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x2ffbff000fff8003 0xf2ffbff000fff800

def z811 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x17fffff00ffffe0f 0xf17fffff00ffffe0

def z812 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x393e70c60c6060c4 0x2393e70c60c6060c

def z813 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x6ffbff380fff9e0b 0xf6ffbff380fff9e0

def z814 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x838670c78c7861c1 0x0838670c78c7861c

def z815 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f09f0739 0x8eee88109f09f073

def z816 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07c87f00007f0001 0x907c87f00007f000

def z817 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff0003ff0001 0x807fbff0003ff000

def z818 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbef1c78cfbe1c7 0x7bbbef1c78cfbe1c

def z819 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07807f000c7f0001 0x707807f000c7f000

def z820 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x5ffbff300fff0001 0xf5ffbff300fff000

def z821 : W := mkw 0x8120061241240860 0x0812006124124086 0x85810e36436419f1 0x085810e36436419f

def z822 : W := mkw 0x105380a89a89d71c 0x3105380a89a89d71 0x969701f1ff1f7935 0x2969701f1ff1f793

def z823 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xd7d3fffff0000000 0x0d7d3fffff000000

def z824 : W := mkw 0x0800245740000002 0x0080024574000000 0xfffbfffff0000000 0x0fffbfffff000000

def z825 : W := mkw 0x23d3db009fff8318 0xd23d3db009fff831 0xe9137e09ff60873a 0x2e9137e09ff60873

def z826 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x911670c78c6061c4 0x2911670c78c6061c

def z827 : W := mkw 0x03d01200957f8310 0xd03d01200957f831 0x0000000000ff873b 0xd0000000000ff873

def z828 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07bb7f000f7f0001 0x707bb7f000f7f000

def z829 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x17ffffc00fff6005 0xf17ffffc00fff600

def z830 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x57fffff80fff7e0d 0xf57fffff80fff7e0

def z831 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff84ff3f 0xfffffffffff84ff3

def z832 : W := mkw 0x8120061241240860 0x0812006124124086 0xdffb7e36436419ff 0xbdffb7e36436419f

def z833 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x0663ff000c9b0000 0x40663ff000c9b000

def z834 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffff1ffffffffff 0xffffff1fffffffff

def z835 : W := mkw 0x100000a800005404 0x2100000a80000540 0x787f00f80f00fe0e 0xf787f00f80f00fe0

def z836 : W := mkw 0x8120061241240860 0x0812006124124086 0x11110e36036019fe 0x211110e36036019f

def z837 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7c7f81f80f87fe0e 0xf7c7f81f80f87fe0

def z838 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7cff80f80f84fe0f 0xf7cff80f80f84fe0

def z839 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0x87937f07f0000000 0x087937f07f000000

def z840 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff3000000 0xbfffbfffff300000

def z841 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0780ff0000ff0001 0x00780ff0000ff000

def z842 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff09f013b 0xdfffbfffff09f013

def z843 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbfbe71c7fc78e1c7 0x7bfbe71c7fc78e1c

def z844 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbffef1c78c78e1c7 0x7bffef1c78c78e1c

def z845 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xcfc87f07f0000000 0x0cfc87f07f000000

def z846 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffffffffc80e60e 0xffffffffffc80e60

def z847 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x47fbff004fff0039 0xf47fbff004fff003

def z848 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xffe8fffff0000000 0x0ffe8fffff000000

def z849 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xbbbe70c78c60e0c6 0x7bbbe70c78c60e0c

def z850 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x301700f80f00fe04 0x2301700f80f00fe0

def z851 : W := mkw 0x23805b0005760000 0xc23805b000576000 0xefe8ff09f07f0001 0x0efe8ff09f07f000

def z852 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xba2670c78c78e1c7 0x7ba2670c78c78e1c

def z853 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7aff80f80f98fe0f 0xf7aff80f80f98fe0

def z854 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffffffff080fe0e 0xdfffffffff080fe0

def z855 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x91137ef7f0000000 0x091137ef7f000000

def z856 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x7ffbfff9b0000000 0x07ffbfff9b000000

def z857 : W := mkw 0x23805b0005760000 0xc23805b000576000 0xcfc87f00407f013b 0x9cfc87f00407f013

def z858 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbb9670c78c78e1c7 0x2bb9670c78c78e1c

def z859 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff80fe04 0x6ffffffffff80fe0

def z860 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x101700f00f00fe0e 0x2101700f00f00fe0

def z861 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x067bff000f9f0000 0xf067bff000f9f000

def z862 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0008002 0x5fffbfffff000800

def z863 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x383f80f80f80fe06 0x7383f80f80f80fe0

def z864 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x303780f80f80fe0e 0xf303780f80f80fe0

def z865 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbfffffc800000 0x4fffbfffffc80000

def z866 : W := mkw 0x8120061241240860 0x0812006124124086 0xdfd90f36437f19ff 0xbdfd90f36437f19f

def z867 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7a7f81f9bf80fe0e 0xf7a7f81f9bf80fe0

def z868 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x27ffffc00fffe001 0xf27ffffc00fffe00

def z869 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87d97f07f0000000 0x087d97f07f000000

def z870 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x67fffff80ffffe09 0xf67fffff80ffffe0

def z871 : W := mkw 0x0050000090098310 0x1005000009009831 0xfeff81f9ff9fff3f 0xffeff81f9ff9fff3

def z872 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdf90e36436499ff 0xffdf90e36436499f

def z873 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0180001 0x5fffbfffff018000

def z874 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xc7807f3ff0000000 0x0c7807f3ff000000

def z875 : W := mkw 0x100000a80a805404 0x2100000a80a80540 0x100400f00f80fe0e 0xf100400f00f80fe0

def z876 : W := mkw 0x2803e9450000000a 0x02803e9450000000 0xfffbffcff0000000 0x0fffbffcff000000

def z877 : W := mkw 0x100000a80a805404 0x2100000a80a80540 0x780400f80f00fe0e 0x2780400f80f00fe0

def z878 : W := mkw 0x0050000090098310 0x1005000009009831 0xfff9813ff3ff9fff 0xffff9813ff3ff9ff

def z879 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7c7f81f87f80fe0e 0xf7c7f81f87f80fe0

def z880 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbfe70c78c78e1cf 0xffbfe70c78c78e1c

def z881 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbfbef1cffcffe7f7 0x7bfbef1cffcffe7f

def z882 : W := mkw 0x8b603657c57ca9e2 0x98b603657c57ca9e 0x66677ef1cf1cf838 0xc66677ef1cf1cf83

def z883 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff00001f0 0x0fffbfffff00001f

def z884 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef1cffcffe1c7 0xffffef1cffcffe1c

def z885 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xa7a6f1cffcffe7f1 0x4a7a6f1cffcffe7f

def z886 : W := mkw 0x8120061241240860 0x0812006124124086 0x11110e36036419f5 0x211110e36036419f

def z887 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x2322ffcfb0000000 0x02322ffcfb000000

def z888 : W := mkw 0x03d01200957f8310 0xd03d01200957f831 0x00000000007f0131 0x000000000007f013

def z889 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f84ff3f 0xf787f80f80f84ff3

def z890 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x1ffbff000fff0007 0xf1ffbff000fff000

def z891 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x919670c60c6061c5 0x2919670c60c6061c

def z892 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x5ffbff380fff1e0f 0xf5ffbff380fff1e0

def z893 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7dff8ef80f80fe0e 0xf7dff8ef80f80fe0

def z894 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xf9177effff00fe0e 0x2f9177effff00fe0

def z895 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07fbff000c7f0001 0x707fbff000c7f000

def z896 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffe70c7ccffe7ff 0xffffe70c7ccffe7f

def z897 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xeffbff09ffff860b 0xfeffbff09ffff860

def z898 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x87fbff004fff0131 0xf87fbff004fff013

def z899 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78f78f9cf 0xfbbbe70c78f78f9c

def z900 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd98f3643e719ff 0xbddd98f3643e719f

def z901 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0322ff000cfb0000 0x40322ff000cfb000

def z902 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfd53fffff0000000 0x0fd53fffff000000

def z903 : W := mkw 0x0050000090098310 0x1005000009009831 0x66e88109f09f8639 0xd66e88109f09f863

def z904 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xffbe71cffc7fe7ff 0x7ffbe71cffc7fe7f

def z905 : W := mkw 0x2003cd1240000008 0x02003cd124000000 0xfffbff3ff0000000 0x0fffbff3ff000000

def z906 : W := mkw 0x0050000090098310 0x1005000009009831 0xaea88109f09f8733 0x5aea88109f09f873

def z907 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c78e0c4 0x6bbbe70c78c78e0c

def z908 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x202780f80f80fe00 0x4202780f80f80fe0

def z909 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbfffff3800000 0x8fffbfffff380000

def z910 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x06007f00001f0000 0x006007f00001f000

def z911 : W := mkw 0x1f8036ff6ff60007 0xc1f8036ff6ff6000 0xf80000ffffff0001 0xff80000ffffff000

def z912 : W := mkw 0xa3a05b0005760860 0xca3a05b000576086 0x07807f00037f19ff 0xb07807f00037f19f

def z913 : W := mkw 0x3003c9a80a80540c 0x23003c9a80a80540 0xfffffff9ff80fe0e 0xffffffff9ff80fe0

def z914 : W := mkw 0x8120061241240860 0x0812006124124086 0x95d90e36436419f5 0xb95d90e36436419f

def z915 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x7e7ffff80f9ffe0e 0xf7e7ffff80f9ffe0

def z916 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef1c7ccffe1ff 0xffffef1c7ccffe1f

def z917 : W := mkw 0x0a10304514512292 0x80a1030451451229 0x5556f1ce7ce766fc 0xa5556f1ce7ce766f

def z918 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xfffef1cffc6060c4 0x2fffef1cffc6060c

def z919 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xffa2fffff0000000 0x0ffa2fffff000000

def z920 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x07a2ff000c9b0000 0x407a2ff000c9b000

def z921 : W := mkw 0x88702457d009abf2 0x188702457d009abf 0xf80400fff000fffe 0x0f80400fff000fff

def z922 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x47fbff080fff0609 0xf47fbff080fff060

def z923 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e36436019fe 0x2ddd90e36436019f

def z924 : W := mkw 0x100000a80a805404 0x2100000a80a80540 0x783e00f80f80fe0e 0xf783e00f80f80fe0

def z925 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x27ffffc80ffffe0f 0xf27ffffc80ffffe0

def z926 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe70c78c7fe1f7 0x7bbbe70c78c7fe1f

def z927 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x939670c78c78e1c7 0x7939670c78c78e1c

def z928 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07d3ff000fff0001 0xa07d3ff000fff000

def z929 : W := mkw 0x8120061241240860 0x0812006124124086 0xdff98f36436419ff 0xbdff98f36436419f

def z930 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07ba7f000fff0001 0xf07ba7f000fff000

def z931 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x311670c78c60e0c4 0x2311670c78c60e0c

def z932 : W := mkw 0x8120061241240860 0x0812006124124086 0xd9990e36436019ff 0x3d9990e36436019f

def z933 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x07ffff000fff7805 0xf07ffff000fff780

def z934 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07ffff000fffe007 0xf07ffff000fffe00

def z935 : W := mkw 0x13d392a89fffd71c 0xf13d392a89fffd71 0x787f80f80fffff3f 0xf787f80f80fffff3

def z936 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x47ffff380ffffe0f 0xf47ffff380ffffe0

def z937 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0x07fbff000fff1839 0xf07fbff000fff183

def z938 : W := mkw 0x3c006dff60005407 0x23c006dff6000540 0xff847ffff000fe0e 0x0ff847ffff000fe0

def z939 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x111670c60c6061c7 0x3111670c60c6061c

def z940 : W := mkw 0x2c00694520000003 0x02c0069452000000 0x07807f01b0000000 0x007807f01b000000

def z941 : W := mkw 0x03d012009fffa390 0xd03d012009fffa39 0x000400000fffe7ff 0xf000400000fffe7f

def z942 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x7e7ffff9ff80fe0e 0xf7e7ffff9ff80fe0

def z943 : W := mkw 0x3383dba80576000c 0xc3383dba80576000 0x7ffbfff8007f0001 0x07ffbfff8007f000

def z944 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7a7f81f80f9bfe0e 0xf7a7f81f80f9bfe0

def z945 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xe7e3fffff0000000 0x0e7e3fffff000000

def z946 : W := mkw 0x8120061241240860 0x0812006124124086 0xfddd0ef64364f9ff 0xbfddd0ef64364f9f

def z947 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xafa87f07f0000000 0x0afa87f07f000000

def z948 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff807e0c 0xaffffffffff807e0

def z949 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78cf8e7cf 0xfbbbe70c78cf8e7c

def z950 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0xfee881fff09f0001 0xdfee881fff09f000

def z951 : W := mkw 0x1a43b0ed8ed8f58e 0xb1a43b0ed8ed8f58 0xc3c1f03f83f81fc9 0x8c3c1f03f83f81fc

def z952 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0xfffbfff9ffff0001 0xffffbfff9ffff000

def z953 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0xeffbff0ff0000000 0x0effbff0ff000000

def z954 : W := mkw 0x0050000090098310 0x1005000009009831 0x66608109f09f873b 0xd66608109f09f873

def z955 : W := mkw 0x8120061241240860 0x0812006124124086 0xdfd90f37f36419ff 0xbdfd90f37f36419f

def z956 : W := mkw 0x3003c9a80000000c 0x03003c9a80000000 0x7ffbfff8009f860b 0xd7ffbfff8009f860

def z957 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x27a6ffc80cffe601 0x427a6ffc80cffe60

def z958 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xa3be70c78c78e1c1 0x7a3be70c78c78e1c

def z959 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x3b3e70c78c78e0c6 0x73b3e70c78c78e0c

def z960 : W := mkw 0x3003c9a80000000c 0x03003c9a80000000 0xfffbfff9f0000000 0x0fffbfff9f000000

def z961 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe71c7bc7be1c7 0x7bbbe71c7bc7be1c

def z962 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x87807f00407f0131 0x087807f00407f013

def z963 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x47fbff300fff1809 0xf47fbff300fff180

def z964 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x07ffffc00fff6001 0xf07ffffc00fff600

def z965 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffbfffff3001800 0x0fffbfffff300180

def z966 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xf97bfefff0000000 0x0f97bfefff000000

def z967 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0xfffffff84fffff3f 0xffffffff84fffff3

def z968 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff00001c6 0x0fffbfffff00001c

def z969 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07ba7f00007f0001 0x007ba7f00007f000

def z970 : W := mkw 0x83701200957dabf0 0x983701200957dabf 0x000400000fffffff 0xf000400000ffffff

def z971 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xabae70c78c78e1c3 0x5abae70c78c78e1c

def z972 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xdfd9ff3ff0000000 0x0dfd9ff3ff000000

def z973 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff06401ff 0xbfffbfffff06401f

def z974 : W := mkw 0x0050000090098310 0x1005000009009831 0xcec88109f09f073b 0x9cec88109f09f073

def z975 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x27fbffc80fff0001 0xf27fbffc80fff000

def z976 : W := mkw 0xbc23edff60005c6f 0x2bc23edff60005c6 0xfffffffff000fffe 0x0fffffffff000fff

def z977 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xdfdb7ff7f0000000 0x0dfdb7ff7f000000

def z978 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xb93e70c78c60e1c6 0x7b93e70c78c60e1c

def z979 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xbbbe70c78c6061c7 0x3bbbe70c78c6061c

def z980 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e36436419f5 0x2ddd90e36436419f

def z981 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0773ff000fff0000 0xe0773ff000fff000

def z982 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07807f0000ff0001 0xd07807f0000ff000

def z983 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfaff80f98f80fe0e 0xffaff80f98f80fe0

def z984 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000ffb0000 0x607fbff000ffb000

def z985 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x7fffffc80fffe60f 0xf7fffffc80fffe60

def z986 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0223ff000f9b0000 0x40223ff000f9b000

def z987 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd98f3e736419ff 0xbddd98f3e736419f

def z988 : W := mkw 0x8120061241240860 0x0812006124124086 0xddfb0e364f6419ff 0xfddfb0e364f6419f

def z989 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xeeebfff9f0000000 0x0eeebfff9f000000

def z990 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0xcffbff004fff19ff 0xfcffbff004fff19f

def z991 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07a2ff000fff0001 0xf07a2ff000fff000

def z992 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffffffffc00fe0e 0x7fffffffffc00fe0

def z993 : W := mkw 0x2000490000000000 0x0200049000000000 0xefe8ff09f0000000 0x0efe8ff09f000000

def z994 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfcff80f84f80fe0e 0xffcff80f84f80fe0

def z995 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x113e70c60c6060c4 0x7113e70c60c6060c

def z996 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbffef1cfbcffe7c7 0xfbffef1cfbcffe7c

def z997 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07faff000cff0001 0xf07faff000cff000

def z998 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff06000c4 0x2fffbfffff06000c

def z999 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbfbe71c78c7fe1c7 0x7bfbe71c78c7fe1c

def z1000 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffffffff0007804 0x0fffffffff000780

def z1001 : W := mkw 0x23805b000ff65400 0xe23805b000ff6540 0x07847f000ffffe0f 0xf07847f000ffffe0

def z1002 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x97917f37f0000000 0x097917f37f000000

def z1003 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0663ff000fff0001 0xf0663ff000fff000

def z1004 : W := mkw 0x03d012009fffd710 0xf03d012009fffd71 0x000400000fffff3f 0xf000400000fffff3

def z1005 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07d9ff0003ff0001 0xb07d9ff0003ff000

def z1006 : W := mkw 0x2203d90004500008 0x82203d9000450000 0x07fbff000cff0001 0xf07fbff000cff000

def z1007 : W := mkw 0x3403cdba6000000d 0x03403cdba6000000 0xeffbff39f0000000 0x0effbff39f000000

def z1008 : W := mkw 0x2053c90090098318 0x12053c9009009831 0x07fbff00009f873b 0xd07fbff00009f873

def z1009 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff807804 0xfffffffffff80780

def z1010 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xddde70c64c6461ff 0xbddde70c64c6461f

def z1011 : W := mkw 0x0050000090098310 0x1005000009009831 0xfff8810ff09f873b 0xdfff8810ff09f873

def z1012 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff084873b 0xdfffbfffff084873

def z1013 : W := mkw 0x3003c9a80a80540c 0x23003c9a80a80540 0x7a7ff1f80f80fe0e 0xf7a7ff1f80f80fe0

def z1014 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff06019ff 0x3fffbfffff06019f

def z1015 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x3bbe70c60c78e0c7 0x73bbe70c60c78e0c

def z1016 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff3809e0e 0xffffbfffff3809e0

def z1017 : W := mkw 0x0c502457f0098313 0x10c502457f009831 0xe800000ff000873a 0x0e800000ff000873

def z1018 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x6fffffc80fffe60b 0xf6fffffc80fffe60

def z1019 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff06001c1 0x0fffbfffff06001c

def z1020 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07baff000cff0001 0x707baff000cff000

def z1021 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbbe70c78c60e1c7 0x7bbbe70c78c60e1c

def z1022 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfddb7efff0000000 0x0fddb7efff000000

def z1023 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x17fef1c60cff60c5 0xf17fef1c60cff60c

def z1024 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xbbbbffffb0000000 0x0bbbbffffb000000

def z1025 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x7ffffff00ffff80f 0xf7ffffff00ffff80

def z1026 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x783f00f80f00fe0e 0x7783f00f80f00fe0

def z1027 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x607f80f80f80fe08 0xf607f80f80f80fe0

def z1028 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xffd97ffff0000000 0x0ffd97ffff000000

def z1029 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x03007f00007b0000 0x003007f00007b000

def z1030 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffffffff380fe0e 0x8fffffffff380fe0

def z1031 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0x9ffbff060fff19ff 0xf9ffbff060fff19f

def z1032 : W := mkw 0xac206d5760000863 0x0ac206d576000086 0xdf807f37f00019fe 0x0df807f37f00019f

def z1033 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000fff180f 0xf07fbff000fff180

def z1034 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x5ffffff00fff780f 0xf5ffffff00fff780

def z1035 : W := mkw 0x3c03e9ed2a80540f 0x23c03e9ed2a80540 0x27ffffc9bf80e600 0xf27ffffc9bf80e60

def z1036 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbfbe71c7fcffe7ff 0xfbfbe71c7fcffe7f

def z1037 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbffef1c78cffe7ff 0xfbffef1c78cffe7f

def z1038 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff0001838 0x0fffbfffff000183

def z1039 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xc7c0ff0ff0000000 0x0c7c0ff0ff000000

def z1040 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbbe70c7cc78e1ff 0x7fbbe70c7cc78e1f

def z1041 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x37fffff80ffffe05 0xf37fffff80ffffe0

def z1042 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xb9be70c60c60e1c7 0x7b9be70c60c60e1c

def z1043 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x585f00f00f80fe0e 0xf585f00f00f80fe0

def z1044 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x47c1ff3803ff1e09 0x847c1ff3803ff1e0

def z1045 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87e8ff07f09f0001 0xd87e8ff07f09f000

def z1046 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfb33fffff0000000 0x0fb33fffff000000

def z1047 : W := mkw 0x2280590004520000 0xc228059000452000 0x07807f00001b0000 0x007807f00001b000

def z1048 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07eaff000cff0001 0xd07eaff000cff000

def z1049 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x7ffffff80fff7805 0xf7ffffff80fff780

def z1050 : W := mkw 0x0050000090098310 0x1005000009009831 0x6e688109f09f863a 0xd6e688109f09f863

def z1051 : W := mkw 0x2000490000000000 0x0200049000000000 0x87807f01f0000000 0x087807f01f000000

def z1052 : W := mkw 0x3643ddbae458a18d 0x93643ddbae458a18 0x44458f387c78e1c7 0x744458f387c78e1c

def z1053 : W := mkw 0x8120061241240860 0x0812006124124086 0xcdc90e36436419fb 0x9cdc90e36436419f

def z1054 : W := mkw 0x3c03edff6000540f 0x23c03edff6000540 0xfffffffff300fe0e 0xbfffffffff300fe0

def z1055 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x13be70c60c78e1c7 0x713be70c60c78e1c

def z1056 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x4641ff39f0000000 0x04641ff39f000000

def z1057 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xf87f80f84f80ff3e 0xff87f80f84f80ff3

def z1058 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffe71c7fc7fe1ff 0xffffe71c7fc7fe1f

def z1059 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffef1cffcfbe7c7 0x7fffef1cffcfbe7c

def z1060 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x81007e07f0000000 0x081007e07f000000

def z1061 : W := mkw 0xac206d5760000863 0x0ac206d576000086 0x87807f07f00001f0 0x087807f07f00001f

def z1062 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffbfffff0800600 0x0fffbfffff080060

def z1063 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xf9ff80fe0f80fe0e 0xff9ff80fe0f80fe0

def z1064 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xeffbff084fff873b 0xfeffbff084fff873

def z1065 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x991670c60c6061c6 0x2991670c60c6061c

def z1066 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x2622ffc9f0000000 0x02622ffc9f000000

def z1067 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbffffff000000 0x2fffbffffff00000

def z1068 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x9f987f06007f01c7 0x39f987f06007f01c

def z1069 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xdffbff304fff193f 0xfdffbff304fff193

def z1070 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x037bff000ffb0000 0xf037bff000ffb000

def z1071 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x606780f80f80fe0e 0xf606780f80f80fe0

def z1072 : W := mkw 0x3c03e9ed2a80540f 0x23c03e9ed2a80540 0x7ffffff9bf80fe0e 0xf7ffffff9bf80fe0

def z1073 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffffffffc80fe0e 0x4fffffffffc80fe0

def z1074 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0xdffbff37f0000000 0x0dffbff37f000000

def z1075 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0553ff000fff0001 0xf0553ff000fff000

def z1076 : W := mkw 0x8120061241240860 0x0812006124124086 0xdddf0ef64f6479ff 0xbdddf0ef64f6479f

def z1077 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c7ce1ff 0xfbbbe70c78c7ce1f

def z1078 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbef0cf8cf8e7c7 0x7bbbef0cf8cf8e7c

def z1079 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xbfbaffcff0000000 0x0bfbaffcff000000

def z1080 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c78e1c1 0x4bbbe70c78c78e1c

def z1081 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x595f70f60f6078ce 0xb595f70f60f6078c

def z1082 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x17fbff060fff00c5 0xf17fbff060fff00c

def z1083 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x01137e000ffb0000 0x601137e000ffb000

def z1084 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x27fbff09bfff0001 0xf27fbff09bfff000

def z1085 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff00780e 0xbffffffffff00780

def z1086 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x47fbff380fff0001 0xf47fbff380fff000

def z1087 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x07fbff000f9b0000 0xf07fbff000f9b000

def z1088 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xa3a670c78c78e1c7 0x7a3a670c78c78e1c

def z1089 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdff8efe4fe4ffff 0xffdff8efe4fe4fff

def z1090 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x6fffff080ffffe0f 0xf6fffff080ffffe0

def z1091 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x13137ff7b0000000 0x013137ff7b000000

def z1092 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7bfff0f80f80fe0e 0xf7bfff0f80f80fe0

def z1093 : W := mkw 0x9c7024fff0098b77 0x19c7024fff0098b7 0xf80000fff0009ffe 0x0f80000fff0009ff

def z1094 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfbfef0cffcf8e7ff 0xffbfef0cffcf8e7f

def z1095 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07817f00037f0001 0x007817f00037f000

def z1096 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffffffffc006004 0x2fffffffffc00600

def z1097 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xb3b670c78c78e1c5 0x6b3b670c78c78e1c

def z1098 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbfef0cf8c78e1c7 0x7fbfef0cf8c78e1c

def z1099 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x9b9e70c78c7861c7 0x39b9e70c78c7861c

def z1100 : W := mkw 0x1c5024fff009d717 0x31c5024fff009d71 0xf80400fff000ff3e 0x0f80400fff000ff3

def z1101 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbbe70cffc78e1c7 0x7fbbe70cffc78e1c

def z1102 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f9ffe0f 0xf787f80f80f9ffe0

def z1103 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xff937ffff0000000 0x0ff937ffff000000

def z1104 : W := mkw 0xb1a3cfba4ba65c6c 0x6b1a3cfba4ba65c6 0x44418f3843871e38 0x844418f3843871e3

def z1105 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x797ef0ce0ce0e6ce 0xf797ef0ce0ce0e6c

def z1106 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xa7fbffcff0000000 0x0a7fbffcff000000

def z1107 : W := mkw 0x8120061241240860 0x0812006124124086 0x59590e36036419ff 0xb59590e36036419f

def z1108 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000f9f0000 0xc07fbff000f9f000

def z1109 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbba670c78c78e1c7 0x4bba670c78c78e1c

def z1110 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87807f07f06001c1 0x087807f07f06001c

def z1111 : W := mkw 0x0300120005740000 0x8030012000574000 0x07fbff000fff0001 0xf07fbff000fff000

def z1112 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbff70f78c78e1c7 0x7fbff70f78c78e1c

def z1113 : W := mkw 0x2283d90004520008 0xc2283d9000452000 0x07fbff00001b0000 0x007fbff00001b000

def z1114 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07807f000cff0001 0x407807f000cff000

def z1115 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x781700f80f80fe0e 0xf781700f80f80fe0

def z1116 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07a0ff0000ff0001 0x407a0ff0000ff000

def z1117 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xfff9ff3ff0000000 0x0fff9ff3ff000000

def z1118 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x87fbff01f0000000 0x087fbff01f000000

def z1119 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07827f000c7f0001 0x007827f000c7f000

def z1120 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x191e70c60c6060c6 0x3191e70c60c6060c

def z1121 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x4ffbff000fff000b 0xf4ffbff000fff000

def z1122 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87ba7f07f0000000 0x087ba7f07f000000

def z1123 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07a2ff00007f0001 0x007a2ff00007f000

def z1124 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xfffb7ff7f0000000 0x0fffb7ff7f000000

def z1125 : W := mkw 0x0050000090098310 0x1005000009009831 0xfeec81c9f09fe73f 0xdfeec81c9f09fe73

def z1126 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x111670c60c7861c5 0x2111670c60c7861c

def z1127 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x7b7ffff80ffbfe0e 0xf7b7ffff80ffbfe0

def z1128 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x06ebff000f9f0001 0xd06ebff000f9f000

def z1129 : W := mkw 0x0010000010010210 0x0001000001001021 0xeee88109f09f0639 0xdeee88109f09f063

def z1130 : W := mkw 0x0c502457f0098313 0x10c502457f009831 0x80000007f0000130 0x080000007f000013

def z1131 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x31137effb0000000 0x031137effb000000

def z1132 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xffff70f7cf7cf9ff 0xfffff70f7cf7cf9f

def z1133 : W := mkw 0x1c53a4fffa89d71f 0x31c53a4fffa89d71 0xf87f80ffff80ff3e 0xff87f80ffff80ff3

def z1134 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x6ffbff080fff0001 0xf6ffbff080fff000

def z1135 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x333670c78c78e1c7 0x7333670c78c78e1c

def z1136 : W := mkw 0x038012000ff60000 0xc038012000ff6000 0x07fb7e000fff0001 0xf07fb7e000fff000

def z1137 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x7ffbfff80fff180f 0xf7ffbfff80fff180

def z1138 : W := mkw 0x3c03edff6000208f 0x03c03edff6000208 0xfffffffff00060c4 0x0fffffffff00060c

def z1139 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbf70f78f78f9c7 0x7bbbf70f78f78f9c

def z1140 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff000180e 0x0fffbfffff000180

def z1141 : W := mkw 0x2003c9000a800008 0x02003c9000a80000 0xeffbff09ff80860a 0xfeffbff09ff80860

def z1142 : W := mkw 0x2c03ed576000000b 0x02c03ed576000000 0x87c1ff07f0000000 0x087c1ff07f000000

def z1143 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x7ffffff80fffe007 0xf7ffffff80fffe00

def z1144 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfeff81f84f9fff3f 0xffeff81f84f9fff3

def z1145 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x0333ff000c9b0000 0x40333ff000c9b000

def z1146 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x6667fff9ff80fe08 0xc6667fff9ff80fe0

def z1147 : W := mkw 0x3283d9a80ed2540c 0xe3283d9a80ed2540 0x7ffffff80f9bfe0e 0xf7ffffff80f9bfe0

def z1148 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd98e3e43e41fff 0xbddd98e3e43e41ff

def z1149 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbffffff80180e 0xffffbffffff80180

def z1150 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xfffaffcff0000000 0x0fffaffcff000000

def z1151 : W := mkw 0x1c5024fff009a397 0x11c5024fff009a39 0xf80400fff000e7fe 0x0f80400fff000e7f

def z1152 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07fbff0000ff0001 0xd07fbff0000ff000

def z1153 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0x979671c7fc7f61f5 0x2979671c7fc7f61f

def z1154 : W := mkw 0x0050000090098310 0x1005000009009831 0xfee8810ff09f87ff 0xdfee8810ff09f87f

def z1155 : W := mkw 0x8120061241240860 0x0812006124124086 0x15d90e36036419ff 0xb15d90e36036419f

def z1156 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfeff81f9ff84ff3f 0xffeff81f9ff84ff3

def z1157 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x999e70c60c78e1c7 0x7999e70c60c78e1c

def z1158 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x391670c60c60e0c6 0x2391670c60c60e0c

def z1159 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfe63fffff0000000 0x0fe63fffff000000

def z1160 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x07fbff000cfb0001 0x707fbff000cfb000

def z1161 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x6fe8ff0800ff860b 0xd6fe8ff0800ff860

def z1162 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0040131 0x0fffbfffff004013

def z1163 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff09f860b 0xdfffbfffff09f860

def z1164 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff80fe08 0xcffffffffff80fe0

def z1165 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffffffff000e006 0x0fffffffff000e00

def z1166 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xdfd97f37f300180e 0xbdfd97f37f300180

def z1167 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xf91670cffc60e7fe 0x2f91670cffc60e7f

def z1168 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07927f000c7f0001 0x207927f000c7f000

def z1169 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff3001804 0x2fffbfffff300180

def z1170 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xbf807fc7f0000000 0x0bf807fc7f000000

def z1171 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff00fe0e 0x2ffffffffff00fe0

def z1172 : W := mkw 0x0050000090098310 0x1005000009009831 0xfef88109f09f873f 0xffef88109f09f873

def z1173 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef0cfccfce7ff 0xffffef0cfccfce7f

def z1174 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07e8ff000fff0001 0xf07e8ff000fff000

def z1175 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xf87f80f9ff80fe0e 0xff87f80f9ff80fe0

def z1176 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfdff80fe4fe4ffff 0xffdff80fe4fe4fff

def z1177 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xffffffffff80e006 0xfffffffffff80e00

def z1178 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x8ffbff000fff0103 0xf8ffbff000fff010

def z1179 : W := mkw 0x3783dba82ff6000d 0xc3783dba82ff6000 0x07fbff083fff0001 0xf07fbff083fff000

def z1180 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffef1cffc7fe1f7 0x7fffef1cffc7fe1f

def z1181 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x782680f80f80fe0e 0xf782680f80f80fe0

def z1182 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xf97ffeffff80fe0e 0xff97ffeffff80fe0

def z1183 : W := mkw 0x8120061241240860 0x0812006124124086 0xdd510e36436419fe 0xadd510e36436419f

def z1184 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xaffbff018fff0001 0xfaffbff018fff000

def z1185 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x797f80fe0fe0fece 0xf797f80fe0fe0fec

def z1186 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0870000 0x8fffbfffff087000

def z1187 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xefe9ff3ff0000000 0x0efe9ff3ff000000

def z1188 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x785f00f80f00fe0e 0xb785f00f80f00fe0

def z1189 : W := mkw 0x8120061241240860 0x0812006124124086 0xd9110e36436419ff 0xbd9110e36436419f

def z1190 : W := mkw 0x0050000090098310 0x1005000009009831 0xeeec8109fc9fe73f 0xfeeec8109fc9fe73

def z1191 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x111670c60c60e1c6 0x2111670c60c60e1c

def z1192 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07937f000fff0001 0xf07937f000fff000

def z1193 : W := mkw 0x2383db000ff62088 0xc2383db000ff6208 0x07ffff000fff60c5 0xf07ffff000fff60c

def z1194 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbfff7ec78c78e1c7 0x7bfff7ec78c78e1c

def z1195 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef1cffcf8e7cf 0xffffef1cffcf8e7c

def z1196 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xdffbff064fff01ff 0xfdffbff064fff01f

def z1197 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7c7f80f84f84fe3e 0xf7c7f80f84f84fe3

def z1198 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x7b7bffffb0000000 0x07b7bffffb000000

def z1199 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfffe70cffc7ce7ff 0xffffe70cffc7ce7f

def z1200 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x3337ffffbf80fe04 0x63337ffffbf80fe0

def z1201 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffffffffc00e000 0x4fffffffffc00e00

def z1202 : W := mkw 0x0000000000000000 0x0000000000000000 0x787f80f80f80fe0e 0xf787f80f80f80fe0

def z1203 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0040038 0x8fffbfffff004003

def z1204 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe70cfbc78e7c7 0x7bbbe70cfbc78e7c

def z1205 : W := mkw 0x0050000090098310 0x1005000009009831 0xeefa8109fc9f873b 0xfeefa8109fc9f873

def z1206 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07807f00037f0001 0xb07807f00037f000

def z1207 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e3643ff19ff 0xfddd90e3643ff19f

def z1208 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x07fbff00009b0000 0x407fbff00009b000

def z1209 : W := mkw 0x8120061241240860 0x0812006124124086 0xfff98f3e43ff9fff 0xffff98f3e43ff9ff

def z1210 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x97fbfff7f0000000 0x097fbfff7f000000

def z1211 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x05db7e000fff0001 0xf05db7e000fff000

def z1212 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000fff013b 0xf07fbff000fff013

def z1213 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbfef0c78cf8e1c7 0xfbbfef0c78cf8e1c

def z1214 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07937f00007f0001 0x007937f00007f000

def z1215 : W := mkw 0x8120061241240860 0x0812006124124086 0xc5c10e36436419ff 0xbc5c10e36436419f

def z1216 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff000013a 0x0fffbfffff000013

def z1217 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07e9ff0003ff0001 0xd07e9ff0003ff000

def z1218 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x939670c78c6060c4 0x2939670c78c6060c

def z1219 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07b3ff000fff0001 0x607b3ff000fff000

def z1220 : W := mkw 0x2053c90090098318 0x12053c9009009831 0xeffbff09f000873a 0x0effbff09f000873

def z1221 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c60e1c6 0x2bbbe70c78c60e1c

def z1222 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbef1cfbc78e1c7 0x7bbbef1cfbc78e1c

def z1223 : W := mkw 0x8120061241240860 0x0812006124124086 0x95910e36436419ff 0xb95910e36436419f

def z1224 : W := mkw 0x8120061241240860 0x0812006124124086 0xdddd0e364f64f9ff 0xfdddd0e364f64f9f

def z1225 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f09f8638 0xceee88109f09f863

def z1226 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x111670c60c60e0c6 0x7111670c60c60e0c

def z1227 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x707780f80f80fe0c 0xe707780f80f80fe0

def z1228 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f80fe04 0x6787f80f80f80fe0

def z1229 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x3337fff80ffbfe04 0x63337fff80ffbfe0

def z1230 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffffe0ffcf 0xfffffffffffe0ffc

def z1231 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x03137f000f7b0000 0x203137f000f7b000

def z1232 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff3001808 0x8fffbfffff300180

def z1233 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07987f00007f0001 0x307987f00007f000

def z1234 : W := mkw 0x8120061241240860 0x0812006124124086 0xdff90e36437c19ff 0xfdff90e36437c19f

def z1235 : W := mkw 0x0050000090098310 0x1005000009009831 0xfefa81c9f09f873b 0xdfefa81c9f09f873

def z1236 : W := mkw 0x0050000090098310 0x1005000009009831 0xe6e08109f09f8739 0xce6e08109f09f873

def z1237 : W := mkw 0x8120061241240860 0x0812006124124086 0xdc410e36436419ff 0xbdc410e36436419f

def z1238 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x27a2ffc9b0000000 0x027a2ffc9b000000

def z1239 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xbfbe7fc7fc00e006 0x7bfbe7fc7fc00e00

def z1240 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x505780f80f80fe0e 0xf505780f80f80fe0

def z1241 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xb7b3fffff0000000 0x0b7b3fffff000000

def z1242 : W := mkw 0x1c5024fff0098317 0x11c5024fff009831 0xf80000fff0000130 0x0f80000fff000013

def z1243 : W := mkw 0x8120061241240860 0x0812006124124086 0xddc10e36436419ff 0x8ddc10e36436419f

def z1244 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbe70c78c78e7ff 0x7bbbe70c78c78e7f

def z1245 : W := mkw 0xbc23edff6a805c6f 0x2bc23edff6a805c6 0xffffffffff80fffe 0xfffffffffff80fff

def z1246 : W := mkw 0x100000a80a805404 0x2100000a80a80540 0x785d00f80f80fe0e 0xf785d00f80f80fe0

def z1247 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x13be70c60c6060c4 0x213be70c60c6060c

def z1248 : W := mkw 0x1c53a4fff009831f 0x11c53a4fff009831 0xf87b80fff080873a 0xdf87b80fff080873

def z1249 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87807f07f0040131 0x087807f07f004013

def z1250 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07e3ff000fff0001 0xc07e3ff000fff000

def z1251 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x686f80f80f80fe0a 0xd686f80f80f80fe0

def z1252 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x67fbfff9f0000000 0x067fbfff9f000000

def z1253 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbbe70f78c78f9cf 0x7fbbe70f78c78f9c

def z1254 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfbbb7efff0000000 0x0fbbb7efff000000

def z1255 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbb3670c78c78e1c6 0x6bb3670c78c78e1c

def z1256 : W := mkw 0x0050000090098310 0x1005000009009831 0xeeee81c9fc9fe73b 0xdeeee81c9fc9fe73

def z1257 : W := mkw 0x2183cb000ba60008 0x42183cb000ba6000 0x07fbff00039f0001 0xd07fbff00039f000

def z1258 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78c7861c5 0x2bbbe70c78c7861c

def z1259 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x07ffff000fffe601 0xf07ffff000fffe60

def z1260 : W := mkw 0x0050000090098310 0x1005000009009831 0xfffe81cffcffe7ff 0xffffe81cffcffe7f

def z1261 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xfeff81f9ff9ffe0f 0xffeff81f9ff9ffe0

def z1262 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x111670c60c7860c5 0x7111670c60c7860c

def z1263 : W := mkw 0x0050000090098310 0x1005000009009831 0xefe8810ff0ff87fb 0xdefe8810ff0ff87f

def z1264 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x01007e000fff0001 0xf01007e000fff000

def z1265 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff30019fe 0xbfffbfffff30019f

def z1266 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07d97f000fff0001 0xf07d97f000fff000

def z1267 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0x3336f1cfbcfbe6c4 0x63336f1cfbcfbe6c

def z1268 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07f9ff0003ff0001 0xf07f9ff0003ff000

def z1269 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x133670c60c7860c4 0x6133670c60c7860c

def z1270 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07db7f000f7f0001 0xb07db7f000f7f000

def z1271 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x6667fff80f9ffe08 0xc6667fff80f9ffe0

def z1272 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffffffffc60e1c7 0x7fffffffffc60e1c

def z1273 : W := mkw 0x2383db0005760008 0xc2383db000576000 0x07fbff00037f0001 0xb07fbff00037f000

def z1274 : W := mkw 0x0050000090098310 0x1005000009009831 0xee608109f09f873a 0xcee608109f09f873

def z1275 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000cff0001 0x407fbff000cff000

def z1276 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xffba7ffff0000000 0x0ffba7ffff000000

def z1277 : W := mkw 0x2103cb0001240008 0x02103cb000124000 0x07fbff0003ff0001 0xf07fbff0003ff000

def z1278 : W := mkw 0x2283d9000ed20008 0xc2283d9000ed2000 0x07fbff000c9f0001 0xd07fbff000c9f000

def z1279 : W := mkw 0x8120061241240860 0x0812006124124086 0xfff98f3ff3ff19ff 0xffff98f3ff3ff19f

def z1280 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfbfef0cf8cffe7ff 0xffbfef0cf8cffe7f

def z1281 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfbbe70cffcffe7ff 0xffbbe70cffcffe7f

def z1282 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0xeffbffc9f0000000 0x0effbffc9f000000

def z1283 : W := mkw 0x8120061241240860 0x0812006124124086 0xdd910e36436419ff 0x2dd910e36436419f

def z1284 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x17977ff00f7f7805 0x217977ff00f7f780

def z1285 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e3643e49fff 0xfddd90e3643e49ff

def z1286 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x111770f60f6078c4 0x2111770f60f6078c

def z1287 : W := mkw 0x0050000090098310 0x1005000009009831 0xea208109f09f873b 0xdea208109f09f873

def z1288 : W := mkw 0x3283d9a80ed2540c 0xe3283d9a80ed2540 0x7ffffff80c9be600 0x47ffffff80c9be60

def z1289 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x2333ffc9b0000000 0x02333ffc9b000000

def z1290 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xef807f0ff0000000 0x0ef807f0ff000000

def z1291 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff36019cf 0xbfffbfffff36019c

def z1292 : W := mkw 0x2000490000000000 0x0200049000000000 0x07e8ff00009f0001 0xd07e8ff00009f000

def z1293 : W := mkw 0x8120061241240860 0x0812006124124086 0xc5d90e36436419f9 0xbc5d90e36436419f

def z1294 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xf87f80fe0f80ffce 0xff87f80fe0f80ffc

def z1295 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0333ff000fff0001 0xf0333ff000fff000

def z1296 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x03bbff000ffb0001 0x703bbff000ffb000

def z1297 : W := mkw 0x0050000090098310 0x1005000009009831 0xeff98f09f09f873b 0xdeff98f09f09f873

def z1298 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff01f0001 0x0fffbfffff01f000

def z1299 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff00419ff 0x9fffbfffff00419f

def z1300 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xf9007efff0000000 0x0f9007efff000000

def z1301 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xb99e70c78c60e1c7 0x3b99e70c78c60e1c

def z1302 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xfbfef1cfbcfbe7cf 0xffbfef1cfbcfbe7c

def z1303 : W := mkw 0x03d012009fff8310 0xd03d012009fff831 0x000000000fff8601 0xf000000000fff860

def z1304 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x783780f80f80fe0e 0x6783780f80f80fe0

def z1305 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xffffffffff00f806 0x7ffffffffff00f80

def z1306 : W := mkw 0x3c03edff6a80000f 0x03c03edff6a80000 0xfffbffffff9f0001 0xffffbffffff9f000

def z1307 : W := mkw 0x005000009009a390 0x1005000009009a39 0xeeec8109f09fe7ff 0xdeeec8109f09fe7f

def z1308 : W := mkw 0x1c0024ff60000007 0x01c0024ff6000000 0xfffb7efff0000000 0x0fffb7efff000000

def z1309 : W := mkw 0xa3a05b0005760860 0xca3a05b000576086 0x07807f00007f01f1 0x007807f00007f01f

def z1310 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f39f9f3f 0xfeee88109f39f9f3

def z1311 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xdf807f37f0000000 0x0df807f37f000000

def z1312 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef1cffc7ce1ff 0xffffef1cffc7ce1f

def z1313 : W := mkw 0x0050000090098310 0x1005000009009831 0xeec08109f09f873b 0x8eec08109f09f873

def z1314 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0800608 0x8fffbfffff080060

def z1315 : W := mkw 0x3003c9a80a80540c 0x23003c9a80a80540 0x7c7f8ff80f80fe0e 0xf7c7f8ff80f80fe0

def z1316 : W := mkw 0x8120061241240860 0x0812006124124086 0xddd90e36436419f9 0x8ddd90e36436419f

def z1317 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x119e70c60c6060c5 0x3119e70c60c6060c

def z1318 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x333670c78c6060c4 0x2333670c78c6060c

def z1319 : W := mkw 0x0050000090098310 0x1005000009009831 0xeef98109f39f873b 0xfeef98109f39f873

def z1320 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x017bfe000fff0001 0xf017bfe000fff000

def z1321 : W := mkw 0x8120061241240860 0x0812006124124086 0xddf98e3643e419ff 0xfddf98e3643e419f

def z1322 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xb91670c78c78e1c7 0x7b91670c78c78e1c

def z1323 : W := mkw 0x23805b000ff60000 0xc23805b000ff6000 0x07807f000f7f0001 0x207807f000f7f000

def z1324 : W := mkw 0x8120061241240860 0x0812006124124086 0x91110e36436019f4 0x291110e36436019f

def z1325 : W := mkw 0x3083c9a80a82540c 0x63083c9a80a82540 0x787f81f80f83fe0e 0xf787f81f80f83fe0

def z1326 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffbfffff3801e0e 0xbfffbfffff3801e0

def z1327 : W := mkw 0x0050000090098310 0x1005000009009831 0xeea08109f09f873b 0x4eea08109f09f873

def z1328 : W := mkw 0x0050000090098310 0x1005000009009831 0xfee88139f09f9f3f 0xdfee88139f09f9f3

def z1329 : W := mkw 0x0200100004500000 0x8020010000450000 0xbbbe70c60c78e1c7 0x7bbbe70c60c78e1c

def z1330 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000fff860b 0xf07fbff000fff860

def z1331 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffe70c7cc78e1c7 0x7fffe70c7cc78e1c

def z1332 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x07fbff000fff1e09 0xf07fbff000fff1e0

def z1333 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xc7fbff3ff0000000 0x0c7fbff3ff000000

def z1334 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0xa7807fcff0000000 0x0a7807fcff000000

def z1335 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x999e70c60c6060c4 0x2999e70c60c6060c

def z1336 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfffef1cf8cffe7cf 0xffffef1cf8cffe7c

def z1337 : W := mkw 0x0050000090098310 0x1005000009009831 0xfef98139f09f873b 0xdfef98139f09f873

def z1338 : W := mkw 0x03d392009fff8318 0xd03d392009fff831 0x687b80080fff873b 0xf687b80080fff873

def z1339 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0x111670c60cffe7ff 0xf111670c60cffe7f

def z1340 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x393e70c60c78e1c7 0x7393e70c60c78e1c

def z1341 : W := mkw 0xa3a3db000ff60868 0xca3a3db000ff6086 0x07fbff000fff18c5 0xf07fbff000fff18c

def z1342 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x27fbff080fff8601 0xf27fbff080fff860

def z1343 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07c17f00037f0001 0x807c17f00037f000

def z1344 : W := mkw 0x1c5024fff0098317 0x11c5024fff009831 0xf80000fff0008600 0x0f80000fff000860

def z1345 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbbbe70c78cffe1c7 0xfbbbe70c78cffe1c

def z1346 : W := mkw 0x000000000a805400 0x2000000000a80540 0x787f00f00f80fe0e 0xf787f00f00f80fe0

def z1347 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x17fbff300fff1805 0xf17fbff300fff180

def z1348 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0800000 0xdfffbfffff080000

def z1349 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffffffffc80e60a 0xdfffffffffc80e60

def z1350 : W := mkw 0x0050000090098310 0x1005000009009831 0xeff88109f0ff873b 0xfeff88109f0ff873

def z1351 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x785780f80f80fe0e 0xa785780f80f80fe0

def z1352 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f00fe0e 0x2787f80f80f00fe0

def z1353 : W := mkw 0x0050000090098310 0x1005000009009831 0xc6c08109f09f873b 0xdc6c08109f09f873

def z1354 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07a27f000c7f0001 0x407a27f000c7f000

def z1355 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xbffe70c78c7ce1c7 0xfbffe70c78c7ce1c

def z1356 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0040001 0x9fffbfffff004000

def z1357 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x383f00f00f80fe0e 0xf383f00f00f80fe0

def z1358 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff09b0000 0x4fffbfffff09b000

def z1359 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x79ff80f80fe0fe0f 0xf79ff80f80fe0fe0

def z1360 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbffef1c7fcffe1f7 0xfbffef1c7fcffe1f

def z1361 : W := mkw 0x0a00304504502082 0x80a0030450450208 0x313670c60c60e0c4 0x6313670c60c60e0c

def z1362 : W := mkw 0x0050000090098310 0x1005000009009831 0xeee88109f09f8731 0x4eee88109f09f873

def z1363 : W := mkw 0x0a00304504502082 0x80a0030450450208 0xbbbe70c78c7860c5 0x7bbbe70c78c7860c

def z1364 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x797ffef80ffffe0f 0xf797ffef80ffffe0

def z1365 : W := mkw 0x3c83edff6a82000f 0x43c83edff6a82000 0xfffbfffff0830000 0x0fffbfffff083000

def z1366 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x8780ff0ff0000000 0x08780ff0ff000000

def z1367 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0x87807f07f01f0001 0x087807f07f01f000

def z1368 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xffc1fffff0000000 0x0ffc1fffff000000

def z1369 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07d97f00007f0001 0x007d97f00007f000

def z1370 : W := mkw 0x100000a80a805404 0x2100000a80a80540 0x786c80f80f80fe0e 0xf786c80f80f80fe0

def z1371 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x87827fc7f0000000 0x087827fc7f000000

def z1372 : W := mkw 0x3383dba80ff6000c 0xc3383dba80ff6000 0x17fbfff00fff0001 0xf17fbfff00fff000

def z1373 : W := mkw 0x0050000090098310 0x1005000009009831 0x26208109f09f8630 0x426208109f09f863

def z1374 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0000103 0x1fffbfffff000010

def z1375 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdd90e3e43649fff 0xbfdd90e3e43649ff

def z1376 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0xfffffffffc80e606 0x7fffffffffc80e60

def z1377 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000f7f0001 0x207fbff000f7f000

def z1378 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x3fffffc00ffffe0f 0xf3fffffc00ffffe0

def z1379 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x3fbe7fc00c7fe007 0x73fbe7fc00c7fe00

def z1380 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x7b7fffffbf80fe0e 0xf7b7fffffbf80fe0

def z1381 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0x2663ffc9b0000000 0x02663ffc9b000000

def z1382 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0641ff00039f0000 0x80641ff00039f000

def z1383 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x87807f06007f01c1 0x087807f06007f01c

def z1384 : W := mkw 0x0a5030459459a392 0x90a5030459459a39 0xbbbef1cfbcffe7ff 0xfbbbef1cfbcffe7f

def z1385 : W := mkw 0x8120061241240860 0x0812006124124086 0xfff90e37c36419ff 0xbfff90e37c36419f

def z1386 : W := mkw 0x2383db000ff65408 0xe2383db000ff6540 0x5fffff300ffffe0f 0xf5fffff300ffffe0

def z1387 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x7773fffff0000000 0x07773fffff000000

def z1388 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0xbfffffc60fffe1c7 0xfbfffffc60fffe1c

def z1389 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x787f80f80f80fe08 0xc787f80f80f80fe0

def z1390 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0xf8ff80f80f80ff0f 0xff8ff80f80f80ff0

def z1391 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x232670c78c78e0c0 0x4232670c78c78e0c

def z1392 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x7eff81f80f80fe0e 0xf7eff81f80f80fe0

def z1393 : W := mkw 0x2c03e9452000000b 0x02c03e9452000000 0x07fbff01b0000000 0x007fbff01b000000

def z1394 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07c1ff000fff0001 0xf07c1ff000fff000

def z1395 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x93be70c78c7861c5 0x793be70c78c7861c

def z1396 : W := mkw 0x0050000090098310 0x1005000009009831 0x86808109f09f0731 0x086808109f09f073

def z1397 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x0622ff000c9f0000 0x40622ff000c9f000

def z1398 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x07fbff000fff01c7 0xf07fbff000fff01c

def z1399 : W := mkw 0x3c03e9ed2000000f 0x03c03e9ed2000000 0xbffbffcfb0000000 0x0bffbffcfb000000

def z1400 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x101700f00f80fe04 0x6101700f00f80fe0

def z1401 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x47fbff087fff0001 0xf47fbff087fff000

def z1402 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0600001 0x3fffbfffff060000

def z1403 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdfb0ef6436419ff 0xbfdfb0ef6436419f

def z1404 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xc7c17f37f0000000 0x0c7c17f37f000000

def z1405 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07917f00037f0001 0x207917f00037f000

def z1406 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xa7a0ff0ff0000000 0x0a7a0ff0ff000000

def z1407 : W := mkw 0x8120061241240860 0x0812006124124086 0x9d990e36436419f7 0x39d990e36436419f

def z1408 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff304193f 0xbfffbfffff304193

def z1409 : W := mkw 0x2003c90000000008 0x02003c9000000000 0x27fbff09b0000000 0x027fbff09b000000

def z1410 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xa7a27fc7f0000000 0x0a7a27fc7f000000

def z1411 : W := mkw 0x8120061241240860 0x0812006124124086 0xfdf98e3e436419ff 0xbfdf98e3e436419f

def z1412 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff000000a 0x9fffbfffff000000

def z1413 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x11177ef00ffffe0f 0xf11177ef00ffffe0

def z1414 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0x131670c78c7860c4 0x2131670c78c7860c

def z1415 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x03bb7e000fff0001 0xf03bb7e000fff000

def z1416 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x87fbff060fff01c1 0xf87fbff060fff01c

def z1417 : W := mkw 0x23805b0005760000 0xc23805b000576000 0x07a87f00007f0001 0x507a87f00007f000

def z1418 : W := mkw 0x2383db000ff60008 0xc2383db000ff6000 0x3ffbffc00fff0001 0xf3ffbffc00fff000

def z1419 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x7ffbfff80fff1e09 0xf7ffbfff80fff1e0

def z1420 : W := mkw 0xbc23edff6000086f 0x0bc23edff6000086 0xfffbfffff00018c4 0x0fffbfffff00018c

def z1421 : W := mkw 0x2c006d5760000003 0x02c006d576000000 0xcfc87f07f004013b 0x9cfc87f07f004013

def z1422 : W := mkw 0x100380a80a80540c 0x2100380a80a80540 0x786780f80f80fe0e 0xc786780f80f80fe0

def z1423 : W := mkw 0x3c03edff6a80540f 0x23c03edff6a80540 0x97977ff7ff007804 0x297977ff7ff00780

def z1424 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0x7e7bfff9f0000000 0x07e7bfff9f000000

def z1425 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x7ffffff80fffe601 0xf7ffffff80fffe60

def z1426 : W := mkw 0x3c03edff6000000f 0x03c03edff6000000 0xfffbfffff0808600 0x4fffbfffff080860

def z1427 : W := mkw 0x3c006dff60000007 0x03c006dff6000000 0x97807ff7f0000000 0x097807ff7f000000

def z1428 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x3ffffff00ffff807 0xf3ffffff00ffff80

def z1429 : W := mkw 0x0a4030458458a182 0x90a4030458458a18 0xfbbe70cf8c78e7cf 0x7fbbe70cf8c78e7c

def z1430 : W := mkw 0x3383dba80ff6540c 0xe3383dba80ff6540 0x07fbff080fff0601 0xf07fbff080fff060

def z1431 : W := mkw 0x0050000090098310 0x1005000009009831 0x46408109f09f0638 0x846408109f09f063

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z10,z2,z4,z5,z6])],[(0,[z11,z8,z2,z12,z4,z5,z6]),(0,[z0,z8,z2,z4,z13,z6,z14]),(1,[z0,z15,z8,z2,z5,z16])],[(0,[z17,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z19,z6]),(0,[z20,z0,z8,z2,z21,z5,z6])],[(0,[z0,z8,z22,z2,z4,z5,z6]),(0,[z0,z8,z23,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z24,z6])],[(0,[z25,z0,z26,z2,z4,z5,z6]),(0,[z27,z0,z8,z2,z4,z5,z6]),(0,[z28,z0,z29,z2,z4,z5,z6]),(0,[z17,z0,z30,z2,z4,z5,z6]),(0,[z0,z8,z2,z31,z4,z5,z6]),(0,[z0,z8,z32,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z33,z6]),(0,[z0,z8,z2,z4,z5,z6,z34])],[(0,[z0,z8,z2,z4,z35,z5,z6]),(0,[z0,z2,z36,z4,z37,z5,z6]),(0,[z0,z8,z2,z38,z39,z5,z6]),(1,[z0,z8,z2,z40,z5,z6])],[(0,[z41,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z43,z2,z42,z5,z6]),(0,[z44,z0,z8,z2,z4,z5,z6])],[(0,[z45,z8,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z3,z42,z5,z6])],[(0,[z0,z26,z2,z4,z5,z6,z14]),(0,[z0,z8,z2,z38,z42,z5,z6]),(0,[z46,z0,z8,z2,z4,z5,z6]),(0,[z47,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z48])],[(0,[z0,z26,z2,z36,z4,z5,z6]),(0,[z0,z8,z2,z12,z4,z9,z6]),(0,[z49,z0,z50,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z51,z6]),(0,[z0,z8,z2,z52,z4,z5,z6]),(0,[z0,z8,z2,z4,z53,z5,z6])],[],[(1,[z0,z29,z2,z4,z5,z6]),(0,[z0,z54,z55,z2,z4,z5,z6]),(0,[z0,z8,z2,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z56,z5,z6])],[(0,[z57,z0,z8,z58,z4,z5,z6]),(0,[z0,z8,z59,z2,z4,z5,z6]),(0,[z0,z8,z2,z60,z4,z5,z6])],[(0,[z0,z8,z61,z4,z42,z5,z6]),(0,[z0,z8,z62,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z63,z5,z6])],[(0,[z0,z8,z2,z4,z64,z5,z6]),(0,[z0,z8,z2,z39,z5,z65,z6]),(0,[z0,z8,z2,z4,z5,z6,z66])],[(0,[z0,z26,z67,z2,z4,z5,z6]),(0,[z0,z8,z61,z4,z5,z9,z6]),(0,[z0,z8,z2,z4,z68,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z69]),(0,[z0,z8,z2,z70,z4,z5,z6])]],
   [[(0,[z71,z0,z8,z2,z4,z5,z6]),(0,[z72,z0,z8,z2,z38,z4,z6]),(0,[z17,z0,z8,z2,z4,z73,z6]),(0,[z0,z50,z8,z32,z4,z5,z6])],[(0,[z74,z0,z8,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z5,z6,z75]),(0,[z0,z8,z2,z4,z5,z76,z6]),(0,[z0,z77,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z78,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z79])],[(0,[z0,z8,z2,z4,z5,z80,z6])],[(0,[z0,z8,z2,z81,z5,z82,z6])],[],[(0,[z0,z8,z2,z4,z18,z5,z6])],[(0,[z20,z0,z26,z2,z4,z5,z6])],[(0,[z20,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z83,z4,z9,z6])],[(0,[z84,z0,z1,z2,z4,z5,z6]),(0,[z0,z85,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z86,z6]),(0,[z0,z8,z2,z36,z5,z6,z16]),(0,[z0,z8,z2,z42,z42,z5,z6])],[(0,[z41,z0,z8,z2,z4,z18,z6]),(0,[z87,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z88,z4,z5,z6]),(0,[z0,z8,z43,z2,z4,z18,z6]),(0,[z89,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z90,z6])],[(0,[z0,z8,z61,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z91,z6]),(0,[z0,z8,z2,z3,z4,z18,z6]),(0,[z0,z8,z2,z42,z5,z9,z6])],[(0,[z45,z0,z26,z2,z4,z5,z6]),(0,[z45,z0,z8,z2,z4,z5,z92]),(0,[z0,z8,z2,z38,z4,z18,z6]),(1,[z0,z8,z2,z38,z93,z6])],[(0,[z0,z8,z2,z4,z94,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z95]),(0,[z0,z8,z2,z39,z5,z6,z16])],[(0,[z96,z0,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z97,z42,z5,z6]),(0,[z0,z8,z2,z98,z4,z5,z6]),(0,[z0,z8,z99,z2,z4,z100,z6]),(0,[z0,z8,z2,z101,z39,z5,z6]),(0,[z0,z8,z102,z2,z4,z5,z6])],[(0,[z0,z26,z1,z2,z4,z5,z6]),(0,[z0,z8,z61,z2,z103,z5,z6]),(0,[z0,z8,z2,z39,z97,z5,z6]),(0,[z104,z0,z8,z105,z4,z5,z6])],[(0,[z106,z0,z8,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z107,z6]),(0,[z49,z0,z8,z3,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z65,z6]),(0,[z0,z8,z2,z39,z108,z5,z6])]],
   [[(0,[z26,z8,z1,z2,z4,z5,z6]),(0,[z25,z26,z8,z2,z4,z5,z6]),(0,[z11,z0,z8,z2,z97,z5,z6]),(0,[z109,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z110])],[(1,[z26,z1,z2,z4,z5,z6]),(0,[z0,z111,z26,z2,z4,z5,z6]),(0,[z104,z0,z26,z2,z4,z5,z6]),(0,[z8,z2,z12,z4,z97,z5,z6]),(0,[z0,z112,z8,z2,z4,z5,z6]),(0,[z0,z8,z113,z4,z5,z9,z6]),(0,[z114,z0,z8,z2,z4,z5,z6])],[(0,[z11,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z115]),(0,[z0,z116,z8,z2,z4,z18,z6])],[(0,[z57,z0,z117,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z118])],[(0,[z0,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z12,z5,z93,z6]),(0,[z28,z0,z8,z2,z4,z5,z119]),(1,[z112,z8,z2,z4,z5,z6]),(0,[z0,z54,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z120])],[(0,[z0,z55,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z121,z6]),(0,[z0,z122,z8,z2,z4,z5,z6])],[(0,[z123,z0,z8,z2,z4,z5,z6]),(0,[z49,z0,z26,z2,z4,z5,z6])],[(1,[z0,z8,z2,z4,z5,z6])],[(1,[z0,z8,z2,z124,z5,z6]),(0,[z0,z125,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z126,z5,z6]),(0,[z0,z8,z2,z4,z127,z5,z6]),(0,[z128,z0,z8,z4,z42,z5,z6])],[(0,[z25,z8,z2,z58,z4,z5,z6]),(0,[z0,z129,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z130]),(0,[z20,z0,z8,z2,z4,z18,z6])],[(0,[z84,z0,z8,z58,z4,z5,z6]),(1,[z0,z8,z2,z103,z5,z6]),(0,[z0,z8,z2,z131,z4,z5,z6]),(1,[z0,z8,z2,z4,z5,z119])],[(0,[z25,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z132,z6]),(1,[z0,z8,z2,z4,z133,z6])],[(0,[z0,z1,z32,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z92,z6]),(0,[z0,z8,z2,z134,z42,z5,z6]),(0,[z0,z8,z43,z2,z4,z5,z135])],[(0,[z136,z0,z137,z2,z4,z5,z6]),(0,[z0,z8,z138,z2,z4,z5,z6])],[(0,[z0,z26,z99,z2,z4,z5,z6]),(0,[z0,z8,z2,z139,z4,z5,z6])]],
   [[(0,[z0,z8,z140,z2,z4,z5,z6]),(0,[z136,z0,z8,z2,z97,z5,z6]),(0,[z0,z8,z2,z141,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z142,z6]),(0,[z0,z143,z8,z2,z4,z5,z6])],[(0,[z17,z0,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z93,z6])],[(0,[z0,z111,z8,z2,z12,z5,z6]),(0,[z45,z8,z2,z4,z5,z92,z6]),(0,[z0,z8,z2,z144,z4,z5,z6]),(0,[z0,z8,z2,z83,z5,z93,z6])],[(0,[z0,z8,z2,z4,z145,z5,z6]),(0,[z57,z0,z8,z2,z4,z5,z146]),(0,[z0,z8,z2,z4,z147,z5,z6]),(0,[z0,z8,z2,z148,z4,z97,z6]),(0,[z0,z8,z2,z4,z18,z126,z6]),(0,[z0,z8,z2,z149,z4,z5,z6])],[(1,[z0,z150,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z151]),(0,[z0,z8,z2,z4,z152,z5,z6]),(0,[z0,z153,z2,z4,z5,z65,z6]),(0,[z0,z154,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z108,z90,z6])],[(1,[z25,z26,z2,z4,z5,z6]),(0,[z155,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z156,z6]),(0,[z0,z8,z2,z4,z73,z5,z6]),(0,[z0,z111,z8,z2,z4,z18,z6])],[(0,[z0,z8,z2,z4,z5,z6,z157]),(0,[z128,z0,z8,z2,z4,z5,z6]),(0,[z158,z0,z8,z2,z4,z18,z6]),(0,[z159,z0,z8,z2,z160,z5,z6])],[(0,[z0,z54,z8,z2,z4,z18,z6])],[(0,[z0,z50,z2,z4,z5,z6,z161]),(0,[z0,z153,z8,z2,z4,z5,z65]),(0,[z0,z8,z2,z4,z5,z6,z162]),(0,[z0,z8,z2,z4,z18,z163,z6])],[(0,[z0,z8,z2,z164,z4,z5,z6]),(0,[z0,z8,z2,z4,z108,z5,z14])],[(0,[z0,z8,z2,z4,z165,z5,z6]),(0,[z0,z8,z2,z4,z5,z166,z6]),(0,[z0,z8,z2,z4,z5,z6,z167])],[(0,[z128,z0,z8,z2,z4,z133,z6])],[(0,[z0,z168,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z37,z5,z6])],[(0,[z72,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z90,z6]),(0,[z0,z8,z2,z4,z5,z6,z169]),(0,[z170,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z171,z2,z4,z5,z6])],[],[(0,[z0,z8,z2,z4,z5,z6,z172])]],
   [[(0,[z0,z8,z99,z4,z5,z9,z6]),(0,[z173,z0,z8,z2,z4,z5,z6])],[(0,[z45,z8,z2,z58,z4,z5,z6]),(0,[z0,z8,z2,z174,z4,z5,z6])],[(0,[z0,z8,z61,z2,z39,z5,z6])],[(0,[z175,z0,z8,z2,z4,z5,z6]),(0,[z45,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z90,z92]),(0,[z0,z8,z2,z4,z5,z13,z6]),(0,[z0,z8,z2,z4,z5,z176,z6])],[(0,[z0,z1,z2,z38,z4,z5,z6]),(0,[z17,z0,z8,z2,z4,z177,z6]),(0,[z178,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z61,z2,z42,z5,z6]),(0,[z0,z179,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z180,z4,z5,z6]),(0,[z181,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z32,z4,z5,z6,z182]),(0,[z0,z183,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z184,z4,z5,z6])],[],[(0,[z185,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z186,z2,z4,z5,z6])],[(0,[z41,z0,z26,z2,z4,z5,z6]),(0,[z20,z0,z8,z4,z18,z5,z6])],[(0,[z0,z26,z2,z4,z5,z92,z6]),(0,[z104,z0,z8,z2,z4,z9,z6]),(0,[z0,z111,z8,z2,z4,z9,z6])],[],[(0,[z0,z8,z2,z4,z5,z187,z6]),(0,[z0,z8,z2,z188,z4,z5,z6]),(0,[z0,z189,z8,z2,z4,z5,z6])],[(0,[z17,z0,z8,z174,z4,z5,z6]),(1,[z128,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z4,z190,z5,z6])],[(0,[z191,z0,z8,z2,z4,z5,z6]),(0,[z192,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z6,z161]),(0,[z0,z8,z2,z4,z193,z5,z6]),(0,[z0,z8,z2,z194,z5,z166,z6])],[(0,[z0,z26,z2,z4,z97,z5,z6]),(0,[z49,z0,z8,z2,z4,z5,z195]),(0,[z49,z0,z8,z2,z4,z9,z6]),(0,[z0,z196,z8,z2,z37,z5,z6])],[(0,[z0,z8,z2,z194,z37,z5,z6]),(0,[z0,z153,z8,z2,z4,z5,z161]),(1,[z0,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z197,z4,z9,z6])]],
   [[(0,[z0,z26,z2,z39,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z6,z161]),(0,[z198,z0,z8,z2,z4,z5,z6])],[(1,[z0,z8,z2,z199,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z200]),(0,[z0,z8,z2,z4,z5,z6,z201])],[(0,[z202,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z203,z5,z6]),(1,[z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z38,z194,z5,z6])],[(0,[z0,z8,z2,z4,z204,z9,z6]),(0,[z0,z205,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z18,z6])],[(0,[z0,z206,z1,z2,z4,z5,z6]),(0,[z0,z8,z113,z2,z39,z5,z6])],[(0,[z0,z1,z2,z4,z5,z93,z6]),(0,[z0,z8,z2,z4,z207,z5,z6]),(0,[z0,z8,z2,z208,z39,z5,z6])],[],[(0,[z0,z8,z2,z4,z5,z6,z209]),(0,[z0,z8,z2,z4,z126,z9,z6]),(0,[z0,z8,z113,z2,z42,z5,z6]),(0,[z0,z8,z2,z88,z4,z18,z6])],[(0,[z0,z26,z2,z58,z4,z5,z6]),(0,[z0,z8,z61,z2,z4,z18,z6]),(1,[z0,z8,z2,z4,z210,z6]),(0,[z0,z8,z2,z4,z5,z211,z6])],[(1,[z0,z8,z212,z4,z5,z6]),(0,[z0,z8,z2,z213,z4,z5,z6]),(0,[z17,z0,z8,z2,z4,z9,z6]),(0,[z214,z0,z8,z2,z4,z5,z6])],[(1,[z0,z8,z2,z4,z5,z215]),(0,[z216,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z32,z2,z4,z9,z6]),(0,[z0,z217,z8,z2,z37,z5,z6]),(0,[z0,z8,z218,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z182]),(0,[z0,z8,z2,z4,z5,z219,z6]),(0,[z0,z8,z220,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z221,z6])],[(0,[z28,z72,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z166,z6]),(0,[z0,z8,z2,z4,z108,z13,z6]),(0,[z128,z0,z8,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z5,z222,z6]),(0,[z0,z154,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z223,z5,z6]),(0,[z114,z0,z8,z2,z4,z18,z6])]],
   [[(0,[z224,z0,z8,z2,z4,z5,z6]),(0,[z0,z2,z4,z126,z5,z13,z6]),(0,[z0,z153,z8,z2,z4,z5,z6])],[(0,[z128,z0,z8,z2,z42,z5,z6])],[(0,[z0,z8,z1,z2,z39,z5,z6]),(0,[z49,z0,z8,z2,z4,z5,z225]),(0,[z0,z8,z3,z4,z5,z6,z182]),(0,[z0,z8,z2,z4,z5,z6,z226])],[(0,[z57,z0,z8,z2,z4,z227,z6]),(0,[z28,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z228,z6]),(1,[z0,z8,z186,z4,z5,z6])],[(0,[z0,z55,z8,z2,z4,z13,z6])],[(0,[z0,z26,z2,z4,z229,z5,z6]),(0,[z0,z8,z2,z4,z230,z5,z6]),(0,[z0,z8,z2,z4,z9,z65,z6]),(1,[z0,z8,z2,z4,z18,z6])],[(0,[z0,z8,z2,z4,z5,z231,z6]),(0,[z0,z54,z26,z2,z4,z5,z6]),(1,[z0,z8,z232,z4,z5,z6]),(0,[z0,z8,z233,z2,z4,z5,z6])],[(0,[z0,z8,z2,z234,z4,z5,z6]),(0,[z28,z8,z2,z4,z5,z82,z6]),(0,[z0,z8,z2,z4,z235,z5,z6]),(1,[z0,z30,z2,z4,z5,z6]),(1,[z0,z8,z2,z18,z42,z6]),(0,[z0,z8,z2,z4,z236,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z14])],[(0,[z28,z0,z111,z8,z2,z4,z6]),(0,[z237,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z36,z4,z5,z6])],[(0,[z0,z8,z32,z2,z238,z5,z6]),(0,[z0,z8,z2,z239,z4,z5,z6])],[(0,[z240,z0,z26,z2,z4,z5,z6]),(1,[z0,z8,z2,z234,z5,z6]),(0,[z0,z241,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z82,z6]),(0,[z0,z8,z2,z39,z5,z135,z6])],[(0,[z0,z26,z2,z4,z5,z6,z161]),(0,[z20,z0,z8,z61,z4,z5,z6]),(0,[z0,z54,z2,z4,z126,z5,z6])],[(1,[z241,z8,z2,z4,z5,z6])],[(0,[z0,z8,z67,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z227,z6]),(0,[z0,z8,z2,z4,z5,z242,z6])],[(0,[z0,z8,z2,z4,z243,z5,z6]),(0,[z0,z8,z113,z2,z4,z5,z6])]],
   [[(0,[z41,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z208,z4,z5,z6]),(0,[z0,z8,z2,z4,z244,z5,z6]),(0,[z0,z8,z2,z245,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z75]),(0,[z0,z8,z43,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z18,z6,z16]),(0,[z0,z8,z2,z4,z5,z6,z246])],[(0,[z0,z8,z2,z3,z4,z9,z6]),(0,[z0,z8,z2,z42,z126,z5,z6]),(0,[z104,z0,z8,z149,z4,z5,z6])],[(0,[z11,z0,z247,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z248,z6]),(0,[z0,z8,z2,z38,z4,z9,z6]),(0,[z0,z8,z43,z2,z249,z5,z6])],[(0,[z0,z250,z1,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z73,z6]),(0,[z251,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z252]),(0,[z0,z8,z99,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z9,z6,z16]),(0,[z0,z8,z2,z21,z4,z5,z6]),(0,[z0,z253,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z254,z4,z5,z6]),(0,[z128,z0,z8,z2,z4,z18,z6])],[(0,[z0,z8,z2,z255,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z51,z6]),(0,[z0,z8,z2,z4,z5,z6,z256])],[(0,[z0,z117,z8,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z5,z257,z6])],[(0,[z0,z8,z212,z2,z4,z5,z6]),(0,[z0,z258,z8,z2,z4,z5,z6])],[(0,[z0,z50,z8,z2,z4,z5,z6]),(0,[z0,z259,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z5,z166,z6,z16])],[(0,[z0,z8,z2,z4,z37,z18,z6])],[(0,[z57,z0,z8,z2,z4,z91,z6]),(0,[z0,z8,z2,z260,z4,z5,z6])],[(0,[z261,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z18,z5,z6]),(0,[z0,z8,z2,z4,z262,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z263]),(0,[z0,z15,z8,z2,z5,z6,z16])],[(0,[z0,z8,z1,z2,z4,z5,z6]),(0,[z264,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z265,z4,z5,z6]),(0,[z0,z266,z8,z2,z4,z5,z6]),(1,[z7,z0,z8,z2,z4,z14])],[(0,[z0,z196,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z24,z6])],[(0,[z8,z2,z4,z5,z92,z6,z75]),(0,[z0,z8,z2,z236,z42,z5,z6])]],
   [[(0,[z0,z8,z2,z4,z267,z5,z6]),(0,[z0,z196,z2,z4,z37,z5,z6]),(1,[z0,z8,z2,z21,z5,z6]),(0,[z0,z8,z2,z4,z268,z5,z6])],[(0,[z0,z1,z61,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z5,z65,z6]),(0,[z20,z0,z8,z2,z4,z9,z6])],[(0,[z0,z269,z8,z2,z4,z5,z6]),(0,[z216,z0,z8,z2,z39,z5,z6])],[(0,[z0,z8,z2,z83,z38,z4,z6])],[(0,[z0,z270,z8,z2,z4,z5,z6]),(0,[z0,z8,z271,z2,z4,z5,z6])],[(0,[z0,z8,z2,z42,z5,z90,z6])],[(0,[z0,z8,z2,z4,z272,z5,z6]),(0,[z0,z8,z2,z4,z108,z82,z6]),(0,[z0,z273,z8,z2,z4,z5,z6]),(0,[z0,z274,z8,z2,z4,z5,z6]),(0,[z275,z0,z8,z2,z4,z5,z6])],[(1,[z0,z276,z2,z4,z5,z6]),(0,[z0,z150,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z277,z4,z5,z6]),(0,[z0,z153,z8,z2,z39,z5,z6]),(0,[z0,z278,z8,z2,z4,z5,z6])],[(0,[z136,z0,z8,z2,z83,z5,z6]),(0,[z49,z0,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z4,z100,z5,z6]),(0,[z0,z8,z2,z4,z108,z5,z90])],[(0,[z0,z8,z2,z4,z279,z5,z6]),(0,[z280,z0,z8,z2,z4,z5,z6]),(0,[z159,z0,z8,z2,z39,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z14]),(0,[z0,z217,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z281,z6]),(0,[z28,z0,z8,z2,z39,z5,z6]),(0,[z0,z153,z8,z2,z42,z5,z6])],[(0,[z0,z8,z2,z4,z5,z146,z6]),(0,[z282,z0,z8,z2,z4,z5,z6]),(0,[z0,z283,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z284,z4,z5,z6])],[(0,[z0,z8,z285,z2,z4,z5,z6]),(1,[z0,z8,z2,z39,z18,z6]),(0,[z0,z8,z2,z38,z5,z93,z6]),(0,[z0,z8,z2,z286,z4,z5,z6])],[(0,[z28,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z135,z75]),(0,[z0,z54,z8,z2,z4,z9,z6]),(0,[z0,z8,z99,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z82,z6]),(0,[z0,z26,z2,z4,z5,z6,z16]),(0,[z0,z8,z2,z287,z4,z5,z6])]],
   [[(0,[z0,z288,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z36,z39,z5,z6]),(0,[z0,z8,z2,z4,z5,z204,z6]),(0,[z0,z111,z8,z2,z38,z5,z6])],[(0,[z0,z0,z26,z2,z4,z5,z6]),(1,[z0,z8,z2,z289,z5,z6]),(1,[z0,z8,z105,z4,z5,z6])],[(0,[z0,z26,z2,z4,z108,z5,z6]),(0,[z0,z290,z8,z2,z4,z5,z6])],[(0,[z0,z1,z113,z2,z4,z5,z6]),(0,[z0,z8,z2,z291,z4,z5,z6]),(0,[z0,z8,z2,z36,z42,z5,z6]),(0,[z292,z0,z8,z2,z4,z5,z6])],[(1,[z0,z26,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z75]),(0,[z0,z8,z2,z39,z39,z5,z6])],[(0,[z293,z0,z8,z2,z4,z5,z6]),(0,[z294,z0,z8,z2,z4,z5,z6]),(0,[z295,z0,z8,z2,z4,z5,z6])],[(0,[z28,z0,z8,z2,z4,z5,z215]),(1,[z0,z8,z2,z194,z5,z166])],[(1,[z1,z2,z4,z5,z6,z75]),(0,[z0,z8,z2,z296,z4,z5,z6]),(0,[z0,z26,z2,z297,z4,z5,z6]),(0,[z0,z8,z298,z2,z4,z5,z6]),(1,[z0,z8,z2,z299,z5,z6])],[],[(0,[z0,z8,z61,z4,z5,z6,z182]),(1,[z0,z8,z131,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z75,z182]),(0,[z49,z0,z8,z2,z4,z262,z6]),(0,[z0,z8,z2,z39,z5,z9,z6])],[(0,[z0,z1,z2,z4,z145,z5,z6]),(0,[z0,z8,z2,z300,z4,z5,z6]),(0,[z301,z0,z8,z2,z4,z5,z6])],[(1,[z57,z8,z58,z4,z5,z6])],[(0,[z0,z8,z2,z302,z42,z5,z6])],[(1,[z0,z8,z2,z303,z5,z6]),(0,[z84,z8,z61,z2,z4,z5,z6]),(0,[z304,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z93,z6]),(1,[z0,z8,z4,z305,z5,z6])],[(0,[z0,z8,z2,z4,z306,z5,z6]),(0,[z0,z8,z2,z4,z5,z307,z6]),(0,[z0,z8,z2,z4,z82,z93,z6]),(0,[z308,z0,z8,z2,z4,z5,z6]),(0,[z0,z153,z8,z2,z4,z18,z6])],[(1,[z136,z8,z2,z97,z5,z6])]],
   [[(0,[z0,z8,z2,z4,z163,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z309,z8,z2,z4,z5,z6]),(1,[z0,z310,z2,z4,z5,z6]),(0,[z28,z0,z8,z2,z4,z18,z6]),(0,[z0,z50,z8,z2,z39,z5,z6]),(0,[z0,z8,z4,z42,z5,z9,z6]),(0,[z0,z8,z2,z4,z18,z6,z311]),(0,[z0,z8,z2,z4,z5,z6,z312])],[(0,[z0,z8,z2,z97,z5,z93,z6]),(0,[z0,z8,z2,z4,z5,z313,z6])],[(0,[z0,z1,z2,z4,z37,z5,z6]),(0,[z128,z0,z26,z2,z4,z5,z6])],[(0,[z72,z0,z8,z2,z4,z82,z6]),(0,[z0,z8,z2,z314,z4,z5,z6]),(0,[z0,z50,z8,z2,z42,z5,z6]),(0,[z0,z259,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z42,z5,z6,z182]),(1,[z159,z0,z8,z4,z5,z182]),(0,[z0,z8,z2,z4,z5,z315,z6])],[(0,[z0,z8,z2,z4,z316,z5,z6]),(0,[z159,z0,z8,z2,z4,z5,z6])],[(0,[z136,z0,z8,z2,z39,z5,z6]),(0,[z28,z0,z8,z2,z234,z5,z6]),(0,[z0,z317,z8,z2,z4,z5,z6]),(0,[z318,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z36,z4,z18,z6]),(0,[z20,z0,z8,z113,z4,z5,z6]),(0,[z0,z319,z8,z2,z4,z5,z6])],[(0,[z84,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z166,z92]),(0,[z0,z320,z8,z2,z4,z5,z6])],[(0,[z321,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z1,z2,z42,z5,z6]),(0,[z0,z8,z61,z2,z4,z147,z6]),(0,[z17,z0,z8,z2,z230,z5,z6]),(0,[z0,z8,z2,z4,z5,z92,z6]),(0,[z0,z322,z8,z2,z4,z5,z6]),(0,[z7,z0,z8,z2,z4,z108,z6])],[],[(0,[z0,z1,z2,z4,z5,z13,z6]),(0,[z0,z323,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z324,z6]),(0,[z0,z8,z2,z4,z18,z9,z6]),(1,[z0,z111,z8,z2,z83,z6])],[(0,[z325,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z326,z5,z6]),(0,[z327,z0,z8,z2,z4,z5,z6])],[(0,[z0,z26,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z328]),(0,[z0,z269,z8,z2,z42,z5,z6]),(0,[z0,z8,z113,z2,z4,z18,z6])],[(0,[z0,z8,z2,z4,z329,z5,z6]),(0,[z8,z2,z4,z203,z5,z82,z6]),(0,[z330,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z186,z38,z4,z5,z6])],[(0,[z0,z8,z61,z2,z4,z9,z6]),(0,[z49,z0,z8,z2,z4,z331,z6]),(0,[z0,z8,z2,z39,z4,z5,z6]),(1,[z0,z8,z4,z42,z9,z6])]],
   [[(0,[z0,z332,z8,z2,z4,z5,z6]),(0,[z57,z0,z8,z2,z39,z5,z6]),(0,[z333,z0,z8,z2,z4,z5,z6]),(0,[z0,z153,z50,z2,z4,z5,z6]),(0,[z334,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z335,z5,z6]),(0,[z11,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z336]),(0,[z0,z273,z8,z2,z42,z5,z6])],[(0,[z0,z1,z99,z2,z4,z5,z6])],[(0,[z7,z0,z8,z2,z4,z5,z14])],[(0,[z337,z0,z8,z2,z4,z5,z6]),(0,[z0,z55,z8,z2,z4,z5,z6]),(0,[z0,z338,z8,z2,z4,z5,z6])],[(1,[z0,z8,z2,z4,z147,z6])],[(0,[z0,z8,z2,z4,z5,z339,z6]),(0,[z0,z8,z2,z4,z340,z5,z6])],[(0,[z0,z8,z2,z58,z4,z5,z6]),(0,[z0,z50,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z6,z341]),(0,[z0,z8,z2,z4,z342,z5,z6]),(1,[z0,z8,z2,z4,z343,z6]),(1,[z0,z8,z2,z344,z5,z6])],[(0,[z0,z8,z2,z4,z91,z5,z6]),(0,[z8,z61,z2,z58,z4,z5,z6]),(0,[z0,z8,z2,z345,z4,z5,z6])],[(0,[z0,z1,z2,z4,z203,z5,z6]),(0,[z0,z217,z2,z36,z4,z5,z6]),(0,[z0,z8,z99,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z346,z5,z6]),(0,[z0,z8,z347,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z348])],[(0,[z0,z8,z2,z4,z5,z92,z16]),(0,[z0,z8,z105,z2,z4,z5,z6])],[(0,[z0,z8,z1,z2,z4,z18,z6]),(0,[z0,z8,z2,z349,z4,z5,z6])],[(1,[z0,z26,z2,z39,z5,z6]),(0,[z0,z8,z137,z2,z4,z5,z6]),(0,[z11,z0,z8,z2,z83,z5,z6]),(0,[z17,z0,z317,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z5,z195]),(0,[z0,z8,z2,z4,z350,z5,z6]),(0,[z0,z8,z2,z4,z126,z108,z6]),(0,[z0,z8,z113,z2,z344,z5,z6]),(1,[z0,z8,z2,z4,z9,z6])],[],[(0,[z11,z0,z150,z2,z4,z5,z6]),(0,[z0,z8,z351,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z352,z5,z6]),(0,[z353,z0,z8,z2,z4,z5,z6]),(1,[z0,z8,z2,z249,z5,z6])],[(1,[z0,z26,z2,z42,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z161]),(0,[z0,z8,z2,z354,z4,z5,z6]),(0,[z0,z8,z2,z4,z355,z5,z6]),(0,[z0,z8,z2,z4,z18,z135,z6])]],
   [[(0,[z0,z8,z2,z194,z97,z5,z6]),(1,[z17,z8,z2,z4,z5,z75]),(0,[z294,z0,z8,z2,z42,z5,z6])],[(0,[z136,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z356,z2,z4,z5,z6]),(0,[z357,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z113,z2,z4,z9,z6]),(0,[z0,z8,z2,z160,z4,z5,z6]),(0,[z0,z8,z2,z358,z4,z5,z6])],[(0,[z0,z8,z359,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z135,z6])],[(0,[z0,z8,z360,z2,z4,z5,z6]),(0,[z361,z0,z8,z2,z4,z5,z6]),(0,[z0,z362,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z229,z5,z6])],[(0,[z25,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z363,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z222,z6]),(0,[z364,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z365,z4,z5,z6])],[(1,[z0,z8,z2,z366,z5,z6]),(0,[z0,z8,z2,z4,z5,z75,z14]),(0,[z0,z196,z217,z2,z4,z5,z6])],[(1,[z45,z8,z2,z4,z5,z92]),(0,[z0,z367,z8,z2,z4,z5,z6]),(0,[z368,z0,z8,z2,z4,z5,z6])],[(1,[z0,z8,z2,z238,z5,z6])],[(0,[z57,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z161]),(0,[z128,z0,z8,z2,z4,z9,z6]),(1,[z0,z8,z42,z5,z9,z6]),(0,[z0,z8,z2,z4,z5,z6,z369])],[(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z370,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z99,z2,z4,z18,z6]),(0,[z0,z15,z8,z2,z4,z5,z6])],[(0,[z0,z8,z247,z2,z4,z5,z6])],[(0,[z0,z8,z2,z371,z4,z5,z6]),(0,[z372,z0,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z36,z4,z5,z6]),(0,[z0,z8,z373,z2,z4,z5,z6]),(0,[z84,z0,z8,z2,z39,z5,z6]),(0,[z0,z374,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z228,z6])]],
   [[(0,[z28,z0,z26,z2,z4,z5,z6]),(0,[z0,z8,z58,z4,z5,z9,z6]),(0,[z375,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z376]),(1,[z0,z8,z2,z4,z5,z225]),(0,[z0,z32,z2,z3,z4,z5,z6]),(0,[z159,z0,z8,z2,z42,z5,z6]),(0,[z0,z377,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z37,z9,z6]),(0,[z0,z8,z2,z378,z4,z5,z6])],[(0,[z0,z26,z2,z12,z4,z5,z6]),(1,[z0,z26,z2,z4,z18,z6]),(0,[z57,z84,z8,z2,z4,z5,z6]),(0,[z84,z0,z8,z2,z42,z5,z6]),(1,[z0,z379,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z203,z6]),(0,[z0,z55,z8,z2,z4,z126,z6])],[(0,[z0,z1,z2,z39,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z380,z6]),(0,[z0,z8,z2,z42,z5,z6,z14])],[(0,[z381,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z82,z6,z14]),(0,[z104,z0,z8,z2,z382,z5,z6])],[(0,[z383,z0,z8,z2,z4,z5,z6]),(0,[z0,z26,z8,z2,z39,z5,z6]),(0,[z28,z0,z8,z131,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z257,z6]),(1,[z11,z8,z2,z12,z5,z6]),(0,[z0,z8,z2,z4,z5,z5,z6]),(0,[z384,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z42,z5,z82,z6]),(0,[z0,z385,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z386,z6])],[(0,[z0,z387,z8,z2,z4,z5,z6]),(0,[z0,z26,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z388])],[(0,[z11,z0,z8,z2,z39,z5,z6]),(0,[z17,z0,z8,z62,z4,z5,z6])],[(1,[z0,z8,z2,z81,z5,z6]),(0,[z0,z8,z2,z39,z42,z5,z6]),(0,[z389,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z390])],[(0,[z0,z8,z2,z4,z5,z133,z6])],[(0,[z45,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z11,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z6]),(0,[z0,z8,z2,z42,z5,z6,z75]),(0,[z0,z55,z8,z2,z39,z5,z6])],[(0,[z391,z0,z8,z2,z4,z5,z6]),(0,[z392,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z36,z194,z5,z6]),(0,[z393,z0,z8,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z5,z135,z6]),(0,[z0,z15,z8,z2,z4,z5,z16])],[(0,[z0,z8,z2,z58,z39,z5,z6]),(0,[z45,z0,z171,z2,z4,z5,z6]),(0,[z0,z50,z8,z3,z4,z5,z6]),(0,[z0,z55,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z63,z5,z6])]],
   [[(0,[z0,z8,z2,z4,z5,z394,z6]),(0,[z0,z8,z2,z4,z5,z65,z6])],[(0,[z0,z8,z2,z12,z5,z6,z16])],[(0,[z104,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z58,z42,z5,z6])],[(1,[z104,z0,z2,z4,z5,z161]),(0,[z0,z8,z2,z4,z395,z5,z6]),(0,[z159,z0,z8,z2,z4,z18,z6])],[(1,[z0,z8,z149,z4,z5,z6]),(1,[z0,z8,z2,z39,z9,z6]),(0,[z0,z8,z2,z396,z4,z5,z6])],[(0,[z84,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z397,z6])],[(0,[z0,z8,z2,z4,z5,z398,z6]),(0,[z0,z8,z2,z399,z4,z5,z6])],[(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z400,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z203,z9,z6]),(0,[z0,z8,z401,z2,z4,z5,z6]),(0,[z0,z8,z2,z37,z5,z6,z16]),(1,[z0,z8,z2,z42,z9,z6])],[],[(0,[z0,z8,z2,z402,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z166,z6])],[(0,[z0,z8,z2,z148,z4,z5,z6]),(0,[z0,z8,z2,z39,z12,z5,z6]),(1,[z0,z8,z2,z4,z177,z6]),(0,[z403,z0,z8,z2,z4,z5,z6])],[(0,[z136,z0,z26,z2,z4,z5,z6]),(0,[z0,z26,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z404,z4,z5,z6]),(0,[z0,z8,z405,z2,z4,z5,z6])],[(0,[z136,z0,z8,z2,z42,z5,z6]),(0,[z406,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z267,z5,z6])],[(1,[z0,z407,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z4,z18,z6])],[(0,[z0,z408,z1,z2,z4,z5,z6]),(1,[z0,z8,z2,z35,z5,z6]),(0,[z0,z8,z2,z4,z5,z409,z6]),(1,[z20,z0,z8,z42,z5,z6]),(1,[z0,z8,z2,z4,z410,z6]),(0,[z0,z8,z2,z4,z5,z411,z6]),(0,[z0,z8,z2,z4,z5,z6,z16])],[(0,[z11,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z412,z2,z4,z5,z6]),(0,[z0,z8,z2,z83,z5,z6,z16])]],
   [[(0,[z0,z8,z2,z4,z97,z5,z6]),(0,[z0,z8,z2,z39,z126,z5,z6]),(0,[z0,z8,z2,z4,z9,z9,z6]),(0,[z0,z8,z2,z4,z5,z6,z413])],[(1,[z84,z8,z61,z4,z5,z6]),(0,[z28,z0,z8,z414,z4,z5,z6]),(0,[z415,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z142,z6]),(0,[z0,z8,z43,z2,z4,z416,z6]),(0,[z0,z111,z8,z2,z4,z108,z6]),(0,[z0,z8,z2,z4,z108,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z417])],[(0,[z17,z0,z1,z2,z4,z5,z6]),(0,[z0,z26,z2,z194,z4,z5,z6]),(0,[z57,z0,z8,z2,z289,z5,z6]),(0,[z136,z11,z8,z2,z4,z5,z6]),(1,[z0,z8,z174,z4,z5,z6]),(0,[z0,z55,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z42,z5,z13,z6])],[(0,[z0,z8,z2,z418,z4,z5,z6]),(0,[z84,z8,z2,z4,z5,z6,z75]),(0,[z136,z0,z8,z212,z4,z5,z6]),(1,[z0,z270,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z419])],[(0,[z0,z15,z8,z2,z39,z5,z6]),(0,[z0,z8,z43,z2,z4,z5,z182])],[(0,[z0,z8,z2,z58,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z6,z420]),(0,[z0,z153,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z421,z42,z5,z6]),(0,[z422,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z423,z6]),(0,[z0,z8,z2,z297,z4,z5,z6]),(0,[z57,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z424,z4,z5,z6]),(0,[z104,z0,z153,z2,z4,z5,z6]),(0,[z0,z8,z4,z5,z135,z6,z182])],[(0,[z0,z26,z2,z425,z4,z5,z6]),(0,[z0,z426,z8,z2,z4,z5,z6]),(0,[z427,z0,z8,z2,z4,z5,z6]),(0,[z0,z15,z8,z2,z42,z5,z6]),(0,[z159,z0,z8,z2,z4,z5,z135]),(0,[z0,z8,z2,z428,z4,z5,z6])],[(1,[z0,z8,z414,z4,z5,z6]),(0,[z28,z0,z8,z2,z4,z9,z6]),(0,[z0,z377,z8,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z429,z5,z6]),(1,[z0,z430,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z431]),(0,[z0,z432,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z433]),(0,[z0,z8,z2,z4,z5,z92,z135])],[(0,[z0,z8,z434,z2,z4,z5,z6])],[(0,[z7,z0,z8,z2,z4,z6,z14]),(1,[z0,z8,z2,z4,z108,z90])],[(0,[z0,z435,z1,z2,z4,z5,z6]),(0,[z0,z26,z50,z2,z4,z5,z6]),(0,[z0,z436,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z36,z4,z9,z6]),(0,[z0,z8,z437,z2,z4,z5,z6])],[(0,[z0,z1,z2,z296,z4,z5,z6]),(0,[z57,z0,z8,z2,z303,z5,z6]),(0,[z438,z0,z8,z2,z4,z5,z6]),(0,[z439,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z440,z6])],[(0,[z136,z0,z8,z2,z4,z18,z6]),(0,[z45,z0,z8,z2,z4,z5,z75]),(0,[z0,z8,z2,z4,z18,z441,z6])]],
   [[(0,[z84,z8,z1,z2,z4,z5,z6]),(0,[z136,z0,z8,z232,z4,z5,z6])],[(0,[z0,z8,z2,z42,z203,z5,z6]),(0,[z0,z8,z2,z4,z442,z5,z6]),(1,[z20,z0,z8,z4,z18,z6])],[(0,[z0,z387,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z443,z6]),(0,[z0,z8,z2,z4,z5,z6,z444])],[(1,[z0,z8,z2,z4,z5,z445])],[],[(0,[z0,z8,z2,z4,z5,z446,z6])],[(0,[z0,z8,z2,z447,z4,z5,z6]),(0,[z0,z8,z2,z4,z448,z5,z6]),(0,[z0,z8,z2,z4,z5,z449,z6])],[(0,[z8,z1,z2,z4,z5,z6,z75]),(0,[z0,z8,z2,z4,z5,z6,z450]),(1,[z0,z8,z2,z4,z262,z6]),(0,[z0,z8,z2,z4,z5,z210,z6])],[(0,[z0,z8,z2,z4,z5,z6,z451]),(0,[z391,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z39,z4,z42,z5,z6])],[(0,[z41,z0,z1,z2,z4,z5,z6]),(0,[z57,z0,z8,z2,z4,z18,z6]),(0,[z0,z452,z8,z2,z4,z5,z6]),(0,[z0,z453,z8,z2,z4,z5,z6]),(0,[z0,z15,z8,z2,z4,z5,z166])],[(0,[z454,z0,z8,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z42,z5,z6]),(0,[z0,z455,z8,z2,z4,z5,z6]),(0,[z0,z15,z8,z2,z4,z18,z6])],[],[(0,[z0,z26,z2,z4,z5,z9,z6]),(0,[z0,z456,z8,z2,z4,z5,z6])],[],[(0,[z0,z8,z99,z61,z4,z5,z6]),(0,[z28,z0,z379,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z457,z5,z6]),(0,[z0,z50,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z238,z4,z5,z6])],[(0,[z0,z458,z8,z2,z4,z5,z6]),(0,[z72,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z215]),(0,[z0,z8,z2,z4,z5,z459,z6]),(0,[z460,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z461,z5,z6]),(0,[z0,z111,z8,z2,z4,z93,z6])]],
   [[(0,[z0,z8,z2,z462,z4,z5,z6])],[(0,[z0,z8,z463,z2,z4,z5,z6]),(0,[z0,z8,z58,z4,z42,z5,z6]),(0,[z464,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z465,z6]),(0,[z0,z8,z2,z4,z221,z5,z6])],[(0,[z0,z8,z1,z2,z4,z9,z6]),(0,[z159,z0,z26,z2,z4,z5,z6]),(0,[z466,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z467,z4,z5,z6])],[(0,[z0,z8,z2,z366,z4,z5,z6]),(0,[z0,z468,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z97,z5,z6]),(0,[z84,z0,z26,z2,z4,z5,z6]),(0,[z72,z0,z111,z8,z2,z4,z6])],[(0,[z0,z1,z2,z4,z108,z5,z6]),(1,[z0,z8,z61,z42,z5,z6]),(0,[z17,z0,z8,z2,z4,z5,z75]),(0,[z159,z0,z8,z2,z299,z5,z6])],[(1,[z468,z8,z2,z4,z5,z6])],[(0,[z0,z323,z26,z2,z4,z5,z6]),(0,[z0,z8,z61,z2,z4,z469,z6]),(0,[z0,z8,z2,z83,z4,z82,z6]),(0,[z0,z8,z2,z18,z42,z5,z6]),(0,[z0,z8,z2,z39,z5,z470,z6])],[(0,[z471,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z472]),(0,[z0,z8,z2,z4,z473,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z474]),(1,[z0,z8,z2,z4,z316,z6]),(0,[z0,z8,z2,z4,z5,z475,z6])],[(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z0,z26,z26,z2,z4,z5,z6]),(0,[z0,z8,z412,z2,z42,z5,z6]),(0,[z20,z0,z8,z99,z4,z5,z6]),(0,[z0,z8,z2,z38,z4,z108,z6])],[],[(0,[z0,z476,z1,z2,z4,z5,z6]),(0,[z0,z8,z43,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z40,z5,z6])],[(0,[z0,z332,z26,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z331,z6]),(0,[z0,z477,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z58,z4,z5,z6]),(0,[z11,z0,z26,z2,z4,z5,z6]),(1,[z0,z22,z2,z4,z5,z6]),(0,[z0,z8,z99,z2,z4,z343,z6]),(1,[z0,z8,z2,z4,z190,z6])],[(1,[z0,z8,z2,z4,z478,z6]),(0,[z0,z8,z2,z479,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z480]),(0,[z0,z8,z2,z4,z5,z6,z311])]],
   [[(0,[z0,z481,z8,z2,z4,z5,z6]),(0,[z28,z0,z8,z2,z4,z203,z6]),(0,[z0,z8,z2,z482,z4,z5,z6]),(0,[z483,z0,z8,z2,z4,z5,z6])],[(1,[z1,z2,z58,z4,z5,z6]),(0,[z0,z55,z26,z2,z4,z5,z6]),(0,[z84,z0,z310,z2,z4,z5,z6]),(0,[z136,z0,z276,z2,z4,z5,z6]),(0,[z484,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z485,z2,z4,z5,z6])],[(0,[z486,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z487,z4,z5,z6]),(0,[z0,z8,z2,z488,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z489,z6])],[(0,[z0,z26,z2,z83,z4,z5,z6]),(0,[z45,z0,z490,z2,z4,z5,z6]),(0,[z49,z237,z8,z2,z4,z5,z6]),(0,[z0,z8,z99,z2,z4,z9,z6]),(0,[z0,z8,z2,z39,z5,z6,z182]),(0,[z0,z8,z2,z4,z18,z53,z6])],[(1,[z0,z8,z2,z4,z469,z6]),(0,[z0,z8,z32,z2,z4,z243,z6]),(0,[z0,z8,z2,z491,z39,z5,z6]),(0,[z159,z0,z8,z4,z5,z6,z182]),(0,[z0,z8,z2,z4,z5,z6,z492]),(0,[z0,z8,z2,z4,z5,z6,z493])],[(0,[z0,z111,z1,z2,z4,z5,z6]),(0,[z494,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z286,z5,z90,z6])],[(0,[z0,z206,z8,z2,z4,z5,z6])],[(0,[z0,z54,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z495,z4,z5,z6]),(0,[z0,z496,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z119,z6]),(0,[z128,z0,z8,z2,z4,z316,z6])],[(1,[z0,z26,z2,z4,z9,z6]),(0,[z0,z8,z2,z81,z4,z5,z6]),(0,[z497,z0,z8,z2,z4,z5,z6])],[(0,[z28,z0,z8,z2,z35,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z498])],[(0,[z499,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z500]),(0,[z0,z8,z2,z4,z501,z5,z6]),(0,[z0,z8,z2,z4,z5,z135,z161]),(0,[z0,z8,z2,z249,z4,z5,z6])],[(0,[z20,z0,z8,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z502,z6]),(0,[z0,z8,z2,z42,z5,z24,z6]),(0,[z0,z8,z412,z2,z4,z18,z6])],[(0,[z0,z503,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z97,z18,z6])],[(0,[z11,z0,z8,z2,z12,z5,z6]),(0,[z0,z8,z43,z32,z4,z5,z6]),(0,[z0,z504,z8,z2,z4,z5,z6])]],
   [[(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z19,z6])],[(1,[z41,z1,z2,z4,z5,z6]),(0,[z505,z0,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z161]),(0,[z506,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z507,z2,z4,z5,z6]),(0,[z0,z508,z8,z2,z4,z5,z6]),(0,[z509,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z510,z5,z6])],[(0,[z511,z0,z8,z2,z4,z5,z6]),(0,[z0,z50,z32,z2,z4,z5,z6]),(0,[z261,z0,z8,z2,z39,z5,z6])],[(0,[z0,z456,z8,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z512,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z513])],[(0,[z0,z1,z373,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z514,z5,z6]),(0,[z0,z8,z2,z515,z4,z5,z6])],[(0,[z0,z516,z8,z2,z4,z5,z6]),(0,[z72,z0,z8,z2,z39,z5,z6])],[(0,[z57,z0,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z38,z4,z93,z6])],[(0,[z0,z15,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z517,z6]),(0,[z0,z518,z8,z2,z4,z5,z6]),(0,[z104,z0,z8,z2,z448,z5,z6]),(0,[z400,z0,z8,z2,z4,z9,z6])],[(0,[z72,z0,z8,z2,z42,z5,z6]),(0,[z159,z0,z8,z2,z4,z9,z6])],[(0,[z0,z8,z2,z4,z5,z519,z6]),(0,[z0,z8,z2,z4,z5,z6,z520])],[(0,[z84,z0,z8,z2,z4,z9,z6]),(1,[z0,z8,z62,z4,z5,z6]),(0,[z0,z521,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z522,z5,z6])],[(0,[z72,z8,z2,z4,z203,z5,z6]),(0,[z0,z8,z2,z4,z5,z135,z6]),(0,[z0,z8,z2,z4,z5,z6,z523]),(0,[z524,z0,z8,z2,z4,z5,z6])],[(0,[z49,z0,z8,z2,z487,z5,z6])],[(0,[z136,z0,z8,z2,z12,z5,z6]),(1,[z28,z8,z2,z4,z82,z6]),(0,[z0,z8,z2,z491,z4,z5,z6])]],
   [[(0,[z0,z8,z2,z4,z525,z5,z6]),(0,[z471,z0,z8,z2,z39,z5,z6])],[(1,[z49,z0,z3,z4,z5,z6]),(0,[z0,z15,z8,z2,z194,z5,z6])],[(0,[z0,z26,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z526,z4,z5,z6]),(0,[z0,z8,z2,z4,z103,z5,z6]),(0,[z0,z8,z2,z4,z527,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z528]),(0,[z0,z8,z2,z39,z18,z5,z6])],[(0,[z0,z8,z529,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z4,z9,z6])],[(0,[z0,z250,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z530,z4,z5,z6]),(0,[z0,z111,z8,z2,z4,z6,z14])],[(0,[z11,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z414,z2,z4,z5,z6]),(0,[z0,z8,z531,z2,z4,z5,z6]),(0,[z0,z8,z2,z532,z4,z5,z6]),(0,[z7,z0,z8,z2,z4,z5,z90])],[(0,[z0,z1,z2,z4,z5,z65,z6]),(0,[z0,z8,z2,z39,z5,z90,z6]),(0,[z0,z8,z2,z4,z533,z5,z6])],[(1,[z0,z8,z39,z42,z5,z6])],[(0,[z0,z55,z8,z2,z4,z9,z6]),(1,[z0,z138,z2,z4,z5,z6])],[(0,[z136,z8,z2,z4,z97,z5,z6])],[(0,[z57,z0,z8,z61,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z534,z6])],[(0,[z0,z8,z2,z58,z4,z9,z6]),(0,[z535,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z30,z2,z4,z5,z6])],[(0,[z72,z0,z8,z2,z4,z18,z6])],[(0,[z261,z0,z8,z2,z4,z5,z6]),(1,[z0,z8,z2,z230,z5,z6]),(0,[z104,z109,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z346,z9,z6])],[(0,[z0,z8,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z536,z6]),(0,[z0,z8,z2,z537,z4,z5,z6]),(0,[z538,z0,z8,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z533,z6])]],
   [[(0,[z0,z1,z2,z402,z4,z5,z6]),(0,[z0,z26,z2,z4,z5,z6,z539]),(0,[z49,z0,z8,z32,z4,z5,z6]),(0,[z0,z196,z8,z2,z4,z5,z6])],[(0,[z540,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z6,z118]),(0,[z0,z8,z2,z194,z4,z5,z6])],[(0,[z541,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z386,z6]),(0,[z0,z8,z2,z4,z18,z108,z6])],[(0,[z0,z8,z2,z4,z126,z6,z14])],[(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z542]),(0,[z0,z543,z8,z2,z4,z5,z6]),(0,[z544,z0,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z16])],[(0,[z0,z8,z2,z425,z4,z5,z6]),(0,[z136,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z545,z6]),(0,[z0,z8,z2,z4,z5,z177,z6]),(0,[z0,z490,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z42,z5,z92,z6]),(0,[z0,z8,z2,z4,z5,z546,z6])],[(0,[z0,z8,z547,z2,z4,z5,z6]),(1,[z0,z171,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z548,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z549]),(0,[z0,z8,z2,z4,z18,z90,z6])],[(0,[z550,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z551,z6]),(0,[z552,z0,z8,z2,z4,z5,z6]),(0,[z553,z0,z8,z2,z4,z5,z6]),(0,[z0,z554,z8,z2,z4,z5,z6]),(0,[z0,z8,z38,z4,z305,z5,z6])],[(0,[z0,z8,z58,z4,z5,z6,z182]),(0,[z136,z0,z8,z2,z38,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z555])],[(0,[z0,z8,z556,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z557,z5,z6]),(0,[z0,z558,z8,z2,z4,z5,z6]),(1,[z0,z8,z4,z18,z9,z6]),(0,[z0,z8,z2,z4,z9,z90,z6]),(0,[z0,z477,z8,z2,z4,z18,z6]),(0,[z0,z559,z8,z2,z4,z5,z6])],[],[(0,[z0,z217,z8,z2,z4,z5,z6]),(0,[z0,z560,z8,z2,z4,z5,z6])],[(0,[z57,z8,z2,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z561,z5,z6]),(0,[z0,z8,z2,z562,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z563,z6]),(0,[z0,z8,z2,z39,z5,z93,z6]),(0,[z564,z0,z8,z2,z4,z5,z6])]],
   [[(0,[z57,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z42,z335,z5,z6])],[(0,[z565,z0,z8,z2,z4,z5,z6]),(0,[z0,z15,z8,z2,z4,z9,z6])],[(1,[z0,z317,z2,z4,z5,z6]),(0,[z0,z8,z2,z37,z42,z5,z6]),(0,[z566,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z567,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z126,z5,z6]),(0,[z17,z0,z8,z2,z371,z5,z6]),(0,[z372,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z194,z4,z5,z16])],[(0,[z28,z0,z8,z2,z38,z4,z6]),(0,[z0,z8,z2,z4,z568,z5,z6]),(0,[z128,z0,z8,z99,z4,z5,z6]),(1,[z422,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z569,z6]),(0,[z0,z8,z2,z570,z4,z5,z6])],[(0,[z0,z111,z8,z2,z97,z5,z6]),(0,[z0,z54,z8,z2,z4,z13,z6]),(0,[z0,z8,z2,z4,z5,z343,z6])],[(0,[z0,z1,z2,z4,z5,z6,z528]),(0,[z0,z26,z32,z2,z4,z5,z6]),(0,[z0,z8,z2,z83,z39,z5,z6])],[(0,[z0,z8,z2,z4,z5,z324,z6]),(0,[z0,z8,z2,z4,z199,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z571]),(0,[z0,z8,z2,z39,z5,z166,z6])],[(0,[z0,z8,z2,z572,z4,z5,z6])],[(0,[z84,z0,z8,z61,z4,z5,z6]),(0,[z573,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z90,z75])],[(1,[z0,z8,z2,z4,z473,z6]),(0,[z0,z8,z2,z4,z108,z203,z6]),(0,[z0,z8,z2,z4,z5,z9,z6]),(1,[z0,z521,z2,z4,z5,z6]),(0,[z7,z0,z8,z2,z4,z5,z6])],[(0,[z159,z0,z8,z2,z4,z410,z6])],[],[(0,[z0,z8,z2,z4,z134,z5,z6]),(0,[z0,z8,z2,z532,z39,z5,z6]),(0,[z574,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z38,z4,z6,z14])],[]],
   [[(0,[z0,z8,z2,z303,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z93,z6])],[(0,[z0,z8,z2,z575,z4,z5,z6]),(0,[z576,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z13,z6])],[],[(0,[z25,z41,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z577,z6]),(0,[z0,z578,z8,z2,z4,z5,z6]),(0,[z104,z0,z2,z4,z5,z6,z161]),(0,[z0,z8,z2,z4,z9,z93,z6])],[(0,[z0,z8,z2,z12,z4,z5,z6]),(0,[z579,z0,z8,z2,z4,z5,z6])],[(0,[z0,z276,z8,z2,z4,z5,z6]),(0,[z0,z580,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z65,z135]),(0,[z0,z581,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z2,z4,z5,z6]),(0,[z582,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z18,z6,z182])],[(0,[z0,z583,z8,z2,z4,z5,z6]),(0,[z0,z29,z8,z2,z4,z5,z6]),(0,[z0,z196,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z395,z9,z6])],[(0,[z261,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z194,z39,z5,z6]),(0,[z0,z8,z2,z4,z18,z166,z6])],[(0,[z321,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z6,z161]),(0,[z0,z8,z2,z584,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z6,z182])],[(0,[z0,z196,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z585]),(0,[z0,z8,z2,z586,z4,z5,z6]),(0,[z0,z8,z2,z4,z587,z5,z6]),(0,[z0,z588,z8,z2,z4,z5,z6])],[(0,[z72,z0,z26,z2,z4,z5,z6]),(0,[z0,z26,z43,z2,z4,z5,z6]),(0,[z0,z8,z2,z194,z42,z5,z6])],[(1,[z0,z1,z2,z39,z5,z6]),(0,[z0,z26,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z589]),(1,[z0,z8,z99,z39,z5,z6]),(0,[z0,z590,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z591,z4,z5,z6])],[(0,[z0,z26,z2,z38,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z42,z6])],[(0,[z0,z8,z288,z2,z4,z5,z6]),(1,[z0,z8,z61,z4,z9,z6]),(0,[z0,z592,z8,z2,z4,z5,z6]),(0,[z0,z8,z593,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z42,z5,z6]),(0,[z0,z8,z2,z39,z203,z5,z6]),(0,[z0,z8,z2,z404,z4,z9,z6]),(1,[z0,z8,z2,z4,z416,z6])],[(0,[z594,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z4,z5,z6]),(0,[z0,z554,z8,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z124,z5,z6]),(0,[z0,z8,z2,z83,z4,z5,z6])],[(0,[z0,z8,z595,z2,z4,z5,z6])],[(0,[z0,z8,z99,z39,z4,z5,z6]),(0,[z159,z0,z138,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z97,z9,z6]),(0,[z0,z596,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z597]),(0,[z0,z8,z2,z4,z5,z6,z225]),(1,[z0,z8,z2,z4,z243,z6]),(0,[z0,z217,z8,z2,z39,z5,z6])],[(0,[z0,z8,z310,z2,z4,z5,z6]),(0,[z0,z430,z8,z2,z4,z5,z6]),(0,[z0,z598,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z108,z9,z6]),(0,[z0,z8,z2,z4,z5,z6,z599])],[(0,[z0,z8,z2,z4,z600,z5,z6]),(0,[z20,z0,z8,z2,z40,z5,z6])],[(0,[z601,z0,z8,z2,z4,z5,z6]),(0,[z0,z217,z8,z2,z42,z5,z6])],[(0,[z0,z8,z2,z4,z5,z331,z6])],[(1,[z45,z1,z2,z4,z5,z6]),(1,[z0,z8,z2,z382,z5,z6]),(0,[z0,z2,z4,z5,z65,z6,z161]),(0,[z159,z0,z8,z2,z4,z533,z6])],[(0,[z602,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z166,z75]),(0,[z0,z8,z2,z4,z5,z161,z182])],[(0,[z8,z2,z58,z4,z5,z6,z75]),(0,[z0,z8,z603,z2,z4,z5,z6]),(0,[z104,z0,z8,z2,z4,z5,z65]),(0,[z261,z0,z8,z2,z4,z18,z6])],[(0,[z0,z481,z26,z2,z4,z5,z6]),(0,[z11,z0,z8,z2,z38,z5,z6]),(0,[z0,z604,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z223,z5,z6]),(0,[z0,z8,z2,z38,z5,z6,z16])],[(0,[z0,z179,z8,z2,z4,z97,z6]),(0,[z0,z196,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z194,z4,z5,z166]),(0,[z0,z8,z2,z4,z5,z605,z6])],[(0,[z0,z1,z2,z4,z5,z9,z6]),(0,[z0,z26,z2,z4,z5,z93,z6]),(1,[z0,z8,z2,z4,z5,z132]),(0,[z0,z8,z2,z4,z5,z6,z606]),(0,[z0,z8,z2,z42,z5,z65,z6]),(0,[z540,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z194,z4,z18,z6]),(0,[z607,z0,z8,z2,z4,z5,z6])]],
   [[(0,[z0,z8,z2,z4,z5,z608,z6]),(0,[z0,z8,z2,z4,z5,z609,z6]),(1,[z0,z196,z2,z37,z5,z6])],[(0,[z28,z0,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z58,z4,z5,z6]),(1,[z237,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z610,z5,z6])],[(0,[z72,z0,z407,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z75,z16]),(0,[z0,z8,z2,z4,z611,z5,z6]),(0,[z0,z436,z8,z2,z4,z9,z6])],[(1,[z0,z8,z58,z42,z5,z6]),(0,[z7,z0,z8,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z612]),(0,[z159,z468,z8,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z6,z14])],[(0,[z0,z26,z2,z4,z5,z6,z182]),(0,[z613,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z614,z2,z4,z5,z6]),(0,[z7,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z43,z2,z522,z5,z6])],[(0,[z25,z0,z8,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z12,z4,z5,z6]),(0,[z0,z8,z2,z4,z615,z5,z6])],[(0,[z0,z8,z2,z4,z616,z5,z6]),(0,[z0,z8,z2,z39,z5,z82,z6]),(0,[z0,z8,z2,z4,z557,z18,z6])],[],[(0,[z0,z503,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z617,z6]),(0,[z0,z217,z8,z2,z4,z18,z6]),(0,[z618,z0,z8,z2,z4,z5,z6])],[(1,[z0,z490,z2,z4,z5,z6])],[(0,[z0,z8,z2,z42,z5,z6,z16]),(0,[z0,z8,z2,z4,z5,z410,z6])],[(0,[z0,z8,z2,z39,z5,z6,z75]),(0,[z0,z8,z2,z2,z39,z5,z6]),(0,[z0,z8,z619,z2,z4,z5,z6])],[(1,[z84,z1,z2,z4,z5,z6]),(0,[z0,z8,z61,z43,z4,z5,z6]),(0,[z0,z8,z2,z12,z42,z5,z6])]],
   [[(0,[z0,z196,z8,z2,z36,z5,z6]),(0,[z0,z8,z2,z42,z108,z5,z6]),(0,[z0,z8,z4,z18,z5,z9,z6])],[(0,[z620,z0,z8,z2,z4,z5,z6]),(0,[z0,z598,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z2,z42,z5,z6])],[(1,[z0,z8,z2,z4,z5,z209]),(0,[z0,z8,z2,z97,z5,z6,z16]),(0,[z0,z8,z2,z4,z621,z5,z6]),(0,[z0,z8,z43,z4,z5,z135,z6]),(1,[z0,z8,z2,z5,z6,z348])],[(0,[z622,z0,z8,z2,z4,z5,z6]),(0,[z104,z0,z8,z2,z4,z5,z161]),(0,[z0,z623,z8,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z135,z6]),(0,[z72,z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z624,z6]),(0,[z0,z8,z2,z4,z416,z5,z6])],[],[(0,[z0,z1,z2,z83,z4,z5,z6]),(0,[z0,z8,z625,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z18,z6,z14])],[(0,[z128,z0,z1,z2,z4,z5,z6]),(0,[z0,z50,z1,z2,z4,z5,z6]),(0,[z57,z0,z8,z2,z4,z5,z445])],[(0,[z0,z8,z2,z4,z289,z5,z6]),(0,[z0,z8,z2,z4,z5,z626,z6]),(0,[z0,z8,z32,z2,z4,z51,z6]),(0,[z0,z8,z2,z42,z5,z6,z431]),(0,[z627,z0,z8,z2,z4,z5,z6])],[(0,[z628,z0,z8,z2,z4,z5,z6]),(0,[z17,z0,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z9,z6,z14]),(0,[z7,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z43,z2,z4,z315,z6])],[(0,[z0,z8,z2,z4,z18,z82,z6]),(0,[z0,z8,z2,z4,z5,z629,z6]),(0,[z0,z8,z2,z630,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z121,z6]),(0,[z631,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z195,z6])],[(1,[z0,z8,z2,z487,z5,z6]),(0,[z0,z8,z2,z4,z42,z5,z6])],[(0,[z0,z632,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z82,z6]),(0,[z0,z8,z2,z4,z203,z93,z6]),(0,[z0,z8,z2,z39,z37,z5,z6]),(0,[z0,z217,z8,z2,z36,z5,z6]),(0,[z0,z8,z2,z83,z42,z5,z6]),(0,[z0,z8,z2,z4,z441,z5,z6])],[(0,[z45,z0,z8,z2,z4,z5,z6]),(0,[z633,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z299,z5,z6])],[(0,[z0,z26,z2,z4,z64,z5,z6]),(0,[z0,z8,z2,z4,z634,z5,z6]),(0,[z0,z8,z2,z4,z18,z6,z75]),(0,[z0,z8,z2,z4,z90,z6,z14])]],
   [[(0,[z96,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z382,z4,z5,z6]),(0,[z0,z183,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z190,z166,z6])],[(0,[z0,z8,z2,z4,z5,z6,z635])],[(0,[z0,z8,z2,z12,z4,z18,z6]),(0,[z0,z8,z2,z4,z9,z6,z75]),(0,[z636,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z637,z6])],[(0,[z0,z8,z2,z4,z638,z5,z6]),(0,[z0,z8,z2,z4,z5,z639,z6]),(0,[z104,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z6,z640])],[(0,[z0,z8,z2,z232,z4,z5,z6])],[(0,[z0,z26,z2,z4,z18,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z641]),(0,[z49,z112,z8,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z100,z6]),(0,[z0,z642,z8,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z194,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z107,z6]),(0,[z0,z8,z2,z4,z5,z6,z445]),(1,[z0,z8,z2,z160,z5,z6])],[(0,[z0,z643,z8,z2,z4,z5,z6]),(0,[z136,z0,z8,z2,z4,z478,z6]),(0,[z49,z0,z8,z2,z4,z5,z6]),(1,[z0,z8,z113,z4,z9,z6])],[(0,[z0,z26,z2,z4,z5,z90,z6]),(0,[z0,z8,z2,z197,z4,z5,z6])],[(0,[z261,z0,z26,z2,z4,z5,z6]),(0,[z0,z26,z61,z2,z4,z5,z6])],[(0,[z84,z0,z430,z2,z4,z5,z6])],[(0,[z0,z196,z26,z2,z4,z5,z6]),(0,[z0,z644,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z6,z162]),(0,[z0,z645,z8,z2,z4,z5,z6])],[(0,[z159,z0,z8,z2,z4,z5,z182]),(0,[z0,z8,z2,z4,z5,z646,z6])],[(0,[z0,z8,z2,z647,z4,z5,z6]),(0,[z25,z0,z8,z2,z39,z5,z6]),(1,[z0,z8,z2,z4,z227,z6]),(0,[z0,z8,z2,z4,z9,z166,z6]),(0,[z0,z8,z2,z4,z648,z5,z6]),(0,[z649,z0,z8,z2,z4,z5,z6]),(0,[z0,z111,z8,z2,z83,z5,z6])]],
   [[(0,[z41,z0,z8,z2,z39,z5,z6]),(0,[z650,z0,z8,z2,z4,z5,z6]),(1,[z0,z179,z8,z2,z4,z6]),(0,[z0,z8,z2,z4,z302,z5,z6]),(0,[z0,z8,z43,z2,z39,z5,z6]),(0,[z0,z8,z2,z83,z4,z18,z6])],[(0,[z0,z8,z2,z4,z5,z92,z182]),(0,[z0,z8,z2,z3,z39,z5,z6]),(1,[z109,z8,z2,z4,z5,z6])],[(0,[z25,z0,z8,z2,z42,z5,z6]),(0,[z57,z0,z22,z2,z4,z5,z6]),(1,[z0,z117,z2,z4,z5,z6]),(0,[z136,z0,z8,z2,z4,z473,z6]),(0,[z0,z8,z2,z4,z126,z5,z6]),(0,[z0,z8,z2,z651,z4,z5,z6]),(0,[z0,z8,z2,z4,z652,z5,z6])],[],[(0,[z0,z26,z2,z4,z5,z231,z6]),(0,[z17,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z18,z13,z6])],[(1,[z0,z8,z2,z371,z5,z6]),(0,[z0,z8,z32,z2,z4,z5,z6])],[(0,[z0,z8,z32,z2,z124,z5,z6]),(0,[z0,z8,z2,z653,z4,z5,z6])],[(0,[z0,z8,z2,z654,z4,z5,z6]),(0,[z655,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z13,z6])],[(0,[z0,z26,z2,z4,z5,z82,z6]),(0,[z0,z8,z2,z4,z656,z5,z6])],[(0,[z0,z217,z26,z2,z4,z5,z6]),(0,[z657,z0,z8,z2,z4,z5,z6])],[],[(0,[z25,z45,z8,z2,z4,z5,z6]),(0,[z0,z8,z61,z2,z265,z5,z6]),(0,[z72,z0,z8,z2,z4,z203,z6])],[(0,[z0,z8,z2,z4,z658,z5,z6]),(0,[z0,z26,z113,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z659,z6]),(0,[z17,z8,z2,z4,z5,z6,z75])],[(0,[z0,z8,z2,z4,z5,z478,z6]),(0,[z0,z8,z2,z4,z344,z5,z6])],[(0,[z0,z435,z8,z2,z4,z5,z6]),(0,[z0,z8,z99,z58,z4,z5,z6]),(0,[z0,z8,z2,z194,z12,z5,z6]),(0,[z660,z0,z8,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z661,z6]),(2,[z0,z8,z42,z9,z6])],[(0,[z0,z153,z1,z2,z4,z5,z6]),(0,[z662,z0,z8,z2,z4,z5,z6]),(0,[z20,z0,z8,z2,z39,z5,z6])],[(1,[z0,z8,z2,z4,z5,z146]),(0,[z0,z8,z407,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z421,z5,z6])],[(0,[z159,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z469,z6]),(0,[z0,z77,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z663,z6])],[(0,[z0,z54,z8,z2,z4,z126,z6]),(0,[z0,z664,z8,z2,z4,z5,z6])],[(0,[z25,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z5,z6,z665]),(0,[z0,z8,z2,z4,z666,z5,z6])],[(1,[z0,z1,z2,z4,z18,z6]),(0,[z0,z8,z408,z2,z4,z5,z6]),(0,[z45,z0,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z39,z5,z92,z6]),(0,[z0,z8,z2,z667,z4,z5,z6]),(0,[z0,z668,z8,z2,z4,z5,z6])],[(0,[z669,z0,z8,z2,z4,z5,z6]),(1,[z0,z137,z2,z4,z5,z6])],[(0,[z7,z0,z26,z2,z4,z5,z6])],[(1,[z0,z8,z2,z265,z5,z6]),(0,[z45,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z670,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z671,z6])],[(0,[z41,z0,z8,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z5,z166,z6]),(0,[z72,z0,z270,z2,z4,z5,z6]),(0,[z0,z8,z43,z2,z4,z5,z6])],[(0,[z0,z8,z2,z3,z4,z5,z6]),(0,[z104,z0,z8,z2,z39,z5,z6]),(0,[z0,z111,z8,z2,z39,z5,z6])],[(0,[z0,z26,z2,z4,z37,z5,z6]),(0,[z0,z8,z2,z38,z4,z5,z6])],[(0,[z0,z54,z8,z2,z39,z5,z6]),(0,[z0,z672,z8,z2,z4,z5,z6])],[(0,[z104,z0,z8,z2,z42,z5,z6]),(0,[z20,z0,z8,z4,z42,z5,z6]),(0,[z0,z111,z8,z2,z42,z5,z6]),(0,[z673,z0,z8,z2,z4,z5,z6])]],
   [[(0,[z0,z674,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z675])],[(0,[z25,z84,z8,z2,z4,z5,z6]),(0,[z49,z0,z8,z2,z39,z5,z6])],[(0,[z159,z422,z8,z2,z4,z5,z6]),(1,[z0,z8,z2,z522,z5,z6]),(0,[z0,z8,z2,z676,z4,z5,z6])],[(0,[z25,z8,z2,z4,z5,z6,z75]),(0,[z0,z643,z26,z2,z4,z5,z6]),(0,[z677,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z203,z6,z14]),(0,[z49,z0,z8,z2,z199,z5,z6]),(0,[z261,z0,z8,z2,z4,z9,z6])],[(0,[z0,z26,z2,z4,z5,z13,z6]),(0,[z0,z8,z2,z678,z4,z5,z6]),(0,[z49,z0,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z679,z6]),(0,[z538,z0,z8,z2,z4,z9,z6]),(0,[z0,z116,z8,z2,z4,z5,z6]),(0,[z0,z111,z8,z2,z83,z4,z6])],[(0,[z0,z196,z8,z2,z4,z9,z6]),(0,[z104,z0,z8,z2,z4,z210,z6]),(0,[z0,z8,z680,z2,z4,z5,z6]),(1,[z0,z8,z2,z4,z6,z201])],[(0,[z136,z0,z8,z2,z4,z5,z132]),(0,[z0,z8,z2,z4,z5,z6,z681]),(0,[z0,z682,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z194,z4,z9,z6])],[(0,[z0,z8,z2,z4,z18,z92,z6]),(0,[z159,z0,z8,z43,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z683,z6]),(0,[z684,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z685,z2,z4,z5,z6]),(1,[z0,z247,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z686,z6])],[(0,[z0,z8,z2,z687,z4,z5,z6]),(0,[z0,z688,z8,z2,z4,z5,z6]),(1,[z0,z55,z2,z4,z13,z6]),(0,[z104,z0,z8,z2,z4,z221,z6]),(0,[z0,z8,z2,z4,z5,z470,z6]),(0,[z159,z0,z521,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z9,z6]),(0,[z689,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z690]),(1,[z0,z8,z99,z4,z9,z6]),(0,[z0,z8,z2,z5,z90,z6,z348])],[(0,[z691,z0,z8,z2,z4,z5,z6]),(0,[z0,z55,z2,z4,z5,z13,z6])],[(0,[z45,z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z42,z5,z135,z6]),(0,[z20,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z305,z5,z6])],[(0,[z0,z8,z2,z4,z634,z18,z6])],[(0,[z0,z476,z8,z2,z4,z5,z6]),(0,[z17,z0,z8,z2,z4,z5,z92]),(0,[z0,z8,z32,z2,z39,z5,z6]),(0,[z0,z554,z8,z2,z4,z9,z6])],[(0,[z136,z0,z1,z2,z4,z5,z6]),(0,[z0,z26,z153,z2,z4,z5,z6]),(1,[z0,z8,z2,z148,z4,z6]),(0,[z17,z0,z8,z2,z42,z5,z6]),(1,[z0,z217,z2,z36,z5,z6]),(1,[z0,z8,z2,z448,z5,z6]),(0,[z0,z8,z692,z2,z4,z5,z6])]],
   [[(0,[z0,z8,z2,z4,z5,z92,z14])],[(0,[z41,z8,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z658,z5,z6]),(0,[z0,z8,z32,z2,z42,z5,z6]),(0,[z693,z0,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z539]),(0,[z0,z217,z8,z2,z4,z9,z6]),(0,[z104,z0,z8,z2,z4,z18,z6])],[(0,[z0,z26,z2,z4,z203,z5,z6]),(0,[z694,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z166,z6,z201])],[(0,[z0,z695,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z696,z6])],[(0,[z0,z8,z2,z101,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z182]),(1,[z0,z8,z2,z4,z315,z6])],[(0,[z697,z0,z8,z2,z4,z5,z6]),(0,[z698,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z699,z4,z5,z6]),(1,[z0,z8,z2,z584,z5,z6]),(0,[z0,z8,z700,z2,z4,z5,z6])],[(0,[z0,z8,z2,z701,z4,z5,z6]),(0,[z49,z0,z8,z2,z4,z18,z6]),(0,[z0,z111,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z83,z194,z5,z6]),(1,[z0,z8,z2,z286,z5,z6])],[(0,[z0,z8,z2,z4,z5,z6,z702]),(0,[z45,z84,z8,z2,z4,z5,z6]),(0,[z28,z0,z8,z2,z4,z82,z6]),(0,[z158,z0,z8,z2,z4,z5,z6])],[(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z136,z0,z8,z2,z4,z5,z209]),(0,[z17,z45,z8,z2,z4,z5,z6]),(0,[z0,z54,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z6,z161]),(0,[z0,z8,z2,z4,z5,z65,z182])],[(0,[z0,z8,z379,z2,z4,z5,z6]),(0,[z104,z241,z8,z2,z4,z5,z6])],[(0,[z0,z8,z113,z2,z584,z5,z6])],[(0,[z0,z8,z2,z703,z4,z5,z6]),(0,[z0,z8,z704,z2,z4,z5,z6]),(0,[z0,z8,z2,z83,z4,z203,z6]),(0,[z705,z0,z8,z2,z4,z5,z6])],[(0,[z240,z0,z8,z2,z4,z5,z6]),(1,[z0,z8,z58,z4,z9,z6]),(0,[z0,z8,z2,z366,z5,z82,z6]),(0,[z0,z8,z2,z4,z648,z18,z6])],[(0,[z706,z0,z8,z2,z4,z5,z6]),(0,[z0,z8,z43,z3,z4,z5,z6]),(0,[z0,z8,z2,z4,z42,z9,z6]),(0,[z0,z8,z2,z88,z39,z5,z6]),(1,[z0,z8,z43,z4,z5,z135])],[(0,[z0,z1,z43,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z57,z8,z58,z4,z18,z6]),(0,[z0,z8,z4,z18,z305,z6]),(0,[z468,z707,z2,z4,z5,z6])],[(0,[z0,z1,z2,z487,z5,z6]),(0,[z0,z1,z2,z448,z5,z6]),(0,[z0,z8,z174,z42,z5,z6]),(0,[z0,z8,z2,z4,z331,z6]),(0,[z0,z8,z2,z4,z708,z6]),(0,[z0,z8,z42,z9,z6,z162]),(0,[z0,z8,z2,z4,z709,z6])],[(0,[z45,z1,z2,z4,z5,z75]),(0,[z0,z8,z2,z303,z18,z6]),(0,[z0,z8,z2,z4,z5,z710]),(0,[z0,z270,z2,z42,z5,z6]),(0,[z0,z8,z62,z371,z5,z6]),(0,[z711,z8,z2,z4,z5,z6]),(0,[z427,z0,z8,z4,z18,z6]),(0,[z505,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z4,z190,z6]),(0,[z0,z712,z2,z4,z5,z6])],[(0,[z0,z8,z131,z234,z5,z6]),(0,[z0,z8,z2,z713,z5,z6]),(0,[z0,z8,z42,z9,z166,z6])],[(0,[z136,z8,z2,z97,z18,z6]),(0,[z0,z8,z414,z39,z5,z6]),(0,[z0,z8,z2,z4,z714,z6])],[(0,[z0,z430,z2,z39,z5,z6]),(0,[z136,z8,z232,z97,z5,z6]),(0,[z0,z8,z2,z35,z5,z215])],[(0,[z0,z26,z2,z4,z147,z6]),(0,[z0,z8,z2,z715,z5,z6]),(0,[z0,z8,z2,z4,z716,z6]),(0,[z0,z8,z149,z4,z18,z6]),(0,[z20,z0,z8,z40,z18,z6]),(1,[z0,z138,z4,z5,z182])],[(0,[z84,z1,z58,z4,z5,z6]),(0,[z28,z29,z2,z4,z82,z6]),(0,[z0,z8,z414,z42,z5,z6]),(0,[z0,z8,z2,z4,z717,z6]),(0,[z334,z0,z3,z4,z5,z6])],[(0,[z0,z26,z2,z4,z343,z6]),(0,[z0,z26,z2,z344,z5,z6]),(0,[z241,z323,z2,z4,z5,z6]),(0,[z109,z8,z2,z382,z5,z6]),(0,[z128,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z39,z108,z90])],[(0,[z0,z8,z2,z4,z718,z6]),(0,[z0,z8,z2,z719,z5,z6]),(0,[z0,z8,z2,z148,z93,z6]),(0,[z0,z8,z2,z42,z343,z6])],[(0,[z566,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z289,z9,z6]),(0,[z0,z8,z2,z4,z6,z720]),(0,[z11,z150,z2,z12,z5,z6]),(0,[z104,z0,z2,z4,z5,z161])],[(0,[z0,z1,z2,z4,z100,z6]),(0,[z45,z8,z174,z4,z5,z6]),(0,[z0,z8,z174,z4,z721,z6]),(0,[z0,z8,z2,z42,z108,z90]),(0,[z7,z0,z8,z2,z39,z14]),(0,[z0,z8,z2,z4,z9,z722]),(0,[z0,z8,z2,z9,z6,z348])],[(0,[z1,z2,z4,z352,z5,z6]),(0,[z0,z8,z2,z103,z469,z6]),(0,[z0,z8,z42,z9,z13,z6])],[(0,[z1,z2,z354,z4,z5,z6]),(0,[z0,z1,z2,z160,z5,z6]),(0,[z0,z26,z2,z4,z5,z195]),(0,[z175,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z199,z9,z6]),(0,[z723,z8,z2,z4,z5,z6]),(0,[z372,z8,z2,z4,z324,z6]),(0,[z0,z724,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z725,z6]),(0,[z0,z8,z61,z18,z42,z6]),(0,[z0,z8,z2,z83,z478,z6]),(0,[z0,z30,z2,z4,z177,z6]),(0,[z241,z8,z149,z4,z5,z6]),(0,[z0,z8,z2,z42,z9,z6]),(0,[z564,z0,z8,z4,z18,z6])],[(0,[z0,z26,z2,z249,z5,z6]),(0,[z0,z8,z2,z39,z5,z445]),(0,[z0,z8,z212,z4,z726,z6]),(0,[z0,z8,z414,z4,z5,z215]),(0,[z8,z2,z4,z5,z727,z6]),(0,[z0,z407,z2,z4,z18,z6]),(0,[z0,z8,z2,z5,z92,z348]),(0,[z0,z8,z728,z4,z5,z6]),(0,[z0,z8,z2,z729,z5,z6]),(0,[z0,z8,z2,z4,z730,z6]),(0,[z0,z8,z197,z42,z9,z6])]],
   [[(0,[z0,z731,z2,z4,z5,z6]),(0,[z0,z8,z529,z4,z5,z135]),(0,[z49,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z732,z6]),(0,[z294,z0,z8,z42,z9,z6]),(0,[z0,z8,z99,z4,z733,z6]),(0,[z0,z8,z2,z5,z6,z734])],[(0,[z0,z8,z4,z715,z5,z6]),(0,[z17,z8,z2,z4,z5,z735]),(0,[z0,z8,z2,z4,z736,z6])],[(0,[z0,z8,z2,z4,z737,z6]),(0,[z17,z8,z2,z42,z5,z75]),(0,[z0,z8,z2,z738,z5,z6])],[(0,[z524,z1,z2,z4,z5,z6]),(0,[z0,z8,z687,z4,z9,z6]),(0,[z0,z8,z2,z39,z262,z6]),(0,[z0,z739,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z740,z6]),(0,[z0,z8,z2,z5,z166,z741])],[(0,[z0,z8,z2,z4,z5,z742]),(0,[z0,z1,z2,z4,z227,z6]),(0,[z0,z8,z174,z4,z18,z6]),(0,[z0,z217,z2,z743,z5,z6])],[(0,[z0,z8,z61,z265,z9,z6]),(0,[z0,z8,z212,z4,z9,z6]),(0,[z0,z8,z2,z35,z5,z6]),(0,[z0,z270,z2,z4,z18,z6]),(0,[z0,z672,z2,z4,z126,z6]),(0,[z20,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z4,z410,z6]),(0,[z505,z0,z8,z4,z18,z6]),(0,[z0,z744,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z75,z14]),(0,[z109,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z303,z9,z6]),(0,[z0,z8,z414,z745,z5,z6]),(0,[z0,z30,z174,z4,z5,z6]),(0,[z0,z8,z4,z305,z9,z6])],[(0,[z0,z1,z2,z4,z746,z6]),(0,[z0,z8,z42,z5,z469,z6]),(0,[z0,z8,z2,z148,z42,z6]),(0,[z0,z8,z2,z38,z449,z6]),(0,[z0,z8,z2,z747,z5,z6])],[(0,[z0,z8,z2,z748,z5,z6]),(0,[z84,z8,z61,z4,z5,z6]),(1,[z0,z8,z749,z5,z6]),(0,[z0,z554,z8,z2,z83,z6]),(0,[z0,z8,z2,z4,z750,z6]),(0,[z0,z8,z2,z286,z108,z6])],[(0,[z0,z26,z2,z366,z5,z6]),(0,[z0,z8,z4,z751,z5,z6]),(0,[z0,z8,z2,z752,z5,z6])],[(0,[z45,z26,z2,z4,z5,z92]),(0,[z0,z310,z2,z4,z9,z6]),(0,[z0,z8,z414,z4,z18,z6]),(0,[z28,z0,z8,z2,z366,z6]),(0,[z0,z753,z8,z2,z4,z6]),(0,[z109,z490,z2,z4,z5,z6]),(0,[z0,z8,z3,z4,z5,z225]),(0,[z754,z8,z2,z4,z5,z6]),(0,[z0,z8,z4,z441,z9,z6])],[(0,[z0,z1,z2,z371,z5,z6]),(0,[z0,z250,z2,z145,z5,z6]),(0,[z0,z26,z2,z238,z5,z6]),(0,[z0,z755,z2,z4,z5,z6]),(0,[z0,z8,z165,z42,z5,z6]),(0,[z0,z8,z2,z5,z6,z756])],[(0,[z0,z26,z42,z5,z9,z6]),(0,[z0,z8,z757,z4,z5,z6])],[(0,[z0,z758,z2,z4,z5,z6]),(0,[z159,z0,z8,z4,z9,z182]),(0,[z159,z0,z8,z4,z5,z759]),(0,[z0,z760,z2,z4,z5,z6])],[(0,[z1,z58,z4,z5,z9,z6]),(0,[z0,z8,z2,z761,z5,z6]),(0,[z0,z8,z2,z31,z5,z166])],[(0,[z0,z8,z414,z234,z5,z6]),(0,[z0,z8,z2,z4,z108,z659]),(0,[z0,z259,z2,z421,z5,z6]),(0,[z0,z259,z8,z42,z9,z6]),(0,[z0,z8,z2,z236,z24,z6]),(0,[z159,z422,z8,z4,z5,z182]),(0,[z0,z8,z4,z5,z6,z759])]],
   [[(0,[z0,z430,z2,z4,z5,z6]),(0,[z0,z8,z699,z4,z9,z6])],[(0,[z0,z8,z2,z4,z5,z762]),(0,[z25,z490,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z5,z225]),(0,[z0,z8,z2,z4,z763,z6]),(0,[z0,z8,z2,z199,z5,z225]),(0,[z764,z8,z2,z4,z5,z6]),(0,[z0,z2,z149,z4,z5,z161]),(0,[z0,z8,z2,z765,z5,z6]),(0,[z0,z8,z2,z4,z766,z6])],[(0,[z0,z8,z232,z4,z9,z6]),(0,[z0,z8,z767,z4,z5,z6]),(0,[z0,z8,z174,z4,z73,z6]),(0,[z0,z8,z2,z42,z5,z225]),(0,[z768,z8,z2,z4,z5,z6]),(0,[z128,z0,z8,z42,z316,z6]),(0,[z0,z8,z2,z39,z5,z769]),(0,[z468,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z5,z6,z770])],[(0,[z0,z1,z4,z5,z6,z771]),(0,[z0,z137,z2,z4,z5,z132]),(0,[z28,z8,z2,z4,z82,z6]),(0,[z0,z8,z2,z772,z5,z6]),(0,[z0,z8,z2,z249,z18,z6]),(0,[z0,z521,z2,z160,z5,z6])],[(0,[z20,z1,z58,z4,z5,z6]),(0,[z0,z8,z61,z103,z9,z6]),(0,[z136,z8,z2,z653,z5,z6]),(0,[z0,z379,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z773,z6]),(0,[z0,z8,z2,z5,z6,z774])],[(0,[z17,z8,z2,z4,z18,z75]),(0,[z0,z8,z2,z39,z316,z6])],[(0,[z136,z276,z2,z97,z5,z6]),(0,[z0,z8,z232,z38,z5,z6]),(0,[z0,z8,z2,z4,z775,z6]),(0,[z0,z8,z2,z234,z9,z6])],[(0,[z0,z8,z58,z4,z227,z6]),(0,[z0,z776,z8,z2,z4,z6]),(0,[z28,z8,z2,z4,z82,z119]),(0,[z0,z8,z2,z243,z124,z6])],[(0,[z0,z8,z2,z777,z5,z6]),(0,[z497,z0,z8,z2,z4,z14]),(0,[z0,z8,z2,z42,z316,z6]),(0,[z20,z0,z8,z4,z18,z6])],[(0,[z0,z8,z2,z4,z778,z6]),(0,[z779,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z331,z6]),(0,[z0,z623,z2,z36,z5,z6]),(0,[z241,z8,z2,z4,z9,z6]),(0,[z104,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z780,z5,z6])],[(0,[z1,z2,z42,z5,z6,z75]),(0,[z0,z26,z2,z194,z5,z166]),(0,[z0,z8,z2,z4,z5,z445]),(0,[z0,z22,z2,z39,z5,z6]),(0,[z0,z8,z58,z40,z5,z6]),(0,[z0,z781,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z190,z6])],[(0,[z0,z1,z2,z4,z782,z6]),(0,[z0,z26,z2,z81,z5,z6]),(0,[z0,z8,z2,z39,z478,z6]),(0,[z112,z8,z2,z4,z262,z6]),(0,[z0,z8,z2,z199,z331,z6]),(0,[z0,z55,z2,z4,z53,z6])],[(0,[z0,z1,z2,z4,z91,z6]),(0,[z0,z8,z2,z42,z331,z6]),(0,[z0,z8,z42,z9,z228,z6])],[(0,[z1,z2,z58,z39,z5,z6]),(0,[z123,z8,z2,z4,z5,z75]),(0,[z0,z26,z131,z4,z5,z6]),(0,[z0,z138,z2,z4,z5,z6]),(0,[z0,z273,z8,z42,z9,z6]),(0,[z0,z8,z2,z42,z190,z6])],[(0,[z0,z1,z2,z265,z5,z6]),(0,[z1,z2,z4,z5,z394,z6]),(0,[z393,z1,z2,z4,z5,z6]),(0,[z0,z8,z99,z265,z5,z6]),(0,[z0,z8,z2,z4,z262,z6]),(0,[z0,z783,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z784])],[(0,[z57,z26,z58,z4,z5,z6]),(0,[z627,z8,z2,z97,z5,z6])]],
   [[(0,[z1,z2,z58,z42,z5,z6]),(0,[z0,z8,z208,z42,z5,z6]),(0,[z0,z8,z2,z39,z469,z6]),(0,[z0,z8,z2,z785,z5,z6]),(0,[z0,z8,z4,z786,z5,z6]),(0,[z0,z8,z42,z9,z6,z14]),(0,[z0,z8,z2,z344,z9,z6])],[(0,[z84,z8,z2,z4,z5,z445]),(0,[z0,z8,z2,z4,z787,z6]),(0,[z0,z8,z2,z148,z194,z6]),(0,[z0,z8,z556,z4,z9,z6]),(0,[z0,z8,z2,z788,z5,z6]),(0,[z0,z8,z3,z42,z9,z6]),(0,[z0,z8,z2,z190,z6,z16])],[(0,[z0,z8,z2,z230,z5,z6]),(0,[z0,z789,z2,z4,z5,z6])],[(0,[z136,z26,z2,z97,z5,z6]),(0,[z0,z8,z4,z790,z9,z6]),(0,[z17,z8,z2,z4,z73,z75]),(0,[z791,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z533,z6])],[(0,[z0,z8,z254,z42,z5,z6]),(0,[z0,z8,z2,z792,z5,z6]),(0,[z0,z8,z2,z793,z5,z6]),(0,[z0,z8,z42,z9,z82,z6])],[(0,[z0,z26,z2,z39,z9,z6]),(0,[z0,z26,z149,z4,z5,z6]),(0,[z45,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z18,z225]),(0,[z0,z8,z2,z4,z9,z195]),(0,[z104,z0,z2,z42,z5,z161]),(0,[z0,z8,z2,z4,z794,z6])],[(0,[z0,z137,z2,z4,z5,z209]),(0,[z0,z8,z2,z4,z795,z6]),(0,[z0,z8,z2,z796,z5,z6])],[(0,[z0,z1,z2,z522,z5,z6]),(0,[z0,z797,z2,z4,z5,z6]),(0,[z191,z0,z8,z42,z5,z6]),(0,[z0,z379,z2,z4,z18,z6]),(0,[z0,z8,z798,z4,z5,z6]),(0,[z20,z0,z8,z344,z5,z6]),(0,[z0,z8,z2,z249,z9,z6])],[(0,[z0,z26,z2,z42,z9,z6]),(0,[z0,z8,z2,z4,z799,z6]),(0,[z0,z8,z61,z289,z5,z6]),(0,[z57,z8,z58,z303,z5,z6]),(1,[z0,z8,z42,z133,z6])],[(0,[z128,z0,z26,z42,z5,z6]),(0,[z0,z8,z42,z9,z6,z75]),(0,[z0,z8,z2,z4,z800,z6])],[(0,[z0,z8,z2,z801,z5,z6]),(0,[z0,z2,z4,z9,z6,z802])],[(0,[z0,z26,z2,z4,z177,z6]),(0,[z11,z8,z2,z12,z18,z6]),(0,[z0,z8,z2,z4,z177,z92]),(0,[z0,z8,z2,z4,z803,z6]),(0,[z0,z8,z2,z804,z5,z6]),(0,[z104,z0,z2,z4,z210,z161]),(0,[z0,z8,z43,z4,z416,z135])],[(0,[z0,z8,z2,z4,z5,z805]),(0,[z0,z171,z2,z4,z5,z6]),(0,[z0,z8,z2,z806,z5,z6]),(0,[z0,z807,z2,z4,z5,z6]),(0,[z0,z379,z2,z234,z5,z6]),(0,[z0,z8,z2,z808,z5,z6]),(0,[z0,z8,z2,z21,z9,z6])],[(0,[z41,z1,z2,z39,z5,z6]),(0,[z0,z1,z2,z103,z5,z6]),(0,[z468,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z769]),(0,[z0,z8,z265,z42,z5,z6]),(0,[z0,z8,z131,z809,z5,z6]),(0,[z237,z8,z2,z487,z5,z6])],[(0,[z0,z8,z2,z810,z5,z6]),(0,[z0,z117,z2,z4,z227,z6]),(0,[z375,z0,z8,z42,z5,z6]),(0,[z0,z8,z4,z42,z469,z6]),(0,[z0,z8,z414,z811,z5,z6]),(0,[z0,z812,z2,z4,z5,z6]),(0,[z0,z8,z43,z4,z5,z759])],[(0,[z0,z1,z99,z4,z9,z6]),(0,[z0,z26,z2,z35,z5,z6]),(0,[z0,z8,z2,z813,z5,z6]),(0,[z0,z8,z2,z38,z4,z215]),(0,[z0,z814,z2,z4,z5,z6]),(0,[z815,z8,z2,z4,z5,z6])]],
   [[(0,[z41,z1,z2,z42,z5,z6]),(0,[z0,z8,z103,z5,z9,z6]),(0,[z0,z8,z62,z816,z5,z6]),(0,[z0,z8,z2,z817,z5,z6]),(0,[z0,z8,z2,z42,z410,z6])],[(0,[z8,z58,z4,z9,z6,z75]),(0,[z0,z818,z2,z4,z5,z6]),(0,[z0,z8,z2,z366,z9,z6]),(0,[z0,z8,z2,z819,z5,z6]),(0,[z0,z8,z39,z18,z42,z6]),(0,[z0,z8,z2,z820,z5,z6])],[(0,[z0,z8,z2,z4,z5,z821]),(0,[z57,z8,z822,z4,z5,z6]),(0,[z45,z8,z2,z4,z9,z92])],[(0,[z0,z8,z2,z4,z823,z6]),(0,[z1,z2,z58,z4,z18,z6]),(0,[z321,z0,z296,z4,z5,z6]),(0,[z0,z26,z174,z4,z5,z6]),(0,[z0,z26,z4,z42,z9,z6]),(0,[z84,z8,z61,z42,z5,z6]),(0,[z0,z276,z2,z4,z9,z6]),(0,[z0,z8,z174,z4,z5,z92]),(0,[z0,z8,z2,z238,z9,z6]),(0,[z471,z8,z2,z223,z5,z6])],[(0,[z0,z1,z2,z148,z4,z6]),(0,[z0,z824,z8,z2,z4,z6]),(0,[z136,z8,z2,z825,z5,z6]),(0,[z0,z826,z2,z4,z5,z6]),(0,[z0,z827,z8,z2,z39,z6])],[(0,[z0,z22,z2,z4,z5,z6]),(0,[z0,z8,z2,z828,z5,z6]),(0,[z0,z8,z2,z829,z5,z6]),(0,[z45,z8,z2,z4,z5,z519]),(0,[z0,z758,z2,z39,z5,z6])],[(0,[z0,z8,z2,z830,z5,z6]),(0,[z0,z317,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z478,z6]),(0,[z0,z8,z174,z4,z831,z6]),(0,[z0,z8,z2,z4,z5,z832]),(0,[z0,z8,z2,z833,z5,z6]),(0,[z0,z755,z2,z42,z5,z6])],[(0,[z0,z834,z2,z4,z5,z6]),(0,[z8,z58,z4,z5,z6,z445]),(0,[z0,z50,z2,z4,z5,z225]),(0,[z0,z8,z835,z4,z5,z6]),(0,[z0,z8,z42,z9,z24,z6]),(0,[z0,z8,z2,z719,z18,z6]),(0,[z0,z111,z8,z305,z5,z6]),(0,[z0,z8,z2,z4,z5,z836])],[(0,[z1,z2,z58,z4,z5,z6]),(0,[z0,z8,z837,z4,z5,z6]),(0,[z0,z8,z838,z4,z5,z6]),(0,[z8,z2,z12,z825,z5,z6]),(0,[z0,z8,z180,z42,z5,z6]),(0,[z104,z0,z2,z4,z18,z161])],[(0,[z0,z26,z414,z4,z5,z6]),(0,[z0,z8,z2,z4,z839,z6]),(0,[z0,z8,z42,z652,z5,z6])],[(0,[z0,z1,z2,z4,z315,z6]),(0,[z0,z8,z58,z522,z5,z6]),(0,[z84,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z840,z6])],[(0,[z0,z1,z2,z584,z5,z6]),(0,[z0,z8,z2,z4,z469,z6]),(0,[z0,z430,z2,z42,z5,z6]),(0,[z28,z8,z2,z39,z82,z6]),(0,[z334,z0,z8,z4,z5,z182]),(0,[z0,z8,z2,z841,z5,z6]),(0,[z0,z8,z2,z4,z842,z6])],[(0,[z0,z1,z2,z286,z5,z6]),(0,[z84,z22,z2,z4,z5,z6]),(0,[z0,z843,z2,z4,z5,z6]),(0,[z0,z844,z2,z4,z5,z6]),(0,[z0,z8,z62,z4,z845,z6]),(0,[z0,z8,z284,z42,z5,z6]),(0,[z0,z183,z2,z4,z121,z6])],[(0,[z308,z1,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z108,z90]),(0,[z49,z0,z3,z39,z5,z6]),(0,[z0,z8,z105,z4,z9,z6])],[(0,[z0,z8,z2,z4,z846,z6]),(0,[z0,z8,z2,z847,z5,z6]),(0,[z0,z8,z2,z4,z227,z146]),(0,[z0,z8,z2,z4,z848,z6]),(0,[z28,z8,z2,z42,z82,z6]),(0,[z0,z554,z8,z42,z5,z6]),(0,[z0,z849,z2,z4,z9,z6]),(0,[z0,z8,z850,z4,z5,z6])],[(1,[z0,z1,z42,z9,z6]),(0,[z84,z310,z61,z4,z5,z6]),(0,[z0,z8,z2,z4,z473,z6]),(0,[z0,z8,z2,z851,z5,z6]),(0,[z159,z0,z8,z4,z410,z182]),(0,[z0,z852,z2,z4,z5,z6])]],
   [[(0,[z0,z26,z2,z4,z9,z6]),(0,[z0,z8,z853,z4,z5,z6]),(0,[z0,z8,z2,z4,z854,z6]),(0,[z0,z8,z2,z4,z855,z6]),(0,[z20,z0,z8,z39,z18,z6])],[(0,[z0,z117,z2,z4,z5,z146]),(0,[z0,z8,z2,z289,z5,z445]),(0,[z384,z0,z8,z2,z4,z14]),(0,[z0,z8,z2,z4,z856,z6])],[(0,[z0,z1,z58,z4,z9,z6]),(0,[z393,z8,z2,z4,z82,z6]),(0,[z0,z8,z2,z857,z5,z6]),(0,[z0,z8,z2,z194,z9,z166])],[(0,[z0,z1,z43,z4,z5,z135]),(0,[z0,z858,z2,z4,z5,z6]),(0,[z0,z8,z2,z35,z18,z6]),(0,[z0,z8,z2,z81,z9,z6]),(0,[z0,z8,z62,z4,z859,z6]),(0,[z0,z8,z2,z299,z9,z6])],[(0,[z0,z26,z2,z4,z5,z445]),(0,[z17,z26,z2,z4,z5,z75]),(0,[z627,z8,z2,z4,z5,z75]),(0,[z0,z8,z4,z18,z652,z6]),(0,[z0,z8,z860,z4,z5,z6])],[(0,[z280,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z445]),(0,[z0,z8,z131,z4,z9,z6]),(0,[z8,z2,z4,z825,z5,z6]),(0,[z552,z0,z3,z4,z5,z6]),(0,[z0,z8,z2,z861,z5,z6]),(0,[z0,z138,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z862,z6]),(0,[z0,z8,z863,z4,z5,z6]),(0,[z84,z8,z61,z4,z18,z6]),(0,[z0,z8,z864,z4,z5,z6]),(0,[z28,z8,z2,z4,z82,z215])],[(0,[z57,z8,z58,z4,z9,z6]),(0,[z11,z0,z8,z2,z148,z6]),(0,[z484,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z4,z108,z679]),(0,[z0,z8,z2,z4,z865,z6]),(0,[z0,z8,z134,z42,z9,z6]),(0,[z0,z8,z2,z39,z5,z866])],[(0,[z41,z1,z2,z4,z5,z6]),(0,[z0,z8,z867,z4,z5,z6]),(0,[z0,z8,z2,z199,z262,z6]),(0,[z0,z8,z2,z868,z5,z6]),(0,[z0,z138,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z108,z489]),(0,[z0,z8,z2,z4,z869,z6]),(0,[z0,z432,z8,z2,z4,z14])],[(0,[z0,z8,z139,z4,z9,z6]),(0,[z0,z8,z2,z42,z262,z6]),(0,[z0,z8,z2,z870,z5,z6])],[(0,[z0,z1,z2,z40,z5,z6]),(0,[z0,z8,z141,z4,z9,z6]),(0,[z871,z8,z2,z4,z5,z6]),(0,[z0,z8,z4,z733,z9,z6])],[(0,[z0,z8,z2,z4,z5,z872]),(0,[z0,z8,z2,z4,z873,z6]),(0,[z170,z1,z2,z4,z5,z6]),(0,[z25,z8,z58,z42,z5,z6]),(0,[z310,z2,z4,z5,z6,z75]),(0,[z136,z8,z2,z97,z9,z6]),(0,[z0,z8,z2,z39,z533,z6]),(0,[z0,z477,z2,z4,z53,z6])],[(0,[z294,z8,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z874,z6]),(0,[z0,z8,z144,z4,z9,z6]),(0,[z7,z0,z8,z2,z4,z311])],[(0,[z0,z8,z2,z303,z5,z445]),(0,[z0,z8,z58,z4,z315,z6]),(0,[z0,z8,z4,z147,z9,z6]),(0,[z0,z8,z149,z4,z9,z6]),(0,[z0,z8,z2,z88,z441,z6])],[(0,[z0,z1,z2,z4,z51,z6]),(0,[z0,z430,z2,z4,z18,z6]),(1,[z0,z8,z103,z9,z6]),(0,[z0,z8,z61,z4,z343,z6]),(0,[z0,z8,z875,z4,z5,z6]),(0,[z0,z8,z2,z42,z533,z6])],[(0,[z1,z58,z4,z42,z5,z6]),(0,[z0,z1,z2,z4,z876,z6]),(0,[z535,z0,z8,z2,z4,z14]),(0,[z0,z598,z2,z63,z5,z6]),(0,[z0,z8,z284,z4,z18,z6]),(1,[z0,z8,z2,z4,z784])]],
   [[(0,[z0,z8,z877,z366,z5,z6]),(0,[z878,z8,z2,z4,z5,z6]),(0,[z0,z111,z8,z2,z6,z48])],[(0,[z8,z2,z822,z4,z5,z6]),(0,[z0,z8,z99,z39,z5,z6]),(0,[z0,z111,z8,z2,z197,z6])],[(0,[z0,z8,z879,z4,z5,z6]),(0,[z0,z880,z2,z4,z5,z6]),(0,[z11,z0,z8,z305,z5,z6]),(0,[z0,z642,z2,z37,z5,z6]),(0,[z7,z0,z8,z2,z42,z14]),(0,[z422,z881,z2,z4,z5,z6])],[(0,[z0,z8,z61,z4,z9,z6]),(0,[z0,z8,z62,z4,z5,z6]),(0,[z84,z8,z61,z4,z147,z6])],[(0,[z0,z171,z2,z39,z5,z6]),(0,[z325,z0,z8,z4,z5,z182]),(0,[z0,z2,z4,z5,z882,z161]),(0,[z0,z8,z2,z4,z416,z6]),(0,[z0,z8,z2,z4,z108,z142])],[(0,[z0,z8,z232,z4,z775,z6])],[(0,[z0,z26,z61,z42,z5,z6]),(0,[z0,z8,z2,z4,z91,z146]),(0,[z28,z8,z2,z234,z82,z6]),(0,[z0,z407,z2,z4,z9,z6])],[(0,[z0,z250,z2,z37,z5,z6]),(0,[z17,z8,z2,z4,z177,z75]),(0,[z0,z171,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z6,z883])],[(0,[z0,z8,z2,z4,z18,z445]),(0,[z49,z0,z3,z4,z5,z6]),(0,[z468,z8,z2,z42,z5,z6]),(0,[z0,z8,z10,z39,z5,z6]),(0,[z0,z884,z2,z4,z5,z6])],[(0,[z0,z8,z703,z4,z9,z6]),(0,[z0,z885,z2,z4,z5,z6]),(0,[z0,z8,z2,z18,z103,z6])],[(0,[z1,z43,z58,z4,z5,z6]),(0,[z11,z26,z2,z12,z5,z6]),(0,[z0,z26,z2,z4,z316,z6]),(0,[z7,z0,z26,z2,z4,z14]),(0,[z0,z8,z414,z4,z147,z6])],[(0,[z0,z379,z131,z4,z5,z6]),(0,[z0,z8,z174,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z886]),(0,[z0,z138,z2,z4,z18,z6])],[(0,[z0,z15,z1,z2,z5,z16]),(0,[z0,z22,z2,z289,z5,z6]),(0,[z0,z270,z2,z4,z9,z6]),(0,[z0,z8,z113,z584,z9,z6]),(0,[z0,z8,z2,z286,z6,z14])],[(1,[z1,z58,z42,z5,z6]),(0,[z1,z2,z4,z5,z6,z480]),(0,[z0,z8,z2,z4,z887,z6]),(0,[z112,z332,z2,z4,z5,z6]),(0,[z109,z8,z2,z448,z5,z6])],[(0,[z0,z179,z1,z2,z4,z6]),(0,[z0,z26,z2,z4,z331,z6]),(0,[z0,z888,z8,z2,z4,z6]),(0,[z0,z8,z889,z4,z5,z6]),(0,[z0,z317,z2,z39,z5,z6]),(0,[z0,z8,z2,z890,z5,z6]),(0,[z0,z8,z2,z382,z5,z6]),(0,[z0,z8,z105,z4,z714,z6]),(0,[z0,z891,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z190,z6]),(0,[z393,z8,z2,z97,z5,z6]),(0,[z17,z8,z174,z4,z5,z75]),(0,[z0,z8,z2,z892,z5,z6]),(0,[z0,z8,z39,z42,z5,z6]),(0,[z0,z826,z2,z42,z5,z6]),(0,[z0,z8,z893,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z38,z93,z6]),(0,[z0,z22,z2,z42,z5,z6]),(0,[z0,z8,z2,z230,z18,z6]),(0,[z483,z8,z2,z4,z5,z92]),(0,[z0,z8,z42,z5,z470,z6]),(0,[z372,z0,z8,z42,z9,z6]),(0,[z422,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z761,z9,z6])],[(0,[z0,z8,z2,z42,z478,z6]),(0,[z0,z8,z414,z4,z9,z6]),(0,[z0,z317,z2,z42,z5,z6]),(0,[z0,z8,z42,z9,z92,z6]),(0,[z0,z456,z2,z101,z5,z6]),(0,[z0,z8,z2,z194,z190,z166])],[(0,[z0,z8,z2,z4,z5,z866]),(0,[z0,z8,z2,z4,z894,z6]),(0,[z0,z8,z603,z39,z5,z6]),(0,[z0,z30,z2,z230,z5,z6]),(0,[z0,z8,z2,z895,z5,z6]),(0,[z0,z896,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z132]),(0,[z0,z8,z2,z897,z5,z6])],[(0,[z11,z0,z8,z42,z9,z6]),(0,[z104,z0,z105,z4,z5,z161])],[(0,[z1,z2,z495,z4,z5,z6]),(0,[z0,z1,z186,z4,z5,z6]),(0,[z0,z8,z2,z898,z5,z6]),(0,[z0,z8,z38,z42,z9,z6]),(0,[z0,z899,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z900]),(0,[z0,z8,z2,z901,z5,z6]),(0,[z0,z8,z2,z42,z469,z6]),(0,[z0,z8,z21,z42,z5,z6]),(0,[z158,z0,z8,z2,z4,z311]),(0,[z0,z8,z2,z653,z93,z6])],[(0,[z0,z8,z2,z4,z902,z6]),(0,[z0,z8,z2,z39,z473,z6]),(0,[z0,z8,z39,z638,z5,z6]),(0,[z0,z521,z2,z39,z5,z6]),(0,[z0,z8,z2,z194,z190,z6]),(0,[z0,z8,z2,z4,z6,z784])],[(0,[z0,z22,z2,z303,z5,z6]),(0,[z20,z0,z8,z4,z147,z6]),(0,[z0,z8,z212,z4,z478,z6]),(0,[z0,z543,z8,z2,z83,z6]),(0,[z903,z8,z2,z4,z5,z6])],[(0,[z112,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z18,z42,z6]),(0,[z0,z8,z42,z5,z156,z6]),(0,[z0,z904,z2,z4,z5,z6]),(0,[z0,z8,z60,z4,z9,z6])],[(0,[z0,z8,z2,z42,z473,z6]),(0,[z0,z171,z2,z4,z18,z6])],[(0,[z0,z8,z2,z905,z4,z6]),(0,[z0,z8,z349,z42,z5,z6]),(0,[z333,z0,z8,z4,z5,z182]),(0,[z906,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z855,z6]),(0,[z468,z8,z2,z4,z18,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z907,z2,z4,z5,z6]),(0,[z17,z8,z2,z4,z9,z75]),(0,[z0,z8,z2,z42,z856,z6])],[(0,[z0,z1,z2,z124,z5,z6]),(0,[z0,z8,z908,z4,z5,z6]),(0,[z0,z8,z131,z4,z203,z6]),(0,[z0,z8,z2,z4,z909,z6]),(0,[z0,z8,z2,z910,z5,z6]),(0,[z0,z8,z2,z911,z5,z6])],[(0,[z8,z2,z825,z97,z5,z6]),(0,[z0,z8,z2,z230,z73,z6]),(0,[z0,z8,z2,z5,z6,z912])],[(0,[z0,z111,z8,z2,z148,z6]),(0,[z0,z8,z4,z913,z5,z6])]],
   [[(0,[z0,z490,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z119]),(0,[z0,z8,z2,z4,z5,z914]),(0,[z0,z8,z2,z4,z262,z195]),(0,[z0,z8,z2,z915,z5,z6]),(0,[z0,z8,z4,z5,z135,z759])],[(0,[z0,z1,z2,z4,z133,z6]),(0,[z0,z8,z212,z4,z473,z6]),(0,[z0,z8,z99,z4,z133,z6]),(0,[z0,z8,z358,z42,z5,z6]),(0,[z20,z0,z8,z21,z18,z6]),(0,[z0,z916,z2,z4,z5,z6])],[(0,[z41,z917,z2,z4,z5,z6]),(0,[z0,z918,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z410,z6]),(0,[z0,z8,z2,z4,z919,z6]),(0,[z0,z8,z4,z18,z9,z6]),(0,[z0,z8,z2,z920,z5,z6])],[(0,[z84,z1,z2,z4,z5,z6]),(0,[z0,z22,z2,z4,z18,z6])],[(0,[z0,z1,z2,z5,z6,z921]),(0,[z0,z317,z2,z4,z18,z6]),(0,[z0,z2,z3,z4,z5,z225]),(0,[z104,z0,z149,z4,z5,z161]),(0,[z0,z15,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z395,z386])],[(0,[z0,z8,z2,z922,z5,z6]),(0,[z0,z8,z232,z4,z478,z6]),(1,[z0,z8,z42,z9,z6]),(0,[z0,z8,z42,z42,z9,z6]),(0,[z0,z8,z2,z299,z410,z6])],[(0,[z84,z171,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z209]),(0,[z0,z8,z2,z4,z5,z923]),(0,[z0,z8,z924,z4,z5,z6]),(0,[z0,z8,z2,z5,z6,z348]),(0,[z0,z8,z2,z925,z5,z6])],[(0,[z565,z1,z2,z4,z5,z6]),(0,[z304,z1,z2,z4,z5,z6]),(0,[z294,z8,z58,z42,z5,z6]),(0,[z0,z926,z2,z4,z5,z6]),(0,[z0,z8,z2,z147,z103,z6]),(0,[z0,z632,z8,z2,z5,z16]),(0,[z0,z379,z414,z4,z5,z6]),(0,[z0,z8,z131,z35,z5,z6])],[(0,[z143,z1,z2,z4,z5,z6]),(0,[z96,z0,z2,z4,z5,z539]),(0,[z0,z927,z2,z4,z5,z6])],[(0,[z84,z8,z359,z4,z5,z6])],[(0,[z0,z8,z2,z928,z5,z6]),(0,[z25,z917,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z929]),(0,[z294,z8,z2,z97,z5,z6]),(0,[z0,z8,z97,z42,z9,z6]),(0,[z0,z8,z2,z930,z5,z6]),(0,[z0,z843,z2,z4,z18,z6]),(0,[z0,z931,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z932]),(0,[z422,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z933,z5,z6]),(0,[z0,z8,z61,z39,z9,z6]),(0,[z0,z8,z62,z39,z5,z6]),(0,[z0,z8,z2,z934,z5,z6])],[(0,[z0,z8,z58,z18,z42,z6]),(0,[z0,z8,z2,z935,z4,z6]),(0,[z0,z8,z2,z4,z9,z225]),(0,[z0,z8,z2,z936,z5,z6]),(0,[z0,z8,z99,z749,z5,z6]),(0,[z0,z8,z2,z39,z416,z6])],[(0,[z0,z8,z2,z5,z6,z937]),(0,[z0,z8,z2,z4,z938,z6]),(0,[z0,z939,z2,z4,z5,z6])],[(0,[z0,z8,z61,z42,z9,z6]),(0,[z0,z8,z232,z4,z473,z6]),(0,[z0,z379,z2,z4,z9,z6]),(0,[z0,z8,z62,z42,z5,z6]),(0,[z294,z8,z2,z335,z5,z6]),(0,[z0,z8,z2,z38,z441,z6]),(0,[z0,z554,z8,z305,z5,z6])],[(0,[z0,z8,z2,z35,z203,z6]),(0,[z0,z8,z2,z4,z940,z6]),(0,[z468,z8,z2,z4,z5,z135])]],
   [[(0,[z1,z2,z4,z527,z5,z6]),(0,[z0,z941,z1,z2,z4,z6]),(0,[z28,z26,z2,z4,z82,z6]),(0,[z628,z0,z8,z4,z5,z182]),(0,[z0,z8,z43,z4,z5,z242]),(0,[z0,z580,z8,z2,z5,z16]),(0,[z0,z8,z2,z4,z942,z6]),(0,[z20,z0,z8,z943,z5,z6])],[(0,[z0,z481,z2,z4,z231,z6]),(0,[z159,z0,z26,z4,z5,z182]),(0,[z0,z8,z2,z83,z5,z209]),(0,[z72,z0,z8,z2,z366,z6]),(0,[z0,z8,z2,z39,z243,z6])],[(0,[z11,z8,z2,z12,z9,z6]),(0,[z0,z317,z2,z4,z73,z6]),(0,[z49,z0,z3,z199,z5,z6]),(0,[z0,z521,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z6,z883])],[(0,[z0,z8,z944,z4,z5,z6]),(0,[z0,z8,z2,z38,z35,z6]),(0,[z28,z8,z2,z81,z82,z6]),(0,[z0,z8,z2,z4,z945,z6]),(0,[z49,z0,z3,z42,z5,z6]),(0,[z241,z153,z2,z4,z5,z6])],[(0,[z0,z435,z2,z36,z5,z6]),(0,[z0,z8,z42,z9,z6,z161]),(0,[z0,z8,z358,z4,z18,z6])],[(0,[z28,z8,z131,z4,z82,z6]),(0,[z0,z8,z2,z4,z92,z201]),(0,[z0,z8,z2,z4,z5,z946])],[(0,[z41,z1,z2,z4,z18,z6]),(0,[z45,z1,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z331,z195])],[(0,[z0,z8,z2,z4,z947,z6]),(0,[z0,z111,z26,z2,z83,z6]),(0,[z0,z8,z39,z749,z5,z6])],[(0,[z0,z8,z2,z4,z948,z6]),(0,[z0,z949,z2,z4,z5,z6]),(0,[z0,z8,z2,z950,z5,z6]),(0,[z0,z8,z2,z194,z5,z502]),(0,[z0,z951,z3,z4,z5,z6])],[(0,[z0,z117,z2,z4,z91,z6]),(0,[z0,z8,z2,z952,z5,z6]),(0,[z0,z8,z2,z4,z953,z6]),(0,[z0,z8,z174,z4,z177,z6]),(0,[z954,z8,z2,z4,z5,z6])],[(0,[z1,z2,z58,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z955]),(0,[z0,z8,z2,z956,z5,z6]),(0,[z691,z0,z8,z2,z4,z14]),(0,[z0,z8,z2,z4,z100,z6]),(0,[z0,z8,z2,z957,z5,z6]),(0,[z0,z958,z2,z4,z5,z6]),(0,[z0,z8,z138,z4,z5,z182])],[(0,[z0,z26,z2,z4,z262,z6]),(0,[z0,z959,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z132]),(0,[z0,z8,z42,z126,z9,z6]),(0,[z0,z8,z149,z765,z5,z6]),(0,[z0,z8,z2,z960,z42,z6])],[(0,[z0,z961,z2,z4,z5,z6]),(0,[z0,z8,z2,z743,z5,z6]),(0,[z0,z111,z8,z42,z9,z6]),(0,[z0,z8,z305,z5,z6,z16]),(0,[z0,z8,z2,z194,z166,z201])],[(0,[z0,z8,z2,z962,z5,z6]),(0,[z237,z8,z2,z39,z5,z6]),(0,[z0,z8,z113,z4,z9,z6]),(0,[z0,z138,z2,z299,z5,z6])],[(0,[z0,z8,z254,z4,z9,z6]),(0,[z57,z8,z58,z4,z5,z445]),(0,[z0,z8,z2,z42,z5,z132]),(0,[z0,z8,z2,z963,z5,z6]),(0,[z0,z153,z8,z42,z9,z6])],[(0,[z0,z26,z2,z230,z5,z6]),(0,[z0,z8,z2,z964,z5,z6]),(0,[z0,z8,z2,z230,z5,z92]),(0,[z0,z8,z2,z382,z210,z6]),(0,[z104,z0,z2,z4,z9,z161]),(0,[z0,z8,z99,z39,z18,z6])]],
   [[(0,[z0,z8,z2,z4,z965,z6]),(0,[z0,z26,z2,z4,z533,z6]),(0,[z0,z8,z2,z4,z966,z6]),(0,[z0,z8,z2,z967,z5,z6]),(0,[z0,z8,z2,z4,z968,z6]),(0,[z0,z8,z2,z969,z5,z6])],[(0,[z0,z8,z62,z4,z18,z6]),(0,[z0,z8,z4,z152,z9,z6]),(0,[z216,z8,z2,z208,z5,z6])],[(0,[z0,z2,z4,z5,z6,z882]),(0,[z0,z8,z2,z911,z4,z6])],[(0,[z0,z8,z2,z4,z6,z970]),(1,[z0,z8,z4,z913,z6]),(0,[z0,z8,z414,z35,z5,z6]),(0,[z0,z30,z62,z4,z5,z6]),(0,[z0,z8,z2,z382,z221,z6]),(0,[z0,z8,z399,z39,z5,z6]),(0,[z0,z8,z2,z299,z533,z6]),(0,[z0,z8,z4,z5,z759,z182])],[(0,[z0,z1,z2,z39,z5,z6]),(0,[z1,z2,z425,z4,z5,z6]),(0,[z0,z971,z2,z4,z5,z6]),(0,[z0,z8,z2,z366,z478,z6])],[(0,[z109,z8,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z799,z6]),(0,[z0,z8,z212,z4,z5,z132])],[(0,[z0,z1,z2,z199,z5,z6]),(0,[z0,z276,z2,z4,z478,z6]),(0,[z0,z8,z131,z793,z5,z6]),(0,[z0,z8,z2,z4,z972,z6]),(0,[z49,z0,z3,z4,z18,z6])],[(0,[z0,z1,z2,z42,z5,z6])],[(0,[z0,z1,z2,z4,z973,z6]),(0,[z1,z2,z4,z5,z6,z555]),(0,[z0,z490,z2,z39,z5,z6]),(0,[z974,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z975,z5,z6]),(0,[z0,z554,z8,z2,z197,z6]),(0,[z0,z8,z2,z4,z6,z976])],[(0,[z0,z8,z2,z4,z977,z6]),(0,[z0,z978,z2,z4,z5,z6]),(0,[z0,z979,z2,z4,z5,z6]),(0,[z0,z8,z42,z9,z65,z6]),(0,[z0,z8,z236,z42,z9,z6])],[(0,[z41,z1,z2,z4,z9,z6]),(0,[z468,z26,z2,z4,z5,z6]),(0,[z0,z8,z61,z4,z5,z445]),(0,[z0,z8,z2,z4,z5,z980]),(0,[z0,z8,z2,z35,z9,z6]),(0,[z0,z8,z2,z4,z331,z225]),(0,[z20,z0,z8,z42,z9,z6]),(0,[z0,z8,z943,z42,z5,z6])],[(0,[z0,z8,z2,z981,z5,z6]),(0,[z84,z1,z2,z39,z5,z6]),(0,[z0,z8,z547,z4,z9,z6]),(0,[z0,z8,z2,z982,z5,z6]),(0,[z0,z490,z2,z42,z5,z6]),(0,[z0,z8,z404,z42,z5,z6])],[(0,[z0,z8,z983,z4,z5,z6]),(0,[z0,z26,z2,z813,z5,z6]),(0,[z0,z26,z4,z18,z9,z6]),(0,[z45,z8,z58,z42,z5,z6]),(0,[z0,z8,z2,z984,z5,z6]),(0,[z0,z8,z2,z4,z243,z6]),(0,[z0,z8,z2,z382,z18,z6]),(0,[z0,z138,z4,z5,z6,z182])],[(0,[z0,z1,z2,z4,z210,z6]),(0,[z0,z8,z359,z42,z5,z6]),(0,[z0,z55,z2,z4,z231,z6]),(0,[z84,z8,z61,z4,z9,z6]),(0,[z0,z183,z2,z4,z13,z6]),(0,[z468,z8,z2,z299,z5,z6])],[(0,[z84,z1,z2,z42,z5,z6]),(0,[z0,z1,z212,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z209]),(0,[z0,z8,z2,z752,z9,z6])],[(0,[z0,z1,z2,z4,z5,z215]),(0,[z0,z8,z2,z985,z5,z6]),(0,[z0,z276,z2,z4,z473,z6]),(0,[z0,z8,z62,z4,z73,z6]),(0,[z0,z8,z39,z305,z5,z6])]],
   [[(0,[z0,z8,z2,z986,z5,z6]),(0,[z0,z8,z2,z4,z5,z987]),(0,[z8,z61,z58,z42,z5,z6]),(0,[z0,z8,z2,z4,z5,z988]),(0,[z159,z0,z138,z4,z5,z182]),(0,[z159,z0,z8,z4,z533,z182]),(0,[z0,z8,z2,z83,z6,z246])],[(0,[z45,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z221,z6]),(0,[z0,z8,z2,z4,z989,z6]),(0,[z333,z8,z58,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z209]),(0,[z0,z8,z2,z4,z18,z132]),(0,[z28,z8,z414,z4,z82,z6]),(0,[z28,z8,z2,z4,z163,z6])],[(0,[z0,z26,z2,z829,z5,z6]),(0,[z0,z8,z232,z4,z5,z132]),(0,[z0,z8,z180,z4,z9,z6]),(0,[z0,z8,z2,z5,z6,z990]),(0,[z0,z8,z2,z991,z5,z6])],[(0,[z0,z26,z2,z4,z478,z6]),(0,[z0,z8,z149,z4,z800,z6]),(0,[z0,z8,z4,z100,z9,z6])],[(0,[z0,z8,z2,z4,z992,z6]),(0,[z241,z8,z2,z382,z5,z6]),(0,[z0,z8,z2,z993,z4,z6])],[(0,[z422,z26,z2,z4,z5,z6]),(0,[z0,z430,z2,z4,z9,z6]),(0,[z0,z2,z4,z5,z6,z802])],[(0,[z0,z8,z2,z4,z5,z146]),(0,[z0,z8,z58,z289,z5,z6]),(0,[z0,z8,z994,z4,z5,z6]),(0,[z0,z995,z2,z4,z5,z6]),(0,[z422,z8,z2,z42,z5,z6]),(0,[z0,z8,z233,z39,z5,z6]),(0,[z0,z996,z2,z4,z5,z6])],[(0,[z0,z8,z2,z997,z5,z6]),(0,[z0,z8,z2,z4,z998,z6]),(0,[z0,z196,z2,z37,z5,z6]),(0,[z0,z8,z42,z9,z6,z16])],[(0,[z237,z8,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z90,z75]),(0,[z0,z26,z2,z4,z469,z6]),(0,[z0,z999,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z1000,z6]),(0,[z0,z8,z212,z4,z5,z209]),(0,[z0,z8,z2,z1001,z5,z6]),(0,[z422,z8,z2,z299,z5,z6])],[(0,[z57,z22,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z1002,z6]),(0,[z0,z8,z2,z1003,z5,z6]),(0,[z0,z1004,z8,z2,z42,z6]),(0,[z0,z8,z42,z5,z6,z256]),(0,[z0,z8,z2,z4,z5,z759])],[(0,[z0,z1,z2,z4,z18,z6]),(0,[z0,z8,z58,z42,z5,z6]),(0,[z0,z8,z2,z1005,z5,z6]),(0,[z49,z0,z3,z4,z5,z195]),(0,[z0,z8,z4,z193,z9,z6])],[(0,[z0,z1,z232,z4,z5,z6]),(0,[z0,z8,z298,z4,z5,z135]),(0,[z0,z8,z2,z18,z344,z6])],[(0,[z0,z1,z2,z1006,z5,z6]),(0,[z0,z26,z2,z4,z473,z6]),(0,[z0,z8,z2,z4,z1007,z6]),(0,[z372,z8,z58,z4,z5,z6]),(0,[z0,z8,z2,z1008,z4,z6]),(0,[z30,z2,z4,z5,z6,z75]),(0,[z8,z2,z174,z4,z5,z75]),(0,[z468,z8,z4,z5,z6,z182])],[(0,[z8,z2,z58,z4,z5,z445]),(0,[z0,z8,z2,z4,z1009,z6]),(0,[z275,z8,z2,z4,z5,z92]),(0,[z0,z521,z2,z42,z5,z6]),(0,[z20,z0,z8,z4,z766,z6])],[(0,[z136,z8,z2,z97,z478,z6]),(0,[z0,z490,z2,z4,z18,z6]),(0,[z0,z8,z4,z305,z108,z6])],[(0,[z323,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z234,z5,z6]),(0,[z0,z8,z2,z4,z9,z445]),(0,[z0,z154,z8,z42,z9,z6]),(0,[z0,z521,z2,z299,z5,z6])]],
   [[(0,[z0,z1010,z2,z4,z5,z6]),(0,[z0,z379,z2,z35,z5,z6]),(1,[z0,z8,z715,z5,z6]),(0,[z0,z8,z531,z39,z5,z6]),(0,[z0,z8,z4,z18,z766,z6]),(0,[z0,z8,z2,z920,z18,z6]),(0,[z0,z8,z2,z416,z522,z6]),(0,[z0,z8,z2,z60,z83,z6])],[(0,[z84,z1,z2,z4,z18,z6]),(0,[z0,z8,z131,z38,z4,z6]),(0,[z1011,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z1012,z6])],[(0,[z241,z1,z2,z4,z5,z6]),(0,[z0,z8,z42,z9,z6,z431]),(0,[z0,z8,z2,z39,z100,z6]),(0,[z0,z138,z2,z4,z9,z6]),(0,[z0,z138,z2,z4,z5,z135]),(0,[z0,z8,z4,z1013,z5,z6])],[(0,[z0,z8,z105,z870,z5,z6])],[(0,[z0,z8,z2,z12,z478,z6]),(0,[z0,z8,z2,z4,z18,z209]),(0,[z28,z8,z2,z366,z82,z6]),(0,[z0,z8,z2,z4,z6,z1014])],[(0,[z0,z8,z463,z42,z5,z6]),(0,[z25,z8,z58,z4,z9,z6]),(0,[z0,z1015,z2,z4,z5,z6]),(0,[z511,z0,z8,z4,z5,z182]),(0,[z0,z8,z232,z4,z5,z209]),(0,[z0,z8,z2,z4,z1016,z6]),(0,[z0,z8,z113,z39,z9,z6]),(0,[z0,z8,z1017,z2,z5,z6])],[(0,[z0,z941,z8,z2,z4,z6]),(0,[z0,z8,z2,z148,z6,z16]),(0,[z0,z317,z2,z4,z177,z6]),(0,[z0,z8,z2,z1018,z5,z6]),(0,[z0,z8,z2,z4,z1019,z6]),(0,[z0,z8,z2,z1020,z5,z6]),(0,[z0,z8,z302,z42,z9,z6]),(0,[z0,z1021,z2,z4,z5,z6])],[(0,[z45,z8,z2,z4,z5,z307]),(0,[z136,z8,z2,z97,z473,z6]),(0,[z0,z8,z2,z4,z1022,z6]),(0,[z0,z8,z2,z230,z9,z6]),(0,[z0,z377,z8,z2,z5,z118])],[(0,[z0,z1023,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z73,z6]),(0,[z0,z8,z2,z4,z1024,z6]),(0,[z0,z8,z131,z4,z634,z6]),(0,[z0,z8,z2,z1025,z5,z6]),(0,[z0,z8,z113,z42,z9,z6]),(0,[z0,z8,z2,z39,z966,z6])],[(0,[z0,z1,z2,z344,z5,z6]),(0,[z0,z8,z1026,z4,z5,z6]),(0,[z0,z8,z1027,z4,z5,z6]),(0,[z0,z8,z2,z4,z1028,z6]),(0,[z0,z8,z2,z88,z470,z6]),(0,[z422,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z4,z6,z201])],[(0,[z660,z8,z58,z4,z5,z6]),(0,[z0,z8,z2,z1029,z5,z6]),(0,[z0,z8,z2,z4,z1030,z6]),(0,[z0,z8,z2,z5,z6,z1031]),(0,[z0,z8,z2,z4,z6,z1032])],[(0,[z0,z8,z2,z39,z227,z6]),(0,[z17,z8,z2,z230,z5,z75]),(0,[z0,z8,z2,z1033,z5,z6])],[(0,[z0,z247,z2,z4,z5,z6]),(0,[z0,z8,z2,z1034,z5,z6]),(0,[z0,z8,z2,z4,z1035,z6])],[(0,[z372,z8,z2,z4,z82,z6]),(0,[z0,z55,z2,z4,z13,z6]),(0,[z109,z8,z2,z39,z5,z6]),(0,[z649,z0,z2,z4,z5,z161])],[(0,[z0,z1,z2,z4,z5,z195]),(0,[z0,z26,z99,z39,z5,z6]),(0,[z0,z117,z2,z39,z5,z6]),(0,[z28,z379,z2,z4,z82,z6]),(0,[z0,z317,z174,z4,z5,z6]),(0,[z49,z0,z3,z4,z5,z225]),(0,[z0,z2,z4,z743,z5,z6]),(0,[z0,z8,z4,z9,z6,z640]),(0,[z0,z468,z8,z4,z5,z182])],[(0,[z0,z1036,z2,z4,z5,z6]),(0,[z0,z1037,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z58,z42,z5,z6]),(0,[z0,z26,z61,z4,z9,z6]),(0,[z0,z26,z62,z4,z5,z6]),(0,[z0,z111,z8,z2,z213,z6]),(0,[z112,z8,z2,z487,z5,z6]),(0,[z0,z8,z2,z4,z6,z1038]),(0,[z109,z8,z2,z42,z5,z6]),(0,[z0,z521,z2,z4,z18,z6]),(0,[z0,z116,z8,z412,z2,z6])],[(0,[z0,z8,z2,z4,z1039,z6]),(0,[z0,z26,z2,z4,z416,z6]),(0,[z0,z117,z2,z42,z5,z6]),(0,[z136,z179,z8,z2,z97,z6]),(0,[z0,z1040,z2,z4,z5,z6]),(0,[z0,z8,z62,z1041,z5,z6]),(0,[z0,z171,z2,z4,z9,z6]),(0,[z0,z978,z2,z39,z5,z6])],[(0,[z0,z8,z2,z4,z5,z882]),(0,[z468,z8,z2,z4,z9,z6])],[(0,[z0,z1042,z2,z4,z5,z6]),(0,[z0,z276,z2,z4,z5,z132]),(0,[z0,z8,z2,z148,z4,z6]),(0,[z0,z8,z2,z4,z82,z215]),(0,[z0,z8,z2,z487,z5,z6]),(0,[z0,z8,z2,z448,z5,z6])],[(0,[z0,z8,z1043,z4,z5,z6]),(0,[z0,z8,z2,z1044,z5,z6]),(0,[z0,z8,z351,z39,z5,z6]),(0,[z0,z217,z8,z42,z9,z6]),(0,[z0,z8,z42,z5,z204,z6]),(0,[z0,z8,z4,z236,z9,z6])],[(0,[z0,z1,z2,z21,z5,z6]),(0,[z0,z8,z2,z4,z1045,z6]),(0,[z0,z8,z99,z21,z5,z6]),(0,[z0,z8,z10,z4,z9,z6])],[(0,[z628,z8,z2,z4,z5,z75]),(0,[z0,z8,z2,z4,z1046,z6]),(0,[z109,z8,z2,z4,z210,z6]),(0,[z0,z8,z186,z4,z100,z6]),(0,[z0,z8,z2,z1047,z5,z6])],[(1,[z1,z58,z4,z9,z6]),(0,[z0,z8,z2,z1048,z5,z6]),(0,[z0,z8,z2,z4,z262,z225]),(0,[z0,z8,z2,z522,z315,z6])],[(0,[z0,z8,z2,z1049,z5,z6]),(0,[z1050,z8,z2,z4,z5,z6]),(0,[z0,z8,z105,z382,z5,z6]),(0,[z0,z8,z2,z4,z18,z955])],[(0,[z1,z2,z4,z5,z166,z75]),(0,[z0,z8,z2,z1051,z4,z6]),(0,[z0,z8,z2,z4,z1052,z6]),(0,[z0,z8,z437,z4,z9,z6])],[(0,[z0,z8,z2,z4,z5,z1053]),(0,[z0,z22,z2,z4,z9,z6]),(0,[z660,z8,z2,z4,z5,z75]),(0,[z109,z8,z2,z4,z221,z6]),(0,[z0,z8,z42,z204,z9,z6]),(0,[z0,z8,z2,z416,z42,z6]),(0,[z0,z8,z2,z4,z1054,z6])],[(0,[z45,z1,z2,z4,z5,z92]),(0,[z20,z0,z26,z42,z5,z6]),(0,[z0,z26,z2,z382,z5,z6]),(0,[z0,z8,z4,z335,z9,z6]),(0,[z89,z8,z61,z4,z5,z6]),(0,[z0,z1055,z2,z4,z5,z6]),(0,[z0,z317,z2,z4,z9,z6]),(1,[z0,z8,z4,z766,z6]),(0,[z0,z8,z113,z4,z766,z6]),(0,[z0,z8,z2,z4,z1056,z6]),(0,[z0,z8,z2,z286,z5,z6])],[(0,[z45,z1,z2,z42,z5,z6]),(0,[z574,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z605,z6]),(0,[z0,z26,z39,z42,z5,z6]),(0,[z0,z8,z1057,z4,z5,z6]),(0,[z0,z1058,z2,z4,z5,z6]),(0,[z0,z8,z4,z305,z93,z6])],[(0,[z0,z1,z42,z5,z9,z6]),(0,[z178,z8,z2,z4,z5,z75]),(0,[z0,z1059,z2,z4,z5,z6])],[(0,[z0,z8,z2,z39,z5,z146]),(0,[z0,z8,z2,z4,z1060,z6]),(0,[z45,z171,z2,z4,z5,z92]),(0,[z0,z8,z2,z4,z6,z1061])],[(0,[z0,z8,z2,z38,z478,z6]),(0,[z0,z8,z603,z4,z9,z6]),(0,[z17,z317,z2,z4,z5,z75]),(0,[z0,z8,z2,z4,z1062,z6]),(0,[z0,z8,z1063,z4,z5,z6]),(0,[z0,z8,z2,z160,z5,z6]),(0,[z0,z8,z2,z1064,z5,z6]),(0,[z0,z15,z8,z2,z5,z741]),(0,[z0,z1065,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z75,z16]),(0,[z0,z26,z2,z4,z5,z132]),(0,[z28,z8,z2,z4,z727,z6]),(0,[z0,z8,z2,z4,z1066,z6]),(0,[z0,z999,z2,z39,z5,z6]),(0,[z0,z8,z43,z522,z5,z135])],[(0,[z0,z8,z2,z42,z5,z146]),(0,[z0,z8,z2,z4,z1067,z6]),(0,[z0,z253,z2,z4,z5,z65])],[(0,[z1,z2,z4,z5,z6,z612]),(0,[z0,z1,z2,z39,z18,z6]),(0,[z237,z26,z2,z4,z5,z6]),(0,[z8,z58,z4,z204,z9,z6]),(0,[z237,z8,z2,z199,z5,z6]),(0,[z0,z8,z2,z1068,z5,z6]),(0,[z0,z8,z2,z4,z733,z6])],[(0,[z0,z8,z1,z42,z9,z6]),(0,[z171,z2,z58,z4,z5,z6]),(0,[z0,z137,z2,z39,z5,z6]),(0,[z0,z8,z62,z4,z177,z6]),(0,[z237,z8,z2,z42,z5,z6]),(0,[z109,z8,z2,z4,z18,z6]),(0,[z0,z554,z8,z42,z9,z6])],[(0,[z0,z8,z595,z42,z5,z6])],[(0,[z8,z58,z4,z5,z75,z182]),(0,[z0,z8,z2,z1069,z5,z6]),(0,[z0,z8,z2,z1070,z5,z6]),(0,[z0,z8,z349,z4,z9,z6]),(0,[z0,z8,z1071,z4,z5,z6]),(0,[z0,z15,z8,z2,z5,z16])],[(0,[z0,z1,z2,z289,z5,z6]),(0,[z0,z1,z105,z4,z5,z6]),(0,[z0,z8,z2,z4,z227,z6]),(0,[z0,z137,z2,z42,z5,z6]),(0,[z0,z8,z2,z4,z1072,z6])],[(0,[z0,z179,z8,z2,z4,z6]),(0,[z0,z8,z2,z4,z1073,z6])],[(0,[z7,z0,z1,z2,z4,z14])],[(0,[z0,z117,z2,z4,z5,z6]),(0,[z0,z917,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z746,z6]),(0,[z0,z8,z2,z366,z108,z6]),(0,[z0,z8,z2,z40,z5,z6]),(0,[z0,z8,z2,z4,z1074,z6]),(0,[z0,z8,z2,z404,z93,z6])],[(0,[z0,z8,z2,z1075,z5,z6]),(0,[z0,z8,z2,z4,z5,z1076]),(0,[z84,z430,z61,z4,z5,z6]),(0,[z28,z8,z2,z35,z82,z6]),(1,[z0,z8,z344,z9,z6])],[(0,[z1,z58,z4,z5,z6,z182]),(0,[z0,z1,z2,z194,z5,z166]),(0,[z136,z8,z2,z97,z5,z132]),(0,[z0,z55,z2,z4,z1052,z6])],[(0,[z0,z1,z2,z81,z5,z6]),(0,[z1,z2,z39,z5,z6,z75]),(0,[z0,z1,z2,z299,z5,z6])],[(0,[z321,z1,z58,z4,z5,z6]),(0,[z0,z206,z2,z4,z107,z6]),(0,[z0,z137,z212,z4,z5,z6]),(0,[z0,z8,z2,z371,z5,z6]),(0,[z0,z1077,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z51,z6])],[(0,[z0,z1,z131,z4,z5,z6]),(0,[z104,z0,z2,z4,z5,z539]),(0,[z0,z1078,z2,z4,z5,z6]),(0,[z0,z8,z2,z124,z51,z6]),(0,[z0,z8,z2,z4,z1079,z6]),(0,[z0,z1080,z2,z4,z5,z6])],[(0,[z0,z29,z2,z4,z5,z6]),(0,[z45,z1,z2,z4,z18,z6]),(0,[z0,z1081,z2,z4,z5,z6]),(0,[z0,z8,z2,z1082,z5,z6]),(0,[z0,z8,z212,z265,z5,z6]),(0,[z216,z8,z2,z12,z5,z6]),(0,[z0,z273,z8,z412,z2,z6]),(0,[z0,z8,z2,z1083,z5,z6])]],
   [[(0,[z57,z1,z58,z4,z5,z6]),(0,[z689,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z1084,z5,z6]),(0,[z0,z8,z2,z4,z1085,z6]),(0,[z0,z1015,z2,z42,z5,z6])],[(0,[z0,z8,z2,z1086,z5,z6]),(0,[z0,z8,z223,z42,z5,z6]),(0,[z0,z8,z99,z39,z343,z6]),(0,[z0,z8,z2,z39,z6,z201]),(0,[z0,z8,z2,z1087,z5,z6])],[(0,[z0,z1,z2,z303,z5,z6]),(0,[z0,z1,z4,z305,z5,z6]),(0,[z558,z26,z2,z4,z5,z6]),(0,[z0,z1088,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z5,z209]),(0,[z0,z26,z2,z5,z6,z348]),(0,[z185,z26,z2,z4,z5,z6]),(0,[z0,z29,z2,z4,z5,z119]),(0,[z0,z8,z43,z4,z315,z135])],[(0,[z136,z1,z2,z97,z5,z6]),(0,[z0,z1,z2,z4,z5,z1089]),(0,[z0,z8,z2,z4,z18,z146]),(0,[z0,z247,z2,z39,z5,z6]),(0,[z0,z8,z2,z42,z6,z201]),(0,[z0,z138,z2,z4,z410,z6])],[(0,[z45,z1010,z2,z4,z5,z6]),(0,[z0,z8,z4,z5,z6,z771]),(0,[z0,z8,z2,z1090,z5,z6]),(0,[z0,z8,z2,z230,z177,z6]),(0,[z0,z196,z2,z37,z18,z6]),(0,[z0,z55,z2,z39,z13,z6]),(0,[z0,z8,z2,z4,z1091,z6])],[(0,[z0,z8,z61,z42,z469,z6]),(0,[z237,z8,z2,z4,z18,z6]),(0,[z0,z8,z1092,z4,z5,z6]),(0,[z0,z588,z2,z4,z13,z6]),(0,[z0,z8,z99,z39,z9,z6]),(0,[z0,z8,z412,z4,z305,z6])],[(0,[z136,z0,z8,z305,z5,z6]),(0,[z0,z247,z2,z42,z5,z6]),(0,[z0,z8,z2,z5,z6,z1093]),(0,[z0,z8,z149,z910,z5,z6]),(0,[z0,z1094,z2,z39,z5,z6])],[(0,[z0,z1,z2,z1095,z5,z6]),(0,[z1,z2,z630,z4,z5,z6]),(0,[z0,z8,z62,z4,z9,z6]),(0,[z0,z55,z2,z42,z13,z6]),(0,[z0,z8,z2,z5,z6,z741])],[(0,[z0,z8,z2,z4,z1096,z6]),(0,[z0,z1097,z2,z4,z5,z6]),(0,[z7,z0,z8,z2,z4,z784])],[(0,[z128,z0,z1,z42,z5,z6]),(0,[z0,z137,z232,z4,z5,z6]),(0,[z391,z8,z2,z302,z5,z6])],[(0,[z0,z1098,z2,z4,z5,z6]),(0,[z0,z1099,z2,z4,z5,z6]),(0,[z0,z8,z2,z1100,z5,z6]),(0,[z0,z1101,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z859,z6]),(0,[z0,z8,z42,z5,z6,z341]),(0,[z0,z8,z2,z249,z416,z6])],[(0,[z0,z1,z2,z4,z177,z6]),(0,[z0,z196,z2,z229,z5,z6]),(0,[z0,z8,z232,z97,z5,z6]),(0,[z0,z8,z1102,z4,z5,z6]),(0,[z17,z8,z62,z4,z5,z75])],[(0,[z1,z2,z4,z18,z6,z75]),(0,[z0,z8,z2,z4,z782,z6]),(0,[z0,z8,z2,z4,z1103,z6]),(0,[z0,z8,z174,z230,z5,z6]),(0,[z49,z0,z3,z4,z9,z6]),(0,[z0,z2,z4,z5,z6,z1104])],[(0,[z1105,z1,z2,z4,z5,z6]),(0,[z0,z137,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z91,z6]),(0,[z45,z8,z2,z4,z5,z735])],[(0,[z320,z1,z2,z4,z5,z6]),(0,[z550,z8,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z1106,z6])]],
   [[(0,[z1,z2,z4,z9,z6,z75]),(0,[z0,z8,z2,z265,z5,z6]),(0,[z136,z8,z2,z148,z97,z6]),(0,[z0,z8,z36,z42,z9,z6]),(0,[z0,z8,z2,z4,z9,z886])],[(0,[z1,z2,z4,z5,z637,z6]),(0,[z22,z2,z58,z4,z5,z6]),(0,[z649,z0,z3,z4,z5,z6]),(0,[z0,z8,z2,z39,z315,z6])],[(0,[z1,z2,z575,z4,z5,z6]),(0,[z104,z109,z2,z4,z5,z161])],[(0,[z0,z8,z2,z4,z5,z1107]),(0,[z84,z8,z595,z4,z5,z6]),(0,[z0,z8,z2,z1108,z5,z6]),(0,[z0,z8,z2,z382,z9,z6]),(0,[z0,z1109,z2,z4,z5,z6]),(0,[z0,z8,z1017,z2,z18,z6])],[(0,[z0,z1,z174,z4,z5,z6]),(0,[z0,z1,z4,z42,z9,z6]),(0,[z0,z8,z2,z12,z5,z209]),(0,[z0,z8,z2,z448,z210,z6]),(0,[z0,z8,z2,z4,z1110,z6]),(0,[z0,z8,z39,z42,z9,z6]),(0,[z468,z8,z2,z4,z410,z6])],[(0,[z26,z1,z2,z4,z5,z6]),(0,[z0,z1111,z1,z2,z5,z6]),(0,[z0,z309,z8,z42,z5,z6]),(0,[z8,z61,z822,z4,z5,z6])],[(0,[z28,z8,z2,z653,z4,z6]),(0,[z0,z8,z42,z9,z135,z6]),(0,[z0,z1112,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z100,z6]),(0,[z0,z8,z2,z366,z93,z6]),(0,[z0,z196,z2,z743,z5,z6]),(0,[z0,z8,z2,z1113,z5,z6]),(0,[z0,z8,z2,z1114,z5,z6])],[(0,[z332,z1,z2,z4,z5,z6]),(0,[z0,z8,z1115,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z132]),(0,[z0,z8,z2,z1116,z5,z6]),(0,[z0,z8,z951,z4,z5,z6]),(0,[z0,z8,z2,z448,z221,z6]),(0,[z0,z8,z2,z897,z9,z6])],[(0,[z0,z26,z2,z160,z5,z6]),(0,[z0,z8,z58,z39,z9,z6]),(0,[z0,z8,z2,z4,z1117,z6]),(0,[z0,z8,z2,z522,z5,z6])],[(0,[z0,z1,z2,z4,z147,z6]),(0,[z0,z1,z414,z4,z5,z6]),(0,[z0,z26,z113,z4,z9,z6]),(0,[z0,z8,z2,z1118,z4,z6]),(0,[z198,z8,z61,z4,z5,z6]),(0,[z0,z247,z2,z4,z18,z6]),(0,[z0,z8,z2,z1119,z5,z6]),(0,[z237,z8,z2,z4,z5,z195]),(0,[z0,z153,z149,z4,z5,z6]),(0,[z422,z1120,z2,z4,z5,z6])],[(0,[z288,z1,z2,z4,z5,z75]),(0,[z0,z8,z2,z1121,z5,z6]),(0,[z0,z8,z2,z4,z1122,z6]),(0,[z0,z2,z4,z1052,z13,z6]),(0,[z0,z8,z2,z1123,z5,z6])],[(0,[z0,z1,z2,z4,z343,z6]),(0,[z0,z8,z2,z4,z5,z735]),(0,[z0,z8,z2,z238,z243,z6]),(0,[z0,z8,z2,z4,z1124,z6])],[(0,[z0,z8,z2,z289,z227,z6]),(0,[z1125,z8,z2,z4,z5,z6]),(0,[z0,z8,z4,z163,z9,z6]),(0,[z0,z1126,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z108,z90])],[(0,[z159,z0,z1,z4,z5,z182]),(0,[z0,z8,z2,z103,z5,z6]),(0,[z0,z8,z822,z4,z5,z6]),(0,[z0,z8,z360,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z119]),(0,[z524,z8,z2,z4,z5,z92]),(0,[z109,z8,z105,z4,z5,z6]),(0,[z0,z149,z4,z5,z6,z161]),(0,[z0,z269,z8,z42,z9,z6])]],
   [[(0,[z1,z2,z651,z4,z5,z6]),(0,[z0,z26,z2,z4,z227,z6]),(0,[z0,z117,z2,z289,z5,z6]),(0,[z0,z8,z2,z1127,z5,z6]),(0,[z241,z2,z4,z5,z6,z161]),(0,[z0,z8,z399,z4,z9,z6])],[(0,[z0,z1,z2,z4,z9,z6]),(0,[z0,z707,z2,z4,z5,z6]),(0,[z0,z8,z2,z1128,z5,z6]),(0,[z0,z8,z2,z42,z227,z6]),(0,[z0,z8,z2,z487,z18,z6]),(0,[z1129,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z448,z18,z6]),(0,[z0,z8,z99,z4,z9,z6]),(0,[z0,z8,z2,z88,z93,z6])],[(0,[z109,z26,z2,z4,z5,z6]),(0,[z0,z1094,z2,z4,z5,z6]),(0,[z0,z8,z4,z305,z6,z14])],[(0,[z1010,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z249,z5,z6]),(0,[z0,z8,z1130,z2,z5,z6]),(0,[z0,z8,z2,z4,z1131,z6])],[(0,[z0,z26,z2,z4,z5,z1076]),(0,[z0,z8,z2,z305,z93,z6]),(0,[z0,z8,z2,z83,z911,z6])],[(0,[z17,z1,z2,z4,z5,z75]),(0,[z1,z2,z653,z4,z5,z6]),(0,[z84,z8,z61,z4,z469,z6]),(0,[z0,z490,z2,z4,z9,z6]),(0,[z0,z8,z2,z39,z51,z6]),(1,[z0,z8,z2,z911,z6])],[(0,[z408,z1,z58,z4,z5,z6]),(0,[z45,z8,z58,z4,z9,z6]),(0,[z0,z1132,z2,z4,z5,z6]),(0,[z0,z8,z2,z1133,z5,z6]),(0,[z0,z217,z2,z36,z5,z6])],[(0,[z0,z1105,z2,z4,z5,z6]),(0,[z636,z1,z2,z4,z5,z6]),(0,[z0,z8,z359,z4,z9,z6]),(0,[z0,z8,z2,z1134,z5,z6]),(0,[z0,z29,z2,z39,z5,z6]),(0,[z0,z196,z2,z63,z5,z6]),(0,[z0,z217,z2,z421,z5,z6])],[(0,[z84,z1,z2,z4,z9,z6]),(0,[z0,z1135,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z51,z6]),(0,[z0,z1136,z8,z2,z5,z6]),(0,[z0,z8,z2,z1137,z5,z6])],[(0,[z0,z8,z2,z4,z1138,z6]),(0,[z0,z26,z2,z4,z243,z6]),(0,[z0,z8,z2,z303,z227,z6]),(0,[z0,z1139,z2,z4,z5,z6]),(0,[z28,z0,z8,z4,z305,z6]),(0,[z0,z8,z4,z326,z9,z6]),(0,[z0,z8,z59,z4,z9,z6]),(0,[z241,z8,z2,z448,z5,z6]),(0,[z0,z8,z2,z4,z1140,z6]),(0,[z0,z8,z2,z286,z18,z6]),(0,[z159,z0,z8,z160,z5,z182])],[(0,[z295,z1,z2,z4,z5,z6]),(0,[z8,z61,z58,z4,z9,z6]),(0,[z0,z8,z148,z4,z913,z6]),(0,[z0,z29,z2,z42,z5,z6])],[(0,[z0,z8,z2,z4,z9,z209]),(0,[z0,z8,z2,z1141,z4,z6]),(0,[z0,z8,z2,z83,z366,z6]),(0,[z49,z0,z3,z4,z331,z6]),(0,[z0,z8,z2,z4,z1142,z6]),(0,[z0,z8,z2,z1143,z5,z6]),(0,[z0,z8,z42,z9,z386,z6]),(0,[z0,z8,z692,z4,z9,z6]),(0,[z0,z8,z1144,z4,z5,z6])],[(0,[z0,z117,z2,z303,z5,z6]),(0,[z0,z8,z2,z1145,z5,z6]),(0,[z0,z8,z2,z4,z1146,z6]),(0,[z0,z926,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z315,z6]),(0,[z468,z138,z2,z4,z5,z6]),(0,[z0,z8,z2,z1147,z5,z6])],[(0,[z1,z99,z58,z4,z5,z6]),(0,[z0,z1,z2,z366,z5,z6]),(0,[z0,z8,z2,z4,z5,z1148]),(0,[z0,z8,z232,z4,z1060,z6]),(0,[z0,z50,z32,z42,z5,z6]),(0,[z0,z8,z2,z584,z5,z6]),(0,[z0,z8,z2,z160,z18,z6])],[(0,[z84,z1105,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z989,z6]),(0,[z237,z8,z2,z4,z5,z225]),(0,[z0,z8,z749,z42,z5,z6]),(0,[z0,z8,z2,z4,z1149,z6])],[(0,[z0,z1,z2,z4,z1150,z6]),(0,[z0,z1,z2,z1151,z5,z6]),(0,[z0,z1,z2,z238,z5,z6]),(0,[z0,z8,z58,z4,z343,z6]),(0,[z0,z8,z2,z1152,z5,z6]),(0,[z0,z8,z2,z4,z177,z75]),(0,[z0,z8,z42,z5,z133,z6])]],
   [[(0,[z0,z1153,z2,z4,z5,z6]),(0,[z0,z8,z2,z289,z5,z146]),(0,[z0,z8,z4,z97,z913,z6]),(0,[z422,z8,z2,z4,z9,z6])],[(0,[z0,z22,z2,z4,z5,z445]),(0,[z178,z8,z2,z4,z82,z6]),(0,[z438,z0,z8,z42,z5,z6]),(0,[z1154,z8,z2,z4,z5,z6]),(0,[z0,z8,z619,z39,z5,z6])],[(0,[z0,z8,z2,z4,z5,z1155]),(0,[z0,z29,z2,z4,z5,z215]),(0,[z45,z490,z2,z4,z5,z92]),(0,[z0,z111,z8,z2,z532,z6]),(0,[z468,z8,z2,z4,z533,z6])],[(0,[z0,z26,z2,z4,z5,z146]),(0,[z0,z26,z2,z4,z1096,z6]),(0,[z0,z8,z482,z42,z5,z6]),(1,[z0,z149,z4,z5,z161]),(0,[z0,z8,z233,z4,z9,z6]),(0,[z0,z15,z8,z2,z18,z16]),(1,[z0,z8,z2,z5,z741]),(0,[z0,z8,z2,z4,z784,z14]),(0,[z0,z8,z1156,z4,z5,z6])],[(0,[z1,z2,z667,z4,z5,z6]),(0,[z0,z26,z2,z4,z998,z6]),(0,[z0,z8,z58,z4,z9,z6]),(0,[z202,z8,z2,z4,z5,z75]),(0,[z705,z8,z61,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z225]),(0,[z0,z1157,z2,z4,z5,z6]),(0,[z0,z8,z2,z487,z5,z195]),(0,[z0,z8,z570,z42,z5,z6]),(0,[z0,z1158,z2,z4,z5,z6]),(0,[z0,z8,z43,z4,z5,z135])],[(0,[z0,z8,z2,z39,z91,z6]),(0,[z0,z8,z2,z4,z1159,z6]),(0,[z0,z8,z2,z1160,z5,z6]),(0,[z0,z8,z4,z749,z5,z6])],[(0,[z0,z1,z61,z42,z5,z6]),(0,[z0,z26,z58,z42,z5,z6]),(0,[z0,z117,z2,z4,z18,z6]),(0,[z0,z8,z2,z1161,z5,z6]),(0,[z0,z8,z174,z4,z5,z75]),(0,[z0,z521,z2,z4,z9,z6]),(0,[z0,z8,z2,z40,z18,z6])],[(0,[z0,z8,z174,z967,z5,z6]),(0,[z0,z8,z2,z4,z108,z784])],[(0,[z0,z26,z2,z4,z1007,z6]),(0,[z0,z8,z2,z42,z91,z6]),(0,[z0,z8,z2,z4,z1162,z6]),(0,[z0,z276,z2,z4,z5,z209]),(0,[z0,z8,z2,z4,z1163,z6]),(0,[z693,z0,z8,z42,z5,z6])],[(0,[z0,z26,z2,z265,z5,z6]),(0,[z57,z8,z58,z4,z5,z146]),(0,[z0,z317,z2,z230,z5,z6]),(0,[z0,z8,z2,z5,z75,z348]),(0,[z0,z8,z2,z4,z1164,z6]),(0,[z104,z0,z2,z382,z5,z161]),(0,[z0,z8,z83,z4,z305,z6])],[(0,[z11,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z4,z316,z6]),(0,[z8,z58,z302,z42,z5,z6]),(0,[z0,z8,z42,z203,z9,z6]),(0,[z0,z8,z2,z816,z5,z6]),(0,[z0,z8,z2,z371,z18,z6]),(0,[z0,z8,z2,z4,z1165,z6]),(0,[z0,z8,z149,z382,z5,z6]),(0,[z0,z8,z2,z4,z1166,z6]),(0,[z0,z8,z4,z9,z6,z79])],[(0,[z0,z1167,z2,z4,z5,z6]),(0,[z0,z8,z2,z303,z5,z146]),(0,[z0,z8,z356,z42,z5,z6]),(0,[z0,z111,z8,z2,z911,z6])],[(0,[z26,z1,z2,z39,z5,z6]),(0,[z0,z8,z2,z1168,z5,z6]),(0,[z0,z8,z2,z4,z1169,z6]),(0,[z0,z29,z2,z4,z18,z6]),(0,[z0,z30,z2,z371,z5,z6]),(0,[z0,z8,z2,z4,z1170,z6]),(0,[z0,z54,z8,z42,z9,z6]),(0,[z0,z8,z113,z344,z9,z6])],[(0,[z0,z8,z2,z4,z1171,z6]),(0,[z1172,z8,z2,z4,z5,z6]),(0,[z538,z0,z8,z42,z9,z6]),(0,[z0,z1173,z2,z4,z5,z6])],[(0,[z0,z8,z463,z4,z9,z6]),(0,[z0,z1,z2,z4,z331,z6]),(0,[z0,z8,z2,z1174,z5,z6]),(0,[z136,z0,z8,z2,z148,z6]),(0,[z0,z8,z1175,z4,z5,z6]),(0,[z159,z0,z8,z42,z9,z6]),(0,[z0,z8,z4,z766,z5,z6])]],
   [[(0,[z26,z1,z2,z42,z5,z6]),(0,[z0,z1,z1176,z4,z5,z6]),(0,[z0,z1,z2,z4,z190,z6]),(1,[z0,z8,z42,z469,z6]),(0,[z0,z8,z2,z4,z1177,z6])],[(0,[z0,z8,z2,z4,z876,z6]),(0,[z20,z0,z26,z4,z18,z6]),(0,[z0,z8,z2,z4,z790,z6]),(0,[z0,z8,z42,z9,z324,z6]),(0,[z0,z8,z2,z38,z6,z110])],[(0,[z0,z8,z2,z1178,z5,z6]),(0,[z0,z29,z2,z234,z5,z6]),(0,[z0,z8,z2,z1179,z5,z6]),(0,[z0,z1180,z2,z4,z5,z6])],[(0,[z0,z8,z2,z39,z5,z6]),(0,[z0,z8,z1181,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z681]),(0,[z438,z0,z8,z4,z18,z6]),(0,[z0,z8,z42,z9,z9,z6])],[(0,[z0,z8,z2,z4,z1182,z6])],[(0,[z0,z8,z2,z4,z5,z1183]),(0,[z0,z8,z2,z1184,z5,z6]),(0,[z0,z26,z2,z4,z6,z201]),(0,[z8,z174,z4,z5,z6,z75]),(0,[z0,z8,z482,z4,z18,z6]),(0,[z468,z834,z2,z4,z5,z6])],[(0,[z0,z8,z1185,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z119]),(0,[z0,z8,z2,z4,z845,z6])],[],[(0,[z0,z1,z2,z39,z9,z6]),(0,[z0,z1,z149,z4,z5,z6]),(0,[z0,z8,z2,z4,z1186,z6]),(0,[z0,z8,z2,z4,z1187,z6]),(0,[z0,z8,z1188,z4,z5,z6]),(0,[z0,z8,z2,z371,z73,z6])],[(0,[z8,z1,z58,z4,z9,z6]),(0,[z682,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z119]),(0,[z0,z8,z39,z152,z5,z6]),(0,[z109,z8,z2,z4,z9,z6])],[(0,[z0,z1111,z8,z2,z5,z6]),(0,[z0,z26,z2,z1128,z5,z6]),(0,[z0,z117,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z5,z1189]),(0,[z0,z8,z2,z825,z5,z6]),(0,[z1190,z8,z2,z4,z5,z6]),(0,[z0,z8,z186,z38,z93,z6]),(0,[z0,z1191,z2,z4,z5,z6])],[(0,[z0,z1,z2,z42,z9,z6]),(0,[z0,z8,z2,z1192,z5,z6]),(0,[z0,z137,z2,z4,z18,z6]),(0,[z0,z8,z99,z42,z9,z6]),(0,[z0,z8,z2,z194,z5,z19])],[(0,[z0,z8,z2,z366,z6,z14]),(0,[z0,z8,z105,z448,z5,z6]),(0,[z0,z8,z2,z38,z470,z6])],[(0,[z0,z8,z2,z1193,z5,z6]),(0,[z0,z8,z2,z265,z18,z6])],[(0,[z0,z1194,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z6,z539]),(0,[z0,z26,z2,z148,z4,z6]),(0,[z0,z26,z2,z487,z5,z6]),(0,[z0,z26,z2,z448,z5,z6]),(0,[z0,z150,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z221,z6]),(0,[z0,z8,z404,z42,z9,z6])],[(0,[z25,z26,z2,z39,z5,z6]),(0,[z136,z8,z2,z97,z5,z209]),(0,[z0,z8,z680,z42,z5,z6]),(0,[z538,z0,z8,z2,z4,z162]),(0,[z0,z8,z2,z4,z18,z1107])],[(0,[z0,z8,z2,z38,z93,z6])],[(0,[z26,z1,z2,z4,z18,z6]),(0,[z0,z1,z2,z35,z5,z6]),(0,[z0,z1,z2,z4,z410,z6]),(0,[z0,z150,z2,z42,z5,z6]),(1,[z0,z3,z4,z5,z225]),(0,[z415,z0,z8,z42,z5,z6]),(0,[z0,z1195,z2,z4,z5,z6]),(0,[z0,z116,z8,z2,z83,z6])],[(0,[z0,z1,z2,z1196,z5,z6]),(0,[z1,z2,z699,z4,z5,z6]),(0,[z25,z26,z2,z42,z5,z6])],[(0,[z0,z8,z1197,z4,z5,z6]),(0,[z0,z8,z2,z4,z1198,z6]),(0,[z128,z0,z8,z18,z42,z6])],[(0,[z1,z2,z4,z5,z6,z702]),(0,[z84,z1,z61,z4,z5,z6]),(0,[z45,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z748,z5,z6]),(0,[z0,z8,z4,z42,z133,z6]),(0,[z0,z138,z2,z4,z5,z182]),(0,[z0,z1199,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z5,z1053]),(0,[z0,z26,z2,z584,z5,z6]),(0,[z0,z8,z62,z230,z5,z6]),(0,[z0,z8,z2,z4,z1200,z6]),(0,[z0,z8,z186,z4,z5,z6]),(0,[z0,z8,z2,z42,z315,z6])],[(0,[z695,z26,z2,z4,z5,z6]),(0,[z0,z26,z2,z286,z5,z6]),(0,[z17,z0,z8,z42,z9,z6]),(0,[z49,z0,z3,z4,z262,z6]),(0,[z0,z8,z2,z4,z1201,z6]),(0,[z0,z143,z8,z2,z5,z16])],[(0,[z1202,z0,z1,z4,z5,z6]),(0,[z0,z8,z2,z4,z1203,z6]),(0,[z0,z1204,z2,z4,z5,z6]),(0,[z1205,z8,z2,z4,z5,z6]),(0,[z0,z8,z625,z42,z5,z6]),(0,[z0,z8,z2,z1206,z5,z6])],[(0,[z1,z2,z703,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z1207])],[(0,[z112,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z9,z146]),(0,[z0,z8,z2,z265,z147,z6]),(0,[z0,z8,z32,z4,z5,z225]),(0,[z0,z8,z2,z18,z42,z6])],[(0,[z240,z0,z425,z4,z5,z6]),(0,[z136,z0,z8,z42,z9,z6]),(0,[z0,z8,z4,z18,z156,z6]),(0,[z0,z196,z2,z37,z9,z6])],[(0,[z0,z8,z2,z4,z18,z119]),(0,[z0,z8,z2,z1208,z5,z6]),(0,[z8,z2,z4,z5,z92,z735]),(0,[z237,z8,z2,z4,z9,z6])],[(0,[z0,z8,z2,z4,z5,z6]),(1,[z8,z2,z4,z5,z735]),(0,[z0,z8,z595,z4,z9,z6]),(0,[z0,z183,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z5,z1209])],[(0,[z26,z271,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z1210,z6]),(0,[z0,z8,z58,z42,z9,z6]),(0,[z0,z8,z2,z124,z5,z6]),(0,[z0,z8,z2,z18,z6,z734])]],
   [[(0,[z0,z137,z2,z4,z9,z6]),(0,[z0,z8,z2,z1211,z5,z6]),(0,[z0,z8,z2,z1212,z5,z6]),(0,[z400,z0,z8,z42,z9,z6]),(0,[z0,z8,z43,z42,z9,z6]),(0,[z0,z8,z43,z42,z5,z135])],[(0,[z28,z1,z2,z4,z82,z6]),(0,[z432,z1,z2,z4,z5,z6]),(0,[z0,z1213,z2,z4,z5,z6]),(0,[z372,z8,z58,z4,z9,z6]),(0,[z393,z0,z8,z2,z38,z6])],[(0,[z1,z2,z4,z5,z6,z34]),(0,[z0,z8,z2,z234,z5,z119]),(0,[z0,z8,z2,z1214,z5,z6]),(0,[z0,z8,z2,z4,z5,z1215]),(0,[z422,z8,z2,z4,z410,z6])],[(0,[z0,z8,z2,z4,z1216,z6]),(0,[z0,z8,z2,z4,z133,z6]),(0,[z0,z8,z39,z193,z5,z6]),(1,[z468,z8,z4,z5,z182])],[(0,[z0,z8,z2,z1217,z5,z6]),(0,[z0,z8,z2,z4,z960,z6]),(0,[z0,z217,z2,z36,z18,z6]),(0,[z0,z8,z2,z42,z1163,z6]),(0,[z0,z1218,z2,z4,z5,z6]),(0,[z0,z8,z2,z38,z176,z6])],[(0,[z0,z8,z232,z83,z5,z6]),(0,[z0,z8,z131,z4,z82,z6]),(0,[z0,z138,z2,z4,z533,z6])],[(0,[z0,z8,z2,z5,z6,z921]),(0,[z0,z26,z2,z40,z5,z6]),(0,[z0,z8,z2,z1219,z5,z6]),(0,[z0,z8,z2,z1220,z5,z6]),(0,[z468,z8,z2,z4,z5,z182])],[(0,[z25,z26,z2,z4,z18,z6]),(0,[z0,z1221,z2,z4,z5,z6]),(0,[z0,z827,z8,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z445]),(0,[z0,z111,z1,z2,z83,z6]),(0,[z0,z1222,z2,z4,z5,z6]),(0,[z128,z0,z8,z749,z5,z6])],[(0,[z84,z8,z822,z4,z5,z6]),(0,[z0,z8,z42,z267,z9,z6]),(0,[z0,z521,z2,z4,z410,z6])],[(0,[z0,z26,z2,z371,z5,z6]),(0,[z0,z26,z2,z4,z51,z6]),(0,[z0,z8,z2,z4,z5,z1223]),(0,[z57,z8,z58,z4,z227,z6]),(0,[z0,z8,z2,z148,z35,z6]),(0,[z0,z8,z2,z4,z5,z1224]),(0,[z1225,z8,z2,z4,z5,z6]),(0,[z0,z8,z305,z42,z5,z6]),(0,[z0,z1226,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z741])],[(0,[z0,z150,z2,z4,z5,z6]),(0,[z0,z8,z1227,z4,z5,z6]),(0,[z123,z1,z2,z4,z5,z75]),(0,[z0,z8,z1228,z4,z5,z6]),(0,[z0,z317,z62,z4,z5,z6]),(0,[z0,z8,z2,z1229,z5,z6]),(0,[z0,z8,z2,z4,z1230,z6]),(0,[z0,z8,z2,z584,z18,z6]),(0,[z0,z1021,z2,z4,z9,z6]),(0,[z0,z8,z2,z1231,z5,z6])],[(0,[z25,z26,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z262,z6]),(0,[z318,z1,z2,z4,z5,z6]),(0,[z0,z26,z2,z1082,z5,z6]),(0,[z0,z8,z2,z4,z1232,z6]),(0,[z0,z8,z625,z4,z18,z6])],[(0,[z57,z117,z58,z4,z5,z6]),(0,[z0,z8,z2,z4,z727,z6]),(0,[z0,z8,z2,z1233,z5,z6]),(0,[z334,z0,z8,z42,z5,z6])],[(0,[z0,z8,z2,z4,z5,z1234]),(0,[z1235,z8,z2,z4,z5,z6]),(0,[z1236,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z1237]),(0,[z0,z2,z743,z37,z5,z6]),(0,[z0,z8,z2,z749,z5,z6]),(0,[z0,z111,z8,z412,z2,z6]),(0,[z0,z8,z2,z39,z1238,z6])],[(0,[z0,z8,z140,z4,z9,z6]),(0,[z173,z8,z2,z12,z5,z6]),(0,[z0,z8,z2,z4,z1239,z6])]],
   [[(0,[z0,z8,z1240,z4,z5,z6]),(0,[z0,z1,z2,z230,z5,z6]),(0,[z0,z8,z2,z4,z1241,z6]),(0,[z0,z8,z2,z1242,z5,z6]),(0,[z0,z8,z212,z4,z1171,z6]),(0,[z0,z8,z2,z4,z5,z1243]),(0,[z0,z8,z412,z42,z9,z6])],[(0,[z0,z247,z2,z4,z9,z6]),(0,[z0,z29,z131,z4,z5,z6]),(0,[z7,z0,z8,z2,z4,z14])],[(0,[z0,z8,z2,z38,z5,z209]),(0,[z0,z1244,z2,z4,z5,z6]),(0,[z47,z8,z2,z4,z203,z6]),(0,[z0,z8,z32,z42,z9,z6]),(0,[z109,z8,z149,z4,z5,z6]),(0,[z0,z8,z421,z42,z9,z6]),(0,[z7,z0,z8,z42,z9,z6]),(0,[z0,z273,z8,z2,z83,z6]),(0,[z0,z8,z2,z4,z6,z1245]),(0,[z0,z8,z1246,z4,z5,z6])],[(0,[z0,z26,z2,z4,z1187,z6]),(0,[z0,z8,z43,z4,z18,z135])],[(0,[z0,z8,z2,z39,z210,z6]),(0,[z0,z1247,z2,z4,z5,z6])],[(0,[z0,z8,z212,z39,z5,z6]),(0,[z0,z8,z700,z4,z9,z6])],[(0,[z0,z8,z61,z4,z227,z6]),(0,[z0,z8,z2,z39,z5,z215]),(0,[z0,z8,z2,z9,z6,z774])],[(0,[z0,z8,z2,z35,z82,z6]),(0,[z0,z8,z2,z1248,z5,z6]),(0,[z0,z8,z2,z4,z1249,z6]),(0,[z0,z8,z2,z1250,z5,z6]),(0,[z0,z8,z670,z4,z9,z6])],[(0,[z0,z8,z1251,z4,z5,z6]),(0,[z0,z8,z2,z289,z91,z6]),(0,[z0,z8,z2,z487,z9,z6]),(0,[z0,z8,z2,z4,z1252,z6]),(0,[z0,z8,z2,z448,z9,z6]),(0,[z0,z8,z2,z39,z221,z6]),(0,[z0,z1253,z2,z4,z5,z6]),(0,[z0,z881,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z1254,z6]),(0,[z0,z8,z2,z147,z42,z6]),(0,[z0,z8,z2,z42,z5,z215]),(0,[z0,z554,z8,z2,z532,z6])],[(0,[z1,z2,z4,z5,z6,z95]),(0,[z0,z1255,z2,z4,z5,z6]),(0,[z293,z0,z8,z2,z38,z6]),(0,[z422,z138,z2,z4,z5,z6])],[(0,[z468,z1,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z91,z6]),(0,[z0,z8,z58,z4,z5,z445]),(0,[z8,z58,z42,z5,z6,z75]),(0,[z594,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z4,z478,z132]),(0,[z0,z8,z285,z42,z5,z6]),(0,[z237,z8,z2,z4,z331,z6]),(0,[z1256,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z42,z221,z6])],[(0,[z917,z1,z2,z4,z5,z6]),(0,[z607,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z1257,z5,z6]),(0,[z0,z1258,z2,z4,z5,z6]),(0,[z0,z8,z4,z103,z9,z6]),(0,[z11,z8,z2,z825,z5,z6]),(0,[z0,z154,z2,z37,z5,z6]),(0,[z0,z8,z2,z1259,z5,z6])],[(0,[z0,z8,z2,z371,z177,z6]),(0,[z0,z8,z2,z4,z75,z201])],[(1,[z917,z2,z4,z5,z6]),(0,[z0,z8,z704,z4,z9,z6]),(0,[z0,z55,z8,z42,z9,z6]),(0,[z1260,z8,z2,z4,z5,z6]),(0,[z0,z8,z1261,z4,z5,z6])],[(0,[z123,z0,z2,z4,z5,z161]),(0,[z0,z8,z186,z39,z5,z6]),(0,[z0,z1262,z2,z4,z5,z6])]],
   [[(0,[z466,z1,z2,z4,z5,z6]),(0,[z49,z112,z3,z4,z5,z6]),(0,[z0,z8,z531,z4,z9,z6]),(0,[z0,z269,z8,z2,z5,z16]),(0,[z538,z0,z8,z2,z4,z14]),(0,[z0,z8,z2,z286,z9,z6]),(0,[z422,z8,z2,z4,z533,z6])],[(0,[z0,z8,z329,z42,z5,z6]),(0,[z1263,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z18,z6]),(0,[z0,z8,z2,z4,z90,z784])],[(0,[z26,z917,z2,z4,z5,z6]),(0,[z57,z8,z58,z4,z91,z6]),(0,[z0,z8,z2,z1264,z5,z6]),(0,[z0,z8,z232,z39,z5,z6]),(0,[z0,z2,z951,z4,z5,z6]),(0,[z0,z8,z186,z42,z5,z6])],[(0,[z0,z30,z2,z39,z5,z6]),(0,[z112,z8,z2,z39,z5,z6]),(0,[z128,z0,z8,z42,z5,z6]),(1,[z0,z8,z4,z5,z759])],[(0,[z0,z1,z2,z4,z478,z6]),(0,[z483,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z303,z91,z6]),(0,[z0,z8,z2,z4,z473,z132]),(0,[z0,z8,z2,z160,z9,z6]),(0,[z0,z8,z2,z18,z522,z6])],[(0,[z0,z8,z2,z289,z5,z6]),(0,[z0,z8,z174,z371,z5,z6]),(0,[z112,z8,z2,z199,z5,z6])],[(0,[z0,z26,z2,z522,z5,z6]),(0,[z57,z0,z8,z42,z9,z6]),(0,[z136,z137,z2,z97,z5,z6]),(0,[z0,z30,z2,z42,z5,z6]),(0,[z112,z8,z2,z42,z5,z6]),(0,[z0,z8,z2,z39,z6,z1265]),(0,[z0,z8,z2,z1266,z5,z6]),(0,[z0,z8,z2,z4,z5,z722])],[(0,[z0,z1267,z2,z4,z5,z6]),(0,[z0,z8,z2,z1268,z5,z6]),(0,[z0,z8,z344,z5,z9,z6]),(0,[z0,z521,z2,z4,z533,z6]),(0,[z0,z1269,z2,z4,z5,z6])],[(0,[z553,z1,z2,z4,z5,z6]),(0,[z0,z206,z2,z4,z13,z6]),(0,[z136,z8,z2,z223,z5,z6]),(0,[z0,z8,z2,z199,z5,z6]),(0,[z128,z0,z8,z42,z133,z6]),(0,[z0,z8,z412,z4,z9,z6]),(0,[z0,z8,z2,z134,z5,z166])],[(0,[z0,z8,z2,z42,z5,z6]),(0,[z0,z1,z2,z4,z469,z6]),(0,[z0,z8,z2,z1270,z5,z6]),(0,[z0,z8,z99,z4,z469,z6]),(0,[z241,z8,z2,z39,z5,z6]),(0,[z0,z8,z2,z1271,z5,z6]),(0,[z0,z8,z2,z42,z5,z1209]),(0,[z20,z0,z8,z4,z100,z6]),(0,[z0,z8,z2,z4,z1238,z6]),(0,[z0,z8,z2,z404,z24,z6]),(0,[z0,z8,z2,z4,z1272,z6]),(0,[z0,z8,z43,z249,z5,z135])],[(0,[z192,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z973,z6]),(0,[z0,z8,z232,z208,z5,z6]),(0,[z0,z15,z8,z2,z9,z16]),(0,[z0,z8,z2,z1273,z5,z6]),(0,[z0,z8,z2,z4,z648,z142])],[(0,[z622,z1,z2,z4,z5,z6]),(0,[z11,z247,z2,z12,z5,z6]),(0,[z1274,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z133,z6]),(0,[z0,z8,z405,z42,z5,z6]),(0,[z0,z8,z2,z1275,z5,z6]),(0,[z0,z8,z38,z305,z93,z6]),(0,[z0,z8,z2,z38,z666,z6])],[(0,[z0,z26,z2,z103,z5,z6]),(0,[z0,z26,z2,z4,z5,z119]),(0,[z0,z8,z2,z4,z18,z215]),(0,[z0,z8,z2,z487,z5,z225]),(0,[z0,z8,z2,z4,z1276,z6]),(0,[z0,z8,z2,z100,z42,z6])],[(0,[z0,z1,z2,z4,z473,z6]),(0,[z1,z2,z139,z4,z5,z6]),(1,[z8,z2,z825,z5,z6]),(0,[z0,z8,z2,z1277,z5,z6]),(0,[z0,z8,z2,z1278,z5,z6]),(0,[z0,z8,z4,z18,z561,z6]),(0,[z261,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z5,z1279])],[(0,[z275,z1,z2,z4,z5,z6]),(0,[z0,z26,z99,z4,z9,z6]),(0,[z0,z8,z2,z4,z478,z209]),(0,[z8,z2,z4,z727,z82,z6]),(0,[z0,z8,z2,z42,z133,z6]),(0,[z0,z8,z2,z40,z9,z6]),(0,[z0,z1280,z2,z4,z5,z6]),(0,[z0,z1281,z2,z4,z5,z6])],[(0,[z106,z1,z2,z4,z5,z6]),(0,[z1202,z0,z8,z4,z5,z6]),(0,[z0,z8,z2,z4,z227,z445]),(0,[z0,z8,z2,z39,z73,z6]),(0,[z0,z8,z2,z4,z210,z6]),(0,[z468,z8,z43,z4,z5,z6])]],
   [[(0,[z0,z8,z212,z4,z5,z6]),(0,[z45,z30,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z1282,z6]),(0,[z0,z8,z2,z4,z5,z215]),(0,[z0,z8,z131,z4,z5,z119]),(0,[z0,z8,z4,z305,z5,z6]),(0,[z468,z521,z2,z4,z5,z6])],[(0,[z0,z117,z2,z4,z5,z445]),(0,[z0,z8,z2,z371,z9,z6]),(0,[z241,z8,z2,z4,z210,z6])],[(0,[z0,z8,z2,z4,z5,z1089]),(0,[z28,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z721,z6]),(0,[z0,z8,z2,z230,z5,z75]),(0,[z0,z8,z567,z42,z5,z6])],[(0,[z0,z8,z2,z4,z5,z1283]),(0,[z0,z29,z2,z4,z9,z6]),(0,[z8,z2,z4,z5,z735,z75]),(0,[z0,z8,z351,z4,z9,z6]),(0,[z0,z8,z105,z1233,z5,z6]),(0,[z0,z8,z18,z42,z9,z6])],[(0,[z0,z310,z2,z4,z5,z6]),(0,[z0,z8,z2,z1284,z5,z6]),(0,[z0,z8,z2,z447,z93,z6]),(0,[z0,z8,z666,z42,z5,z6]),(0,[z0,z8,z186,z4,z18,z6])],[(0,[z0,z26,z2,z4,z1138,z6]),(0,[z0,z8,z2,z4,z5,z1285]),(0,[z0,z111,z8,z2,z4,z215]),(0,[z17,z8,z2,z371,z5,z75]),(0,[z0,z8,z2,z487,z331,z6]),(0,[z241,z8,z2,z4,z221,z6]),(0,[z0,z8,z2,z1087,z9,z6]),(0,[z0,z1286,z2,z4,z5,z6])],[(0,[z84,z8,z61,z265,z5,z6]),(0,[z0,z50,z32,z4,z9,z6]),(0,[z1287,z8,z2,z4,z5,z6])],[(0,[z321,z0,z3,z4,z5,z6]),(0,[z0,z8,z2,z745,z5,z6]),(0,[z159,z0,z8,z4,z5,z182])],[(0,[z89,z1,z2,z4,z5,z6]),(0,[z0,z26,z2,z4,z315,z6]),(0,[z0,z8,z61,z522,z5,z6]),(0,[z112,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z1288,z5,z6])],[(0,[z353,z1,z2,z4,z5,z6]),(0,[z237,z430,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z1289,z6]),(0,[z0,z8,z42,z335,z9,z6]),(0,[z0,z8,z2,z911,z38,z6])],[(0,[z0,z8,z2,z4,z1290,z6])],[(0,[z0,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z134,z5,z228]),(0,[z422,z521,z2,z4,z5,z6])],[(0,[z0,z8,z232,z4,z5,z6]),(0,[z0,z8,z2,z4,z1291,z6]),(0,[z0,z8,z2,z1292,z5,z6])],[(0,[z0,z30,z2,z4,z5,z6]),(0,[z0,z8,z2,z1006,z5,z6]),(1,[z0,z26,z42,z9,z6]),(0,[z0,z8,z2,z4,z5,z1293]),(0,[z0,z8,z1294,z4,z5,z6]),(0,[z0,z8,z4,z568,z9,z6]),(0,[z0,z8,z619,z4,z9,z6])],[(0,[z0,z8,z2,z1295,z5,z6]),(0,[z104,z0,z2,z448,z5,z161]),(0,[z0,z8,z2,z236,z93,z6])]],
   [[(0,[z0,z8,z2,z1296,z5,z6]),(0,[z72,z0,z8,z4,z305,z6]),(0,[z0,z8,z2,z238,z51,z6]),(0,[z0,z8,z149,z448,z5,z6]),(0,[z0,z436,z8,z42,z9,z6]),(0,[z0,z8,z2,z1100,z9,z6]),(0,[z1297,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z194,z5,z489])],[(0,[z0,z1,z61,z4,z9,z6]),(0,[z0,z1,z62,z4,z5,z6]),(0,[z0,z26,z58,z4,z9,z6]),(0,[z0,z8,z2,z4,z1298,z6]),(0,[z0,z8,z2,z234,z5,z6]),(0,[z0,z179,z8,z2,z39,z6]),(0,[z0,z8,z2,z4,z6,z1299]),(0,[z0,z8,z2,z4,z6,z1265])],[(0,[z0,z1,z2,z4,z416,z6]),(0,[z0,z26,z43,z4,z5,z135]),(0,[z0,z8,z2,z4,z1300,z6]),(0,[z0,z1301,z2,z4,z5,z6]),(0,[z0,z1218,z2,z4,z18,z6])],[(0,[z0,z276,z2,z39,z5,z6]),(0,[z0,z1302,z2,z4,z5,z6])],[(0,[z241,z8,z2,z4,z5,z6]),(1,[z8,z822,z4,z5,z6]),(0,[z0,z1303,z8,z2,z4,z6]),(0,[z0,z8,z2,z4,z611,z90]),(0,[z0,z8,z105,z4,z1164,z6]),(0,[z0,z8,z194,z305,z5,z6])],[(0,[z0,z8,z2,z265,z9,z6]),(0,[z0,z8,z1304,z4,z5,z6]),(0,[z0,z8,z174,z1029,z5,z6]),(0,[z0,z1195,z2,z4,z9,z6]),(0,[z0,z8,z2,z911,z93,z6])],[(0,[z0,z8,z2,z4,z1305,z6]),(0,[z0,z8,z2,z4,z1306,z6]),(0,[z0,z8,z567,z4,z18,z6])],[(0,[z0,z30,z2,z4,z73,z6]),(0,[z1307,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z1308,z4,z6]),(0,[z0,z8,z2,z5,z6,z1309])],[(0,[z237,z8,z2,z4,z262,z6]),(0,[z0,z644,z8,z42,z5,z6]),(0,[z1310,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z1311,z6]),(0,[z0,z1312,z2,z4,z5,z6])],[(0,[z0,z150,z2,z4,z18,z6])],[(0,[z26,z1,z2,z4,z9,z6]),(0,[z0,z26,z2,z1168,z5,z6]),(0,[z0,z8,z2,z4,z73,z6]),(0,[z1313,z8,z2,z4,z5,z6])],[(0,[z430,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z1314,z6]),(0,[z112,z50,z2,z4,z5,z6]),(0,[z0,z8,z4,z1315,z5,z6]),(0,[z0,z8,z2,z344,z5,z6]),(0,[z0,z8,z2,z108,z90,z348])],[(0,[z20,z0,z1,z42,z5,z6]),(0,[z0,z1,z2,z382,z5,z6]),(0,[z0,z8,z61,z4,z315,z6]),(0,[z0,z8,z2,z4,z5,z1316])],[(0,[z0,z1,z39,z42,z5,z6]),(0,[z631,z8,z2,z12,z5,z6]),(0,[z112,z8,z2,z4,z5,z195]),(0,[z0,z8,z105,z39,z5,z6])],[(0,[z0,z2,z4,z1052,z5,z6]),(0,[z0,z8,z2,z522,z9,z6])],[(0,[z0,z643,z2,z229,z5,z6]),(0,[z104,z0,z2,z4,z5,z882]),(0,[z0,z1317,z2,z4,z5,z6])]],
   [[(0,[z0,z26,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z5,z195]),(0,[z0,z8,z149,z4,z5,z65]),(0,[z0,z8,z186,z21,z5,z6])],[(0,[z0,z1,z2,z4,z5,z132]),(0,[z0,z8,z2,z4,z725,z6]),(0,[z0,z8,z2,z993,z39,z6]),(0,[z0,z1318,z2,z4,z5,z6])],[(0,[z0,z8,z42,z561,z5,z6]),(0,[z1319,z8,z2,z4,z5,z6]),(0,[z0,z1126,z2,z4,z9,z6])],[(0,[z0,z8,z2,z1320,z5,z6]),(0,[z0,z8,z366,z715,z5,z6])],[(0,[z123,z0,z2,z4,z5,z528]),(0,[z0,z1,z2,z4,z533,z6]),(0,[z0,z26,z1185,z4,z5,z6]),(0,[z0,z8,z2,z103,z9,z6]),(0,[z0,z8,z2,z4,z9,z119])],[(0,[z0,z8,z2,z4,z5,z1321]),(0,[z0,z1322,z2,z4,z5,z6]),(0,[z0,z8,z131,z39,z5,z6]),(0,[z0,z8,z2,z1323,z5,z6]),(0,[z0,z8,z2,z243,z42,z6]),(0,[z0,z8,z2,z4,z5,z1324]),(0,[z540,z8,z2,z4,z163,z6])],[(0,[z0,z8,z4,z1325,z5,z6]),(0,[z0,z8,z105,z4,z210,z6]),(0,[z0,z8,z2,z4,z1326,z6]),(0,[z1327,z8,z2,z4,z5,z6]),(0,[z1328,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z160,z410,z6])],[(0,[z57,z8,z58,z39,z5,z6]),(0,[z0,z8,z2,z21,z5,z6])],[(0,[z0,z8,z2,z194,z5,z440]),(0,[z0,z1329,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z210,z6]),(0,[z325,z0,z2,z4,z5,z161])],[(0,[z0,z26,z212,z4,z5,z6]),(0,[z0,z8,z105,z4,z221,z6]),(0,[z0,z8,z2,z42,z210,z6])],[(0,[z0,z26,z2,z4,z5,z215]),(0,[z0,z26,z2,z1193,z5,z6]),(0,[z20,z0,z8,z103,z5,z6]),(0,[z0,z8,z212,z42,z5,z6]),(0,[z0,z217,z2,z36,z9,z6]),(0,[z0,z8,z680,z4,z9,z6])],[(0,[z0,z8,z2,z1330,z5,z6]),(0,[z0,z8,z42,z5,z324,z6]),(0,[z0,z8,z61,z40,z5,z6]),(0,[z0,z8,z2,z366,z5,z6]),(0,[z0,z1331,z2,z4,z5,z6]),(1,[z8,z174,z4,z5,z75]),(0,[z0,z50,z8,z42,z9,z6]),(0,[z0,z8,z2,z1332,z5,z6]),(0,[z0,z2,z42,z5,z6,z1104])],[(0,[z0,z179,z26,z2,z4,z6]),(0,[z0,z26,z2,z4,z221,z6]),(0,[z0,z22,z2,z4,z5,z146]),(1,[z8,z58,z4,z5,z445]),(0,[z0,z310,z2,z39,z5,z6]),(0,[z0,z150,z2,z4,z9,z6]),(0,[z45,z8,z2,z4,z5,z92]),(0,[z0,z8,z2,z4,z1333,z6])],[(0,[z0,z276,z2,z4,z5,z6]),(0,[z490,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z1151,z5,z6]),(0,[z25,z26,z2,z4,z9,z6]),(0,[z0,z8,z2,z238,z5,z6]),(0,[z0,z8,z2,z4,z395,z90]),(0,[z0,z8,z2,z4,z1334,z6]),(0,[z0,z1335,z2,z4,z5,z6])],[(0,[z669,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z4,z18,z6]),(0,[z0,z26,z2,z38,z93,z6]),(0,[z0,z8,z42,z5,z9,z6]),(0,[z0,z1336,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z4,z18,z9,z6]),(0,[z0,z310,z2,z42,z5,z6]),(0,[z0,z8,z2,z811,z5,z6]),(0,[z391,z0,z8,z42,z9,z6]),(0,[z0,z154,z2,z267,z5,z6]),(0,[z0,z8,z39,z18,z9,z6]),(0,[z159,z0,z8,z39,z5,z182]),(0,[z1337,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z286,z108,z90])],[],[(0,[z0,z217,z2,z297,z5,z6]),(0,[z0,z8,z2,z584,z9,z6]),(0,[z0,z138,z43,z4,z5,z6]),(0,[z0,z8,z2,z5,z663,z16])],[(0,[z0,z1,z2,z4,z5,z821]),(0,[z0,z8,z2,z289,z18,z6]),(0,[z0,z8,z2,z83,z577,z6]),(0,[z0,z8,z2,z487,z262,z6]),(0,[z159,z0,z8,z42,z5,z182]),(0,[z0,z8,z2,z249,z315,z6])],[(0,[z0,z1,z2,z5,z6,z348]),(0,[z0,z26,z186,z4,z5,z6]),(0,[z0,z1338,z8,z2,z4,z6]),(0,[z11,z8,z2,z515,z5,z6]),(0,[z0,z8,z2,z4,z696,z14])],[(0,[z0,z1339,z2,z4,z5,z6]),(0,[z0,z1340,z2,z4,z5,z6]),(0,[z0,z8,z2,z97,z478,z6]),(0,[z0,z2,z36,z743,z5,z6])],[(0,[z0,z29,z2,z35,z5,z6]),(0,[z0,z8,z2,z199,z18,z6])],[(0,[z0,z26,z232,z4,z5,z6]),(0,[z0,z8,z2,z5,z6,z1341]),(0,[z0,z8,z149,z4,z5,z161]),(0,[z0,z111,z8,z2,z284,z6])],[(0,[z198,z1,z2,z4,z5,z6]),(0,[z112,z26,z2,z4,z5,z6]),(0,[z0,z26,z2,z18,z42,z6]),(0,[z0,z8,z2,z1342,z5,z6]),(0,[z0,z8,z232,z42,z5,z6]),(0,[z0,z1004,z8,z2,z4,z6]),(0,[z0,z8,z105,z4,z5,z6]),(0,[z181,z0,z8,z4,z5,z182])],[(0,[z422,z1,z2,z4,z5,z6]),(0,[z0,z849,z2,z4,z5,z6]),(0,[z0,z111,z8,z131,z4,z6]),(0,[z0,z8,z2,z39,z1298,z6])],[(0,[z26,z507,z2,z4,z5,z6]),(0,[z45,z310,z2,z4,z5,z6]),(0,[z0,z379,z2,z4,z5,z119]),(0,[z0,z8,z43,z4,z9,z135])],[(0,[z0,z26,z2,z4,z5,z6]),(0,[z241,z8,z105,z4,z5,z6]),(0,[z0,z8,z2,z1343,z5,z6])],[(0,[z0,z26,z2,z124,z5,z6]),(0,[z0,z8,z2,z1041,z5,z6]),(0,[z0,z8,z2,z1344,z5,z6]),(0,[z49,z0,z951,z4,z5,z6]),(0,[z0,z8,z42,z395,z9,z6]),(0,[z0,z1280,z2,z4,z18,z6])],[(0,[z0,z8,z43,z4,z5,z661]),(0,[z0,z1345,z2,z4,z5,z6]),(0,[z1346,z0,z8,z4,z5,z6]),(0,[z0,z8,z2,z194,z5,z166])],[(0,[z1,z2,z4,z5,z6,z75]),(0,[z241,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z1347,z5,z6]),(0,[z0,z8,z212,z4,z18,z6]),(0,[z0,z8,z2,z81,z5,z6]),(0,[z11,z8,z2,z302,z5,z6]),(0,[z0,z8,z2,z4,z831,z6]),(0,[z0,z8,z42,z9,z6,z182]),(0,[z0,z269,z8,z2,z5,z431]),(0,[z0,z8,z2,z299,z5,z6]),(0,[z0,z138,z2,z160,z5,z6])],[(0,[z0,z1,z2,z4,z846,z6]),(0,[z321,z8,z58,z4,z5,z6]),(0,[z0,z8,z1176,z4,z5,z6]),(0,[z0,z387,z2,z297,z5,z6]),(0,[z0,z8,z877,z4,z5,z6]),(0,[z241,z8,z2,z42,z5,z6])]],
   [[(0,[z0,z26,z2,z4,z133,z6]),(0,[z0,z8,z2,z4,z1348,z6]),(0,[z0,z8,z131,z4,z5,z6]),(0,[z0,z8,z2,z148,z39,z6]),(0,[z0,z29,z414,z4,z5,z6]),(0,[z49,z237,z3,z4,z5,z6]),(0,[z104,z241,z2,z4,z5,z161])],[(0,[z25,z430,z2,z4,z5,z6]),(0,[z0,z26,z2,z1217,z5,z6]),(0,[z0,z8,z2,z39,z147,z6]),(0,[z0,z8,z2,z4,z1349,z6]),(0,[z1350,z8,z2,z4,z5,z6])],[(0,[z0,z8,z1351,z4,z5,z6]),(0,[z618,z26,z2,z4,z5,z6]),(0,[z57,z8,z58,z4,z5,z6])],[(0,[z0,z310,z2,z4,z18,z6]),(0,[z0,z8,z2,z39,z343,z6])],[(0,[z0,z26,z2,z4,z73,z6]),(0,[z0,z8,z2,z303,z5,z6]),(0,[z0,z8,z2,z234,z5,z215]),(0,[z8,z2,z4,z5,z6,z735]),(0,[z0,z8,z4,z766,z9,z6]),(0,[z0,z8,z2,z160,z533,z6])],[(0,[z0,z8,z2,z42,z73,z6]),(1,[z0,z2,z743,z5,z6]),(0,[z0,z8,z2,z18,z6,z348])],[(0,[z136,z8,z2,z97,z5,z6]),(0,[z0,z8,z1352,z4,z5,z6]),(0,[z159,z0,z8,z4,z18,z182])],[(0,[z0,z8,z556,z42,z5,z6]),(0,[z0,z8,z715,z5,z82,z6]),(0,[z1353,z8,z2,z4,z5,z6]),(0,[z0,z196,z8,z42,z9,z6]),(0,[z334,z0,z8,z4,z9,z6]),(0,[z0,z8,z2,z1354,z5,z6])],[(0,[z0,z8,z232,z12,z5,z6]),(0,[z0,z1355,z2,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z195]),(0,[z0,z8,z149,z4,z5,z6]),(0,[z0,z8,z2,z39,z9,z6])],[(0,[z0,z26,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z1356,z6]),(0,[z0,z8,z12,z42,z9,z6]),(0,[z0,z8,z60,z39,z5,z6])],[(0,[z0,z8,z2,z1095,z5,z6]),(0,[z0,z8,z1357,z4,z5,z6]),(0,[z0,z8,z2,z4,z473,z209]),(0,[z0,z8,z2,z199,z5,z195]),(0,[z0,z8,z42,z108,z9,z6])],[(0,[z0,z824,z1,z2,z4,z6]),(0,[z0,z1,z113,z4,z9,z6]),(0,[z0,z8,z232,z4,z18,z6]),(0,[z0,z8,z2,z4,z1358,z6]),(0,[z0,z8,z2,z809,z5,z6]),(0,[z0,z8,z2,z42,z5,z195]),(0,[z0,z8,z1359,z4,z5,z6]),(0,[z0,z1360,z2,z4,z5,z6]),(0,[z0,z8,z2,z1292,z18,z6]),(0,[z0,z1361,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z18,z6]),(0,[z17,z8,z2,z39,z5,z75]),(0,[z0,z320,z8,z42,z5,z6]),(0,[z1362,z8,z2,z4,z5,z6])],[(0,[z0,z8,z2,z18,z124,z6]),(0,[z0,z1120,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z965,z6]),(0,[z0,z1363,z2,z4,z5,z6]),(0,[z0,z8,z2,z1364,z5,z6]),(0,[z0,z8,z2,z4,z177,z6]),(0,[z0,z456,z2,z36,z5,z6]),(0,[z0,z8,z2,z4,z1365,z6]),(0,[z0,z8,z2,z4,z1366,z6]),(0,[z468,z8,z2,z160,z5,z6]),(1,[z0,z8,z305,z93,z6])],[(0,[z0,z8,z2,z4,z1367,z6]),(0,[z0,z583,z8,z2,z5,z16]),(0,[z0,z8,z2,z234,z18,z6]),(0,[z0,z8,z2,z4,z1368,z6]),(0,[z0,z8,z37,z42,z9,z6]),(0,[z0,z8,z2,z194,z5,z741]),(0,[z0,z8,z2,z1369,z5,z6])]],
   [[(0,[z0,z8,z1370,z4,z5,z6]),(0,[z0,z8,z2,z42,z5,z1324])],[(0,[z0,z1,z2,z4,z6,z970]),(0,[z0,z407,z2,z4,z5,z6]),(0,[z0,z26,z2,z21,z5,z6]),(0,[z0,z8,z2,z4,z1371,z6]),(0,[z0,z8,z4,z9,z6,z341]),(0,[z0,z111,z8,z2,z83,z6])],[(0,[z644,z1,z2,z4,z5,z6]),(0,[z0,z1,z99,z39,z5,z6]),(0,[z705,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z1372,z5,z6]),(0,[z1373,z8,z2,z4,z5,z6]),(0,[z241,z8,z2,z4,z18,z6]),(0,[z0,z8,z2,z38,z24,z6])],[(0,[z0,z8,z2,z4,z1374,z6]),(0,[z0,z8,z2,z1196,z5,z6]),(0,[z168,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z1375]),(0,[z0,z8,z2,z4,z9,z215]),(0,[z0,z153,z2,z4,z5,z76]),(0,[z0,z1329,z2,z42,z5,z6]),(0,[z0,z8,z2,z491,z5,z19])],[],[(0,[z0,z26,z1251,z4,z5,z6]),(0,[z0,z8,z285,z4,z9,z6]),(0,[z45,z8,z2,z39,z5,z92]),(0,[z0,z8,z149,z4,z1230,z6]),(0,[z0,z8,z2,z4,z1376,z6]),(0,[z0,z8,z42,z346,z9,z6])],[(0,[z0,z8,z2,z1377,z5,z6]),(0,[z0,z8,z174,z4,z5,z6]),(0,[z0,z8,z2,z35,z5,z119]),(0,[z0,z8,z2,z1378,z5,z6]),(0,[z0,z8,z4,z42,z9,z6])],[(0,[z0,z270,z2,z4,z5,z6]),(0,[z0,z518,z8,z2,z5,z16]),(0,[z0,z8,z83,z42,z9,z6]),(0,[z0,z15,z8,z2,z5,z118])],[(0,[z45,z8,z2,z42,z5,z92]),(0,[z112,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z1379,z5,z6])],[(0,[z0,z26,z2,z1257,z5,z6]),(0,[z0,z8,z4,z634,z9,z6]),(0,[z84,z8,z61,z103,z5,z6]),(0,[z0,z276,z2,z42,z5,z6]),(0,[z422,z8,z2,z160,z5,z6])],[(0,[z0,z1,z2,z4,z243,z6]),(0,[z0,z8,z2,z4,z91,z445]),(0,[z0,z111,z8,z2,z35,z6]),(0,[z0,z8,z2,z4,z1380,z6]),(0,[z0,z8,z2,z4,z1381,z6]),(0,[z0,z1336,z2,z42,z5,z6]),(0,[z0,z8,z2,z1382,z5,z6])],[(0,[z0,z8,z2,z1383,z5,z6]),(0,[z0,z1384,z2,z4,z5,z6])],[(0,[z0,z8,z2,z4,z5,z1385]),(0,[z41,z0,z8,z42,z9,z6]),(0,[z1,z2,z4,z5,z135,z75]),(0,[z0,z8,z2,z4,z147,z6]),(0,[z0,z8,z414,z4,z5,z6]),(0,[z0,z8,z2,z39,z5,z225]),(0,[z0,z8,z186,z4,z9,z6]),(0,[z0,z8,z2,z1386,z5,z6])],[(0,[z0,z8,z2,z4,z1387,z6]),(0,[z0,z1,z2,z985,z5,z6]),(0,[z0,z22,z2,z4,z227,z6]),(0,[z0,z8,z2,z4,z726,z6]),(0,[z0,z8,z2,z1388,z5,z6])],[(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z26,z2,z39,z18,z6]),(0,[z0,z8,z4,z638,z9,z6]),(0,[z0,z379,z2,z39,z5,z6]),(0,[z0,z8,z2,z4,z18,z195]),(0,[z0,z8,z1389,z4,z5,z6]),(0,[z0,z8,z2,z4,z343,z6])],[(0,[z0,z8,z1390,z4,z5,z6]),(0,[z0,z1391,z2,z4,z5,z6]),(0,[z0,z8,z1392,z4,z5,z6]),(0,[z0,z8,z305,z5,z93,z6])]],
   [[(0,[z0,z276,z212,z4,z5,z6]),(0,[z0,z8,z414,z4,z5,z119]),(0,[z0,z30,z2,z4,z9,z6]),(0,[z112,z8,z2,z4,z9,z6]),(0,[z0,z8,z2,z4,z1393,z6]),(0,[z0,z8,z2,z4,z108,z90])],[(0,[z579,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z1394,z5,z6]),(0,[z0,z8,z2,z1320,z18,z6])],[(0,[z0,z26,z2,z289,z5,z6]),(0,[z49,z0,z425,z4,z5,z6]),(0,[z0,z26,z105,z4,z5,z6]),(0,[z0,z8,z42,z9,z90,z6])],[(0,[z0,z8,z2,z4,z9,z6]),(0,[z0,z8,z875,z148,z4,z6]),(0,[z0,z8,z105,z42,z5,z6])],[(0,[z0,z1,z2,z4,z5,z146]),(0,[z25,z0,z8,z42,z9,z6]),(0,[z662,z26,z2,z4,z5,z6]),(0,[z0,z1395,z2,z4,z5,z6]),(0,[z17,z30,z2,z4,z5,z75]),(0,[z0,z8,z2,z124,z9,z6])],[(0,[z0,z1,z2,z997,z5,z6]),(0,[z0,z26,z2,z199,z5,z6]),(0,[z0,z317,z2,z371,z5,z6]),(0,[z1396,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z249,z5,z6]),(0,[z0,z8,z2,z21,z18,z6])],[(0,[z0,z26,z2,z42,z5,z6]),(0,[z237,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z1397,z5,z6]),(0,[z0,z8,z2,z1398,z5,z6])],[(0,[z1,z2,z4,z5,z75,z182]),(0,[z17,z8,z2,z4,z5,z75]),(0,[z20,z0,z8,z18,z42,z6])],[(0,[z0,z1,z58,z42,z5,z6]),(0,[z0,z26,z2,z299,z5,z6]),(0,[z0,z179,z8,z2,z42,z6]),(0,[z0,z8,z2,z4,z1399,z6])],[(0,[z57,z8,z58,z289,z5,z6]),(0,[z0,z8,z61,z147,z42,z6]),(0,[z0,z8,z2,z4,z913,z6]),(0,[z0,z379,z2,z4,z5,z215]),(0,[z0,z8,z194,z42,z9,z6]),(0,[z0,z8,z1400,z4,z5,z6])],[(0,[z0,z8,z2,z1401,z5,z6]),(0,[z8,z822,z58,z4,z5,z6]),(0,[z0,z8,z61,z1161,z5,z6]),(0,[z0,z8,z2,z366,z18,z6]),(0,[z0,z8,z2,z4,z1402,z6]),(0,[z0,z8,z4,z302,z9,z6])],[(0,[z0,z8,z131,z42,z5,z6]),(0,[z45,z8,z2,z4,z18,z92]),(0,[z0,z8,z2,z4,z5,z1403])],[(0,[z0,z276,z2,z4,z18,z6]),(0,[z0,z8,z2,z238,z18,z6]),(0,[z0,z8,z2,z4,z1404,z6]),(0,[z0,z8,z651,z4,z9,z6]),(0,[z0,z8,z2,z5,z741,z16])],[(0,[z57,z8,z58,z42,z5,z6]),(0,[z0,z276,z232,z4,z5,z6]),(0,[z0,z8,z2,z1405,z5,z6]),(0,[z49,z0,z3,z487,z5,z6]),(0,[z0,z8,z141,z39,z5,z6])],[(0,[z0,z1,z908,z4,z5,z6]),(0,[z0,z26,z2,z303,z5,z6]),(0,[z0,z26,z4,z305,z5,z6]),(0,[z0,z15,z26,z2,z5,z16]),(0,[z0,z8,z2,z4,z1406,z6]),(0,[z0,z8,z42,z9,z121,z6])],[(0,[z0,z8,z1161,z42,z5,z6]),(0,[z0,z8,z139,z42,z5,z6]),(0,[z427,z0,z8,z42,z5,z6]),(0,[z104,z0,z2,z39,z5,z161]),(0,[z0,z8,z305,z42,z9,z6])]],
   [[(0,[z0,z8,z2,z4,z5,z1407]),(0,[z0,z8,z2,z4,z1408,z6]),(0,[z0,z111,z8,z2,z127,z6]),(0,[z0,z8,z149,z39,z5,z6]),(0,[z0,z8,z99,z39,z100,z6])],[(0,[z0,z435,z2,z402,z5,z6]),(0,[z0,z8,z2,z4,z1150,z6]),(0,[z0,z8,z2,z1409,z4,z6]),(0,[z0,z3,z4,z5,z6,z225]),(0,[z0,z8,z2,z4,z1410,z6])],[(0,[z613,z26,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z1411]),(0,[z159,z0,z521,z4,z5,z182])],[(0,[z0,z8,z2,z4,z1412,z6]),(0,[z0,z8,z131,z4,z5,z215]),(0,[z0,z8,z2,z1413,z5,z6]),(0,[z0,z8,z149,z42,z5,z6]),(0,[z0,z1340,z2,z4,z18,z6]),(0,[z0,z1414,z2,z4,z5,z6])],[(0,[z0,z8,z61,z4,z790,z6]),(0,[z112,z8,z2,z4,z5,z225]),(0,[z0,z8,z2,z943,z5,z6])],[(0,[z0,z8,z2,z1415,z5,z6]),(0,[z0,z22,z2,z4,z91,z6]),(0,[z0,z8,z2,z97,z5,z209]),(0,[z0,z8,z42,z5,z6,z635])],[(0,[z0,z137,z2,z4,z478,z6]),(0,[z0,z8,z2,z39,z177,z6]),(0,[z0,z8,z2,z1416,z5,z6]),(0,[z0,z8,z105,z4,z18,z6]),(0,[z0,z8,z2,z38,z397,z6])],[(0,[z0,z8,z2,z1417,z5,z6]),(0,[z0,z1,z2,z4,z5,z209]),(0,[z0,z1,z2,z4,z6,z201]),(0,[z0,z8,z2,z4,z5,z225]),(0,[z0,z3,z4,z5,z161,z182]),(0,[z544,z0,z2,z4,z5,z161])],[(0,[z136,z8,z212,z97,z5,z6]),(0,[z0,z8,z2,z1418,z5,z6]),(0,[z0,z8,z4,z344,z9,z6]),(0,[z159,z0,z8,z299,z5,z182])],[(0,[z0,z26,z2,z4,z18,z6]),(0,[z0,z379,z2,z4,z5,z6]),(0,[z0,z8,z61,z42,z5,z6]),(0,[z0,z407,z2,z39,z5,z6]),(0,[z0,z8,z2,z42,z177,z6]),(0,[z0,z8,z2,z1419,z5,z6]),(0,[z0,z8,z149,z4,z210,z6])],[(0,[z0,z8,z2,z4,z6,z1420]),(0,[z72,z0,z8,z42,z9,z6]),(0,[z0,z8,z2,z4,z1421,z6]),(0,[z0,z8,z1422,z4,z5,z6]),(0,[z0,z8,z42,z9,z93,z6]),(0,[z0,z8,z2,z39,z410,z6])],[(0,[z917,z8,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z328]),(0,[z0,z8,z2,z4,z1423,z6]),(0,[z0,z8,z2,z4,z203,z215]),(0,[z0,z8,z2,z4,z1424,z6]),(0,[z564,z0,z8,z42,z5,z6]),(0,[z0,z8,z2,z194,z18,z166])],[(0,[z0,z8,z2,z81,z18,z6]),(0,[z0,z407,z2,z42,z5,z6]),(0,[z104,z0,z2,z4,z221,z161]),(0,[z0,z8,z2,z299,z18,z6]),(0,[z0,z8,z2,z1425,z5,z6])],[(0,[z84,z8,z61,z39,z5,z6]),(0,[z0,z8,z2,z265,z469,z6]),(0,[z11,z8,z2,z12,z5,z6]),(0,[z0,z8,z149,z4,z221,z6]),(0,[z0,z8,z2,z4,z316,z6]),(0,[z159,z468,z8,z4,z5,z182])],[(0,[z0,z26,z2,z234,z5,z6]),(0,[z0,z8,z2,z4,z1426,z6]),(0,[z0,z8,z2,z4,z1427,z6]),(0,[z0,z8,z131,z4,z18,z6]),(0,[z0,z8,z174,z39,z5,z6]),(0,[z112,z8,z2,z4,z331,z6])],[(0,[z0,z8,z703,z42,z5,z6]),(0,[z0,z8,z2,z1428,z5,z6]),(0,[z0,z1429,z2,z4,z5,z6]),(0,[z0,z137,z2,z4,z473,z6]),(0,[z0,z270,z2,z39,z5,z6]),(0,[z0,z8,z2,z1430,z5,z6]),(0,[z0,z8,z4,z666,z9,z6]),(0,[z1431,z8,z2,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 479).take 459) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 938).take 480) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1418).take 203) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1621)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [479, 459, 480, 203] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 65).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 136).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 209).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 284).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 349).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 429).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 508).take 4).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [65, 71, 73, 75, 65, 80, 79, 4] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_nil pcend))))))))

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

end PEqualNP.Outside.L_meta_38107

theorem PEqualNP.Outside.L_meta_38107 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276813512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276813512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38107.solve