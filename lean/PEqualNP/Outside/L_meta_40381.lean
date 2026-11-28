import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40381

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4276808352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x80014861000a0aa8#64 ++ 0x04000a4308005055#64 ++ 0x6027d8e3023e3ffe#64 ++ 0xfb013ec71811f1ff#64 : BitVec 256),
   (0x084b0b2c0cd8d990#64 ++ 0x884258596066c6cc#64 ++ 0xe8db2f3c1dd9d99d#64 ++ 0xf746d979e0eececc#64 : BitVec 256),
   (0x0314301661616141#64 ++ 0x5018a180b30b0b0a#64 ++ 0xdf1c303fe1e1e1fb#64 ++ 0xeef8e181ff0f0f0f#64 : BitVec 256),
   (0x05a03580b601b402#64 ++ 0x602d01ac05b00da0#64 ++ 0xf7e03fc0fe01fe17#64 ++ 0xdfbf01fe07f00ff0#64 : BitVec 256),
   (0x06fe8000dbb40003#64 ++ 0x8037f40006dda000#64 ++ 0xdfffc000fffe000f#64 ++ 0xbefffe0007fff000#64 : BitVec 256),
   (0x27fffefb0000001c#64 ++ 0x013ffff7d8000000#64 ++ 0xe7ffffff00000000#64 ++ 0x7f3ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0214001641604141 0x1010a000b20b020a 0x081c003f01e001e8 0x2040e001f80f000f

def z1 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c303fe1e1e1fb 0xeef8e181ff0f0f0f

def z2 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fc0fe01fe17 0xdfbf01fe07f00ff0

def z3 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc000fffe000f 0xbefffe0007fff000

def z4 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88d8271c1dc1c001 0x0446c138e0ee0e00

def z5 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z6 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6027d8e3023e3ffe 0xfb013ec71811f1ff

def z7 : W := mkw 0x0000000400404100 0x0000000020020208 0x0800000001c1c199 0x80400000000e0e0c

def z8 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1dd9d99d 0xf746d979e0eececc

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0x40041023002021fa 0xea0020811801010f

def z10 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0db2f3c00000000 0x7706d979e0000000

def z11 : W := mkw 0x0eff8b2cdffcd993 0x8877fc5966ffe6cc 0xffffef3cffffd99f 0xffffff79e7fffecc

def z12 : W := mkw 0x0001082000000000 0x0000084100000000 0x6003082000000000 0x7300184100000000

def z13 : W := mkw 0x07b43596f761f543 0x703da1acb7bb0faa 0xfffc3fffffe1ffff 0xffffe1ffffff0fff

def z14 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffffff1fffffff 0xff47fffff8ffffff

def z15 : W := mkw 0x004a000008900000 0x8002500000448000 0xc8db00001dd8000d 0xb646d80000eec000

def z16 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7ffe71c00000000 0x3e3fff38e0000000

def z17 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x97e037c0fe01e603 0x0cbf01be07f00f30

def z18 : W := mkw 0x004a000008900000 0x8002500000448000 0xc8ffc0001ffe000f 0xbe47fe0000fff000

def z19 : W := mkw 0x225fca7b49b4001d 0x8112fe53da4da000 0x081fc03f01fe0008 0x2040fe01f80ff000

def z20 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffffe000f 0xfffffffffffff000

def z21 : W := mkw 0x06fe8580dfb49403 0xa037f42c06fda4a0 0xffffcfc0fffe1e0f 0xbffffe7e07fff0f0

def z22 : W := mkw 0x004a000408d04100 0x8002500020468208 0xc8db203c1dd9c19d 0xf646d901e0eece0c

def z23 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8ffffff1dd9d99d 0xff47fffff8eececc

def z24 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f18201ce1c1c001 0x04f8c100e70e0e00

def z25 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001dd9d99d 0x8040000000eececc

def z26 : W := mkw 0x04a0000000000000 0x0025000000000000 0xc7e0000000000000 0x1e3f000000000000

def z27 : W := mkw 0x80014961b60bbeaa 0x64000a4b0db05df5 0x7027d8e3fe3fffff 0xfb813ec71ff1ffff

def z28 : W := mkw 0x0314301261212041 0x5018a18093090902 0xd71c303fe0202062 0x6eb8e181ff010103

def z29 : W := mkw 0x0000000461616141 0x50000000230b0b0a 0x58041023e1e1e1fb 0xeac020811f0f0f0f

def z30 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7dc373f00000000 0x6e3ee1b9f8000000

def z31 : W := mkw 0x07feb580ffb5b403 0xe03ff5ac07fdada0 0xffffffc0fffffe1f 0xfffffffe07fffff0

def z32 : W := mkw 0x85a17de1b60bbeaa 0x642d0bef0db05df5 0xf7e7ffe3fe3fffff 0xffbf3fff1ff1ffff

def z33 : W := mkw 0x27b5fefb0000001c 0x013daff7d8000000 0x2724ffff00000000 0x493927fff8000000

def z34 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fd80000fdc00001 0x04fec00007ee0000

def z35 : W := mkw 0x0001082000080880 0x0000084100004044 0x600308200018199c 0xf30018410000c0cc

def z36 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2023c8c0021e1e04 0x11011e460010f0f0

def z37 : W := mkw 0x025e8000dbb40003 0x8012f40006dda000 0x181fc000fffe000f 0xa0c0fe0007fff000

def z38 : W := mkw 0x27fffffbb601b41e 0x613fffffddb00da0 0xf7fffffffe01fe17 0xffbffffffff00ff0

def z39 : W := mkw 0x2100369a00000014 0x010801b4d0000000 0x0000271c00000000 0x00000138e0000000

def z40 : W := mkw 0x06fe8000d3240003 0x0037f40006992000 0xd7ffc000e2260002 0x3ebffe0007113000

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z42 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87d8271c00000000 0x043ec138e0000000

def z43 : W := mkw 0x010035802401b400 0x600801ac01200da0 0xe0c03fc01c01fe15 0xd70601fe00e00ff0

def z44 : W := mkw 0x010035962441f540 0x700801acb1220faa 0x20003fff0001fff0 0x410001fff8000fff

def z45 : W := mkw 0x0deb3facbed9fd92 0xe86f59fd65f6cfec 0xfffb3ffcffd9ff9f 0xffffd9ffe7fecffc

def z46 : W := mkw 0x05a03480b2012402 0x602d01a405900920 0x172010c0e2002602 0x08b9008607100130

def z47 : W := mkw 0x080001040448d980 0x08400008202246cc 0x000000000001d990 0x0000000000000ecc

def z48 : W := mkw 0x08010b2c0448d990 0x08400859602246cc 0x20002f3c0001d990 0x41000179e0000ecc

def z49 : W := mkw 0x2fffffff0cd8d99c 0x897ffffff866c6cc 0xefffffff1dd9d99d 0xff7ffffff8eececc

def z50 : W := mkw 0x0001486100000008 0x00000a4308000000 0x6027d8e300000000 0x7b013ec718000000

def z51 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0x88d8271c1dd9d99d 0x8446c138e0eececc

def z52 : W := mkw 0x20014ee90000001c 0x01000a7748000000 0x20000fc000000000 0x0100007e00000000

def z53 : W := mkw 0x080001040cd0d100 0x8840000820668688 0x080000001dc1c001 0x0040000000ee0e00

def z54 : W := mkw 0x0b5f3b3e6df9f9d1 0xd85af9d9f36fcfce 0xffdf3f3ffdf9f9ff 0xfffef9f9ffefcfcf

def z55 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff023e3ffe 0xff3ffffff811f1ff

def z56 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x20003fff00000000 0x410001fff8000000

def z57 : W := mkw 0x00000000dbb40003 0x8000000006dda000 0x18000000fffe000f 0x80c0000007fff000

def z58 : W := mkw 0x084b0a2c08d84990 0x884258516046c24c 0x081b003c01d80188 0x2040d801e00ec00c

def z59 : W := mkw 0x27b4f4d30000000c 0x013da7a698000000 0xe7e4ffc300000000 0x5f3f27fe18000000

def z60 : W := mkw 0x8000404100020228 0x0400020208001011 0x0024d0c302262662 0x0801268618113133

def z61 : W := mkw 0x07feb000fbb52003 0xc03ff58007dda900 0xdffff000ffffe01f 0xfeffff8007ffff00

def z62 : W := mkw 0x27fffeff6161615d 0x513ffff7fb0b0b0a 0xffffffffe1e1e1fb 0xffffffffff0f0f0f

def z63 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xe8d82f1c1dc1d815 0xd746c178e0ee0ec0

def z64 : W := mkw 0x06b48000dbb40003 0x8035a40006dda000 0x1f24c000fffe000f 0x88f9260007fff000

def z65 : W := mkw 0x0315787761616149 0x5018abc3bb0b0b0a 0xff3ff8ffe1e1e1fb 0xfff9ffc7ff0f0f0f

def z66 : W := mkw 0x04ea80009a940002 0x8027540004d4a000 0x00e3c0001e1e0004 0x10071e0000f0f000

def z67 : W := mkw 0x07feb016fbf56143 0xd03ff580b7dfab0a 0xdffff03fffffe1ff 0xfeffff81ffffff0f

def z68 : W := mkw 0x27fffffb0400901c 0x013fffffd8200480 0xe7ffffff1c01d815 0xff3ffffff8e00ec0

def z69 : W := mkw 0x0000000400404100 0x0000000020020208 0x8818201c01c1c001 0x0440c100e00e0e00

def z70 : W := mkw 0x82154877416a4be9 0x1410aa43ba0b525f 0x683fd8ff03fe3ffe 0xfb41fec7f81ff1ff

def z71 : W := mkw 0x83157877616b6be9 0x5418abc3bb0b5b5f 0xff3ff8ffe3ffffff 0xfff9ffc7ff1fffff

def z72 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e7ffc0fe3ffe1f 0xffbf3ffe07f1fff0

def z73 : W := mkw 0x0000010004009000 0x0000000800200480 0x20c00f001c001804 0x1106007800e000c0

def z74 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x17e7c000fe3e0006 0x18bf3e0007f1f000

def z75 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff002021fa 0xff3ffffff801010f

def z76 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff023e000e 0xff3ffffff811f000

def z77 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9ffbc000ffde0005 0x14ffde0007fef000

def z78 : W := mkw 0x00000100b601b402 0x6000000805b00da0 0x10000000fe01fe17 0x8080000007f00ff0

def z79 : W := mkw 0x05a17ce100000008 0x002d0be708000000 0xe7e7ffe300000000 0x7f3f3fff18000000

def z80 : W := mkw 0x27fffefffbf5615f 0xd13ffff7ffdfab0a 0xffffffffffffe1ff 0xffffffffffffff0f

def z81 : W := mkw 0x86ffc861dbbe0aab 0x8437fe430eddf055 0xffffd8e3fffe3fff 0xfffffec71ffff1ff

def z82 : W := mkw 0x20014a7b0000001c 0x01000a53d8000000 0x0000003f00000000 0x00000001f8000000

def z83 : W := mkw 0x0314301261212041 0x5018a18093090902 0x57041023e02021fa 0xeab820811f01010f

def z84 : W := mkw 0x025e800049b40001 0x8012f400024da000 0x081fc00001fe0008 0x2040fe00000ff000

def z85 : W := mkw 0x031431166561f141 0x5018a188b32b0f8a 0xffdc3f3ffde1f9ff 0xfffee1f9ffef0fcf

def z86 : W := mkw 0x07feb580ffb5b403 0xe03ff5ac07fdada0 0xdfffe700ffffc00f 0xbeffff3807fffe00

def z87 : W := mkw 0x084b0b280c989890 0x884258594064c4c4 0xe0c32f001c19d815 0xd706197800e0cec0

def z88 : W := mkw 0x80014865004a4ba8 0x04000a432802525d 0xe83ff8ff03ffffff 0xff41ffc7f81fffff

def z89 : W := mkw 0x27b4f4d3d324000f 0x013da7a69e992000 0x1724d0c3e2260002 0x08b926861f113000

def z90 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e43fe3fe21ffff 0xffbf21ff1ff10fff

def z91 : W := mkw 0x8314705361232269 0x5418a3829b091913 0x1724d0c3e2262662 0x08b926861f113133

def z92 : W := mkw 0x08000104bed9fd82 0xe840000825f6cfec 0x18000000ffd9ff9f 0x80c0000007fecffc

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x602018c002003e16 0xdb0100c6001001f0

def z94 : W := mkw 0x24ebcee99a94001e 0x81275e774cd4a000 0x20e3cfc01e1e0004 0x11071e7e00f0f000

def z95 : W := mkw 0x0214000041200001 0x0010a00002090000 0xdf1c0000e1e0000b 0xaef8e000070f0000

def z96 : W := mkw 0x27fffefb4120001d 0x013ffff7da090000 0xffffffffe1e0000b 0xffffffffff0f0000

def z97 : W := mkw 0x080001046df9f9c1 0xd8400008236fcfce 0x18000000fdf9f9ff 0x80c0000007efcfcf

def z98 : W := mkw 0x000001002401b400 0x6000000801200da0 0x000000000001fe10 0x0000000000000ff0

def z99 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x4027c000023e3ffe 0xba013e000011f1ff

def z100 : W := mkw 0x83157877616b6be9 0x5418abc3bb0b5b5f 0xdf1ff03fe1ffe1fb 0xeef8ff81ff0fff0f

def z101 : W := mkw 0x06b48000d3240003 0x0035a40006992000 0x1724c000e2260002 0x08b9260007113000

def z102 : W := mkw 0x06fe800000000000 0x0037f40000000000 0xc7ffc00000000000 0x3e3ffe0000000000

def z103 : W := mkw 0x27b4f4d76161614d 0x513da7a6bb0b0b0a 0xdf3cf0ffe1e1e1fb 0xeef9e787ff0f0f0f

def z104 : W := mkw 0x85a075c1b603b62a 0x642d03ae0db01db1 0xf7e4ffc3fe27fe77 0xdfbf27fe1ff13ff3

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c000001c000005 0x9606000000e00000

def z106 : W := mkw 0x0ceb8b289e9c9892 0x88675c5944f4e4c4 0x20e3cf001e1e1804 0x11071e7800f0f0c0

def z107 : W := mkw 0x03143016fbf56143 0xd018a180b7dfab0a 0xdf1c303fffffe1ff 0xeef8e181ffffff0f

def z108 : W := mkw 0x004b0a2c00404110 0x0002585160020208 0xe8db2f3c01c1c199 0xf746d979e00e0e0c

def z109 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x200018e300003ff0 0x410000c7180001ff

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x4027c000023e000e 0xba013e000011f000

def z111 : W := mkw 0x0000000461616141 0x50000000230b0b0a 0xd818203ce1e1e1fb 0xe6c0c101e70f0f0f

def z112 : W := mkw 0x86ffc861dbbe0aab 0x8437fe430eddf055 0xdfffc023fffe01ef 0xbefffe011ffff00f

def z113 : W := mkw 0x8314705761636369 0x5418a382bb0b1b1b 0xdf3cf0ffe3e7e7fb 0xeef9e787ff1f3f3f

def z114 : W := mkw 0x05a0348000000000 0x002d01a400000000 0x87c0270000000000 0x043e013800000000

def z115 : W := mkw 0x000001040440d100 0x0000000820220688 0xe8d82f3c1dc1d99d 0xf746c179e0ee0ecc

def z116 : W := mkw 0x06ff8820dbbc0883 0x8037fc4106dde044 0xffffc820fffe199f 0xfffffe4107fff0cc

def z117 : W := mkw 0x27b4b49200000004 0x013da5a490000000 0x0700000000000000 0x0038000000000000

def z118 : W := mkw 0x0000000008900000 0x8000000000448000 0x080000001dd8000d 0x8040000000eec000

def z119 : W := mkw 0xa7fffffbb60bbebe 0x653fffffddb05df5 0xf7fffffffe3fffff 0xffbffffffff1ffff

def z120 : W := mkw 0x0ceb0b2c9ed8d992 0x8867585964f6c6cc 0xfffb2f3cffd9d99f 0xffffd979e7fececc

def z121 : W := mkw 0x0214000461616141 0x5010a000230b0b0a 0xdf1c0000e1e1e1fb 0xaef8e000070f0f0f

def z122 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x6027ffff023e3ffe 0xfb013ffff811f1ff

def z123 : W := mkw 0x27b4f4d30000000c 0x013da7a698000000 0x0724d0c300000000 0x0839268618000000

def z124 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x00000000023e3ffe 0x800000000011f1ff

def z125 : W := mkw 0x0000000400404100 0x0000000020020208 0xc818203c01c1c199 0xe640c101e00e0e0c

def z126 : W := mkw 0x0100300020012000 0x4008018001000900 0xd7003000e001e013 0xceb8018007000f00

def z127 : W := mkw 0x2ffffeff08d8499c 0x897ffff7f846c24c 0xefffffff01d80188 0x7f7ffffff80ec00c

def z128 : W := mkw 0x25a17ffbb601b41e 0x612d0bffddb00da0 0xf7e03ffffe01fe17 0xdfbf01fffff00ff0

def z129 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f18303fe1c1e1f1 0x44f8c181ff0e0f0f

def z130 : W := mkw 0x884b4a6d08da4bb8 0x8c425a536846d25d 0x081fc03f01fe01e8 0x2040fe01f80ff00f

def z131 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x97c02700fc01c001 0x04be013807e00e00

def z132 : W := mkw 0x084b0b280c989890 0x884258594064c4c4 0x20c30f001c181804 0x1106187800e0c0c0

def z133 : W := mkw 0x0314301200000000 0x0018a18090000000 0xc71c303f002021fa 0xee38e181f801010f

def z134 : W := mkw 0x084a03080c909010 0x8842501840648480 0x00c007001c000000 0x0006003800e00000

def z135 : W := mkw 0x0000010004009000 0x0000000800200480 0xe0c02f001c01d815 0xd706017800e00ec0

def z136 : W := mkw 0x04a0058096009402 0x2025002c04b004a0 0x20e00fc01e001e04 0x1107007e00f000f0

def z137 : W := mkw 0x0000010004009000 0x0000000800200480 0x80c027001c01c001 0x0406013800e00e00

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x202008c002001e04 0x11010046001000f0

def z139 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8d82f3c1dc1d991 0x4546c179e0ee0ecc

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x6027d8c0023e3e1e 0xfb013ec60011f1f0

def z141 : W := mkw 0x0100301620416140 0x50080180b1020b0a 0x0000303f0001e1f0 0x40000181f8000f0f

def z142 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x4027c023023e01ee 0xba013e011811f00f

def z143 : W := mkw 0x80010820000a0aa0 0x0400084100005055 0x60030820023e3ffe 0xf30018410011f1ff

def z144 : W := mkw 0x004b4a6900000018 0x00025a5348000000 0xe0ffffff00000000 0x7f07fffff8000000

def z145 : W := mkw 0x00000100b601b402 0x6000000805b00da0 0x10000000fc01c001 0x0080000007e00e00

def z146 : W := mkw 0x27feb79ab601b416 0x613ff5bcd5b00da0 0xf7f83fdcfe01fe17 0xdfbfc1fee7f00ff0

def z147 : W := mkw 0x0100300020012000 0x4008018001000900 0x17001000e0002002 0x08b8008007000100

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004102300000000 0x6a00208118000000

def z149 : W := mkw 0x0214800041240001 0x0010a40002092000 0x0004c00000260000 0x0000260000013000

def z150 : W := mkw 0x85a074c1b203262a 0x642d03a60d901931 0x1724d0c3e2262662 0x08b926861f113133

def z151 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x0007c023003e01e8 0x20003e011801f00f

def z152 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff003e01e8 0x7f3ffffff801f00f

def z153 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0x20e3cfc000000000 0x11071e7e00000000

def z154 : W := mkw 0x04a0000092000002 0x0025000004900000 0xd7e00000fe000007 0x9ebf000007f00000

def z155 : W := mkw 0x0100301620416140 0x50080180b1020b0a 0xc818303f01c1e1f9 0xe640c181f80e0f0f

def z156 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x4007d023003e21fa 0xea003e811801f10f

def z157 : W := mkw 0x010035802401b400 0x600801ac01200da0 0x60203fc00201fe16 0xdb0101fe00100ff0

def z158 : W := mkw 0x27fef4d3dbb4000f 0x813ff7a69edda000 0xdfffd0c3fffe000f 0xbefffe861ffff000

def z159 : W := mkw 0x0100300020012000 0x4008018001000900 0x000030000001e010 0x4000018000000f00

def z160 : W := mkw 0x04ea00009a900002 0x8027500004d48000 0xdffb0000ffd8000f 0xbeffd80007fec000

def z161 : W := mkw 0x0eff8a2cdbfc4993 0x8877fc5166dfe24c 0xdfffc03cfffe018f 0xbefffe01e7fff00c

def z162 : W := mkw 0x2a5fcb7f0cd8d99c 0x8952fe5bf866c6cc 0xe8dfef3f1dd9d99d 0xf746ff79f8eececc

def z163 : W := mkw 0x00010a2800000010 0x0000085140000000 0x20002f3c00000000 0x41000179e0000000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x0023c000021e0004 0x10011e000010f000

def z165 : W := mkw 0x010035802401b400 0x600801ac01200da0 0x20003fc00001fe10 0x410001fe00000ff0

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000002000000198 0xe20000010000000c

def z167 : W := mkw 0xa25fca7b000a0abc 0x0512fe53d8005055 0x001fc03f003e01e8 0x2000fe01f801f00f

def z168 : W := mkw 0x004a000008900000 0x8002500000448000 0x88d800001dc00001 0x0446c00000ee0000

def z169 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8df3f3f1df9f9ff 0xff46f9f9f8efcfcf

def z170 : W := mkw 0x86fe8000dbbe0aa3 0x8437f40006ddf055 0xdfffc000fffe3fff 0xbefffe0007fff1ff

def z171 : W := mkw 0x05a03584b641f502 0x602d01ac25b20fa8 0xfff83ffcffc1ff9f 0xffffc1ffe7fe0ffc

def z172 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8db271c1dd9c00d 0xb646d938e0eece00

def z173 : W := mkw 0x0314301261212041 0x5018a18093090902 0x17041003e0202062 0x08b820801f010103

def z174 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x0027d0e3023e27ea 0x28013e871811f13f

def z175 : W := mkw 0x084b0a2808980890 0x884258514044c044 0x0003000000180000 0x000018000000c000

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000023e000e 0x800000000011f000

def z177 : W := mkw 0x0a5f0b3e4df8d9d1 0x9852f859f26fc6ce 0xe8df2f3f1df9d9fd 0xf746f979f8efcecf

def z178 : W := mkw 0x225e821a00000014 0x0112f410d0000000 0x0018001c00000000 0x0000c000e0000000

def z179 : W := mkw 0x0314301261212041 0x5018a18093090902 0xdf1c1003e1e0206b 0xaef8e0801f0f0103

def z180 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8ffef3c1fffd99f 0xff47ff79e0fffecc

def z181 : W := mkw 0x09013fac2449fd90 0x684809fd61224fec 0x20003ffc0001ff90 0x410001ffe0000ffc

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0c02f0000000000 0x5706017800000000

def z183 : W := mkw 0x2fffffffdffcd99f 0x897ffffffeffe6cc 0xffffffffffffd99f 0xfffffffffffffecc

def z184 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c201ce1e1c00b 0xaef8e100e70f0e00

def z185 : W := mkw 0x004b0a2800000010 0x0002585140000000 0x20c30f0000000000 0x1106187800000000

def z186 : W := mkw 0x0ceb8b2c9edcd992 0x88675c5964f6e6cc 0xe8fbef3c1fdfd99d 0xf747df79e0fefecc

def z187 : W := mkw 0x25ebffe9b601b41e 0x612f5fff4db00da0 0xf7e3ffc0fe01fe17 0xdfbf1ffe07f00ff0

def z188 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8db3fff1dd9fffd 0xf746d9fff8eecfff

def z189 : W := mkw 0x04ea80009a940002 0x8027540004d4a000 0xd7e3c000fe1e0007 0x9ebf1e0007f0f000

def z190 : W := mkw 0x0100300461616141 0x50080180230b0b0a 0xdf003000e1e1e1fb 0xcef80180070f0f0f

def z191 : W := mkw 0x27b5fcf30000000c 0x013dafe798000000 0x6727d8e300000000 0x7b393ec718000000

def z192 : W := mkw 0x004b0a2800080890 0x0002585140004044 0xe0db2f3c0018199c 0xf706d979e000c0cc

def z193 : W := mkw 0x06ff8a2800000010 0x0037fc5140000000 0xe7ffef3c00000000 0x7f3fff79e0000000

def z194 : W := mkw 0x06fe800049b40001 0x8037f400024da000 0xcfffc00001fe0008 0x3e7ffe00000ff000

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0xc018203c00000000 0x6600c101e0000000

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020000002000006 0x9a01000000100000

def z197 : W := mkw 0x07feb596fff5f543 0xf03ff5acb7ffafaa 0xffffffffffffffff 0xffffffffffffffff

def z198 : W := mkw 0x8000000000020220 0x0400000000001011 0x0000000002262662 0x0000000000113133

def z199 : W := mkw 0x0000000461616141 0x50000000230b0b0a 0x18000000e1e1e1fb 0x80c00000070f0f0f

def z200 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8fb3ffc1fd9ff9f 0xff47d9ffe0fecffc

def z201 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8dfef3f1dffd9fd 0xf746ff79f8effecf

def z202 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x602018c0023e3ffe 0xdb0100c60011f1ff

def z203 : W := mkw 0x0001486100080888 0x00000a4308004044 0x6027d8e30018199c 0xfb013ec71800c0cc

def z204 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff021e1e04 0x7f3ffffff810f0f0

def z205 : W := mkw 0x204bca690000001c 0x01025e5348000000 0x0003c00000000000 0x00001e0000000000

def z206 : W := mkw 0x86ffc861000a0aa8 0x0437fe4308005055 0xe7ffd8e3023e3ffe 0xff3ffec71811f1ff

def z207 : W := mkw 0x05a0348000000000 0x002d01a400000000 0xe7e03fc000000000 0x5f3f01fe00000000

def z208 : W := mkw 0x0b5f3b3e0cd8d990 0x885af9d9f066c6cc 0xefdf3f3f1dd9d99d 0xff7ef9f9f8eececc

def z209 : W := mkw 0x04a0058096009402 0x2025002c04b004a0 0x60e01fc01e003e16 0xdb0700fe00f001f0

def z210 : W := mkw 0x86b4c041d326022b 0x0435a6020e993011 0x1724d0c3e2262662 0x08b926861f113133

def z211 : W := mkw 0x0a5f0b2c4df8d991 0x8852f859626fc6cc 0xffdf2f3cfdf9d99f 0xfffef979e7efcecc

def z212 : W := mkw 0x294b7fff0cd8d99c 0x894a5bfff866c6cc 0xe8db3fff1dd9d99d 0xf746d9fff8eececc

def z213 : W := mkw 0xa7b5fcf3000a0aac 0x053dafe798005055 0x6727d8e3023e3ffe 0xfb393ec71811f1ff

def z214 : W := mkw 0x23157efb0000001c 0x0118abf7d8000000 0xe71c3fff00000000 0x6f38e1fff8000000

def z215 : W := mkw 0x05a03480b2012402 0x602d01a405900920 0xd72030c0e201e613 0xceb9018607100f30

def z216 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffd023fffe21ff 0xfefffe811ffff10f

def z217 : W := mkw 0x0000000000000000 0x0000000000000000 0x400300000018000c 0xb20018000000c000

def z218 : W := mkw 0x07b43492f3212443 0x703da1a497990922 0x172410c3e2202662 0x08b920861f110133

def z219 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fdfc000fdfe0009 0x24fefe0007eff000

def z220 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x88db273c1dd9c189 0x2446d939e0eece0c

def z221 : W := mkw 0x04a0000092000002 0x0025000004900000 0x00e000001e000004 0x1007000000f00000

def z222 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0xe0dfef3f00000000 0x7706ff79f8000000

def z223 : W := mkw 0x00000000dbb40003 0x8000000006dda000 0x18000000fdc00001 0x00c0000007ee0000

def z224 : W := mkw 0x004a020800000010 0x0002501040000000 0x80d8271c00000000 0x0406c138e0000000

def z225 : W := mkw 0x04ea80009a940002 0x8027540004d4a000 0x00c000001c000000 0x0006000000e00000

def z226 : W := mkw 0x0b5f3a3e69f969d1 0xd85af9d1f34fcb4e 0xdf1f303fe1f9e1fb 0xeef8f981ff0fcf0f

def z227 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf3ff03fe3ffe1ff 0xfef9ff81ff1fff0f

def z228 : W := mkw 0x05eb3fa8b601b412 0x602f59fd45b00da0 0xf7fb3ffcfe01fe17 0xffbfd9ffe7f00ff0

def z229 : W := mkw 0x07feb580ffb5b403 0xe03ff5ac07fdada0 0x9fd82700fdc1c001 0x04fec13807ee0e00

def z230 : W := mkw 0x00000000dbb40003 0x8000000006dda000 0x5827c000fffe000f 0xbac13e0007fff000

def z231 : W := mkw 0x035eb01669f56141 0xd01af580b34fab0a 0xdf1ff03fe1ffe1fb 0xeef8ff81ff0fff0f

def z232 : W := mkw 0x0001082000080880 0x0000084100004044 0x2000082000001990 0x41000041000000cc

def z233 : W := mkw 0xa4ebcee9000a0abc 0x05275e7748005055 0x60e7dfe3023e3ffe 0xfb073eff1811f1ff

def z234 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff02003e16 0xff3ffffff81001f0

def z235 : W := mkw 0xafffffff0cdadbbc 0x8d7ffffff866d6dd 0xefffffff1fffffff 0xff7ffffff8ffffff

def z236 : W := mkw 0x0001082000080880 0x0000084100004044 0x6027c820023e199e 0xfb013e410011f0cc

def z237 : W := mkw 0x07b43596f761f543 0x703da1acb7bb0faa 0xfff83fdcffc1fe17 0xdfffc1fee7fe0ff0

def z238 : W := mkw 0x2a5fca7f08d8499c 0x8952fe53f846c24c 0x081fc03f01d80188 0x2040fe01f80ec00c

def z239 : W := mkw 0x004a0000dbb40003 0x8002500006dda000 0xd8db0000fffe000f 0xb6c6d80007fff000

def z240 : W := mkw 0x04a0048000000000 0x0025002400000000 0x20e00fc000000000 0x1107007e00000000

def z241 : W := mkw 0x0000000000000000 0x0000000000000000 0x200018c000003e10 0x410000c6000001f0

def z242 : W := mkw 0x84a14de1960a9eaa 0x24250a6f0cb054f5 0x20e3cfc01e1e1e04 0x11071e7e00f0f0f0

def z243 : W := mkw 0x0eff8b2cdffcd993 0x8877fc5966ffe6cc 0xffdb2f3cfdd9d99d 0xf7fed979e7eececc

def z244 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0xe7db2f3c00000000 0x773ed979e0000000

def z245 : W := mkw 0x85a17ce1000a0aa8 0x042d0be708005055 0xe7e7ffe3023e3ffe 0xff3f3fff1811f1ff

def z246 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6027d8e3003e01e8 0x7b013ec71801f00f

def z247 : W := mkw 0x27fffefb9200001e 0x013ffff7dc900000 0xf7fffffffe000007 0xffbffffffff00000

def z248 : W := mkw 0x80014861dbbe0aab 0x84000a430eddf055 0x7827d8e3fffe3fff 0xfbc13ec71ffff1ff

def z249 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7d83fff00000000 0x453ec1fff8000000

def z250 : W := mkw 0x084a020c08d04110 0x8842501060468208 0x0818001c01c00000 0x0040c000e00e0000

def z251 : W := mkw 0x0214000000000000 0x0010a00000000000 0xc71c000000000000 0x2e38e00000000000

def z252 : W := mkw 0x07b4b580f725b403 0x603da5ac07b92da0 0xf7e4ffc0fe27fe17 0xdfbf27fe07f13ff0

def z253 : W := mkw 0x0800000408d84980 0x884000002046c24c 0x0800000001d80188 0x00400000000ec00c

def z254 : W := mkw 0x00000104f761f543 0x7000000827bb0faa 0x18000000ffe1ffff 0x80c0000007ff0fff

def z255 : W := mkw 0x27feb79ab601b416 0x613ff5bcd5b00da0 0x97d8271cfc01c001 0x04bec138e7e00e00

def z256 : W := mkw 0x04a00000dbb40003 0x8025000006dda000 0xdfe00000fffe000f 0x9eff000007fff000

def z257 : W := mkw 0x0dea378cbed1f512 0xe86f51bc65f68fa8 0xfff83fdcffc1fe17 0xdfffc1fee7fe0ff0

def z258 : W := mkw 0x0100300000000000 0x0008018000000000 0xc700300000000000 0x4e38018000000000

def z259 : W := mkw 0x0ceb0fa89e989c92 0xa867587d44f4c4e4 0x20e30fc01e181e04 0x1107187e00f0c0f0

def z260 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0x001fc03f00000000 0x2000fe01f8000000

def z261 : W := mkw 0x2fffffff0448d99c 0x097ffffff82246cc 0xe7ffffff0001d990 0x7f3ffffff8000ecc

def z262 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7c03fc0fc01fe11 0x45be01fe07e00ff0

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x602418e302203ffe 0xfb0120c7181101ff

def z264 : W := mkw 0x0214000041200001 0x0010a00002090000 0x081c000001e00008 0x2040e000000f0000

def z265 : W := mkw 0x27fffefb6121205d 0x513ffff7db090902 0xf7ffffffe0202062 0x7fbfffffff010103

def z266 : W := mkw 0x084b0b280c989890 0x884258594064c4c4 0xe0db2f3c1c181804 0x7706d979e0e0c0c0

def z267 : W := mkw 0x0001486100000008 0x00000a4308000000 0x2023c8c000000000 0x11011e4600000000

def z268 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f1c203fe1e1c1e9 0x24f8e101ff0f0e0f

def z269 : W := mkw 0x05a03480b2012402 0x602d01a405900920 0xd7e010c0fe002607 0x9ebf008607f00130

def z270 : W := mkw 0xa4ebcee9000a0abc 0x05275e7748005055 0x20e3cfc0021e1e04 0x11071e7e0010f0f0

def z271 : W := mkw 0x004a000008900000 0x8002500000448000 0x081b000001d80008 0x2040d800000ec000

def z272 : W := mkw 0x03153836616969c1 0x5018a9c1b30b4b4e 0xff1f383fe1f9f9ff 0xfff8f9c1ff0fcfcf

def z273 : W := mkw 0x035f3a3a00000010 0x001af9d1d0000000 0xe7df3f3f00000000 0x7f3ef9f9f8000000

def z274 : W := mkw 0x0a5f8b2c4dfcd991 0x8852fc59626fe6cc 0xe8dfef3c1dffd99d 0xf746ff79e0effecc

def z275 : W := mkw 0x004a000000000000 0x0002500000000000 0xc0db000000000000 0x3606d80000000000

def z276 : W := mkw 0x0315787300000008 0x0018abc398000000 0xe73ff8ff00000000 0x7f39ffc7f8000000

def z277 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8db2f3c1fffffff 0xf746d979e0ffffff

def z278 : W := mkw 0x25ebfefb0000001c 0x012f5ff7d8000000 0x20e3ffff00000000 0x51071ffff8000000

def z279 : W := mkw 0x0314301200000000 0x0018a18090000000 0xc71c303f00000000 0x6e38e181f8000000

def z280 : W := mkw 0x0001082000080880 0x0000084100004044 0x2003080000181804 0x110018400000c0c0

def z281 : W := mkw 0x27fffffbb601b41e 0x613fffffddb00da0 0xf7fffffffc01c001 0x7fbfffffffe00e00

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x4027d023023e21fe 0xfa013e811811f10f

def z283 : W := mkw 0x010031002401b000 0x4008018801200d80 0xf7c03f00fc01f817 0xdfbe01f807e00fc0

def z284 : W := mkw 0x80000100b60bbea2 0x6400000805b05df5 0x10000000fe3fffff 0x8080000007f1ffff

def z285 : W := mkw 0x07feb580b601b402 0x603ff5ac05b00da0 0xf7ffffc0fe01fe17 0xffbffffe07f00ff0

def z286 : W := mkw 0x00000004fbf56143 0xd000000027dfab0a 0x18000000ffffe1ff 0x80c0000007ffff0f

def z287 : W := mkw 0x0b5e331e6df1f151 0xd85af198f36f8f8a 0x9fd8271cfdc1c001 0x04fec138e7ee0e00

def z288 : W := mkw 0x83157877616b6be9 0x5418abc3bb0b5b5f 0xff1c38ffe1e1fffb 0xeff8e1c7ff0f0fff

def z289 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdff80000ffc00007 0x9effc00007fe0000

def z290 : W := mkw 0x084b0b280c989890 0x884258594064c4c4 0x60c30f201c18199c 0xf306187900e0c0cc

def z291 : W := mkw 0x235ffefb0000001c 0x011afff7d8000000 0x201fffff00000000 0x6100fffff8000000

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000100000002012 0xca00008000000100

def z293 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0xe8c02f001dd9d99d 0xd746017800eececc

def z294 : W := mkw 0x06ff8a28dbb40013 0x8037fc5146dda000 0xffffef3cfffe000f 0xffffff79e7fff000

def z295 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff02262662 0x7f3ffffff8113133

def z296 : W := mkw 0xa7fffefbdbbe0abf 0x853ffff7deddf055 0xfffffffffffe3fff 0xfffffffffffff1ff

def z297 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xff3c38ffe3e1ffff 0xfff9e1c7ff1f0fff

def z298 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xe7f83fdc00000000 0x5f3fc1fee0000000

def z299 : W := mkw 0x05a0348092000002 0x002d01a404900000 0xf7e03fc0fe000007 0xdfbf01fe07f00000

def z300 : W := mkw 0x0001082000080880 0x0000084100004044 0x602318e002183f9e 0xfb0118c70010c1fc

def z301 : W := mkw 0x004b0a2800000010 0x0002585140000000 0x001b003c00000000 0x2000d801e0000000

def z302 : W := mkw 0x27fffffbffb5b41f 0xe13fffffdffdada0 0xfffffffffffffe1f 0xfffffffffffffff0

def z303 : W := mkw 0x06fe800008900000 0x8037f40000448000 0xcfffc0001dd8000d 0xbe7ffe0000eec000

def z304 : W := mkw 0x0100301620416140 0x50080180b1020b0a 0xd700303fe001e1f3 0xceb80181ff000f0f

def z305 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fd80000fffe000f 0x84fec00007fff000

def z306 : W := mkw 0x0214001661616141 0x5010a000b30b0b0a 0x181c003fe1e1e1fb 0xa0c0e001ff0f0f0f

def z307 : W := mkw 0x084b0a2c08d84990 0x884258516046c24c 0xe8db2f3c01d80188 0x7746d979e00ec00c

def z308 : W := mkw 0x04a0000092000002 0x0025000004900000 0xd7e7c000fe3e000f 0xbebf3e0007f1f000

def z309 : W := mkw 0x06b48000d3240003 0x0035a40006992000 0x5727c000e23e000e 0xbab93e000711f000

def z310 : W := mkw 0x080001000c989880 0x884000080064c4c4 0x000000001c181804 0x0000000000e0c0c0

def z311 : W := mkw 0x2fffffff0cd0d11c 0x897ffffff8668688 0xefffffff1dc1c001 0x7f7ffffff8ee0e00

def z312 : W := mkw 0x07b4b480f3252403 0x603da5a407992920 0x1724d0c0e2262602 0x08b9268607113130

def z313 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x0007c023023e3ffe 0xa0003e011811f1ff

def z314 : W := mkw 0x05a03480b2012402 0x602d01a405900920 0xf7e03fc0e2002602 0x5fbf01fe07100130

def z315 : W := mkw 0x25a17efb0000001c 0x012d0bf7d8000000 0xe7e03fff00000000 0x5f3f01fff8000000

def z316 : W := mkw 0x825fc86149be0aa9 0x8412fe430a4df055 0x081fc02301fe01e8 0x2040fe01180ff00f

def z317 : W := mkw 0x29017fff0448d99c 0x09480bfff82246cc 0x20003fff0001d990 0x410001fff8000ecc

def z318 : W := mkw 0x084b0b280c989890 0x884258594064c4c4 0xe8db0f001dd8180d 0xb746d87800eec0c0

def z319 : W := mkw 0x0000000400404100 0x0000000020020208 0xc81c303f01e1e1fb 0xee40e181f80f0f0f

def z320 : W := mkw 0x0100300020012000 0x4008018001000900 0xf72038c0e201fe17 0xdfb901c607100ff0

def z321 : W := mkw 0x27b4f4d30000000c 0x013da7a698000000 0xc73cf0ff00000000 0x6e39e787f8000000

def z322 : W := mkw 0x0ceb0fac9ed8dd92 0xa867587d64f6c6ec 0xe8fb2ffc1fd9df9d 0xf747d97fe0fecefc

def z323 : W := mkw 0x27fffefb9a94001e 0x813ffff7dcd4a000 0xe7ffffff1e1e0004 0x7f3ffffff8f0f000

def z324 : W := mkw 0x0000010004009000 0x0000000800200480 0x000000001c01d815 0x8000000000e00ec0

def z325 : W := mkw 0x0000000400404100 0x0000000020020208 0x0818003c01c00188 0x2040c001e00e000c

def z326 : W := mkw 0x0314301261212041 0x5018a18093090902 0xd7043003e021e073 0xceb821801f010f03

def z327 : W := mkw 0x27fffeff0040411c 0x013ffff7f8020208 0xefffffff01c1c199 0xff7ffffff80e0e0c

def z328 : W := mkw 0x05a13da0b609bc82 0x602d09ed05b04de4 0xf7e33fe0fe19ff9f 0xffbf19ff07f0cffc

def z329 : W := mkw 0x04ea800000000000 0x0027540000000000 0x00e3c00000000000 0x10071e0000000000

def z330 : W := mkw 0xa7fffeff616b6bfd 0x553ffff7fb0b5b5f 0xffffffffe3ffffff 0xffffffffff1fffff

def z331 : W := mkw 0x0eff8b2c0cd8d990 0x8877fc596066c6cc 0xefffef3c1dd9d99d 0xff7fff79e0eececc

def z332 : W := mkw 0x27fef4d30000000c 0x013ff7a698000000 0xc7ffd0c300000000 0x3e3ffe8618000000

def z333 : W := mkw 0x8deb7fedbedbffba 0xec6f5bff6df6dffd 0xffffffffffffffff 0xffffffffffffffff

def z334 : W := mkw 0x06fe80009a940002 0x8037f40004d4a000 0xc7ffc0001e1e0004 0x3e3ffe0000f0f000

def z335 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x1f3fc000e3fe000a 0x28f9fe00071ff000

def z336 : W := mkw 0x23157eff6161615d 0x5118abf7fb0b0b0a 0xff1c3fffe1e1e1fb 0xeff8e1ffff0f0f0f

def z337 : W := mkw 0x0314301261212041 0x5018a18093090902 0x17000000e0000000 0x00b8000007000000

def z338 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x6027ffff00000000 0x7b013ffff8000000

def z339 : W := mkw 0x0800030c0440d110 0x0840001860220688 0x0000271c0001c000 0x00000138e0000e00

def z340 : W := mkw 0x0b153b3e6569f9d1 0x5858a9d9f32b4fce 0xff1c3f3fe1e1f9fb 0xeff8e1f9ff0f0fcf

def z341 : W := mkw 0x214b7efb0000001c 0x010a5bf7d8000000 0xe0db3fff00000000 0x7706d9fff8000000

def z342 : W := mkw 0x0b1431166df9f9c1 0xd858a188b36fcfce 0xdf1c303ffdf9f9ff 0xeef8e181ffefcfcf

def z343 : W := mkw 0x080109240cd8d980 0x884008492066c6cc 0x680308201dd9d99d 0xf340184100eececc

def z344 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfdb0000fdd8000d 0xb6fed80007eec000

def z345 : W := mkw 0x82154877416a4be9 0x1410aa43ba0b525f 0x081fc03f01fe01e8 0x2040fe01f80ff00f

def z346 : W := mkw 0x07b4349200000000 0x003da1a490000000 0xe7fc3fff00000000 0x7f3fe1fff8000000

def z347 : W := mkw 0x000000009a940002 0x8000000004d4a000 0x000000001e1e0004 0x0000000000f0f000

def z348 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0x9fd8271cfdc00001 0x04fec138e7ee0000

def z349 : W := mkw 0x00000100b601b402 0x6000000805b00da0 0x702018c0fe01fe17 0xdb8100c607f00ff0

def z350 : W := mkw 0x04a0000092000002 0x0025000004900000 0xf7e018c0fe003e17 0xdfbf00c607f001f0

def z351 : W := mkw 0x8000404100020228 0x0400020208001011 0x6024d8c302263e76 0xdb0126c6181131f3

def z352 : W := mkw 0x07b4b016f3656143 0x503da580b79b2b0a 0xdf3cf03fe3e7e1fb 0xeef9e781ff1f3f0f

def z353 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x1f041003e1e1e1fb 0x88f820801f0f0f0f

def z354 : W := mkw 0x0da03584bed9fd82 0xe86d01ac25f6cfec 0xffe03fc0ffd9ff9f 0xdfff01fe07fecffc

def z355 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7e02fc0fe01de05 0x15bf017e07f00ef0

def z356 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0x603fd8ff00000000 0x7b01fec7f8000000

def z357 : W := mkw 0x06fe8004fbf56143 0xd037f40027dfab0a 0xdfffc000ffffe1ff 0xbefffe0007ffff0f

def z358 : W := mkw 0x025e800000000000 0x0012f40000000000 0x001fc00000000000 0x2000fe0000000000

def z359 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x00000000003e01e8 0x000000000001f00f

def z360 : W := mkw 0x27b4f5d3b601b40e 0x613da7ae9db00da0 0xf7e4ffc3fe01fe17 0xdfbf27fe1ff00ff0

def z361 : W := mkw 0x0fffbb3efffdf9d3 0xd87ffdd9f7ffefce 0xffffff3ffffff9ff 0xfffffff9ffffffcf

def z362 : W := mkw 0x0214001200000000 0x0010a00090000000 0x001c003f00000000 0x2000e001f8000000

def z363 : W := mkw 0x83157873612b2ae9 0x5418abc39b095957 0x7727d8e3e23e3ffe 0xfbb93ec71f11f1ff

def z364 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6027d8e3021e1e04 0x7b013ec71810f0f0

def z365 : W := mkw 0x05a03480b2012402 0x602d01a405900920 0x17000000e0000000 0x00b8000007000000

def z366 : W := mkw 0x26ffcefb0000001c 0x0137fe77d8000000 0x20ffcfff00000000 0x3107fe7ff8000000

def z367 : W := mkw 0x2cebcfed0cd8d99c 0x89675e7f6866c6cc 0xe8fbeffc1dd9d99d 0xf747df7fe0eececc

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001023000021f0 0x400000811800010f

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x0024c00002260002 0x0801260000113000

def z370 : W := mkw 0x0001486100000008 0x00000a4308000000 0x6027d8e3002021fa 0xfb013ec71801010f

def z371 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x172010c0fe01fe17 0x88b9008607f00ff0

def z372 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfdc0000fde0000b 0xaefee00007ef0000

def z373 : W := mkw 0x0000000461616141 0x50000000230b0b0a 0x18000000e1c1c001 0x00c00000070e0e00

def z374 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x081b003c1dd9d99d 0xa040d801e0eececc

def z375 : W := mkw 0x81017861200b2aa8 0x44080bc309005955 0xf727f8e3e23fffff 0xffb93fc71f11ffff

def z376 : W := mkw 0x07b43592b601b402 0x603da1ac95b00da0 0xf7fc3ffffe01fe17 0xffbfe1fffff00ff0

def z377 : W := mkw 0x07b43496f3616543 0x703da1a4b79b0b2a 0xdf3c30ffe3e1e7fb 0xeef9e187ff1f0f3f

def z378 : W := mkw 0x27feb69e61616155 0x513ff5b4f30b0b0a 0x9fd8271ce1c1c001 0x04fec138e70e0e00

def z379 : W := mkw 0x84a14861920a0aaa 0x04250a430c905055 0xf7e7d8e3fe3e3fff 0xffbf3ec71ff1f1ff

def z380 : W := mkw 0x07feb48000000000 0x003ff5a400000000 0xe7ffffc000000000 0x7f3ffffe00000000

def z381 : W := mkw 0x27fffefbd324001f 0x013ffff7de992000 0xf7ffffffe2260002 0x7fbfffffff113000

def z382 : W := mkw 0x2214c0530000000c 0x0110a60298000000 0x0004c00300000000 0x0000260018000000

def z383 : W := mkw 0x0000000420416140 0x5000000021020b0a 0x000000000001e1f0 0x0000000000000f0f

def z384 : W := mkw 0x05a03596b641f542 0x702d01acb5b20faa 0xf7e03ffffe01fff7 0xdfbf01fffff00fff

def z385 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8db2f1c1dd9d805 0x1546d978e0eecec0

def z386 : W := mkw 0x08010a2c00484990 0x084008516002424c 0x0000003c00000180 0x00000001e000000c

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x0007c000003e0008 0x20003e000001f000

def z388 : W := mkw 0x07feb01661616141 0x503ff580b30b0b0a 0xdffff03fe1e1e1fb 0xfeffff81ff0f0f0f

def z389 : W := mkw 0x8b5f7b7f6dfbfbf9 0xdc5afbdbfb6fdfdf 0xffffffffffffffff 0xffffffffffffffff

def z390 : W := mkw 0x24ea868800000014 0x0127543440000000 0x00c0070000000000 0x0006003800000000

def z391 : W := mkw 0x0214001641604141 0x1010a000b20b020a 0xdf1c003fe1e001eb 0xaef8e001ff0f000f

def z392 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffdc00001 0x7fffffffffee0000

def z393 : W := mkw 0x804b4a69000a0ab8 0x04025a5348005055 0xe0ffffff023e3ffe 0xff07fffff811f1ff

def z394 : W := mkw 0x0dea378cbed1f512 0xe86f51bc65f68fa8 0x9fd8271cfdc1c001 0x04fec138e7ee0e00

def z395 : W := mkw 0x05a03480b2012402 0x602d01a405900920 0x772018c0e2003e16 0xdbb900c6071001f0

def z396 : W := mkw 0x0214000041200001 0x0010a00002090000 0x17040000e0200002 0x08b8200007010000

def z397 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x87dfe73f00000000 0x243eff39f8000000

def z398 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f18201ce1e1e1fb 0x84f8c100e70f0f0f

def z399 : W := mkw 0x07b43596f761f543 0x703da1acb7bb0faa 0xdfdc373ffde1e1fb 0xeefee1b9ffef0f0f

def z400 : W := mkw 0x07feb01200000000 0x003ff58090000000 0xc7fff03f00000000 0x7e3fff81f8000000

def z401 : W := mkw 0x010035802401b400 0x600801ac01200da0 0x000027000001c000 0x0000013800000e00

def z402 : W := mkw 0x85a17ce1b20b2eaa 0x642d0be70d905975 0x7727d8e3e23e3ffe 0xfbb93ec71f11f1ff

def z403 : W := mkw 0x0100301661616141 0x50080180b30b0b0a 0x1800303fe1e1e1fb 0xc0c00181ff0f0f0f

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x4027c00000000000 0x3a013e0000000000

def z405 : W := mkw 0x01003580b601b402 0x600801ac05b00da0 0x30003fc0fe01fe17 0xc18001fe07f00ff0

def z406 : W := mkw 0x06fe800000000000 0x0037f40000000000 0x87d8000000000000 0x043ec00000000000

def z407 : W := mkw 0x27fffeff6161615d 0x513ffff7fb0b0b0a 0xffffffffe1c1c001 0x7fffffffff0e0e00

def z408 : W := mkw 0x80000004616b6be1 0x54000000230b5b5f 0x18000000e3ffffff 0x80c00000071fffff

def z409 : W := mkw 0x06fe8100dfb49003 0x8037f40806fda480 0xffffef00ffffd81f 0xffffff7807fffec0

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x400400000020000a 0xaa00200000010000

def z411 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7c02f00fc01d815 0xd7be017807e00ec0

def z412 : W := mkw 0x08010b2c0448d990 0x08400859602246cc 0xe0c02f3c1c01d995 0xd7060179e0e00ecc

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x002010c002002602 0x0801008600100130

def z414 : W := mkw 0x025e800049b40001 0x8012f400024da000 0xdf1fc000e1fe000b 0xaef8fe00070ff000

def z415 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2024d8e302263ff2 0x490126c7181131ff

def z416 : W := mkw 0x0314301200000000 0x0018a18090000000 0x0704100300000000 0x0838208018000000

def z417 : W := mkw 0x0100301200000000 0x0008018090000000 0x0000303f00000000 0x40000181f8000000

def z418 : W := mkw 0x87fff877fbff6beb 0xd43fffc3bfdffb5f 0xfffff8ffffffffff 0xffffffc7ffffffff

def z419 : W := mkw 0x0000404100000008 0x0000020208000000 0x0024d0c300000000 0x0801268618000000

def z420 : W := mkw 0x84ebc8619a9e0aaa 0x84275e430cd4f055 0x60e7d8e31e3e3ffe 0xfb073ec718f1f1ff

def z421 : W := mkw 0x06fe800041200001 0x0037f40002090000 0xdfffc000e1e0000b 0xbefffe00070f0000

def z422 : W := mkw 0x81017877204b6be8 0x54080bc3b9025b5f 0x200038ff0001fff0 0x410001c7f8000fff

def z423 : W := mkw 0x884b4b690c9a9ab8 0x8c425a5b4864d4d5 0x60e7dfe31e3e3ffe 0xfb073eff18f1f1ff

def z424 : W := mkw 0x2fffbfbe0cd8d994 0x897ffdfdf066c6cc 0xefdb2f3c1dd9d99d 0xf77ed979e0eececc

def z425 : W := mkw 0x0000000092000002 0x0000000004900000 0x10000000fe000007 0x8080000007f00000

def z426 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xffffd8c0fffe3e1f 0xfffffec607fff1f0

def z427 : W := mkw 0x08000104dffcd983 0x8840000826ffe6cc 0x18000000ffffd99f 0x80c0000007fffecc

def z428 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2023d8e3021e3ff4 0x51011ec71810f1ff

def z429 : W := mkw 0x235ffa7f6161615d 0x511affd3fb0b0b0a 0xdf1ff03fe1e1e1fb 0xeef8ff81ff0f0f0f

def z430 : W := mkw 0x0deb3fac0cd8d990 0x886f59fd6066c6cc 0xeffb3ffc1dd9d99d 0xff7fd9ffe0eececc

def z431 : W := mkw 0x06fe8100ffb5b403 0xe037f40807fdada0 0xdfffc000fffffe1f 0xbefffe0007fffff0

def z432 : W := mkw 0x80000000dbbe0aa3 0x8400000006ddf055 0x18000000fffe3fff 0x80c0000007fff1ff

def z433 : W := mkw 0x27feb69e61616155 0x513ff5b4f30b0b0a 0xdfdc373fe1e1e1fb 0xeefee1b9ff0f0f0f

def z434 : W := mkw 0x27fffeff2041615c 0x513ffff7f9020b0a 0xe7ffffff0001e1f0 0x7f3ffffff8000f0f

def z435 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x0000000000003ff0 0x00000000000001ff

def z436 : W := mkw 0x0001486100000008 0x00000a4308000000 0x6027d8e302003e16 0xfb013ec7181001f0

def z437 : W := mkw 0x80004041000a0aa8 0x0400020208005055 0x0024d0c3023e3ffe 0x880126861811f1ff

def z438 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7fbefdc00000000 0x153fdf7ee0000000

def z439 : W := mkw 0x86b5c861d32e0aab 0x0435ae430e997055 0x7727d8e3e23e3ffe 0xfbb93ec71f11f1ff

def z440 : W := mkw 0x210074d30000000c 0x010803a698000000 0x000010c300000000 0x0000008618000000

def z441 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0xe0fbeffc00000000 0x7707df7fe0000000

def z442 : W := mkw 0x0000000000080880 0x0000000000004044 0x000000000018199c 0x800000000000c0cc

def z443 : W := mkw 0x06fe800000000000 0x0037f40000000000 0xc7ffc000023e000e 0xbe3ffe000011f000

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x602018c000000000 0x5b0100c600000000

def z445 : W := mkw 0x05eb3ea800000010 0x002f59f540000000 0xe7fb3ffc00000000 0x7f3fd9ffe0000000

def z446 : W := mkw 0x07b4349661616141 0x503da1a4b30b0b0a 0xfffc3fffe1e1e1fb 0xffffe1ffff0f0f0f

def z447 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8d8273c1dc1c199 0xe646c139e0ee0e0c

def z448 : W := mkw 0x0314301200000000 0x0018a18090000000 0x8718201c00000000 0x0438c100e0000000

def z449 : W := mkw 0x86ffc861dbbe0aab 0x8437fe430eddf055 0xffffc8c0fffe1e0f 0xbffffe4607fff0f0

def z450 : W := mkw 0x084b0b2c0448d990 0x08425859602246cc 0xe0db2f3c0001d990 0x7706d979e0000ecc

def z451 : W := mkw 0x05a0348000000000 0x002d01a400000000 0xe7e03fc002003e16 0xdf3f01fe001001f0

def z452 : W := mkw 0x0000000400404100 0x0000000020020208 0x0000203c0001c190 0x40000101e0000e0c

def z453 : W := mkw 0x81017877204b6be8 0x54080bc3b9025b5f 0x6027f8ff023ffffe 0xfb013fc7f811ffff

def z454 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6007c823003e19fc 0xf3003e411801f0cf

def z455 : W := mkw 0x27fffefb2001201c 0x413ffff7d9000900 0xf7ffffffe001e013 0xffbfffffff000f00

def z456 : W := mkw 0x04ea85809e949402 0xa027542c04f4a4a0 0x20e3cfc01e1e1e04 0x11071e7e00f0f0f0

def z457 : W := mkw 0x07feb480dbb40003 0x803ff5a406dda000 0xffffffc0fffe000f 0xfffffffe07fff000

def z458 : W := mkw 0x24ebcfe99600941e 0x21275e7f4cb004a0 0x20e3cfc01e001e04 0x11071e7e00f000f0

def z459 : W := mkw 0x0000058004009400 0x2000002c002004a0 0x20000fc000001e00 0x0100007e000000f0

def z460 : W := mkw 0x0100348000000000 0x000801a400000000 0x20003fc000000000 0x410001fe00000000

def z461 : W := mkw 0x004a01000c909000 0x8002500800648480 0xe8db2f001dd9d81d 0xf746d97800eecec0

def z462 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f1c301fe1e1e063 0x0cf8e180ff0f0f03

def z463 : W := mkw 0x8effcb6ddffedbbb 0x8c77fe5b6efff6dd 0xffffffffffffffff 0xffffffffffffffff

def z464 : W := mkw 0x0001082000080880 0x0000084100004044 0x60071823003839fe 0xfb0038c11801c1cf

def z465 : W := mkw 0x084b0b2cbed9fd92 0xe842585965f6cfec 0xf8db2f3cffd9ff9f 0xf7c6d979e7fecffc

def z466 : W := mkw 0x004a000008900000 0x8002500000448000 0x00c300001c180004 0x1006180000e0c000

def z467 : W := mkw 0x084b0b2c6df9f9d1 0xd8425859636fcfce 0xf8db2f3cfdf9f9ff 0xf7c6d979e7efcfcf

def z468 : W := mkw 0x0da13facb649fd92 0x686d09fd65b24fec 0xf7e03ffcfe01ff97 0xdfbf01ffe7f00ffc

def z469 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027c8e3023e1fec 0x31013e471811f0ff

def z470 : W := mkw 0x04a0058096009402 0x2025002c04b004a0 0x00c007001c000000 0x0006003800e00000

def z471 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6023c8e0021e1f9c 0xf3011e470010f0fc

def z472 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x00000000021e1e04 0x000000000010f0f0

def z473 : W := mkw 0x004b0a2808900010 0x8002585140448000 0xe8db2f3c1dd8000d 0xf746d979e0eec000

def z474 : W := mkw 0x084a01040cd8d980 0x884250082066c6cc 0xc8db00001dd9d99d 0xb646d80000eececc

def z475 : W := mkw 0x0b5e331e6df1f151 0xd85af198f36f8f8a 0xdfdc373ffde1e1fb 0xeefee1b9ffef0f0f

def z476 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0xe8db2f3c1dc1c001 0x7746d979e0ee0e00

def z477 : W := mkw 0x26ffcee9dbb4001f 0x8137fe774edda000 0xffffcfc0fffe000f 0xbffffe7e07fff000

def z478 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2007d8e3003e3ff8 0x61003ec71801f1ff

def z479 : W := mkw 0x0214001641604141 0x1010a000b20b020a 0xc81c203f01e1c1f9 0xe640e101f80f0e0f

def z480 : W := mkw 0x04ea8000dbb40003 0x8027540006dda000 0x18e3c000fffe000f 0x90c71e0007fff000

def z481 : W := mkw 0x0100300420416100 0x4008018021020b08 0xdf18303ce1c1e19b 0xeef8c181e70e0f0c

def z482 : W := mkw 0x00000000b2012402 0x6000000005900920 0x10000000e2002602 0x0080000007100130

def z483 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff0018199c 0xff3ffffff800c0cc

def z484 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6027d8e300003ff0 0x7b013ec7180001ff

def z485 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x20003fff00003ff0 0x410001fff80001ff

def z486 : W := mkw 0x0fff3fbefff9fdd3 0xf87ff9fdf7ffcfee 0xffff3ffffff9ffff 0xfffff9ffffffcfff

def z487 : W := mkw 0x08010b2c0448d990 0x08400859602246cc 0xe8182f3c01c1d999 0xe740c179e00e0ecc

def z488 : W := mkw 0x0eff8b28dfbc9893 0x8877fc5946fde4c4 0xffffcf00fffe180f 0xbffffe7807fff0c0

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0x00040023002001e8 0x200020011801000f

def z490 : W := mkw 0x07feb012dbb40003 0x803ff58096dda000 0xdffff03ffffe000f 0xfeffff81fffff000

def z491 : W := mkw 0x07feb016fbf56143 0xd03ff580b7dfab0a 0xdfdc303ffde1e1fb 0xeefee181ffef0f0f

def z492 : W := mkw 0x06b40000d3200003 0x0035a00006990000 0xdffc0000ffe0000f 0xbeffe00007ff0000

def z493 : W := mkw 0x27fffefbb201241e 0x613ffff7dd900920 0xf7ffffffe2002602 0x7fbfffffff100130

def z494 : W := mkw 0x06b4800000000000 0x0035a40000000000 0x0724c00000000000 0x0839260000000000

def z495 : W := mkw 0x07feb480fbb52403 0xe03ff5a407dda920 0xdfffd0c0fffe260f 0xbefffe8607fff130

def z496 : W := mkw 0x27fffefb49b4001d 0x813ffff7da4da000 0xefffffff01fe0008 0x7f7ffffff80ff000

def z497 : W := mkw 0x025e801649f44141 0x9012f400b24fa20a 0x081fc03f01fe01e8 0x2040fe01f80ff00f

def z498 : W := mkw 0x04a0058096009402 0x2025002c04b004a0 0xf7e00fc0fe001e07 0x9fbf007e07f000f0

def z499 : W := mkw 0x05a03000b2012002 0x402d018005900900 0xd7e03000fe01e017 0xdebf018007f00f00

def z500 : W := mkw 0x8000404100020228 0x0400020208001011 0x0004c00300260060 0x0000260018013003

def z501 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x200008c000001e00 0x01000046000000f0

def z502 : W := mkw 0x0a5f0a3e49f849d1 0x9852f851f24fc24e 0x081f003f01f801e8 0x2040f801f80fc00f

def z503 : W := mkw 0x0214000041200001 0x0010a00002090000 0x9f180000e1c00001 0x04f8c000070e0000

def z504 : W := mkw 0x0000000061212041 0x5000000003090902 0x10000000e0202062 0x0080000007010103

def z505 : W := mkw 0x0314300061212001 0x4018a18003090900 0xdf1c3000e1e1e01b 0xeef8e180070f0f00

def z506 : W := mkw 0x00000000d3240003 0x0000000006992000 0x10000000e2260002 0x0080000007113000

def z507 : W := mkw 0x0214000041200001 0x0010a00002090000 0xdf3fc000e3fe000f 0xbef9fe00071ff000

def z508 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x08ffc0001ffe000c 0x3047fe0000fff000

def z509 : W := mkw 0x05a0348020012000 0x402d01a401000900 0xf7e03fc0e001e013 0xdfbf01fe07000f00

def z510 : W := mkw 0x0001082000080880 0x0000084100004044 0x0003002000180188 0x200018010000c00c

def z511 : W := mkw 0x8000404100020228 0x0400020208001011 0x0020c0c002060600 0x0001060600103030

def z512 : W := mkw 0x06b48000d3240003 0x0035a40006992000 0xd7e4c000fe260007 0x9ebf260007f13000

def z513 : W := mkw 0x0efe830cdff4d113 0x8877f41866ffa688 0xdfffe71cffffc00f 0xbeffff38e7fffe00

def z514 : W := mkw 0x03143116f761f543 0x7018a188b7bb0faa 0xdf1c303fffe1ffff 0xeef8e181ffff0fff

def z515 : W := mkw 0x07feb580ffb5b403 0xe03ff5ac07fdada0 0xfff83fc0ffc1fe17 0xdfffc1fe07fe0ff0

def z516 : W := mkw 0x04ea80009a940002 0x8027540004d4a000 0x40e7c0001e3e000e 0xba073e0000f1f000

def z517 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0x87fcf7df00000000 0x0c3fe7bef8000000

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0xc818000001c00009 0xa640c000000e0000

def z519 : W := mkw 0x880001040cdadba0 0x8c4000082066d6dd 0x080000001fffffff 0x8040000000ffffff

def z520 : W := mkw 0x80014865616b6be9 0x54000a432b0b5b5f 0x7827d8e3e3ffffff 0xfbc13ec71f1fffff

def z521 : W := mkw 0x05a03580ffb5b403 0xe02d01ac07fdada0 0xffe03fc0fffffe1f 0xdfff01fe07fffff0

def z522 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff00003ff0 0x7f3ffffff80001ff

def z523 : W := mkw 0x031435966561f541 0x7018a1acb32b0faa 0xff1c3fffe1e1fffb 0xeff8e1ffff0f0fff

def z524 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x37203fc0e201fe12 0x49b901fe07100ff0

def z525 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0xdfffe71cfffe000f 0xbeffff38e7fff000

def z526 : W := mkw 0x26ffca7bdbb4001f 0x8137fe53dedda000 0xdfffc03ffffe000f 0xbefffe01fffff000

def z527 : W := mkw 0x0100300020012000 0x4008018001000900 0x97002000e001c001 0x04b8010007000e00

def z528 : W := mkw 0x0100301220012040 0x5008018091000902 0x0000100300002060 0x0000008018000103

def z529 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9ffcc000ffe60003 0x0cffe60007ff3000

def z530 : W := mkw 0x06b48000d3240003 0x0035a40006992000 0x17000000e0000000 0x00b8000007000000

def z531 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x200018e3023e3ffe 0xc10000c71811f1ff

def z532 : W := mkw 0x25ebfee90000001c 0x012f5ff748000000 0xe7e3ffc000000000 0x5f3f1ffe00000000

def z533 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x602018e302003ff6 0xdb0100c7181001ff

def z534 : W := mkw 0x880149650cdadba8 0x8c400a4b2866d6dd 0x6827d8e31fffffff 0xfb413ec718ffffff

def z535 : W := mkw 0x04a00100b601b402 0x6025000805b00da0 0xd7e00000fe01fe17 0x9ebf000007f00ff0

def z536 : W := mkw 0x88014b6d044adbb8 0x0c400a5b682256dd 0x6027ffff023ffffe 0xfb013ffff811ffff

def z537 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x27e7dfc300000000 0x193f3efe18000000

def z538 : W := mkw 0x0314301241200001 0x0018a18092090000 0xdf1c303fe1e0000b 0xeef8e181ff0f0000

def z539 : W := mkw 0x85a17de1b60bbeaa 0x642d0bef0db05df5 0xf7e03fe3fe01fff7 0xdfbf01ff1ff00fff

def z540 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0x60e7dfe300000000 0x7b073eff18000000

def z541 : W := mkw 0x2ffeb79e0cd0d114 0x897ff5bcf0668688 0x8fd8271c1dc1c001 0x047ec138e0ee0e00

def z542 : W := mkw 0x07b43592f721b443 0x703da1ac97b90da2 0xf7e43fc3fe21fe77 0xdfbf21fe1ff10ff3

def z543 : W := mkw 0x21017ffb2401b41c 0x61080bffd9200da0 0x20003fff0001fe10 0x410001fff8000ff0

def z544 : W := mkw 0x86fec041dbb6022b 0x8437f6020eddb011 0xdfffd0c3fffe266f 0xbefffe861ffff133

def z545 : W := mkw 0x06fe800092000002 0x0037f40004900000 0xd7ffc000fe000007 0xbebffe0007f00000

def z546 : W := mkw 0x094b3b3e2cd9f9d0 0xd84a59d9f166cfce 0xe8db3f3f1dd9f9fd 0xf746d9f9f8eecfcf

def z547 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x97c02700fe01fe17 0x84be013807f00ff0

def z548 : W := mkw 0x0fffbfacfffdfd93 0xe87ffdfd67ffefec 0xfffffffcffffff9f 0xffffffffe7fffffc

def z549 : W := mkw 0x8000404100020228 0x0400020208001011 0x000010c300002660 0x0000008618000133

def z550 : W := mkw 0x80000000000a0aa0 0x0400000000005055 0x40041023023e3ffe 0xea0020811811f1ff

def z551 : W := mkw 0x0001486100000008 0x00000a4308000000 0x6027d8e3023e000e 0xfb013ec71811f000

def z552 : W := mkw 0x0000000020012000 0x4000000001000900 0x10000000e001e013 0x8080000007000f00

def z553 : W := mkw 0x00000100ffb5b403 0xe000000807fdada0 0x18000000fffffe1f 0x80c0000007fffff0

def z554 : W := mkw 0x04a0800092040002 0x0025040004902000 0x0020c00002060000 0x0001060000103000

def z555 : W := mkw 0x05a0358096009402 0x202d01ac04b004a0 0xe7e03fc01e001e04 0x5f3f01fe00f000f0

def z556 : W := mkw 0x05ea3580be91b402 0xe02f51ac05f48da0 0xfffb3fc0ffd9fe1f 0xffffd9fe07fecff0

def z557 : W := mkw 0x83143016616b6be1 0x5418a180b30b5b5f 0xdf1c303fe3ffffff 0xeef8e181ff1fffff

def z558 : W := mkw 0x035e301669f16141 0xd01af180b34f8b0a 0xdfdf303ffdf9e1ff 0xfefef981ffefcf0f

def z559 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x37e01fc0fe003e06 0x19bf00fe07f001f0

def z560 : W := mkw 0x0314301620416140 0x5018a180b1020b0a 0xc71c303f0001e1f0 0x6e38e181f8000f0f

def z561 : W := mkw 0x0a5f8a2c49fc4991 0x8852fc51624fe24c 0x081fc03c01fe0188 0x2040fe01e00ff00c

def z562 : W := mkw 0x2cebcfe90c98989c 0x89675e7f4864c4c4 0x20e3cfc01c181804 0x11071e7e00e0c0c0

def z563 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8fbeffc1fdfdf9d 0xf747df7fe0fefefc

def z564 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x1f1c103fe1e021ea 0x28f8e081ff0f010f

def z565 : W := mkw 0x025e800049b40001 0x8012f400024da000 0xc8dfc0001dfe000d 0xb646fe0000eff000

def z566 : W := mkw 0x035f3a3e61616151 0x501af9d1f30b0b0a 0xffdf3f3fe1e1e1fb 0xfffef9f9ff0f0f0f

def z567 : W := mkw 0x0deb3fa8be99bc92 0xe86f59fd45f4cde4 0xf7e33fc0fe19fe17 0xdfbf19fe07f0cff0

def z568 : W := mkw 0x094b3b2c2cd9f990 0xc84a59d96166cfcc 0xffdb3f3cfdd9f99f 0xfffed9f9e7eecfcc

def z569 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x28c30f001dd9d99d 0x9146187800eececc

def z570 : W := mkw 0x0100348020012400 0x600801a401000920 0x000010c000002600 0x0000008600000130

def z571 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x600418e300203ffa 0xeb0020c7180101ff

def z572 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x081c303f01e1e1f8 0x6040e181f80f0f0f

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004100300202062 0x0800208018010103

def z574 : W := mkw 0x0b5f3b3e6df9f9d1 0xd85af9d9f36fcfce 0xffdb2f3cfdd9d99d 0xf7fed979e7eececc

def z575 : W := mkw 0x0000010096009402 0x2000000804b004a0 0x000000001e001e04 0x0000000000f000f0

def z576 : W := mkw 0x07b4b012f3252043 0x503da58097992902 0x1724d003e2262062 0x08b926801f113103

def z577 : W := mkw 0x24a0c4c10000000c 0x0125062608000000 0x0020c0c000000000 0x0001060600000000

def z578 : W := mkw 0x0214001641604141 0x1010a000b20b020a 0x0818001c01c00000 0x0040c000e00e0000

def z579 : W := mkw 0x05eab580be95b402 0xe02f55ac05f4ada0 0xf7e3ffc0fe1ffe17 0xdfbf1ffe07f0fff0

def z580 : W := mkw 0x0efe8104dffcd983 0x8877f40826ffe6cc 0xdfffc000ffffd99f 0xbefffe0007fffecc

def z581 : W := mkw 0x05a17de1b601b40a 0x602d0bef0db00da0 0xf7e7ffe3fe01fe17 0xffbf3fff1ff00ff0

def z582 : W := mkw 0x8000404100020228 0x0400020208001011 0x4024d0e3022627fa 0xea0126871811313f

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000002021fa 0x800000000001010f

def z584 : W := mkw 0x04a0000092000002 0x0025000004900000 0x97c00000fc000001 0x04be000007e00000

def z585 : W := mkw 0x27fffffb2401b41c 0x613fffffd9200da0 0xe7ffffff0001fe10 0x7f3ffffff8000ff0

def z586 : W := mkw 0x0314301220012000 0x4018a18091000900 0xd71c303fe001e013 0xeeb8e181ff000f00

def z587 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x600318e300183ffc 0xf30018c71800c1ff

def z588 : W := mkw 0x884b4a6d08da4bb8 0x8c425a536846d25d 0x683fd8ff03fe3ffe 0xfb41fec7f81ff1ff

def z589 : W := mkw 0x88014b6d044adbb8 0x0c400a5b682256dd 0x20003fff0001fff0 0x410001fff8000fff

def z590 : W := mkw 0x07b43016f3616143 0x503da180b79b0b0a 0xdffc303fffe1e1ff 0xfeffe181ffff0f0f

def z591 : W := mkw 0x0214000041200001 0x0010a00002090000 0xdf1c1023e1e021fb 0xeef8e0811f0f010f

def z592 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6023d8c0021e3e16 0xdb011ec60010f1f0

def z593 : W := mkw 0x235ffa7b0000001c 0x011affd3d8000000 0xc71ff03f00000000 0x6e38ff81f8000000

def z594 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027d8c3023e3e66 0x19013ec61811f1f3

def z595 : W := mkw 0x0efe830cdff4d113 0x8877f41866ffa688 0x9fd8271cfdc1c001 0x04fec138e7ee0e00

def z596 : W := mkw 0x0000010004009000 0x0000000800200480 0xe0e03fc01e01fe17 0xdf0701fe00f00ff0

def z597 : W := mkw 0x06ffc86100000008 0x0037fe4308000000 0xe7ffd8e300000000 0x7f3ffec718000000

def z598 : W := mkw 0x884b4b690c9a9ab8 0x8c425a5b4864d4d5 0x20e3cfc01e1e1e04 0x11071e7e00f0f0f0

def z599 : W := mkw 0x010035802401b400 0x600801ac01200da0 0xf7003fc0e001fe13 0xcfb801fe07000ff0

def z600 : W := mkw 0x07feb016fbf56143 0xd03ff580b7dfab0a 0xdfffe01cffffc00f 0xbeffff00e7fffe00

def z601 : W := mkw 0x87fffde1ffbfbeab 0xe43fffef0ffdfdf5 0xffffffe3ffffffff 0xffffffff1fffffff

def z602 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x20c32f3c1c19d994 0x51061979e0e0cecc

def z603 : W := mkw 0x0001092004089880 0x00000849002044c4 0xe0c32f201c19d99d 0xf706197900e0cecc

def z604 : W := mkw 0x85a17de1b60bbeaa 0x642d0bef0db05df5 0xf7e3ffc0fe1ffe17 0xdfbf1ffe07f0fff0

def z605 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fc0fc01c001 0x5fbf01fe07e00e00

def z606 : W := mkw 0x0100301620416140 0x50080180b1020b0a 0x0000201c0001c000 0x00000100e0000e00

def z607 : W := mkw 0x81017de1240bbea8 0x64080bef09205df5 0x20003fe30001fff0 0x410001ff18000fff

def z608 : W := mkw 0x084b0a2c08d84990 0x884258516046c24c 0xc81b203c01d9c199 0xe640d901e00ece0c

def z609 : W := mkw 0x27fffffff761f55f 0x713fffffffbb0faa 0xffffffffffe1ffff 0xffffffffffff0fff

def z610 : W := mkw 0x04a0048092000402 0x2025002404900020 0x002000c002000600 0x0001000600100030

def z611 : W := mkw 0x80014961040a9aa8 0x04000a4b082054d5 0xe0e7ffe31e3fffff 0xff073fff18f1ffff

def z612 : W := mkw 0x26ffcee90000001c 0x0137fe7748000000 0xe7ffcfc000000000 0x3f3ffe7e00000000

def z613 : W := mkw 0x05a035802401b400 0x602d01ac01200da0 0xe7e03fc00001fe10 0x5f3f01fe00000ff0

def z614 : W := mkw 0x07b43596f761f543 0x703da1acb7bb0faa 0x9fd8271cfdc1c001 0x04fec138e7ee0e00

def z615 : W := mkw 0x06fe8016dbf44143 0x9037f400b6dfa20a 0xdfffc03ffffe01ef 0xbefffe01fffff00f

def z616 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2023c8c0023e3ffe 0x91011e460011f1ff

def z617 : W := mkw 0x05a0348000000000 0x002d01a400000000 0x072010c000000000 0x0839008600000000

def z618 : W := mkw 0xa25fca7b000a0abc 0x0512fe53d8005055 0x603fd8ff023e3ffe 0xfb01fec7f811f1ff

def z619 : W := mkw 0x0100300020012000 0x4008018001000900 0xd7043023e021e1fb 0xeeb821811f010f0f

def z620 : W := mkw 0x83157873000a0aa8 0x0418abc398005055 0xe73ff8ff023e3ffe 0xff39ffc7f811f1ff

def z621 : W := mkw 0x2fffffff6df9f9dd 0xd97ffffffb6fcfce 0xfffffffffdf9f9ff 0xffffffffffefcfcf

def z622 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf18203ce1c1c199 0xe6f8c101e70e0e0c

def z623 : W := mkw 0x025e800049b40001 0x8012f400024da000 0x483fc00003fe000e 0xba41fe00001ff000

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0xd7000000e0000003 0x8eb8000007000000

def z625 : W := mkw 0x004b082008980880 0x800258410044c044 0xe8db08201dd8199d 0xf746d84100eec0cc

def z626 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x6027c8c0023e1e0e 0xbb013e460011f0f0

def z627 : W := mkw 0x084b0a2c08d84990 0x884258516046c24c 0xc8db003c1dd8018d 0xb646d801e0eec00c

def z628 : W := mkw 0x08010b2c0cd8d990 0x884008596066c6cc 0x28002f3c1dd9d99d 0xc1400179e0eececc

def z629 : W := mkw 0x87b57df7f76bffeb 0x743dabefbfbb5fff 0xffffffffffffffff 0xffffffffffffffff

def z630 : W := mkw 0x81017de1240bbea8 0x64080bef09205df5 0x6027ffe3023ffffe 0xfb013fff1811ffff

def z631 : W := mkw 0x27fffefb0890001c 0x813ffff7d8448000 0xefffffff1dd8000d 0xff7ffffff8eec000

def z632 : W := mkw 0x84a14de1960a9eaa 0x24250a6f0cb054f5 0x60e7dfe31e3e3ffe 0xfb073eff18f1f1ff

def z633 : W := mkw 0x0001486100000008 0x00000a4308000000 0x0007c02300000000 0x20003e0118000000

def z634 : W := mkw 0x0000000049b40001 0x80000000024da000 0x0800000001fe0008 0x00400000000ff000

def z635 : W := mkw 0x21017eff2041615c 0x51080bf7f9020b0a 0x20003fff0001e1f0 0x410001fff8000f0f

def z636 : W := mkw 0x27b4f4d3b201240e 0x613da7a69d900920 0x1724d0c3e2002602 0x08b926861f100130

def z637 : W := mkw 0x27b4f4d36121204d 0x513da7a69b090902 0x1724d0c3e0202062 0x08b926861f010103

def z638 : W := mkw 0xa7b4f4d30002022c 0x053da7a698001011 0x0724d0c302262662 0x0839268618113133

def z639 : W := mkw 0x09013b3e2449f9d0 0x584809d9f1224fce 0x20003f3f0001f9f0 0x410001f9f8000fcf

def z640 : W := mkw 0x0314301641604141 0x1018a180b20b020a 0xcf1c303f01e001e8 0x6e78e181f80f000f

def z641 : W := mkw 0x0001486100000008 0x00000a4308000000 0x200018e300000000 0x410000c718000000

def z642 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc000fdc00001 0x3efffe0007ee0000

def z643 : W := mkw 0x0001082400484980 0x000008412002424c 0xe81b283c01d9d99d 0xf740d941e00ececc

def z644 : W := mkw 0x8001486100020228 0x04000a4308001011 0x6027d8e302262662 0x7b013ec718113133

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002003e16 0x80000000001001f0

def z646 : W := mkw 0x02140000dbb40003 0x8010a00006dda000 0xdf1c0000fffe000f 0xaef8e00007fff000

def z647 : W := mkw 0x04a0000092000002 0x0025000004900000 0x17200000e2000002 0x08b9000007100000

def z648 : W := mkw 0x00000100b601b402 0x6000000805b00da0 0xf0c02f00fe01fe17 0xd786017807f00ff0

def z649 : W := mkw 0x05a0358004009000 0x002d01ac00200480 0xe7e03fc01c01d815 0xdf3f01fe00e00ec0

def z650 : W := mkw 0x04a00580b601b402 0x6025002c05b00da0 0x30e00fc0fe01fe17 0x9187007e07f00ff0

def z651 : W := mkw 0x084b0a2c08d84990 0x884258516046c24c 0x681b083c01d8199c 0xf340d841e00ec0cc

def z652 : W := mkw 0x84ebc8619a9e0aaa 0x84275e430cd4f055 0x20e3c8c01e1e1e04 0x11071e4600f0f0f0

def z653 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x00000023000001e0 0x000000011800000f

def z654 : W := mkw 0x26ffca7b0000001c 0x0137fe53d8000000 0xc7ffc03f00000000 0x3e3ffe01f8000000

def z655 : W := mkw 0x804b4861089a0aa8 0x84025a430844d055 0xe8ffd8e31ffe3fff 0xff47fec718fff1ff

def z656 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x281b2f3c01d9d998 0x6140d979e00ececc

def z657 : W := mkw 0x0deb3facbed9fd92 0xe86f59fd65f6cfec 0xffdb2f3cfdd9d99d 0xf7fed979e7eececc

def z658 : W := mkw 0x27fffffb9600941e 0x213fffffdcb004a0 0xe7ffffff1e001e04 0x7f3ffffff8f000f0

def z659 : W := mkw 0x0214001641604141 0x1010a000b20b020a 0x481c103f01e021fa 0xea40e081f80f010f

def z660 : W := mkw 0x0214000441604101 0x0010a000220b0208 0xdf1c203ce1e1c19b 0xeef8e101e70f0e0c

def z661 : W := mkw 0x225fca7f4160415d 0x1112fe53fa0b020a 0x081fc03f01e001e8 0x2040fe01f80f000f

def z662 : W := mkw 0x85a03580b60bbea2 0x642d01ac05b05df5 0xf7e03fc0fe3fffff 0xdfbf01fe07f1ffff

def z663 : W := mkw 0x06ffc861dbb4000b 0x8037fe430edda000 0xffffd8e3fffe000f 0xfffffec71ffff000

def z664 : W := mkw 0x27fffeff4160415d 0x113ffff7fa0b020a 0xefffffff01e001e8 0x7f7ffffff80f000f

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000080000001814 0xd3000040000000c0

def z666 : W := mkw 0x8000404100020228 0x0400020208001011 0x4027d0c3023e266e 0xba013e861811f133

def z667 : W := mkw 0x025e000049b00001 0x8012f000024d8000 0xdfdf0000fdf8000f 0xbefef80007efc000

def z668 : W := mkw 0x2ffffffb0c98989c 0x897fffffd864c4c4 0xe7ffffff1c181804 0x7f3ffffff8e0c0c0

def z669 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x1704303fe021e1f2 0x48b82181ff010f0f

def z670 : W := mkw 0x82154861412a0aa9 0x0410aa430a095055 0xff3fd8e3e3fe3fff 0xfff9fec71f1ff1ff

def z671 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x28db0f3c1dd8198c 0x3146d879e0eec0cc

def z672 : W := mkw 0x004b0b2804009010 0x0002585940200480 0xe0db2f3c1c01d815 0xf706d979e0e00ec0

def z673 : W := mkw 0x0000000441604141 0x10000000220b020a 0x0800000001e001e8 0x00400000000f000f

def z674 : W := mkw 0x08010b2804089890 0x08400859402044c4 0x20000f0000001800 0x01000078000000c0

def z675 : W := mkw 0x06b48000d3240003 0x0035a40006992000 0xdf3cc000e3e6000b 0xaef9e600071f3000

def z676 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c303fe1c1c001 0x6ef8e181ff0e0e00

def z677 : W := mkw 0x07feb016fbf56143 0xd03ff580b7dfab0a 0x9fd8201cfdc1c001 0x04fec100e7ee0e00

def z678 : W := mkw 0x04a0010096009002 0x0025000804b00480 0xf7e02f00fe01d817 0xdfbf017807f00ec0

def z679 : W := mkw 0x0000001600404140 0x10000000b002020a 0x0000003f000001e0 0x00000001f800000f

def z680 : W := mkw 0x025e800049b40001 0x8012f400024da000 0x0818000001c00000 0x0040c000000e0000

def z681 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xd7e02700fe01c007 0x9ebf013807f00e00

def z682 : W := mkw 0x0314301600404100 0x0018a180b0020208 0xcf1c303f01c1c199 0xee78e181f80e0e0c

def z683 : W := mkw 0x0000010004009000 0x0000000800200480 0x20002f000001d810 0x4100017800000ec0

def z684 : W := mkw 0x0100301620416140 0x50080180b1020b0a 0x4004303f0021e1fa 0xea002181f8010f0f

def z685 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xd7c03700fc01e013 0xcebe01b807e00f00

def z686 : W := mkw 0x04ea80009a940002 0x8027540004d4a000 0xc8fbc0001fde000d 0xb647de0000fef000

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00020000001c011 0xc600010000000e00

def z688 : W := mkw 0x06fe8004dbf44103 0x8037f40026dfa208 0xdfffe03cffffc19f 0xfeffff01e7fffe0c

def z689 : W := mkw 0x01003100b601b402 0x6008018805b00da0 0xd7003000fe01fe17 0xceb8018007f00ff0

def z690 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0xc818203c1dd9d99d 0xe640c101e0eececc

def z691 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x073fd0ff00000000 0x2839fe87f8000000

def z692 : W := mkw 0x0000000041200001 0x0000000002090000 0x18000000e1e0000b 0x80c00000070f0000

def z693 : W := mkw 0x07b43580f721b403 0x603da1ac07b90da0 0xfffc3fc0ffe1fe1f 0xffffe1fe07ff0ff0

def z694 : W := mkw 0x2fffffffbed9fd9e 0xe97ffffffdf6cfec 0xffffffffffd9ff9f 0xfffffffffffecffc

def z695 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf18301ce1c1e013 0xcef8c180e70e0f00

def z696 : W := mkw 0x0214001241200041 0x1010a00092090002 0x0004000300200060 0x0000200018010003

def z697 : W := mkw 0x05a03584f761f543 0x702d01ac27bb0faa 0xffe03fc0ffe1ffff 0xdfff01fe07ff0fff

def z698 : W := mkw 0x094b3fac2cd9fd90 0xe84a59fd6166cfec 0xe8db3ffc1dd9ff9d 0xf746d9ffe0eecffc

def z699 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x20e03fc01e01fe14 0x510701fe00f00ff0

def z700 : W := mkw 0x004a800008940000 0x800254000044a000 0x0003c000001e0000 0x00001e000000f000

def z701 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x0003c000001e0000 0x00001e000000f000

def z702 : W := mkw 0x04a0058096009402 0x2025002c04b004a0 0xe0e02fc01e01de15 0xd707017e00f00ef0

def z703 : W := mkw 0x825fc86149be0aa9 0x8412fe430a4df055 0x683fd8e303fe3ffe 0xfb41fec7181ff1ff

def z704 : W := mkw 0x084b0b2cdffcd993 0x8842585966ffe6cc 0xf8db2f3cffffd99f 0xf7c6d979e7fffecc

def z705 : W := mkw 0x08010b2c0448d990 0x08400859602246cc 0x60032f3c0019d99c 0xf3001979e000cecc

def z706 : W := mkw 0x07feb012fbb52043 0xd03ff58097dda902 0xdfffd003fffe206f 0xbefffe801ffff103

def z707 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0xe83fd8e303fe3fff 0xff41fec7181ff1ff

def z708 : W := mkw 0x05a03592b601b402 0x602d01ac95b00da0 0xf7e03ffffe01fe17 0xdfbf01fffff00ff0

def z709 : W := mkw 0xa1017efb0002023c 0x05080bf7d8001011 0x2024ffff02262662 0x490127fff8113133

def z710 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027d8e3023e3fee 0x39013ec71811f1ff

def z711 : W := mkw 0x080001042cd9f980 0xc84000082166cfcc 0x18000000fdd9f99f 0x80c0000007eecfcc

def z712 : W := mkw 0x26fe869a00000014 0x0137f434d0000000 0x00d8071c00000000 0x0006c038e0000000

def z713 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8dfffff1dfffffd 0xf746fffff8efffff

def z714 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88d8271c1dd9c00d 0x8446c138e0eece00

def z715 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff003e21fa 0xff3ffffff801f10f

def z716 : W := mkw 0x00000104f761f543 0x7000000827bb0faa 0x18000000ffc1fe17 0x80c0000007fe0ff0

def z717 : W := mkw 0x2100369a00000014 0x010801b4d0000000 0x20003fdc00000000 0x410001fee0000000

def z718 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8df3f3f1fffffff 0xff46f9f9f8ffffff

def z719 : W := mkw 0x27feb69ad3240017 0x013ff5b4d6992000 0x97fce71ce2260002 0x0cbfe738e7113000

def z720 : W := mkw 0x27fef6dbdbb4001f 0x813ff7b6dedda000 0x9ffcf7dfffe60003 0x0cffe7beffff3000

def z721 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fc0fe3ffe1f 0xdfbf01fe07f1fff0

def z722 : W := mkw 0x27fffefb2001201c 0x413ffff7d9000900 0xf7ffffffe201fe17 0xffbfffffff100ff0

def z723 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8db2f3c1dd9d999 0x6546d979e0eececc

def z724 : W := mkw 0x214b7efb0000001c 0x010a5bf7d8000000 0xe0ffffff00000000 0x7f07fffff8000000

def z725 : W := mkw 0x0efe8104dffcd983 0x8877f40826ffe6cc 0x9fd80000fdd9d99d 0x84fec00007eececc

def z726 : W := mkw 0x01013a3a00000010 0x000809d1d0000000 0x20003f3f00000000 0x410001f9f8000000

def z727 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x6027ffff023e000e 0xfb013ffff811f000

def z728 : W := mkw 0x880001040cdadba0 0x8c4000082066d6dd 0x080000001dd9fffd 0x8040000000eecfff

def z729 : W := mkw 0x884a030c0cdadbb0 0x8c4250186066d6dd 0x88d8271c1fffffff 0x8446c138e0ffffff

def z730 : W := mkw 0x080001040448d980 0x08400008202246cc 0x000000001c01d995 0x8000000000e00ecc

def z731 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff02183f9e 0xff3ffffff810c1fc

def z732 : W := mkw 0x06fe820800000010 0x0037f41040000000 0x87d8271c00000000 0x043ec138e0000000

def z733 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8ffffff1fffd99f 0xff47fffff8fffecc

def z734 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xffffef00fffe000f 0xffffff7807fff000

def z735 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x87dbe71c00000000 0x043edf38e0000000

def z736 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0x20dfcf3f00000000 0x3106fe79f8000000

def z737 : W := mkw 0x06ff8a28dbb40013 0x8037fc5146dda000 0xffdb2f3cfdc00001 0x77fed979e7ee0000

def z738 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x1fffc000fffe000e 0x38fffe0007fff000

def z739 : W := mkw 0x07b4349200000000 0x003da1a490000000 0xe7fc3fff02203ffe 0xff3fe1fff81101ff

def z740 : W := mkw 0x27fffefbf325205f 0x513ffff7df992902 0xf7ffffffe2262062 0x7fbfffffff113103

def z741 : W := mkw 0xa7b5fefb000a0abc 0x053daff7d8005055 0x2724ffff02263ff2 0x493927fff81131ff

def z742 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001dc1d991 0x0040000000ee0ecc

def z743 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x1f1c103fe1e1e1fb 0xa8f8e081ff0f0f0f

def z744 : W := mkw 0x27b57efb0000001c 0x013dabf7d8000000 0xe7fc3fff00000000 0x7f3fe1fff8000000

def z745 : W := mkw 0x27fffefb0890001c 0x813ffff7d8448000 0xefffffff1ffe000f 0xff7ffffff8fff000

def z746 : W := mkw 0x27fffefbd324001f 0x013ffff7de992000 0xf7ffffffe23e000e 0xffbfffffff11f000

def z747 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0xe027f8e3023fffff 0xff013fc71811ffff

def z748 : W := mkw 0x225fcb7bb601b41e 0x6112fe5bddb00da0 0x101fc03ffe01fe17 0xa080fe01fff00ff0

def z749 : W := mkw 0x804b4a6900020238 0x04025a5348001011 0xe0ffffff02262662 0x7f07fffff8113133

def z750 : W := mkw 0x02140000dbb40003 0x8010a00006dda000 0xdf3fc000fffe000f 0xbef9fe0007fff000

def z751 : W := mkw 0x20014ee90000001c 0x01000a7748000000 0x20002ffc00000000 0x4100017fe0000000

def z752 : W := mkw 0x07b4349200000000 0x003da1a490000000 0xe7f83fdc00000000 0x5f3fc1fee0000000

def z753 : W := mkw 0x004b0a2800080890 0x0002585140004044 0xe0db2f3c00001990 0x7706d979e00000cc

def z754 : W := mkw 0x080001044df8d981 0x88400008226fc6cc 0x18000000fdf9d99f 0x80c0000007efcecc

def z755 : W := mkw 0x04eb8a2800000010 0x00275c5140000000 0xe0fbef3c00000000 0x7707df79e0000000

def z756 : W := mkw 0x06fe8480dbb40403 0xa037f42406dda020 0xdfffc0c0fffe060f 0xbefffe0607fff030

def z757 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0x88db273c1dc1c001 0x2446d939e0ee0e00

def z758 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8df3fff1df9ffff 0xff46f9fff8efcfff

def z759 : W := mkw 0x084b09240cd8d980 0x884258492066c6cc 0xe8db08201dd9d99d 0xf746d84100eececc

def z760 : W := mkw 0x27fffefb49b4001d 0x813ffff7da4da000 0xffffffffe1fe000b 0xffffffffff0ff000

def z761 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xe8d82f3c1dc1d99d 0xf746c179e0ee0ecc

def z762 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8d8271c1dc1c009 0xa646c138e0ee0e00

def z763 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0xe8db2f3c1dc1c199 0xf746d979e0ee0e0c

def z764 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8dfef3c1dffd99d 0xf746ff79e0effecc

def z765 : W := mkw 0x25ebfefb0000001c 0x012f5ff7d8000000 0x60e7ffff00000000 0x7b073ffff8000000

def z766 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0xc8c000001dd9d99d 0x9646000000eececc

def z767 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xa0db2f1c00000000 0x1506d978e0000000

def z768 : W := mkw 0x004b4a6908900018 0x80025a5348448000 0xe8ffffff1ffe000f 0xff47fffff8fff000

def z769 : W := mkw 0x214b7efb0000001c 0x010a5bf7d8000000 0xa0d83fff00000000 0x4506c1fff8000000

def z770 : W := mkw 0x27fffefbfbb5201f 0xc13ffff7dfdda900 0xffffffffffffe01f 0xffffffffffffff00

def z771 : W := mkw 0x27fffefb2001201c 0x413ffff7d9000900 0xf7ffffffe0002002 0x7fbfffffff000100

def z772 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88db271c1dd9c005 0x1446d938e0eece00

def z773 : W := mkw 0x05ea368800000010 0x002f51b440000000 0x87d8271c00000000 0x043ec138e0000000

def z774 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001dd9c189 0x0040000000eece0c

def z775 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1fd9ff9f 0xf746d979e0fecffc

def z776 : W := mkw 0x0efe81040cd8d980 0x8877f4082066c6cc 0xcfffc0001dd9d99d 0xbe7ffe0000eececc

def z777 : W := mkw 0x235ffefb49b4001d 0x811afff7da4da000 0x281fffff01fe0008 0x6140fffff80ff000

def z778 : W := mkw 0xa7fffefbd32e0abf 0x053ffff7de997055 0xf7ffffffe23e3ffe 0xffbfffffff11f1ff

def z779 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f1c303fe1e1e1f9 0x64f8e181ff0f0f0f

def z780 : W := mkw 0x05eb3ea8b2012412 0x602f59f545900920 0xf7fb3ffce2002602 0x7fbfd9ffe7100130

def z781 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xff3c38ffe1e1e1fb 0xfff9e1c7ff0f0f0f

def z782 : W := mkw 0x80014a69000a0ab8 0x04000a5348005055 0x6027ffff023e3ffe 0xfb013ffff811f1ff

def z783 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x1fe7c000fffe000f 0x98ff3e0007fff000

def z784 : W := mkw 0x07feb492dbb40003 0x803ff5a496dda000 0xfffffffffffe000f 0xfffffffffffff000

def z785 : W := mkw 0x04a00000dbb40003 0x8025000006dda000 0xdfe7c000fffe000f 0xbeff3e0007fff000

def z786 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7db3fff00000000 0x773ed9fff8000000

def z787 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff00002012 0xff3ffffff8000100

def z788 : W := mkw 0x27fffefb2001201c 0x413ffff7d9000900 0xf7ffffffe001c001 0x7fbfffffff000e00

def z789 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7dc3fff00000000 0x6f3ee1fff8000000

def z790 : W := mkw 0x04eb0a2892000012 0x0027585144900000 0xf7fb2f3cfe000007 0xffbfd979e7f00000

def z791 : W := mkw 0x000001046561f541 0x70000008232b0faa 0x18000000e1e1fffb 0x80c00000070f0fff

def z792 : W := mkw 0x004b4a6900000018 0x00025a5348000000 0xe0dfef3f00000000 0x7706ff79f8000000

def z793 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xa0d82f3c00000000 0x4506c179e0000000

def z794 : W := mkw 0x27fffefb9200001e 0x013ffff7dc900000 0xf7fffffffe003e17 0xffbffffffff001f0

def z795 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0xe03ff8ff023e3ffe 0xff01ffc7f811f1ff

def z796 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0x80dfe73f00000000 0x2406ff39f8000000

def z797 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf3c303fe3e1e1ff 0xfef9e181ff1f0f0f

def z798 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8ffef3c1fffffff 0xff47ff79e0ffffff

def z799 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff00180188 0x7f3ffffff800c00c

def z800 : W := mkw 0x004a020800000010 0x0002501040000000 0xc0db271c00000000 0x3606d938e0000000

def z801 : W := mkw 0x27fffefbb201241e 0x613ffff7dd900920 0xf7ffffffe2003e16 0xffbfffffff1001f0

def z802 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xff1c38ffe1e1fffb 0xeff8e1c7ff0f0fff

def z803 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x682018c01fd9ff9f 0xdb4100c600fecffc

def z804 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c303fe3ffe1ff 0xeef8e181ff1fff0f

def z805 : W := mkw 0x87b57cf3f32b2eeb 0x743dabe79f995977 0x7727d8e3e23e3ffe 0xfbb93ec71f11f1ff

def z806 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8fbeffc1dd9d99d 0xf747df7fe0eececc

def z807 : W := mkw 0x225e821a00000014 0x0112f410d0000000 0x80d8271c00000000 0x0406c138e0000000

def z808 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db3f3f1dd9f9fd 0xf746d9f9f8eecfcf

def z809 : W := mkw 0x2100369a00000014 0x010801b4d0000000 0x0000373f00000000 0x400001b9f8000000

def z810 : W := mkw 0x26ffcee90000001c 0x0137fe7748000000 0xe7ffeffc00000000 0x7f3fff7fe0000000

def z811 : W := mkw 0x235ffefb0000001c 0x011afff7d8000000 0xe0dfffff00000000 0x7706fffff8000000

def z812 : W := mkw 0x000001046561f141 0x50000008232b0f8a 0x18000000fde1f9ff 0x80c0000007ef0fcf

def z813 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87dfe71c00000000 0x243eff38e0000000

def z814 : W := mkw 0x85a17de1b60bbeaa 0x642d0bef0db05df5 0x97c7e723fc3fc1e9 0x24be3f391fe1fe0f

def z815 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8db271c1dc1c001 0x3646d938e0ee0e00

def z816 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7d8273c00000000 0x663ec139e0000000

def z817 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7dfef3f00000000 0x773eff79f8000000

def z818 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8fbfffc1fdfff9f 0xff47dfffe0fefffc

def z819 : W := mkw 0x0a5e01046df9f9c1 0xd852f008236fcfce 0xdfdf0000fdf9f9ff 0xbefef80007efcfcf

def z820 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0xe0e7d8e31e3e3fff 0xff073ec718f1f1ff

def z821 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc023fffe01ef 0xbefffe011ffff00f

def z822 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xe7d82f1c00000000 0x573ec178e0000000

def z823 : W := mkw 0x0b5f3b3a6db9b8d1 0xd85af9d9d36dcdc6 0x37c71f03fc383866 0x19be38f81fe1c1c3

def z824 : W := mkw 0x080001040cd0d100 0x8840000820668688 0x080000001dc1c199 0x8040000000ee0e0c

def z825 : W := mkw 0x0100349200000000 0x000801a490000000 0x20003fff00000000 0x410001fff8000000

def z826 : W := mkw 0x00000104f761f543 0x7000000827bb0faa 0x18000000fdc1c001 0x00c0000007ee0e00

def z827 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8fb2ffc1fd9df9d 0xf747d97fe0fecefc

def z828 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7fbffff00000000 0x553fdffff8000000

def z829 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0xe0e7ffe3023e3ffe 0xff073fff1811f1ff

def z830 : W := mkw 0x0efe8104fffdfd83 0xe877f40827ffefec 0xdfffc000ffffff9f 0xbefffe0007fffffc

def z831 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0xe8db2f3c1dc1d815 0xf746d979e0ee0ec0

def z832 : W := mkw 0x21017efb0008089c 0x01080bf7d8004044 0x20003fff00001990 0x410001fff80000cc

def z833 : W := mkw 0xa6ffcefb000a0abc 0x0537fe77d8005055 0x60ffdfff023e3ffe 0xfb07fefff811f1ff

def z834 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0x88d8271c1dd9c189 0x0446c138e0eece0c

def z835 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7fcffff00000000 0x4d3fe7fff8000000

def z836 : W := mkw 0x880149650cdadba8 0x8c400a4b2866d6dd 0x280018e31dd9fffd 0xc14000c718eecfff

def z837 : W := mkw 0x884a434d0cd2d338 0x8c42521a68669699 0x88fcf7df1fe7e663 0x0c47e7bef8ff3f33

def z838 : W := mkw 0x05eb3ea800080890 0x002f59f540004044 0xe7fb3ffc02183f9e 0xff3fd9ffe010c1fc

def z839 : W := mkw 0x27b4f4d3f325204f 0x513da7a69f992902 0x1724d0c3e2262062 0x08b926861f113103

def z840 : W := mkw 0x08000104fff9fdc3 0xf840000827ffcfee 0x18000000fff9ffff 0x80c0000007ffcfff

def z841 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fdbc000fdde0001 0x04fede0007eef000

def z842 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf3ff03fe1e1e1fb 0xfef9ff81ff0f0f0f

def z843 : W := mkw 0x87b57cf3000a0aa8 0x043dabe798005055 0xe7ffffff023e3ffe 0xff3ffffff811f1ff

def z844 : W := mkw 0x8ceb4fe99e9a9eba 0xac675a7f4cf4d4f5 0x20e3cfc01e1e1e04 0x11071e7e00f0f0f0

def z845 : W := mkw 0x27b5fefb0000001c 0x013daff7d8000000 0x6727ffff00000000 0x7b393ffff8000000

def z846 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7c03fc0fc01fe15 0xd7be01fe07e00ff0

def z847 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1ff03fe1ffe1fb 0xeef8ff81ff0fff0f

def z848 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0xe0c03fff00000000 0x570601fff8000000

def z849 : W := mkw 0x0eb58b2cd76cd993 0x0875ac5966bb66cc 0x3724ef3ce227d992 0x49b92779e7113ecc

def z850 : W := mkw 0x27fffefb6121201d 0x413ffff7db090900 0xffffffffe1e1e01b 0xffffffffff0f0f00

def z851 : W := mkw 0x25a0369a00000014 0x012d01b4d0000000 0x87c0271c00000000 0x043e0138e0000000

def z852 : W := mkw 0x89017b7f244bfbf8 0x5c480bdbf9225fdf 0x20003fff0001fff0 0x410001fff8000fff

def z853 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027d8e3023e3ff6 0x59013ec71811f1ff

def z854 : W := mkw 0x000001040440d100 0x0000000820220688 0x88d8271c1dc1c001 0x0446c138e0ee0e00

def z855 : W := mkw 0x235ffefb0000001c 0x011afff7d8000000 0xe71fffff00000000 0x6f38fffff8000000

def z856 : W := mkw 0x27fffefb9200001e 0x013ffff7dc900000 0xf7fffffffc000001 0x7fbfffffffe00000

def z857 : W := mkw 0x204bca690000001c 0x01025e5348000000 0xe0dbef3c00000000 0x7706df79e0000000

def z858 : W := mkw 0x27fffefb9204001e 0x013ffff7dc902000 0xe7ffffff02060000 0x7f3ffffff8103000

def z859 : W := mkw 0x080001046df9f9c1 0xd8400008236fcfce 0x18000000fdd9d99d 0x80c0000007eececc

def z860 : W := mkw 0x27fffefb0890001c 0x813ffff7d8448000 0xefffffff01d80008 0x7f7ffffff80ec000

def z861 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8db2f3c1dffd9fd 0xf746d979e0effecf

def z862 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7dc373f002021fa 0xee3ee1b9f801010f

def z863 : W := mkw 0x27fffefbb201241e 0x613ffff7dd900920 0xf7ffffffe0000000 0x7fbfffffff000000

def z864 : W := mkw 0x86ffc861dbbe0aab 0x8437fe430eddf055 0xbfd818e3fdc03ff1 0x45fec0c71fee01ff

def z865 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff00183ffc 0xff3ffffff800c1ff

def z866 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7fff73f00000000 0x7e3fffb9f8000000

def z867 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc000ffde0005 0x3efffe0007fef000

def z868 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff02000006 0xff3ffffff8100000

def z869 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8d82f3c1dd9d99d 0xc546c179e0eececc

def z870 : W := mkw 0x27fffefbb201241e 0x613ffff7dd900920 0xf7fffffffe002607 0xffbffffffff00130

def z871 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001dd9d805 0x0040000000eecec0

def z872 : W := mkw 0xa7fffefb920a0abe 0x053ffff7dc905055 0xf7fffffffe3e3fff 0xffbffffffff1f1ff

def z873 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x60203fff02003e16 0xdb0101fff81001f0

def z874 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0d82f3c00000000 0x7706c179e0000000

def z875 : W := mkw 0x85eb7ee9000a0ab8 0x042f5bf748005055 0xe7ffffff023e3ffe 0xff3ffffff811f1ff

def z876 : W := mkw 0x07ff3eba00000010 0x003ff9f5d0000000 0xe7ff3fff00000000 0x7f3ff9fff8000000

def z877 : W := mkw 0x2fb4f5d70cd8d98c 0x897da7aeb866c6cc 0x0f24d0c31dd9d99d 0x8879268618eececc

def z878 : W := mkw 0x24ebcee99a94001e 0x81275e774cd4a000 0xe8fbeffc1fde000d 0xf747df7fe0fef000

def z879 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x20002fdc00000000 0x0100017ee0000000

def z880 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x60043fff00000000 0x6b0021fff8000000

def z881 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001fd9ff9f 0x8040000000fecffc

def z882 : W := mkw 0x804b4a69000a0ab8 0x04025a5348005055 0xe0db3fff00003ff0 0x7706d9fff80001ff

def z883 : W := mkw 0x084a01040cd8d980 0x884250082066c6cc 0x08c300001dd9d99d 0x9046180000eececc

def z884 : W := mkw 0x23157efb4120001d 0x0118abf7da090000 0xff1c3fffe1e0000b 0xeff8e1ffff0f0000

def z885 : W := mkw 0x035e321a00000010 0x001af190d0000000 0x87d8271c00000000 0x043ec138e0000000

def z886 : W := mkw 0x21017efbdbb4001f 0x81080bf7dedda000 0x38003ffffffe000f 0xc1c001fffffff000

def z887 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff00202062 0x7f3ffffff8010103

def z888 : W := mkw 0x235ffefb0000001c 0x011afff7d8000000 0x603fffff00000000 0x7b01fffff8000000

def z889 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff02003ff6 0xff3ffffff81001ff

def z890 : W := mkw 0x05eab016bad56142 0xd02f5580b5d6ab0a 0x00e3f03f1e1fe1f4 0x50071f81f8f0ff0f

def z891 : W := mkw 0x27fffefb6121205d 0x513ffff7db090902 0xf7ffffffe02021fa 0xffbfffffff01010f

def z892 : W := mkw 0x27feb69a61212055 0x513ff5b4d3090902 0x97dc371fe0202062 0x0cbee1b8ff010103

def z893 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff00260060 0x7f3ffffff8013003

def z894 : W := mkw 0x214a369a00000014 0x010a51b4d0000000 0x80d8271c00000000 0x0406c138e0000000

def z895 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff00001990 0x7f3ffffff80000cc

def z896 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0xe7003fff00000000 0x4f3801fff8000000

def z897 : W := mkw 0x27fffefb9200001e 0x013ffff7dc900000 0xf7ffffffe2000002 0x7fbfffffff100000

def z898 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c203fe1e1c1f9 0xe6f8e101ff0f0e0f

def z899 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffffff1dffd9fd 0xff47fffff8effecf

def z900 : W := mkw 0x06b40596d760d543 0x3035a02cb6bb06aa 0x28fc0fff1fe01fec 0x3147e07ff8ff00ff

def z901 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7c03fc0fc01fe13 0xcfbe01fe07e00ff0

def z902 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x1f3fc000fffe000f 0xa8f9fe0007fff000

def z903 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027d8c3023e3ffe 0x99013ec61811f1ff

def z904 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8d82f3c1dc1d999 0xe746c179e0ee0ecc

def z905 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7f83ffcfe01fe17 0xffbfc1ffe7f00ff0

def z906 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff023e27ea 0x7f3ffffff811f13f

def z907 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9ffbc000fffe000f 0x94ffde0007fff000

def z908 : W := mkw 0xa5a17efb000a0abc 0x052d0bf7d8005055 0xe7e03fff02003ff6 0xdf3f01fff81001ff

def z909 : W := mkw 0x24ebcefb0000001c 0x01275e77d8000000 0x20e3cfff00000000 0x11071e7ff8000000

def z910 : W := mkw 0x27fffefb0894001c 0x813ffff7d844a000 0xe7ffffff001e0000 0x7f3ffffff800f000

def z911 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xffffd8e3fffe3fff 0xfffffec71ffff1ff

def z912 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0x88d8271c1dd9d805 0x0446c138e0eecec0

def z913 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0fb3ffc00000000 0x7f07d9ffe0000000

def z914 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xffffffffffc00007 0xfffffffffffe0000

def z915 : W := mkw 0x0eff8924dffcd983 0x8877fc4926ffe6cc 0xffffc820ffffd99f 0xfffffe4107fffecc

def z916 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x88db271c1dd9c001 0x0446d938e0eece00

def z917 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8db2f3c1dd9d995 0x5546d979e0eececc

def z918 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8fbef3c1fdfd99d 0xf747df79e0fefecc

def z919 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xdfffe73ffffe000f 0xbeffff39fffff000

def z920 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0fb3ffc02003e16 0xff07d9ffe01001f0

def z921 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027d8e3023e3ffa 0x69013ec71811f1ff

def z922 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f1c203fe1e1e1fb 0xa4f8e101ff0f0f0f

def z923 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0xe8d82f1c1dd9d99d 0xd746c178e0eececc

def z924 : W := mkw 0x25ebfefb0000001c 0x012f5ff7d8000000 0xe0fbffff00000000 0x7707dffff8000000

def z925 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0xfff83fdcffc00007 0xdfffc1fee7fe0000

def z926 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1df9f9ff 0xf746d979e0efcfcf

def z927 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff023e3e1e 0xff3ffffff811f1f0

def z928 : W := mkw 0x080109240448d980 0x08400849202246cc 0x200008200001d990 0x4100004100000ecc

def z929 : W := mkw 0x27ffbebadbb40017 0x813ffdf5d6dda000 0xffffef3cfffe000f 0xffffff79e7fff000

def z930 : W := mkw 0x004a01040cd0d100 0x8002500820668688 0xe8db2f3c1dd9d99d 0xf746d979e0eececc

def z931 : W := mkw 0x035f3a3a49b00011 0x801af9d1d24d8000 0xffdf3f3ffdf8000f 0xfffef9f9ffefc000

def z932 : W := mkw 0x06ff8a2800080890 0x0037fc5140004044 0xe7ffef3c023e199e 0xff3fff79e011f0cc

def z933 : W := mkw 0x080001046569f9c1 0x58400008232b4fce 0x18000000e1e1f9fb 0x80c00000070f0fcf

def z934 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0db2f3c0018000c 0xf706d979e000c000

def z935 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffe03cfffe000f 0xfeffff01e7fff000

def z936 : W := mkw 0x26ffcefbdbb4001f 0x8137fe77dedda000 0x28ffcfff1ffe000c 0x3147fe7ff8fff000

def z937 : W := mkw 0x025f0a2841200011 0x0012f85142090000 0xffdf2f3ce1e0000b 0xfffef979e70f0000

def z938 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x60203fff00000000 0x5b0101fff8000000

def z939 : W := mkw 0xa7feb69a000a0ab4 0x053ff5b4d0005055 0x87d8271c023e3ffe 0x843ec138e011f1ff

def z940 : W := mkw 0x25eab69a00000014 0x012f55b4d0000000 0x00c0271c00000000 0x00060138e0000000

def z941 : W := mkw 0xa7fffefbb203263e 0x653ffff7dd901931 0xf7ffffffe2262662 0x7fbfffffff113133

def z942 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffefdc00000000 0x3f3fff7ee0000000

def z943 : W := mkw 0x23157efb0000001c 0x0118abf7d8000000 0xe73fffff00000000 0x7f39fffff8000000

def z944 : W := mkw 0x0314349200000000 0x0018a1a490000000 0xe71c3fff00000000 0x6f38e1fff8000000

def z945 : W := mkw 0x000001042441f540 0x7000000821220faa 0x000000000001fff0 0x0000000000000fff

def z946 : W := mkw 0x000109240448d980 0x00000849202246cc 0xe8db2f3c1dd9d99d 0xf746d979e0eececc

def z947 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c303fe1c1e1f1 0x6ef8e181ff0e0f0f

def z948 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c303fe3e1ffff 0xeef8e181ff1f0fff

def z949 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f1c303fe1e1e1f3 0x4cf8e181ff0f0f0f

def z950 : W := mkw 0x27fffefb4120001d 0x013ffff7da090000 0xffffffffe3fe000f 0xffffffffff1ff000

def z951 : W := mkw 0x080001049edcd982 0x8840000824f6e6cc 0x080000001fdfd99d 0x8040000000fefecc

def z952 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8d8271c1dc1c005 0x9646c138e0ee0e00

def z953 : W := mkw 0x025e000049b00001 0x8012f000024d8000 0xdfffc000fffe000f 0xbefffe0007fff000

def z954 : W := mkw 0x83157877616b6be9 0x5418abc3bb0b5b5f 0xbf3be8dce3dfde05 0x15f9df46e71efef0

def z955 : W := mkw 0xa5ebfefb000a0abc 0x052f5ff7d8005055 0x60e7ffff023e3ffe 0xfb073ffff811f1ff

def z956 : W := mkw 0x0efe8104fffdf9c3 0xd877f40827ffefce 0xdfffc000fffff9ff 0xbefffe0007ffffcf

def z957 : W := mkw 0x080109240cd8d980 0x884008492066c6cc 0x280008201dd9d99d 0xc140004100eececc

def z958 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1dc1d991 0x7746d979e0ee0ecc

def z959 : W := mkw 0x27fffefb9a94001e 0x813ffff7dcd4a000 0xe7ffffff1c000000 0x7f3ffffff8e00000

def z960 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7ffe71c023e000e 0xbe3fff38e011f000

def z961 : W := mkw 0x27feb69a20012014 0x413ff5b4d1000900 0x97d8271ce001c001 0x04bec138e7000e00

def z962 : W := mkw 0x25ebfefb9a94001e 0x812f5ff7dcd4a000 0x20e3ffff1e1e0004 0x51071ffff8f0f000

def z963 : W := mkw 0x00000104b641f502 0x6000000825b20fa8 0x18000000ffc1ff9f 0x80c0000007fe0ffc

def z964 : W := mkw 0x025e800049b40001 0x8012f400024da000 0xdfdfc000fdfe000f 0xbefefe0007eff000

def z965 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8dfff3f1dfff9ff 0xff46fff9f8efffcf

def z966 : W := mkw 0xa25fca7b000a0abc 0x0512fe53d8005055 0xe0dfef3f003e19fc 0xf706ff79f801f0cf

def z967 : W := mkw 0x00010a2800000010 0x0000085140000000 0x60032f3c00000000 0x73001979e0000000

def z968 : W := mkw 0x07feb596fff5f543 0xf03ff5acb7ffafaa 0x9fd8271cfdc1c001 0x04fec138e7ee0e00

def z969 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8df3f3f1dd9d99d 0xff46f9f9f8eececc

def z970 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0db2f3c00001814 0xf706d979e00000c0

def z971 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xa8fbefdc1fdfde05 0x1547df7ee0fefef0

def z972 : W := mkw 0x06fe8208dbb40013 0x8037f41046dda000 0xdfffe71cfffe000f 0xbeffff38e7fff000

def z973 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff00001e00 0x7f3ffffff80000f0

def z974 : W := mkw 0xa3157efb000a0abc 0x0518abf7d8005055 0xe71c3fff00203ffa 0xef38e1fff80101ff

def z975 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffefff1fffdffd 0xf747ff7ff8fffeff

def z976 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffffe3e1f 0xfffffffffffff1f0

def z977 : W := mkw 0x04a0010096009002 0x0025000804b00480 0xf7e03fc0fe01fe17 0xdfbf01fe07f00ff0

def z978 : W := mkw 0x01013ea800000010 0x000809f540000000 0x20003ffc00000000 0x410001ffe0000000

def z979 : W := mkw 0xa3157efb000a0abc 0x0518abf7d8005055 0xe73fffff023e3ffe 0xff39fffff811f1ff

def z980 : W := mkw 0x27fffefbb201241e 0x613ffff7dd900920 0xf7ffffffe201e613 0xffbfffffff100f30

def z981 : W := mkw 0x06ffca6900000018 0x0037fe5348000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z982 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf3c30ffe3e1e7fb 0xeef9e187ff1f0f3f

def z983 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x0027d0e3023e3ffe 0xa8013e871811f1ff

def z984 : W := mkw 0x07b43492d3200003 0x003da1a496990000 0xfffc3fffffe0000f 0xffffe1ffffff0000

def z985 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff003e0008 0x7f3ffffff801f000

def z986 : W := mkw 0x27fffefbd320001f 0x013ffff7de990000 0xffffffffffe0000f 0xffffffffffff0000

def z987 : W := mkw 0x035eb5806db5b401 0xe01af5ac036dada0 0x281fffc001fffe18 0x6140fffe000ffff0

def z988 : W := mkw 0x084a01040cd8d980 0x884250082066c6cc 0x081b00001dd9d99d 0xa040d80000eececc

def z989 : W := mkw 0x27feb69a9a940016 0x813ff5b4d4d4a000 0x87d8271c1c000000 0x043ec138e0e00000

def z990 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0db2f3c0001c011 0xf706d979e0000e00

def z991 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff023e21fe 0xff3ffffff811f10f

def z992 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f1c1dd9d815 0xd746d978e0eecec0

def z993 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0xc7fcf7ff00000000 0x6e3fe7bff8000000

def z994 : W := mkw 0x06b48000dbb40003 0x8035a40006dda000 0x5f27c000fffe000f 0xbaf93e0007fff000

def z995 : W := mkw 0x27fffefb2001201c 0x413ffff7d9000900 0xe7ffffff0001e010 0x7f3ffffff8000f00

def z996 : W := mkw 0x27fffefb49b4001d 0x813ffff7da4da000 0xefffffff1dfe000d 0xff7ffffff8eff000

def z997 : W := mkw 0x004b4a6900000018 0x00025a5348000000 0xe0db3fff00000000 0x7706d9fff8000000

def z998 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001df9f9ff 0x8040000000efcfcf

def z999 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0xc81800001dd9d99d 0xa640c00000eececc

def z1000 : W := mkw 0x27b5fefb0000001c 0x013daff7d8000000 0xe73cffff00000000 0x6f39e7fff8000000

def z1001 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x60043fff002021fa 0xeb0021fff801010f

def z1002 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff00000198 0xff3ffffff800000c

def z1003 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x680008001dd9d99d 0xd340004000eececc

def z1004 : W := mkw 0x07b4349200000000 0x003da1a490000000 0xc7dc373f00000000 0x6e3ee1b9f8000000

def z1005 : W := mkw 0x27feb69a08900014 0x813ff5b4d0448000 0xcfdb271c1dd8000d 0xb67ed938e0eec000

def z1006 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87dc371f00000000 0x0c3ee1b8f8000000

def z1007 : W := mkw 0x05ea368800000010 0x002f51b440000000 0xe7f83fdc00000000 0x5f3fc1fee0000000

def z1008 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff000001e0 0x7f3ffffff800000f

def z1009 : W := mkw 0x27b4b69a00000014 0x013da5b4d0000000 0x0700271c00000000 0x00380138e0000000

def z1010 : W := mkw 0xa4ebcee9000a0abc 0x05275e7748005055 0xe0ffffff023e3ffe 0xff07fffff811f1ff

def z1011 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff003e3ff8 0x7f3ffffff801f1ff

def z1012 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0xe7fcffdf00000000 0x5f3fe7fef8000000

def z1013 : W := mkw 0x880041450cdadba8 0x8c40020a2866d6dd 0x0824d0c31fffffff 0x8841268618ffffff

def z1014 : W := mkw 0x07feb49200000000 0x003ff5a490000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1015 : W := mkw 0x08000104dffcd983 0x8840000826ffe6cc 0x18000000fdd9d99d 0x80c0000007eececc

def z1016 : W := mkw 0x00000104f761f543 0x7000000827bb0faa 0x18000000fde1e1fb 0x80c0000007ef0f0f

def z1017 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8db2f1c1dd9d99d 0x9546d978e0eececc

def z1018 : W := mkw 0x27feb69a92000016 0x013ff5b4d4900000 0x97d8271cfc000001 0x04bec138e7e00000

def z1019 : W := mkw 0x27feb69ab2012416 0x613ff5b4d5900920 0x97d8271ce0000000 0x04bec138e7000000

def z1020 : W := mkw 0x035e321a00000010 0x001af190d0000000 0xc7dc373f00000000 0x6e3ee1b9f8000000

def z1021 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e7ffc0fe01fe17 0xffbf3ffe07f00ff0

def z1022 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0ffef3c00000000 0x7f07ff79e0000000

def z1023 : W := mkw 0x00010a2800080890 0x0000085140004044 0x20002f3c00001990 0x41000179e00000cc

def z1024 : W := mkw 0x004b4a6900000018 0x00025a5348000000 0xe0fbeffc00000000 0x7707df7fe0000000

def z1025 : W := mkw 0x204b4a7b0000001c 0x01025a53d8000000 0xe0db2f3f00000000 0x7706d979f8000000

def z1026 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8dfef3f1fffffff 0xf746ff79f8ffffff

def z1027 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffdfe0009 0x7fffffffffeff000

def z1028 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0x88dfe73f1dffc1e9 0x2446ff39f8effe0f

def z1029 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc000fffe21ff 0xbefffe0007fff10f

def z1030 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0xe0ffffff00000000 0x7f07fffff8000000

def z1031 : W := mkw 0x835f7a7b000a0ab8 0x041afbd3d8005055 0xe7ffffff023e3ffe 0xff3ffffff811f1ff

def z1032 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0x87dce71f00000000 0x043ee738f8000000

def z1033 : W := mkw 0x08000104b649fd82 0x6840000825b24fec 0x10000000fe01ff97 0x8080000007f00ffc

def z1034 : W := mkw 0x804b0a28000a0ab0 0x0402585140005055 0xe0db2f3c023e3ffe 0xf706d979e011f1ff

def z1035 : W := mkw 0x27fffefb49b0001d 0x813ffff7da4d8000 0xfffffffffdf8000f 0xffffffffffefc000

def z1036 : W := mkw 0x27fffefbd324001f 0x013ffff7de992000 0xf7fffffffe260007 0xffbffffffff13000

def z1037 : W := mkw 0x27fffefb49b4001d 0x813ffff7da4da000 0xefffffff03fe000e 0xff7ffffff81ff000

def z1038 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff02263ff2 0x7f3ffffff81131ff

def z1039 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8db3fff1dd9d99d 0xf746d9fff8eececc

def z1040 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff02203ffe 0xff3ffffff81101ff

def z1041 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xffffffffffde0005 0x7ffffffffffef000

def z1042 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xbffbefdcffde0005 0x15ffdf7ee7fef000

def z1043 : W := mkw 0x235ffefb0000001c 0x011afff7d8000000 0x001fe73f00000000 0x2000ff39f8000000

def z1044 : W := mkw 0x025e8000dbb40003 0x8012f40006dda000 0xdf1fc000fffe000f 0xaef8fe0007fff000

def z1045 : W := mkw 0xa5ebfefb000a0abc 0x052f5ff7d8005055 0x20e3ffff021e3ff4 0x51071ffff810f1ff

def z1046 : W := mkw 0x000001040440d100 0x0000000820220688 0x080000001dc1d99d 0x8040000000ee0ecc

def z1047 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7ffefff00000000 0x353fff7ff8000000

def z1048 : W := mkw 0x07ffba3adbb40013 0x803ffdd1d6dda000 0xffffff3ffffe000f 0xfffffff9fffff000

def z1049 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff023e3e66 0x7f3ffffff811f1f3

def z1050 : W := mkw 0x235eb69a00000014 0x011af5b4d0000000 0x0018271c00000000 0x0000c138e0000000

def z1051 : W := mkw 0x025f8a2849b40011 0x8012fc51424da000 0xe8dfef3c01fe0008 0x7746ff79e00ff000

def z1052 : W := mkw 0x0314349661616141 0x5018a1a4b30b0b0a 0xff1c3fffe1e1e1fb 0xeff8e1ffff0f0f0f

def z1053 : W := mkw 0x035f3a3a00000010 0x001af9d1d0000000 0xe7db2f3c00000000 0x773ed979e0000000

def z1054 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xa7d83fff00003ff0 0x453ec1fff80001ff

def z1055 : W := mkw 0x26ffcefb0000001c 0x0137fe77d8000000 0xe0ffefff00000000 0x7707ff7ff8000000

def z1056 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xa7f82fdc00000000 0x153fc17ee0000000

def z1057 : W := mkw 0x214b7efb0000001c 0x010a5bf7d8000000 0x20c33fff00000000 0x510619fff8000000

def z1058 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0df3f3f00000000 0x7f06f9f9f8000000

def z1059 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0xf727d8e3e23e3fff 0xffb93ec71f11f1ff

def z1060 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7e03fc0fe01fe15 0x55bf01fe07f00ff0

def z1061 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x080300001dd9d99d 0x8040180000eececc

def z1062 : W := mkw 0x07b4349200000000 0x003da1a490000000 0x87d8271c00000000 0x043ec138e0000000

def z1063 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8db2f3f1dd9d9fd 0xf746d979f8eececf

def z1064 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffd0c0fffe260f 0xbefffe8607fff130

def z1065 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x37e01fc0fe01fe17 0x99bf00fe07f00ff0

def z1066 : W := mkw 0x0100301620416140 0x50080180b1020b0a 0xdf18303fe1c1e1fb 0xeef8c181ff0e0f0f

def z1067 : W := mkw 0x04ea00009a900002 0x8027500004d48000 0xdfffc000fffe000f 0xbefffe0007fff000

def z1068 : W := mkw 0x21017efb2001201c 0x41080bf7d9000900 0x20003fff0001e010 0x410001fff8000f00

def z1069 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1f303fe1f9e1ff 0xfef8f981ff0fcf0f

def z1070 : W := mkw 0x05eb7ee900000018 0x002f5bf748000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1071 : W := mkw 0x81017df7244bffe8 0x74080befb9225fff 0x20003fff0001fff0 0x410001fff8000fff

def z1072 : W := mkw 0xa7fffefbdbbe0abf 0x853ffff7deddf055 0xfffffffffffe1e0f 0xfffffffffffff0f0

def z1073 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xe8d82f1c1dc1c001 0x5746c178e0ee0e00

def z1074 : W := mkw 0x025f0a2800000010 0x0012f85140000000 0xe7df2f3c00000000 0x7f3ef979e0000000

def z1075 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdfdc303ffde1e1ff 0xfefee181ffef0f0f

def z1076 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8fb3ffc1fffffff 0xff47d9ffe0ffffff

def z1077 : W := mkw 0x084b0a2808980890 0x884258514044c044 0xe0db2f3c00180000 0x7706d979e000c000

def z1078 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8df2f3c1df9d99f 0xff46f979e0efcecc

def z1079 : W := mkw 0x0000020800000010 0x0000001040000000 0x0000271c00000000 0x00000138e0000000

def z1080 : W := mkw 0x004b0a2808900010 0x8002585140448000 0xe8db2f3c1dc00001 0x7746d979e0ee0000

def z1081 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0xa0fbefdc00000000 0x1507df7ee0000000

def z1082 : W := mkw 0xa7fffefb200b2abc 0x453ffff7d9005955 0xf7ffffffe23fffff 0xffbfffffff11ffff

def z1083 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x20003fff00001e00 0x410001fff80000f0

def z1084 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x0000273f00000000 0x00000139f8000000

def z1085 : W := mkw 0x00014a6900000018 0x00000a5348000000 0x20003fff00000000 0x410001fff8000000

def z1086 : W := mkw 0xa7fffefb9a9e0abe 0x853ffff7dcd4f055 0xe7ffffff1e1e1e04 0x7f3ffffff8f0f0f0

def z1087 : W := mkw 0x880149656dfbfbe9 0xdc400a4b2b6fdfdf 0x7827d8e3ffffffff 0xfbc13ec71fffffff

def z1088 : W := mkw 0x0cea0104bed9fd82 0xe867500825f6cfec 0xdffb0000ffd9ff9f 0xbeffd80007fecffc

def z1089 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0xa8d82f3c1dc1c001 0x4546c179e0ee0e00

def z1090 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x2023ffff021e1e04 0x51011ffff810f0f0

def z1091 : W := mkw 0x21013eba00000014 0x010809f5d0000000 0x20002f3c00000000 0x41000179e0000000

def z1092 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xc7dff73f00000000 0x6e3effb9f8000000

def z1093 : W := mkw 0x05a13ea800000010 0x002d09f540000000 0xe7e03ffc00000000 0x5f3f01ffe0000000

def z1094 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0xe8db2f3c1dd9c00d 0xf746d979e0eece00

def z1095 : W := mkw 0x2314369a00000014 0x0118a1b4d0000000 0x8718271c00000000 0x0438c138e0000000

def z1096 : W := mkw 0x880001040cdadba0 0x8c4000082066d6dd 0x080000001fdfdf9d 0x8040000000fefefc

def z1097 : W := mkw 0x080109240448d980 0x08400849202246cc 0x600308200019d99c 0xf30018410000cecc

def z1098 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x28db2f3c1dd9d99c 0x7146d979e0eececc

def z1099 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff002001e8 0x7f3ffffff801000f

def z1100 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7d8371c00000000 0x4e3ec1b8e0000000

def z1101 : W := mkw 0x24ebceed6161615d 0x51275e776b0b0b0a 0x38e3cfc0e1e1e1fb 0x91c71e7e070f0f0f

def z1102 : W := mkw 0x080109240cd8d980 0x884008492066c6cc 0x280308001dd9d99d 0x9140184000eececc

def z1103 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xbfd83ffffdc00001 0x45fec1ffffee0000

def z1104 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xe8f83fdc1fc1fe17 0xdf47c1fee0fe0ff0

def z1105 : W := mkw 0x880001046dfbfbe1 0xdc400008236fdfdf 0x18000000ffffffff 0x80c0000007ffffff

def z1106 : W := mkw 0x00014a6900000018 0x00000a5348000000 0x6027ffff00000000 0x7b013ffff8000000

def z1107 : W := mkw 0xa35ffefb000a0abc 0x051afff7d8005055 0x201fffff003e3ff8 0x6100fffff801f1ff

def z1108 : W := mkw 0x27feb69a49b40015 0x813ff5b4d24da000 0x8fdfe71c01fe0008 0x247eff38e00ff000

def z1109 : W := mkw 0xa7fffefbdbbe0abf 0x853ffff7deddf055 0xfffffffffffe01ef 0xfffffffffffff00f

def z1110 : W := mkw 0x8efe8104dffedba3 0x8c77f40826fff6dd 0xdfffc000ffffffff 0xbefffe0007ffffff

def z1111 : W := mkw 0x05a0348461616141 0x502d01a4230b0b0a 0xffe03fc0e1e1e1fb 0xdfff01fe070f0f0f

def z1112 : W := mkw 0x27fffefb4120001d 0x013ffff7da090000 0xffffffffe1e021fb 0xffffffffff0f010f

def z1113 : W := mkw 0x880149650cdadba8 0x8c400a4b2866d6dd 0x2823c8c01fdfdf9d 0x91411e4600fefefc

def z1114 : W := mkw 0x27fffefb6121205d 0x513ffff7db090902 0xf7ffffffe0000000 0x7fbfffffff000000

def z1115 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0xe7fb3ffc00000000 0x7f3fd9ffe0000000

def z1116 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8d8271c1dc1c011 0xc646c138e0ee0e00

def z1117 : W := mkw 0x26fe821adbb40017 0x8137f410d6dda000 0xdfffc01cfffe000f 0xbefffe00e7fff000

def z1118 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x20003fff000001e0 0x410001fff800000f

def z1119 : W := mkw 0x06fe8208dbb40013 0x8037f41046dda000 0x9fd8271cfdc00001 0x04fec138e7ee0000

def z1120 : W := mkw 0x0b1431166df9f9c1 0xd858a188b36fcfce 0x1f041003fdf9f9ff 0x88f820801fefcfcf

def z1121 : W := mkw 0x25ebfefb0000001c 0x012f5ff7d8000000 0x20c03fff00000000 0x410601fff8000000

def z1122 : W := mkw 0x04ea8000dbb40003 0x8027540006dda000 0xdfe3c000fffe000f 0x9eff1e0007fff000

def z1123 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x88d8273c1dc1c181 0x0446c139e0ee0e0c

def z1124 : W := mkw 0x080001044dfcd981 0x88400008226fe6cc 0x080000001dffd99d 0x8040000000effecc

def z1125 : W := mkw 0x08000104bed9fd82 0xe840000825f6cfec 0x18000000fdd9d99d 0x80c0000007eececc

def z1126 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7dfffff00000000 0x653efffff8000000

def z1127 : W := mkw 0x80004041000a0aa8 0x0400020208005055 0x4027d0c3023e3ffe 0xba013e861811f1ff

def z1128 : W := mkw 0x27fffefb9200001e 0x013ffff7dc900000 0xe7ffffff1e000004 0x7f3ffffff8f00000

def z1129 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff023e1e0e 0xff3ffffff811f0f0

def z1130 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0x87d837df00000000 0x043ec1bef8000000

def z1131 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf18303fe1c1e1f9 0xe6f8c181ff0e0f0f

def z1132 : W := mkw 0x080001046df1f141 0xd8400008236f8f8a 0x18000000fdc1c001 0x00c0000007ee0e00

def z1133 : W := mkw 0xa7fffefb49be0abd 0x853ffff7da4df055 0xefffffff03fe3ffe 0xff7ffffff81ff1ff

def z1134 : W := mkw 0x05eb3ea89a900012 0x802f59f544d48000 0xfffb3ffcffd8000f 0xffffd9ffe7fec000

def z1135 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0x20fbcffc00000000 0x3107de7fe0000000

def z1136 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f18303fe1e1e1fb 0xc4f8c181ff0f0f0f

def z1137 : W := mkw 0x884a01040cdadba0 0x8c4250082066d6dd 0xc8ffc0001fffffff 0xbe47fe0000ffffff

def z1138 : W := mkw 0x084a01040cd8d980 0x884250082066c6cc 0x88d800001dd9d99d 0x8446c00000eececc

def z1139 : W := mkw 0x0ca001049ed8d982 0x8865000824f6c6cc 0xdfe00000ffd9d99f 0x9eff000007fececc

def z1140 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xc7ffe73f00000000 0x3e3fff39f8000000

def z1141 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xffffc800fffe181f 0xfffffe4007fff0c0

def z1142 : W := mkw 0x23157efb0000001c 0x0118abf7d8000000 0x27043fff00000000 0x493821fff8000000

def z1143 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xa7d83fdc00000000 0x453ec1fee0000000

def z1144 : W := mkw 0x004b0a2800000010 0x0002585140000000 0x20c32f3c00000000 0x51061979e0000000

def z1145 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88d8271c1dc1c199 0x8446c138e0ee0e0c

def z1146 : W := mkw 0x0314301200000000 0x0018a18090000000 0xe7dc3f3f00000000 0x7f3ee1f9f8000000

def z1147 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xffdb2f3cfdd9d99f 0xfffed979e7eececc

def z1148 : W := mkw 0x004b0a2800000010 0x0002585140000000 0x20db0f3c00000000 0x3106d879e0000000

def z1149 : W := mkw 0x27fffefb0890001c 0x813ffff7d8448000 0xefffffff1dc00001 0x7f7ffffff8ee0000

def z1150 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0xe7ffef3c00000000 0x7f3fff79e0000000

def z1151 : W := mkw 0x27fffefbd324001f 0x013ffff7de992000 0xf7ffffffe0000000 0x7fbfffffff000000

def z1152 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7f8271c00000000 0x1e3fc138e0000000

def z1153 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8ffe71c1fffc00f 0xbe47ff38e0fffe00

def z1154 : W := mkw 0x07ffbea8dbb40013 0x803ffdf546dda000 0xfffffffcfffe000f 0xffffffffe7fff000

def z1155 : W := mkw 0x27b4f4d3f325240f 0x613da7a69f992920 0x1724d0c3e2262602 0x08b926861f113130

def z1156 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0xe0ffffff00000000 0x7f07fffff8000000

def z1157 : W := mkw 0x23157efb6121205d 0x5118abf7db090902 0x37043fffe0202062 0x49b821ffff010103

def z1158 : W := mkw 0x00010a2800080890 0x0000085140004044 0x60032f3c0018199c 0xf3001979e000c0cc

def z1159 : W := mkw 0x00000104fff5f543 0xf000000827ffafaa 0x18000000ffffffff 0x80c0000007ffffff

def z1160 : W := mkw 0x04eb8a289a940012 0x80275c5144d4a000 0xe0fbef3c1e1e0004 0x7707df79e0f0f000

def z1161 : W := mkw 0x004a020800000010 0x0002501040000000 0xe0d82f1c00000000 0x5706c178e0000000

def z1162 : W := mkw 0x06fe8012dbb40043 0x9037f40096dda002 0xdfffc003fffe006f 0xbefffe001ffff003

def z1163 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x20ffffff00000000 0x7107fffff8000000

def z1164 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001dd8198c 0x0040000000eec0cc

def z1165 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xa8d82f1c1dc1d805 0x1546c178e0ee0ec0

def z1166 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffffe21ff 0xfffffffffffff10f

def z1167 : W := mkw 0x08000104dff4d103 0x8840000826ffa688 0x18000000fdc1c001 0x00c0000007ee0e00

def z1168 : W := mkw 0x00000104f761f543 0x7000000827bb0faa 0x782418e3ffe1ffff 0xfbc120c71fff0fff

def z1169 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdffbc000ffde0007 0x9effde0007fef000

def z1170 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88d8273c1dc1c191 0x4446c139e0ee0e0c

def z1171 : W := mkw 0x04eb0a2800000010 0x0027585140000000 0xe7fb2f3c00000000 0x7f3fd979e0000000

def z1172 : W := mkw 0x27fffefbfbb5241f 0xe13ffff7dfdda920 0xfffffffffffe260f 0xfffffffffffff130

def z1173 : W := mkw 0x084b0b2c0cd0d110 0x8842585960668688 0xa8db2f1c1dc1c001 0x1546d978e0ee0e00

def z1174 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x1f1c303fe1e1e1fa 0x68f8e181ff0f0f0f

def z1175 : W := mkw 0x27feb69a41200015 0x013ff5b4d2090000 0xdfdc271ce1e0000b 0xaefee138e70f0000

def z1176 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff003839fe 0xff3ffffff801c1cf

def z1177 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c303fe1e1c1e9 0x6ef8e181ff0f0e0f

def z1178 : W := mkw 0x25a17efb0000001c 0x012d0bf7d8000000 0xa7c03fff00000000 0x453e01fff8000000

def z1179 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e7ffe3fe3fffff 0xffbf3fff1ff1ffff

def z1180 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc020fffe019f 0xfefffe0107fff00c

def z1181 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff023e01ee 0xff3ffffff811f00f

def z1182 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff00203ffa 0xff3ffffff80101ff

def z1183 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x0800000001d9d998 0x00400000000ececc

def z1184 : W := mkw 0x0214001641604141 0x1010a000b20b020a 0xdf1c203fe1e1c1fb 0xeef8e101ff0f0e0f

def z1185 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf1c203fe1e1c1eb 0xaef8e101ff0f0e0f

def z1186 : W := mkw 0x06ff8a28d3240013 0x0037fc5146992000 0xf7ffef3ce2260002 0x7fbfff79e7113000

def z1187 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0x9fdfe73ffdfe0009 0x24feff39ffeff000

def z1188 : W := mkw 0x204b4ee90000001c 0x01025a7748000000 0xe0db2ffc00000000 0x7706d97fe0000000

def z1189 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfdfc000fdfe000d 0xb6fefe0007eff000

def z1190 : W := mkw 0x26ffcefb0000001c 0x0137fe77d8000000 0x20fbcfdc00000000 0x1107de7ee0000000

def z1191 : W := mkw 0x25a17efb9200001e 0x012d0bf7dc900000 0xf7e03ffffe000007 0xdfbf01fffff00000

def z1192 : W := mkw 0x00010a2800000010 0x0000085140000000 0xe0c02f3c00000000 0x57060179e0000000

def z1193 : W := mkw 0x225fca7b49b4001d 0x8112fe53da4da000 0xe8dfef3f1dfe000d 0xf746ff79f8eff000

def z1194 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8db2f3c1dd9fffd 0xf746d979e0eecfff

def z1195 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7e02fc0fe01fe17 0x95bf017e07f00ff0

def z1196 : W := mkw 0x000001040440d100 0x0000000820220688 0xe8fc3fff1fe1ffff 0xff47e1fff8ff0fff

def z1197 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0xdfdc373ffde0000b 0xeefee1b9ffef0000

def z1198 : W := mkw 0x27b4f6db0000001c 0x013da7b6d8000000 0x0724f7df00000000 0x083927bef8000000

def z1199 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffe000ffffc01f 0xfeffff0007fffe00

def z1200 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f1c303fe1e1e1eb 0x2cf8e181ff0f0f0f

def z1201 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1fffd99f 0xf746d979e0fffecc

def z1202 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff00003e10 0x7f3ffffff80001f0

def z1203 : W := mkw 0x8a5f4a7f49fa4bf9 0x9c52fa53fa4fd25f 0x081fc03f01fe01e8 0x2040fe01f80ff00f

def z1204 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfdfc000fdfe000b 0xaefefe0007eff000

def z1205 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xffffffffe3fe000a 0x7fffffffff1ff000

def z1206 : W := mkw 0x0efe8104dff4d103 0x8877f40826ffa688 0xdfffc000ffffc00f 0xbefffe0007fffe00

def z1207 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffef3f1fffd9ff 0xff47ff79f8fffecf

def z1208 : W := mkw 0x04a0058096009402 0x2025002c04b004a0 0xf7e02fc0fe01de17 0xdfbf017e07f00ef0

def z1209 : W := mkw 0x25a17efb0000001c 0x012d0bf7d8000000 0x20e03fff00000000 0x510701fff8000000

def z1210 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x080000001fffd99f 0x8040000000fffecc

def z1211 : W := mkw 0x88000104bedbffa2 0xec40000825f6dffd 0x18000000ffffffff 0x80c0000007ffffff

def z1212 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db3f3c1dd9f99f 0xff46d9f9e0eecfcc

def z1213 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8d82f3c1dc1d995 0xd746c179e0ee0ecc

def z1214 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e43fc0fe21fe1f 0xffbf21fe07f10ff0

def z1215 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x20003fff023e3ffe 0xc10001fff811f1ff

def z1216 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x273fffff00000000 0x6939fffff8000000

def z1217 : W := mkw 0x084b8b2c0cdcd990 0x88425c596066e6cc 0xe8dbef3c1ddfd99d 0xf746df79e0eefecc

def z1218 : W := mkw 0x080109246df9f9c1 0xd8400849236fcfce 0x78071823fdf9f9ff 0xfbc038c11fefcfcf

def z1219 : W := mkw 0x0100300420416100 0x4008018021020b08 0xdf1c303fe1e1e1fb 0xeef8e181ff0f0f0f

def z1220 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88d8271c1dc1d815 0x8446c138e0ee0ec0

def z1221 : W := mkw 0x05a0349200000000 0x002d01a490000000 0xe7e03fff00000000 0x5f3f01fff8000000

def z1222 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff021e0004 0x7f3ffffff810f000

def z1223 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffd003fffe206f 0xbefffe801ffff103

def z1224 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8fb2f3c1fd9d99f 0xff47d979e0fececc

def z1225 : W := mkw 0x04ea80009a940002 0x8027540004d4a000 0xdffbc000ffde000f 0xbeffde0007fef000

def z1226 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x60033fff00000000 0x730019fff8000000

def z1227 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7e03fc0fe01fe07 0x1dbf01fe07f00ff0

def z1228 : W := mkw 0x884b0b2c0cdadbb0 0x8c4258596066d6dd 0xe8db2f3c1fdfdf9d 0xf746d979e0fefefc

def z1229 : W := mkw 0xa7fffefb089a0abc 0x853ffff7d844d055 0xefffffff1ffe3fff 0xff7ffffff8fff1ff

def z1230 : W := mkw 0x27fffefb6121205d 0x513ffff7db090902 0xffffffffe1e0206b 0xffffffffff0f0103

def z1231 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0x88d8271c1dc1d991 0x0446c138e0ee0ecc

def z1232 : W := mkw 0xa7fffefb612b2afd 0x553ffff7db095957 0xf7ffffffe23e3ffe 0xffbfffffff11f1ff

def z1233 : W := mkw 0xa7fffefbd326023f 0x053ffff7de993011 0xf7ffffffe2262662 0x7fbfffffff113133

def z1234 : W := mkw 0x004b0a2800080890 0x0002585140004044 0xe0db2f3c00181804 0x7706d979e000c0c0

def z1235 : W := mkw 0x0214001661616141 0x5010a000b30b0b0a 0xdf1c003fe1e1e1fb 0xaef8e001ff0f0f0f

def z1236 : W := mkw 0x08000104fffdf9c3 0xd840000827ffefce 0x18000000fffff9ff 0x80c0000007ffffcf

def z1237 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7e03fc0fe01fe13 0x4dbf01fe07f00ff0

def z1238 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e4ffc0fe27fe17 0xdfbf27fe07f13ff0

def z1239 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff021e3e16 0xff3ffffff810f1f0

def z1240 : W := mkw 0x24eb8ea800000014 0x01275c7540000000 0xe0db2f3c00000000 0x7706d979e0000000

def z1241 : W := mkw 0x235ffa7b0000001c 0x011affd3d8000000 0xe7dfff3f00000000 0x7f3efff9f8000000

def z1242 : W := mkw 0x035f3a3a61212051 0x501af9d1d3090902 0xf7df3f3fe0202062 0x7fbef9f9ff010103

def z1243 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8db2ffc1dd9df9d 0xf746d97fe0eecefc

def z1244 : W := mkw 0x25a17efb0000001c 0x012d0bf7d8000000 0x27203fff00000000 0x493901fff8000000

def z1245 : W := mkw 0xa7fffefb49be0abd 0x853ffff7da4df055 0xefffffff01fe01e8 0x7f7ffffff80ff00f

def z1246 : W := mkw 0x004b0a2800000010 0x0002585140000000 0x80db273c00000000 0x2406d939e0000000

def z1247 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff02060600 0x7f3ffffff8103030

def z1248 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdffbc000ffde000d 0xb6ffde0007fef000

def z1249 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff000021f0 0x7f3ffffff800010f

def z1250 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffffff1fdfdf9d 0xff47fffff8fefefc

def z1251 : W := mkw 0x26fe8688dbb40017 0x8137f43446dda000 0xdfffc700fffe000f 0xbefffe3807fff000

def z1252 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0x9f18203fe1c1c1e1 0x04f8c101ff0e0e0f

def z1253 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x20003fff00003e10 0x410001fff80001f0

def z1254 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff02001e04 0x7f3ffffff81000f0

def z1255 : W := mkw 0x27fffefb9a94001e 0x813ffff7dcd4a000 0xefffffff1fde000d 0xff7ffffff8fef000

def z1256 : W := mkw 0x004a020800000010 0x0002501040000000 0xc0d8273c00000000 0x6606c139e0000000

def z1257 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8fb3ffc1dd9d99d 0xff47d9ffe0eececc

def z1258 : W := mkw 0x24ebcee90000001c 0x01275e7748000000 0x20e3effc00000000 0x51071f7fe0000000

def z1259 : W := mkw 0xa14b7efb000a0abc 0x050a5bf7d8005055 0xe0db3fff00183ffc 0xf706d9fff800c1ff

def z1260 : W := mkw 0x884b49650cdadba8 0x8c425a4b2866d6dd 0xe8ffd8e31fffffff 0xff47fec718ffffff

def z1261 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0x87db273c00000000 0x243ed939e0000000

def z1262 : W := mkw 0x07b43492f3212443 0x703da1a497990922 0x772418e3e2203ffe 0xfbb920c71f1101ff

def z1263 : W := mkw 0x07ffba3a00000010 0x003ffdd1d0000000 0xe7ffff3f00000000 0x7f3ffff9f8000000

def z1264 : W := mkw 0x0deb3eacbad96d92 0xe86f59f565d6cb6c 0x1f3b10fce3d8278a 0x28f9d887e71ec13c

def z1265 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc000fdfe0009 0x3efffe0007eff000

def z1266 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x2024ffff00000000 0x490127fff8000000

def z1267 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7fbeffc00000000 0x773fdf7fe0000000

def z1268 : W := mkw 0x004b0a2808980890 0x800258514044c044 0xe8db2f3c1dd8199d 0xf746d979e0eec0cc

def z1269 : W := mkw 0x080149650cd8d988 0x88400a4b2866c6cc 0x6827d8e31dd9d99d 0xfb413ec718eececc

def z1270 : W := mkw 0x004b0b280c909010 0x8002585940648480 0xe8db2f3c1dd9d81d 0xf746d979e0eecec0

def z1271 : W := mkw 0x27feb69a61212055 0x513ff5b4d3090902 0x97d8271ce0000000 0x04bec138e7000000

def z1272 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8fb3fff1fd9ffff 0xff47d9fff8fecfff

def z1273 : W := mkw 0x07b4b492f3252443 0x703da5a497992922 0x1724d0c3e2262662 0x08b926861f113133

def z1274 : W := mkw 0x27fffefbfbb5205f 0xd13ffff7dfdda902 0xfffffffffffe206f 0xfffffffffffff103

def z1275 : W := mkw 0x08000104bed1f502 0xe840000825f68fa8 0x18000000fdc1c001 0x00c0000007ee0e00

def z1276 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0xa7db2f1c00000000 0x153ed978e0000000

def z1277 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff003e19fc 0xff3ffffff801f0cf

def z1278 : W := mkw 0x880001040cdadba0 0x8c4000082066d6dd 0x080000001dffd9fd 0x8040000000effecf

def z1279 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0xc80020001dd9d99d 0xc640010000eececc

def z1280 : W := mkw 0x0a1401044df8d981 0x8850a008226fc6cc 0xdf1c0000fdf9d99f 0xaef8e00007efcecc

def z1281 : W := mkw 0x084a01040cd0d100 0x8842500820668688 0x88d800001dc1c001 0x0446c00000ee0e00

def z1282 : W := mkw 0x23157efb0000001c 0x0118abf7d8000000 0xa7183fff00000000 0x4538c1fff8000000

def z1283 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x000000001c19d994 0x0000000000e0cecc

def z1284 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf18303fe1c1e1f3 0xcef8c181ff0e0f0f

def z1285 : W := mkw 0xa7fffefb9a9e0abe 0x853ffff7dcd4f055 0xe7ffffff1e3e3ffe 0xff3ffffff8f1f1ff

def z1286 : W := mkw 0x88014965bedbffaa 0xec400a4b2df6dffd 0x7827d8e3ffffffff 0xfbc13ec71fffffff

def z1287 : W := mkw 0xa25fca7b000a0abc 0x0512fe53d8005055 0xe0ffffff023e3ffe 0xff07fffff811f1ff

def z1288 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xff3ff8ffe3ffffff 0xfff9ffc7ff1fffff

def z1289 : W := mkw 0x080001040cd0d100 0x8840000820668688 0x080000001dc1d815 0x8040000000ee0ec0

def z1290 : W := mkw 0x07b57cf300000008 0x003dabe798000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1291 : W := mkw 0x8cebcb699e9e9aba 0x8c675e5b4cf4f4d5 0x20e3cfc01e1e1e04 0x11071e7e00f0f0f0

def z1292 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8d82f1c1dc1d801 0x0546c178e0ee0ec0

def z1293 : W := mkw 0x014b3a3a00000010 0x000a59d1d0000000 0xe0db3f3f00000000 0x7706d9f9f8000000

def z1294 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xc8db273c1dd9c18d 0xb646d939e0eece0c

def z1295 : W := mkw 0x27feb69a08900014 0x813ff5b4d0448000 0x8fd8271c1dc00001 0x047ec138e0ee0000

def z1296 : W := mkw 0x27feb69ad3240017 0x013ff5b4d6992000 0x97d8271ce0000000 0x04bec138e7000000

def z1297 : W := mkw 0x27fffefb0890001c 0x813ffff7d8448000 0xe7ffffff1c180004 0x7f3ffffff8e0c000

def z1298 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff02260002 0x7f3ffffff8113000

def z1299 : W := mkw 0x214bfefb0000001c 0x010a5ff7d8000000 0x2003ffff00000000 0x41001ffff8000000

def z1300 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0db2f3c1c000005 0xf706d979e0e00000

def z1301 : W := mkw 0x05eb3ea800000010 0x002f59f540000000 0xe7db2f3c00000000 0x773ed979e0000000

def z1302 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff00002660 0x7f3ffffff8000133

def z1303 : W := mkw 0x004a020808900010 0x8002501040448000 0x88d8271c1dc00001 0x0446c138e0ee0000

def z1304 : W := mkw 0x004a020808900010 0x8002501040448000 0xc8db271c1dd8000d 0xb646d938e0eec000

def z1305 : W := mkw 0x26ffcefbdbb4001f 0x8137fe77dedda000 0xffffcffffffe000f 0xbffffe7ffffff000

def z1306 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e43fe3fe01fe17 0xffbf21ff1ff00ff0

def z1307 : W := mkw 0x27b5fefbd324001f 0x013daff7de992000 0x3724ffffe2260002 0x49b927ffff113000

def z1308 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x480410231df9f9ff 0xea40208118efcfcf

def z1309 : W := mkw 0x804b4a69089a0ab8 0x84025a534844d055 0xe8ffffff1ffe3fff 0xff47fffff8fff1ff

def z1310 : W := mkw 0x27b5fefb0000001c 0x013daff7d8000000 0x27003fff00000000 0x413801fff8000000

def z1311 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x20003fff000021f0 0x410001fff800010f

def z1312 : W := mkw 0x21017efb2001201c 0x41080bf7d9000900 0xf7003fffe001e013 0xcfb801ffff000f00

def z1313 : W := mkw 0x21017efb2001241c 0x61080bf7d9000920 0x20003fff00002600 0x410001fff8000130

def z1314 : W := mkw 0x880149650cdadba8 0x8c400a4b2866d6dd 0x0807c0231dffd9fd 0xa0403e0118effecf

def z1315 : W := mkw 0x06ff8a2800000010 0x0037fc5140000000 0xe7db2f3c00000000 0x773ed979e0000000

def z1316 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0ffef3c023e000e 0xff07ff79e011f000

def z1317 : W := mkw 0x27fffefb4120001d 0x013ffff7da090000 0xffffffffe1c00001 0x7fffffffff0e0000

def z1318 : W := mkw 0x010035802401b400 0x600801ac01200da0 0xf7c03fc0fc01fe17 0xdfbe01fe07e00ff0

def z1319 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xefffffff01c00009 0xff7ffffff80e0000

def z1320 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xa8d82f1c1dc1d811 0x4546c178e0ee0ec0

def z1321 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7f83fff00000000 0x5f3fc1fff8000000

def z1322 : W := mkw 0x084b4b6d0cd0d118 0x88425a5b68668688 0xe8ffffff1dc1c001 0x7f47fffff8ee0e00

def z1323 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8db273c1dd9c19d 0xf646d939e0eece0c

def z1324 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87d8373f00000000 0x443ec1b9f8000000

def z1325 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xa7fbefdc021e1e04 0x153fdf7ee010f0f0

def z1326 : W := mkw 0x2315fefb0000001c 0x0118aff7d8000000 0x2004ffff00000000 0x410027fff8000000

def z1327 : W := mkw 0x07b43492f3212443 0x703da1a497990922 0x17041003e0202062 0x08b820801f010103

def z1328 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fe0fe01ff9f 0xffbf01ff07f00ffc

def z1329 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e33fc0fe19fe1f 0xffbf19fe07f0cff0

def z1330 : W := mkw 0x27fffefb4120005d 0x113ffff7da090002 0xe7ffffff00200060 0x7f3ffffff8010003

def z1331 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xfff83fc0ffc1fe1f 0xffffc1fe07fe0ff0

def z1332 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffd023fffe000f 0xfefffe811ffff000

def z1333 : W := mkw 0x004b0a2c08d04110 0x8002585160468208 0xe8db2f3c1dd9c19d 0xf746d979e0eece0c

def z1334 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xffffffffffe60003 0x7fffffffffff3000

def z1335 : W := mkw 0x000001040440d100 0x0000000820220688 0xc8d8273c1dc1c199 0xe646c139e0ee0e0c

def z1336 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8fbeffc1fffffff 0xf747df7fe0ffffff

def z1337 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8fbffff1fdffffd 0xf747dffff8feffff

def z1338 : W := mkw 0x235ffefb0000001c 0x011afff7d8000000 0x20183fff00000000 0x4100c1fff8000000

def z1339 : W := mkw 0x06b40000d3200003 0x0035a00006990000 0xdfffc000fffe000f 0xbefffe0007fff000

def z1340 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe8db2f3c01c00009 0xf746d979e00e0000

def z1341 : W := mkw 0x07ffbea800000010 0x003ffdf540000000 0xe7fffffc00000000 0x7f3fffffe0000000

def z1342 : W := mkw 0xa6ffcefb000a0abc 0x0537fe77d8005055 0x20ffcfff023e1fec 0x3107fe7ff811f0ff

def z1343 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0xe0183fff00000000 0x6700c1fff8000000

def z1344 : W := mkw 0x06fe8480dbb40003 0x8037f42406dda000 0xffffcfc0fffe000f 0xbffffe7e07fff000

def z1345 : W := mkw 0x000001040440d100 0x0000000820220688 0xe8d82f1c1dc1d815 0xd746c178e0ee0ec0

def z1346 : W := mkw 0x8a5fca6d49fe4bb9 0x8c52fe536a4ff25d 0x081fc03f01fe01e8 0x2040fe01f80ff00f

def z1347 : W := mkw 0x27fffefb4120001d 0x013ffff7da090000 0xefffffff01e00008 0x7f7ffffff80f0000

def z1348 : W := mkw 0x07b43492f3212443 0x703da1a497990922 0x172010c0e2002602 0x08b9008607100130

def z1349 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e3ffc0fe1ffe17 0xdfbf1ffe07f0fff0

def z1350 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffeffc1fffdf9f 0xff47ff7fe0fffefc

def z1351 : W := mkw 0x0cea81049edcd982 0x8867540824f6e6cc 0x08e3c0001fdfd99d 0x90471e0000fefecc

def z1352 : W := mkw 0x27fffefb2001241c 0x613ffff7d9000920 0xe7ffffff00002600 0x7f3ffffff8000130

def z1353 : W := mkw 0x25ebfefb0000001c 0x012f5ff7d8000000 0x20e3efdc00000000 0x11071f7ee0000000

def z1354 : W := mkw 0x284bcb6d0cd8d99c 0x89425e5b6866c6cc 0xe8dbef3c1dd9d99d 0xf746df79e0eececc

def z1355 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e02fc0fe01de15 0xd7bf017e07f00ef0

def z1356 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x2023ffff00000000 0x51011ffff8000000

def z1357 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8ffffff1fd9ff9f 0xff47fffff8fecffc

def z1358 : W := mkw 0x05a0b580b605b402 0x602d05ac05b02da0 0xf7e0ffc0fe07fe17 0xdfbf07fe07f03ff0

def z1359 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff00181804 0x7f3ffffff800c0c0

def z1360 : W := mkw 0x27fef6dbdbb4001f 0x813ff7b6dedda000 0xdffff7dffffe000f 0xbeffffbefffff000

def z1361 : W := mkw 0x26ffca7bdbb4001f 0x8137fe53dedda000 0xffffef3ffffe000f 0xffffff79fffff000

def z1362 : W := mkw 0xa14b7efb000a0abc 0x050a5bf7d8005055 0xe0ffffff023e3ffe 0xff07fffff811f1ff

def z1363 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7c03fc0fe01fe17 0xc5be01fe07f00ff0

def z1364 : W := mkw 0x80000104f76bffe3 0x7400000827bb5fff 0x18000000ffffffff 0x80c0000007ffffff

def z1365 : W := mkw 0x08000104dff4d103 0x8840000826ffa688 0x18000000ffffc00f 0x80c0000007fffe00

def z1366 : W := mkw 0x08010b2c0448d990 0x08400859602246cc 0xe8d82f3c1dc1d99d 0xf746c179e0ee0ecc

def z1367 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0db2f3c00000198 0xf706d979e000000c

def z1368 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xe7fc3fff00000000 0x7f3fe1fff8000000

def z1369 : W := mkw 0x25ebfefb0000001c 0x012f5ff7d8000000 0xe7e3ffff00000000 0x5f3f1ffff8000000

def z1370 : W := mkw 0x06fe8012dbb40003 0x8037f40096dda000 0xdfffc03ffffe000f 0xbefffe01fffff000

def z1371 : W := mkw 0x080001040cd0d100 0x8840000820668688 0x080000001dd9c00d 0x8040000000eece00

def z1372 : W := mkw 0x06ffca69dbb4001b 0x8037fe534edda000 0xfffffffffffe000f 0xfffffffffffff000

def z1373 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7d82fdc00000000 0x053ec17ee0000000

def z1374 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0x87dfe73f003e01e8 0x243eff39f801f00f

def z1375 : W := mkw 0x26ffcefb0000001c 0x0137fe77d8000000 0xe7ffcfff00000000 0x3f3ffe7ff8000000

def z1376 : W := mkw 0x25a17efbb201241e 0x612d0bf7dd900920 0x37203fffe2002602 0x49b901ffff100130

def z1377 : W := mkw 0x0efe8104dff4d103 0x8877f40826ffa688 0x9fd80000fdc1c001 0x04fec00007ee0e00

def z1378 : W := mkw 0x090031042cd9f980 0xc84801882166cfcc 0xdf003000fdd9f99f 0xcef8018007eecfcc

def z1379 : W := mkw 0x08000104fffdfd83 0xe840000827ffefec 0x18000000ffffff9f 0x80c0000007fffffc

def z1380 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff02002602 0x7f3ffffff8100130

def z1381 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fc0fe01de05 0x5fbf01fe07f00ef0

def z1382 : W := mkw 0xa5a17efb000a0abc 0x052d0bf7d8005055 0xe7e7ffff023e3ffe 0xff3f3ffff811f1ff

def z1383 : W := mkw 0x27fffefb9200001e 0x013ffff7dc900000 0xf7fffffffe3e000f 0xffbffffffff1f000

def z1384 : W := mkw 0x27fffefb0898089c 0x813ffff7d844c044 0xefffffff1dd8199d 0xff7ffffff8eec0cc

def z1385 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xf7ffffffe0000003 0xffbfffffff000000

def z1386 : W := mkw 0x27fffefb9a90001e 0x813ffff7dcd48000 0xffffffffffd8000f 0xfffffffffffec000

def z1387 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1dd9c189 0x7746d979e0eece0c

def z1388 : W := mkw 0x225f8a3a00000014 0x0112fc51d0000000 0xe0db2f3c00000000 0x7706d979e0000000

def z1389 : W := mkw 0x06ff8a28dbbc0893 0x8037fc5146dde044 0xffffef3cfffe199f 0xffffff79e7fff0cc

def z1390 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xefffffff1ffe000c 0x7f7ffffff8fff000

def z1391 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8dc373f1de1e1fb 0xee46e1b9f8ef0f0f

def z1392 : W := mkw 0x27fffefb4124001d 0x013ffff7da092000 0xe7ffffff00260000 0x7f3ffffff8013000

def z1393 : W := mkw 0x80014861000a0aa8 0x04000a4308005055 0x2027d8e3023e3ffc 0x71013ec71811f1ff

def z1394 : W := mkw 0x27fffefb49b4001d 0x813ffff7da4da000 0xefffffff01c00000 0x7f7ffffff80e0000

def z1395 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xffdc3f3fe1e1e1fb 0xfffee1f9ff0f0f0f

def z1396 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88db271c1dd9c009 0x2446d938e0eece00

def z1397 : W := mkw 0x0214000441604101 0x0010a000220b0208 0xdf1c303fe1e1e1fb 0xeef8e181ff0f0f0f

def z1398 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7db271c00000000 0x363ed938e0000000

def z1399 : W := mkw 0x27b5fefb0000001c 0x013daff7d8000000 0xe7e4ffff00000000 0x5f3f27fff8000000

def z1400 : W := mkw 0x004b0a28dbb40013 0x8002585146dda000 0xf8db2f3cfffe000f 0xf7c6d979e7fff000

def z1401 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xc7dc271c00000000 0x2e3ee138e0000000

def z1402 : W := mkw 0x87b474d3f323266b 0x743da3a69f991933 0x1724d0c3e2262662 0x08b926861f113133

def z1403 : W := mkw 0x04a00580b601b402 0x6025002c05b00da0 0xf7e00fc0fe01fe17 0x9fbf007e07f00ff0

def z1404 : W := mkw 0x21017efb2001205c 0x51080bf7d9000902 0x20003fff00002060 0x410001fff8000103

def z1405 : W := mkw 0xa7fffefbb20b2ebe 0x653ffff7dd905975 0xf7ffffffe23e3ffe 0xffbfffffff11f1ff

def z1406 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8ffffff1dd9fffd 0xff47fffff8eecfff

def z1407 : W := mkw 0x2314369a00000014 0x0118a1b4d0000000 0xc71c373f00000000 0x6e38e1b9f8000000

def z1408 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8dbef3c1ddfd99d 0xf746df79e0eefecc

def z1409 : W := mkw 0x225fcefb0000001c 0x0112fe77d8000000 0x201fcfff00000000 0x2100fe7ff8000000

def z1410 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x87fff7ff00000000 0x2c3fffbff8000000

def z1411 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff023e1fec 0x7f3ffffff811f0ff

def z1412 : W := mkw 0x035f3a3a00080890 0x001af9d1d0004044 0xe7df3f3f003839fe 0xff3ef9f9f801c1cf

def z1413 : W := mkw 0x25a1fefb0000001c 0x012d0ff7d8000000 0x2020ffff00000000 0x410107fff8000000

def z1414 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x4827c0001fffd99f 0xba413e0000fffecc

def z1415 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87f837dc00000000 0x0c3fc1bee0000000

def z1416 : W := mkw 0x080001042449f9c0 0x5840000821224fce 0x000000000001f9f0 0x0000000000000fcf

def z1417 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xa7ffffdf00000000 0x1d3ffffef8000000

def z1418 : W := mkw 0x084a01040cd0d100 0x8842500820668688 0xc8db00001dd9c00d 0xb646d80000eece00

def z1419 : W := mkw 0x27fffefb0008089c 0x013ffff7d8004044 0xe7ffffff023e199e 0xff3ffffff811f0cc

def z1420 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8dfef3f1dd9d99d 0xf746ff79f8eececc

def z1421 : W := mkw 0x035f7a7b00000018 0x001afbd3d8000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1422 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff022627fa 0xff3ffffff811313f

def z1423 : W := mkw 0x80014965f76bffeb 0x74000a4b2fbb5fff 0x7827d8e3ffffffff 0xfbc13ec71fffffff

def z1424 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff0020000a 0xff3ffffff8010000

def z1425 : W := mkw 0x08010924dffcd983 0x8840084926ffe6cc 0x7827c820ffffd99f 0xfbc13e4107fffecc

def z1426 : W := mkw 0x080001040448d980 0x08400008202246cc 0x000000000019d99c 0x800000000000cecc

def z1427 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fffc000fffe0007 0x1cfffe0007fff000

def z1428 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0xc8d8273c1dd9d99d 0xe646c139e0eececc

def z1429 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f1c1dd9d80d 0xb746d978e0eecec0

def z1430 : W := mkw 0x27fffefb9a94001e 0x813ffff7dcd4a000 0xf7fffffffe1e0007 0xffbffffffff0f000

def z1431 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xc8db273c1dd9c199 0xe646d939e0eece0c

def z1432 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0x9fd8271cfffe000f 0x84fec138e7fff000

def z1433 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87fbe71c00000000 0x143fdf38e0000000

def z1434 : W := mkw 0x214b7efb0890001c 0x810a5bf7d8448000 0xe8db3fff1dd8000d 0xf746d9fff8eec000

def z1435 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff023e266e 0xff3ffffff811f133

def z1436 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff001e0000 0x7f3ffffff800f000

def z1437 : W := mkw 0x20014efb0000001c 0x01000a77d8000000 0x20000fff00000000 0x0100007ff8000000

def z1438 : W := mkw 0x080001042cd9f9c0 0xd84000082166cfce 0x080000001dd9f9fd 0x8040000000eecfcf

def z1439 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87fce71c00000000 0x0c3fe738e0000000

def z1440 : W := mkw 0x89017fed244bffb8 0x6c480bff69225ffd 0x20003fff0001fff0 0x410001fff8000fff

def z1441 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x87d8273f00000000 0x043ec139f8000000

def z1442 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xe7f83fdc02003e16 0xdf3fc1fee01001f0

def z1443 : W := mkw 0x88000104dffedba3 0x8c40000826fff6dd 0x18000000ffffffff 0x80c0000007ffffff

def z1444 : W := mkw 0x06fe8104fff5f543 0xf037f40827ffafaa 0xdfffc000ffffffff 0xbefffe0007ffffff

def z1445 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fdfc000fffe000f 0xa4fefe0007fff000

def z1446 : W := mkw 0x26ffca7b0000001c 0x0137fe53d8000000 0xe7ffef3f00000000 0x7f3fff79f8000000

def z1447 : W := mkw 0x03153a3a00000010 0x0018a9d1d0000000 0xe71c3f3f00000000 0x6f38e1f9f8000000

def z1448 : W := mkw 0x27ffbebadbb40017 0x813ffdf5d6dda000 0xffdb2f3cfdd8000d 0xf7fed979e7eec000

def z1449 : W := mkw 0x27feb69a41200015 0x013ff5b4d2090000 0x9fd8271ce1c00001 0x04fec138e70e0000

def z1450 : W := mkw 0xa4ebcee9000a0abc 0x05275e7748005055 0xe0fbeffc021e1f9c 0xf707df7fe010f0fc

def z1451 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db2f3c1dd9d805 0x7746d979e0eecec0

def z1452 : W := mkw 0x27fffefb2001205c 0x513ffff7d9000902 0xe7ffffff00002060 0x7f3ffffff8000103

def z1453 : W := mkw 0x21017efb0008089c 0x01080bf7d8004044 0x60033fff0018199c 0xf30019fff800c0cc

def z1454 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff0018000c 0xff3ffffff800c000

def z1455 : W := mkw 0x27fffefb9200041e 0x213ffff7dc900020 0xe7ffffff02000600 0x7f3ffffff8100030

def z1456 : W := mkw 0x25ebfee90000001c 0x012f5ff748000000 0xe7fbfffc00000000 0x7f3fdfffe0000000

def z1457 : W := mkw 0x080001049ed8dd82 0xa840000824f6c6ec 0x080000001fd9df9d 0x8040000000fecefc

def z1458 : W := mkw 0x010031002401b000 0x4008018801200d80 0xf7e03fc0fe01fe17 0xdfbf01fe07f00ff0

def z1459 : W := mkw 0x06fe820800000010 0x0037f41040000000 0xc7ffe71c00000000 0x3e3fff38e0000000

def z1460 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0xe8d82f3c1dd9d99d 0xf746c179e0eececc

def z1461 : W := mkw 0x080001044df8d9c1 0x98400008226fc6ce 0x080000001df9d9fd 0x8040000000efcecf

def z1462 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xe8db2f1c1dd9d81d 0xf746d978e0eecec0

def z1463 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e43fc3fe21fe77 0xdfbf21fe1ff10ff3

def z1464 : W := mkw 0x08010924bed9fd82 0xe840084925f6cfec 0x782318e0ffd9ff9f 0xfbc118c707fecffc

def z1465 : W := mkw 0x88000104044adba0 0x0c400008202256dd 0x000000000001fff0 0x0000000000000fff

def z1466 : W := mkw 0x05a0348000000000 0x002d01a400000000 0xe7f83ffc00000000 0x7f3fc1ffe0000000

def z1467 : W := mkw 0x214b3eba00000014 0x010a59f5d0000000 0xe0db2f3c00000000 0x7706d979e0000000

def z1468 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xf7fffffffe3e0006 0x7fbffffffff1f000

def z1469 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x27ffdfff00000000 0x393ffefff8000000

def z1470 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xb7c02fc0fc01de01 0x05be017e07e00ef0

def z1471 : W := mkw 0x27fffefb9a94001e 0x813ffff7dcd4a000 0xe7ffffff1e3e000e 0xff3ffffff8f1f000

def z1472 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xa8db2f3c1dd9d98d 0x3546d979e0eececc

def z1473 : W := mkw 0x27fffefbf321245f 0x713ffff7df990922 0xf7ffffffe2202662 0x7fbfffffff110133

def z1474 : W := mkw 0x0eb48104dffcd983 0x8875a40826ffe6cc 0x1f24c000ffffd99f 0x88f9260007fffecc

def z1475 : W := mkw 0x225fca7b0000001c 0x0112fe53d8000000 0x201fef3f00000000 0x6100ff79f8000000

def z1476 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xe8db3fff1fffffff 0xf746d9fff8ffffff

def z1477 : W := mkw 0x080001046df1f141 0xd8400008236f8f8a 0x18000000fde1e1fb 0x80c0000007ef0f0f

def z1478 : W := mkw 0x014b3a2820012010 0x400a59d141000900 0xf7db3f3ce001e013 0xffbed9f9e7000f00

def z1479 : W := mkw 0x004b0a2808900010 0x8002585140448000 0xe8db2f3c01d80008 0x7746d979e00ec000

def z1480 : W := mkw 0x2ffffefb0898089c 0x897ffff7d844c044 0xe7ffffff00180000 0x7f3ffffff800c000

def z1481 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0xffffffdcfffe000f 0xfffffffee7fff000

def z1482 : W := mkw 0x26ffcefb0000001c 0x0137fe77d8000000 0x60ffdfff00000000 0x7b07fefff8000000

def z1483 : W := mkw 0x27feb69a9a940016 0x813ff5b4d4d4a000 0x87fbe71c1e1e0004 0x143fdf38e0f0f000

def z1484 : W := mkw 0x27b4f4d30000000c 0x013da7a698000000 0xe7fcffff00000000 0x7f3fe7fff8000000

def z1485 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fe3fe01fff7 0xdfbf01ff1ff00fff

def z1486 : W := mkw 0x004b0a2800000010 0x0002585140000000 0x201b2f3c00000000 0x6100d979e0000000

def z1487 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8fffffc1fffff9f 0xff47ffffe0fffffc

def z1488 : W := mkw 0x88014965044adba8 0x0c400a4b282256dd 0x6027d8e3023ffffe 0xfb013ec71811ffff

def z1489 : W := mkw 0x084b4b6d0cd8d998 0x88425a5b6866c6cc 0xe8ffffff1df9f9ff 0xff47fffff8efcfcf

def z1490 : W := mkw 0x080001049ed8d982 0x8840000824f6c6cc 0x18000000ffd9d99f 0x80c0000007fececc

def z1491 : W := mkw 0x27fffefb2001201c 0x413ffff7d9000900 0xf7ffffffe021e1fb 0xffbfffffff010f0f

def z1492 : W := mkw 0x27feb69a20012014 0x413ff5b4d1000900 0xd7d8371ce001e013 0xcebec1b8e7000f00

def z1493 : W := mkw 0x0a5e81044dfcd981 0x8852f408226fe6cc 0x081fc0001dffd99d 0xa040fe0000effecc

def z1494 : W := mkw 0x004b0b2c0440d110 0x0002585960220688 0xe8db2f3c1dc1d99d 0xf746d979e0ee0ecc

def z1495 : W := mkw 0x0da03584bed9fd82 0xe86d01ac25f6cfec 0x1f2010c0ffd9ff9f 0x88f9008607fecffc

def z1496 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xdf3cf03fe3e7e1fb 0xeef9e781ff1f3f0f

def z1497 : W := mkw 0xa7fffefbdbb6023f 0x853ffff7deddb011 0xfffffffffffe266f 0xfffffffffffff133

def z1498 : W := mkw 0x86ffca69dbbe0abb 0x8437fe534eddf055 0xfffffffffffe3fff 0xfffffffffffff1ff

def z1499 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fc0fe21ffff 0xdfbf01fe07f10fff

def z1500 : W := mkw 0x27fffefbd324001f 0x013ffff7de992000 0xffffffffe3e6000b 0xffffffffff1f3000

def z1501 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffdd8000d 0xffffffffffeec000

def z1502 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e02fc0fe01de07 0x9fbf017e07f00ef0

def z1503 : W := mkw 0x26ffcee9dbb4001f 0x8137fe774edda000 0xffffeffcfffe000f 0xffffff7fe7fff000

def z1504 : W := mkw 0x80014a69000a0ab8 0x04000a5348005055 0x20003fff00003ff0 0x410001fff80001ff

def z1505 : W := mkw 0xa1017efb0002023c 0x05080bf7d8001011 0x20003fff00002660 0x410001fff8000133

def z1506 : W := mkw 0x025f8a2800000010 0x0012fc5140000000 0xe0dfef3c00000000 0x7706ff79e0000000

def z1507 : W := mkw 0x0314b01661656141 0x5018a580b30b2b0a 0xdf1cf03fe1e7e1fb 0xeef8e781ff0f3f0f

def z1508 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7fbffdc00000000 0x5f3fdffee0000000

def z1509 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0x87dc273f00000000 0x243ee139f8000000

def z1510 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x480000201dd9d99d 0xe240000100eececc

def z1511 : W := mkw 0x210076db0000001c 0x010803b6d8000000 0x000037df00000000 0x000001bef8000000

def z1512 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffd000fffe201f 0xfefffe8007fff100

def z1513 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8ff3fff1ff9ffff 0xff47f9fff8ffcfff

def z1514 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff021e3ff4 0x7f3ffffff810f1ff

def z1515 : W := mkw 0x20014a7b0000001c 0x01000a53d8000000 0x20002f3f00000000 0x41000179f8000000

def z1516 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fffc000fffe000d 0x34fffe0007fff000

def z1517 : W := mkw 0x27fffefbb201201e 0x413ffff7dd900900 0xf7fffffffe01e017 0xffbffffffff00f00

def z1518 : W := mkw 0x235f7efb0000001c 0x011afbf7d8000000 0xe7df3fff00000000 0x7f3ef9fff8000000

def z1519 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xdfffc000fffe3e1f 0xbefffe0007fff1f0

def z1520 : W := mkw 0x084a030c0cd8d990 0x884250186066c6cc 0xc8db271c1dd9d99d 0xb646d938e0eececc

def z1521 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0x88db273c1dd9d99d 0xa446d939e0eececc

def z1522 : W := mkw 0x00010a2800000010 0x0000085140000000 0xe0182f3c00000000 0x6700c179e0000000

def z1523 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0x9fffc000fffe000b 0x2cfffe0007fff000

def z1524 : W := mkw 0x07b43492f3212443 0x703da1a497990922 0x17000000e0000000 0x00b8000007000000

def z1525 : W := mkw 0x24ea868800000014 0x0127543440000000 0x80d8271c00000000 0x0406c138e0000000

def z1526 : W := mkw 0x0314301661616141 0x5018a180b30b0b0a 0xff1c383fe1e1f9ff 0xfff8e1c1ff0f0fcf

def z1527 : W := mkw 0x214b7efb0000001c 0x010a5bf7d8000000 0x201b3fff00000000 0x6100d9fff8000000

def z1528 : W := mkw 0x080001040cd8d980 0x884000082066c6cc 0x480300001dd9d99d 0xb240180000eececc

def z1529 : W := mkw 0x27feb69a92000016 0x013ff5b4d4900000 0xd7f8271cfe000007 0x9ebfc138e7f00000

def z1530 : W := mkw 0x004b0a2808900010 0x8002585140448000 0xe0db2f3c1c180004 0x7706d979e0e0c000

def z1531 : W := mkw 0xa35ffefb000a0abc 0x051afff7d8005055 0x603fffff023e3ffe 0xfb01fffff811f1ff

def z1532 : W := mkw 0x08000104bed1f502 0xe840000825f68fa8 0x18000000ffc1fe17 0x80c0000007fe0ff0

def z1533 : W := mkw 0x080001040448d980 0x08400008202246cc 0x0800000001c1d999 0x80400000000e0ecc

def z1534 : W := mkw 0x27feb69a49b40015 0x813ff5b4d24da000 0x8fd8271c01c00000 0x047ec138e00e0000

def z1535 : W := mkw 0x27fffefb4120001d 0x013ffff7da090000 0xf7ffffffe0200002 0x7fbfffffff010000

def z1536 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xffffd8c0fffe000f 0xfffffec607fff000

def z1537 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff00001814 0xff3ffffff80000c0

def z1538 : W := mkw 0x88014965dffedbab 0x8c400a4b2efff6dd 0x7827d8e3ffffffff 0xfbc13ec71fffffff

def z1539 : W := mkw 0x27fffefbf325241f 0x613ffff7df992920 0xf7ffffffe2262602 0x7fbfffffff113130

def z1540 : W := mkw 0x06fe8000dbb40003 0x8037f40006dda000 0xffffc8c0fffe1e0f 0xbffffe4607fff0f0

def z1541 : W := mkw 0x0000000000000000 0x0000000000000000 0x6027d8e3023e3ffe 0xfb013ec71811f1ff

def z1542 : W := mkw 0x27feb69adbb40017 0x813ff5b4d6dda000 0xdffff73ffffe000f 0xfeffffb9fffff000

def z1543 : W := mkw 0x86ffca69000a0ab8 0x0437fe5348005055 0xe7ffffff023e3ffe 0xff3ffffff811f1ff

def z1544 : W := mkw 0x07b43596f761f543 0x703da1acb7bb0faa 0x1f2410c3ffe1ffff 0x88f920861fff0fff

def z1545 : W := mkw 0x8effc965dffedbab 0x8c77fe4b2efff6dd 0xffffd8e3ffffffff 0xfffffec71fffffff

def z1546 : W := mkw 0xa7fef6db0002023c 0x053ff7b6d8001011 0x87fcf7df02262662 0x0c3fe7bef8113133

def z1547 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0x87f8e7dc00000000 0x043fc73ee0000000

def z1548 : W := mkw 0xa7fffefb0002023c 0x053ffff7d8001011 0xe7ffffff02263e76 0xff3ffffff81131f3

def z1549 : W := mkw 0xa7b5fefb000a0abc 0x053daff7d8005055 0x6727ffff023e3ffe 0xfb393ffff811f1ff

def z1550 : W := mkw 0x23157efb0000001c 0x0118abf7d8000000 0x201c3fff00000000 0x6100e1fff8000000

def z1551 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0x37e03fc0fe01fe16 0x59bf01fe07f00ff0

def z1552 : W := mkw 0x27fef6db0000001c 0x013ff7b6d8000000 0xc7fff7df00000000 0x3e3fffbef8000000

def z1553 : W := mkw 0x88014965044adba8 0x0c400a4b282256dd 0x200018e30001fff0 0x410000c718000fff

def z1554 : W := mkw 0x07b43492f3212443 0x703da1a497990922 0xf7fc3fffe2202662 0x7fbfe1ffff110133

def z1555 : W := mkw 0x004b0a2800000010 0x0002585140000000 0xe0df3f3f002021fa 0xff06f9f9f801010f

def z1556 : W := mkw 0x080001040440d100 0x0840000820220688 0x000000000001c000 0x0000000000000e00

def z1557 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0xa7d82f3c00000000 0x453ec179e0000000

def z1558 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0xc8d8273c1dc1c001 0x6646c139e0ee0e00

def z1559 : W := mkw 0x27feb69a00000014 0x013ff5b4d0000000 0xe7ffffdc00000000 0x7f3ffffee0000000

def z1560 : W := mkw 0x27feb69ab2012416 0x613ff5b4d5900920 0x97f837dce2002602 0x0cbfc1bee7100130

def z1561 : W := mkw 0x05a03592b601b442 0x702d01ac95b00da2 0xf7e03fc3fe01fe77 0xdfbf01fe1ff00ff3

def z1562 : W := mkw 0x27ffbeba00000014 0x013ffdf5d0000000 0xe7df3f3f00000000 0x7f3ef9f9f8000000

def z1563 : W := mkw 0x804b4a69000a0ab8 0x04025a5348005055 0xe0dfef3f003e01e8 0x7706ff79f801f00f

def z1564 : W := mkw 0x27b4f4d3f321244f 0x713da7a69f990922 0x1724d0c3e2202662 0x08b926861f110133

def z1565 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8ffef3c1dd9d99d 0xff47ff79e0eececc

def z1566 : W := mkw 0x27fffefbdbbc089f 0x813ffff7dedde044 0xfffffffffffe199f 0xfffffffffffff0cc

def z1567 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8df2f3f1df9d9fd 0xf746f979f8efcecf

def z1568 : W := mkw 0x884b4b6d0cdadbb8 0x8c425a5b6866d6dd 0xa8d83fff1dc1fff1 0x4546c1fff8ee0fff

def z1569 : W := mkw 0x27ffbeba00080894 0x013ffdf5d0004044 0xe7db2f3c0018199c 0xf73ed979e000c0cc

def z1570 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8ffff3f1ffff9ff 0xff47fff9f8ffffcf

def z1571 : W := mkw 0x080001042449fd80 0x6840000821224fec 0x000000000001ff90 0x0000000000000ffc

def z1572 : W := mkw 0xa1017efb000a0abc 0x05080bf7d8005055 0x2007ffff003e01e8 0x61003ffff801f00f

def z1573 : W := mkw 0xa7fffefb000a0abc 0x053ffff7d8005055 0xe7ffffff021e1f9c 0xff3ffffff810f0fc

def z1574 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xfffffffffde0000b 0xffffffffffef0000

def z1575 : W := mkw 0x804b4a69000a0ab8 0x04025a5348005055 0xe0fbeffc021e1e04 0x7707df7fe010f0f0

def z1576 : W := mkw 0x0314349661616541 0x7018a1a4b30b0b2a 0xdf1c30ffe1e1e7fb 0xeef8e187ff0f0f3f

def z1577 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff0001c011 0xff3ffffff8000e00

def z1578 : W := mkw 0x084a030c0cd0d110 0x8842501860668688 0x88d8273c1dc1c189 0x2446c139e0ee0e0c

def z1579 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0x27e7ffff00000000 0x593f3ffff8000000

def z1580 : W := mkw 0x05a03580b601b402 0x602d01ac05b00da0 0xf7e03fc0fc01fe11 0x5fbf01fe07e00ff0

def z1581 : W := mkw 0x03143112b601b402 0x6018a18895b00da0 0xd71c303ffe01fe17 0xeeb8e181fff00ff0

def z1582 : W := mkw 0x25a17efb0000001c 0x012d0bf7d8000000 0xe7e7ffff00000000 0x7f3f3ffff8000000

def z1583 : W := mkw 0x080109240cd8d980 0x884008492066c6cc 0x080300201dd9d99d 0xa040180100eececc

def z1584 : W := mkw 0x04eb0ea800000010 0x0027587540000000 0xe0fb2ffc00000000 0x7707d97fe0000000

def z1585 : W := mkw 0x00000104b641f542 0x7000000825b20faa 0x10000000fe01fff7 0x8080000007f00fff

def z1586 : W := mkw 0x27fffefb0000001c 0x013ffff7d8000000 0xe7ffffff1c000005 0xff3ffffff8e00000

def z1587 : W := mkw 0x084b0b2c0cd8d990 0x884258596066c6cc 0xe8db3ffc1dd9ff9d 0xf746d9ffe0eecffc

def z1588 : W := mkw 0x80014965044adba8 0x04000a4b282256dd 0xe8ffffff1fffffff 0xff47fffff8ffffff

def z1589 : W := mkw 0x025f0a3a00000010 0x0012f851d0000000 0xe0df2f3f00000000 0x7706f979f8000000

def z1590 : W := mkw 0x27fffefb6121205d 0x513ffff7db090902 0xf7ffffffe021e073 0xffbfffffff010f03

def z1591 : W := mkw 0x25a0369a00000014 0x012d01b4d0000000 0xe7e03fdc00000000 0x5f3f01fee0000000

def z1592 : W := mkw 0x014b3ea800000010 0x000a59f540000000 0xe0db3ffc00000000 0x7706d9ffe0000000

def z1593 : W := mkw 0x080001042cd9fd80 0xe84000082166cfec 0x080000001dd9ff9d 0x8040000000eecffc

def z1594 : W := mkw 0x06b40104f761f543 0x7035a00827bb0faa 0xdffc0000ffe1ffff 0xbeffe00007ff0fff

def z1595 : W := mkw 0x014b3a2800000010 0x000a59d140000000 0xe7db3f3c00000000 0x7f3ed9f9e0000000

def z1596 : W := mkw 0xa7fffefb412a0abd 0x053ffff7da095055 0xffffffffe3fe3fff 0xffffffffff1ff1ff

def z1597 : W := mkw 0x27fffefbdbb4001f 0x813ffff7dedda000 0xffffefdcfffe000f 0xbfffff7ee7fff000

def z1598 : W := mkw 0x25eb7efb0000001c 0x012f5bf7d8000000 0xe7fb3fff00000000 0x7f3fd9fff8000000

def z1599 : W := mkw 0x26ffcefb0000001c 0x0137fe77d8000000 0x00dfc73f00000000 0x2006fe39f8000000

def z1600 : W := mkw 0x88000104044adba0 0x0c400008202256dd 0x00000000023ffffe 0x800000000011ffff

def z1601 : W := mkw 0x004b0a2800080890 0x0002585140004044 0xe0db2f3c00180188 0x7706d979e000c00c

def z1602 : W := mkw 0xa7fffefb6123227d 0x553ffff7db091913 0xf7ffffffe2262662 0x7fbfffffff113133

def z1603 : W := mkw 0x21017efb0000001c 0x01080bf7d8000000 0x2007ffff00000000 0x61003ffff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z11,z6]),(0,[z12,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z13,z5,z6,z14]),(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z16,z5,z6]),(0,[z1,z17,z2,z3,z8,z5,z6]),(0,[z18,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z19,z20,z6]),(1,[z10,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z21,z8,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z23,z5,z6])],[],[(0,[z24,z1,z2,z3,z25,z8,z6]),(0,[z1,z26,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z27]),(0,[z28,z1,z2,z3,z25,z8,z6]),(0,[z29,z1,z2,z3,z8,z5,z6])],[(0,[z9,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z30,z5,z6]),(0,[z1,z3,z31,z8,z5,z6,z32]),(0,[z15,z1,z2,z3,z8,z33,z6]),(0,[z1,z2,z34,z3,z8,z20,z6]),(0,[z35,z1,z2,z3,z25,z8,z6])],[(0,[z1,z2,z3,z25,z8,z36,z6]),(0,[z37,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z38,z6]),(1,[z1,z2,z3,z8,z39,z6]),(0,[z1,z2,z40,z3,z25,z8,z6]),(0,[z18,z1,z2,z3,z5,z6,z14]),(0,[z41,z1,z2,z3,z8,z42,z6])],[(0,[z43,z1,z2,z3,z8,z5,z6])],[(0,[z44,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z45,z6]),(0,[z1,z46,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z47,z48,z8,z6]),(0,[z1,z2,z3,z5,z49,z6,z14]),(0,[z50,z1,z2,z3,z51,z5,z6])],[(0,[z1,z2,z3,z8,z52,z5,z6]),(0,[z1,z2,z3,z53,z25,z8,z6])],[(0,[z1,z2,z3,z8,z54,z6,z55]),(0,[z1,z2,z3,z8,z11,z56,z6]),(1,[z57,z1,z2,z8,z56,z6]),(0,[z1,z2,z3,z8,z56,z49,z6])],[(0,[z1,z2,z3,z25,z58,z8,z6]),(0,[z57,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z13,z8,z42,z6]),(0,[z1,z2,z3,z8,z5,z36,z6]),(0,[z1,z2,z3,z8,z59,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6])],[(0,[z1,z2,z3,z61,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z6]),(0,[z1,z2,z3,z4,z5,z20,z6])],[(1,[z1,z2,z3,z63,z5,z6]),(0,[z10,z1,z2,z64,z3,z8,z6]),(0,[z1,z65,z2,z3,z8,z5,z6])]],
   [[(0,[z66,z2,z3,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z6]),(0,[z1,z2,z3,z5,z38,z6,z14])],[(0,[z69,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z70]),(0,[z1,z2,z3,z8,z42,z6,z71]),(0,[z1,z2,z3,z31,z8,z20,z6]),(0,[z1,z2,z72,z3,z8,z5,z6])],[(1,[z1,z2,z3,z23,z5,z6]),(0,[z50,z1,z2,z3,z8,z6,z55])],[(0,[z73,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z74,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z75,z6]),(0,[z1,z2,z3,z8,z5,z76,z6])],[(1,[z1,z2,z77,z8,z5,z6])],[(0,[z78,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z79,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z80,z6])],[(0,[z1,z66,z2,z8,z5,z6,z81]),(0,[z1,z2,z3,z8,z82,z56,z6]),(0,[z1,z2,z3,z42,z5,z6,z14]),(1,[z1,z2,z3,z4,z5,z14]),(0,[z83,z1,z2,z3,z4,z5,z6])],[(0,[z84,z1,z2,z3,z4,z5,z6]),(0,[z1,z85,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z86,z8,z5,z6])],[(0,[z1,z2,z3,z87,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z88]),(0,[z1,z2,z3,z8,z89,z20,z6]),(0,[z1,z2,z3,z4,z8,z5,z6])],[(1,[z1,z90,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z91])],[(0,[z1,z2,z3,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z6,z71]),(1,[z1,z2,z3,z92,z8,z6]),(0,[z93,z1,z3,z8,z5,z6,z32]),(0,[z1,z2,z3,z8,z94,z5,z6])],[(0,[z95,z1,z2,z3,z8,z96,z6]),(0,[z1,z66,z2,z3,z25,z8,z6]),(1,[z1,z2,z3,z97,z8,z6]),(0,[z98,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z99,z6])],[(0,[z1,z2,z3,z8,z5,z6,z100]),(0,[z15,z1,z2,z101,z8,z5,z6]),(0,[z1,z2,z102,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z103,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z104])],[(0,[z105,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z106,z5,z6]),(0,[z1,z107,z2,z3,z8,z5,z6])],[(0,[z108,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z109,z6]),(0,[z110,z1,z2,z8,z5,z6,z81]),(0,[z111,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z112])],[(0,[z1,z2,z3,z67,z5,z6,z14]),(0,[z1,z2,z3,z8,z5,z6,z113]),(0,[z1,z114,z2,z3,z8,z42,z6])],[(0,[z115,z1,z2,z3,z13,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z116,z8,z5,z6]),(0,[z1,z2,z3,z8,z117,z42,z6])],[(0,[z1,z2,z102,z3,z5,z6,z14]),(0,[z118,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z8,z6,z55,z119])],[],[(0,[z24,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z120,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z32]),(0,[z121,z1,z2,z3,z8,z56,z6]),(1,[z1,z2,z3,z8,z16,z6])],[(0,[z1,z2,z3,z8,z56,z6,z122]),(0,[z10,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z123,z6,z55]),(0,[z35,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z42,z124,z6])],[(0,[z125,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z25,z8,z20,z6])],[(0,[z126,z1,z2,z3,z8,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z127,z6]),(0,[z1,z2,z3,z8,z128,z5,z6]),(0,[z129,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z130])],[(0,[z1,z2,z3,z8,z11,z5,z6])],[(0,[z1,z131,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z53,z8,z6,z55])],[(0,[z10,z1,z2,z3,z132,z8,z6]),(0,[z133,z1,z2,z3,z8,z6,z55])],[(0,[z1,z2,z3,z134,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z6]),(0,[z135,z1,z2,z3,z8,z56,z6])],[(0,[z1,z136,z2,z3,z8,z56,z6]),(0,[z137,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z6,z55])],[(0,[z138,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z71]),(0,[z1,z2,z3,z8,z42,z38,z6]),(1,[z1,z2,z3,z139,z5,z6])],[(0,[z140,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z102,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z20,z124,z6]),(0,[z1,z2,z3,z8,z52,z56,z6]),(0,[z1,z2,z3,z25,z8,z6,z81])]],
   [[(0,[z1,z2,z31,z8,z5,z6,z81]),(0,[z1,z2,z3,z58,z8,z20,z6])],[(0,[z141,z1,z2,z3,z8,z20,z6])],[(0,[z1,z2,z3,z8,z5,z142,z6]),(0,[z1,z2,z3,z92,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z143,z6]),(1,[z144,z1,z2,z3,z8,z6])],[(0,[z145,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z42,z146,z6])],[(0,[z1,z2,z3,z8,z39,z5,z6])],[(0,[z147,z1,z2,z3,z8,z5,z6]),(0,[z125,z2,z3,z8,z54,z5,z6]),(0,[z148,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z82,z5,z6]),(0,[z149,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z150]),(0,[z1,z2,z3,z8,z151,z6,z152])],[(0,[z1,z2,z3,z25,z8,z153,z6]),(0,[z1,z154,z2,z3,z25,z8,z6]),(0,[z78,z1,z2,z3,z8,z6,z55]),(0,[z155,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z156,z6]),(0,[z95,z1,z2,z3,z8,z20,z6])],[(0,[z1,z2,z3,z8,z146,z5,z6])],[(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z157,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z4,z8,z6]),(0,[z1,z2,z3,z8,z158,z5,z6])],[(0,[z159,z1,z2,z3,z8,z5,z6]),(0,[z1,z160,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z4,z42,z6])],[(0,[z1,z2,z3,z8,z161,z5,z6]),(0,[z1,z2,z3,z8,z5,z162,z6]),(0,[z163,z1,z2,z3,z8,z56,z6])],[(0,[z164,z1,z2,z3,z8,z5,z6]),(0,[z1,z66,z2,z3,z8,z6,z55]),(0,[z10,z1,z154,z2,z3,z8,z6]),(0,[z165,z84,z1,z2,z8,z5,z6])],[(1,[z1,z2,z3,z8,z96,z6]),(1,[z95,z2,z67,z8,z5,z6])],[(0,[z166,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z8,z56,z6])],[(0,[z1,z2,z3,z8,z5,z6,z167])]],
   [[(0,[z168,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z25,z5,z6])],[(0,[z1,z2,z3,z8,z169,z5,z6]),(0,[z9,z1,z2,z3,z8,z5,z71]),(0,[z1,z154,z2,z31,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z151,z6]),(0,[z1,z2,z3,z8,z5,z6,z170])],[(0,[z1,z2,z171,z3,z8,z5,z6]),(0,[z1,z2,z3,z132,z8,z6,z55]),(0,[z1,z2,z101,z3,z8,z56,z6]),(1,[z1,z2,z3,z172,z5,z6]),(0,[z1,z2,z3,z4,z5,z124,z6])],[(0,[z173,z2,z3,z132,z8,z5,z6]),(0,[z135,z1,z46,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z174,z6]),(0,[z121,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z175,z8,z5,z6]),(0,[z176,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z177,z5,z6]),(0,[z1,z2,z3,z8,z178,z5,z6]),(1,[z50,z1,z2,z3,z8,z55])],[(0,[z179,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z48,z8,z42,z6]),(1,[z1,z2,z3,z180,z5,z6]),(0,[z1,z2,z3,z8,z42,z6,z14])],[(0,[z1,z2,z3,z8,z181,z5,z6])],[(0,[z182,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z183,z6]),(0,[z184,z1,z2,z3,z8,z5,z6]),(0,[z185,z10,z1,z2,z3,z8,z6]),(1,[z1,z2,z3,z8,z42,z55])],[(0,[z1,z2,z3,z8,z186,z5,z6]),(0,[z173,z1,z2,z3,z132,z5,z6]),(0,[z1,z2,z3,z8,z187,z5,z6]),(1,[z1,z2,z3,z5,z6,z188])],[(0,[z135,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z151,z6])],[(0,[z1,z136,z2,z3,z8,z5,z6]),(0,[z1,z189,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z31,z8,z6]),(0,[z190,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z191,z5,z6]),(1,[z192,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z193,z8,z5,z6]),(0,[z57,z10,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z123,z5,z49,z6])],[(0,[z126,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z194,z3,z8,z5,z6])],[(0,[z10,z1,z66,z2,z3,z8,z6])],[(0,[z195,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(0,[z196,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z6,z14]),(1,[z10,z1,z2,z3,z49,z6])]],
   [[(0,[z135,z1,z2,z3,z5,z6,z14])],[(0,[z1,z136,z2,z3,z5,z6,z14]),(1,[z1,z2,z3,z169,z5,z6])],[(0,[z1,z2,z3,z197,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z109,z6]),(0,[z1,z2,z3,z8,z5,z198,z6])],[(0,[z199,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z200,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z201])],[(0,[z1,z2,z3,z8,z5,z202,z6]),(0,[z203,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z96,z6]),(0,[z9,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z36,z6,z204]),(0,[z15,z1,z2,z3,z11,z5,z6])],[(0,[z1,z2,z3,z8,z205,z5,z6]),(0,[z173,z1,z2,z3,z8,z56,z6]),(0,[z84,z1,z154,z2,z8,z5,z6]),(0,[z1,z154,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z5,z6,z206]),(0,[z10,z1,z2,z3,z8,z8,z6]),(0,[z50,z10,z1,z2,z3,z8,z6]),(1,[z1,z2,z3,z42,z6,z14])],[(0,[z1,z207,z2,z3,z8,z6,z55]),(1,[z1,z2,z101,z48,z5,z6])],[(0,[z165,z1,z2,z31,z8,z5,z6]),(1,[z1,z2,z3,z8,z20,z6])],[(0,[z163,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z39,z56,z6]),(0,[z50,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z208,z5,z6]),(0,[z1,z209,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z210]),(0,[z29,z1,z2,z3,z8,z42,z6])],[(0,[z1,z2,z3,z8,z211,z5,z6]),(0,[z1,z2,z3,z8,z5,z212,z6]),(0,[z1,z2,z3,z8,z5,z6,z213])],[(0,[z1,z66,z2,z3,z8,z214,z6]),(0,[z1,z215,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z216,z8,z5,z6]),(0,[z217,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z151,z6]),(0,[z10,z1,z2,z101,z3,z8,z6])],[(0,[z1,z2,z34,z3,z8,z56,z6])],[(1,[z1,z2,z3,z20,z6,z14]),(0,[z1,z2,z3,z5,z6,z14,z14])]],
   [[(0,[z1,z2,z101,z3,z8,z5,z6])],[(0,[z1,z2,z3,z218,z13,z5,z6]),(0,[z1,z2,z90,z3,z8,z5,z6]),(0,[z93,z1,z2,z219,z8,z5,z6]),(1,[z1,z2,z3,z220,z5,z6])],[(0,[z1,z221,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z222,z5,z6]),(0,[z93,z10,z1,z2,z3,z8,z6]),(0,[z1,z2,z34,z3,z8,z5,z81]),(0,[z1,z2,z3,z4,z5,z6,z14])],[(0,[z1,z2,z3,z25,z8,z38,z6]),(1,[z1,z2,z3,z200,z5,z6]),(1,[z1,z2,z3,z5,z6,z201]),(0,[z223,z1,z2,z3,z8,z5,z6]),(1,[z224,z1,z2,z3,z8,z6])],[(0,[z1,z225,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z226,z5,z6]),(0,[z1,z2,z3,z25,z8,z123,z6])],[(0,[z1,z2,z3,z5,z36,z6,z14]),(0,[z1,z2,z101,z3,z5,z6,z14]),(0,[z1,z227,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z228,z3,z8,z6]),(0,[z35,z1,z2,z3,z8,z5,z60])],[(0,[z1,z2,z3,z229,z8,z5,z6]),(0,[z110,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z34,z3,z8,z5,z109]),(0,[z1,z2,z3,z8,z49,z6,z55]),(0,[z50,z1,z2,z3,z8,z5,z55]),(0,[z230,z1,z2,z3,z8,z5,z6])],[(0,[z1,z231,z2,z3,z8,z5,z6]),(0,[z232,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z172,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z5,z6])],[(0,[z35,z10,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z25,z8,z60,z6])],[(0,[z95,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z62,z6]),(0,[z1,z2,z3,z31,z8,z56,z6])],[(0,[z1,z2,z3,z8,z5,z6,z233]),(1,[z1,z2,z3,z8,z234,z6]),(0,[z1,z2,z228,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z235])],[(0,[z1,z2,z3,z8,z45,z6,z55]),(0,[z236,z1,z2,z3,z8,z5,z6]),(0,[z35,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z237,z8,z5,z6]),(0,[z165,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z5,z238,z6]),(0,[z239,z1,z2,z3,z8,z5,z6])],[(0,[z1,z240,z2,z3,z8,z5,z6]),(0,[z241,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z38,z6,z55]),(0,[z1,z2,z3,z8,z5,z6,z242]),(0,[z1,z2,z3,z8,z243,z5,z6]),(0,[z1,z2,z3,z4,z8,z42,z6]),(1,[z1,z2,z3,z8,z244,z6])],[(0,[z1,z2,z3,z8,z5,z6,z245]),(0,[z1,z2,z3,z8,z5,z246,z6]),(0,[z1,z2,z3,z139,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z60,z6]),(0,[z1,z2,z3,z5,z60,z6,z14])]],
   [[(0,[z1,z2,z3,z67,z8,z42,z6]),(0,[z141,z66,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z62,z6]),(0,[z1,z154,z2,z3,z8,z247,z6]),(0,[z1,z2,z3,z8,z5,z20,z6]),(0,[z1,z2,z3,z53,z4,z5,z6])],[(0,[z126,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z5,z6,z248]),(0,[z110,z1,z2,z3,z8,z249,z6]),(0,[z1,z2,z3,z250,z4,z5,z6])],[(0,[z125,z1,z2,z3,z132,z5,z6])],[(0,[z0,z1,z2,z3,z8,z20,z6]),(0,[z251,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z46,z2,z3,z8,z6])],[(0,[z173,z1,z2,z3,z8,z5,z6]),(0,[z84,z1,z3,z31,z8,z5,z6]),(0,[z15,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z252,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z5,z124])],[],[(0,[z199,z1,z2,z3,z25,z8,z6])],[(0,[z1,z2,z3,z253,z8,z5,z6])],[(1,[z254,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z19,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z81])],[(0,[z1,z2,z3,z8,z255,z5,z6]),(0,[z78,z10,z1,z2,z3,z8,z6]),(0,[z1,z256,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z180,z5,z6])],[(0,[z173,z1,z2,z3,z5,z6,z14]),(0,[z1,z207,z2,z3,z25,z8,z6]),(0,[z110,z227,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z257,z5,z6]),(0,[z1,z2,z3,z8,z42,z42,z6])],[(0,[z258,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z259,z5,z6]),(0,[z1,z2,z3,z8,z260,z6,z55]),(0,[z1,z2,z3,z193,z8,z11,z6]),(0,[z1,z2,z3,z8,z5,z261,z6]),(1,[z1,z262,z3,z8,z5,z6])],[(0,[z263,z1,z2,z3,z8,z5,z6]),(0,[z264,z1,z2,z3,z8,z5,z6]),(0,[z173,z1,z2,z3,z8,z265,z6]),(0,[z1,z2,z3,z266,z8,z5,z6]),(0,[z267,z1,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z8,z20,z6]),(1,[z268,z2,z3,z8,z5,z6]),(0,[z1,z269,z2,z3,z8,z5,z6]),(0,[z1,z2,z34,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z188])],[(0,[z126,z1,z2,z3,z8,z42,z6]),(0,[z1,z131,z2,z3,z8,z5,z151]),(0,[z1,z2,z3,z8,z6,z270,z55])],[(0,[z271,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z11,z42,z6]),(0,[z1,z272,z2,z3,z8,z5,z6])],[(0,[z125,z1,z2,z3,z8,z56,z6]),(1,[z1,z273,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z274,z5,z6]),(0,[z57,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z25,z8,z56,z6])]],
   [[],[(0,[z126,z2,z3,z13,z8,z5,z6]),(0,[z9,z24,z2,z3,z8,z5,z6]),(0,[z275,z10,z1,z2,z3,z8,z6])],[(0,[z1,z66,z2,z3,z4,z5,z6]),(0,[z1,z276,z2,z3,z8,z5,z6]),(0,[z268,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z34,z3,z5,z6,z14]),(0,[z1,z2,z3,z5,z124,z6,z277])],[(0,[z1,z2,z3,z8,z278,z5,z6]),(0,[z279,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z8,z56,z36,z6]),(0,[z1,z46,z3,z58,z8,z5,z6]),(1,[z224,z1,z2,z3,z4,z6]),(0,[z41,z1,z2,z3,z8,z6,z55])],[],[(0,[z1,z2,z101,z48,z8,z5,z6]),(0,[z1,z2,z8,z56,z5,z20,z6]),(0,[z57,z1,z2,z8,z56,z5,z6])],[(1,[z115,z1,z2,z3,z5,z6]),(0,[z280,z1,z2,z3,z8,z5,z6]),(0,[z199,z1,z207,z2,z3,z8,z6])],[(0,[z110,z1,z2,z3,z8,z6,z55]),(0,[z50,z1,z2,z3,z23,z5,z6])],[(0,[z78,z279,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z153,z6,z55]),(0,[z1,z2,z3,z31,z8,z5,z6]),(0,[z1,z2,z3,z58,z8,z56,z6])],[(0,[z141,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z8,z5,z281,z6]),(0,[z1,z2,z3,z8,z39,z42,z6])],[(0,[z136,z2,z3,z13,z8,z5,z6]),(0,[z282,z1,z2,z3,z8,z5,z6]),(0,[z283,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z6,z71]),(0,[z1,z2,z3,z8,z5,z284,z6]),(0,[z1,z2,z3,z285,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z80,z6]),(0,[z286,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z287,z5,z6]),(0,[z84,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z288])],[(0,[z1,z2,z289,z3,z8,z5,z6])],[(0,[z1,z2,z3,z5,z6,z81,z14])],[(0,[z1,z2,z3,z5,z62,z6,z14]),(0,[z1,z2,z3,z290,z8,z5,z6]),(0,[z1,z2,z3,z8,z291,z5,z6]),(0,[z1,z2,z3,z31,z5,z6,z14]),(0,[z1,z2,z3,z4,z8,z5,z14])],[(0,[z292,z1,z2,z3,z8,z5,z6]),(0,[z95,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z293,z8,z5,z6]),(0,[z1,z2,z3,z8,z89,z5,z6]),(0,[z1,z2,z3,z294,z8,z5,z6]),(1,[z1,z2,z3,z8,z6,z295]),(0,[z1,z2,z3,z8,z6,z55,z296])]],
   [[(0,[z9,z1,z2,z216,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z71]),(0,[z165,z1,z2,z3,z25,z8,z6]),(0,[z1,z297,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z298,z6]),(0,[z1,z299,z2,z3,z8,z20,z6])],[(0,[z173,z1,z46,z2,z3,z5,z6]),(0,[z300,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z193,z8,z6])],[(0,[z301,z10,z1,z2,z3,z8,z6])],[(1,[z1,z2,z3,z8,z265,z6]),(0,[z1,z2,z3,z8,z20,z302,z6]),(0,[z1,z2,z303,z3,z8,z5,z6])],[(0,[z1,z2,z3,z97,z8,z5,z6])],[(0,[z0,z1,z136,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z54,z5,z6]),(0,[z304,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z305,z3,z8,z5,z6])],[(0,[z306,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z5,z124,z6,z14])],[(0,[z1,z2,z3,z307,z8,z5,z6])],[(0,[z199,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z31,z8,z42,z6]),(0,[z224,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z178,z42,z6])],[(0,[z24,z1,z2,z3,z8,z20,z6]),(1,[z1,z2,z3,z8,z291,z6]),(0,[z1,z2,z3,z8,z56,z6,z32]),(0,[z1,z308,z2,z3,z8,z5,z6])],[(0,[z1,z154,z2,z3,z4,z5,z6])],[(0,[z125,z1,z2,z3,z8,z5,z6]),(0,[z1,z207,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z8,z5,z6]),(0,[z1,z2,z309,z3,z8,z5,z6])],[(0,[z1,z2,z3,z310,z8,z5,z6]),(0,[z93,z1,z2,z3,z8,z5,z32]),(0,[z1,z2,z3,z25,z8,z124,z6]),(0,[z1,z2,z3,z4,z5,z311,z6])],[(0,[z1,z2,z3,z312,z8,z5,z6]),(0,[z135,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z5,z313,z6]),(0,[z1,z2,z3,z25,z8,z260,z6]),(0,[z1,z314,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z136,z2,z3,z8,z42,z6]),(0,[z279,z2,z3,z8,z5,z62,z6]),(1,[z1,z2,z3,z8,z315,z6]),(0,[z1,z2,z3,z8,z5,z6,z316]),(0,[z1,z2,z3,z8,z5,z317,z6])],[(0,[z1,z2,z3,z5,z20,z6,z14])],[(0,[z1,z2,z3,z318,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z6,z55]),(0,[z319,z1,z2,z3,z8,z5,z6])],[(0,[z279,z1,z2,z3,z8,z6,z55])],[(0,[z320,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z102,z3,z8,z6]),(0,[z1,z2,z3,z8,z5,z124,z6])],[(0,[z1,z2,z3,z8,z321,z5,z6])],[(0,[z1,z2,z3,z8,z322,z5,z6]),(1,[z1,z2,z3,z8,z323,z6]),(0,[z1,z2,z3,z58,z8,z5,z6]),(0,[z1,z131,z2,z3,z8,z6,z55]),(0,[z41,z1,z2,z3,z25,z8,z6])],[(0,[z141,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z131,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z295])],[(0,[z324,z1,z2,z3,z25,z8,z6]),(0,[z319,z1,z2,z3,z5,z6,z14])],[],[(0,[z325,z1,z2,z3,z8,z5,z6]),(0,[z326,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z327,z6]),(0,[z1,z2,z3,z8,z5,z265,z6]),(0,[z1,z2,z3,z8,z56,z6,z81]),(0,[z1,z2,z328,z3,z8,z5,z6])],[(0,[z1,z2,z3,z13,z25,z8,z6]),(0,[z1,z329,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z330]),(0,[z165,z1,z3,z8,z5,z6,z32]),(0,[z1,z2,z3,z58,z5,z6,z14]),(0,[z1,z2,z3,z8,z5,z38,z6]),(0,[z78,z1,z2,z3,z8,z20,z6]),(0,[z10,z1,z2,z3,z48,z8,z6]),(0,[z1,z2,z3,z8,z331,z5,z6])],[(0,[z141,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z92,z8,z45,z6])],[(1,[z1,z2,z3,z218,z5,z6]),(0,[z2,z3,z8,z5,z36,z6,z71]),(0,[z1,z2,z3,z8,z332,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z333])],[(0,[z1,z2,z334,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z8,z5,z6]),(0,[z1,z2,z335,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z277])]],
   [[(1,[z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z4,z123,z5,z6]),(0,[z1,z2,z3,z8,z6,z55,z55])],[(0,[z1,z2,z3,z8,z336,z5,z6])],[(0,[z337,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z153,z6]),(0,[z57,z1,z2,z102,z8,z5,z6]),(0,[z1,z2,z3,z8,z338,z5,z6]),(0,[z1,z2,z3,z339,z4,z5,z6])],[(0,[z95,z1,z2,z3,z5,z6,z14]),(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z72,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z340,z5,z6])],[(0,[z1,z2,z3,z8,z341,z5,z6]),(0,[z1,z2,z101,z3,z8,z42,z6]),(0,[z1,z2,z3,z5,z109,z6,z188])],[(0,[z1,z2,z101,z3,z48,z5,z6]),(1,[z163,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z342,z5,z6]),(1,[z1,z2,z3,z4,z6,z55])],[(0,[z1,z2,z3,z4,z56,z5,z6]),(1,[z129,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z47,z8,z20,z6]),(0,[z337,z1,z2,z3,z5,z6,z14]),(1,[z1,z2,z3,z343,z8,z6])],[(0,[z1,z2,z3,z25,z8,z151,z6]),(1,[z110,z1,z2,z8,z5,z81]),(0,[z1,z2,z344,z3,z8,z5,z6])],[(0,[z125,z1,z46,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z345])],[(0,[z1,z131,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z346,z13,z8,z6]),(0,[z347,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z348,z20,z6]),(0,[z349,z1,z2,z3,z8,z5,z6])],[(0,[z230,z1,z2,z3,z8,z42,z6])],[(0,[z1,z350,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z14,z55])],[(0,[z1,z2,z3,z8,z5,z323,z6]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z125,z135,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z351,z6]),(0,[z1,z2,z3,z25,z8,z6,z14])],[(0,[z95,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z5,z151,z6]),(1,[z1,z2,z3,z5,z6,z277])]],
   [[],[(0,[z1,z2,z102,z8,z5,z20,z6])],[(0,[z1,z2,z3,z352,z8,z5,z6]),(0,[z1,z2,z3,z48,z8,z6,z55]),(0,[z353,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z354,z5,z6]),(1,[z1,z2,z3,z25,z123,z6])],[(0,[z1,z355,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z356,z5,z6]),(0,[z10,z1,z2,z3,z8,z49,z6])],[(0,[z1,z2,z3,z8,z54,z20,z6]),(0,[z1,z2,z3,z357,z8,z5,z6]),(0,[z358,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z359,z6]),(0,[z1,z2,z3,z8,z360,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z14])],[(0,[z1,z2,z3,z8,z361,z5,z6]),(1,[z1,z2,z34,z8,z5,z109]),(0,[z10,z1,z2,z3,z25,z8,z6])],[(0,[z362,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z363]),(0,[z1,z2,z3,z8,z5,z364,z6]),(0,[z1,z365,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z234,z6])],[(0,[z9,z1,z2,z3,z8,z5,z36])],[(0,[z1,z2,z3,z8,z366,z5,z6]),(0,[z1,z2,z3,z8,z5,z367,z6]),(0,[z1,z3,z58,z8,z45,z5,z6])],[(0,[z368,z1,z2,z3,z8,z5,z6]),(0,[z173,z1,z2,z3,z8,z42,z6]),(0,[z1,z131,z2,z3,z25,z8,z6]),(0,[z369,z1,z2,z3,z8,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z6])],[(0,[z370,z1,z2,z3,z8,z5,z6]),(0,[z110,z10,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z6,z81,z296]),(0,[z10,z1,z371,z2,z3,z8,z6])],[(0,[z0,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z34,z67,z8,z5,z6]),(1,[z279,z2,z3,z8,z62,z6]),(0,[z1,z2,z372,z3,z8,z5,z6]),(0,[z373,z1,z2,z3,z8,z6,z55])],[(0,[z1,z2,z3,z13,z8,z6,z55]),(0,[z1,z2,z3,z374,z8,z5,z6]),(0,[z15,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z25,z8,z11,z6]),(0,[z50,z1,z2,z3,z8,z20,z6]),(0,[z1,z365,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z8,z5,z6,z375]),(0,[z10,z1,z2,z3,z67,z8,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z6,z14,z55]),(0,[z1,z2,z3,z8,z60,z6,z55])],[(0,[z1,z2,z3,z376,z8,z5,z6]),(0,[z1,z2,z3,z377,z8,z5,z6]),(0,[z1,z2,z102,z3,z25,z8,z6])],[(0,[z1,z2,z3,z8,z378,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z379]),(0,[z1,z2,z3,z380,z8,z5,z6]),(1,[z1,z131,z3,z8,z5,z151]),(0,[z1,z2,z34,z8,z5,z109,z6])]],
   [[(0,[z135,z1,z3,z8,z45,z5,z6]),(0,[z1,z2,z101,z3,z8,z381,z6]),(0,[z1,z2,z3,z8,z5,z6,z235])],[(0,[z1,z2,z3,z8,z382,z5,z6]),(0,[z1,z2,z3,z8,z56,z212,z6]),(0,[z1,z2,z34,z3,z8,z42,z6])],[(0,[z383,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z6,z167,z55])],[(0,[z1,z2,z384,z3,z8,z5,z6])],[(0,[z9,z1,z2,z3,z385,z5,z6]),(0,[z1,z46,z2,z3,z8,z56,z6]),(1,[z1,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z386,z8,z5,z6]),(0,[z10,z1,z207,z2,z3,z8,z6])],[(0,[z279,z1,z207,z2,z3,z8,z6]),(0,[z387,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z388,z8,z5,z6]),(0,[z1,z2,z64,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z389])],[(0,[z1,z2,z3,z8,z390,z5,z6]),(0,[z391,z1,z2,z3,z8,z5,z6]),(0,[z57,z1,z2,z3,z8,z56,z6])],[(0,[z199,z1,z2,z3,z8,z153,z6]),(0,[z1,z2,z34,z3,z8,z392,z6])],[(1,[z173,z2,z3,z132,z5,z6]),(0,[z199,z10,z1,z2,z3,z8,z6]),(0,[z10,z1,z2,z3,z8,z6,z393])],[(0,[z1,z2,z3,z8,z394,z5,z6]),(0,[z224,z10,z1,z2,z3,z8,z6]),(0,[z1,z395,z2,z3,z4,z5,z6])],[(0,[z10,z126,z1,z2,z3,z8,z6]),(0,[z396,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z397,z6])],[(0,[z1,z2,z3,z8,z257,z5,z6]),(0,[z398,z1,z2,z3,z8,z5,z6])],[],[],[(0,[z1,z2,z3,z8,z56,z38,z6]),(0,[z1,z2,z3,z399,z8,z5,z6]),(0,[z35,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z123,z20,z6])]],
   [[(0,[z1,z2,z3,z400,z8,z5,z6]),(0,[z401,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z42,z6])],[(0,[z1,z2,z3,z8,z5,z6,z402]),(0,[z93,z1,z2,z3,z220,z5,z6]),(0,[z403,z1,z2,z3,z8,z5,z6]),(0,[z404,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z123,z6])],[],[(0,[z84,z1,z2,z3,z8,z56,z6]),(0,[z93,z1,z2,z3,z200,z5,z6])],[(0,[z110,z1,z2,z3,z8,z76,z6])],[(0,[z141,z24,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z151,z6,z201]),(0,[z405,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z60,z6])],[(0,[z125,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z1,z2,z3,z8,z56,z62,z6]),(0,[z1,z2,z406,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z20,z6]),(0,[z1,z2,z3,z25,z5,z6,z14]),(1,[z35,z1,z2,z3,z5,z14])],[(0,[z1,z2,z3,z8,z5,z407,z6]),(1,[z1,z2,z3,z8,z392,z6])],[(0,[z1,z2,z3,z8,z5,z408,z6]),(0,[z1,z2,z3,z409,z8,z5,z6]),(0,[z78,z1,z2,z3,z8,z38,z6]),(0,[z10,z1,z2,z3,z4,z5,z6])],[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z410,z1,z2,z3,z8,z5,z6]),(0,[z279,z1,z2,z3,z4,z5,z6]),(0,[z1,z411,z2,z3,z8,z5,z6])],[(0,[z15,z1,z2,z3,z8,z5,z6])],[(0,[z93,z1,z2,z3,z8,z234,z6]),(0,[z1,z2,z3,z47,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z81,z55]),(0,[z10,z1,z2,z3,z5,z49,z6])],[(0,[z1,z131,z2,z3,z4,z5,z6])],[(0,[z254,z1,z2,z3,z13,z8,z6]),(0,[z1,z2,z3,z412,z8,z5,z6]),(0,[z93,z1,z2,z3,z8,z56,z6])],[(0,[z413,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z102,z3,z8,z6,z55])],[(0,[z0,z1,z2,z3,z5,z6,z14]),(0,[z414,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z415,z6])]],
   [[(0,[z173,z1,z2,z3,z54,z5,z6]),(0,[z15,z1,z2,z3,z5,z6,z14])],[(0,[z10,z141,z1,z2,z3,z8,z6]),(0,[z185,z1,z2,z3,z8,z5,z6]),(0,[z144,z1,z2,z3,z8,z6,z14])],[(0,[z125,z1,z2,z3,z8,z42,z6]),(0,[z416,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z42,z6])],[(0,[z24,z1,z2,z3,z8,z56,z6]),(0,[z417,z1,z2,z3,z8,z56,z6])],[(0,[z1,z2,z3,z8,z5,z6,z418]),(0,[z9,z1,z2,z3,z25,z8,z6]),(1,[z165,z84,z1,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z128,z6]),(0,[z7,z1,z2,z3,z25,z8,z6]),(0,[z419,z1,z2,z3,z8,z5,z6])],[(0,[z1,z66,z2,z3,z8,z20,z6]),(0,[z57,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z53,z4,z8,z6])],[(0,[z141,z1,z2,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z420]),(0,[z1,z2,z3,z4,z45,z5,z6])],[(0,[z1,z2,z3,z8,z54,z5,z6]),(0,[z1,z2,z3,z25,z132,z8,z6]),(0,[z1,z2,z421,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z16,z109,z6])],[(0,[z1,z154,z3,z31,z8,z5,z6]),(0,[z1,z46,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z8,z5,z6,z422])],[(0,[z1,z2,z3,z8,z5,z6,z423]),(0,[z1,z2,z3,z8,z11,z6,z55]),(0,[z1,z2,z3,z8,z42,z424,z6])],[(0,[z1,z2,z3,z132,z8,z20,z6]),(0,[z425,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z58,z8,z42,z6]),(1,[z1,z2,z426,z8,z5,z6]),(0,[z57,z1,z2,z3,z5,z6,z14])],[(0,[z1,z136,z2,z3,z25,z8,z6]),(0,[z95,z1,z2,z67,z8,z5,z6]),(0,[z141,z1,z2,z3,z8,z42,z6]),(0,[z93,z268,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z427,z8,z6])],[(0,[z1,z2,z3,z8,z5,z428,z6]),(0,[z1,z2,z3,z8,z429,z5,z6]),(0,[z110,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z109,z6,z14])],[(1,[z199,z2,z3,z8,z153,z6])],[(0,[z115,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z430,z5,z6]),(0,[z1,z2,z3,z431,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z392,z6])]],
   [[(0,[z1,z2,z3,z8,z260,z153,z6]),(0,[z1,z2,z3,z8,z5,z432,z6]),(0,[z83,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z433,z6])],[(0,[z1,z2,z3,z8,z5,z434,z6]),(0,[z84,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z435,z6])],[(0,[z436,z1,z2,z3,z8,z5,z6])],[],[(0,[z1,z46,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z5,z437,z6])],[(0,[z1,z2,z3,z8,z438,z5,z6])],[(0,[z1,z2,z3,z8,z56,z6,z71]),(0,[z1,z2,z3,z8,z5,z6,z439]),(0,[z1,z299,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z440,z56,z6])],[(0,[z1,z2,z3,z8,z441,z5,z6]),(0,[z9,z1,z355,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z36,z6,z55]),(0,[z84,z1,z2,z3,z5,z6,z14]),(0,[z442,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z443,z3,z8,z6,z55])],[(0,[z1,z2,z3,z8,z5,z302,z6]),(0,[z444,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z48,z4,z5,z6])],[(0,[z1,z2,z445,z3,z8,z5,z6]),(0,[z1,z2,z3,z446,z8,z5,z6]),(0,[z41,z10,z1,z2,z3,z8,z6])],[(0,[z10,z1,z2,z3,z8,z109,z6])],[(0,[z1,z2,z3,z447,z5,z36,z6]),(0,[z93,z1,z2,z3,z8,z5,z6])],[(0,[z448,z1,z2,z3,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z449]),(0,[z1,z2,z3,z450,z8,z5,z6]),(0,[z1,z451,z2,z3,z8,z5,z6])],[(0,[z1,z262,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z130,z14])],[(0,[z126,z1,z3,z13,z8,z5,z6]),(0,[z452,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z453]),(0,[z1,z2,z3,z8,z5,z454,z6])],[(0,[z126,z1,z2,z3,z8,z455,z6]),(0,[z1,z2,z3,z67,z25,z8,z6]),(0,[z1,z154,z2,z3,z8,z20,z6])]],
   [[(0,[z1,z207,z2,z3,z8,z20,z6]),(0,[z10,z1,z2,z3,z8,z6,z32]),(0,[z349,z1,z2,z3,z8,z42,z6])],[(0,[z417,z1,z2,z3,z8,z5,z6]),(0,[z24,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z447,z5,z6]),(0,[z1,z456,z2,z3,z8,z5,z6]),(0,[z93,z1,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z13,z4,z5,z6]),(0,[z1,z2,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z457,z8,z5,z6]),(0,[z1,z3,z8,z260,z5,z38,z6]),(0,[z1,z2,z3,z8,z123,z5,z6]),(0,[z35,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z346,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z333]),(0,[z1,z2,z3,z8,z458,z5,z6]),(0,[z1,z2,z40,z3,z8,z5,z6]),(0,[z144,z1,z2,z3,z8,z5,z6])],[(0,[z2,z3,z13,z8,z5,z6,z71]),(0,[z459,z1,z2,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z8,z6,z55]),(0,[z460,z1,z2,z3,z8,z56,z6]),(0,[z12,z10,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z117,z5,z6,z14])],[(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z6,z14])],[(0,[z125,z173,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z153,z5,z6,z14]),(0,[z461,z1,z2,z3,z8,z5,z6]),(0,[z84,z1,z2,z3,z8,z315,z6]),(0,[z110,z1,z2,z3,z139,z5,z6]),(0,[z1,z2,z3,z53,z8,z5,z6]),(0,[z462,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z463])],[(0,[z464,z1,z2,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z465,z5,z6]),(0,[z1,z2,z3,z8,z42,z49,z6])],[(0,[z466,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z467,z5,z6]),(0,[z1,z2,z3,z25,z8,z45,z6])],[(0,[z125,z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z8,z468,z5,z6]),(0,[z1,z2,z3,z8,z56,z5,z6]),(0,[z144,z1,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z8,z5,z469,z6]),(0,[z1,z470,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z471,z6]),(0,[z1,z2,z3,z8,z56,z124,z6])],[(0,[z1,z2,z3,z8,z5,z472,z6]),(1,[z1,z2,z216,z8,z5,z6]),(0,[z135,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z56,z260,z6]),(0,[z473,z1,z2,z3,z8,z20,z6]),(1,[z1,z2,z3,z474,z8,z6]),(1,[z1,z2,z3,z25,z6,z14]),(0,[z1,z2,z3,z4,z475,z5,z6])],[(0,[z126,z1,z2,z3,z25,z8,z6]),(0,[z1,z136,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z54,z56,z6])],[(0,[z1,z207,z3,z8,z5,z38,z6]),(0,[z1,z2,z3,z476,z5,z124,z6])],[(1,[z1,z2,z3,z476,z5,z6])],[(0,[z1,z2,z3,z8,z477,z5,z6]),(0,[z1,z2,z3,z8,z5,z478,z6]),(0,[z479,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z294,z8,z6]),(0,[z224,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z2,z3,z132,z8,z54,z5,z6]),(0,[z1,z480,z2,z3,z8,z5,z6]),(0,[z481,z1,z2,z3,z8,z5,z6]),(0,[z482,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z49,z6]),(1,[z1,z2,z3,z8,z483,z6])],[(0,[z1,z2,z3,z8,z20,z6,z296]),(0,[z1,z2,z3,z8,z5,z484,z6]),(0,[z1,z2,z3,z8,z6,z485,z55])],[(0,[z1,z2,z3,z8,z486,z5,z6]),(0,[z1,z2,z3,z487,z8,z5,z6]),(0,[z1,z2,z3,z8,z488,z5,z6]),(0,[z78,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z8,z6])],[(0,[z489,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z490,z8,z5,z6]),(0,[z1,z2,z3,z491,z8,z5,z6])],[(0,[z78,z1,z2,z3,z8,z260,z6]),(0,[z1,z2,z3,z8,z440,z5,z6]),(0,[z50,z1,z2,z3,z8,z56,z6])],[(0,[z1,z2,z3,z8,z45,z20,z6]),(0,[z1,z371,z2,z3,z8,z5,z6])],[(0,[z1,z2,z492,z3,z8,z5,z6]),(0,[z95,z2,z3,z67,z8,z5,z6]),(0,[z165,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z101,z3,z8,z341,z6]),(0,[z192,z1,z2,z3,z8,z5,z6])],[(0,[z0,z24,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z153,z6]),(0,[z135,z1,z2,z3,z45,z5,z6]),(1,[z1,z2,z3,z8,z493,z6]),(0,[z1,z2,z494,z3,z8,z5,z6])],[(0,[z279,z1,z2,z3,z8,z153,z6]),(0,[z10,z10,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z495,z8,z5,z6])],[(1,[z1,z2,z3,z8,z496,z6]),(0,[z275,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z244,z60,z6])],[(0,[z497,z1,z2,z3,z8,z5,z6]),(0,[z1,z498,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z54,z6])],[(0,[z1,z499,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z390,z42,z6])],[(0,[z1,z2,z3,z4,z8,z6,z55])],[(0,[z1,z2,z3,z8,z315,z5,z6]),(0,[z1,z2,z3,z8,z5,z500,z6]),(0,[z110,z1,z2,z3,z180,z5,z6])],[(0,[z1,z2,z3,z8,z5,z501,z6]),(0,[z1,z2,z3,z67,z8,z6,z55]),(0,[z1,z2,z3,z8,z502,z5,z6]),(0,[z1,z2,z3,z8,z62,z6,z55]),(0,[z165,z84,z1,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z42,z124])]],
   [[(1,[z1,z2,z3,z8,z6,z204])],[(0,[z135,z173,z1,z2,z3,z5,z6]),(0,[z9,z2,z3,z8,z5,z6,z71]),(1,[z1,z2,z3,z8,z222,z6]),(0,[z1,z2,z101,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z348,z5,z6])],[(0,[z1,z2,z3,z67,z4,z5,z6]),(0,[z460,z1,z2,z3,z8,z5,z6]),(1,[z1,z207,z3,z8,z38,z6]),(0,[z1,z2,z3,z8,z5,z6,z270])],[(0,[z503,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z6])],[(0,[z504,z1,z2,z3,z8,z5,z6]),(0,[z135,z1,z2,z3,z58,z5,z6]),(0,[z1,z2,z3,z8,z260,z20,z6]),(0,[z163,z1,z2,z3,z48,z8,z6]),(0,[z1,z2,z102,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z123,z5,z6])],[(0,[z505,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z151,z6]),(0,[z506,z1,z2,z3,z8,z5,z6])],[(0,[z10,z1,z2,z34,z3,z8,z6])],[(0,[z10,z279,z1,z2,z3,z8,z6]),(0,[z507,z1,z2,z3,z8,z5,z6]),(0,[z35,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z476,z8,z5,z6])],[(0,[z1,z2,z508,z3,z8,z5,z6]),(0,[z1,z509,z2,z3,z8,z5,z6]),(0,[z1,z2,z34,z31,z8,z5,z6]),(0,[z165,z1,z131,z3,z8,z5,z6]),(0,[z510,z1,z2,z3,z8,z5,z6]),(0,[z93,z1,z2,z426,z8,z5,z6]),(1,[z93,z1,z3,z8,z5,z32]),(1,[z473,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z123,z5,z6,z14]),(0,[z1,z2,z3,z8,z5,z483,z6]),(0,[z1,z2,z3,z8,z124,z6,z55])],[(0,[z1,z2,z3,z8,z214,z5,z6]),(0,[z1,z2,z3,z31,z25,z8,z6]),(1,[z1,z2,z3,z4,z5,z60]),(0,[z1,z2,z3,z8,z42,z6,z55])],[(0,[z1,z273,z2,z3,z8,z54,z6]),(0,[z1,z2,z3,z8,z5,z511,z6]),(0,[z1,z2,z3,z8,z153,z38,z6]),(0,[z1,z2,z512,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z56,z6,z14])],[(0,[z1,z2,z3,z8,z5,z6,z389]),(0,[z10,z1,z2,z3,z8,z36,z6]),(0,[z301,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z513,z5,z6]),(0,[z1,z2,z406,z3,z8,z42,z6])],[(0,[z126,z1,z2,z3,z8,z6,z55]),(0,[z1,z514,z2,z3,z8,z5,z6]),(0,[z41,z1,z2,z3,z8,z20,z6]),(1,[z1,z2,z3,z8,z348,z6])],[(0,[z10,z173,z1,z2,z3,z8,z6])],[(0,[z0,z1,z2,z3,z8,z42,z6]),(0,[z2,z3,z8,z153,z5,z62,z6]),(0,[z135,z1,z2,z3,z25,z8,z6]),(1,[z1,z2,z3,z8,z381,z6]),(0,[z1,z2,z3,z8,z56,z56,z6]),(0,[z1,z2,z3,z515,z8,z5,z6])],[(0,[z1,z516,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z493,z6]),(0,[z15,z1,z2,z3,z8,z42,z6])]],
   [[(0,[z10,z1,z2,z3,z58,z8,z6]),(0,[z15,z1,z2,z3,z48,z5,z6]),(1,[z1,z2,z3,z8,z517,z6])],[(0,[z518,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z153,z20,z6]),(0,[z1,z2,z445,z3,z8,z45,z6]),(0,[z1,z2,z3,z25,z8,z354,z6])],[(0,[z1,z2,z3,z8,z5,z496,z6]),(0,[z1,z2,z3,z8,z20,z6,z55]),(1,[z1,z2,z3,z6,z519,z14]),(0,[z50,z1,z2,z3,z8,z5,z6])],[(0,[z1,z66,z2,z3,z8,z323,z6]),(0,[z1,z2,z3,z134,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z311,z6])],[(0,[z1,z2,z3,z8,z5,z6,z520]),(0,[z137,z1,z2,z3,z4,z5,z6])],[(0,[z254,z1,z2,z3,z8,z5,z6]),(0,[z173,z1,z2,z3,z8,z6,z55]),(0,[z10,z24,z1,z2,z3,z8,z6]),(0,[z1,z2,z521,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z58,z5,z6]),(0,[z1,z2,z3,z8,z109,z6,z522])],[(0,[z9,z1,z2,z77,z8,z5,z6]),(0,[z9,z1,z2,z3,z8,z438,z6]),(0,[z78,z1,z2,z3,z8,z56,z6]),(0,[z15,z1,z2,z8,z11,z5,z6]),(1,[z1,z2,z3,z8,z6,z522])],[(0,[z383,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z204]),(0,[z1,z131,z3,z31,z8,z5,z6]),(0,[z1,z523,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z260,z5,z6]),(0,[z1,z524,z2,z3,z8,z5,z6]),(0,[z50,z1,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z5,z6,z32,z14]),(0,[z1,z2,z3,z8,z42,z525,z6]),(0,[z1,z2,z3,z8,z525,z5,z6])],[(0,[z1,z2,z3,z5,z6,z71,z14]),(0,[z1,z2,z3,z8,z526,z5,z6]),(0,[z1,z2,z3,z8,z33,z5,z6]),(0,[z57,z1,z2,z3,z8,z42,z6]),(1,[z1,z2,z3,z56,z6,z14])],[(0,[z527,z1,z2,z3,z8,z5,z6]),(0,[z528,z1,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z8,z493,z6])],[(0,[z1,z2,z3,z8,z54,z42,z6]),(0,[z1,z207,z2,z3,z8,z38,z6]),(0,[z1,z2,z529,z3,z8,z5,z6])],[(0,[z1,z66,z2,z3,z8,z56,z6]),(0,[z1,z2,z530,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z531,z6]),(0,[z1,z2,z3,z8,z249,z5,z6]),(0,[z1,z2,z34,z3,z8,z6,z55])],[(0,[z50,z1,z2,z3,z8,z5,z124])],[(0,[z1,z2,z3,z8,z532,z5,z6]),(0,[z199,z1,z2,z3,z8,z62,z6]),(0,[z1,z2,z3,z8,z5,z533,z6])]],
   [[(0,[z84,z1,z2,z34,z8,z5,z6]),(1,[z1,z2,z3,z8,z6,z534])],[(0,[z199,z78,z1,z2,z3,z8,z6]),(0,[z1,z535,z2,z3,z8,z5,z6])],[(0,[z24,z1,z2,z3,z8,z5,z71]),(0,[z1,z154,z2,z3,z8,z291,z6]),(0,[z1,z2,z3,z8,z5,z6,z536]),(0,[z1,z2,z3,z5,z6,z14,z55])],[(0,[z1,z2,z3,z8,z537,z5,z6]),(0,[z1,z2,z3,z132,z8,z56,z6]),(0,[z538,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z539])],[(0,[z1,z2,z101,z3,z25,z8,z6]),(0,[z28,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z540,z5,z6]),(0,[z1,z46,z2,z3,z8,z222,z6]),(0,[z1,z2,z3,z8,z5,z541,z6]),(0,[z1,z2,z3,z4,z5,z6,z55])],[(0,[z1,z2,z3,z542,z8,z5,z6]),(0,[z84,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z543,z5,z6]),(0,[z1,z2,z3,z5,z151,z6,z14]),(0,[z1,z2,z3,z8,z5,z381,z6]),(0,[z1,z2,z3,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z544])],[(0,[z9,z10,z1,z2,z3,z8,z6]),(0,[z168,z1,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z31,z8,z6,z55]),(0,[z1,z2,z545,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z342,z6])],[(0,[z1,z2,z3,z8,z546,z5,z6]),(0,[z24,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z250,z8,z5,z6]),(0,[z133,z1,z2,z3,z8,z5,z6])],[(0,[z1,z136,z3,z8,z5,z6,z32]),(0,[z95,z1,z2,z3,z8,z278,z6]),(0,[z93,z1,z2,z3,z8,z397,z6]),(0,[z10,z1,z2,z3,z8,z20,z6]),(0,[z35,z1,z2,z3,z5,z6,z14]),(0,[z1,z547,z2,z3,z8,z5,z6])],[(0,[z279,z1,z2,z3,z8,z62,z6]),(0,[z279,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z548,z5,z6]),(0,[z1,z2,z3,z8,z5,z549,z6]),(0,[z110,z129,z2,z3,z8,z5,z6]),(0,[z182,z10,z1,z2,z3,z8,z6]),(1,[z1,z2,z3,z8,z6,z519])],[(0,[z1,z2,z3,z8,z5,z550,z6]),(0,[z84,z1,z2,z3,z8,z496,z6])],[(0,[z126,z0,z2,z3,z8,z5,z6]),(0,[z95,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z385,z8,z5,z6]),(0,[z551,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z244,z5,z6])],[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z552,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z346,z8,z6]),(1,[z1,z2,z3,z385,z5,z6]),(0,[z553,z1,z2,z3,z8,z5,z6]),(0,[z1,z131,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z522])]],
   [[(0,[z93,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z34,z3,z8,z338,z6])],[(0,[z126,z1,z2,z3,z8,z366,z6]),(0,[z1,z3,z13,z8,z5,z6,z32]),(0,[z135,z1,z2,z3,z4,z5,z6]),(0,[z448,z1,z2,z3,z8,z42,z6])],[(0,[z1,z136,z2,z3,z4,z5,z6]),(0,[z145,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z6,z534]),(0,[z1,z2,z3,z8,z6,z55,z330])],[(0,[z1,z554,z2,z3,z8,z5,z6]),(0,[z1,z555,z2,z3,z8,z5,z6]),(0,[z110,z1,z262,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z6,z81])],[(0,[z199,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z556,z3,z8,z5,z6])],[(1,[z1,z2,z445,z3,z8,z6]),(0,[z1,z2,z3,z220,z8,z5,z6])],[(0,[z24,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z5,z6,z557])],[(0,[z1,z154,z2,z3,z8,z56,z6]),(0,[z1,z558,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z109,z6]),(0,[z1,z2,z3,z8,z123,z42,z6]),(0,[z35,z1,z2,z3,z8,z42,z6])],[(0,[z1,z559,z2,z3,z8,z5,z6]),(0,[z173,z1,z2,z3,z25,z8,z6]),(0,[z1,z207,z2,z3,z8,z56,z6]),(0,[z1,z131,z2,z3,z8,z5,z32]),(0,[z560,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z534])],[(0,[z1,z2,z3,z8,z561,z5,z6]),(0,[z1,z2,z3,z8,z5,z562,z6])],[(0,[z24,z2,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z5,z36,z6,z563])],[(0,[z1,z66,z2,z3,z8,z5,z6]),(0,[z78,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z253,z25,z8,z6]),(0,[z69,z1,z2,z3,z4,z5,z6])],[(0,[z564,z1,z2,z3,z8,z5,z6])],[(1,[z0,z136,z3,z8,z5,z6]),(0,[z565,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z119]),(0,[z10,z1,z2,z3,z4,z8,z6]),(0,[z1,z566,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z8,z5,z60])],[(0,[z1,z2,z3,z8,z567,z5,z6]),(0,[z1,z2,z3,z8,z56,z42,z6])],[(1,[z1,z2,z3,z4,z20,z6])]],
   [[(0,[z1,z2,z3,z8,z568,z5,z6]),(0,[z1,z2,z3,z569,z8,z5,z6]),(0,[z1,z2,z3,z8,z30,z36,z6]),(0,[z570,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z34,z3,z25,z8,z6])],[(0,[z1,z2,z3,z8,z5,z571,z6]),(0,[z1,z66,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z132,z8,z5,z6]),(0,[z572,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z427,z8,z5,z6]),(1,[z1,z2,z3,z47,z8,z6])],[(1,[z1,z2,z3,z8,z455,z6]),(0,[z1,z2,z3,z63,z8,z5,z6]),(0,[z118,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z63,z5,z151,z6]),(0,[z110,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6])],[(0,[z573,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z153,z5,z6]),(0,[z1,z2,z3,z8,z574,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z519])],[(0,[z575,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z576,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z519,z14])],[(0,[z1,z2,z3,z8,z577,z5,z6]),(0,[z1,z2,z3,z8,z5,z435,z6]),(0,[z1,z535,z2,z3,z8,z56,z6])],[(0,[z1,z66,z2,z34,z8,z5,z6]),(0,[z1,z2,z3,z132,z5,z6,z14]),(0,[z1,z2,z3,z8,z260,z62,z6]),(0,[z1,z2,z3,z58,z8,z6,z55]),(0,[z78,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z101,z3,z4,z5,z6]),(0,[z223,z1,z2,z3,z8,z6,z55])],[(0,[z578,z1,z2,z3,z8,z5,z6]),(0,[z141,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z579,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z48,z8,z6]),(0,[z1,z2,z3,z25,z8,z580,z6]),(0,[z1,z2,z581,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z424,z6]),(0,[z1,z2,z3,z343,z8,z5,z6])],[(0,[z10,z1,z2,z3,z13,z8,z6]),(0,[z1,z2,z3,z447,z8,z5,z6]),(0,[z1,z2,z219,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z109,z6])],[(0,[z10,z1,z2,z3,z8,z6,z71]),(0,[z1,z2,z3,z8,z5,z6,z463]),(0,[z1,z2,z3,z48,z8,z20,z6])],[(1,[z1,z2,z3,z8,z278,z6]),(0,[z1,z2,z3,z8,z5,z582,z6])],[(0,[z583,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z77,z3,z8,z5,z6]),(0,[z1,z584,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z45,z56,z6]),(0,[z1,z2,z3,z8,z475,z5,z6])],[(0,[z95,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z5,z585,z6]),(0,[z165,z1,z2,z3,z8,z56,z6]),(1,[z1,z2,z3,z8,z6,z296]),(1,[z10,z1,z2,z3,z6,z14]),(0,[z1,z2,z3,z8,z433,z5,z6])],[(0,[z2,z3,z67,z8,z5,z6,z71]),(0,[z586,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z587,z6]),(1,[z1,z2,z3,z25,z8,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z588]),(0,[z1,z2,z3,z8,z5,z6,z589])],[(0,[z1,z2,z3,z218,z8,z5,z6]),(0,[z1,z2,z3,z590,z8,z5,z6]),(0,[z1,z2,z3,z8,z298,z5,z6]),(0,[z591,z1,z2,z3,z8,z5,z6])],[(0,[z126,z1,z2,z3,z4,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z132,z8,z42,z6]),(0,[z9,z1,z2,z3,z169,z5,z6]),(0,[z224,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z6,z485])],[],[(0,[z1,z2,z3,z13,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z592,z6]),(0,[z1,z2,z3,z8,z593,z5,z6]),(0,[z1,z2,z3,z8,z5,z594,z6]),(0,[z1,z154,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z595,z5,z6])],[(0,[z1,z207,z2,z3,z8,z5,z6]),(0,[z596,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z55,z235])],[(0,[z1,z2,z3,z45,z5,z6,z14]),(0,[z1,z2,z3,z597,z8,z5,z6]),(0,[z35,z1,z2,z3,z8,z5,z14])],[(1,[z126,z3,z13,z8,z5,z6]),(0,[z199,z1,z2,z3,z5,z6,z14]),(0,[z1,z207,z2,z3,z8,z260,z6]),(0,[z1,z2,z3,z5,z6,z598,z14])],[(0,[z9,z1,z2,z3,z8,z75,z6]),(1,[z1,z2,z3,z8,z249,z6])],[(0,[z1,z2,z3,z8,z5,z455,z6]),(0,[z599,z1,z2,z3,z8,z5,z6]),(0,[z9,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z397,z5,z6])],[(0,[z173,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z600,z8,z5,z6]),(0,[z1,z154,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z5,z6,z601])],[(0,[z1,z46,z2,z3,z45,z5,z6]),(0,[z1,z207,z2,z3,z5,z6,z14]),(0,[z596,z1,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z602,z8,z5,z6]),(0,[z603,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z5,z55])],[(0,[z95,z1,z66,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z604])],[(0,[z279,z1,z2,z3,z8,z5,z6]),(0,[z9,z1,z90,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z36,z6]),(1,[z1,z154,z31,z8,z5,z6]),(0,[z1,z2,z3,z25,z8,z49,z6]),(0,[z1,z605,z2,z3,z8,z5,z6])]],
   [[(0,[z606,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z607])],[(0,[z1,z2,z3,z608,z8,z5,z6]),(0,[z125,z1,z2,z3,z25,z8,z6]),(0,[z473,z1,z2,z3,z8,z5,z6]),(0,[z551,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z25,z8,z6]),(0,[z1,z2,z3,z5,z6,z589,z14])],[(0,[z1,z2,z3,z8,z5,z609,z6]),(0,[z0,z136,z2,z3,z8,z5,z6]),(0,[z1,z610,z2,z3,z8,z5,z6]),(1,[z227,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z310,z25,z8,z6])],[(0,[z1,z2,z3,z8,z5,z6,z611]),(0,[z1,z2,z34,z3,z4,z5,z6]),(1,[z1,z2,z3,z8,z6,z393]),(0,[z1,z314,z2,z3,z25,z8,z6])],[(0,[z1,z2,z3,z8,z612,z5,z6]),(1,[z1,z2,z3,z8,z341,z6]),(0,[z41,z1,z2,z3,z8,z56,z6])],[(0,[z141,z2,z3,z8,z5,z6,z71]),(0,[z1,z613,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z49,z6]),(1,[z1,z2,z3,z51,z5,z6])],[(0,[z1,z2,z3,z614,z8,z5,z6]),(0,[z1,z2,z3,z615,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z616,z6]),(0,[z1,z617,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z296]),(0,[z1,z2,z530,z3,z5,z6,z14])],[(0,[z199,z2,z3,z8,z153,z5,z6]),(0,[z10,z1,z2,z3,z8,z38,z6]),(0,[z1,z2,z3,z8,z5,z6,z618]),(0,[z50,z1,z2,z3,z8,z42,z6])],[(1,[z9,z2,z3,z8,z5,z71]),(0,[z1,z2,z3,z8,z20,z36,z6]),(0,[z110,z1,z2,z3,z8,z56,z6]),(1,[z1,z2,z3,z8,z6,z122])],[(1,[z1,z2,z3,z8,z30,z6]),(0,[z619,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z123,z6])],[(0,[z1,z2,z3,z474,z8,z56,z6])],[(0,[z141,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z8,z5,z6,z620]),(0,[z1,z2,z3,z8,z45,z5,z6]),(0,[z15,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z339,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z485])],[(0,[z165,z1,z2,z3,z8,z5,z6]),(0,[z110,z1,z2,z3,z8,z5,z81])],[(0,[z1,z2,z3,z8,z5,z621,z6]),(0,[z1,z2,z3,z8,z298,z151,z6]),(0,[z10,z1,z2,z3,z8,z60,z6]),(0,[z1,z2,z3,z8,z513,z5,z6]),(0,[z622,z1,z2,z3,z8,z5,z6])],[(0,[z10,z1,z2,z3,z8,z62,z6]),(0,[z623,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z109,z6,z55])],[(0,[z1,z2,z3,z31,z4,z5,z6]),(1,[z1,z2,z3,z25,z4,z6]),(1,[z1,z2,z3,z8,z6,z55])]],
   [[(0,[z624,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z427,z8,z11,z6]),(0,[z625,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z51,z8,z5,z6])],[(0,[z165,z1,z154,z3,z8,z5,z6]),(0,[z10,z165,z1,z2,z3,z8,z6]),(0,[z135,z10,z1,z2,z3,z8,z6]),(0,[z110,z1,z2,z3,z8,z5,z109]),(0,[z1,z2,z3,z8,z42,z109,z6])],[(0,[z1,z2,z3,z8,z5,z626,z6]),(0,[z1,z2,z3,z627,z8,z5,z6]),(0,[z165,z1,z2,z3,z5,z6,z14]),(1,[z15,z1,z2,z11,z5,z6])],[(0,[z1,z46,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z628,z8,z5,z6])],[(0,[z1,z136,z131,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z629]),(0,[z1,z2,z3,z67,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z6,z630]),(1,[z1,z2,z3,z8,z631,z6]),(1,[z1,z2,z8,z56,z20,z6])],[(0,[z98,z1,z2,z3,z8,z20,z6]),(0,[z195,z10,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z5,z6,z632]),(0,[z173,z1,z2,z3,z8,z441,z6]),(0,[z1,z2,z3,z8,z42,z6,z32]),(1,[z1,z2,z3,z8,z33,z6]),(0,[z1,z2,z102,z3,z8,z20,z6]),(0,[z35,z1,z2,z3,z8,z483,z6])],[(0,[z1,z2,z3,z8,z6,z71,z55]),(1,[z135,z1,z3,z45,z5,z6])],[(0,[z633,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z580,z6])],[(0,[z1,z2,z3,z8,z260,z5,z6]),(1,[z10,z1,z2,z3,z25,z6])],[(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z3,z8,z5,z6,z393])],[(0,[z634,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z635,z5,z6]),(0,[z84,z1,z2,z8,z5,z6,z81]),(0,[z1,z2,z3,z8,z517,z5,z6])],[(0,[z1,z2,z3,z8,z636,z5,z6]),(0,[z1,z2,z3,z3,z8,z56,z6])],[(0,[z1,z2,z3,z8,z637,z5,z6]),(0,[z10,z1,z2,z3,z8,z6,z14]),(0,[z1,z2,z3,z8,z5,z6,z638]),(1,[z1,z2,z3,z8,z525,z6])]],
   [[(0,[z1,z2,z3,z8,z639,z5,z6]),(0,[z1,z2,z3,z54,z5,z6,z14]),(0,[z1,z2,z3,z8,z20,z6,z32]),(0,[z1,z2,z3,z8,z5,z6,z122]),(0,[z163,z10,z1,z2,z3,z8,z6])],[(0,[z125,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z25,z8,z6,z55])],[(0,[z41,z1,z2,z3,z8,z5,z6]),(0,[z640,z1,z2,z3,z8,z5,z6]),(0,[z641,z1,z2,z3,z8,z56,z6]),(1,[z1,z2,z3,z8,z338,z6])],[(0,[z93,z1,z2,z3,z8,z5,z151]),(0,[z1,z2,z3,z8,z11,z20,z6]),(0,[z10,z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z642,z3,z8,z5,z6])],[(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z279,z1,z2,z3,z8,z56,z6]),(0,[z643,z1,z2,z3,z8,z5,z6]),(0,[z324,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z151,z6,z55]),(0,[z1,z2,z3,z25,z8,z644,z6]),(0,[z1,z2,z3,z25,z4,z5,z6]),(0,[z1,z2,z309,z3,z4,z5,z6])],[(0,[z645,z1,z2,z3,z8,z5,z6])],[(0,[z646,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z6,z55])],[(0,[z373,z1,z2,z3,z8,z5,z6]),(0,[z1,z131,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z8,z5,z6,z55])],[(0,[z1,z2,z3,z13,z8,z5,z6]),(0,[z1,z647,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z474,z8,z5,z6]),(0,[z442,z1,z2,z3,z25,z8,z6]),(0,[z648,z1,z2,z3,z8,z5,z6]),(0,[z41,z1,z2,z3,z5,z6,z14])],[(1,[z1,z2,z3,z8,z247,z6]),(0,[z1,z649,z2,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z6,z55]),(0,[z1,z650,z2,z3,z8,z5,z6])],[(0,[z15,z1,z2,z3,z8,z6,z55]),(0,[z10,z353,z1,z2,z3,z8,z6])],[(1,[z297,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z651,z8,z5,z6]),(0,[z110,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z8,z5,z109,z6,z81])],[(0,[z1,z2,z3,z8,z5,z631,z6]),(0,[z1,z2,z3,z8,z5,z6,z652]),(0,[z1,z2,z3,z8,z60,z6,z295])],[(0,[z141,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z8,z441,z6])],[(1,[z1,z2,z3,z8,z214,z6]),(0,[z24,z2,z3,z8,z5,z36,z6]),(0,[z1,z2,z3,z8,z5,z653,z6]),(0,[z1,z2,z3,z8,z654,z5,z6])]],
   [[(0,[z1,z66,z2,z3,z8,z42,z6]),(0,[z78,z1,z207,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z6,z81])],[(0,[z15,z1,z2,z3,z8,z631,z6]),(0,[z1,z2,z3,z8,z5,z6,z655]),(0,[z1,z2,z3,z8,z5,z6,z598])],[(0,[z1,z2,z3,z656,z8,z5,z6]),(0,[z1,z131,z3,z8,z5,z151,z6]),(0,[z110,z1,z2,z34,z8,z5,z6])],[(0,[z1,z46,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z4,z5,z6,z32]),(0,[z1,z2,z3,z8,z657,z5,z6]),(0,[z1,z2,z3,z4,z42,z5,z6]),(0,[z1,z395,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z366,z6]),(0,[z95,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z5,z658,z6]),(0,[z1,z2,z3,z11,z5,z6,z14])],[(0,[z659,z1,z2,z3,z8,z5,z6]),(0,[z660,z1,z2,z3,z8,z5,z6]),(0,[z57,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z8,z39,z6,z81])],[(0,[z141,z95,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z661,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z6]),(1,[z1,z2,z3,z4,z56,z6]),(0,[z35,z1,z2,z3,z8,z517,z6]),(0,[z1,z2,z3,z5,z6,z519,z14]),(0,[z1,z2,z3,z8,z5,z6,z662])],[(0,[z1,z2,z3,z8,z5,z6,z563]),(0,[z1,z2,z48,z8,z11,z5,z6]),(0,[z110,z1,z2,z3,z8,z42,z6])],[(0,[z1,z2,z3,z8,z153,z42,z6]),(0,[z538,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z172,z5,z109,z6])],[(0,[z10,z84,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z663,z8,z5,z6])],[(0,[z141,z1,z66,z2,z8,z5,z6]),(0,[z1,z2,z101,z3,z11,z5,z6]),(1,[z1,z72,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z664,z6]),(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z114,z2,z3,z8,z5,z6])],[(0,[z24,z2,z3,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z117,z5,z6]),(0,[z1,z2,z3,z343,z8,z42,z6])],[(0,[z1,z2,z3,z56,z5,z6,z14]),(1,[z144,z1,z2,z3,z6,z14])],[(0,[z0,z1,z3,z13,z8,z5,z6]),(0,[z665,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z666,z6]),(1,[z1,z2,z3,z53,z8,z6])]],
   [[(0,[z667,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z668,z6]),(0,[z669,z1,z2,z3,z8,z5,z6]),(0,[z641,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z670]),(0,[z1,z2,z3,z8,z5,z247,z6]),(0,[z10,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z6,z6])],[(1,[z1,z2,z3,z8,z438,z6]),(0,[z84,z1,z2,z3,z8,z6,z55]),(1,[z1,z2,z102,z8,z20,z6]),(0,[z10,z1,z2,z3,z8,z124,z6])],[(0,[z1,z2,z3,z671,z8,z5,z6]),(0,[z672,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z2,z3,z8,z260,z6]),(0,[z10,z1,z131,z2,z3,z8,z6]),(0,[z1,z2,z3,z48,z8,z56,z6]),(0,[z1,z2,z3,z8,z20,z183,z6]),(0,[z1,z2,z3,z4,z5,z6,z81])],[(0,[z126,z1,z136,z3,z8,z5,z6]),(0,[z135,z1,z2,z3,z8,z20,z6])],[(0,[z673,z1,z2,z3,z8,z5,z6]),(0,[z1,z136,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z674,z8,z5,z6]),(0,[z1,z2,z675,z3,z8,z5,z6]),(1,[z1,z355,z3,z8,z5,z6]),(0,[z1,z131,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z25,z8,z109,z6])],[(0,[z0,z2,z3,z8,z5,z6,z71]),(0,[z199,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z56,z336,z6]),(0,[z10,z1,z2,z3,z5,z6,z14]),(0,[z676,z1,z2,z3,z8,z5,z6])],[(0,[z279,z1,z2,z3,z5,z6,z14]),(0,[z24,z1,z2,z3,z8,z5,z36]),(1,[z1,z2,z3,z5,z6,z563]),(0,[z224,z1,z2,z3,z8,z42,z6])],[(1,[z1,z2,z3,z294,z8,z6])],[(0,[z1,z2,z3,z677,z8,z5,z6]),(0,[z1,z154,z2,z3,z8,z42,z6])],[(1,[z125,z2,z3,z54,z5,z6]),(0,[z1,z207,z2,z3,z8,z42,z6]),(0,[z1,z131,z2,z3,z5,z6,z14]),(0,[z1,z678,z2,z3,z8,z5,z6])],[(0,[z679,z1,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z58,z5,z6]),(0,[z93,z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z25,z8,z6,z32])],[(0,[z1,z2,z3,z13,z8,z56,z6]),(0,[z0,z1,z2,z3,z25,z8,z6]),(0,[z680,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z6,z152]),(0,[z1,z681,z2,z3,z8,z5,z6]),(0,[z682,z1,z2,z3,z8,z5,z6]),(0,[z1,z451,z2,z3,z8,z6,z55])],[(0,[z683,z1,z2,z3,z8,z5,z6]),(0,[z684,z1,z2,z3,z8,z5,z6]),(0,[z10,z1,z566,z2,z3,z8,z6])],[(0,[z1,z2,z3,z47,z25,z8,z6])]],
   [[(0,[z1,z273,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z62,z38,z6]),(1,[z1,z2,z219,z8,z5,z6])],[(0,[z9,z1,z2,z3,z8,z56,z6]),(1,[z10,z1,z2,z3,z8,z6])],[(0,[z10,z1,z136,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z6,z638,z55])],[(0,[z10,z95,z1,z2,z3,z8,z6]),(0,[z279,z1,z2,z3,z8,z42,z6]),(0,[z1,z685,z2,z3,z8,z5,z6])],[(0,[z1,z686,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z20,z6])],[],[(0,[z687,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z688,z8,z5,z6]),(0,[z1,z2,z3,z8,z94,z20,z6])],[(0,[z57,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z8,z5,z99,z6]),(0,[z1,z2,z3,z4,z191,z5,z6])],[(0,[z1,z2,z3,z8,z6,z32,z55]),(0,[z1,z2,z101,z3,z8,z20,z6])],[(0,[z689,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z690,z8,z5,z6]),(0,[z1,z2,z3,z8,z691,z5,z6]),(0,[z1,z3,z8,z5,z151,z6,z32])],[(0,[z692,z1,z2,z3,z8,z5,z6])],[(0,[z10,z1,z2,z3,z8,z151,z6]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z1,z2,z3,z693,z8,z5,z6]),(0,[z1,z2,z3,z97,z8,z54,z6]),(0,[z1,z2,z3,z4,z132,z5,z6]),(0,[z1,z2,z3,z8,z5,z694,z6]),(0,[z695,z1,z2,z3,z8,z5,z6])],[(0,[z10,z1,z2,z3,z8,z437,z6]),(1,[z1,z2,z3,z53,z4,z6])]],
   [[(0,[z1,z2,z3,z8,z45,z42,z6])],[(0,[z696,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z697,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z698,z5,z6]),(0,[z165,z1,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z48,z8,z5,z6]),(0,[z1,z2,z3,z8,z580,z5,z6]),(0,[z1,z2,z3,z8,z42,z60,z6])],[(0,[z1,z699,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z62,z6]),(0,[z1,z2,z3,z8,z42,z20,z6])],[(0,[z50,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z443,z3,z8,z5,z6])],[(0,[z700,z1,z2,z3,z8,z5,z6]),(0,[z125,z10,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z20,z38,z6])],[(0,[z126,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z701,z6]),(0,[z199,z279,z2,z3,z8,z5,z6]),(0,[z84,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z8,z5,z6,z152])],[(0,[z1,z2,z67,z8,z5,z6,z81]),(1,[z78,z1,z3,z8,z260,z6]),(0,[z1,z2,z3,z260,z5,z6,z14])],[(0,[z1,z2,z3,z25,z8,z54,z6]),(0,[z1,z2,z3,z48,z5,z6,z14]),(0,[z192,z1,z2,z3,z8,z6,z55])],[(0,[z1,z702,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z703]),(0,[z1,z2,z3,z8,z704,z5,z6])],[(0,[z93,z297,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z426,z8,z5,z6])],[(0,[z10,z0,z1,z2,z3,z8,z6]),(0,[z78,z1,z3,z8,z260,z5,z6]),(0,[z1,z2,z3,z8,z20,z60,z6]),(0,[z1,z2,z3,z8,z42,z6,z81])],[(0,[z1,z2,z3,z8,z20,z62,z6]),(0,[z1,z2,z3,z8,z20,z20,z6])],[(1,[z1,z2,z3,z8,z76,z6])],[(0,[z1,z2,z3,z67,z8,z56,z6]),(0,[z1,z2,z3,z705,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z644,z6])],[(0,[z173,z1,z2,z3,z8,z20,z6]),(0,[z15,z10,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z706,z8,z5,z6]),(0,[z1,z2,z3,z8,z260,z42,z6]),(0,[z93,z1,z2,z3,z25,z8,z6]),(0,[z1,z2,z102,z3,z8,z56,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z8,z5,z707]),(0,[z121,z2,z3,z8,z153,z6]),(0,[z1,z355,z77,z8,z5,z6]),(0,[z1,z355,z3,z8,z438,z6]),(0,[z1,z2,z3,z427,z4,z6]),(0,[z10,z1,z2,z3,z331,z6]),(0,[z110,z1,z2,z8,z81,z55])],[(0,[z1,z708,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z709])],[(0,[z1,z2,z3,z8,z5,z710]),(0,[z1,z2,z3,z711,z8,z6]),(0,[z1,z2,z3,z8,z712,z6]),(0,[z1,z2,z3,z5,z6,z713]),(0,[z1,z2,z3,z8,z397,z6]),(0,[z1,z2,z3,z714,z5,z6]),(0,[z1,z2,z3,z476,z5,z6]),(0,[z1,z2,z530,z5,z6,z589])],[(0,[z1,z2,z3,z8,z6,z715]),(0,[z1,z2,z3,z8,z666,z55]),(0,[z1,z2,z3,z51,z20,z6])],[(0,[z716,z1,z2,z3,z8,z6]),(0,[z1,z2,z426,z8,z56,z6]),(0,[z1,z2,z3,z8,z717,z6])],[(0,[z1,z2,z3,z5,z6,z718]),(0,[z1,z2,z3,z8,z719,z6]),(0,[z1,z2,z3,z8,z720,z6]),(0,[z1,z721,z3,z8,z5,z6]),(0,[z57,z1,z2,z8,z6,z485])],[(0,[z9,z2,z77,z8,z5,z71]),(0,[z1,z2,z3,z169,z6,z55]),(0,[z9,z2,z3,z8,z438,z71]),(0,[z1,z2,z3,z8,z722,z6]),(0,[z1,z2,z3,z723,z5,z6]),(0,[z1,z2,z3,z5,z245,z14]),(0,[z1,z2,z3,z8,z724,z6]),(0,[z1,z2,z3,z8,z725,z6])],[(0,[z1,z2,z3,z8,z42,z6]),(0,[z726,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z63,z6,z55]),(0,[z1,z2,z3,z8,z727,z6]),(0,[z1,z2,z34,z8,z109,z522]),(0,[z1,z2,z3,z8,z6,z728]),(0,[z1,z2,z3,z5,z6,z729])],[(0,[z1,z2,z3,z5,z313,z14])],[(0,[z1,z2,z3,z730,z8,z6]),(0,[z1,z2,z3,z8,z731,z6]),(0,[z1,z2,z101,z8,z525,z6]),(0,[z1,z72,z3,z4,z5,z6])],[(0,[z1,z2,z3,z732,z8,z6]),(0,[z1,z2,z3,z733,z20,z6]),(0,[z10,z1,z2,z734,z8,z6])],[(0,[z1,z2,z3,z8,z735,z6]),(0,[z1,z2,z74,z8,z20,z6]),(0,[z1,z2,z3,z8,z736,z6]),(0,[z1,z2,z3,z8,z493,z6])],[(0,[z1,z2,z3,z737,z8,z6])],[(0,[z1,z2,z738,z8,z5,z6]),(0,[z1,z2,z3,z739,z8,z6]),(0,[z1,z2,z3,z8,z740,z6]),(0,[z1,z2,z77,z8,z6,z55]),(0,[z1,z2,z3,z6,z563,z204]),(0,[z1,z2,z3,z4,z5,z611]),(0,[z1,z2,z3,z8,z6,z741]),(0,[z1,z2,z3,z742,z139,z6]),(0,[z10,z743,z2,z3,z8,z6]),(0,[z35,z1,z2,z3,z5,z14])],[(0,[z1,z2,z3,z8,z744,z6]),(0,[z1,z2,z3,z8,z496,z6]),(0,[z1,z2,z3,z8,z42,z206]),(0,[z1,z2,z3,z8,z392,z6]),(0,[z1,z2,z3,z8,z745,z6]),(0,[z1,z2,z3,z8,z746,z6])],[(0,[z1,z2,z3,z8,z5,z747]),(0,[z133,z2,z3,z8,z62,z6]),(0,[z1,z2,z3,z385,z75,z6]),(0,[z1,z3,z8,z260,z748,z6]),(0,[z1,z2,z3,z6,z749,z14]),(0,[z750,z1,z2,z8,z42,z6])]],
   [[(0,[z1,z2,z3,z8,z751,z6]),(0,[z1,z2,z77,z4,z5,z6]),(0,[z1,z2,z3,z385,z20,z6]),(0,[z1,z2,z3,z4,z438,z6]),(0,[z1,z2,z3,z752,z8,z6]),(0,[z10,z268,z2,z3,z8,z6]),(0,[z1,z2,z102,z4,z20,z6]),(0,[z10,z1,z72,z3,z8,z6]),(0,[z753,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z754,z8,z6]),(0,[z1,z755,z2,z3,z8,z6]),(0,[z1,z2,z8,z20,z317,z6]),(0,[z182,z1,z228,z3,z8,z6]),(0,[z1,z2,z3,z25,z476,z6])],[(0,[z95,z2,z67,z8,z278,z6]),(0,[z173,z2,z3,z132,z42,z6]),(0,[z1,z90,z3,z8,z6,z55])],[(0,[z1,z2,z756,z8,z5,z6]),(0,[z1,z2,z3,z757,z5,z6]),(0,[z1,z2,z3,z8,z42,z124])],[(0,[z1,z2,z3,z5,z6,z758]),(0,[z1,z2,z3,z8,z6,z204]),(0,[z9,z10,z2,z3,z8,z71]),(0,[z1,z2,z3,z759,z8,z6]),(0,[z185,z353,z2,z3,z8,z6]),(0,[z1,z2,z3,z6,z534,z14])],[(0,[z1,z2,z3,z8,z760,z6]),(0,[z95,z2,z67,z25,z8,z6]),(0,[z195,z566,z2,z3,z8,z6])],[(0,[z1,z2,z3,z761,z5,z6]),(0,[z1,z2,z3,z762,z5,z6]),(0,[z135,z1,z3,z45,z20,z6]),(0,[z1,z207,z3,z8,z38,z6])],[(0,[z1,z2,z3,z8,z348,z435]),(0,[z35,z1,z2,z3,z25,z14])],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z207,z3,z8,z748,z6])],[(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z2,z3,z56,z6,z277]),(0,[z1,z2,z3,z25,z6,z749])],[(0,[z1,z2,z3,z8,z765,z6]),(0,[z1,z2,z3,z447,z56,z6]),(0,[z1,z2,z3,z766,z8,z6]),(0,[z10,z1,z2,z3,z6,z188])],[(0,[z767,z1,z2,z3,z8,z6]),(0,[z1,z207,z3,z8,z146,z6]),(0,[z1,z2,z3,z4,z6,z152]),(0,[z768,z1,z2,z3,z6,z14]),(0,[z1,z2,z3,z4,z769,z6])],[(0,[z1,z2,z3,z8,z770,z6]),(0,[z1,z2,z3,z8,z771,z6]),(0,[z1,z2,z3,z772,z5,z6]),(0,[z1,z2,z773,z3,z8,z6]),(0,[z1,z2,z3,z774,z220,z6]),(0,[z473,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z33,z6,z14]),(0,[z10,z1,z2,z3,z343,z6])],[(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z8,z776,z6]),(0,[z1,z2,z3,z4,z5,z60])],[(0,[z0,z136,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z777,z6]),(0,[z473,z1,z2,z3,z48,z6])],[(0,[z619,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z30,z6,z563]),(0,[z1,z2,z219,z4,z5,z6]),(0,[z1,z2,z3,z8,z6,z778]),(0,[z1,z2,z3,z249,z6,z14]),(0,[z35,z1,z2,z3,z42,z14])]],
   [[(0,[z779,z2,z3,z8,z5,z6]),(0,[z1,z72,z3,z8,z76,z6]),(0,[z1,z2,z3,z4,z16,z6])],[(0,[z1,z2,z780,z3,z8,z6])],[(0,[z1,z2,z3,z218,z25,z6]),(0,[z781,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z381,z6]),(0,[z1,z2,z3,z8,z5,z782])],[(0,[z1,z2,z783,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z233]),(0,[z1,z2,z3,z427,z8,z6]),(0,[z1,z2,z8,z56,z525,z6])],[(0,[z1,z2,z3,z784,z8,z6]),(0,[z1,z66,z2,z294,z8,z6]),(0,[z1,z2,z216,z8,z56,z6]),(0,[z1,z785,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z786,z6])],[(0,[z1,z2,z3,z8,z787,z6]),(0,[z1,z2,z3,z4,z5,z174]),(0,[z1,z2,z3,z298,z6,z201]),(0,[z10,z1,z2,z3,z628,z6]),(0,[z1,z2,z3,z4,z5,z393])],[(0,[z1,z2,z3,z8,z788,z6]),(0,[z1,z2,z3,z139,z6,z55]),(0,[z1,z2,z3,z25,z172,z6])],[(0,[z1,z2,z3,z8,z789,z6]),(0,[z1,z790,z2,z3,z8,z6]),(0,[z791,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z42,z245]),(0,[z792,z1,z2,z3,z6,z201]),(0,[z793,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z794,z6]),(0,[z10,z1,z2,z3,z8,z795]),(0,[z1,z2,z3,z8,z796,z6])],[(0,[z507,z2,z67,z8,z5,z6]),(0,[z797,z2,z3,z8,z5,z6]),(0,[z1,z2,z426,z5,z6,z14]),(0,[z1,z2,z3,z56,z6,z798]),(0,[z1,z2,z3,z8,z42,z437]),(0,[z35,z1,z2,z3,z519,z14])],[(0,[z1,z2,z3,z8,z799,z6]),(0,[z800,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z801,z6])],[(0,[z1,z2,z3,z218,z42,z6]),(0,[z802,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z402,z14]),(0,[z1,z2,z3,z803,z8,z6]),(0,[z804,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z5,z6,z805]),(0,[z1,z207,z3,z8,z128,z6]),(0,[z1,z2,z3,z8,z6,z522])],[(0,[z1,z2,z3,z806,z5,z6]),(0,[z1,z2,z3,z8,z807,z6])],[(0,[z1,z2,z3,z808,z5,z6]),(0,[z1,z2,z3,z8,z809,z6]),(0,[z165,z84,z1,z8,z42,z6])],[(0,[z1,z2,z3,z8,z810,z6]),(0,[z279,z2,z3,z446,z8,z6]),(0,[z1,z2,z3,z8,z811,z6]),(0,[z812,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z56,z6,z14])],[(0,[z1,z2,z3,z8,z813,z6]),(0,[z1,z2,z426,z8,z397,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z814]),(0,[z1,z2,z3,z815,z5,z6])],[(0,[z1,z2,z3,z5,z375,z14]),(0,[z1,z2,z3,z8,z816,z6]),(0,[z1,z2,z3,z8,z644,z55])],[(0,[z279,z566,z2,z3,z8,z6]),(0,[z1,z2,z3,z6,z14,z152])],[(0,[z1,z2,z3,z8,z817,z6]),(1,[z1,z2,z3,z4,z534])],[(0,[z1,z2,z3,z5,z6,z818]),(0,[z1,z2,z3,z8,z819,z6]),(0,[z1,z2,z357,z8,z20,z6]),(0,[z1,z2,z3,z8,z5,z820]),(0,[z165,z84,z1,z8,z496,z6]),(0,[z78,z1,z3,z4,z260,z6]),(0,[z1,z2,z426,z8,z42,z6]),(0,[z1,z2,z3,z8,z6,z534])],[(0,[z95,z2,z67,z8,z6,z55]),(0,[z135,z1,z171,z3,z5,z6]),(0,[z689,z1,z3,z8,z260,z6]),(0,[z93,z1,z3,z220,z5,z32]),(0,[z163,z1,z2,z101,z48,z6])],[(0,[z1,z2,z821,z8,z5,z6])],[(0,[z1,z2,z3,z76,z6,z14])],[(0,[z95,z2,z67,z4,z5,z6]),(0,[z1,z2,z3,z8,z822,z6])],[(0,[z126,z3,z13,z8,z20,z6]),(0,[z173,z2,z3,z823,z5,z6]),(0,[z1,z2,z3,z824,z447,z6]),(0,[z7,z2,z3,z8,z342,z6]),(0,[z1,z2,z3,z53,z123,z6]),(0,[z69,z2,z3,z475,z5,z6])],[(0,[z1,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z172,z6,z55]),(0,[z10,z1,z2,z3,z4,z60])],[(0,[z825,z1,z2,z3,z8,z6]),(0,[z826,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z827,z5,z6]),(0,[z1,z2,z3,z8,z828,z6]),(0,[z1,z2,z3,z4,z5,z655])],[(0,[z1,z355,z3,z169,z5,z6]),(0,[z1,z2,z3,z8,z5,z829]),(0,[z1,z2,z3,z8,z830,z6]),(0,[z297,z131,z3,z8,z5,z6]),(0,[z473,z1,z2,z3,z4,z6]),(0,[z10,z1,z2,z3,z212,z6]),(0,[z10,z1,z2,z3,z53,z6])],[(0,[z1,z2,z3,z831,z5,z6]),(0,[z15,z1,z2,z513,z5,z6]),(0,[z1,z2,z3,z8,z832,z6])],[(0,[z1,z2,z3,z8,z6,z833]),(0,[z10,z126,z3,z13,z8,z6]),(0,[z1,z2,z334,z8,z20,z6]),(0,[z10,z1,z2,z3,z169,z6]),(0,[z1,z2,z3,z42,z6,z563]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z3,z8,z835,z6]),(0,[z1,z2,z3,z180,z6,z55]),(0,[z1,z2,z3,z8,z6,z836]),(1,[z1,z2,z3,z5,z837])],[(0,[z1,z2,z838,z3,z8,z6]),(0,[z93,z1,z3,z8,z234,z32]),(0,[z1,z2,z3,z839,z20,z6])]],
   [[(0,[z1,z2,z3,z840,z8,z6]),(0,[z1,z2,z77,z8,z438,z6]),(0,[z1,z154,z31,z8,z291,z6])],[(0,[z1,z2,z841,z8,z5,z6]),(0,[z93,z1,z3,z8,z56,z32]),(0,[z842,z2,z3,z8,z5,z6]),(0,[z1,z2,z34,z8,z42,z109])],[(0,[z1,z2,z3,z8,z6,z843]),(0,[z1,z2,z216,z8,z5,z6]),(0,[z1,z355,z3,z8,z75,z6]),(0,[z9,z2,z3,z169,z5,z71]),(0,[z2,z3,z8,z5,z6,z844]),(0,[z1,z2,z3,z25,z636,z6]),(0,[z1,z2,z3,z474,z8,z6]),(0,[z1,z2,z3,z8,z845,z6]),(0,[z1,z846,z3,z8,z5,z6])],[(0,[z1,z2,z3,z346,z8,z6]),(0,[z1,z355,z3,z8,z20,z6]),(0,[z1,z2,z3,z315,z6,z14]),(0,[z847,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z848,z6]),(0,[z1,z2,z3,z394,z5,z14]),(0,[z1,z2,z849,z11,z5,z6]),(0,[z227,z2,z3,z8,z20,z6])],[(0,[z1,z2,z3,z8,z850,z6]),(0,[z1,z2,z3,z8,z851,z6]),(0,[z1,z2,z101,z48,z341,z6]),(0,[z1,z2,z5,z6,z14,z852])],[(0,[z1,z2,z3,z8,z611,z55]),(0,[z1,z2,z3,z63,z6,z152]),(0,[z1,z2,z3,z4,z39,z6])],[(0,[z1,z2,z3,z8,z5,z853]),(0,[z163,z1,z2,z3,z474,z6]),(0,[z1,z2,z3,z348,z6,z14]),(0,[z10,z1,z2,z3,z172,z6])],[(0,[z854,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z855,z6]),(0,[z1,z2,z3,z20,z6,z563]),(0,[z1,z2,z3,z8,z856,z6]),(0,[z1,z371,z3,z8,z260,z6]),(0,[z1,z2,z3,z8,z56,z782]),(0,[z1,z2,z3,z8,z483,z6])],[(0,[z1,z2,z3,z8,z857,z6]),(0,[z1,z2,z3,z8,z858,z6]),(0,[z1,z2,z216,z5,z6,z14]),(0,[z9,z2,z3,z8,z75,z71]),(0,[z1,z2,z3,z859,z8,z6]),(0,[z1,z2,z3,z8,z860,z6]),(0,[z1,z2,z3,z5,z6,z861]),(0,[z383,z2,z3,z8,z94,z6]),(0,[z1,z2,z34,z8,z392,z109])],[(0,[z9,z2,z3,z8,z20,z71]),(0,[z1,z2,z3,z8,z862,z6]),(0,[z1,z2,z3,z8,z393,z71]),(0,[z1,z2,z3,z8,z863,z6]),(0,[z1,z2,z3,z8,z348,z81]),(0,[z57,z1,z2,z4,z56,z6]),(0,[z1,z2,z8,z5,z6,z864])],[(0,[z1,z2,z3,z447,z42,z6]),(0,[z10,z1,z2,z3,z200,z6]),(0,[z1,z2,z3,z8,z6,z865]),(0,[z1,z2,z3,z8,z42,z531]),(0,[z1,z451,z3,z8,z6,z119])],[(0,[z1,z2,z3,z8,z866,z6]),(0,[z1,z2,z867,z8,z5,z6]),(0,[z1,z2,z3,z8,z868,z6]),(0,[z1,z131,z3,z8,z42,z151]),(0,[z1,z2,z3,z869,z5,z6]),(0,[z1,z2,z3,z47,z89,z6]),(0,[z1,z2,z3,z474,z440,z6]),(0,[z133,z2,z3,z8,z6,z330])],[(0,[z1,z2,z3,z8,z870,z6]),(0,[z1,z2,z3,z8,z109,z122]),(0,[z1,z2,z3,z8,z39,z122])],[(0,[z1,z2,z3,z871,z8,z6]),(0,[z1,z2,z3,z8,z6,z872]),(0,[z163,z1,z2,z3,z8,z782]),(0,[z10,z1,z2,z3,z6,z277])],[(0,[z1,z2,z3,z214,z6,z14]),(0,[z9,z90,z3,z8,z5,z71]),(0,[z1,z2,z3,z8,z873,z6]),(0,[z1,z2,z3,z8,z348,z109])],[(0,[z874,z115,z1,z2,z3,z6]),(0,[z125,z2,z3,z25,z54,z6]),(0,[z1,z2,z101,z48,z6,z55]),(0,[z1,z2,z3,z53,z6,z14])]],
   [[(0,[z1,z2,z734,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z875]),(0,[z1,z2,z102,z8,z525,z6])],[(0,[z1,z2,z3,z876,z8,z6]),(0,[z1,z2,z3,z5,z877,z6])],[(0,[z1,z2,z3,z8,z878,z6]),(0,[z1,z2,z3,z8,z879,z6]),(0,[z1,z2,z77,z8,z880,z6]),(0,[z1,z2,z3,z4,z75,z6]),(0,[z1,z2,z3,z881,z200,z6]),(0,[z1,z72,z3,z139,z5,z6]),(0,[z29,z2,z3,z8,z390,z6])],[(0,[z90,z3,z8,z5,z6,z71]),(0,[z15,z1,z2,z11,z20,z6]),(0,[z1,z2,z3,z4,z20,z6]),(0,[z1,z262,z3,z25,z8,z6]),(0,[z1,z2,z3,z139,z249,z6]),(0,[z1,z2,z3,z8,z6,z882])],[(0,[z1,z2,z3,z883,z8,z6]),(0,[z10,z1,z90,z3,z8,z6]),(0,[z1,z2,z3,z493,z6,z14]),(0,[z1,z2,z3,z6,z519,z277])],[(0,[z1,z2,z3,z8,z884,z6]),(0,[z1,z2,z3,z265,z6,z14]),(0,[z1,z154,z31,z8,z56,z6])],[(0,[z135,z1,z3,z25,z45,z6])],[(0,[z1,z885,z2,z3,z8,z6]),(0,[z1,z2,z3,z447,z6,z204]),(0,[z1,z2,z3,z25,z220,z6]),(0,[z1,z2,z8,z886,z20,z6]),(0,[z1,z2,z3,z476,z42,z6])],[(1,[z2,z3,z823,z5,z6]),(0,[z1,z2,z3,z8,z887,z6]),(0,[z1,z90,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z222,z6]),(0,[z1,z2,z409,z8,z20,z6])],[(0,[z1,z2,z3,z8,z888,z6]),(0,[z1,z2,z3,z8,z6,z889]),(0,[z1,z2,z3,z220,z6,z55]),(0,[z1,z2,z3,z25,z89,z6]),(0,[z1,z2,z3,z294,z6,z14])],[(0,[z1,z2,z890,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z582]),(0,[z224,z1,z2,z3,z343,z6]),(0,[z1,z2,z3,z8,z891,z6])],[(0,[z1,z2,z3,z8,z892,z6]),(0,[z1,z2,z3,z8,z6,z893]),(0,[z1,z2,z3,z200,z6,z55]),(0,[z1,z2,z3,z8,z894,z6]),(0,[z1,z2,z3,z8,z895,z6]),(0,[z1,z2,z3,z51,z56,z6])],[(0,[z1,z2,z3,z8,z896,z6]),(0,[z3,z13,z8,z5,z6,z375]),(0,[z1,z2,z3,z8,z897,z6]),(1,[z1,z3,z8,z748,z6]),(0,[z227,z2,z3,z139,z5,z6])],[(0,[z527,z3,z13,z8,z5,z6]),(0,[z898,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z899]),(0,[z1,z262,z3,z8,z249,z6]),(0,[z203,z1,z2,z3,z5,z14])],[(0,[z0,z900,z3,z8,z5,z6]),(0,[z1,z901,z3,z8,z5,z6]),(0,[z1,z2,z902,z8,z5,z6]),(0,[z1,z2,z3,z234,z6,z14]),(0,[z239,z1,z2,z8,z56,z6]),(0,[z10,z1,z2,z3,z8,z903]),(0,[z1,z2,z3,z525,z6,z14])],[(0,[z1,z2,z3,z323,z6,z14]),(0,[z1,z2,z3,z904,z5,z6]),(0,[z1,z905,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z906]),(0,[z93,z1,z3,z8,z5,z32]),(0,[z10,z1,z262,z3,z8,z6]),(0,[z1,z2,z34,z8,z109,z55]),(0,[z35,z1,z2,z3,z483,z14])]],
   [[(0,[z1,z2,z907,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z908])],[(0,[z1,z2,z3,z8,z909,z6]),(0,[z1,z2,z3,z53,z476,z6])],[(0,[z1,z2,z3,z474,z4,z6]),(0,[z10,z1,z2,z3,z6,z14])],[(0,[z1,z2,z3,z8,z910,z6]),(0,[z1,z2,z3,z346,z4,z6]),(0,[z1,z2,z911,z8,z5,z6]),(0,[z1,z2,z3,z912,z5,z6]),(0,[z1,z584,z31,z8,z5,z6]),(0,[z10,z1,z2,z3,z430,z6]),(0,[z1,z2,z3,z8,z348,z6]),(0,[z324,z1,z3,z8,z354,z6]),(0,[z1,z2,z3,z476,z42,z124])],[(0,[z913,z1,z2,z3,z200,z6]),(0,[z1,z2,z3,z8,z914,z6]),(0,[z1,z2,z3,z56,z14,z122]),(0,[z1,z2,z3,z8,z915,z6])],[(0,[z1,z2,z3,z916,z5,z6]),(0,[z1,z2,z3,z917,z5,z6]),(0,[z1,z2,z3,z918,z5,z6]),(0,[z10,z1,z2,z3,z374,z6]),(0,[z1,z2,z8,z849,z5,z6])],[(0,[z1,z2,z3,z5,z428,z14]),(0,[z10,z1,z2,z3,z367,z6]),(0,[z1,z2,z3,z8,z919,z6]),(0,[z920,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z517,z6]),(0,[z1,z2,z3,z4,z8,z534])],[(0,[z1,z2,z3,z385,z56,z6]),(0,[z1,z2,z3,z8,z5,z921]),(0,[z922,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z923,z5,z6])],[(0,[z1,z2,z3,z8,z924,z6]),(0,[z1,z2,z3,z8,z27,z55]),(0,[z1,z2,z3,z8,z925,z6]),(0,[z15,z1,z2,z294,z8,z6]),(0,[z1,z2,z3,z6,z519,z14]),(0,[z1,z2,z3,z4,z244,z6])],[(0,[z1,z2,z3,z926,z5,z6]),(0,[z1,z2,z8,z20,z6,z422]),(0,[z1,z2,z3,z8,z927,z6]),(0,[z1,z2,z3,z928,z8,z6]),(0,[z1,z2,z4,z56,z20,z6]),(0,[z1,z72,z3,z180,z5,z6]),(0,[z1,z2,z3,z8,z929,z6])],[(0,[z930,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z218,z857,z6]),(0,[z1,z931,z2,z3,z8,z6]),(0,[z78,z1,z697,z3,z8,z6]),(0,[z1,z2,z3,z25,z467,z6]),(0,[z10,z1,z2,z3,z690,z6]),(0,[z1,z2,z3,z774,z8,z6]),(0,[z1,z2,z3,z932,z8,z6]),(0,[z1,z2,z3,z933,z8,z6]),(0,[z1,z2,z3,z180,z249,z6]),(0,[z934,z1,z2,z3,z8,z6]),(0,[z10,z1,z2,z935,z8,z6])],[(0,[z110,z1,z2,z3,z8,z393]),(0,[z1,z2,z3,z8,z877,z6])],[(0,[z297,z2,z3,z8,z20,z6])],[(0,[z1,z2,z3,z8,z936,z6]),(0,[z937,z1,z2,z3,z8,z6]),(0,[z135,z1,z3,z45,z56,z6]),(0,[z1,z2,z3,z8,z938,z6]),(0,[z10,z1,z2,z3,z6,z235]),(1,[z1,z2,z3,z8,z939])],[(0,[z1,z2,z3,z8,z940,z6]),(0,[z1,z2,z3,z8,z6,z941]),(0,[z1,z2,z3,z8,z348,z124])]],
   [[(0,[z1,z2,z3,z8,z942,z6]),(0,[z1,z2,z3,z6,z201,z55])],[(0,[z1,z2,z3,z8,z943,z6]),(0,[z1,z944,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z42,z313])],[(0,[z945,z1,z2,z3,z8,z6]),(0,[z946,z1,z2,z3,z5,z6]),(0,[z947,z2,z3,z8,z5,z6])],[(0,[z1,z154,z31,z8,z5,z6]),(0,[z948,z2,z3,z8,z5,z6]),(0,[z949,z2,z3,z8,z5,z6]),(0,[z1,z262,z3,z8,z6,z55]),(0,[z1,z2,z34,z3,z8,z393]),(0,[z596,z1,z3,z5,z6,z333]),(0,[z1,z2,z3,z244,z6,z14])],[(0,[z1,z2,z3,z8,z950,z6]),(0,[z78,z1,z3,z8,z6,z167]),(0,[z10,z297,z2,z3,z8,z6]),(0,[z268,z2,z3,z8,z6,z55]),(0,[z227,z2,z3,z180,z5,z6]),(0,[z10,z1,z2,z3,z476,z6])],[(0,[z1,z2,z3,z951,z8,z6]),(0,[z1,z2,z3,z247,z6,z14]),(0,[z1,z2,z3,z952,z5,z6])],[(0,[z0,z136,z3,z8,z56,z6]),(0,[z953,z1,z2,z8,z5,z6]),(0,[z297,z2,z3,z220,z5,z6]),(1,[z1,z2,z3,z4,z393])],[(0,[z1,z2,z3,z8,z5,z954]),(0,[z1,z2,z3,z8,z174,z55]),(0,[z1,z2,z3,z5,z454,z14])],[(0,[z1,z2,z3,z8,z6,z955]),(0,[z1,z2,z3,z8,z956,z6]),(0,[z1,z2,z3,z8,z36,z393]),(0,[z297,z2,z3,z200,z5,z6]),(0,[z1,z2,z3,z8,z341,z6]),(0,[z1,z2,z3,z957,z8,z6]),(0,[z373,z2,z3,z8,z6,z270])],[(0,[z173,z2,z3,z377,z5,z6]),(0,[z1,z154,z31,z5,z6,z14]),(0,[z1,z2,z3,z958,z5,z6]),(0,[z1,z2,z64,z8,z56,z6]),(0,[z1,z2,z3,z51,z5,z6]),(0,[z1,z785,z2,z8,z42,z6])],[(0,[z1,z2,z3,z346,z218,z6]),(0,[z1,z2,z3,z8,z959,z6]),(0,[z1,z2,z3,z8,z960,z6]),(0,[z224,z1,z2,z3,z53,z6])],[(0,[z1,z2,z3,z8,z961,z6]),(0,[z1,z2,z3,z4,z96,z6]),(0,[z1,z2,z3,z8,z962,z6]),(0,[z963,z1,z2,z3,z8,z6])],[(0,[z964,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z965]),(0,[z1,z2,z77,z169,z5,z6]),(0,[z1,z2,z3,z169,z438,z6]),(0,[z1,z2,z3,z8,z6,z966]),(0,[z1,z2,z3,z8,z6,z122]),(0,[z1,z72,z3,z8,z20,z6]),(0,[z967,z1,z2,z3,z8,z6]),(0,[z953,z1,z2,z5,z6,z14])],[(0,[z1,z2,z3,z968,z8,z5]),(0,[z1,z2,z3,z969,z5,z6]),(0,[z970,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z63,z20,z6]),(0,[z1,z2,z3,z172,z16,z6])],[(0,[z115,z1,z2,z3,z6,z55])],[(0,[z1,z2,z3,z5,z6,z971]),(0,[z135,z1,z445,z3,z45,z6]),(0,[z1,z2,z3,z517,z6,z14]),(0,[z35,z1,z2,z3,z517,z14]),(0,[z1,z2,z972,z4,z8,z6])]],
   [[(0,[z464,z1,z2,z3,z5,z14]),(0,[z297,z2,z3,z8,z234,z6]),(0,[z1,z2,z3,z733,z5,z6])],[(0,[z1,z2,z3,z8,z6,z973]),(0,[z1,z2,z3,z23,z20,z6])],[(0,[z1,z2,z3,z8,z6,z974]),(0,[z1,z2,z77,z8,z75,z6])],[(0,[z1,z2,z3,z8,z6,z55]),(0,[z1,z2,z3,z5,z6,z975]),(0,[z1,z2,z3,z5,z469,z14]),(0,[z1,z2,z3,z5,z471,z14]),(0,[z473,z173,z1,z2,z3,z6]),(0,[z1,z2,z77,z8,z20,z6]),(0,[z1,z2,z335,z8,z20,z6]),(0,[z1,z2,z3,z8,z976,z6]),(0,[z1,z2,z3,z139,z76,z6]),(0,[z1,z2,z3,z8,z6,z519])],[(0,[z1,z977,z3,z8,z5,z6])],[(0,[z93,z10,z1,z3,z8,z32]),(0,[z10,z1,z2,z3,z4,z393])],[(0,[z115,z254,z1,z2,z3,z6]),(0,[z1,z2,z3,z385,z5,z6]),(0,[z1,z2,z3,z496,z6,z14]),(0,[z978,z1,z2,z3,z8,z6]),(0,[z15,z1,z2,z11,z5,z6]),(0,[z1,z2,z3,z4,z42,z55])],[(0,[z1,z2,z3,z8,z6,z979]),(0,[z1,z90,z3,z8,z75,z6])],[(0,[z1,z2,z3,z8,z980,z6]),(0,[z1,z90,z77,z8,z5,z6]),(0,[z1,z90,z3,z8,z438,z6]),(0,[z1,z2,z3,z5,z478,z14]),(0,[z1,z2,z3,z981,z8,z6])],[(0,[z982,z2,z3,z8,z5,z6]),(0,[z473,z1,z2,z3,z49,z6]),(0,[z1,z2,z3,z6,z188,z522]),(0,[z10,z1,z2,z3,z8,z983]),(0,[z1,z2,z3,z8,z124,z534])],[(0,[z1,z2,z3,z984,z8,z6]),(0,[z1,z2,z3,z8,z985,z6]),(0,[z1,z2,z8,z886,z5,z6]),(0,[z1,z977,z3,z5,z6,z14])],[(0,[z1,z2,z3,z8,z986,z6]),(0,[z1,z987,z3,z8,z5,z6]),(0,[z1,z2,z3,z988,z8,z6]),(0,[z1,z2,z3,z16,z6,z188])],[(0,[z1,z2,z3,z8,z989,z6]),(0,[z1,z2,z3,z4,z5,z594]),(0,[z125,z2,z3,z54,z20,z6]),(0,[z135,z1,z3,z45,z5,z6]),(0,[z1,z2,z445,z3,z8,z6]),(0,[z93,z1,z426,z8,z5,z32]),(0,[z1,z2,z642,z8,z20,z6])],[(0,[z990,z1,z2,z3,z8,z6]),(0,[z141,z66,z2,z8,z20,z6]),(0,[z1,z2,z3,z8,z580,z6])],[(0,[z1,z2,z3,z8,z991,z6])],[(0,[z1,z2,z3,z992,z5,z6]),(0,[z1,z131,z3,z8,z151,z55]),(0,[z129,z2,z3,z25,z8,z6])]],
   [[(0,[z223,z1,z2,z8,z6,z485])],[(0,[z126,z3,z13,z8,z56,z6]),(0,[z254,z126,z3,z13,z8,z6]),(0,[z1,z2,z3,z8,z993,z6]),(0,[z110,z1,z2,z25,z8,z81]),(0,[z10,z1,z2,z994,z8,z6])],[(0,[z1,z2,z3,z8,z995,z6]),(0,[z1,z2,z3,z8,z996,z6]),(0,[z1,z2,z219,z8,z20,z6]),(0,[z1,z2,z3,z5,z439,z14]),(0,[z997,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z5,z837])],[(0,[z1,z2,z3,z4,z5,z88]),(0,[z1,z2,z3,z998,z169,z6]),(0,[z2,z3,z8,z5,z954,z71]),(0,[z1,z2,z3,z8,z525,z6]),(0,[z1,z2,z305,z8,z56,z6])],[(0,[z0,z136,z3,z8,z5,z6]),(0,[z1,z2,z3,z999,z8,z6]),(0,[z1,z2,z3,z8,z1000,z6]),(0,[z1,z2,z3,z8,z1001,z6]),(0,[z349,z1,z3,z8,z260,z6])],[(0,[z1,z2,z3,z8,z1002,z6]),(0,[z1,z2,z3,z1003,z8,z6]),(0,[z1,z2,z3,z1004,z8,z6]),(0,[z1,z2,z3,z8,z1005,z6])],[(0,[z1,z2,z3,z8,z1006,z6]),(0,[z1,z2,z3,z4,z291,z6]),(0,[z1,z2,z3,z298,z6,z14]),(0,[z1,z2,z3,z8,z338,z6]),(0,[z1,z2,z1007,z3,z8,z6])],[(0,[z1,z2,z216,z8,z42,z6]),(0,[z1,z2,z3,z8,z6,z1008]),(0,[z268,z2,z3,z25,z8,z6]),(0,[z1,z2,z3,z8,z1009,z6])],[(0,[z1,z2,z3,z8,z6,z1010]),(0,[z1,z2,z3,z8,z6,z1011]),(0,[z1,z2,z3,z8,z1012,z6]),(0,[z1,z2,z3,z47,z8,z6]),(0,[z230,z1,z2,z8,z56,z6]),(0,[z1,z2,z3,z8,z6,z1013]),(0,[z1,z2,z3,z25,z877,z6])],[(0,[z1,z2,z3,z8,z455,z6]),(0,[z1,z2,z3,z1014,z8,z6]),(0,[z129,z2,z3,z8,z249,z6]),(0,[z1,z2,z3,z5,z14,z213]),(0,[z349,z1,z3,z8,z178,z6])],[(0,[z0,z136,z3,z5,z6,z14]),(0,[z1,z2,z294,z8,z56,z6]),(0,[z1,z2,z3,z1015,z8,z6])],[(0,[z2,z900,z3,z8,z5,z6]),(0,[z1,z355,z3,z8,z56,z6]),(0,[z1,z2,z3,z92,z6,z14]),(0,[z1016,z1,z2,z3,z8,z6]),(0,[z227,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z180,z76,z6]),(0,[z110,z1,z2,z8,z249,z81])],[(0,[z1,z2,z3,z96,z6,z14]),(0,[z1,z2,z3,z97,z6,z14]),(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z2,z3,z8,z1018,z6]),(0,[z1,z2,z3,z8,z60,z122]),(0,[z1,z2,z3,z6,z728,z188])],[(0,[z22,z10,z1,z2,z3,z6]),(0,[z141,z1,z2,z8,z525,z6])],[(0,[z1,z2,z3,z8,z1019,z6]),(0,[z110,z227,z2,z8,z5,z81]),(0,[z1,z1020,z2,z3,z8,z6])],[(0,[z1,z2,z3,z397,z6,z14]),(0,[z1,z1021,z3,z8,z5,z6])]],
   [[(0,[z297,z2,z3,z8,z5,z6]),(0,[z1022,z1,z2,z3,z180,z6])],[(0,[z9,z2,z3,z8,z56,z71]),(0,[z1023,z1,z2,z3,z8,z6])],[(0,[z1024,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1025,z6]),(0,[z1,z2,z3,z5,z6,z1026])],[(0,[z659,z136,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z278,z6]),(0,[z1,z2,z3,z8,z214,z6]),(0,[z1,z2,z3,z8,z246,z55]),(0,[z1,z2,z3,z8,z1027,z6]),(0,[z1,z2,z3,z5,z6,z1028]),(0,[z224,z1,z2,z3,z8,z393])],[(0,[z1,z2,z1029,z8,z5,z6]),(0,[z236,z1,z2,z3,z5,z14]),(0,[z1,z2,z3,z6,z393,z14]),(0,[z1,z2,z3,z1030,z6,z14])],[(0,[z1,z2,z3,z8,z6,z1031]),(0,[z1,z2,z3,z8,z1032,z6]),(0,[z1,z2,z3,z5,z587,z14]),(0,[z1,z2,z3,z1033,z8,z6]),(0,[z1,z2,z3,z8,z6,z296]),(0,[z1,z2,z3,z8,z6,z1034]),(0,[z192,z1,z2,z3,z53,z6])],[(0,[z1,z2,z3,z25,z8,z6]),(0,[z115,z1,z2,z3,z346,z6]),(0,[z1,z2,z3,z218,z6,z55]),(0,[z0,z136,z3,z8,z42,z6]),(0,[z1,z2,z3,z8,z1035,z6]),(0,[z1,z2,z3,z8,z1036,z6]),(0,[z110,z1,z2,z3,z14,z55])],[(0,[z1,z2,z3,z8,z1037,z6]),(0,[z1,z2,z3,z8,z6,z1038]),(0,[z1,z2,z3,z1039,z56,z6])],[(0,[z1,z2,z3,z8,z366,z6]),(0,[z1,z2,z3,z8,z1040,z6]),(0,[z1,z2,z77,z8,z1041,z6]),(0,[z1,z2,z3,z8,z1042,z6])],[(0,[z1,z2,z8,z5,z6,z852]),(0,[z165,z84,z1,z8,z6,z55]),(0,[z1,z2,z3,z4,z234,z6]),(0,[z227,z262,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1043,z6])],[(0,[z1044,z1,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z485]),(0,[z1,z2,z3,z4,z8,z393])],[(0,[z95,z2,z67,z8,z20,z6]),(0,[z1,z2,z3,z8,z6,z1045]),(0,[z15,z1,z2,z11,z56,z6]),(0,[z1,z2,z3,z4,z56,z6]),(0,[z1,z2,z4,z513,z20,z6]),(0,[z1,z2,z303,z8,z20,z6])],[(0,[z1046,z115,z1,z2,z3,z6]),(0,[z1,z2,z445,z3,z4,z6])],[(0,[z1,z2,z3,z8,z1047,z6]),(0,[z1,z2,z3,z1048,z8,z6]),(0,[z1,z2,z34,z3,z14,z55])],[(0,[z1,z2,z3,z8,z6,z1049]),(0,[z1,z2,z3,z8,z1050,z6]),(0,[z1051,z1,z2,z3,z8,z6]),(0,[z1,z2,z8,z56,z886,z6])],[(0,[z126,z3,z13,z8,z5,z6]),(0,[z1,z72,z3,z8,z5,z6]),(0,[z436,z1,z2,z3,z8,z55]),(0,[z93,z1,z3,z8,z397,z32]),(0,[z129,z2,z3,z8,z6,z55])]],
   [[(0,[z125,z10,z2,z3,z54,z6]),(0,[z1052,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z6]),(0,[z1,z2,z3,z172,z20,z6])],[(0,[z1,z1053,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z6,z1054])],[(0,[z1,z2,z3,z8,z1055,z6]),(0,[z1,z2,z3,z8,z1056,z6]),(0,[z1,z2,z3,z8,z1057,z6]),(0,[z1058,z1,z2,z3,z169,z6]),(0,[z1,z2,z431,z8,z20,z6]),(0,[z1,z2,z48,z8,z580,z6]),(0,[z129,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z5,z6,z463]),(0,[z144,z1,z2,z3,z6,z14])],[(0,[z1,z2,z3,z8,z5,z1059]),(0,[z1,z1060,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1061,z8,z6]),(0,[z1,z2,z3,z1062,z8,z6]),(0,[z10,z1,z2,z77,z8,z6]),(0,[z93,z1,z3,z8,z42,z32]),(0,[z1,z2,z3,z8,z39,z99])],[(0,[z126,z3,z13,z5,z6,z14]),(0,[z254,z1,z2,z3,z6,z14]),(0,[z1,z2,z3,z839,z5,z6]),(0,[z1,z2,z3,z5,z6,z1063]),(0,[z1,z2,z1064,z8,z5,z6])],[(0,[z1,z1065,z3,z8,z5,z6]),(0,[z1066,z2,z3,z8,z5,z6]),(0,[z1,z1067,z2,z8,z5,z6]),(0,[z1,z2,z34,z8,z6,z485]),(0,[z1,z2,z1007,z3,z4,z6])],[(0,[z1,z2,z3,z8,z1068,z6]),(0,[z1069,z2,z3,z8,z5,z6]),(0,[z1,z2,z1070,z3,z6,z14])],[(0,[z1,z2,z8,z5,z6,z1071]),(0,[z1,z2,z3,z8,z6,z1072]),(0,[z596,z1,z3,z45,z5,z6]),(0,[z1,z2,z3,z1073,z5,z6]),(0,[z1,z2,z3,z47,z4,z6])],[(0,[z1,z355,z3,z8,z5,z6]),(0,[z1074,z1,z2,z3,z8,z6]),(0,[z227,z2,z3,z8,z5,z6]),(0,[z9,z2,z3,z5,z71,z14]),(0,[z1075,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z1076]),(0,[z1,z262,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1077,z8,z6]),(0,[z1,z2,z3,z1078,z5,z6]),(0,[z2,z890,z3,z8,z5,z6]),(0,[z268,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z220,z6]),(0,[z1079,z1,z2,z3,z8,z6]),(0,[z10,z129,z2,z3,z8,z6]),(0,[z1080,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z6,z393])],[(0,[z337,z2,z3,z5,z6,z598]),(0,[z1,z2,z3,z8,z1081,z6])],[(0,[z1,z2,z3,z8,z6,z1082]),(0,[z1,z2,z3,z5,z6,z563]),(0,[z15,z10,z1,z2,z11,z6]),(0,[z57,z1,z2,z8,z886,z6])],[(0,[z279,z2,z3,z8,z433,z6]),(0,[z1,z2,z3,z8,z6,z1083]),(0,[z1,z2,z102,z294,z8,z6])],[(0,[z1,z2,z3,z169,z75,z6]),(0,[z1,z2,z3,z8,z1084,z6]),(0,[z1,z2,z309,z8,z20,z6]),(0,[z1,z2,z3,z5,z541,z14]),(0,[z144,z1,z2,z3,z6,z235]),(0,[z1,z1020,z2,z3,z4,z6])],[(0,[z9,z2,z3,z8,z5,z71]),(0,[z1,z2,z3,z169,z20,z6]),(0,[z1,z2,z3,z6,z563,z55]),(0,[z1085,z1,z2,z3,z6,z14]),(0,[z227,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z6,z1086])]],
   [[(0,[z1,z2,z3,z8,z6,z1087]),(0,[z1,z2,z3,z8,z30,z6]),(0,[z1,z2,z3,z8,z1088,z6]),(0,[z551,z1,z2,z3,z8,z296]),(0,[z1,z2,z3,z1089,z56,z6]),(0,[z1,z2,z3,z123,z877,z6])],[],[(0,[z874,z1,z2,z3,z8,z6]),(0,[z24,z2,z3,z8,z36,z55]),(0,[z1,z2,z3,z8,z6,z1090]),(0,[z768,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1091,z6]),(0,[z1,z2,z3,z343,z117,z6])],[(0,[z24,z2,z216,z8,z5,z6]),(0,[z93,z1,z3,z5,z32,z14]),(0,[z1,z2,z3,z25,z23,z6]),(0,[z224,z1,z2,z3,z4,z393])],[(0,[z1,z2,z3,z8,z1092,z6]),(0,[z1,z90,z3,z169,z5,z6]),(0,[z1,z3,z8,z748,z38,z6]),(0,[z1,z2,z3,z392,z6,z14])],[(0,[z297,z2,z3,z8,z56,z6]),(0,[z1,z2,z1093,z3,z8,z6]),(0,[z1,z2,z3,z1094,z20,z6]),(0,[z417,z2,z3,z8,z336,z6]),(0,[z1,z2,z3,z1039,z5,z6]),(0,[z227,z2,z34,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1095,z6]),(0,[z10,z165,z84,z1,z8,z6]),(0,[z1,z2,z8,z543,z20,z6]),(0,[z1,z2,z3,z25,z4,z6])],[(0,[z24,z2,z3,z8,z5,z626]),(0,[z1,z2,z3,z8,z520,z55]),(0,[z1,z2,z3,z6,z1096,z563]),(0,[z1,z350,z31,z8,z5,z6]),(0,[z1,z2,z3,z1097,z8,z6]),(0,[z793,z1,z2,z3,z139,z6])],[(0,[z1,z2,z3,z1098,z5,z6]),(0,[z1,z2,z3,z8,z1099,z6]),(0,[z1,z154,z31,z8,z42,z6]),(0,[z1,z2,z3,z4,z20,z14])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z1100,z6]),(0,[z2,z3,z8,z1101,z62,z6]),(0,[z1,z2,z3,z75,z6,z14]),(0,[z1,z2,z3,z1102,z8,z6]),(0,[z1,z2,z3,z42,z6,z201]),(0,[z1,z2,z3,z8,z1103,z6]),(0,[z1,z2,z3,z6,z1013,z14])],[(0,[z473,z1,z2,z3,z47,z6]),(0,[z118,z1,z2,z8,z580,z6])],[(0,[z1,z90,z3,z8,z20,z6]),(0,[z1,z2,z3,z1104,z5,z6]),(0,[z15,z1,z2,z193,z11,z6]),(0,[z1,z2,z3,z123,z6,z534]),(0,[z192,z1,z2,z3,z6,z14])],[(0,[z591,z2,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z1105]),(0,[z165,z84,z1,z25,z8,z6]),(0,[z1,z2,z3,z8,z631,z6]),(0,[z1106,z1,z2,z3,z8,z6]),(0,[z1,z2,z8,z56,z20,z6]),(1,[z1,z2,z3,z14,z122])],[(0,[z1,z2,z3,z8,z6,z1107]),(0,[z1,z131,z3,z8,z151,z152]),(0,[z163,z1,z2,z3,z212,z6]),(0,[z1,z2,z3,z4,z6,z295])],[(0,[z1,z2,z3,z8,z1108,z6]),(0,[z1,z2,z3,z8,z6,z1109]),(0,[z1,z2,z3,z4,z298,z6]),(0,[z1,z2,z3,z8,z33,z6]),(0,[z1,z2,z3,z193,z6,z14]),(0,[z1,z2,z3,z6,z14,z1110]),(0,[z1,z2,z3,z51,z42,z6])],[(0,[z1,z1111,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1112,z6])]],
   [[(0,[z1,z2,z3,z8,z6,z1113]),(0,[z1,z262,z3,z8,z76,z6]),(0,[z1,z2,z34,z8,z338,z109])],[(0,[z1,z2,z3,z4,z265,z6]),(0,[z1,z2,z3,z8,z1114,z6]),(0,[z173,z2,z3,z132,z6,z55]),(0,[z1,z2,z3,z8,z1115,z6]),(0,[z1,z46,z3,z25,z58,z6]),(0,[z10,z1,z2,z3,z25,z6])],[(0,[z1,z2,z3,z1116,z5,z6]),(0,[z1,z2,z3,z20,z6,z201]),(0,[z1,z2,z3,z25,z63,z6]),(0,[z1,z2,z3,z8,z6,z939])],[(0,[z95,z2,z67,z8,z96,z6]),(0,[z1,z2,z8,z1117,z5,z6]),(0,[z1,z2,z426,z25,z8,z6]),(0,[z1,z2,z3,z8,z6,z1118]),(0,[z1,z2,z3,z16,z6,z14]),(0,[z1,z2,z3,z1119,z8,z6]),(0,[z1,z2,z3,z476,z6,z55])],[(0,[z1,z2,z3,z8,z1120,z6]),(0,[z1,z72,z3,z8,z56,z6])],[(0,[z1,z2,z3,z8,z1101,z6]),(0,[z1,z2,z3,z8,z1121,z6]),(0,[z140,z1,z2,z8,z5,z81]),(0,[z1,z2,z3,z63,z56,z6]),(0,[z1052,z2,z3,z8,z56,z6]),(0,[z10,z1,z905,z3,z8,z6])],[],[(0,[z1,z1122,z2,z8,z5,z6]),(0,[z125,z2,z3,z823,z5,z6]),(0,[z1,z2,z3,z1123,z5,z6]),(0,[z1,z2,z3,z1124,z8,z6]),(0,[z1,z2,z3,z1125,z8,z6]),(0,[z1,z2,z3,z123,z6,z519]),(0,[z192,z1,z2,z3,z6,z235])],[(0,[z199,z2,z3,z8,z6,z270]),(0,[z1,z2,z3,z8,z1126,z6]),(0,[z10,z1,z2,z3,z8,z1127])],[(0,[z1,z2,z3,z8,z1128,z6]),(0,[z1,z2,z3,z8,z6,z1129]),(0,[z2,z216,z8,z5,z6,z71]),(0,[z1,z2,z3,z8,z1130,z6]),(0,[z1,z2,z3,z23,z56,z6])],[(0,[z1,z2,z457,z8,z56,z6]),(0,[z10,z1,z131,z3,z8,z151]),(0,[z1131,z2,z3,z8,z5,z6]),(0,[z1079,z1,z2,z3,z4,z6])],[(0,[z1,z131,z3,z8,z5,z156]),(0,[z1,z2,z3,z1132,z8,z6]),(0,[z1,z2,z77,z8,z56,z6]),(0,[z1,z2,z3,z385,z42,z6]),(0,[z1,z2,z3,z8,z6,z1133]),(0,[z1,z2,z1134,z3,z8,z6]),(0,[z1,z2,z3,z8,z1135,z6]),(0,[z15,z1,z2,z11,z42,z6]),(0,[z1136,z2,z3,z8,z5,z6]),(0,[z1,z2,z102,z8,z886,z6]),(0,[z1,z2,z3,z6,z1137,z14]),(0,[z129,z72,z3,z8,z5,z6]),(0,[z1,z2,z3,z1138,z8,z6])],[(0,[z1,z987,z154,z8,z5,z6]),(0,[z1,z2,z3,z8,z1139,z6]),(0,[z1,z2,z3,z8,z1140,z6]),(0,[z1,z2,z1141,z8,z5,z6]),(0,[z10,z1,z2,z34,z8,z109])],[(0,[z1,z2,z3,z8,z1142,z6]),(0,[z1,z2,z3,z8,z42,z550]),(0,[z1,z2,z3,z8,z1143,z6])],[(0,[z1144,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z315,z6]),(0,[z1,z314,z3,z8,z38,z6]),(0,[z1,z2,z219,z220,z5,z6]),(0,[z1,z2,z3,z1089,z5,z6])],[(0,[z1,z2,z3,z1145,z5,z6]),(0,[z1146,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z139,z20,z6]),(0,[z1,z2,z3,z8,z248,z55])]],
   [[(0,[z1,z2,z3,z1147,z5,z6]),(0,[z1148,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z247,z6]),(0,[z1,z2,z219,z200,z5,z6]),(0,[z913,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1149,z6]),(0,[z1,z2,z3,z8,z1150,z6]),(0,[z1,z2,z3,z8,z1151,z6]),(0,[z1,z2,z3,z8,z76,z6]),(0,[z1,z2,z34,z25,z8,z109]),(0,[z1,z2,z3,z8,z534,z55])],[(0,[z1,z2,z3,z25,z266,z6]),(0,[z1,z2,z3,z8,z1152,z6]),(0,[z135,z1,z3,z45,z42,z6]),(0,[z551,z1,z2,z3,z8,z55]),(0,[z1,z2,z3,z1153,z5,z6]),(0,[z1,z2,z3,z6,z188,z55]),(0,[z10,z1,z2,z3,z311,z6])],[(0,[z115,z126,z3,z13,z5,z6]),(0,[z1,z2,z216,z8,z879,z6]),(0,[z1,z2,z34,z8,z525,z6])],[(0,[z279,z2,z3,z8,z336,z6]),(0,[z1,z2,z3,z1154,z8,z6]),(0,[z78,z1,z3,z8,z748,z6]),(0,[z1,z2,z3,z1155,z20,z6]),(0,[z224,z1,z2,z3,z6,z14]),(0,[z1,z2,z972,z8,z5,z6])],[(0,[z1,z2,z3,z4,z323,z6]),(0,[z125,z2,z3,z54,z56,z6]),(0,[z1,z2,z3,z1156,z6,z14]),(0,[z1,z2,z3,z4,z14,z55]),(0,[z1,z2,z3,z6,z14,z295])],[(0,[z1,z2,z3,z8,z441,z6]),(0,[z1,z2,z3,z8,z1157,z6]),(0,[z1,z207,z228,z3,z8,z6]),(0,[z1158,z1,z2,z3,z8,z6])],[(0,[z1159,z1,z2,z3,z8,z6]),(0,[z1,z1160,z2,z3,z8,z6]),(0,[z1,z2,z40,z47,z8,z6])],[(0,[z1161,z1,z2,z3,z8,z6]),(0,[z110,z1,z72,z8,z5,z81]),(0,[z1,z114,z3,z8,z146,z6])],[(0,[z1,z2,z219,z8,z234,z6]),(0,[z460,z1,z3,z8,z128,z6])],[(0,[z1,z2,z1162,z8,z5,z6]),(0,[z2,z3,z823,z54,z5,z6]),(0,[z297,z2,z3,z5,z6,z14]),(0,[z1,z2,z101,z849,z5,z6]),(0,[z1,z2,z3,z8,z6,z1137]),(0,[z10,z1,z2,z972,z8,z6])],[(0,[z1,z2,z3,z8,z1163,z6]),(0,[z1,z2,z3,z1164,z8,z6]),(0,[z1,z2,z3,z1165,z5,z6]),(0,[z2,z3,z8,z153,z1101,z6]),(0,[z1,z2,z3,z8,z1166,z6]),(0,[z1,z2,z219,z8,z56,z6]),(0,[z1,z131,z3,z25,z8,z151]),(0,[z1,z2,z3,z1167,z8,z6]),(0,[z1,z2,z3,z25,z6,z638])],[(0,[z1168,z1,z2,z3,z8,z6]),(0,[z1,z2,z1169,z8,z5,z6]),(0,[z10,z95,z2,z67,z8,z6]),(0,[z1,z2,z3,z1170,z5,z6]),(0,[z1,z1171,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1172,z6]),(0,[z1,z2,z426,z8,z1084,z6]),(0,[z1,z2,z3,z8,z39,z6]),(0,[z1,z2,z3,z972,z8,z6]),(0,[z35,z144,z1,z2,z3,z14])],[(0,[z125,z2,z3,z97,z54,z6]),(0,[z1,z2,z3,z1173,z5,z6]),(0,[z1174,z2,z3,z8,z5,z6]),(0,[z1,z2,z34,z8,z5,z533])],[(0,[z1,z2,z3,z8,z1175,z6]),(0,[z1,z2,z3,z8,z1176,z6]),(0,[z1177,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1178,z6]),(0,[z1,z2,z3,z4,z60,z295])],[(0,[z1,z1179,z3,z8,z5,z6]),(0,[z1,z2,z3,z595,z5,z14]),(0,[z145,z1,z3,z8,z6,z167])],[(0,[z1,z2,z1180,z8,z5,z6]),(0,[z1,z2,z294,z31,z8,z6]),(0,[z1,z2,z3,z8,z6,z1181]),(0,[z165,z84,z1,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z6,z1182]),(0,[z173,z2,z3,z132,z441,z6]),(0,[z297,z2,z3,z8,z397,z6]),(0,[z1,z2,z8,z11,z525,z6])],[(0,[z1,z2,z3,z6,z201,z152]),(0,[z121,z2,z3,z8,z52,z6])],[(0,[z1,z2,z3,z1183,z8,z6]),(0,[z1184,z2,z3,z8,z5,z6]),(0,[z1185,z2,z3,z8,z5,z6]),(0,[z135,z1,z3,z92,z45,z6]),(0,[z1,z2,z3,z1186,z8,z6]),(0,[z1,z2,z3,z42,z6,z188])],[(0,[z1,z2,z3,z63,z5,z6]),(0,[z1,z2,z426,z8,z976,z6]),(0,[z1,z2,z426,z8,z6,z55]),(0,[z1,z2,z3,z8,z1187,z6]),(0,[z110,z1,z262,z8,z5,z81]),(0,[z35,z1,z2,z3,z8,z534])],[(0,[z1,z189,z2,z8,z20,z6]),(0,[z1,z2,z3,z8,z1188,z6]),(0,[z1,z2,z1189,z8,z5,z6]),(0,[z1,z2,z3,z8,z1190,z6])],[(0,[z1,z2,z3,z8,z1191,z6]),(0,[z1192,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1193,z6]),(0,[z297,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z20,z6,z1194])],[(0,[z1,z1195,z3,z8,z5,z6]),(0,[z1,z131,z3,z8,z5,z142]),(0,[z1,z2,z3,z53,z8,z6])],[(0,[z1196,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z1197,z6]),(0,[z1,z2,z194,z8,z20,z6]),(0,[z1,z2,z3,z180,z20,z6]),(0,[z110,z1,z2,z4,z5,z81]),(0,[z1,z2,z3,z8,z1198,z6]),(0,[z1,z2,z3,z23,z5,z6]),(0,[z1,z2,z994,z4,z5,z6])],[(0,[z1,z2,z1199,z8,z5,z6]),(0,[z10,z1,z2,z3,z576,z6]),(0,[z1200,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z63,z298,z6]),(0,[z1,z2,z3,z1201,z5,z6]),(0,[z1,z72,z3,z5,z6,z14]),(0,[z1,z2,z8,z6,z81,z485]),(0,[z1,z2,z3,z25,z4,z14])],[(0,[z1,z2,z77,z8,z5,z6]),(0,[z1,z2,z3,z8,z438,z6]),(0,[z1,z2,z3,z8,z1202,z6]),(0,[z268,z2,z219,z8,z5,z6]),(0,[z1,z2,z102,z8,z20,z6]),(0,[z473,z1,z2,z3,z183,z6]),(0,[z1,z3,z5,z6,z14,z1203])],[(0,[z1,z2,z1204,z8,z5,z6]),(0,[z1,z2,z3,z8,z364,z55])],[(0,[z1,z2,z3,z8,z1205,z6]),(0,[z1,z2,z3,z20,z6,z188]),(0,[z10,z1,z2,z3,z877,z6]),(0,[z1,z2,z3,z4,z1206,z6])],[(0,[z137,z1,z3,z257,z5,z6])],[(0,[z507,z1,z2,z8,z20,z6]),(0,[z1,z2,z3,z5,z6,z1207]),(0,[z1,z2,z3,z48,z8,z782])],[(0,[z1,z1208,z3,z8,z5,z6]),(0,[z1,z3,z8,z748,z5,z6]),(0,[z1,z72,z34,z8,z5,z6]),(0,[z1,z2,z309,z339,z5,z6])],[(0,[z1,z2,z3,z8,z1209,z6]),(0,[z414,z1,z2,z8,z20,z6]),(0,[z1,z273,z2,z3,z6,z14]),(0,[z1,z2,z3,z5,z616,z14]),(0,[z1,z2,z3,z25,z465,z6]),(0,[z1,z2,z3,z1210,z180,z6]),(0,[z1,z1067,z2,z5,z6,z14])]],
   [[(0,[z1,z2,z3,z294,z8,z6]),(0,[z1,z2,z102,z20,z6,z14]),(0,[z1,z2,z3,z6,z1211,z14])],[(0,[z1,z2,z3,z1212,z5,z6]),(0,[z28,z2,z3,z8,z62,z6]),(0,[z1,z2,z3,z1213,z5,z6]),(0,[z1,z2,z8,z56,z526,z6]),(0,[z1,z2,z8,z20,z6,z607])],[(0,[z1,z1214,z3,z8,z5,z6]),(0,[z125,z2,z3,z54,z5,z6]),(0,[z1,z355,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z6,z1215])],[(0,[z95,z2,z67,z8,z56,z6]),(0,[z1,z2,z3,z25,z6,z563]),(0,[z1,z2,z3,z447,z30,z6]),(0,[z1,z2,z3,z8,z1216,z6]),(0,[z1,z2,z34,z4,z5,z109])],[(0,[z126,z3,z13,z8,z42,z6]),(0,[z1,z2,z3,z1217,z5,z6]),(0,[z1,z2,z3,z1218,z8,z6]),(0,[z1,z987,z31,z8,z5,z6]),(0,[z1219,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z351]),(0,[z672,z1,z2,z3,z25,z6]),(0,[z1,z2,z3,z8,z6,z152]),(0,[z1,z2,z3,z1220,z5,z6]),(0,[z1,z72,z3,z8,z42,z6]),(0,[z1,z2,z8,z525,z6,z81]),(0,[z1,z2,z3,z8,z769,z6])],[(0,[z1,z1221,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1222,z6]),(0,[z1,z2,z1223,z8,z5,z6]),(0,[z110,z1,z2,z294,z8,z6])],[(0,[z1,z2,z3,z1224,z5,z6]),(0,[z10,z1,z2,z3,z6,z534]),(0,[z1,z2,z3,z580,z6,z14])],[(0,[z93,z1,z3,z8,z5,z814])],[(0,[z1,z1225,z2,z8,z5,z6]),(0,[z1,z2,z219,z8,z5,z6]),(0,[z1,z2,z101,z48,z20,z6]),(0,[z1,z2,z3,z172,z56,z6]),(0,[z1,z2,z3,z8,z1226,z6])],[(0,[z10,z1,z2,z3,z8,z6]),(0,[z2,z890,z67,z8,z5,z6]),(0,[z1,z1227,z3,z8,z5,z6]),(0,[z279,z2,z3,z4,z62,z6]),(0,[z1,z2,z3,z5,z6,z1228]),(0,[z1,z2,z3,z447,z6,z55]),(0,[z1,z2,z3,z8,z6,z1229]),(0,[z1,z2,z3,z8,z16,z6])],[(0,[z503,z2,z67,z8,z5,z6]),(0,[z1219,z2,z3,z5,z6,z14])],[(0,[z115,z10,z1,z2,z3,z6]),(0,[z125,z473,z1,z2,z3,z6]),(0,[z10,z1,z355,z3,z8,z6]),(0,[z1,z2,z3,z8,z880,z6]),(0,[z1,z2,z3,z972,z4,z6])],[(0,[z83,z2,z3,z132,z5,z6]),(0,[z1,z2,z3,z824,z8,z6]),(0,[z1,z2,z3,z8,z1230,z6]),(0,[z1,z2,z8,z20,z6,z485]),(0,[z129,z2,z3,z8,z76,z6]),(0,[z1,z2,z3,z5,z6,z837])],[(0,[z646,z1,z2,z8,z56,z6]),(0,[z1,z2,z3,z1231,z20,z6])],[(0,[z1,z355,z3,z8,z42,z6]),(0,[z10,z1,z2,z3,z312,z6]),(0,[z1,z2,z219,z5,z6,z14]),(0,[z227,z2,z3,z8,z42,z6]),(0,[z110,z1,z2,z8,z76,z81])],[(0,[z1,z2,z3,z8,z6,z1232]),(0,[z1,z2,z3,z5,z99,z14]),(0,[z1,z2,z3,z8,z6,z1233]),(0,[z224,z1,z2,z3,z25,z6])]],
   [[(0,[z297,z2,z426,z8,z5,z6]),(0,[z12,z1,z2,z3,z8,z393])],[(0,[z1234,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z881,z8,z6]),(0,[z1235,z2,z3,z8,z56,z6])],[(0,[z1,z2,z3,z1236,z8,z6]),(0,[z1,z2,z3,z8,z255,z55]),(0,[z1,z2,z3,z220,z20,z6]),(1,[z1,z3,z8,z5,z814]),(0,[z1,z1237,z3,z8,z5,z6]),(0,[z1,z1238,z3,z8,z5,z6]),(0,[z224,z1,z2,z994,z8,z6]),(0,[z10,z1,z2,z3,z6,z519]),(0,[z1,z2,z443,z8,z6,z296])],[(0,[z1,z2,z3,z455,z6,z14]),(0,[z1,z2,z3,z8,z6,z1239]),(0,[z1,z2,z3,z8,z5,z795]),(0,[z1,z2,z216,z8,z6,z55]),(0,[z1161,z1,z2,z3,z63,z6])],[(0,[z10,z173,z2,z3,z132,z6]),(0,[z9,z2,z3,z8,z42,z71]),(0,[z1,z2,z3,z8,z1240,z6]),(0,[z1,z2,z3,z200,z20,z6])],[(0,[z1,z2,z3,z8,z1241,z6]),(0,[z1,z1242,z2,z3,z8,z6])],[(0,[z1,z2,z216,z385,z5,z6]),(0,[z1,z2,z3,z1155,z5,z6]),(0,[z1,z426,z8,z5,z6,z32]),(0,[z1,z2,z3,z25,z704,z6]),(0,[z1,z2,z3,z53,z4,z6]),(0,[z10,z1,z2,z3,z424,z6])],[(0,[z1,z2,z3,z169,z56,z6])],[(0,[z10,z0,z136,z3,z8,z6]),(0,[z1,z2,z3,z5,z6,z1243]),(0,[z1,z2,z3,z8,z88,z55]),(0,[z1,z2,z3,z8,z1244,z6]),(0,[z1,z2,z3,z25,z51,z6])],[(0,[z1,z256,z2,z8,z56,z6]),(0,[z1,z2,z3,z4,z397,z6]),(0,[z110,z1,z2,z8,z39,z81]),(0,[z1,z2,z3,z8,z6,z1245])],[(0,[z1246,z1,z2,z3,z220,z6])],[(0,[z1,z2,z3,z30,z6,z14]),(0,[z10,z1,z2,z783,z8,z6])],[(0,[z1,z2,z3,z8,z6,z1247]),(0,[z1,z2,z1248,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1249,z6]),(0,[z78,z1,z3,z8,z260,z6]),(1,[z1,z2,z972,z8,z6])],[(0,[z1,z2,z3,z5,z6,z1250]),(0,[z1,z2,z8,z1251,z5,z6]),(0,[z1252,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1253,z6]),(0,[z1,z2,z3,z8,z886,z6]),(0,[z1,z2,z3,z4,z42,z6]),(0,[z35,z1,z2,z3,z5,z837])],[(0,[z1046,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1254,z6]),(0,[z2,z3,z8,z823,z5,z6]),(0,[z1,z2,z3,z8,z1255,z6]),(0,[z1256,z1,z2,z3,z447,z6]),(0,[z1,z2,z3,z92,z4,z6]),(0,[z1,z2,z3,z1257,z5,z6]),(0,[z15,z1,z2,z849,z5,z6]),(0,[z1,z2,z3,z8,z1258,z6]),(0,[z224,z1,z2,z3,z311,z6])]],
   [[(0,[z1,z2,z3,z8,z6,z1259]),(0,[z1,z2,z3,z8,z6,z1260]),(0,[z1,z2,z3,z4,z56,z14]),(0,[z1,z2,z8,z5,z864,z81]),(0,[z1,z2,z3,z294,z4,z6])],[(0,[z1,z2,z3,z8,z96,z6]),(0,[z95,z2,z67,z8,z5,z6]),(0,[z1,z2,z3,z8,z1261,z6]),(0,[z144,z1,z2,z3,z25,z6])],[(0,[z1,z2,z3,z1262,z5,z6]),(0,[z1,z2,z3,z1263,z8,z6]),(0,[z1,z3,z8,z1264,z5,z6]),(0,[z1,z2,z3,z4,z493,z6]),(0,[z1,z2,z1265,z8,z5,z6]),(0,[z50,z1,z2,z3,z8,z122]),(0,[z1,z2,z3,z343,z123,z6]),(0,[z1,z2,z3,z5,z837,z14]),(0,[z1,z2,z3,z8,z1266,z6])],[(0,[z1,z2,z3,z8,z1267,z6]),(0,[z1,z90,z3,z8,z56,z6]),(0,[z1268,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z1269,z8,z6])],[(0,[z1270,z1,z2,z3,z20,z6]),(0,[z129,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z8,z42,z122]),(0,[z1,z2,z3,z4,z392,z6]),(0,[z1,z2,z3,z4,z746,z6]),(0,[z1,z2,z3,z42,z6,z277])],[(0,[z1,z2,z3,z8,z1271,z6]),(0,[z1,z2,z3,z5,z6,z1272]),(0,[z1,z3,z1264,z45,z5,z6]),(0,[z1,z2,z3,z172,z5,z6]),(0,[z10,z1,z2,z3,z23,z6]),(0,[z1,z2,z3,z8,z5,z939])],[(0,[z1,z2,z3,z1273,z5,z6]),(0,[z1,z2,z3,z5,z670,z14]),(0,[z1,z2,z3,z8,z1274,z6]),(0,[z1,z2,z3,z1275,z8,z6]),(0,[z301,z1,z371,z3,z8,z6]),(0,[z1,z2,z3,z8,z124,z939])],[(0,[z1,z900,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1276,z6]),(0,[z1,z2,z3,z8,z6,z1277]),(0,[z1,z2,z3,z8,z6,z1278]),(0,[z1,z2,z8,z1117,z42,z6])],[(0,[z1,z2,z8,z6,z485,z296]),(0,[z10,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z25,z6,z393]),(0,[z50,z1,z2,z3,z8,z55])],[(0,[z900,z3,z13,z8,z5,z6]),(1,[z2,z3,z8,z1101,z6]),(0,[z1,z2,z3,z8,z151,z393])],[(0,[z1,z2,z3,z1279,z8,z6]),(0,[z1,z2,z3,z8,z1280,z6]),(0,[z1,z2,z3,z4,z6,z204]),(0,[z1,z2,z3,z1281,z8,z6])],[(0,[z10,z1,z2,z3,z569,z6]),(0,[z1,z2,z3,z8,z1282,z6]),(0,[z1,z262,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z60,z837]),(0,[z1,z2,z3,z8,z42,z55])],[(0,[z1,z2,z3,z1283,z8,z6]),(0,[z1284,z2,z3,z8,z5,z6]),(0,[z1,z207,z3,z4,z38,z6]),(0,[z268,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z4,z5,z437])],[(0,[z1,z2,z3,z8,z6,z1285]),(0,[z173,z2,z3,z5,z6,z598]),(0,[z1,z2,z490,z8,z56,z6]),(0,[z1,z2,z3,z20,z6,z277])],[(0,[z1235,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z536,z55]),(1,[z1,z2,z3,z877,z6])]],
   [[(0,[z1,z2,z3,z8,z6,z1286]),(0,[z1,z2,z3,z8,z6,z1287])],[(0,[z1,z2,z8,z56,z477,z6]),(1,[z1,z987,z8,z5,z6]),(0,[z1288,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1289,z8,z6])],[(0,[z1,z2,z3,z1290,z8,z6]),(0,[z1,z2,z3,z56,z6,z563]),(0,[z1,z2,z3,z8,z5,z983]),(0,[z10,z1,z2,z3,z293,z6]),(0,[z57,z1,z2,z8,z56,z6]),(0,[z2,z3,z5,z6,z14,z1291]),(0,[z224,z1,z2,z994,z4,z6])],[(0,[z1,z2,z3,z1292,z5,z6]),(0,[z1293,z1,z2,z3,z8,z6]),(0,[z10,z1,z2,z3,z49,z6])],[(0,[z1,z2,z3,z1294,z5,z6]),(0,[z1,z2,z3,z25,z191,z6])],[(0,[z1,z2,z3,z169,z5,z6]),(0,[z10,z1,z2,z3,z63,z6]),(0,[z1,z2,z3,z8,z1295,z6]),(0,[z1,z2,z3,z381,z6,z14]),(0,[z1,z2,z3,z8,z1296,z6]),(0,[z110,z1,z2,z5,z81,z14])],[(0,[z1,z2,z216,z25,z8,z6]),(0,[z15,z1,z2,z427,z11,z6]),(0,[z163,z1,z2,z3,z6,z14]),(0,[z10,z1,z2,z3,z541,z6])],[(0,[z115,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z8,z1297,z6]),(0,[z1,z131,z3,z63,z5,z151]),(0,[z1,z2,z3,z8,z1298,z6]),(0,[z1,z2,z3,z139,z56,z6])],[(0,[z1,z2,z3,z8,z1299,z6]),(0,[z1300,z1,z2,z3,z8,z6]),(0,[z268,z2,z3,z200,z5,z6]),(0,[z1,z2,z3,z8,z5,z837]),(0,[z1,z2,z3,z343,z6,z14]),(0,[z1,z2,z972,z8,z42,z6])],[(0,[z1,z2,z3,z25,z307,z6]),(0,[z1,z2,z426,z4,z5,z6]),(0,[z1,z2,z3,z48,z474,z6])],[(0,[z1,z2,z1301,z3,z8,z6]),(0,[z1,z2,z3,z8,z6,z1302]),(0,[z192,z1,z2,z3,z25,z6]),(0,[z1,z2,z3,z42,z6,z14]),(0,[z1,z2,z3,z53,z6,z638])],[(0,[z1,z2,z3,z8,z75,z6]),(0,[z1,z2,z101,z48,z5,z6]),(0,[z1303,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z1094,z5,z6])],[(0,[z1,z2,z3,z8,z20,z6]),(0,[z199,z2,z3,z4,z153,z6]),(0,[z1,z2,z3,z8,z6,z1211]),(0,[z1304,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z1305,z6]),(0,[z1,z1306,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z42,z616]),(0,[z190,z2,z3,z8,z153,z6]),(1,[z1,z2,z972,z4,z6])],[(0,[z1,z2,z545,z8,z20,z6]),(0,[z1,z2,z3,z8,z1307,z6]),(0,[z1,z2,z8,z39,z525,z6]),(0,[z129,z2,z3,z139,z5,z6]),(0,[z1,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z796,z6])],[(0,[z126,z900,z3,z8,z5,z6]),(0,[z2,z3,z8,z1101,z5,z6]),(0,[z1,z2,z3,z1308,z8,z6]),(0,[z792,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z5,z415]),(0,[z1,z2,z56,z20,z6,z14])]],
   [[(0,[z10,z1,z2,z3,z218,z6]),(0,[z1,z2,z3,z8,z6,z1309]),(0,[z1,z2,z3,z1231,z5,z6]),(0,[z110,z1,z2,z139,z5,z81]),(0,[z1,z2,z3,z8,z1310,z6]),(0,[z1,z2,z3,z4,z801,z6])],[(0,[z1,z90,z3,z8,z5,z6])],[(0,[z1,z2,z77,z5,z6,z14]),(0,[z1,z2,z3,z8,z1311,z6]),(0,[z1024,z1,z2,z3,z6,z563]),(0,[z1,z2,z3,z92,z8,z6]),(0,[z1,z2,z3,z4,z6,z522])],[(0,[z1,z2,z3,z8,z1312,z6]),(0,[z1,z2,z3,z97,z8,z6]),(0,[z1,z2,z3,z8,z1313,z6]),(0,[z1,z2,z3,z8,z6,z1314]),(0,[z1,z2,z3,z20,z6,z14]),(0,[z1,z2,z3,z1315,z8,z6]),(0,[z1,z2,z34,z8,z16,z109])],[(0,[z29,z2,z3,z8,z153,z6]),(0,[z1,z154,z31,z8,z6,z55]),(0,[z224,z1,z2,z3,z6,z534])],[(0,[z0,z136,z3,z25,z8,z6]),(0,[z125,z2,z3,z475,z5,z6]),(0,[z1,z2,z3,z36,z14,z55]),(0,[z1,z262,z3,z139,z5,z6]),(0,[z1316,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z1317,z6]),(0,[z1318,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z139,z6])],[(0,[z1,z2,z3,z8,z1319,z6]),(0,[z1,z90,z3,z5,z6,z14]),(0,[z1,z2,z3,z1320,z5,z6]),(0,[z1,z2,z3,z8,z1321,z6]),(0,[z1,z2,z3,z200,z5,z6]),(0,[z1,z2,z3,z5,z6,z201]),(0,[z224,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z1322,z5,z6])],[(0,[z282,z1,z2,z8,z5,z81]),(0,[z1,z2,z3,z1323,z5,z6]),(0,[z279,z2,z3,z8,z1101,z6]),(0,[z199,z2,z3,z8,z342,z6]),(0,[z1,z2,z3,z63,z42,z6]),(0,[z1,z2,z3,z53,z4,z14])],[(0,[z1,z2,z615,z8,z20,z6]),(0,[z1,z2,z3,z8,z1324,z6]),(0,[z1,z355,z216,z8,z5,z6]),(0,[z1,z2,z3,z39,z6,z14]),(0,[z50,z1,z2,z3,z4,z55])],[(0,[z0,z209,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z903]),(0,[z1,z2,z3,z8,z6,z1325]),(0,[z1,z2,z3,z8,z1326,z6]),(0,[z10,z1,z2,z3,z4,z437]),(0,[z1,z2,z3,z51,z6,z55])],[(0,[z1,z2,z3,z1281,z4,z6]),(0,[z1,z2,z3,z4,z6,z534])],[(0,[z1,z2,z3,z1327,z5,z6]),(0,[z1,z2,z34,z5,z109,z188]),(0,[z1,z2,z3,z23,z42,z6])],[(0,[z165,z1,z2,z8,z525,z6]),(0,[z28,z2,z3,z310,z8,z6])],[(0,[z1,z1328,z3,z8,z5,z6]),(0,[z1,z2,z77,z8,z42,z6]),(0,[z110,z129,z2,z8,z5,z81])],[(0,[z125,z273,z2,z3,z54,z6]),(0,[z108,z1,z2,z3,z25,z6]),(0,[z9,z2,z216,z8,z5,z71]),(0,[z1,z2,z3,z8,z42,z618]),(0,[z1,z1329,z3,z8,z5,z6]),(0,[z1,z2,z3,z180,z56,z6]),(0,[z1,z2,z3,z745,z6,z14]),(0,[z83,z2,z3,z134,z5,z6]),(0,[z1,z2,z406,z8,z525,z6])]],
   [[(0,[z1,z2,z3,z8,z1330,z6]),(0,[z1,z1331,z3,z8,z5,z6]),(0,[z1,z2,z1332,z8,z5,z6]),(0,[z1,z207,z3,z38,z6,z14]),(1,[z1,z2,z8,z886,z6]),(0,[z1333,z1,z2,z3,z20,z6]),(0,[z1,z2,z8,z513,z20,z6]),(0,[z1,z2,z3,z8,z1334,z6])],[(0,[z767,z1,z2,z3,z385,z6])],[(0,[z10,z1,z2,z902,z8,z6]),(0,[z1,z2,z3,z8,z244,z6])],[(0,[z126,z3,z13,z8,z455,z6]),(0,[z1,z2,z3,z8,z42,z620]),(0,[z1,z509,z3,z8,z38,z6]),(0,[z1,z90,z3,z8,z42,z6]),(0,[z93,z1,z3,z25,z8,z32]),(0,[z1335,z1,z2,z3,z5,z6]),(0,[z1,z131,z3,z5,z151,z201])],[(0,[z224,z1,z2,z3,z424,z6])],[(0,[z1,z2,z3,z139,z5,z6]),(0,[z1,z2,z3,z8,z484,z55])],[(0,[z1,z2,z3,z5,z6,z1336]),(0,[z129,z2,z3,z180,z5,z6]),(0,[z275,z1,z2,z294,z8,z6])],[(0,[z1,z2,z3,z5,z6,z1337]),(0,[z125,z2,z3,z54,z42,z6]),(0,[z1,z2,z3,z385,z6,z55]),(0,[z1,z2,z3,z8,z1338,z6])],[(0,[z126,z3,z218,z13,z5,z6]),(0,[z1,z2,z1339,z8,z5,z6]),(0,[z1340,z1,z2,z3,z8,z6]),(0,[z1,z2,z688,z8,z20,z6]),(0,[z1,z2,z3,z5,z363,z14]),(0,[z1,z2,z3,z1341,z8,z6]),(0,[z1,z2,z219,z8,z397,z6]),(0,[z110,z1,z2,z180,z5,z81])],[(0,[z1,z2,z3,z8,z6,z1342]),(0,[z1,z2,z216,z4,z5,z6]),(0,[z144,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z519,z14]),(0,[z1,z2,z3,z4,z845,z6])],[(0,[z1,z2,z3,z8,z1343,z6])],[(0,[z1,z2,z1344,z8,z5,z6]),(0,[z1345,z1,z2,z3,z5,z6]),(0,[z1303,z1,z2,z3,z4,z6]),(0,[z1,z72,z8,z5,z6,z81]),(0,[z10,z1,z2,z3,z4,z14])],[(0,[z254,z1,z2,z3,z8,z6]),(0,[z1,z3,z5,z6,z14,z1346])],[(0,[z1,z2,z3,z8,z1347,z6]),(0,[z1,z2,z219,z8,z42,z6]),(0,[z1,z2,z3,z1289,z63,z6]),(0,[z1,z262,z3,z180,z5,z6])],[(0,[z1,z3,z8,z5,z6,z1203]),(0,[z1,z2,z3,z998,z8,z6]),(0,[z1,z2,z3,z1348,z5,z6]),(0,[z1,z2,z1070,z3,z8,z6]),(0,[z1,z2,z3,z4,z483,z6])],[(0,[z1,z2,z3,z218,z20,z6]),(0,[z1,z1349,z3,z8,z5,z6])]],
   [[(0,[z126,z3,z13,z25,z8,z6]),(0,[z1,z2,z3,z5,z6,z1350]),(0,[z1,z2,z8,z635,z20,z6]),(0,[z473,z1,z46,z2,z3,z6]),(0,[z18,z1,z2,z11,z5,z6]),(0,[z1,z2,z101,z48,z56,z6]),(0,[z1,z2,z34,z172,z5,z109]),(0,[z50,z1,z2,z3,z8,z393])],[(0,[z1,z2,z3,z8,z1351,z6]),(0,[z586,z2,z3,z8,z62,z6]),(0,[z1,z2,z3,z8,z1041,z6]),(0,[z1,z2,z3,z8,z1352,z6]),(0,[z10,z1,z2,z101,z48,z6]),(0,[z1,z2,z3,z8,z1353,z6])],[(0,[z1,z2,z3,z5,z1354,z6]),(0,[z1,z1355,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1356,z6]),(0,[z165,z84,z1,z8,z20,z6]),(0,[z1,z2,z3,z1357,z5,z6])],[(0,[z1,z2,z3,z97,z4,z6]),(0,[z199,z2,z3,z153,z6,z14]),(0,[z10,z1,z2,z216,z8,z6]),(0,[z1,z2,z3,z8,z56,z1127]),(0,[z1,z2,z3,z8,z42,z393])],[(0,[z1,z1358,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1359,z6])],[(0,[z0,z136,z3,z8,z6,z55]),(0,[z227,z2,z8,z5,z6,z81]),(0,[z1,z2,z3,z8,z1360,z6])],[(0,[z10,z1,z2,z3,z6,z563]),(0,[z1,z2,z3,z8,z1361,z6]),(0,[z93,z268,z3,z8,z5,z32]),(0,[z1,z3,z8,z5,z814,z32]),(0,[z1085,z1,z2,z3,z8,z6])],[(0,[z2,z3,z8,z5,z6,z954]),(0,[z1,z31,z8,z5,z6,z379]),(0,[z1,z154,z31,z25,z8,z6]),(0,[z224,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z496,z6]),(0,[z1,z2,z3,z220,z234,z6]),(0,[z1,z2,z3,z8,z6,z1362]),(0,[z1,z1363,z3,z8,z5,z6]),(0,[z1,z2,z3,z483,z6,z14])],[(0,[z1,z2,z3,z8,z1364,z6]),(0,[z1246,z1,z2,z3,z8,z6]),(0,[z163,z1,z2,z3,z8,z1127]),(0,[z1,z2,z3,z1365,z8,z6])],[(0,[z1,z2,z3,z1366,z5,z6]),(0,[z95,z2,z67,z5,z6,z14]),(0,[z1367,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z200,z234,z6]),(0,[z1,z2,z3,z220,z56,z6]),(0,[z1,z3,z8,z5,z6,z814]),(0,[z110,z1,z2,z8,z20,z81]),(0,[z1,z2,z3,z5,z6,z1194]),(0,[z224,z1,z2,z972,z8,z6]),(0,[z10,z1,z2,z3,z6,z1013])],[(0,[z1,z2,z3,z8,z1368,z6]),(0,[z1,z2,z3,z8,z1369,z6]),(0,[z35,z10,z1,z2,z3,z14])],[(0,[z1,z2,z1370,z8,z5,z6]),(0,[z1,z2,z3,z200,z56,z6]),(0,[z1,z2,z3,z1371,z172,z6]),(0,[z1,z2,z3,z1372,z6,z14])],[(0,[z1,z2,z3,z180,z5,z6]),(0,[z1,z2,z3,z742,z8,z6])],[(0,[z1,z2,z3,z8,z1373,z6]),(0,[z10,z1,z154,z31,z8,z6]),(0,[z1,z2,z3,z8,z6,z1374])],[(0,[z1,z2,z3,z4,z222,z6])]],
   [[(0,[z1,z2,z3,z8,z1375,z6]),(0,[z1,z2,z3,z8,z378,z55]),(0,[z1,z2,z3,z5,z6,z188])],[(0,[z1,z2,z294,z67,z8,z6]),(0,[z1,z2,z935,z8,z5,z6]),(0,[z1,z2,z3,z8,z1376,z6]),(0,[z1,z2,z3,z8,z1377,z6]),(0,[z1,z2,z3,z4,z891,z6])],[(0,[z192,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z1378,z6]),(0,[z1,z2,z21,z8,z20,z6]),(0,[z1,z2,z3,z1379,z8,z6]),(0,[z1,z2,z3,z849,z5,z6]),(0,[z1,z2,z8,z1251,z42,z6])],[(0,[z1,z2,z3,z8,z1030,z6]),(0,[z1,z2,z3,z4,z5,z423]),(0,[z1,z2,z3,z8,z1380,z6]),(0,[z227,z2,z3,z8,z249,z6]),(0,[z442,z1,z2,z3,z8,z534])],[(0,[z319,z2,z3,z54,z5,z6]),(0,[z1,z1381,z3,z8,z5,z6]),(0,[z140,z1,z3,z8,z5,z32]),(0,[z1,z2,z3,z8,z6,z1382]),(0,[z1,z2,z3,z8,z1383,z6]),(0,[z1,z2,z3,z193,z8,z6]),(0,[z1,z2,z3,z8,z1384,z6])],[(0,[z1,z2,z3,z8,z1385,z6]),(0,[z95,z2,z67,z8,z42,z6]),(0,[z165,z1,z987,z8,z5,z6]),(0,[z135,z1,z3,z1264,z5,z6]),(0,[z1,z2,z3,z8,z1386,z6]),(0,[z93,z1,z3,z4,z5,z32]),(0,[z1,z2,z34,z8,z20,z109])],[(0,[z1,z2,z3,z222,z6,z14]),(0,[z1,z2,z3,z1387,z5,z6]),(0,[z1,z2,z3,z8,z1388,z6]),(0,[z1,z2,z3,z42,z14,z55]),(0,[z1,z2,z3,z1389,z8,z6])],[(0,[z1,z2,z3,z8,z1390,z6]),(0,[z1,z2,z3,z1391,z5,z6]),(0,[z1,z2,z3,z8,z1392,z6]),(0,[z1,z2,z8,z56,z158,z6]),(0,[z50,z1,z2,z3,z8,z939])],[(0,[z1,z2,z3,z8,z5,z1393]),(0,[z1,z2,z3,z8,z1394,z6]),(0,[z1395,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1264,z5,z6]),(0,[z78,z1,z3,z8,z19,z6]),(0,[z268,z2,z3,z220,z5,z6]),(0,[z10,z1,z2,z3,z8,z782]),(0,[z35,z1,z2,z3,z8,z393]),(0,[z1,z2,z3,z53,z6,z393]),(0,[z144,z1,z2,z3,z4,z6])],[(0,[z95,z2,z890,z8,z5,z6]),(0,[z1,z2,z216,z8,z1166,z6]),(0,[z1,z2,z3,z1396,z5,z6]),(0,[z1,z2,z3,z8,z748,z6]),(0,[z1397,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z348,z6]),(0,[z10,z1395,z2,z3,z8,z6]),(0,[z1,z2,z3,z42,z124,z277])],[(0,[z1,z131,z426,z8,z5,z6]),(0,[z1,z2,z3,z8,z1398,z6]),(0,[z1,z2,z3,z172,z42,z6]),(0,[z10,z1,z2,z3,z51,z6]),(0,[z1,z2,z3,z8,z42,z939])],[(0,[z254,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z427,z6,z14]),(0,[z1,z2,z3,z4,z381,z6])],[(0,[z173,z2,z3,z25,z132,z6]),(0,[z1058,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1399,z6]),(0,[z1400,z1,z2,z3,z8,z6]),(0,[z129,z2,z3,z8,z56,z6])],[(0,[z1,z2,z3,z8,z1401,z6]),(0,[z1,z2,z3,z4,z517,z6])],[(0,[z1,z2,z3,z5,z6,z1402]),(0,[z1,z1403,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1404,z6]),(0,[z24,z90,z3,z8,z5,z6]),(0,[z1,z2,z3,z447,z20,z6]),(0,[z1,z2,z3,z8,z291,z6]),(0,[z1,z2,z3,z8,z6,z1405]),(0,[z538,z2,z3,z8,z80,z6]),(0,[z1,z2,z3,z5,z6,z1406]),(0,[z1,z2,z3,z8,z1407,z6])]],
   [[(0,[z126,z3,z13,z8,z6,z55]),(0,[z1,z2,z3,z5,z6,z1408]),(0,[z1,z2,z3,z8,z1409,z6]),(0,[z1,z131,z3,z8,z20,z151]),(0,[z1397,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z8,z1410,z6]),(0,[z1,z2,z3,z8,z5,z1127])],[],[(0,[z1,z2,z3,z871,z385,z6]),(0,[z268,z2,z3,z8,z234,z6]),(0,[z1,z2,z3,z8,z5,z864])],[(0,[z1,z2,z3,z8,z6,z1411]),(0,[z1,z1412,z2,z3,z8,z6]),(0,[z9,z2,z3,z8,z71,z55]),(0,[z1,z262,z3,z8,z56,z6]),(0,[z1,z2,z3,z53,z191,z6])],[(0,[z1,z2,z3,z8,z1413,z6]),(0,[z1,z2,z3,z6,z14,z204]),(0,[z268,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z56,z99,z14]),(0,[z1,z2,z3,z474,z123,z6]),(0,[z1,z2,z3,z1414,z8,z6])],[(0,[z9,z2,z3,z8,z5,z954]),(0,[z1,z2,z3,z8,z1415,z6])],[(0,[z1,z2,z3,z1416,z8,z6]),(0,[z10,z1,z1065,z3,z8,z6])],[(0,[z1,z2,z3,z8,z1417,z6]),(0,[z1,z2,z3,z220,z5,z6]),(0,[z1,z2,z3,z8,z348,z55]),(0,[z1,z2,z3,z6,z1105,z14]),(0,[z1,z2,z3,z1418,z8,z6])],[(0,[z370,z1,z2,z3,z8,z55]),(0,[z1,z2,z216,z8,z438,z6]),(0,[z743,z2,z3,z8,z5,z6]),(0,[z1,z451,z3,z8,z38,z6]),(0,[z1,z131,z3,z8,z5,z814]),(0,[z1,z2,z3,z8,z1419,z6]),(0,[z57,z1,z2,z56,z6,z14]),(0,[z1,z2,z3,z8,z541,z55]),(0,[z1,z2,z3,z25,z117,z6]),(0,[z1,z2,z3,z1365,z4,z6]),(0,[z50,z1,z2,z3,z23,z55])],[(0,[z173,z2,z3,z132,z20,z6]),(0,[z1,z2,z3,z169,z42,z6]),(0,[z1,z154,z31,z4,z5,z6]),(0,[z1,z2,z3,z1420,z5,z6]),(0,[z1,z2,z309,z48,z5,z6]),(0,[z1,z2,z40,z8,z20,z6]),(0,[z227,z2,z3,z8,z6,z55]),(0,[z1,z1421,z2,z3,z6,z14]),(0,[z224,z1,z2,z972,z4,z6])],[(0,[z1,z2,z3,z8,z6,z1422]),(0,[z129,z262,z3,z8,z5,z6])],[(0,[z1,z2,z3,z476,z20,z6]),(0,[z1,z2,z3,z25,z450,z6])],[(0,[z1,z2,z3,z8,z6,z1423]),(0,[z1,z2,z3,z8,z1424,z6]),(0,[z1,z355,z3,z385,z5,z6]),(0,[z1022,z1,z2,z3,z8,z6])],[(0,[z1,z308,z2,z8,z20,z6]),(0,[z1,z2,z3,z25,z6,z201]),(0,[z1,z2,z3,z1425,z8,z6]),(0,[z1,z2,z3,z1426,z8,z6])],[(0,[z115,z1,z2,z3,z56,z6]),(0,[z1,z2,z1427,z8,z5,z6]),(0,[z1,z2,z3,z1428,z5,z6]),(0,[z1,z2,z3,z4,z341,z6]),(0,[z163,z1,z2,z294,z8,z6]),(0,[z1,z2,z3,z42,z124,z14])]],
   [[(0,[z95,z1,z2,z8,z525,z6]),(0,[z1,z2,z3,z1429,z5,z6]),(0,[z1,z2,z3,z25,z447,z6]),(0,[z1,z2,z101,z48,z42,z6])],[(0,[z1,z2,z3,z8,z1430,z6]),(0,[z1,z2,z3,z1431,z5,z6]),(0,[z1,z2,z3,z8,z1432,z6])],[(0,[z1,z2,z3,z8,z1433,z6]),(0,[z1,z480,z2,z8,z56,z6]),(0,[z1,z2,z3,z8,z234,z6]),(0,[z1,z2,z3,z8,z1434,z6]),(0,[z1,z2,z3,z8,z6,z1435]),(0,[z1,z2,z663,z8,z56,z6]),(0,[z1,z2,z3,z49,z6,z393]),(0,[z1,z2,z3,z117,z6,z519]),(0,[z192,z1,z2,z3,z4,z6])],[(0,[z254,z1,z2,z3,z218,z6]),(0,[z9,z2,z3,z385,z5,z71]),(0,[z1,z2,z294,z48,z8,z6]),(0,[z10,z1,z2,z3,z8,z829]),(0,[z1,z2,z3,z4,z42,z14])],[(0,[z1,z2,z3,z8,z56,z6]),(0,[z1,z2,z3,z8,z6,z1436]),(0,[z297,z2,z3,z25,z8,z6]),(0,[z110,z10,z1,z2,z8,z81]),(0,[z1,z2,z34,z5,z109,z14]),(0,[z1,z2,z3,z6,z277,z55])],[(0,[z1,z2,z3,z8,z1437,z6]),(0,[z1,z2,z3,z1438,z8,z6]),(0,[z1,z299,z3,z8,z38,z6]),(0,[z1,z2,z3,z193,z4,z6]),(0,[z1,z2,z3,z8,z1439,z6]),(0,[z1,z2,z5,z6,z14,z1440])],[(0,[z1,z2,z3,z25,z6,z213])],[(0,[z1,z2,z3,z8,z1441,z6]),(0,[z1,z2,z3,z200,z397,z6]),(0,[z1,z2,z3,z8,z1442,z6]),(0,[z2,z3,z8,z5,z6,z1291]),(0,[z35,z1,z2,z3,z20,z14]),(0,[z1,z2,z3,z6,z1443,z14])],[(0,[z1,z2,z3,z1444,z8,z6]),(0,[z1,z2,z3,z278,z6,z14]),(0,[z1,z987,z2,z8,z5,z6]),(0,[z1,z2,z1445,z8,z5,z6])],[(0,[z1,z2,z3,z25,z385,z6]),(0,[z1,z2,z3,z8,z1446,z6])],[(0,[z163,z1,z2,z3,z8,z6]),(0,[z15,z1,z2,z11,z6,z55]),(0,[z1,z1447,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z1448,z6]),(0,[z50,z1,z2,z3,z14,z55]),(0,[z1,z2,z3,z4,z6,z519])],[(0,[z1,z2,z3,z8,z1449,z6]),(0,[z129,z2,z3,z8,z5,z6]),(0,[z1270,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z474,z6,z14]),(0,[z1,z2,z3,z5,z143,z14])],[(0,[z24,z2,z3,z8,z5,z592]),(0,[z1,z2,z3,z8,z6,z1450]),(0,[z1,z2,z3,z1451,z5,z6]),(0,[z1,z535,z3,z8,z260,z6]),(0,[z1,z2,z3,z200,z42,z6]),(0,[z1,z2,z3,z6,z14,z522]),(0,[z1,z2,z3,z25,z4,z534])],[(0,[z320,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z8,z1452,z6]),(0,[z1,z2,z3,z8,z1453,z6]),(0,[z110,z1,z2,z8,z5,z81]),(0,[z1,z2,z994,z8,z5,z6]),(0,[z1,z2,z3,z1114,z6,z14])],[(0,[z1,z2,z3,z8,z1454,z6]),(0,[z448,z2,z3,z8,z433,z6])],[(0,[z84,z1,z987,z8,z5,z6])]],
   [[(0,[z84,z1,z2,z294,z8,z6]),(0,[z135,z1,z3,z45,z6,z55]),(0,[z15,z1,z2,z11,z631,z6]),(0,[z1,z2,z3,z8,z6,z1110])],[(0,[z1,z2,z3,z8,z1455,z6]),(0,[z1,z154,z31,z8,z247,z6]),(0,[z129,z2,z3,z5,z6,z14])],[(0,[z1,z2,z3,z8,z1456,z6]),(0,[z2,z67,z8,z5,z6,z670]),(0,[z1,z262,z3,z8,z5,z6]),(0,[z15,z1,z2,z11,z33,z6])],[(0,[z268,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1457,z8,z6]),(0,[z1458,z1,z3,z8,z5,z6]),(0,[z279,z2,z3,z62,z6,z14]),(0,[z1,z2,z3,z291,z6,z14]),(0,[z1,z72,z3,z25,z8,z6]),(0,[z997,z1,z2,z3,z6,z188]),(0,[z1,z2,z3,z5,z6,z277]),(0,[z1,z2,z3,z1459,z8,z6])],[(0,[z1,z2,z3,z1460,z5,z6]),(0,[z1,z2,z3,z1461,z8,z6]),(0,[z199,z514,z2,z3,z8,z6]),(0,[z1,z2,z3,z1462,z5,z6]),(0,[z1,z2,z8,z580,z20,z6]),(0,[z1,z1403,z3,z8,z56,z6]),(0,[z1,z2,z3,z4,z580,z6])],[(0,[z126,z3,z13,z8,z366,z6]),(0,[z1,z1463,z3,z8,z5,z6]),(0,[z1,z2,z3,z1464,z8,z6]),(1,[z1,z2,z849,z5,z6]),(0,[z1,z2,z3,z8,z6,z1465]),(0,[z144,z1,z2,z3,z6,z519])],[(0,[z1,z1466,z2,z3,z8,z6]),(0,[z1,z273,z2,z3,z8,z6]),(0,[z1,z2,z3,z5,z379,z14]),(0,[z1,z2,z3,z8,z1467,z6])],[(0,[z1,z2,z3,z8,z1468,z6]),(0,[z538,z2,z3,z8,z62,z6]),(0,[z135,z473,z1,z2,z3,z6]),(0,[z1,z2,z101,z5,z6,z589]),(0,[z1,z2,z3,z4,z5,z666]),(0,[z1,z2,z3,z4,z20,z60])],[(0,[z1,z2,z3,z8,z1469,z6]),(0,[z1,z1470,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1471,z6]),(0,[z1,z262,z3,z5,z6,z14])],[(0,[z1,z2,z3,z1472,z5,z6]),(0,[z1,z2,z3,z8,z1473,z6]),(0,[z1,z2,z3,z5,z620,z14]),(0,[z1,z2,z3,z8,z42,z202]),(0,[z268,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z8,z1474,z6]),(0,[z1,z2,z3,z8,z1475,z6]),(0,[z1,z2,z3,z5,z6,z1476]),(0,[z1,z2,z443,z8,z20,z6]),(0,[z10,z1,z2,z3,z139,z6]),(0,[z800,z1,z2,z3,z172,z6]),(0,[z1458,z1,z3,z5,z6,z14]),(0,[z1,z2,z3,z1477,z8,z6])],[(0,[z1478,z1,z2,z3,z8,z6]),(0,[z1479,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z348,z296]),(0,[z1,z2,z3,z139,z42,z6]),(0,[z1,z2,z3,z8,z6,z749])],[(0,[z0,z136,z3,z4,z5,z6]),(0,[z224,z1,z2,z3,z8,z437]),(0,[z144,z1,z2,z3,z4,z14])],[(0,[z1,z2,z3,z8,z1480,z6]),(0,[z1,z2,z426,z8,z20,z6]),(0,[z1,z2,z3,z8,z1481,z6])],[(0,[z1,z2,z3,z8,z1482,z6]),(0,[z115,z1,z2,z3,z5,z6]),(0,[z263,z2,z3,z8,z5,z71]),(0,[z1,z2,z3,z8,z1483,z6]),(0,[z1,z355,z3,z25,z8,z6]),(1,[z1,z2,z3,z8,z782]),(0,[z227,z2,z3,z25,z8,z6]),(0,[z1,z72,z3,z8,z249,z6])],[(0,[z1,z2,z3,z8,z1484,z6]),(0,[z1,z1485,z3,z8,z5,z6]),(0,[z1,z2,z3,z25,z637,z6]),(0,[z1486,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z1487,z5,z6]),(0,[z1,z2,z3,z8,z6,z1488]),(0,[z1,z2,z294,z8,z109,z6])],[(0,[z1,z2,z3,z1489,z5,z6]),(0,[z199,z2,z3,z8,z1101,z6]),(0,[z1,z2,z3,z1490,z8,z6]),(0,[z1,z2,z3,z8,z1491,z6])]],
   [[(0,[z1,z2,z3,z4,z455,z6]),(0,[z1,z2,z3,z8,z1492,z6]),(0,[z1,z2,z3,z8,z1493,z6]),(0,[z297,z3,z8,z5,z6,z32])],[(0,[z1494,z1,z2,z3,z5,z6]),(0,[z1,z535,z3,z8,z82,z6])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z126,z3,z346,z13,z8,z6]),(0,[z1,z2,z3,z8,z1495,z6]),(0,[z1,z2,z8,z20,z6,z170]),(0,[z1,z2,z3,z5,z6,z798])],[(0,[z9,z2,z3,z25,z8,z71]),(0,[z1,z308,z31,z8,z5,z6]),(0,[z35,z1,z2,z3,z14,z55])],[(0,[z37,z1,z2,z8,z56,z6]),(0,[z297,z2,z3,z8,z6,z55]),(0,[z1496,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z1497]),(0,[z1,z2,z3,z8,z6,z1498]),(0,[z224,z1,z2,z3,z49,z6])],[(0,[z1,z2,z426,z220,z5,z6]),(0,[z93,z1,z219,z8,z5,z32]),(0,[z10,z1,z2,z3,z474,z6]),(1,[z1,z2,z8,z5,z864])],[(0,[z1,z1499,z3,z8,z5,z6]),(0,[z227,z72,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z295]),(0,[z1,z2,z3,z25,z4,z644])],[(0,[z1,z2,z3,z218,z56,z6]),(0,[z115,z1,z2,z3,z25,z6]),(0,[z1,z2,z3,z8,z1500,z6]),(0,[z1,z2,z3,z8,z298,z6]),(0,[z1,z2,z426,z200,z5,z6]),(0,[z1,z2,z3,z25,z6,z188]),(0,[z1,z2,z3,z8,z1501,z6])],[(0,[z1,z2,z3,z5,z6,z14]),(0,[z1,z1502,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1503,z6]),(0,[z473,z1,z2,z3,z6,z14])],[(0,[z1,z2,z3,z8,z594,z55]),(0,[z15,z1,z2,z25,z11,z6]),(0,[z1,z2,z3,z25,z180,z6]),(0,[z1,z2,z3,z8,z6,z1504]),(0,[z1,z2,z3,z4,z5,z644]),(0,[z319,z2,z3,z5,z6,z389]),(0,[z144,z1,z2,z3,z23,z6]),(0,[z1,z2,z3,z8,z6,z1505])],[(0,[z1,z2,z3,z4,z278,z6]),(0,[z1,z2,z3,z8,z265,z6]),(0,[z750,z1,z2,z8,z5,z6]),(0,[z165,z84,z1,z8,z56,z6]),(0,[z1506,z1,z2,z3,z8,z6]),(0,[z1507,z2,z3,z8,z5,z6]),(0,[z163,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z60,z55])],[(0,[z1,z2,z3,z8,z1508,z6]),(0,[z1,z2,z3,z8,z1509,z6])],[(0,[z1,z2,z3,z1510,z8,z6]),(0,[z1,z2,z3,z4,z6,z296]),(0,[z641,z1,z2,z3,z8,z122])],[(0,[z173,z2,z3,z132,z5,z6]),(0,[z1,z2,z3,z56,z6,z201]),(0,[z1,z2,z3,z8,z1511,z6]),(0,[z1,z2,z3,z4,z244,z60])],[(0,[z1,z2,z1512,z8,z5,z6]),(0,[z1,z2,z3,z1513,z5,z6]),(0,[z1,z2,z3,z8,z6,z1514]),(0,[z1,z2,z3,z8,z1515,z6])],[(0,[z1,z2,z3,z4,z366,z6]),(0,[z115,z1,z2,z3,z42,z6]),(0,[z78,z1,z3,z8,z354,z6]),(0,[z1,z2,z426,z8,z234,z6])]],
   [[(0,[z1,z2,z1516,z8,z5,z6]),(1,[z900,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1517,z6]),(0,[z1,z2,z3,z823,z5,z6])],[(0,[z1,z2,z3,z8,z1518,z6]),(0,[z1,z3,z8,z5,z6,z1346]),(0,[z1,z2,z3,z4,z6,z485])],[(0,[z1,z2,z1519,z8,z5,z6]),(0,[z110,z1,z2,z8,z56,z81]),(0,[z1,z2,z3,z1520,z56,z6]),(0,[z1,z2,z3,z180,z42,z6])],[(0,[z1,z2,z3,z1521,z5,z6]),(0,[z1,z72,z3,z8,z6,z55]),(0,[z1,z2,z3,z1459,z4,z6])],[(0,[z1,z2,z219,z8,z938,z6]),(0,[z1,z131,z3,z5,z151,z14])],[(0,[z1522,z1,z2,z3,z8,z6]),(0,[z173,z2,z3,z132,z265,z6]),(0,[z1,z2,z216,z169,z5,z6])],[(0,[z126,z3,z13,z4,z5,z6]),(0,[z282,z2,z3,z8,z5,z71]),(0,[z1333,z1,z2,z3,z5,z6]),(0,[z1,z273,z2,z3,z4,z6]),(0,[z9,z355,z3,z8,z5,z71]),(0,[z1,z2,z1523,z8,z5,z6]),(0,[z10,z1,z2,z219,z8,z6]),(0,[z1,z2,z3,z631,z6,z14]),(0,[z473,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z8,z14,z122]),(0,[z144,z1,z2,z3,z49,z6])],[(0,[z1,z2,z3,z8,z315,z6]),(0,[z10,z227,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z249,z6]),(0,[z1,z2,z3,z338,z6,z14])],[(0,[z10,z1,z2,z426,z8,z6]),(0,[z1,z2,z3,z23,z6,z55])],[(0,[z1,z2,z3,z1524,z5,z6]),(0,[z1,z2,z3,z8,z1525,z6]),(0,[z1526,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1527,z6]),(0,[z1,z2,z3,z1477,z4,z6])],[(0,[z93,z297,z3,z8,z5,z32]),(0,[z1,z2,z3,z341,z6,z14]),(0,[z1,z2,z3,z6,z1465,z14]),(0,[z1,z2,z3,z1528,z8,z6])],[(0,[z1,z2,z216,z8,z75,z6]),(0,[z135,z10,z1,z3,z45,z6]),(0,[z110,z1,z2,z8,z5,z864])],[(0,[z1,z2,z3,z218,z1473,z6]),(0,[z1,z2,z216,z8,z20,z6]),(0,[z1,z2,z3,z8,z1529,z6]),(0,[z1,z2,z3,z4,z5,z536]),(0,[z1,z2,z3,z53,z8,z534])],[(0,[z1,z2,z3,z8,z323,z6]),(0,[z1530,z1,z2,z3,z8,z6]),(0,[z1,z355,z3,z8,z6,z55]),(0,[z1,z2,z77,z385,z5,z6]),(0,[z1,z2,z3,z385,z438,z6]),(0,[z1,z2,z3,z8,z6,z1531]),(0,[z135,z1,z3,z257,z5,z6]),(0,[z1,z2,z101,z47,z48,z6]),(0,[z1,z2,z3,z1532,z8,z6])],[(0,[z1,z2,z3,z1533,z8,z6]),(0,[z1,z2,z3,z8,z1534,z6]),(0,[z1,z2,z3,z8,z6,z782]),(0,[z1,z2,z34,z8,z56,z109])],[(0,[z263,z1,z3,z8,z5,z32]),(0,[z1,z2,z3,z8,z1535,z6]),(0,[z1,z2,z1536,z8,z5,z6])]],
   [[(0,[z1,z355,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z1537,z6]),(0,[z268,z2,z426,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z1538]),(0,[z1,z2,z3,z8,z42,z99]),(0,[z227,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z42,z213]),(0,[z1,z2,z3,z1372,z8,z6])],[(0,[z136,z900,z3,z8,z5,z6]),(0,[z1,z90,z216,z8,z5,z6]),(0,[z1,z2,z3,z8,z1539,z6]),(0,[z93,z1,z3,z8,z32,z55]),(0,[z1,z2,z3,z4,z6,z393])],[(0,[z2,z3,z132,z823,z5,z6]),(0,[z1,z90,z3,z385,z5,z6]),(0,[z1,z2,z34,z8,z5,z864]),(0,[z1,z2,z3,z4,z1081,z6]),(0,[z1,z2,z3,z8,z939,z55])],[(0,[z1,z2,z1540,z8,z5,z6]),(0,[z125,z2,z3,z54,z6,z55]),(0,[z1,z2,z3,z6,z14,z296])],[],[(0,[z1,z2,z3,z218,z5,z6]),(0,[z1541,z1,z2,z3,z8,z5]),(0,[z125,z85,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z1542,z6]),(0,[z1,z2,z3,z8,z6,z1543]),(0,[z1,z2,z309,z4,z20,z6]),(0,[z203,z1,z2,z3,z8,z55])],[(0,[z10,z1,z2,z3,z208,z6]),(0,[z9,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z4,z6,z122]),(0,[z1,z2,z8,z5,z109,z864])],[(0,[z1,z2,z3,z1544,z8,z6]),(0,[z1,z2,z3,z438,z6,z14]),(0,[z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z8,z1156,z6]),(0,[z1,z2,z3,z8,z6,z1545]),(0,[z1,z2,z3,z8,z6,z1546])],[(0,[z1,z2,z3,z8,z1547,z6]),(0,[z165,z84,z1,z8,z5,z6]),(0,[z1,z2,z3,z220,z397,z6]),(0,[z1,z131,z3,z8,z56,z151]),(0,[z1,z2,z3,z6,z14,z485])],[(0,[z1,z2,z3,z441,z6,z14]),(0,[z10,z1,z2,z3,z162,z6]),(0,[z1,z2,z219,z8,z6,z55]),(0,[z10,z1,z2,z3,z180,z6])],[(0,[z1,z2,z3,z8,z6,z1548]),(0,[z1,z3,z8,z5,z151,z814]),(0,[z1,z2,z3,z8,z6,z1549])],[(0,[z1,z2,z3,z8,z1550,z6]),(0,[z1,z1551,z3,z8,z5,z6]),(0,[z1,z207,z3,z376,z8,z6]),(0,[z1,z2,z3,z25,z169,z6]),(0,[z1,z2,z48,z849,z5,z6]),(0,[z1,z2,z101,z25,z48,z6]),(0,[z1,z2,z3,z8,z1552,z6])],[(0,[z1,z2,z3,z8,z6,z1443]),(0,[z1,z2,z3,z8,z6,z1553]),(0,[z224,z1,z2,z3,z4,z14])],[(0,[z1,z2,z3,z366,z6,z14]),(0,[z1,z2,z3,z1554,z8,z6]),(0,[z1555,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z220,z42,z6]),(0,[z1,z2,z3,z4,z6,z55]),(0,[z2,z3,z5,z6,z14,z844])],[(0,[z165,z84,z1,z5,z6,z14]),(0,[z1,z2,z3,z8,z393,z32]),(0,[z1,z2,z3,z1556,z8,z6]),(0,[z1,z2,z3,z8,z1557,z6]),(0,[z50,z1,z2,z3,z51,z55])],[(0,[z1,z2,z3,z346,z6,z14]),(0,[z1,z2,z3,z1558,z5,z6]),(0,[z1,z2,z426,z8,z5,z6]),(0,[z1,z2,z3,z8,z1559,z6]),(0,[z1,z2,z3,z8,z1560,z6]),(0,[z110,z1,z2,z8,z81,z296]),(0,[z1,z2,z3,z343,z8,z6]),(0,[z192,z1,z2,z3,z49,z6])]],
   [[(0,[z157,z84,z1,z8,z5,z6]),(0,[z1,z2,z3,z1520,z5,z6])],[(0,[z1,z1561,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1562,z6]),(0,[z1,z2,z3,z981,z6,z14])],[(0,[z173,z2,z3,z132,z56,z6]),(0,[z199,z2,z3,z8,z153,z6]),(0,[z1,z2,z3,z8,z6,z1563]),(0,[z1,z2,z3,z172,z6,z522]),(0,[z1,z2,z3,z4,z5,z534])],[(0,[z1,z2,z3,z1564,z5,z6]),(0,[z1,z2,z3,z4,z631,z6]),(0,[z1,z708,z3,z8,z56,z6])],[(0,[z1,z2,z3,z1565,z5,z6]),(0,[z473,z1,z2,z3,z25,z6]),(0,[z1,z2,z3,z476,z56,z6]),(0,[z1,z2,z3,z8,z1206,z6])],[(0,[z1,z2,z445,z3,z6,z14]),(0,[z78,z1,z3,z260,z6,z14]),(0,[z1,z2,z3,z32,z14,z55]),(0,[z1,z2,z3,z4,z33,z6]),(0,[z1,z2,z3,z8,z1566,z6])],[(0,[z1,z2,z3,z1567,z5,z6]),(0,[z461,z10,z1,z2,z3,z6]),(0,[z1,z2,z3,z56,z6,z188]),(0,[z1,z2,z3,z5,z6,z1568]),(0,[z1,z2,z3,z53,z8,z644])],[(0,[z1,z2,z3,z25,z200,z6]),(0,[z227,z2,z3,z8,z76,z6]),(0,[z1,z2,z3,z8,z1569,z6])],[(0,[z1,z2,z3,z1570,z5,z6]),(0,[z1,z154,z2,z8,z525,z6]),(0,[z165,z623,z1,z8,z5,z6]),(0,[z1,z2,z3,z1571,z8,z6]),(0,[z1,z2,z3,z8,z6,z1572]),(0,[z57,z1,z2,z8,z580,z6])],[(0,[z1,z2,z3,z8,z6,z1573]),(0,[z1,z2,z3,z8,z1574,z6]),(0,[z1,z2,z3,z8,z6,z1575]),(0,[z1,z2,z3,z8,z6,z1096]),(0,[z1576,z2,z3,z8,z5,z6]),(0,[z93,z1,z3,z8,z20,z32]),(0,[z1,z2,z3,z25,z123,z6]),(0,[z1,z2,z3,z863,z6,z14])],[(0,[z1,z2,z3,z25,z6,z277]),(0,[z1,z2,z3,z1310,z6,z14])],[(0,[z1,z2,z3,z877,z49,z6])],[(0,[z1,z2,z3,z8,z1577,z6]),(0,[z1,z2,z3,z1578,z5,z6]),(0,[z1,z2,z3,z8,z1579,z6]),(0,[z1,z2,z3,z71,z14,z55]),(0,[z1,z2,z3,z474,z11,z6]),(0,[z1,z1580,z3,z8,z5,z6]),(0,[z1,z2,z34,z8,z5,z109]),(0,[z1,z2,z3,z1210,z8,z6]),(0,[z1,z2,z3,z1371,z8,z6]),(0,[z1,z2,z3,z53,z4,z534])],[(0,[z1,z2,z77,z25,z8,z6]),(0,[z165,z84,z1,z8,z315,z6]),(0,[z1,z2,z3,z6,z14,z122]),(0,[z1,z2,z3,z1532,z4,z6]),(0,[z1,z2,z3,z4,z525,z6])],[(0,[z1,z1421,z2,z3,z8,z6]),(0,[z1,z1581,z2,z3,z8,z6]),(0,[z1,z2,z101,z48,z381,z6]),(0,[z1,z2,z3,z5,z14,z122])],[(0,[z1,z2,z3,z8,z1582,z6]),(0,[z1,z2,z47,z8,z580,z6]),(0,[z35,z1,z2,z3,z56,z14]),(0,[z1,z2,z3,z1151,z6,z14]),(0,[z230,z1,z2,z8,z39,z6])]],
   [[(0,[z1,z2,z3,z1583,z8,z6]),(0,[z129,z2,z3,z8,z42,z6]),(0,[z1,z2,z3,z4,z338,z6])],[(0,[z1,z1584,z2,z3,z8,z6]),(0,[z10,z1,z2,z3,z6,z201]),(0,[z1,z2,z3,z47,z6,z14]),(0,[z1,z299,z3,z8,z302,z6]),(0,[z1,z314,z3,z253,z8,z6])],[(0,[z1585,z1,z2,z3,z8,z6]),(0,[z279,z2,z3,z8,z62,z6]),(0,[z1,z90,z3,z25,z8,z6]),(0,[z1256,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z151,z14,z55]),(0,[z110,z1,z2,z8,z42,z81]),(0,[z1,z2,z3,z8,z42,z143]),(0,[z1,z2,z994,z8,z42,z6])],[(0,[z10,z1,z2,z3,z447,z6]),(0,[z1,z2,z3,z8,z1586,z6]),(0,[z1,z2,z3,z1587,z5,z6]),(0,[z268,z2,z3,z8,z397,z6]),(0,[z1,z2,z3,z6,z1278,z201])],[(0,[z1,z2,z3,z5,z6,z1588]),(0,[z1589,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z287,z5,z14]),(0,[z1,z2,z3,z8,z1590,z6]),(0,[z93,z1,z3,z200,z5,z32]),(0,[z1,z2,z3,z8,z81,z122]),(0,[z1,z2,z3,z8,z1591,z6]),(0,[z1,z2,z3,z6,z14,z55])],[(0,[z1,z2,z3,z447,z5,z6]),(0,[z1592,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z1593,z8,z6]),(0,[z300,z1,z2,z3,z5,z14]),(0,[z297,z2,z219,z8,z5,z6]),(0,[z1,z131,z3,z8,z5,z151]),(0,[z15,z1,z2,z8,z580,z6])],[(0,[z1,z2,z1594,z3,z8,z6]),(0,[z1,z2,z421,z8,z20,z6]),(0,[z24,z2,z3,z5,z36,z14]),(0,[z1,z2,z3,z4,z247,z6]),(0,[z1,z262,z3,z8,z42,z6]),(0,[z1,z2,z3,z4,z1149,z6])],[(0,[z1595,z1,z2,z3,z8,z6]),(0,[z268,z2,z3,z8,z42,z6])],[(0,[z1,z2,z219,z8,z1027,z6]),(0,[z98,z1,z3,z8,z19,z6]),(0,[z168,z1,z2,z513,z5,z6])],[(0,[z1,z2,z3,z8,z6,z1596]),(0,[z1,z2,z3,z8,z1597,z6]),(0,[z1,z2,z8,z5,z6,z1440]),(0,[z1,z2,z3,z4,z5,z588]),(0,[z297,z2,z3,z4,z5,z6]),(0,[z1,z2,z972,z4,z5,z6])],[(0,[z1,z131,z3,z8,z298,z151])],[(0,[z1,z2,z34,z8,z5,z571]),(0,[z1,z2,z3,z4,z441,z6]),(0,[z10,z1,z2,z3,z385,z6]),(0,[z1,z2,z3,z8,z1598,z6]),(0,[z1,z2,z219,z25,z8,z6]),(0,[z1,z2,z3,z724,z6,z14]),(0,[z224,z1,z2,z3,z51,z6])],[(0,[z1,z2,z3,z4,z214,z6]),(0,[z199,z2,z3,z8,z94,z6]),(0,[z1,z2,z3,z8,z1599,z6]),(0,[z1,z154,z31,z8,z20,z6]),(0,[z1,z2,z3,z8,z6,z1600])],[(0,[z1601,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z1556,z4,z6]),(0,[z163,z1,z2,z64,z8,z6])],[(0,[z353,z2,z3,z8,z153,z6]),(0,[z1,z2,z3,z8,z6,z1602]),(0,[z1,z2,z3,z8,z1603,z6]),(0,[z1,z2,z3,z4,z56,z60]),(0,[z1,z2,z3,z25,z6,z14]),(0,[z1,z2,z3,z343,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 481) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 481).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 963).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1441).take 246) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1687)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [481, 482, 478, 246] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 121).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 235).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 345).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 454).take 58).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [121, 114, 110, 109, 58] = true :=
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

end PEqualNP.Outside.L_meta_40381

theorem PEqualNP.Outside.L_meta_40381 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276808352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276808352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40381.solve