import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39529_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono_k {ops : α → α → Finset α} {goal : α} {k₁ k₂ : ℕ} {av : Finset α}
    (hle : k₁ ≤ k₂) (h : build ops goal k₁ av) : build ops goal k₂ av := by
  induction hle with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono_av {ops : α → α → Finset α} {goal : α} {k : ℕ} {av₁ av₂ : Finset α}
    (hsub : av₁ ⊆ av₂) (h : build ops goal k av₁) : build ops goal k av₂ := by
  induction k generalizing av₁ av₂ with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn; apply sub; intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := fun u hu =>
          (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hu).2)).resolve_left (Finset.mem_erase.mp hu).1
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

theorem live_map {α β : Type} [DecidableEq α] [DecidableEq β]
    {ops1 : α → α → Finset α} {ops2 : β → β → Finset β}
    {g1 : α} {g2 : β} (f : α → β)
    (hinj : Function.Injective f) (hgoal : f g1 = g2)
    (hops : ∀ a b z, z ∈ ops1 a b → f z ∈ ops2 (f a) (f b))
    {k : ℕ} {s : Finset α} (h : live ops1 g1 k s) :
    live ops2 g2 k (s.image f) := by
  induction k generalizing s with
  | zero => change s = {g1} at h; subst h; simp [live, hgoal]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun he => hab (hinj he), f z, hops a b z hz, ?_, rest.image f, ?_, ?_⟩
      · intro hm
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
        exact hout (hinj he ▸ hu)
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih tail

end Live

def ops (n : ℕ) (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (n : ℕ) (a b : BitVec n) : Finset (BitVec n) :=
  ((ops n a b).filter (fun z => z != 0 && z != BitVec.allOnes n)).toFinset
def nrm (n : ℕ) (u : BitVec n) : BitVec n := if u.getLsbD 0 then ~~~u else u

theorem ops_swap (n : ℕ) (a b : BitVec n) : basicOps n a b = basicOps n b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem ops_diff_ij {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (a b z : BitVec n)
    (hz : z ∈ basicOps n a b) (hd : z.getLsbD i ≠ z.getLsbD j) :
    a.getLsbD i ≠ a.getLsbD j ∨ b.getLsbD i ≠ b.getLsbD j := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz.1 with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      decide_eq_true hi, decide_eq_true hj, Bool.true_and, ha, hb]

def dif (n : ℕ) (w : BitVec n) (d : ℕ) : BitVec n := (w ^^^ (w >>> d)) &&& (BitVec.allOnes n >>> d)
def unionDif (n : ℕ) (ws : List (BitVec n)) (d : ℕ) : BitVec n := ws.foldr (fun w s => dif n w d ||| s) 0
def cover (n : ℕ) (jumps : List ℕ) (t : BitVec n) (ws : List (BitVec n)) : Bool :=
  jumps.all fun d => (dif n t d &&& unionDif n ws d) == dif n t d

theorem bit_dif {n : ℕ} {w : BitVec n} {d i : ℕ} (_hi : i < n) :
    (dif n w d).getLsbD i = true ↔ i + d < n ∧ w.getLsbD i ≠ w.getLsbD (i + d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

theorem bit_union (n : ℕ) (ws : List (BitVec n)) (d i : ℕ) :
    (unionDif n ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif n w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif n w d ||| unionDif n ws d).getLsbD i = true ↔ _
    simp [ih]

theorem live_cover {n k : ℕ} {jumps : List ℕ} {goal : BitVec n} {ws : List (BitVec n)}
    (h : live (basicOps n) goal k ws.toFinset) : cover n jumps goal ws = true := by
  apply List.all_eq_true.mpr; intro d _
  apply beq_iff_eq.mpr; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif n goal d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    obtain ⟨w, hw, hdw⟩ := live_separates (fun u : BitVec n => u.getLsbD i ≠ u.getLsbD (i + d))
      hne (ops_diff_ij i (i + d) hi hj) h
    rw [(bit_union n ws d i).mpr ⟨w, List.mem_toFinset.mp hw, (bit_dif hi).mpr ⟨hj, hdw⟩⟩]; rfl

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
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
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

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {α : Type} [DecidableEq α] {xs ys : List α} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def actN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p2 :: ps, n => Nat.bit (Nat.beq (Nat.mod (Nat.div n p2) 2) 1) (actN ps n)

def actB (n : ℕ) (ps : List ℕ) (x : BitVec n) : BitVec n := BitVec.ofNat n (actN ps x.toNat)

theorem mod_div_two_pow_eq_testBit (n p : ℕ) :
    Nat.beq (Nat.mod (Nat.div n (2 ^ p)) 2) 1 = n.testBit p := by
  change Nat.beq (n / 2 ^ p % 2) 1 = n.testBit p
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases h : n / 2 ^ p % 2 with
  | zero => rfl
  | succ k =>
    have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : k = 0 := by omega
    subst hk; rfl

theorem actN_testBit : ∀ (pi ps : List ℕ) (n k : ℕ),
    ps = pi.map (fun p => 2 ^ p) →
    (actN ps n).testBit k = (pi[k]?.map n.testBit).getD false
  | [], _, _, _, rfl => by simp [actN]
  | p :: pi, _, n, 0, rfl => by simp [actN, mod_div_two_pow_eq_testBit]
  | p :: pi, _, n, k + 1, rfl => by
    simp [actN, Nat.testBit_bit_succ, actN_testBit pi (pi.map (fun q => 2 ^ q)) n k rfl]

theorem actB_getLsbD (n : ℕ) (pi : List ℕ) (x : BitVec n) (k : ℕ) (hk : k < n) :
    (actB n (pi.map (fun p => 2 ^ p)) x).getLsbD k = (pi[k]?.map x.getLsbD).getD false := by
  unfold actB
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, actN_testBit pi _ x.toNat k rfl]
  cases pi[k]? <;> rfl

def symValid (n gsize : ℕ) (G_idx G_pow : Array (List ℕ)) (G_inv : Array ℕ) (goal : BitVec n) (g : ℕ) : Bool :=
  let pi := G_idx[g]?.getD []
  let inv := G_idx[G_inv[g]?.getD 0]?.getD []
  let ps := G_pow[g]?.getD []
  Nat.blt (G_inv[g]?.getD 0) gsize &&
  Nat.beq (G_inv[G_inv[g]?.getD 0]?.getD 0) g &&
  Nat.beq pi.length n &&
  Nat.beq inv.length n &&
  (ps == pi.map (fun p => 2 ^ p)) &&
  (actB n ps goal == goal) &&
  (List.range n).all (fun k => match pi[k]? with
    | some p => Nat.blt p n && (inv[p]? == some k)
    | none => false)

theorem actB_spec {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) :
    G_inv[g]?.getD 0 < gsize ∧
    G_inv[G_inv[g]?.getD 0]?.getD 0 = g ∧
    G_pow[g]?.getD [] = (G_idx[g]?.getD []).map (fun p => 2 ^ p) ∧
    actB n (G_pow[g]?.getD []) goal = goal ∧
    (∀ k < n, ∃ p < n, (G_idx[g]?.getD [])[k]? = some p ∧ (G_idx[G_inv[g]?.getD 0]?.getD [])[p]? = some k) := by
  have hv := List.all_eq_true.mp hvalid g (List.mem_range.mpr hg)
  unfold symValid at hv
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at hv
  refine ⟨hv.1.1.1.1.1.1, Nat.eq_of_beq_eq_true hv.1.1.1.1.1.2, hv.1.1.2, hv.1.2, fun k hk => ?_⟩
  have h1 := hv.2 k hk
  cases hp : (G_idx[g]?.getD [])[k]? with
  | none => simp [hp] at h1
  | some p =>
    simp only [hp, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h1
    exact ⟨p, h1.1, rfl, h1.2⟩

theorem actB_inv_left {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (x : BitVec n) :
    actB n (G_pow[G_inv[g]?.getD 0]?.getD []) (actB n (G_pow[g]?.getD []) x) = x := by
  obtain ⟨hinv_lt, hinv2, hpow, _, _⟩ := actB_spec hv g hg
  obtain ⟨_, _, hpow', _, hpi'⟩ := actB_spec hv (G_inv[g]?.getD 0) hinv_lt
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow', actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, hpk⟩ := hpi' k hk
  rw [hinv2] at hpk
  rw [hkp]; simp only [Option.map_some, Option.getD_some]
  rw [hpow, actB_getLsbD n _ _ p hp, hpk]; simp

theorem actB_inj {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : Function.Injective (actB n (G_pow[g]?.getD [])) :=
  Function.LeftInverse.injective (actB_inv_left hv g hg)

theorem actB_and {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a &&& b) = actB n (G_pow[g]?.getD []) a &&& actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_and]

theorem actB_or {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a ||| b) = actB n (G_pow[g]?.getD []) a ||| actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_or]

theorem actB_not {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a : BitVec n) :
    actB n (G_pow[g]?.getD []) (~~~a) = ~~~actB n (G_pow[g]?.getD []) a := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  simp [hkp, hk, hp]

theorem actB_zero {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) 0 = 0 := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp]

theorem actB_allOnes {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) (BitVec.allOnes n) = BitVec.allOnes n := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  rw [hkp]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_allOnes, hk, hp, decide_true]

theorem actB_ops {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b z : BitVec n) (hz : z ∈ basicOps n a b) :
    actB n (G_pow[g]?.getD []) z ∈ basicOps n (actB n (G_pow[g]?.getD []) a) (actB n (G_pow[g]?.getD []) b) := by
  simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hz ⊢
  refine ⟨?_, fun e => hz.2.1 (actB_inj hv g hg (e.trans (actB_zero hv g hg).symm)),
               fun e => hz.2.2 (actB_inj hv g hg (e.trans (actB_allOnes hv g hg).symm))⟩
  have hz' := hz.1
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz' ⊢
  rcases hz' with rfl | rfl | rfl | rfl
  · left; exact actB_and hv g hg a b
  · right; left; exact actB_or hv g hg a b
  · right; right; left; rw [actB_and hv g hg, actB_not hv g hg]
  · right; right; right; rw [actB_and hv g hg, actB_not hv g hg]

def checkChildP (n k : ℕ) (targets : List (List (BitVec n))) (nxt : List (BitVec n)) : Bool :=
  decide (nxt.length > k) || targets.any (fun t => sameSet nxt t)

def checkStepP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (k extra : ℕ)
    (targets : List (List (BitVec n))) (a b : BitVec n) (r : List (BitVec n)) : Bool :=
  (ops n a b).all fun w =>
    (w == 0 || w == BitVec.allOnes n || w == a || w == b || r.contains w) ||
    (!cover n jumps goal (w :: r) || checkChildP n k targets (w :: r)) &&
    ((extra == 0) ||
      ((!cover n jumps goal (w :: a :: r) || checkChildP n k targets (w :: a :: r)) &&
       (!cover n jumps goal (w :: b :: r) || checkChildP n k targets (w :: b :: r)))) &&
    ((extra < 2) || !cover n jumps goal (w :: a :: b :: r) || checkChildP n k targets (w :: a :: b :: r))

def checkNodeP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hs) =>
    decide ws.Nodup && !(ws.contains goal) && decide (ws.length ≤ k + 1) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepP n jumps goal k extra targets a b r)

def checkBlockP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeP n jumps goal gsize G_pow k cur prev (start + m) &&
      checkBlockP n jumps goal gsize G_pow k cur prev start m

theorem checkBlockP_at {n gsize k start m : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h : checkBlockP n jumps goal gsize G_pow k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeP n jumps goal gsize G_pow k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_P {n gsize k i : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hchk : checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hs⟩
  have hget : cur[i]? = some (ws, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeP at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps n) goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (G_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB n (G_pow[G_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [])).1.map (actB n (G_pow[g]?.getD []))).toFinset.image
        (actB n (G_pow[G_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB n (G_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec n} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps n a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps n) goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover n jumps goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepP at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes n || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildP n k targets (z :: kept) = true) : False := by
        unfold checkChildP at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with hgt | ⟨t, ht, hss⟩
        · omega
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap n a b ▸ hz)

theorem level_sound_P {n gsize k : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset :=
  fun i hi => node_sound_P hk hi hvalid hprev (hblk i hi)

theorem no_build_of_top {n gsize k rg : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {rows top_ws : List (BitVec n)}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hrg : rg < gsize)
    (hsub : rows.sublists.filter (fun ws => cover n jumps goal ws) = [rows])
    (hmatch : sameSet (rows.map (actB n (G_pow[rg]?.getD []))) top_ws = true)
    (hdead : ¬ live (basicOps n) goal k top_ws.toFinset) :
    ¬ build (basicOps n) goal k rows.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := rows.filter (· ∈ s)
  have hsubl : ws.Sublist rows := List.filter_sublist
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hcov : cover n jumps goal ws = true := live_cover (heq.symm ▸ hl)
  have hmem : ws ∈ rows.sublists.filter (fun zs => cover n jumps goal zs) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr hsubl, hcov⟩
  rw [hsub, List.mem_singleton] at hmem
  have hs_eq : s = rows.toFinset := by rw [← heq, hmem]
  have hl_rows : live (basicOps n) goal k rows.toFinset := hs_eq ▸ hl
  have hrg_g := (actB_spec hvalid rg hrg).2.2.2.1
  have hrot := live_map (actB n (G_pow[rg]?.getD [])) (actB_inj hvalid rg hrg) hrg_g (actB_ops hvalid rg hrg) hl_rows
  have himg : rows.toFinset.image (actB n (G_pow[rg]?.getD [])) =
      (rows.map (actB n (G_pow[rg]?.getD []))).toFinset := by
    ext u; simp [List.mem_map]
  rw [himg, sameSet_sound hmatch] at hrot
  exact hdead hrot


def jumps4 : List ℕ := [1,2,4,8]

def jumps5 : List ℕ := [1,2,4,8,16]

def jumps6 : List ℕ := [1,2,4,8,16,32]

def rows4 : List (BitVec 16) := [0xaaaa,0xcccc,0xf0f0,0xff00]

def rows5 : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def rows6 : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def goal6 : BitVec 64 := 0xfefefeeafeecf8e8

def projN {m : ℕ} : List ℕ → BitVec m → ℕ
  | [], _ => 0
  | idx :: idxs, w => Nat.bit (w.getLsbD idx) (projN idxs w)

theorem projN_testBit {m : ℕ} : ∀ (idxs : List ℕ) (w : BitVec m) (k : ℕ),
    (projN idxs w).testBit k = (idxs[k]?.map w.getLsbD).getD false
  | [], _, _ => by simp [projN]
  | idx :: idxs, w, 0 => by simp [projN]
  | idx :: idxs, w, k + 1 => by simp [projN, Nat.testBit_bit_succ, projN_testBit idxs w k]

def projB (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := BitVec.ofNat n (projN idxs w)
def projS (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := nrm n (projB n idxs w)

theorem projB_getLsbD (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) (k : ℕ) (hk : k < n) :
    (projB n idxs w).getLsbD k = (idxs[k]?.map w.getLsbD).getD false := by
  unfold projB; rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, projN_testBit]

theorem projB_and (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a &&& b) = projB n idxs a &&& projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_and]

theorem projB_or (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a ||| b) = projB n idxs a ||| projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_or]

theorem projB_not (n : ℕ) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n) (hlt : ∀ idx ∈ idxs, idx < m) (a : BitVec m) :
    projB n idxs (~~~a) = ~~~projB n idxs a := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  have hk' : k < idxs.length := by omega
  rw [List.getElem?_eq_getElem hk']
  have hmem := hlt idxs[k] (List.getElem_mem hk')
  simp [hk, hmem]

theorem projB_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projB n idxs (0 : BitVec m) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk]; cases idxs[k]? <;> simp

theorem projB_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projB n idxs (w &&& mask) = projB n idxs w := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases h : idxs[k]? with
  | none => rfl
  | some idx =>
    have hmem : idx ∈ idxs := List.mem_of_getElem? h
    simp [BitVec.getLsbD_and, hm idx hmem]

theorem nrm_bit0 (n : ℕ) (hn : 0 < n) (u : BitVec n) : (nrm n u).getLsbD 0 = false := by
  unfold nrm
  cases h : u.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]

theorem projS_ne_allOnes (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (w : BitVec m) :
    projS n idxs w ≠ BitVec.allOnes n := by
  intro h
  have := nrm_bit0 n hn (projB n idxs w)
  change (projS n idxs w).getLsbD 0 = false at this
  rw [h, BitVec.getLsbD_allOnes, decide_eq_true hn] at this
  exact Bool.noConfusion this

theorem nrm_zero (n : ℕ) : nrm n 0 = 0 := by unfold nrm; simp
theorem projS_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projS n idxs (0 : BitVec m) = 0 := by
  unfold projS; rw [projB_zero, nrm_zero]
theorem projS_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projS n idxs (w &&& mask) = projS n idxs w := by
  unfold projS; rw [projB_mask n idxs mask hm w]

theorem nrm_neg (n : ℕ) (hn : 0 < n) (u : BitVec n) : nrm n (~~~u) = nrm n u := by
  unfold nrm
  cases h : u.getLsbD 0
  · have h1 : (~~~u).getLsbD 0 = true := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_false]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · have h1 : (~~~u).getLsbD 0 = false := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true]

theorem projS_not (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (w : BitVec m) :
    projS n idxs (~~~w) = projS n idxs w := by
  unfold projS; rw [projB_not n idxs hlen hlt w, nrm_neg n hn]

theorem nrm_ops (n : ℕ) (hn : 0 < n) (x y z : BitVec n) (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false)
    (hz : z ∈ ops n x y ∨ z ∈ ops n (~~~x) y ∨ z ∈ ops n x (~~~y) ∨ z ∈ ops n (~~~x) (~~~y)) :
    nrm n z ∈ ops n x y := by
  have nrm_f (u : BitVec n) (hu : u.getLsbD 0 = false) : nrm n u = u := by
    unfold nrm; simp only [hu, Bool.false_eq_true, ite_false]
  have nrm_t (u : BitVec n) (hu : u.getLsbD 0 = true) : nrm n u = ~~~u := by
    unfold nrm; simp only [hu, ite_true]
  have b_eq (u v : BitVec n) (h : ∀ i < n, u.getLsbD i = v.getLsbD i) : u = v := BitVec.eq_of_getLsbD_eq h
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, hx, hy, Bool.and_false])
  · right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_or, hx, hy, Bool.or_false])
  · right; right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.and_false])]
    exact BitVec.and_comm ..
  · right; right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.or_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem projS_ops (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (a b z : BitVec m) (hz : z ∈ ops m a b) :
    projS n idxs z ∈ ops n (projS n idxs a) (projS n idxs b) := by
  have hrest : projB n idxs z ∈ ops n (projB n idxs a) (projB n idxs b) := by
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · left; exact projB_and n idxs a b
    · right; left; exact projB_or n idxs a b
    · right; right; left; rw [projB_and, projB_not n idxs hlen hlt]
    · right; right; right; rw [projB_and, projB_not n idxs hlen hlt]
  apply nrm_ops n hn (projS n idxs a) (projS n idxs b) (projB n idxs z) (nrm_bit0 n hn _) (nrm_bit0 n hn _)
  unfold projS nrm
  cases ha : (projB n idxs a).getLsbD 0 <;> cases hb : (projB n idxs b).getLsbD 0 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · exact Or.inl hrest
  · exact Or.inr (Or.inr (Or.inl hrest))
  · exact Or.inr (Or.inl hrest)
  · exact Or.inr (Or.inr (Or.inr hrest))

theorem ops_zero_left (n : ℕ) (y : BitVec n) : ∀ w ∈ ops n 0 y, w = 0 ∨ w = y := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.zero_and
  · right; exact BitVec.zero_or
  · left; exact BitVec.zero_and
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]

theorem ops_zero_right (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x 0, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.and_zero
  · right; exact BitVec.or_zero
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]
  · left; exact BitVec.zero_and

theorem ops_self (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x x, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · right; exact BitVec.and_self
  · right; exact BitVec.or_self
  · left; exact BitVec.and_not_self x
  · left; exact BitVec.and_not_self x

def zCount {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : ℕ :=
  (s.filter (fun w => f w = 0)).card
def nonZeroImg {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : Finset (BitVec n) :=
  (s.image f).erase 0

set_option maxRecDepth 100000 in
theorem live_restrict {m n : ℕ} (hn : 0 < n) (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) {opsM : BitVec m → BitVec m → Finset (BitVec m)}
    (hopsM : ∀ a b z, z ∈ opsM a b → z ∈ ops m a b)
    {g : BitVec m} {goalN : BitVec n} (hg : projS n idxs g = goalN) (hgnz : goalN ≠ 0)
    {k : ℕ} {s : Finset (BitVec m)} (h : live opsM g k s) :
    build (basicOps n) goalN (k - zCount (projS n idxs) s) (nonZeroImg (projS n idxs) s) := by
  let f : BitVec m → BitVec n := projS n idxs
  change build (basicOps n) goalN (k - zCount f s) (nonZeroImg f s)
  induction k generalizing s with
  | zero =>
    change s = {g} at h; subst h
    have hzc : zCount f {g} = 0 := by
      unfold zCount; rw [Finset.filter_singleton, if_neg (by change projS n idxs g ≠ 0; rw [hg]; exact hgnz)]; rfl
    rw [hzc]; change goalN ∈ nonZeroImg f {g}
    exact Finset.mem_erase.mpr ⟨hgnz, Finset.mem_image.mpr ⟨g, Finset.mem_singleton_self g, hg⟩⟩
  | succ k ih =>
    have hsc := live_card h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs_eq, tail⟩
    · exact build_mono_k (by omega) (ih skip)
    · have htail := ih tail
      have hz_ops : f z ∈ ops n (f a) (f b) := projS_ops n hn idxs hlen hlt a b z (hopsM a b z hz)
      have hsub_rest : nonZeroImg f rest ⊆ nonZeroImg f s := by
        intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu ⊢
        obtain ⟨hne, v, hv, rfl⟩ := hu; exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
      have hcard_rest : zCount f rest ≤ zCount f (insert z rest) := by
        unfold zCount; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert z rest))
      by_cases hza : f a = 0
      · have hzb_or := ops_zero_left n (f b) (f z) (hza ▸ hz_ops)
        have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
          obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
          · rcases hzb_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, b, hb, h1.symm⟩
          · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
        have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
          by_cases hzb : f b = 0
          · have hzz : f z = 0 := by rcases hzb_or with h0 | h1; exact h0; exact h1.trans hzb
            have hz_nr : z ∉ rest := fun hm => hout (by rw [hs_eq]; simp [hm])
            have h1 : zCount f (insert z rest) = zCount f rest + 1 := by
              unfold zCount; rw [Finset.filter_insert, if_pos hzz, Finset.card_insert_of_notMem (by simp [hz_nr])]
            have h2 : zCount f s ≤ zCount f rest + 2 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_pos hza]
              have hc1 := Finset.card_insert_le a (insert b (rest.filter (fun w => f w = 0)))
              have hc2 := Finset.card_insert_le b (rest.filter (fun w => f w = 0))
              omega
            omega
          · have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_pos hza]
              exact Finset.card_insert_le a (rest.filter (fun w => f w = 0))
            omega
        exact build_mono_k (by omega) (build_mono_av hsub htail)
      · by_cases hzb : f b = 0
        · have hza_or := ops_zero_right n (f a) (f z) (hzb ▸ hz_ops)
          have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
            intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
            obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
            · rcases hza_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
            · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
          have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
            have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_neg hza]
              exact Finset.card_insert_le b (rest.filter (fun w => f w = 0))
            omega
          exact build_mono_k (by omega) (build_mono_av hsub htail)
        · have hzc_eq : zCount f s = zCount f rest := by
            unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_neg hza]
          have hzc_le : zCount f s ≤ k := by
            have hsubf : insert a (insert b (s.filter (fun w => f w = 0))) ⊆ s := by
              intro u hu
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact ha
              · rcases Finset.mem_insert.mp hu with rfl | hu
                · exact hb
                · exact (Finset.mem_filter.mp hu).1
            have han : a ∉ insert b (s.filter (fun w => f w = 0)) := by
              simp only [Finset.mem_insert, Finset.mem_filter, not_or]; exact ⟨hab, fun h => hza h.2⟩
            have hbn : b ∉ s.filter (fun w => f w = 0) := by
              simp only [Finset.mem_filter]; exact fun h => hzb h.2
            have hle := Finset.card_le_card hsubf
            rw [Finset.card_insert_of_notMem han, Finset.card_insert_of_notMem hbn] at hle
            unfold zCount; omega
          by_cases hzz : f z = 0
          · have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
              intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
              obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
              · exact (hne hzz).elim
              · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
            exact build_mono_k (by omega) (build_mono_av hsub htail)
          · by_cases heqab : f a = f b
            · have hsame := ops_self n (f a) (f z) (heqab ▸ hz_ops)
              have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
                intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
                obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                · rcases hsame with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
                · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
              exact build_mono_k (by omega) (build_mono_av hsub htail)
            · have hstep : build (basicOps n) goalN ((k - zCount f (insert z rest)) + 1) (nonZeroImg f s) := by
                refine Or.inr ⟨f a, ?_, f b, ?_, heqab, f z, ?_, ?_⟩
                · exact Finset.mem_erase.mpr ⟨hza, Finset.mem_image_of_mem f ha⟩
                · exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_image_of_mem f hb⟩
                · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
                  exact ⟨hz_ops, hzz, projS_ne_allOnes n hn idxs z⟩
                · apply build_mono_av _ htail
                  intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu
                  obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                  · exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (hsub_rest (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f hv⟩))
              exact build_mono_k (by omega) hstep

def b4_0_goal : BitVec 16 := 0xe8a8
def b4_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_0_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_0_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0,b4_0_s1]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0,b4_0_p1]
def b4_0_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_G_valid : (List.range 2).all (symValid 16 2 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcc88,0xf0f0],[]),
([0xaaaa,0xcc0c,0xf0f0],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(1,0)]),
([0x5500,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcc00,0xcccc,0xf0f0],[]),
([0xcc,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 2 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 2 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_0_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 2 b4_0_pow 3 b4_0_L3 b4_0_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 2 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true := by
  intro i hi
  have hsz : b4_0_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 2 b4_0_pow 4 b4_0_L4 b4_0_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 2 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true := by
  intro i hi
  have hsz : b4_0_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
set_option maxRecDepth 100000 in
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 4 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L4_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xfeea
def b4_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_1_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_1_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_1_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_1_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_1_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_1_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_1_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_1_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_1_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_1_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1,b4_1_s2,b4_1_s3,b4_1_s4,b4_1_s5]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1,b4_1_p2,b4_1_p3,b4_1_p4,b4_1_p5]
def b4_1_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 6).all (symValid 16 6 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xcccc,0xfafa,0xffaa],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
  intro i hi
  have hsz : b4_1_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
set_option maxRecDepth 100000 in
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 4 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L4_sound 0 (by decide))

def b4_2_goal : BitVec 16 := 0xeae8
def b4_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_2_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_2_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_2_idx : Array (List ℕ) := Array.mk [b4_2_s0,b4_2_s1]
def b4_2_pow : Array (List ℕ) := Array.mk [b4_2_p0,b4_2_p1]
def b4_2_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_G_valid : (List.range 2).all (symValid 16 2 b4_2_idx b4_2_pow b4_2_inv b4_2_goal) = true := by decide +kernel
def b4_2_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfaf0],[]),
([0xaaaa,0xcccc,0xf3f0],[])
]
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaa00,0xaaaa,0xcccc,0xf0f0],[(0,0),(1,0)]),
([0xaa,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcccc,0xf0f0,0xffcc],[]),
([0xf00,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_2_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_2_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 2 b4_2_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_2 : ∀ i < b4_2_L2.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 2 b4_2_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_2_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_2_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_3_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 3 b4_2_L3 b4_2_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_3 : ∀ i < b4_2_L3.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 3 b4_2_L3 b4_2_L2 i = true := by
  intro i hi
  have hsz : b4_2_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_2_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_4_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 4 b4_2_L4 b4_2_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_4 : ∀ i < b4_2_L4.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 4 b4_2_L4 b4_2_L3 i = true := by
  intro i hi
  have hsz : b4_2_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_2_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_2_L2_sound : ∀ i < b4_2_L2.size, ¬ live (basicOps 16) b4_2_goal 2 (b4_2_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid (fun j hj => by simp at hj) b4_2_chk_2
theorem b4_2_L3_sound : ∀ i < b4_2_L3.size, ¬ live (basicOps 16) b4_2_goal 3 (b4_2_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid b4_2_L2_sound b4_2_chk_3
theorem b4_2_L4_sound : ∀ i < b4_2_L4.size, ¬ live (basicOps 16) b4_2_goal 4 (b4_2_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid b4_2_L3_sound b4_2_chk_4
set_option maxRecDepth 100000 in
theorem b4_2_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_2_goal ws) = [rows4] := by decide +kernel
theorem b4_2_top_match : sameSet (rows4.map (actB 16 (b4_2_pow[0]?.getD []))) (b4_2_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_2_no_build : ¬ build (basicOps 16) b4_2_goal 4 rows4.toFinset :=
  no_build_of_top b4_2_G_valid (by decide) b4_2_sublists b4_2_top_match (b4_2_L4_sound 0 (by decide))

def b4_3_goal : BitVec 16 := 0xeac8
def b4_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_3_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_3_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0,b4_3_s1]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0,b4_3_p1]
def b4_3_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_G_valid : (List.range 2).all (symValid 16 2 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 2 b4_3_pow 3 b4_3_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 2 b4_3_pow 3 b4_3_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_3_L3.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) (by omega)
theorem b4_3_L3_sound : ∀ i < b4_3_L3.size, ¬ live (basicOps 16) b4_3_goal 3 (b4_3_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid (fun j hj => by simp at hj) b4_3_chk_3
set_option maxRecDepth 100000 in
theorem b4_3_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_3_goal ws) = [rows4] := by decide +kernel
theorem b4_3_top_match : sameSet (rows4.map (actB 16 (b4_3_pow[0]?.getD []))) (b4_3_L3[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_3_no_build : ¬ build (basicOps 16) b4_3_goal 3 rows4.toFinset :=
  no_build_of_top b4_3_G_valid (by decide) b4_3_sublists b4_3_top_match (b4_3_L3_sound 0 (by decide))

def b4_4_goal : BitVec 16 := 0xeee8
def b4_4_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_4_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_4_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_4_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_4_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_4_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_4_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_4_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_4_idx : Array (List ℕ) := Array.mk [b4_4_s0,b4_4_s1,b4_4_s2,b4_4_s3]
def b4_4_pow : Array (List ℕ) := Array.mk [b4_4_p0,b4_4_p1,b4_4_p2,b4_4_p3]
def b4_4_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_G_valid : (List.range 4).all (symValid 16 4 b4_4_idx b4_4_pow b4_4_inv b4_4_goal) = true := by decide +kernel
def b4_4_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[])
]
def b4_4_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_4_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_2_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 2 b4_4_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_2 : ∀ i < b4_4_L2.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 2 b4_4_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_4_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_3_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 3 b4_4_L3 b4_4_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_3 : ∀ i < b4_4_L3.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 3 b4_4_L3 b4_4_L2 i = true := by
  intro i hi
  have hsz : b4_4_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_4_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_4_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 4 b4_4_L4 b4_4_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_4 : ∀ i < b4_4_L4.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 4 b4_4_L4 b4_4_L3 i = true := by
  intro i hi
  have hsz : b4_4_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_4_L2_sound : ∀ i < b4_4_L2.size, ¬ live (basicOps 16) b4_4_goal 2 (b4_4_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid (fun j hj => by simp at hj) b4_4_chk_2
theorem b4_4_L3_sound : ∀ i < b4_4_L3.size, ¬ live (basicOps 16) b4_4_goal 3 (b4_4_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid b4_4_L2_sound b4_4_chk_3
theorem b4_4_L4_sound : ∀ i < b4_4_L4.size, ¬ live (basicOps 16) b4_4_goal 4 (b4_4_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid b4_4_L3_sound b4_4_chk_4
set_option maxRecDepth 100000 in
theorem b4_4_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_4_goal ws) = [rows4] := by decide +kernel
theorem b4_4_top_match : sameSet (rows4.map (actB 16 (b4_4_pow[0]?.getD []))) (b4_4_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_4_no_build : ¬ build (basicOps 16) b4_4_goal 4 rows4.toFinset :=
  no_build_of_top b4_4_G_valid (by decide) b4_4_sublists b4_4_top_match (b4_4_L4_sound 0 (by decide))

def nrmM32 (m : BitVec 32) (b0 : ℕ) (u : BitVec 32) : BitVec 32 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM32 (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 32) :
    projS 16 idxs (nrmM32 m b0 u) = projS 16 idxs u := by
  unfold nrmM32
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 16 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 16 idxs m hm (~~~u), projS_not 16 (by decide) idxs hlen hlt u]

abbrev W5Node := List (BitVec 32) × List (BitVec 32 × BitVec 32 × BitVec 32) × List ℕ × List (ℕ × ℕ)

def checkReplay32 (m : BitVec 32) (b0 : ℕ) (bank : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → Bool
  | [], targets => targets.all (fun t => nrmM32 m b0 t == 0 || bank.contains (nrmM32 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 32 a b).contains v &&
    checkReplay32 m b0 (v :: bank) rest targets

theorem checkReplay32_sound (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 16)
    (steps : List (BitVec 32 × BitVec 32 × BitVec 32)) (targets : List (BitVec 32)) :
    ∀ (bank : List (BitVec 32)) (k : ℕ),
      checkReplay32 m b0 bank steps targets = true →
      build (basicOps 16) g k (nonZeroImg (projS 16 idxs) targets.toFinset) →
      build (basicOps 16) g (k + steps.length) (nonZeroImg (projS 16 idxs) bank.toFinset) := by
  let f : BitVec 32 → BitVec 16 := projS 16 idxs
  have hn : 0 < 16 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay32, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM32 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM32 m b0 t, hmem, projS_nrmM32 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay32, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 16 (f a) (f b) := projS_ops 16 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 16 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 16 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 16 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 16 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed32 (stock needed : List (BitVec 32)) (u : BitVec 32) : List (BitVec 32) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded32 (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM32 m b0 w
    let needed' := if needed.contains pw then addNeed32 stock (addNeed32 stock needed (nrmM32 m b0 a)) (nrmM32 m b0 b) else needed
    buildNeeded32 m b0 stock rest needed'

def buildSteps32 (m : BitVec 32) (b0 : ℕ) (needed : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32 × BitVec 32 × BitVec 32)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM32 m b0 w
    let pa := nrmM32 m b0 a
    let pb := nrmM32 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 32 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps32 m b0 needed rest (pw :: bank)
    else
      buildSteps32 m b0 needed rest bank

def checkCofClose32 (lb fuel : ℕ) (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM32 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeed32 stock acc (nrmM32 m b0 u)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeeded32 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildSteps32 m b0 needed hist stock
        Nat.blt (steps.length + rem) lb && checkReplay32 m b0 stock steps nxt
      else false
    else false
  else false

theorem checkCofClose32_sound_aux (goal5 : BitVec 32) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 32)) (g : BitVec 16) (hgnz : g ≠ 0)
    (hg : projS 16 idxs goal5 = g)
    (hstock : stock.all (fun w => rows4.contains (projS 16 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 16) g (lb - 1) rows4.toFinset)
    (fuel : ℕ) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32))
    (hnd : nxt.Nodup) (hchk : checkCofClose32 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 32) goal5 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose32 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops32 : ∀ a b z : BitVec 32, z ∈ basicOps 32 a b → z ∈ ops 32 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 16) idxs hlen hlt hops32 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM32 m b0 u == 0)).length ≤ zCount (projS 16 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM32 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM32 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay32_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 16 idxs) stock.toFinset ⊆ rows4.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW5 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose32 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW5 (goal5 : BitVec 32) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (a b : BitVec 32) (r : List (BitVec 32)) : Bool :=
  (ops 32 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 32 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 32 jumps5 goal5 (w :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 32 jumps5 goal5 (w :: a :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 32 jumps5 goal5 (w :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 32 jumps5 goal5 (w :: a :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW5 (goal5 : BitVec 32) (gsize : ℕ) (g5_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal5) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW5 goal5 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW5 (goal5 : BitVec 32) (gsize : ℕ) (g5_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW5_at {goal5 : BitVec 32} {gsize ncf k start m : ℕ} {g5_pow : Array (List ℕ)}
    {cfLBs cfB0s : Array ℕ} {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (h : checkBlockW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W5 {goal5 : BitVec 32} {gsize ncf k i : ℕ}
    {g5_idx g5_pow : Array (List ℕ)} {g5_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 32 gsize g5_idx g5_pow g5_inv goal5) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW5 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 32) goal5 (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (g5_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 32 (g5_pow[g5_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[g]?.getD []))).toFinset.image
        (actB 32 (g5_pow[g5_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 32 (g5_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal5 ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 32} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 32 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 32) goal5 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 32 jumps5 goal5 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW5 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 32 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW5 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact hcof c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 32 a b ▸ hz)

theorem level_sound_W5 {goal5 : BitVec 32} {gsize ncf k : ℕ}
    {g5_idx g5_pow : Array (List ℕ)} {g5_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 32 gsize g5_idx g5_pow g5_inv goal5) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W5 hk hi hvalid hcof hprev (hblk i hi)

def u0 : BitVec 32 := 0xcccccccc
def u1 : BitVec 32 := 0xaaaaaaaa
def u2 : BitVec 32 := 0xf0f0f0f0
def u3 : BitVec 32 := 0xffff0000
def u4 : BitVec 32 := 0xff00ff00
def u5 : BitVec 32 := 0xeeeeeeee
def u6 : BitVec 32 := 0xfafafafa
def u7 : BitVec 32 := 0x88888888
def u8 : BitVec 32 := 0x22222222
def u9 : BitVec 32 := 0xcc00cc
def u10 : BitVec 32 := 0xfff0fff0
def u11 : BitVec 32 := 0xfcfcfcfc
def u12 : BitVec 32 := 0xffffcccc
def u13 : BitVec 32 := 0xaa00aa
def u14 : BitVec 32 := 0xffccffcc
def u15 : BitVec 32 := 0xffaaffaa
def u16 : BitVec 32 := 0x33330000
def u17 : BitVec 32 := 0xff0000
def u18 : BitVec 32 := 0x44444444
def u19 : BitVec 32 := 0xff88ff88
def u20 : BitVec 32 := 0xee00ee
def u21 : BitVec 32 := 0x30303030
def u22 : BitVec 32 := 0xfff00000

def c5_0_goal : BitVec 32 := 0xfeeaece8
def c5_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s1 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]
def c5_0_p1 : List ℕ := [1,4,2,8,16,64,32,128,65536,262144,131072,524288,1048576,4194304,2097152,8388608,256,1024,512,2048,4096,16384,8192,32768,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648]
def c5_0_idx : Array (List ℕ) := Array.mk [c5_0_s0,c5_0_s1]
def c5_0_pow : Array (List ℕ) := Array.mk [c5_0_p0,c5_0_p1]
def c5_0_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_G_valid : (List.range 2).all (symValid 32 2 c5_0_idx c5_0_pow c5_0_inv c5_0_goal) = true := by decide +kernel
def c5_0_m0 : BitVec 32 := 0x55555555
def c5_0_st0 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_0_ix0 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_0 : c5_0_ix0.length = 16 ∧ (∀ idx ∈ c5_0_ix0, idx < 32) ∧ (∀ idx ∈ c5_0_ix0, c5_0_m0.getLsbD idx = true) ∧ projS 16 c5_0_ix0 c5_0_goal = b4_0_goal ∧ c5_0_st0.all (fun w => rows4.contains (projS 16 c5_0_ix0 w)) = true := by decide +kernel
def c5_0_m1 : BitVec 32 := 0xff00ff00
def c5_0_st1 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_0_ix1 : List ℕ := [8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_1 : c5_0_ix1.length = 16 ∧ (∀ idx ∈ c5_0_ix1, idx < 32) ∧ (∀ idx ∈ c5_0_ix1, c5_0_m1.getLsbD idx = true) ∧ projS 16 c5_0_ix1 c5_0_goal = b4_1_goal ∧ c5_0_st1.all (fun w => rows4.contains (projS 16 c5_0_ix1 w)) = true := by decide +kernel
def c5_0_m2 : BitVec 32 := 0xffff0000
def c5_0_st2 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_0_ix2 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_2 : c5_0_ix2.length = 16 ∧ (∀ idx ∈ c5_0_ix2, idx < 32) ∧ (∀ idx ∈ c5_0_ix2, c5_0_m2.getLsbD idx = true) ∧ projS 16 c5_0_ix2 c5_0_goal = b4_1_goal ∧ c5_0_st2.all (fun w => rows4.contains (projS 16 c5_0_ix2 w)) = true := by decide +kernel
def c5_0_m3 : BitVec 32 := 0x33333333
def c5_0_st3 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def c5_0_ix3 : List ℕ := [0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_3 : c5_0_ix3.length = 16 ∧ (∀ idx ∈ c5_0_ix3, idx < 32) ∧ (∀ idx ∈ c5_0_ix3, c5_0_m3.getLsbD idx = true) ∧ projS 16 c5_0_ix3 c5_0_goal = b4_0_goal ∧ c5_0_st3.all (fun w => rows4.contains (projS 16 c5_0_ix3 w)) = true := by decide +kernel
def c5_0_m4 : BitVec 32 := 0xffff
def c5_0_st4 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_0_ix4 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_4 : c5_0_ix4.length = 16 ∧ (∀ idx ∈ c5_0_ix4, idx < 32) ∧ (∀ idx ∈ c5_0_ix4, c5_0_m4.getLsbD idx = true) ∧ projS 16 c5_0_ix4 c5_0_goal = b4_2_goal ∧ c5_0_st4.all (fun w => rows4.contains (projS 16 c5_0_ix4 w)) = true := by decide +kernel
def c5_0_m5 : BitVec 32 := 0xff00ff
def c5_0_st5 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_0_ix5 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_5 : c5_0_ix5.length = 16 ∧ (∀ idx ∈ c5_0_ix5, idx < 32) ∧ (∀ idx ∈ c5_0_ix5, c5_0_m5.getLsbD idx = true) ∧ projS 16 c5_0_ix5 c5_0_goal = b4_2_goal ∧ c5_0_st5.all (fun w => rows4.contains (projS 16 c5_0_ix5 w)) = true := by decide +kernel
def c5_0_m6 : BitVec 32 := 0xf0f0f0f
def c5_0_st6 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_0_ix6 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_6 : c5_0_ix6.length = 16 ∧ (∀ idx ∈ c5_0_ix6, idx < 32) ∧ (∀ idx ∈ c5_0_ix6, c5_0_m6.getLsbD idx = true) ∧ projS 16 c5_0_ix6 c5_0_goal = b4_3_goal ∧ c5_0_st6.all (fun w => rows4.contains (projS 16 c5_0_ix6 w)) = true := by decide +kernel
def c5_0_cfMasks : Array (BitVec 32) := Array.mk [c5_0_m0,c5_0_m1,c5_0_m2,c5_0_m3,c5_0_m4,c5_0_m5,c5_0_m6]
def c5_0_cfB0s : Array ℕ := Array.mk [0,8,16,0,0,0,0]
def c5_0_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_0_st0,c5_0_st1,c5_0_st2,c5_0_st3,c5_0_st4,c5_0_st5,c5_0_st6]
def c5_0_cfLBs : Array ℕ := Array.mk [5,5,5,5,5,5,4]
theorem c5_0_cof_sound (c fuel : ℕ) (hc : c < 7) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_0_cfLBs[c]?.getD 0) fuel (c5_0_cfMasks[c]?.getD 0) (c5_0_cfB0s[c]?.getD 0) (c5_0_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_0_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix0 c5_0_cspec_0.1 c5_0_cspec_0.2.1 c5_0_m0 c5_0_cspec_0.2.2.1 0 c5_0_st0 b4_0_goal (by decide) c5_0_cspec_0.2.2.2.1 c5_0_cspec_0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix1 c5_0_cspec_1.1 c5_0_cspec_1.2.1 c5_0_m1 c5_0_cspec_1.2.2.1 8 c5_0_st1 b4_1_goal (by decide) c5_0_cspec_1.2.2.2.1 c5_0_cspec_1.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix2 c5_0_cspec_2.1 c5_0_cspec_2.2.1 c5_0_m2 c5_0_cspec_2.2.2.1 16 c5_0_st2 b4_1_goal (by decide) c5_0_cspec_2.2.2.2.1 c5_0_cspec_2.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix3 c5_0_cspec_3.1 c5_0_cspec_3.2.1 c5_0_m3 c5_0_cspec_3.2.2.1 0 c5_0_st3 b4_0_goal (by decide) c5_0_cspec_3.2.2.2.1 c5_0_cspec_3.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix4 c5_0_cspec_4.1 c5_0_cspec_4.2.1 c5_0_m4 c5_0_cspec_4.2.2.1 0 c5_0_st4 b4_2_goal (by decide) c5_0_cspec_4.2.2.2.1 c5_0_cspec_4.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix5 c5_0_cspec_5.1 c5_0_cspec_5.2.1 c5_0_m5 c5_0_cspec_5.2.2.1 0 c5_0_st5 b4_2_goal (by decide) c5_0_cspec_5.2.2.2.1 c5_0_cspec_5.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose32_sound_aux c5_0_goal 4 c5_0_ix6 c5_0_cspec_6.1 c5_0_cspec_6.2.1 c5_0_m6 c5_0_cspec_6.2.2.1 0 c5_0_st6 b4_3_goal (by decide) c5_0_cspec_6.2.2.2.1 c5_0_cspec_6.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | c + 7 => omega
def c5_0_L3 : Array W5Node := Array.mk [
([u5,u2,0xffaacc88],[],[],[])
]
def c5_0_L4 : Array W5Node := Array.mk [
([u5,u6,u11,u4,u3],[(u5,u0,u1),(u11,u0,u2),(u6,u1,u2)],[0],[]),
([u5,u2,u6,u4,u12],[],[],[]),
([u5,u2,u15,u12],[(u5,u0,u1),(u12,u0,u3),(u15,u1,u4)],[1,2],[(0,0)]),
([u1,u0,u2,0xfafac8c8,u4],[(u6,u1,u2),(u12,u0,u3),(0xfafac8c8,u6,u12)],[0],[]),
([0xa8fca8fc,u1,u0,u2,u3],[],[],[]),
([u1,u0,u2,0xffaacc88],[(u12,u0,u3),(u15,u1,u4),(0xffaacc88,u15,u12)],[0,3],[(0,0)])
]
def c5_0_L5 : Array W5Node := Array.mk [
([u1,u5,u2,u11,u4,u3],[(u5,u0,u1),(u11,u0,u2)],[0],[(0,0),(1,1)]),
([u1,u5,u2,u4,u12],[(u5,u0,u1),(u12,u0,u3)],[0,1,2,3,4],[(0,1),(0,2)]),
([u1,u0,u2,0xfefefefe,u4,u3],[(u5,u1,u0),(0xfefefefe,u5,u2)],[1,2,4,5],[]),
([0xe0e0e0e,u1,u0,u2,u4,u3],[],[],[]),
([u1,u0,u6,u11,u4,u3],[(u6,u1,u2),(u11,u0,u2)],[0],[(0,0)]),
([u21,u1,u0,u6,u4,u3],[(u6,u1,u2),(u21,u0,u2)],[0],[]),
([0x32323232,u1,u0,u2,u4,u3],[(u6,u1,u2),(0x32323232,u0,u6)],[2,4],[]),
([u1,u0,u2,u6,u4,u12],[(u6,u1,u2),(u12,u0,u3)],[0,2],[(0,1),(0,3)]),
([u16,u1,u0,u2,u6,u4],[(u6,u1,u2),(u16,u0,u3)],[0,4],[(1,4)]),
([u1,u0,u2,0xfafa0000,u6,u4],[(u6,u1,u2),(0xfafa0000,u6,u3)],[0,2],[]),
([0xfafa,u1,u0,u2,u6,u4],[(u6,u1,u2),(0xfafa,u6,u3)],[0,4],[]),
([u1,0xbabababa,u0,u2,u4,u3],[(u21,u0,u2),(0xbabababa,u21,u1)],[2,4],[]),
([u21,u1,u0,u2,u15,u3],[],[],[]),
([u21,0x55005500,u1,u0,u2,u3],[],[],[]),
([u1,u0,u2,u15,u12],[(u12,u0,u3),(u15,u1,u4)],[0,1,2,3,4,5],[(0,2),(0,5)]),
([u16,u1,u0,u2,u15],[(u15,u1,u4),(u16,u0,u3)],[0,1,3,4,5],[]),
([u16,0x55005500,u1,u0,u2],[(u16,u0,u3),(0x55005500,u1,u4)],[0,3,4,5],[])
]
def c5_0_L6 : Array W5Node := Array.mk [
([u1,u0,u5,u2,u4,u3],[(u5,u1,u0)],[0,1,2,3,4,5,6],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)]),
([u1,u0,u2,u6,u4,u3],[(u6,u1,u2)],[0,1,2,3,4,5,6],[(0,2),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,0)]),
([u21,u1,u0,u2,u4,u3],[(u21,u0,u2)],[0,1,2,3,4,5,6],[(0,5),(0,11),(0,12),(0,13)]),
([u1,u0,u2,u4,u12],[(u12,u0,u3)],[0,1,2,3,4,5],[(0,1),(0,7),(0,14),(1,12),(1,15)]),
([u16,u1,u0,u2,u4],[(u16,u0,u3)],[0,1,3,4,5],[(0,8),(0,15),(0,16),(1,13)])
]
def c5_0_L7 : Array W5Node := Array.mk [
([u1,u0,u2,u4,u3],[],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_3 : ∀ i < c5_0_L3.size, checkNodeW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_0_L3.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_4 : ∀ i < c5_0_L4.size, checkNodeW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 i = true := by
  intro i hi
  have hsz : c5_0_L4.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_1 : checkBlockW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 16 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_5 : ∀ i < c5_0_L5.size, checkNodeW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 i = true := by
  intro i hi
  have hsz : c5_0_L5.size = 17 := by decide +kernel
  have hi' : i < 17 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_0_chk_5_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_0_chk_5_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_6 : ∀ i < c5_0_L6.size, checkNodeW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 i = true := by
  intro i hi
  have hsz : c5_0_L6.size = 5 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_7 : ∀ i < c5_0_L7.size, checkNodeW5 c5_0_goal 2 c5_0_pow 7 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 i = true := by
  intro i hi
  have hsz : c5_0_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_0_L3_sound : ∀ i < c5_0_L3.size, ¬ live (basicOps 32) c5_0_goal 3 (c5_0_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound (fun j hj => by simp at hj) c5_0_chk_3
theorem c5_0_L4_sound : ∀ i < c5_0_L4.size, ¬ live (basicOps 32) c5_0_goal 4 (c5_0_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L3_sound c5_0_chk_4
theorem c5_0_L5_sound : ∀ i < c5_0_L5.size, ¬ live (basicOps 32) c5_0_goal 5 (c5_0_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L4_sound c5_0_chk_5
theorem c5_0_L6_sound : ∀ i < c5_0_L6.size, ¬ live (basicOps 32) c5_0_goal 6 (c5_0_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L5_sound c5_0_chk_6
theorem c5_0_L7_sound : ∀ i < c5_0_L7.size, ¬ live (basicOps 32) c5_0_goal 7 (c5_0_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L6_sound c5_0_chk_7
set_option maxRecDepth 100000 in
theorem c5_0_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_0_goal ws) = [rows5] := by decide +kernel
theorem c5_0_top_match : sameSet (rows5.map (actB 32 (c5_0_pow[0]?.getD []))) (c5_0_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 7 rows5.toFinset :=
  no_build_of_top c5_0_G_valid (by decide) c5_0_sublists c5_0_top_match (c5_0_L7_sound 0 (by decide))

def c5_1_goal : BitVec 32 := 0xeee8eac8
def c5_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_1_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]
def c5_1_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768,65536,262144,131072,524288,16777216,67108864,33554432,134217728,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_1_idx : Array (List ℕ) := Array.mk [c5_1_s0,c5_1_s1]
def c5_1_pow : Array (List ℕ) := Array.mk [c5_1_p0,c5_1_p1]
def c5_1_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_G_valid : (List.range 2).all (symValid 32 2 c5_1_idx c5_1_pow c5_1_inv c5_1_goal) = true := by decide +kernel
def c5_1_m0 : BitVec 32 := 0xf0f0f0f
def c5_1_st0 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_1_ix0 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_0 : c5_1_ix0.length = 16 ∧ (∀ idx ∈ c5_1_ix0, idx < 32) ∧ (∀ idx ∈ c5_1_ix0, c5_1_m0.getLsbD idx = true) ∧ projS 16 c5_1_ix0 c5_1_goal = b4_0_goal ∧ c5_1_st0.all (fun w => rows4.contains (projS 16 c5_1_ix0 w)) = true := by decide +kernel
def c5_1_m1 : BitVec 32 := 0xff00ff
def c5_1_st1 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_1_ix1 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_1 : c5_1_ix1.length = 16 ∧ (∀ idx ∈ c5_1_ix1, idx < 32) ∧ (∀ idx ∈ c5_1_ix1, c5_1_m1.getLsbD idx = true) ∧ projS 16 c5_1_ix1 c5_1_goal = b4_0_goal ∧ c5_1_st1.all (fun w => rows4.contains (projS 16 c5_1_ix1 w)) = true := by decide +kernel
def c5_1_m2 : BitVec 32 := 0xffff0000
def c5_1_st2 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_1_ix2 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_2 : c5_1_ix2.length = 16 ∧ (∀ idx ∈ c5_1_ix2, idx < 32) ∧ (∀ idx ∈ c5_1_ix2, c5_1_m2.getLsbD idx = true) ∧ projS 16 c5_1_ix2 c5_1_goal = b4_4_goal ∧ c5_1_st2.all (fun w => rows4.contains (projS 16 c5_1_ix2 w)) = true := by decide +kernel
def c5_1_m3 : BitVec 32 := 0xffff
def c5_1_st3 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_1_ix3 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_3 : c5_1_ix3.length = 16 ∧ (∀ idx ∈ c5_1_ix3, idx < 32) ∧ (∀ idx ∈ c5_1_ix3, c5_1_m3.getLsbD idx = true) ∧ projS 16 c5_1_ix3 c5_1_goal = b4_3_goal ∧ c5_1_st3.all (fun w => rows4.contains (projS 16 c5_1_ix3 w)) = true := by decide +kernel
def c5_1_cfMasks : Array (BitVec 32) := Array.mk [c5_1_m0,c5_1_m1,c5_1_m2,c5_1_m3]
def c5_1_cfB0s : Array ℕ := Array.mk [0,0,16,0]
def c5_1_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_1_st0,c5_1_st1,c5_1_st2,c5_1_st3]
def c5_1_cfLBs : Array ℕ := Array.mk [5,5,5,4]
theorem c5_1_cof_sound (c fuel : ℕ) (hc : c < 4) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_1_cfLBs[c]?.getD 0) fuel (c5_1_cfMasks[c]?.getD 0) (c5_1_cfB0s[c]?.getD 0) (c5_1_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_1_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix0 c5_1_cspec_0.1 c5_1_cspec_0.2.1 c5_1_m0 c5_1_cspec_0.2.2.1 0 c5_1_st0 b4_0_goal (by decide) c5_1_cspec_0.2.2.2.1 c5_1_cspec_0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix1 c5_1_cspec_1.1 c5_1_cspec_1.2.1 c5_1_m1 c5_1_cspec_1.2.2.1 0 c5_1_st1 b4_0_goal (by decide) c5_1_cspec_1.2.2.2.1 c5_1_cspec_1.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix2 c5_1_cspec_2.1 c5_1_cspec_2.2.1 c5_1_m2 c5_1_cspec_2.2.2.1 16 c5_1_st2 b4_4_goal (by decide) c5_1_cspec_2.2.2.2.1 c5_1_cspec_2.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_1_goal 4 c5_1_ix3 c5_1_cspec_3.1 c5_1_cspec_3.2.1 c5_1_m3 c5_1_cspec_3.2.2.1 0 c5_1_st3 b4_3_goal (by decide) c5_1_cspec_3.2.2.2.1 c5_1_cspec_3.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | c + 4 => omega
def c5_1_L3 : Array W5Node := Array.mk [
([0xaa88aa88,u0,u2,0xffaa0000],[],[],[])
]
def c5_1_L4 : Array W5Node := Array.mk [
([u8,u18,u2,u4,u3],[],[],[]),
([u8,u0,0xf8f8f8f8,u4,u3],[],[],[]),
([u1,u5,u2,u19,u3],[],[],[]),
([u1,u0,0xf8f8f8f8,u19,u3],[],[],[]),
([0x70707070,u1,u0,u19,u3],[],[],[]),
([u1,u0,u2,u19,0xffff8888],[],[],[]),
([0x77770000,u1,u0,u2,u19],[],[],[]),
([u1,u0,u2,0xff08ff08,u3],[],[],[]),
([u1,u0,u2,u19,u3],[],[],[]),
([0x70707070,0x77007700,u1,u0,u3],[],[],[]),
([0x70707070,u1,u0,u4,0xffff8888],[],[],[]),
([0x70707070,0x77770000,u1,u0,u4],[],[],[]),
([0x66666666,u1,u2,u4,u3],[],[],[]),
([u20,u1,u0,u2,u3],[],[],[]),
([u1,u0,0xe0e0e0e0,0xee00ee00,u3],[],[],[]),
([u20,u1,u0,0xe0e0e0e0,u3],[],[],[]),
([u1,u0,0xe0e0e0e0,0xeeee0000,u4],[],[],[]),
([0xeeee,u1,u0,0xe0e0e0e0,u4],[],[],[]),
([0xfe00fe,u1,u0,u2,u3],[],[],[]),
([u20,0xe0e0e0e,u1,u0,u3],[],[],[]),
([u20,u1,u0,0xeeee0000,u2],[],[],[]),
([0xeeee,u20,u1,u0,u2],[],[],[]),
([u8,0x66666666,u2,u4,u3],[],[],[]),
([u8,0xc4c4c4c4,u2,u4,u3],[],[],[]),
([u1,u0,u2,0xff330000,u14],[],[],[]),
([0xaa88aa88,u0,u2,u15,u3],[],[],[(0,0)]),
([0xa8a8a8a8,u0,u6,u4,u3],[],[],[]),
([u1,u0,u2,0xffaa0000,u14],[],[],[(0,0)]),
([u1,u0,u2,0xffc8ffc8,u3],[],[],[]),
([0xaaa0aaa0,u0,u6,u4,u3],[],[],[]),
([u1,u0,u2,u14,u22],[],[],[]),
([0xa0a0aaaa,u0,u6,u4,u3],[],[],[]),
([0xaaa8aaa8,u0,u2,u4,u3],[],[],[]),
([0x33323332,u1,u2,u4,u3],[],[],[]),
([u13,0xaaeeaaee,u0,u2,u3],[],[],[]),
([u13,u1,u0,u2,0xff330000],[],[],[]),
([u9,u1,0xcceeccee,u2,u3],[],[],[]),
([u13,u1,u0,u2,0xffaa0000],[],[],[]),
([0xae00ae,u1,u0,u2,u3],[],[],[]),
([u13,0x55505550,u0,u2,u3],[],[],[]),
([u13,u1,u0,u2,u22],[],[],[]),
([u13,0xaaffaaaa,u0,u2,u3],[],[],[]),
([0xee00aa,u1,u0,u2,u3],[],[],[]),
([u1,u0,u2,0xff88ffcc,u3],[],[],[]),
([u1,u0,u2,0xffc0ffcc,u3],[],[],[]),
([0xaf00aa,u1,u0,u2,u3],[],[],[])
]
def c5_1_L5 : Array W5Node := Array.mk [
([u8,u7,u0,u2,u4,u3],[(u7,u1,u0),(u8,u7,u1)],[0],[(0,0),(0,1)]),
([u8,u1,u0,u2,u4,u3],[],[],[(0,0)]),
([u1,u0,u2,u19,u3],[],[],[(0,2),(1,1)]),
([u7,u1,u0,u2,u19,u3],[(u7,u0,u1),(u19,u7,u4)],[1],[(0,3),(0,4),(0,5),(0,6),(1,1)]),
([u1,u0,u2,0xf8f8f8f8,u4,u3],[],[],[]),
([0x880088,u1,u0,u2,u4,u3],[(u7,u0,u1),(0x880088,u7,u4)],[0,2,3],[(0,8),(1,7)]),
([0x70707070,u7,u1,u0,u4,u3],[],[],[(0,4),(0,9),(0,10),(0,11),(1,8)]),
([u7,u1,u0,u2,u4,0xffff8888],[(u7,u1,u0),(0xffff8888,u7,u3)],[3],[(0,5),(0,10),(1,5),(1,10)]),
([0x77770000,u1,u0,u2,u4],[],[],[]),
([0x77770000,u7,u1,u0,u2,u4],[(u7,u1,u0),(0x77770000,u7,u3)],[2],[(0,6),(0,11),(1,6),(1,11)]),
([u7,u1,u5,u2,u4,u3],[],[],[(0,2),(0,12)]),
([u8,u1,u5,u2,u4,u3],[(u5,u1,u0),(u8,u1,u0)],[0],[(0,0)]),
([u1,u5,u2,u4,u14,u3],[(u5,u0,u1),(u14,u0,u4)],[1],[]),
([u9,u1,u5,u2,u4,u3],[(u5,u0,u1),(u9,u0,u4)],[1],[]),
([u1,u0,0xe0e0e0e0,u5,u4,u3],[],[],[(0,14),(0,15),(0,16),(0,17),(1,13)]),
([u1,u0,u2,0xfefefefe,u4,u3],[(u5,u1,u0),(0xfefefefe,u5,u2)],[1,2,3],[(0,18),(1,13)]),
([u20,u1,u0,u2,u3],[],[],[]),
([u20,u1,u0,u5,u2,u3],[(u5,u0,u1),(u20,u5,u4)],[1],[(0,15),(0,19),(0,20),(0,21)]),
([u20,u1,u0,u2,u4,u3],[],[],[]),
([u1,u0,0xeeee0000,u2,u4],[],[],[]),
([u1,u0,0xeeee0000,u5,u2,u4],[(u5,u1,u0),(0xeeee0000,u5,u3)],[2],[(0,16),(0,20),(1,16),(1,20)]),
([0xeeee,u1,u0,u5,u2,u4],[(u5,u1,u0),(0xeeee,u5,u3)],[3],[(0,17),(0,21),(1,17),(1,21)]),
([u7,u1,u0,u2,u4,u3],[(u8,u1,u0),(u7,u8,u1)],[0,1,2,3],[(0,8),(1,8)]),
([u1,u0,u5,u2,u4,u3],[(u8,u1,u0),(u5,u8,u0)],[0,1,2,3],[(0,13),(1,13)]),
([u1,u0,u2,0xf2f2f2f2,u4,u3],[],[],[]),
([0x440044,u1,u0,u2,u4,u3],[(u18,u0,u1),(0x440044,u18,u4)],[2,3],[]),
([u1,u0,u2,0xf4f4f4f4,u4,u3],[(u18,u0,u1),(0xf4f4f4f4,u18,u2)],[2,3],[]),
([0x220022,u1,u0,u2,u4,u3],[],[],[]),
([u8,u18,u2,u4,u3],[],[],[(0,22),(1,22)]),
([u8,u18,u1,u2,u4,u3],[],[],[(0,12)]),
([u8,u0,u2,u6,u4,u3],[(u8,u1,u0),(u6,u1,u2)],[0],[]),
([u9,u18,u1,u2,u4,u3],[(u18,u0,u1),(u9,u0,u4)],[1],[(1,23)]),
([u9,u1,u0,u2,u14,u3],[(u14,u0,u4),(u9,u0,u4)],[0,1],[(0,24)]),
([u1,u0,u2,u15,u14,u3],[],[],[(0,8),(0,25),(0,27),(1,26)]),
([0xaa88aa88,u1,u0,u2,u4,u3],[(u14,u0,u4),(0xaa88aa88,u1,u14)],[0,1,2,3],[(0,8),(0,25),(1,28)]),
([0x32323232,u1,u0,u2,u4,u3],[],[],[]),
([u1,u0,u2,u14,u10,u3],[(u14,u0,u4),(u10,u4,u2)],[0],[(0,30),(1,29)]),
([u17,u1,u0,u2,u14,u3],[(u14,u0,u4),(u17,u4,u3)],[2],[(1,31)]),
([u1,u0,u2,u4,0xfffafffa,u3],[(u6,u1,u2),(0xfffafffa,u6,u4)],[2,3],[(0,33),(1,32)]),
([0xfa00fa,u1,u0,u2,u4,u3],[],[],[]),
([u1,0xaaeeaaee,u0,u2,u4,u3],[],[],[(0,13),(0,34)]),
([0xaa22aa22,u1,u0,u2,u4,u3],[(u9,u0,u4),(0xaa22aa22,u9,u1)],[1],[(1,23)]),
([u1,u0,u2,0xf0fcf0fc,u4,u3],[],[],[]),
([0xa000a,u1,u0,u2,u4,u3],[(0xa0a0a0a,u1,u2),(0xa000a,0xa0a0a0a,u4)],[2,3],[]),
([u9,u1,u0,u2,u4,0xffff00cc],[(u9,u0,u4),(0xffff00cc,u9,u3)],[1,3],[]),
([u1,u0,u2,0xf5f50000,u4],[(0xa0a0a0a,u1,u2),(0xf5f50000,0xa0a0a0a,u3)],[0],[(1,24),(1,35)]),
([u9,u1,u0,u2,u4,0xff330000],[(u9,u0,u4),(0xff330000,u9,u3)],[1,2],[(0,24)]),
([u13,u9,u1,u0,u2,u3],[],[],[(0,13),(0,34),(0,35),(0,36)]),
([0xa8a8a8a8,u1,u0,u2,u4,u3],[],[],[(0,26),(1,8)]),
([0x33223322,u1,u0,u2,u4,u3],[],[],[]),
([u13,u1,u0,u2,u15,u3],[(u15,u1,u4),(u13,u1,u4)],[0,1],[(0,37)]),
([0xfc00fc,u1,u0,u2,u4,u3],[],[],[]),
([u1,u0,u2,0xfcfc0000,u4],[(u11,u0,u2),(0xfcfc0000,u11,u3)],[0],[(1,27),(1,37)]),
([u1,u0,u2,0xfcfc0000,u11,u4],[(u11,u0,u2),(0xfcfc0000,u11,u3)],[2],[(1,37)]),
([0xfcfc,u1,u0,u2,u11,u4],[(u11,u0,u2),(0xfcfc,u11,u3)],[3],[]),
([u1,0xaeaeaeae,u0,u2,u4,u3],[(0xc0c0c0c,u0,u2),(0xaeaeaeae,0xc0c0c0c,u1)],[1,2,3],[(0,38),(1,13),(1,36)]),
([0xa2a2a2a2,u1,u0,u2,u4,u3],[],[],[]),
([u1,u0,u2,0xf0faf0fa,u4,u3],[],[],[]),
([u13,u1,u0,u2,u10,u3],[(u13,u1,u4),(u10,u2,u4)],[0],[(0,39),(0,40)]),
([u13,u17,u1,u0,u2,u3],[(u13,u1,u4),(u17,u4,u3)],[2],[(0,41)]),
([u1,u0,0xeeeeaaaa,u2,u4,u3],[(0xcccc0000,u0,u3),(0xeeeeaaaa,0xcccc0000,u1)],[1,3],[(0,42)]),
([0x2222aaaa,u1,u0,u2,u4,u3],[],[],[]),
([u1,u0,u2,0xfafaf0f0,u4,u3],[],[],[]),
([u1,u0,u2,0xfcfcf0f0,u4,u3],[(0xcccc0000,u0,u3),(0xfcfcf0f0,0xcccc0000,u2)],[0],[]),
([u1,0xbbbbaaaa,u0,u2,u4,u3],[],[],[]),
([0x8888aaaa,u1,u0,u2,u4,u3],[(u16,u0,u3),(0x8888aaaa,u16,u1)],[0,3],[(1,43)]),
([u1,u0,u2,0xf3f3f0f0,u4,u3],[],[],[]),
([u1,u0,u2,0xf5f5f0f0,u4,u3],[(0x55550000,u1,u3),(0xf5f5f0f0,0x55550000,u2)],[0],[]),
([0xaaa0aaa0,u1,u0,u2,u4,u3],[(u10,u2,u4),(0xaaa0aaa0,u1,u10)],[1],[(0,29)]),
([0x33303330,u1,u0,u2,u4,u3],[(u10,u4,u2),(0x33303330,u0,u10)],[1],[(1,39)]),
([u1,u0,u2,u4,u22],[(u10,u2,u4),(u22,u10,u3)],[0,1],[(0,30),(0,40),(1,30),(1,40)]),
([u1,u0,u2,u4,u22,u10],[(u10,u2,u4),(u22,u10,u3)],[2],[]),
([0xfff0,u1,u0,u2,u4,u10],[(u10,u2,u4),(0xfff0,u10,u3)],[3],[]),
([u1,0xaaffaaaa,u0,u2,u4,u3],[(u17,u4,u3),(0xaaffaaaa,u17,u1)],[2],[(0,41)]),
([0xaa00aaaa,u1,u0,u2,u4,u3],[(u17,u4,u3),(0xaa00aaaa,u17,u1)],[0,1,3],[(1,44)]),
([u1,0xafafaaaa,u0,u2,u4,u3],[(0xf0f0000,u2,u3),(0xafafaaaa,0xf0f0000,u1)],[0,1,3],[(0,45)]),
([0xa0a0aaaa,u1,u0,u2,u4,u3],[(0xf0f0000,u2,u3),(0xa0a0aaaa,0xf0f0000,u1)],[2],[(0,31)]),
([u1,u0,u2,0xf0fff0f0,u4,u3],[],[],[])
]
def c5_1_L6 : Array W5Node := Array.mk [
([u7,u1,u0,u2,u4,u3],[(u7,u1,u0)],[0,1,2,3],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10)]),
([u1,u0,u5,u2,u4,u3],[(u5,u1,u0)],[0,1,2,3],[(0,1),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(1,1),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18)]),
([u8,u1,u0,u2,u4,u3],[(u8,u1,u0)],[0,1,2,3],[(0,0),(0,11),(0,22),(0,23),(0,24),(0,27),(0,28),(0,29),(0,30),(1,25),(1,26),(1,29),(1,31)]),
([u1,u0,u2,u6,u4,u3],[(u6,u1,u2)],[0,1,2,3],[(0,15),(0,30),(0,35),(0,38),(0,39),(1,12),(1,27),(1,32),(1,33),(1,34),(1,36),(1,37)]),
([u9,u1,u0,u2,u4,u3],[(u9,u0,u4)],[0,1,2,3],[(0,5),(0,13),(0,25),(0,31),(0,32),(0,40),(0,41),(0,42),(0,44),(0,46),(0,47),(1,43),(1,45)]),
([u1,u0,u2,u11,u4,u3],[(u11,u0,u2)],[0,1,2,3],[(0,15),(0,48),(0,51),(0,52),(0,53),(0,54),(1,25),(1,33),(1,38),(1,49),(1,50)]),
([u13,u1,u0,u2,u4,u3],[(u13,u1,u4)],[0,1,2,3],[(0,5),(0,27),(0,43),(0,47),(0,50),(0,57),(0,58),(0,59),(1,55),(1,56)]),
([0xaaaa0000,u1,u0,u2,u4,u3],[(0xaaaa0000,u1,u3)],[0,1,2,3],[(0,62),(1,60),(1,61),(1,63)]),
([u16,u1,u0,u2,u4,u3],[(u16,u0,u3)],[0,1,2,3],[(0,64),(0,65),(0,66),(1,67)]),
([u1,u0,u2,u4,u10,u3],[(u10,u2,u4)],[0,1,2,3],[(0,36),(0,38),(0,43),(0,58),(0,68),(0,69),(0,70),(0,71),(0,72),(1,36),(1,38),(1,43),(1,58),(1,68),(1,69)]),
([u17,u1,u0,u2,u4,u3],[(u17,u4,u3)],[0,1,2,3],[(0,37),(0,59),(0,73),(0,74),(0,77),(1,75),(1,76)])
]
def c5_1_L7 : Array W5Node := Array.mk [
([u1,u0,u2,u4,u3],[],[0,1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,10)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_3_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 3 c5_1_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_3 : ∀ i < c5_1_L3.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 3 c5_1_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_1_L3.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_1 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_2 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 32 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_4 : ∀ i < c5_1_L4.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 i = true := by
  intro i hi
  have hsz : c5_1_L4.size = 46 := by decide +kernel
  have hi' : i < 46 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW5_at c5_1_chk_4_0 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_4_1 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_1_chk_4_2 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_1 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_2 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_3 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_4 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 64 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_5 : ∀ i < c5_1_L5.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 i = true := by
  intro i hi
  have hsz : c5_1_L5.size = 78 := by decide +kernel
  have hi' : i < 78 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_1_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_1_chk_5_1 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_5_2 i (by omega) (by omega)
  ·
    by_cases h : i < 64
    ·
      exact checkBlockW5_at c5_1_chk_5_3 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_5_4 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_6_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 0 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_6 : ∀ i < c5_1_L6.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 i = true := by
  intro i hi
  have hsz : c5_1_L6.size = 11 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_7_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 7 c5_1_L7 c5_1_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_7 : ∀ i < c5_1_L7.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 7 c5_1_L7 c5_1_L6 i = true := by
  intro i hi
  have hsz : c5_1_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_1_L3_sound : ∀ i < c5_1_L3.size, ¬ live (basicOps 32) c5_1_goal 3 (c5_1_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound (fun j hj => by simp at hj) c5_1_chk_3
theorem c5_1_L4_sound : ∀ i < c5_1_L4.size, ¬ live (basicOps 32) c5_1_goal 4 (c5_1_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L3_sound c5_1_chk_4
theorem c5_1_L5_sound : ∀ i < c5_1_L5.size, ¬ live (basicOps 32) c5_1_goal 5 (c5_1_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L4_sound c5_1_chk_5
theorem c5_1_L6_sound : ∀ i < c5_1_L6.size, ¬ live (basicOps 32) c5_1_goal 6 (c5_1_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L5_sound c5_1_chk_6
theorem c5_1_L7_sound : ∀ i < c5_1_L7.size, ¬ live (basicOps 32) c5_1_goal 7 (c5_1_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L6_sound c5_1_chk_7
set_option maxRecDepth 100000 in
theorem c5_1_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_1_goal ws) = [rows5] := by decide +kernel
theorem c5_1_top_match : sameSet (rows5.map (actB 32 (c5_1_pow[0]?.getD []))) (c5_1_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_1_no_build : ¬ build (basicOps 32) c5_1_goal 7 rows5.toFinset :=
  no_build_of_top c5_1_G_valid (by decide) c5_1_sublists c5_1_top_match (c5_1_L7_sound 0 (by decide))

def nrmM64 (m : BitVec 64) (b0 : ℕ) (u : BitVec 64) : BitVec 64 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM64 (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 64) :
    projS 32 idxs (nrmM64 m b0 u) = projS 32 idxs u := by
  unfold nrmM64
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 32 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 32 idxs m hm (~~~u), projS_not 32 (by decide) idxs hlen hlt u]

abbrev W6Node := List (BitVec 64) × List (BitVec 64 × BitVec 64 × BitVec 64) × List ℕ × List (ℕ × ℕ)

def checkReplay64 (m : BitVec 64) (b0 : ℕ) (bank : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → Bool
  | [], targets => targets.all (fun t => nrmM64 m b0 t == 0 || bank.contains (nrmM64 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 64 a b).contains v &&
    checkReplay64 m b0 (v :: bank) rest targets

theorem checkReplay64_sound (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 32)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay64 m b0 bank steps targets = true →
      build (basicOps 32) g k (nonZeroImg (projS 32 idxs) targets.toFinset) →
      build (basicOps 32) g (k + steps.length) (nonZeroImg (projS 32 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 32 := projS 32 idxs
  have hn : 0 < 32 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay64, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM64 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM64 m b0 t, hmem, projS_nrmM64 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay64, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 32 (f a) (f b) := projS_ops 32 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 32 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 32 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 32 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 32 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed64 (stock needed : List (BitVec 64)) (u : BitVec 64) : List (BitVec 64) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded64 (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM64 m b0 w
    let needed' := if needed.contains pw then addNeed64 stock (addNeed64 stock needed (nrmM64 m b0 a)) (nrmM64 m b0 b) else needed
    buildNeeded64 m b0 stock rest needed'

def buildSteps64 (m : BitVec 64) (b0 : ℕ) (needed : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64 × BitVec 64 × BitVec 64)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM64 m b0 w
    let pa := nrmM64 m b0 a
    let pb := nrmM64 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 64 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps64 m b0 needed rest (pw :: bank)
    else
      buildSteps64 m b0 needed rest bank

def checkCofClose64 (lb fuel : ℕ) (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM64 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeed64 stock acc (nrmM64 m b0 u)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeeded64 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildSteps64 m b0 needed hist stock
        Nat.blt (steps.length + rem) lb && checkReplay64 m b0 stock steps nxt
      else false
    else false
  else false

theorem checkCofClose64_sound_aux (goal6 : BitVec 64) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 64)) (g : BitVec 32) (hgnz : g ≠ 0)
    (hg : projS 32 idxs goal6 = g)
    (hstock : stock.all (fun w => rows5.contains (projS 32 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 32) g (lb - 1) rows5.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose64 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose64 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 32) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM64 m b0 u == 0)).length ≤ zCount (projS 32 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM64 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM64 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay64_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 32 idxs) stock.toFinset ⊆ rows5.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW6 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose64 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW6 (goal6 : BitVec 64) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (a b : BitVec 64) (r : List (BitVec 64)) : Bool :=
  (ops 64 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 64 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 64 jumps6 goal6 (w :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 64 jumps6 goal6 (w :: a :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 64 jumps6 goal6 (w :: b :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 64 jumps6 goal6 (w :: a :: b :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW6 (goal6 : BitVec 64) (gsize : ℕ) (g6_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cur prev : Array W6Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal6) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW6 goal6 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW6 (goal6 : BitVec 64) (gsize : ℕ) (g6_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cur prev : Array W6Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW6_at {goal6 : BitVec 64} {gsize ncf k start m : ℕ} {g6_pow : Array (List ℕ)}
    {cfLBs cfB0s : Array ℕ} {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (h : checkBlockW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW6, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W6 {goal6 : BitVec 64} {gsize ncf k i : ℕ}
    {g6_idx g6_pow : Array (List ℕ)} {g6_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 64 gsize g6_idx g6_pow g6_inv goal6) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose64 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 64) goal6 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW6 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 64) goal6 (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (g6_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[g]?.getD []))).toFinset.image
        (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 64 (g6_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal6 ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 64} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 64 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 64) goal6 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 64 jumps6 goal6 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW6 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 64 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW6 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact hcof c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 64 a b ▸ hz)

theorem level_sound_W6 {goal6 : BitVec 64} {gsize ncf k : ℕ}
    {g6_idx g6_pow : Array (List ℕ)} {g6_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 64 gsize g6_idx g6_pow g6_inv goal6) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose64 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 64) goal6 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W6 hk hi hvalid hcof hprev (hblk i hi)

def v0 : BitVec 64 := 0xaaaaaaaaaaaaaaaa
def v1 : BitVec 64 := 0xff00ff00ff00ff00
def v2 : BitVec 64 := 0xcccccccccccccccc
def v3 : BitVec 64 := 0xf0f0f0f0f0f0f0f0
def v4 : BitVec 64 := 0xffff0000ffff0000
def v5 : BitVec 64 := 0xffffffff00000000
def v6 : BitVec 64 := 0xeeeeeeeeeeeeeeee
def v7 : BitVec 64 := 0xffaaffaaffaaffaa
def v8 : BitVec 64 := 0xfcfcfcfcfcfcfcfc
def v9 : BitVec 64 := 0xfafafafafafafafa
def v10 : BitVec 64 := 0xffffff00ffffff00
def v11 : BitVec 64 := 0xfffffffff0f0f0f0
def v12 : BitVec 64 := 0xffffffffcccccccc
def v13 : BitVec 64 := 0xffccffccffccffcc
def v14 : BitVec 64 := 0xffffffffffff0000
def v15 : BitVec 64 := 0xfffff0f0fffff0f0
def v16 : BitVec 64 := 0xffffffffff00ff00
def v17 : BitVec 64 := 0xffffaaaaffffaaaa
def v18 : BitVec 64 := 0xfff0fff0fff0fff0
def v19 : BitVec 64 := 0xfffafffafffafffa
def v20 : BitVec 64 := 0xfefefefefefefefe
def v21 : BitVec 64 := 0xffffffaaffffffaa
def v22 : BitVec 64 := 0xffffccccffffcccc
def v23 : BitVec 64 := 0xffffffffaaaaaaaa
def v24 : BitVec 64 := 0xeeeeeeee
def v25 : BitVec 64 := 0xffccffcc
def v26 : BitVec 64 := 0xffffffffffccffcc
def v27 : BitVec 64 := 0xf0a0f0a0f0a0f0a
def v28 : BitVec 64 := 0xfff0fff0
def v29 : BitVec 64 := 0xffeeffeeffeeffee
def v30 : BitVec 64 := 0xffaaffaa
def v31 : BitVec 64 := 0xfffafffa
def v32 : BitVec 64 := 0xfffffffffffff0f0
def v33 : BitVec 64 := 0xf0f0a0a0f0f0a0a
def v34 : BitVec 64 := 0xe0e0e0e0e0e0e0e
def v35 : BitVec 64 := 0xfefefefe
def v36 : BitVec 64 := 0xf0f0f000f0f0f00
def v37 : BitVec 64 := 0xffffff00
def v38 : BitVec 64 := 0xffffffaa
def v39 : BitVec 64 := 0xfcfcfcfc
def v40 : BitVec 64 := 0xf0f0f0f0f0f0000
def v41 : BitVec 64 := 0xfffffffffcfcfcfc
def v42 : BitVec 64 := 0xf0f0c0c0f0f0c0c
def v43 : BitVec 64 := 0xffffffccffffffcc
def v44 : BitVec 64 := 0xffffffffeeeeeeee
def v45 : BitVec 64 := 0xfffffcfcfffffcfc
def v46 : BitVec 64 := 0xfffffafafffffafa
def v47 : BitVec 64 := 0xffffffffffaaffaa
def v48 : BitVec 64 := 0xfffffffffff0fff0
def v49 : BitVec 64 := 0xffffeeeeffffeeee
def v50 : BitVec 64 := 0xffffffffffffff00
def v51 : BitVec 64 := 0xffaa
def v52 : BitVec 64 := 0xfffefffefffefffe
def v53 : BitVec 64 := 0xffffffeeffffffee
def v54 : BitVec 64 := 0xfffcfffcfffcfffc
def v55 : BitVec 64 := 0xe0e0e0e
def v56 : BitVec 64 := 0xf0f0e0e0f0f0e0e
def v57 : BitVec 64 := 0xf0f0f0a0f0f0f0a
def v58 : BitVec 64 := 0xf0a0f0a
def v59 : BitVec 64 := 0xfffffff0fffffff0
def v60 : BitVec 64 := 0x302030203020302
def v61 : BitVec 64 := 0xf0f0f0c0f0f0f0c
def v62 : BitVec 64 := 0xffeeffee
def v63 : BitVec 64 := 0xeeee
def v64 : BitVec 64 := 0x5454545454545454
def v65 : BitVec 64 := 0xffffffcc
def v66 : BitVec 64 := 0x5550555055505550
def v67 : BitVec 64 := 0xffffffffffffaaaa
def v68 : BitVec 64 := 0xfffcfffc
def v69 : BitVec 64 := 0xf0c0f0c
def v70 : BitVec 64 := 0xfffffffffafafafa
def v71 : BitVec 64 := 0xf0f0f0f0c0c0c0c
def v72 : BitVec 64 := 0xf0e0f0e0f0e0f0e
def v73 : BitVec 64 := 0x3333333333003300
def v74 : BitVec 64 := 0xffaa0000ffaa
def v75 : BitVec 64 := 0xf0f0f0f0f0f0a0a
def v76 : BitVec 64 := 0xf0f0f00
def v77 : BitVec 64 := 0xfe00fe00fe00fe00
def v78 : BitVec 64 := 0xff00ff00cc00cc
def v79 : BitVec 64 := 0xf0f0a0a
def v80 : BitVec 64 := 0xf0f0c0c
def v81 : BitVec 64 := 0x3232323232323232
def v82 : BitVec 64 := 0xfffefffe
def v83 : BitVec 64 := 0xf0f0f0e0f0f0f0e
def v84 : BitVec 64 := 0xf0f0f0f0f000f00
def v85 : BitVec 64 := 0xffccf0c0ffccf0c0
def v86 : BitVec 64 := 0xeeeee0e0eeeee0e0
def v87 : BitVec 64 := 0xffffaaaacccc8888
def v88 : BitVec 64 := 0x3322332233223322
def v89 : BitVec 64 := 0xffffffee
def v90 : BitVec 64 := 0x303030303000300
def v91 : BitVec 64 := 0xfffffffafffffffa
def v92 : BitVec 64 := 0xfffffffcfffffffc
def v93 : BitVec 64 := 0x5555550055555500
def v94 : BitVec 64 := 0x55445544
def v95 : BitVec 64 := 0x3333333322222222
def v96 : BitVec 64 := 0xfffffefefffffefe
def v97 : BitVec 64 := 0x54545454
def v98 : BitVec 64 := 0x55505550
def v99 : BitVec 64 := 0xf0f0f0f0f0f0f00
def v100 : BitVec 64 := 0xffaaffaaf0a0f0a0
def v101 : BitVec 64 := 0x303030003030300
def v102 : BitVec 64 := 0xff00fc00ff00fc00
def v103 : BitVec 64 := 0xfffffffffffffafa
def v104 : BitVec 64 := 0xfffffffffffcfffc
def v105 : BitVec 64 := 0x5544554455445544
def v106 : BitVec 64 := 0x55555500
def v107 : BitVec 64 := 0xfff0
def v108 : BitVec 64 := 0xfafa
def v109 : BitVec 64 := 0xffffffffffffffcc
def v110 : BitVec 64 := 0x5555555550505050
def v111 : BitVec 64 := 0xffffffffffffffaa
def v112 : BitVec 64 := 0x303030302020202
def v113 : BitVec 64 := 0xfefe0000fefe0000
def v114 : BitVec 64 := 0x5555555544444444
def v115 : BitVec 64 := 0xfafa0000fafa
def v116 : BitVec 64 := 0xfffffffffffafffa
def v117 : BitVec 64 := 0xffffffffffffcccc
def v118 : BitVec 64 := 0x5555505055555050
def v119 : BitVec 64 := 0xffaaffaaffaa0000
def v120 : BitVec 64 := 0xffff0000ff00
def v121 : BitVec 64 := 0x3333333330303030
def v122 : BitVec 64 := 0xffff0000eeee0000
def v123 : BitVec 64 := 0xff00ff00aa00aa
def v124 : BitVec 64 := 0xffffffffffeeffee
def v125 : BitVec 64 := 0x3333222233332222
def v126 : BitVec 64 := 0xfffafffa00000000
def v127 : BitVec 64 := 0xeeee0000eeee
def v128 : BitVec 64 := 0x3333333333330000
def v129 : BitVec 64 := 0xff00ff00ff00f000
def v130 : BitVec 64 := 0xaaaafefeaaaafefe
def v131 : BitVec 64 := 0xff00ff00ff0000
def v132 : BitVec 64 := 0xffffaaaa
def v133 : BitVec 64 := 0xffaaf0a0ffaaf0a0
def v134 : BitVec 64 := 0xf0c0f0c0f0c0f0c
def v135 : BitVec 64 := 0xfefe0000fefe
def v136 : BitVec 64 := 0xffff0000ffcc
def v137 : BitVec 64 := 0xaaaaaaaafefefefe
def v138 : BitVec 64 := 0xafafafafaeaeaeae
def v139 : BitVec 64 := 0xaaaaaaaafffafffa
def v140 : BitVec 64 := 0xaaaaffffaaaaeeee
def v141 : BitVec 64 := 0xfffffffffffffff0
def v142 : BitVec 64 := 0xffffffffffccf0c0
def v143 : BitVec 64 := 0xffffffff0f0f0a0a
def v144 : BitVec 64 := 0xffffffff0f0a0f0a
def v145 : BitVec 64 := 0x5555555555005500
def v146 : BitVec 64 := 0xff33ff22ff33ff22
def v147 : BitVec 64 := 0xffffffff55445544
def v148 : BitVec 64 := 0xffffffff0000fafa
def v149 : BitVec 64 := 0xf0f0f0f0fffffafa
def v150 : BitVec 64 := 0xffffffff0000eeee
def v151 : BitVec 64 := 0xeeeeeeeeeeee0000
def v152 : BitVec 64 := 0xff00ff00ffffffaa
def v153 : BitVec 64 := 0xffff0000ffcc0000
def v154 : BitVec 64 := 0xffffffff0000ffaa
def v155 : BitVec 64 := 0xfcfc0000fcfc
def v156 : BitVec 64 := 0xaaaaaaaaffeeffee
def v157 : BitVec 64 := 0xffffcccc
def v158 : BitVec 64 := 0x3333303033333030
def v159 : BitVec 64 := 0xff33ff33ff22ff22
def v160 : BitVec 64 := 0xafafafafafaaafaa
def v161 : BitVec 64 := 0xffff0000cccc
def v162 : BitVec 64 := 0xaaaaaaaaffffffaa
def v163 : BitVec 64 := 0xfafafafac8c8c8c8
def v164 : BitVec 64 := 0xffff0000eeee
def v165 : BitVec 64 := 0xff0eff0eff0eff0e
def v166 : BitVec 64 := 0xf0f0f0f0fefefefe
def v167 : BitVec 64 := 0xffffffff0e0e0e0e
def v168 : BitVec 64 := 0xff00ff00ffeeffee
def v169 : BitVec 64 := 0xffffffff0f0c0f0c
def v170 : BitVec 64 := 0xf0f0f0f0fffafffa
def v171 : BitVec 64 := 0xf0f0f0f0fffffff0
def v172 : BitVec 64 := 0xffffffff0f0f0f00
def v173 : BitVec 64 := 0xff32ff32ff32ff32
def v174 : BitVec 64 := 0xeee0eee0eee0eee0
def v175 : BitVec 64 := 0xfafafafa
def v176 : BitVec 64 := 0xff33ff33ff30ff30
def v177 : BitVec 64 := 0xffaacc88ffaacc88
def v178 : BitVec 64 := 0xfff0ccc0fff0ccc0
def v179 : BitVec 64 := 0xfff0fff0fff00000
def v180 : BitVec 64 := 0xafafafafafafaaaa
def v181 : BitVec 64 := 0xaaaaffffaaaaffaa
def v182 : BitVec 64 := 0xf0f0f0f0a0a0a0a
def v183 : BitVec 64 := 0xff33ff33ff33ff00
def v184 : BitVec 64 := 0xffffffaaffccff88
def v185 : BitVec 64 := 0xfafafafafa00fa00
def v186 : BitVec 64 := 0xfffc0000fffc
def v187 : BitVec 64 := 0xff32ff32
def v188 : BitVec 64 := 0xff00ff00fffafffa
def v189 : BitVec 64 := 0xf3f2f3f2f3f2f3f2
def v190 : BitVec 64 := 0xf3f3f3f0f3f3f3f0
def v191 : BitVec 64 := 0xffffffaa00000000
def v192 : BitVec 64 := 0xff00ff00f000f0
def v193 : BitVec 64 := 0xff33ff22
def v194 : BitVec 64 := 0xffffffff0000fff0
def v195 : BitVec 64 := 0xee00ee00ee00ee
def v196 : BitVec 64 := 0xfc00fc00fc00fc
def v197 : BitVec 64 := 0xe000e000e000e
def v198 : BitVec 64 := 0xffffeeee
def v199 : BitVec 64 := 0xff00f000ff00f0
def v200 : BitVec 64 := 0x5555555555550000
def v201 : BitVec 64 := 0xaaaaffffaaaafafa
def v202 : BitVec 64 := 0xafafafaaafafafaa
def v203 : BitVec 64 := 0xfff00000fff0
def v204 : BitVec 64 := 0xfcfcfc00fcfcfc00
def v205 : BitVec 64 := 0xfefefefe00000000
def v206 : BitVec 64 := 0xf3f3f3f3f2f2f2f2
def v207 : BitVec 64 := 0xff0fff0fff0cff0c
def v208 : BitVec 64 := 0xf0fff0faf0fff0fa
def v209 : BitVec 64 := 0xff0fff0aff0fff0a
def v210 : BitVec 64 := 0xf0f0f0f0fffffcfc
def v211 : BitVec 64 := 0xffffffff0f0f0c0c
def v212 : BitVec 64 := 0xffffaaaaff00aa00
def v213 : BitVec 64 := 0xf0f0f0f0fffcfffc
def v214 : BitVec 64 := 0xffffffaafffff0a0
def v215 : BitVec 64 := 0xffffffff0000ffcc
def v216 : BitVec 64 := 0xff0fff0cff0fff0c
def v217 : BitVec 64 := 0xff0fff0fff0fff00
def v218 : BitVec 64 := 0xff33ff30ff33ff30
def v219 : BitVec 64 := 0xfffffffffefefefe
def v220 : BitVec 64 := 0xffffffff54545454
def v221 : BitVec 64 := 0xafafaeaeafafaeae
def v222 : BitVec 64 := 0xff00ff00ffffffcc
def v223 : BitVec 64 := 0xff00ff00fffffff0
def v224 : BitVec 64 := 0xffffffff55505550
def v225 : BitVec 64 := 0xff00ff00fffcfffc
def v226 : BitVec 64 := 0xff00f050ff00f050
def v227 : BitVec 64 := 0xafaeafaeafaeafae
def v228 : BitVec 64 := 0xffffffff0000fcfc
def v229 : BitVec 64 := 0xeeeeee00eeeeee00
def v230 : BitVec 64 := 0xff00aa00ff00aa
def v231 : BitVec 64 := 0xffcc0000ffcc
def v232 : BitVec 64 := 0xaaaafffaaaaafffa
def v233 : BitVec 64 := 0xff00cc00ff00cc
def v234 : BitVec 64 := 0xffffffff55555500
def v235 : BitVec 64 := 0x550033007700
def v236 : BitVec 64 := 0xff00ffffff00ffcc
def v237 : BitVec 64 := 0xf3f3f2f2f3f3f2f2
def v238 : BitVec 64 := 0xf0fef0fef0fef0fe
def v239 : BitVec 64 := 0xffff0000fffffafa
def v240 : BitVec 64 := 0xffff0000ffffeeee
def v241 : BitVec 64 := 0xcfcecfcecfcecfce
def v242 : BitVec 64 := 0xcfcfcfcfcfcccfcc
def v243 : BitVec 64 := 0xf3f3f3f3f3f0f3f0
def v244 : BitVec 64 := 0x3333330033333300
def v245 : BitVec 64 := 0xffff0000ffffffaa
def v246 : BitVec 64 := 0xf0fff0fcf0fff0fc
def v247 : BitVec 64 := 0xf0fff0fff0fff0f0
def v248 : BitVec 64 := 0xffff0e0effff0e0e
def v249 : BitVec 64 := 0xff00ff00ff00ffee
def v250 : BitVec 64 := 0x5555444455554444
def v251 : BitVec 64 := 0x3330333033303330
def v252 : BitVec 64 := 0xaaaaffeeaaaaffee
def v253 : BitVec 64 := 0xff00ff00ff330000
def v254 : BitVec 64 := 0xf0f0f0f0f0c0f0c
def v255 : BitVec 64 := 0xffffeeee00000000
def v256 : BitVec 64 := 0xff55ff55ff44ff44
def v257 : BitVec 64 := 0xff00ff00ff00f0f0
def v258 : BitVec 64 := 0xff00ff00fffefffe
def v259 : BitVec 64 := 0x303020203030202
def v260 : BitVec 64 := 0xf3f3f3f3f3f3f0f0
def v261 : BitVec 64 := 0x303030303030000
def v262 : BitVec 64 := 0xccccccccfffcfffc
def v263 : BitVec 64 := 0xccccccccffeeffee
def v264 : BitVec 64 := 0xff0fff0fff0aff0a

def g6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s1 : List ℕ := [0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31,32,33,36,37,34,35,38,39,48,49,52,53,50,51,54,55,40,41,44,45,42,43,46,47,56,57,60,61,58,59,62,63]
def g6_p1 : List ℕ := [1,2,16,32,4,8,64,128,65536,131072,1048576,2097152,262144,524288,4194304,8388608,256,512,4096,8192,1024,2048,16384,32768,16777216,33554432,268435456,536870912,67108864,134217728,1073741824,2147483648,4294967296,8589934592,68719476736,137438953472,17179869184,34359738368,274877906944,549755813888,281474976710656,562949953421312,4503599627370496,9007199254740992,1125899906842624,2251799813685248,18014398509481984,36028797018963968,1099511627776,2199023255552,17592186044416,35184372088832,4398046511104,8796093022208,70368744177664,140737488355328,72057594037927936,144115188075855872,1152921504606846976,2305843009213693952,288230376151711744,576460752303423488,4611686018427387904,9223372036854775808]
def g6_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31,48,50,49,51,52,54,53,55,56,58,57,59,60,62,61,63]
def g6_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768,4294967296,17179869184,8589934592,34359738368,68719476736,274877906944,137438953472,549755813888,1099511627776,4398046511104,2199023255552,8796093022208,17592186044416,70368744177664,35184372088832,140737488355328,65536,262144,131072,524288,1048576,4194304,2097152,8388608,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648,281474976710656,1125899906842624,562949953421312,2251799813685248,4503599627370496,18014398509481984,9007199254740992,36028797018963968,72057594037927936,288230376151711744,144115188075855872,576460752303423488,1152921504606846976,4611686018427387904,2305843009213693952,9223372036854775808]
def g6_s3 : List ℕ := [0,2,4,6,1,3,5,7,32,34,36,38,33,35,37,39,8,10,12,14,9,11,13,15,40,42,44,46,41,43,45,47,16,18,20,22,17,19,21,23,48,50,52,54,49,51,53,55,24,26,28,30,25,27,29,31,56,58,60,62,57,59,61,63]
def g6_p3 : List ℕ := [1,4,16,64,2,8,32,128,4294967296,17179869184,68719476736,274877906944,8589934592,34359738368,137438953472,549755813888,256,1024,4096,16384,512,2048,8192,32768,1099511627776,4398046511104,17592186044416,70368744177664,2199023255552,8796093022208,35184372088832,140737488355328,65536,262144,1048576,4194304,131072,524288,2097152,8388608,281474976710656,1125899906842624,4503599627370496,18014398509481984,562949953421312,2251799813685248,9007199254740992,36028797018963968,16777216,67108864,268435456,1073741824,33554432,134217728,536870912,2147483648,72057594037927936,288230376151711744,1152921504606846976,4611686018427387904,144115188075855872,576460752303423488,2305843009213693952,9223372036854775808]
def g6_s4 : List ℕ := [0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23,32,36,33,37,34,38,35,39,48,52,49,53,50,54,51,55,8,12,9,13,10,14,11,15,24,28,25,29,26,30,27,31,40,44,41,45,42,46,43,47,56,60,57,61,58,62,59,63]
def g6_p4 : List ℕ := [1,16,2,32,4,64,8,128,65536,1048576,131072,2097152,262144,4194304,524288,8388608,4294967296,68719476736,8589934592,137438953472,17179869184,274877906944,34359738368,549755813888,281474976710656,4503599627370496,562949953421312,9007199254740992,1125899906842624,18014398509481984,2251799813685248,36028797018963968,256,4096,512,8192,1024,16384,2048,32768,16777216,268435456,33554432,536870912,67108864,1073741824,134217728,2147483648,1099511627776,17592186044416,2199023255552,35184372088832,4398046511104,70368744177664,8796093022208,140737488355328,72057594037927936,1152921504606846976,144115188075855872,2305843009213693952,288230376151711744,4611686018427387904,576460752303423488,9223372036854775808]
def g6_s5 : List ℕ := [0,4,2,6,1,5,3,7,32,36,34,38,33,37,35,39,16,20,18,22,17,21,19,23,48,52,50,54,49,53,51,55,8,12,10,14,9,13,11,15,40,44,42,46,41,45,43,47,24,28,26,30,25,29,27,31,56,60,58,62,57,61,59,63]
def g6_p5 : List ℕ := [1,16,4,64,2,32,8,128,4294967296,68719476736,17179869184,274877906944,8589934592,137438953472,34359738368,549755813888,65536,1048576,262144,4194304,131072,2097152,524288,8388608,281474976710656,4503599627370496,1125899906842624,18014398509481984,562949953421312,9007199254740992,2251799813685248,36028797018963968,256,4096,1024,16384,512,8192,2048,32768,1099511627776,17592186044416,4398046511104,70368744177664,2199023255552,35184372088832,8796093022208,140737488355328,16777216,268435456,67108864,1073741824,33554432,536870912,134217728,2147483648,72057594037927936,1152921504606846976,288230376151711744,4611686018427387904,144115188075855872,2305843009213693952,576460752303423488,9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0,g6_s1,g6_s2,g6_s3,g6_s4,g6_s5]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0,g6_p1,g6_p2,g6_p3,g6_p4,g6_p5]
def g6_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_G_valid : (List.range 6).all (symValid 64 6 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel

def g6_m0 : BitVec 64 := 0xffffffff

def g6_st0 : List (BitVec 64) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def g6_ix0 : List ℕ := [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31]

set_option maxRecDepth 100000 in

theorem g6_cspec_0 : g6_ix0.length = 32 ∧ (∀ idx ∈ g6_ix0, idx < 64) ∧ (∀ idx ∈ g6_ix0, g6_m0.getLsbD idx = true) ∧ projS 32 g6_ix0 goal6 = c5_0_goal ∧ g6_st0.all (fun w => rows5.contains (projS 32 g6_ix0 w)) = true := by decide +kernel

def g6_m1 : BitVec 64 := 0xff00ff00ff00ff

def g6_st1 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]

def g6_ix1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_1 : g6_ix1.length = 32 ∧ (∀ idx ∈ g6_ix1, idx < 64) ∧ (∀ idx ∈ g6_ix1, g6_m1.getLsbD idx = true) ∧ projS 32 g6_ix1 goal6 = c5_0_goal ∧ g6_st1.all (fun w => rows5.contains (projS 32 g6_ix1 w)) = true := by decide +kernel

def g6_m2 : BitVec 64 := 0x3333333333333333

def g6_st2 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]

def g6_ix2 : List ℕ := [0,1,4,5,8,9,12,13,32,33,36,37,40,41,44,45,16,17,20,21,24,25,28,29,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_2 : g6_ix2.length = 32 ∧ (∀ idx ∈ g6_ix2, idx < 64) ∧ (∀ idx ∈ g6_ix2, g6_m2.getLsbD idx = true) ∧ projS 32 g6_ix2 goal6 = c5_1_goal ∧ g6_st2.all (fun w => rows5.contains (projS 32 g6_ix2 w)) = true := by decide +kernel

def g6_m3 : BitVec 64 := 0xf0f0f0f0f0f0f0f

def g6_st3 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]

def g6_ix3 : List ℕ := [0,1,2,3,16,17,18,19,32,33,34,35,48,49,50,51,8,9,10,11,24,25,26,27,40,41,42,43,56,57,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_3 : g6_ix3.length = 32 ∧ (∀ idx ∈ g6_ix3, idx < 64) ∧ (∀ idx ∈ g6_ix3, g6_m3.getLsbD idx = true) ∧ projS 32 g6_ix3 goal6 = c5_1_goal ∧ g6_st3.all (fun w => rows5.contains (projS 32 g6_ix3 w)) = true := by decide +kernel

def g6_m4 : BitVec 64 := 0x5555555555555555

def g6_st4 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]

def g6_ix4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_4 : g6_ix4.length = 32 ∧ (∀ idx ∈ g6_ix4, idx < 64) ∧ (∀ idx ∈ g6_ix4, g6_m4.getLsbD idx = true) ∧ projS 32 g6_ix4 goal6 = c5_1_goal ∧ g6_st4.all (fun w => rows5.contains (projS 32 g6_ix4 w)) = true := by decide +kernel

def g6_m5 : BitVec 64 := 0xffff0000ffff

def g6_st5 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]

def g6_ix5 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,32,33,36,37,34,35,38,39,40,41,44,45,42,43,46,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_5 : g6_ix5.length = 32 ∧ (∀ idx ∈ g6_ix5, idx < 64) ∧ (∀ idx ∈ g6_ix5, g6_m5.getLsbD idx = true) ∧ projS 32 g6_ix5 goal6 = c5_0_goal ∧ g6_st5.all (fun w => rows5.contains (projS 32 g6_ix5 w)) = true := by decide +kernel

def g6_cfMasks : Array (BitVec 64) := Array.mk [g6_m0,g6_m1,g6_m2,g6_m3,g6_m4,g6_m5]

def g6_cfB0s : Array ℕ := Array.mk [0,0,0,0,0,0]

def g6_cfStocks : Array (List (BitVec 64)) := Array.mk [g6_st0,g6_st1,g6_st2,g6_st3,g6_st4,g6_st5]

def g6_cfLBs : Array ℕ := Array.mk [8,8,8,8,8,8]

theorem g6_cof_sound (c fuel : ℕ) (hc : c < 6) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) (hnd : nxt.Nodup) (hchk : checkCofClose64 (g6_cfLBs[c]?.getD 0) fuel (g6_cfMasks[c]?.getD 0) (g6_cfB0s[c]?.getD 0) (g6_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose64_sound_aux goal6 8 g6_ix0 g6_cspec_0.1 g6_cspec_0.2.1 g6_m0 g6_cspec_0.2.2.1 0 g6_st0 c5_0_goal (by decide) g6_cspec_0.2.2.2.1 g6_cspec_0.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_sound_aux goal6 8 g6_ix1 g6_cspec_1.1 g6_cspec_1.2.1 g6_m1 g6_cspec_1.2.2.1 0 g6_st1 c5_0_goal (by decide) g6_cspec_1.2.2.2.1 g6_cspec_1.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_sound_aux goal6 8 g6_ix2 g6_cspec_2.1 g6_cspec_2.2.1 g6_m2 g6_cspec_2.2.2.1 0 g6_st2 c5_1_goal (by decide) g6_cspec_2.2.2.2.1 g6_cspec_2.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_sound_aux goal6 8 g6_ix3 g6_cspec_3.1 g6_cspec_3.2.1 g6_m3 g6_cspec_3.2.2.1 0 g6_st3 c5_1_goal (by decide) g6_cspec_3.2.2.2.1 g6_cspec_3.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_sound_aux goal6 8 g6_ix4 g6_cspec_4.1 g6_cspec_4.2.1 g6_m4 g6_cspec_4.2.2.1 0 g6_st4 c5_1_goal (by decide) g6_cspec_4.2.2.2.1 g6_cspec_4.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_sound_aux goal6 8 g6_ix5 g6_cspec_5.1 g6_cspec_5.2.1 g6_m5 g6_cspec_5.2.2.1 0 g6_st5 c5_0_goal (by decide) g6_cspec_5.2.2.2.1 g6_cspec_5.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | c + 6 => omega

def g6_L3 : Array W6Node := Array.mk [
([v0,0xfcfcfca8fcfcfca8,v85,v5],[],[],[]),
([v0,v2,v3,0xffffffaaffccf080],[],[],[])
]

def g6_L4 : Array W6Node := Array.mk [
([v86,v8,v1,v17,v5],[],[],[]),
([v39,0xeeeeeeeee0e0e0e0,v9,v1,v4],[],[],[]),
([v0,0xfcfcfca8fcfcfca8,v13,v15,v5],[],[],[(0,0)]),
([v0,v8,v85,v21,v5],[(v8,v2,v3),(v13,v2,v1),(v15,v3,v4),(v17,v0,v4),(v21,v1,v17),(v85,v13,v15)],[0],[(0,0)]),
([v0,v204,v13,v15,v5],[],[],[]),
([v63,v6,v3,v1,v87],[(v6,v0,v2),(v17,v0,v4),(v12,v2,v5),(v24,v6,v5),(v63,v24,v4),(v87,v17,v12)],[1],[]),
([v40,v6,v3,v1,v87],[],[],[]),
([v0,v204,v8,v85,v5],[],[],[]),
([0x555533330000,v6,v3,v1,v87],[],[],[]),
([v0,v8,v85,v10,v142],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1),(v10,v1,v4),(v85,v13,v15),(v142,v85,v5)],[2],[]),
([v235,v6,v3,v87,v14],[],[],[]),
([v0,v8,v85,v10,v5],[],[],[]),
([v28,v2,v9,v100,v4],[],[],[]),
([v0,v2,v3,0xff000054ff000054,v5],[],[],[]),
([v0,v2,v3,v184,v32],[],[],[(0,1)]),
([v0,v2,v3,v10,v142],[],[],[]),
([v0,v2,v3,0xffffff00ffccff0c,v32],[],[],[]),
([v40,v0,v2,v3,v184],[],[],[]),
([v0,v2,v3,0xffffff00ffccf000,v142],[],[],[]),
([0xff88,v0,v2,v3,v184],[],[],[]),
([v0,v2,v3,v1,0xffffffaaffcc0000],[],[],[]),
([v0,v2,v3,v253,v236],[],[],[]),
([v0,v2,v3,v1,0xff00ff55ffff00aa],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L5 : Array W6Node := Array.mk [
([v60,v9,v1,v29,v4,v5],[(v8,v3,v2),(v9,v3,v0),(v6,v2,v0),(v29,v6,v1),(v60,v8,v29)],[3],[]),
([v39,v6,v9,v1,v4,v41],[(v6,v0,v2),(v9,v0,v3),(v8,v2,v3),(v41,v8,v5),(v39,v5,v41)],[4],[]),
([v60,v6,v9,v1,v4,v5],[(v8,v3,v2),(v9,v3,v0),(v6,v2,v0),(v29,v6,v1),(v60,v8,v29)],[4],[]),
([0xeeee0404eeee0404,v6,v8,v1,v4,v5],[],[],[]),
([v24,v39,v6,v9,v1,v4],[],[],[]),
([v112,v6,v9,v1,v4,v5],[(v8,v3,v2),(v9,v3,v0),(v6,v2,v0),(v44,v6,v5),(v112,v8,v44)],[4],[]),
([v31,v6,v9,v8,v1,v4],[(v6,v2,v0),(v8,v2,v3),(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[4],[]),
([0xf0f04040f0f0404,v6,v8,v1,v4,v5],[],[],[]),
([v0,v86,v8,v1,v4,v5],[],[],[]),
([v55,v6,v9,v1,v4,v12],[],[],[(2,0)]),
([v86,v8,v1,v17,v5],[],[],[]),
([v86,v6,v8,v1,v17,v5],[],[],[]),
([v86,v8,v1,v17,v15,v5],[],[],[]),
([v60,v9,v7,v13,v4,v5],[],[],[(4,0)]),
([v86,v8,v1,v4,v46,v5],[],[],[]),
([v39,v6,v9,v1,v4,v12],[],[],[(1,1)]),
([v0,v8,v1,0xffccfac8ffccfac8,v4,v5],[],[],[]),
([v42,v6,v8,v1,v17,v5],[],[],[]),
([v0,v86,v8,v1,v49,v5],[],[],[]),
([v39,v71,v0,v6,v1,v4],[],[],[]),
([0xa8a8acaca8a8acac,v2,v9,v1,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v46,v9,v4),(v118,v0,v46),(0xa8a8acaca8a8acac,v118,v8)],[4],[]),
([0xa8a8a8a8acacacac,v2,v9,v1,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v70,v9,v5),(v110,v0,v70),(0xa8a8a8a8acacacac,v110,v8)],[4],[]),
([v0,v8,v13,v15,v21,v5],[(v8,v2,v3),(v13,v2,v1),(v15,v3,v4),(v17,v0,v4),(v21,v1,v17)],[0],[(0,2),(0,3)]),
([v0,v8,v1,v85,v17,v5],[],[],[(0,3)]),
([0xf0f0a0a0c0c0808,v6,v3,v1,v4,v5],[],[],[]),
([v63,v6,v3,v1,v17,v12],[(v6,v0,v2),(v17,v0,v4),(v12,v2,v5),(v24,v6,v5),(v63,v24,v4)],[1],[(0,5),(3,4)]),
([v24,v6,v3,v1,v4,v87],[],[],[(0,5)]),
([v40,v6,v3,v1,v17,v12],[],[],[(0,6)]),
([v0,v204,v13,v15,v5],[],[],[]),
([v0,v204,v8,v13,v15,v5],[],[],[(0,7)]),
([v0,v204,v13,v15,v10,v5],[],[],[]),
([v101,v0,v13,v15,v10,v5],[],[],[(0,4)]),
([v0,v8,v85,v10,v5],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1),(v10,v1,v4),(v85,v13,v15)],[0,2],[(0,3),(0,7),(0,9),(4,5),(4,6),(4,8),(4,10)]),
([v0,v8,v85,v13,v10,v5],[],[],[]),
([v58,v2,v9,v7,v4,v16],[],[],[(2,11)]),
([v28,v2,v9,v7,v4,v11],[],[],[(0,12)]),
([v0,v8,v1,v85,v43,v5],[],[],[(3,12)]),
([v0,v8,v1,0xffeefaeaffeefaea,v4,v5],[],[],[]),
([0x444422226666,v6,v3,v1,v4,v5],[],[],[]),
([v0,v8,v1,v85,v4,v142],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1),(v85,v13,v15),(v142,v85,v5)],[2,3],[(0,9)]),
([v235,v6,v3,v4,v87,v5],[],[],[(0,10)]),
([v0,v8,v1,v85,v4,v5],[],[],[(0,11)]),
([v33,v6,v237,v1,v4,v5],[],[],[]),
([v27,v88,v9,v13,v4,v5],[],[],[]),
([v0,0xcccccacacccccaca,v8,v1,v4,v5],[],[],[]),
([v0,v2,v163,v1,v4,v11],[],[],[]),
([v0,v2,0xfafafafafac8fac8,v1,v4,v11],[],[],[(2,2)]),
([v0,v2,0xfafafafa00003232,v1,v4,v11],[],[],[]),
([0x303505003035050,v0,v2,0xfcfca8a8fcfca8a8,v1,v5],[],[],[]),
([0x303505003035050,v0,v2,v1,v15,v5],[],[],[]),
([v0,v2,0xfafafafa02020202,v1,v4,v11],[],[],[]),
([v0,v2,v185,v1,v4,v11],[],[],[(2,4)]),
([v0,0xccccc0c0cfcfc0c0,v8,v1,v4,v5],[],[],[]),
([v0,v2,v185,v4,v10,v11],[],[],[]),
([v0,v2,0xfafafafa000000fa,v1,v4,v11],[],[],[]),
([0x30003cc030003cc,v0,v3,v13,v4,v5],[],[],[]),
([v30,v2,v3,v185,v7,v4],[],[],[]),
([v0,v2,0xfafafafa000a000a,v1,v4,v11],[],[],[]),
([v0,v2,0xfafafafa00000a0a,v1,v4,v11],[],[],[]),
([v34,v81,v64,v1,v4,v5],[],[],[]),
([v35,v34,v64,v2,v1,v4],[],[],[]),
([v34,v81,v0,v77,v4,v5],[],[],[]),
([v34,v81,v0,v205,v1,v4],[],[],[]),
([v35,v34,v81,v0,v1,v4],[],[],[]),
([v34,v0,v2,v77,v113,v5],[],[],[]),
([v35,v0,v2,v3,v77,v4],[],[],[]),
([v35,v135,v0,v2,v3,v1],[],[],[]),
([v0,v2,v3,v77,v113,v205],[],[],[]),
([v35,v0,v2,v3,v77,v113],[],[],[]),
([v72,v0,v2,v113,v1,v5],[],[],[]),
([v56,v0,v2,v77,v4,v5],[],[],[]),
([0x1000100fffefffe,v0,v2,v3,v1,v4],[],[],[]),
([v82,v0,v2,v3,v113,v1],[],[],[]),
([v35,v135,v0,v2,v3,v77],[],[],[]),
([v56,0x5555545455555454,v2,v1,v4,v5],[],[],[]),
([v72,0x3332333233323332,v0,v1,v4,v5],[],[],[]),
([v56,v0,v2,0xff00fe00ff00fe00,v4,v5],[],[],[]),
([v35,0xf0f0f0f0e0e0e0e,v0,v2,v1,v4],[],[],[]),
([v35,0x5555555554545454,v2,v3,v1,v4],[],[],[]),
([v72,v0,v2,v1,0xfffe0000fffe0000,v5],[],[],[]),
([v35,v0,v2,v3,0xff00ff00fe00fe00,v4],[],[],[]),
([v35,0xffff0000fefe,v0,v2,v3,v1],[],[],[]),
([v82,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,0xff00fe00ff00fe00,v4,0xfffffefe00000000],[],[],[]),
([v82,v0,v2,v3,v1,0xfffe0000fffe0000],[],[],[]),
([v83,v0,v2,v1,v4,v5],[],[],[]),
([0xfffffffe,v0,v2,v3,v1,v4],[],[],[]),
([v82,0xfffe0000fffe,v0,v2,v3,v1],[],[],[]),
([v0,v2,v3,v1,0xfffe0100fffe0100,v5],[],[],[]),
([v35,0xfffe0000fffe,v0,v2,v3,v1],[],[],[]),
([v35,v135,0xfe00fe00fe00fe,v0,v2,v3],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff01010100],[],[],[]),
([v35,v164,v0,v2,v3,v1],[],[],[]),
([v35,v186,v0,v2,v3,v1],[],[],[]),
([v0,v2,v3,v1,0xfffafffa01000100,v4],[],[],[]),
([v0,v2,v3,0xfe00fe00fe04fe04,v4,v5],[],[],[]),
([v0,v2,v238,v165,v4,v5],[],[],[]),
([0xffffff0e,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v166,v1,v4,v167],[],[],[]),
([v55,v0,v2,v3,v1,0xffff00000e0e0000],[],[],[]),
([v187,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff00000054],[],[],[]),
([0xa0a0e0e0a0a0e0e,v64,v2,v1,v4,v5],[],[],[]),
([v39,0xf0f0f0f04040404,v0,v2,v1,v4],[],[],[]),
([v24,0x3333333302020202,v0,v3,v1,v4],[],[],[]),
([v24,0x5555555504040404,v2,v3,v1,v4],[],[],[]),
([v0,0xcdcdc8c8cdcdc8c8,v8,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffffcdcdc8c8],[],[],[]),
([v33,v118,v2,v1,v22,v5],[],[],[]),
([v39,v71,v121,v0,v1,v4],[],[],[]),
([0xff33ff32,v0,v2,v3,v1,v4],[],[],[]),
([v57,0x5555555055555550,v2,v1,v4,v5],[],[],[]),
([v68,0x3333333333303330,v0,v3,v1,v4],[],[],[]),
([v62,0x3333333333223322,v0,v3,v1,v4],[],[],[]),
([v57,v0,0xccccccc8ccccccc8,v1,v4,v5],[],[],[]),
([v62,0x5555555555445544,v2,v3,v1,v4],[],[],[]),
([v68,v254,v0,v2,v1,v4],[],[],[]),
([v62,v0,v2,0xf0f0f0f0f0e0f0e0,v1,v4],[],[],[]),
([0xaaaaaaaaaaa8aaa8,v2,v3,v1,0xffff0000fffc0000,v5],[],[],[]),
([v89,v0,v2,0xf0f0f0e0f0f0f0e0,v1,v4],[],[],[]),
([v68,0xaaaaaaaaaaa8aaa8,v2,v3,v1,v4],[],[],[]),
([v83,v0,v2,v1,v4,0xffffffee00000000],[],[],[]),
([v89,v83,v0,v2,v1,v4],[],[],[]),
([v62,0xff00ff00ee00ee,v0,v2,v3,v4],[],[],[]),
([v62,v0,v2,v3,v1,0xffff0000ffee0000],[],[],[]),
([v89,v0,v2,v3,v1,v4],[],[],[]),
([0xf0f0f0f0f0f0f0e,v0,v2,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff000000fc],[],[],[]),
([v24,0x5555555555445544,v2,v3,v1,v4],[],[],[]),
([v24,0x3333333333223322,v0,v3,v1,v4],[],[],[]),
([0x303030354545454,v0,v2,v3,v1,v4],[],[],[]),
([v30,v0,v2,v3,v225,v4],[],[],[]),
([v0,v2,v3,v1,v239,v148],[],[],[]),
([v39,0xf0f0f0f00000c0c,v0,v2,v1,v4],[],[],[]),
([v39,v0,v2,v149,v1,v4],[],[],[]),
([v27,v66,v2,v13,v4,v5],[],[],[]),
([v24,v95,v114,v3,v1,v4],[],[],[]),
([v27,v66,v2,v1,v126,v4],[],[],[]),
([v31,v27,v66,v2,v1,v4],[],[],[]),
([v24,v95,v0,v3,v1,v122],[],[],[]),
([v24,v164,v95,v0,v3,v1],[],[],[]),
([v56,v0,v2,v1,v255,v15],[],[],[]),
([v55,v0,v2,v3,v1,v122],[],[],[]),
([v56,v0,v2,v102,v4,v5],[],[],[]),
([v72,v0,v2,v1,v126,v4],[],[],[]),
([0x1010fffffefe,v0,v2,v3,v1,v4],[],[],[]),
([v35,v0,v2,v3,0xff00ff00fa00fa00,v4],[],[],[]),
([v82,v0,v2,v3,v1,0xfffc0000fffc0000],[],[],[]),
([v0,v2,v3,0xff00fe02ff00fe02,v4,v5],[],[],[]),
([v31,0xfffe0000fffe,v0,v2,v3,v1],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff00001110],[],[],[]),
([v24,v114,v2,v3,v1,v122],[],[],[]),
([v24,v164,v114,v2,v3,v1],[],[],[]),
([v0,v130,v2,v3,v102,v5],[],[],[]),
([v83,v0,v2,v1,v4,v255],[],[],[]),
([v31,0x3333333233333332,v0,v3,v1,v4],[],[],[]),
([0x1100ffffffee,v0,v2,v3,v1,v4],[],[],[]),
([v62,v0,v2,v3,v1,v122],[],[],[]),
([v0,v2,v3,v1,0xffff0000ffee1100,v5],[],[],[]),
([v61,0x3333333033333330,v0,v1,v4,v5],[],[],[]),
([v31,0x5555555555505550,v2,v3,v1,v4],[],[],[]),
([v31,0xf0f0f0f0f0a0f0a,v0,v2,v1,v4],[],[],[]),
([v31,0xff00ff00fa00fa,v0,v2,v3,v4],[],[],[]),
([0x303545403035454,v0,v2,v3,v1,v5],[],[],[]),
([v28,v0,v2,v3,v168,v4],[],[],[]),
([v25,v0,v2,v3,v188,v4],[],[],[(2,13)]),
([v0,v2,v3,v1,v240,v150],[],[],[]),
([v63,v0,v2,v3,v10,v16],[(v6,v0,v2),(v127,v6,v4),(v63,v127,v5),(v16,v1,v5),(v10,v1,v4)],[1],[]),
([v24,0x5555555500004444,v2,v3,v1,v4],[],[],[]),
([v24,0xaaaaaaaafffffafa,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,0xffff0303ff000300,v14],[],[],[]),
([0x303ffff0303fcfc,v0,v2,v3,v1,v5],[],[],[]),
([v0,0xcfcfcfcfcececece,v206,v1,v4,v5],[],[],[]),
([0x303525203035252,v0,v2,v1,v4,v5],[],[],[]),
([v39,v0,v2,v163,v1,v4],[],[],[(1,1)]),
([v0,v241,v189,v1,v4,v5],[],[],[]),
([v0,v2,0xeeeee0f0eeeee0f0,v3,v1,v5],[],[],[]),
([0xeefeeefe,v0,v2,v3,v1,v4],[],[],[]),
([0xeeffeefe,v0,v2,v3,v1,v4],[],[],[]),
([v0,v242,v243,v1,v4,v5],[],[],[]),
([v0,v2,v151,v3,v10,v16],[],[],[]),
([0xfefefeaa,v0,v2,v3,v1,v4],[],[],[]),
([v0,0xcfcfcfcccfcfcfcc,v190,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffffa8a8a8fc],[],[],[]),
([0xeeffeeee,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,v87,v32],[(v11,v3,v5),(v12,v2,v5),(v17,v0,v4),(v32,v4,v11),(v87,v17,v12)],[1],[(0,14),(3,3)]),
([v0,v2,v3,v1,0xffaaffaaf0b0f0b0,v4],[],[],[]),
([v0,v2,v3,v1,v17,v142],[],[],[(4,14)]),
([0xaa8caa8caa8caa8c,v2,v3,v7,v4,v5],[],[],[]),
([v0,0xcccccccccacacaca,v3,v1,v4,v12],[],[],[]),
([v27,v0,v189,v13,v4,v5],[],[],[]),
([v0,v2,0xf0f0f0f0f3c0f3c0,v1,v4,v11],[],[],[]),
([v33,v0,v2,v226,v1,v5],[],[],[]),
([v0,v2,v3,v10,v26,v32],[(v11,v3,v5),(v12,v2,v5),(v10,v4,v1),(v32,v4,v11),(v26,v1,v12)],[1],[(0,15)]),
([v57,v0,v2,v1,v15,v191],[],[],[]),
([v25,v73,v0,v3,v7,v4],[],[],[]),
([v0,v2,v3,v1,v4,v142],[],[],[(0,15)]),
([v0,v2,v3,v226,v21,v5],[],[],[]),
([0xaa88aaccaa88aacc,v2,v3,v7,v4,v5],[],[],[]),
([v25,v0,v2,v3,0xffffffaaffff0022,v5],[],[],[(3,16)]),
([0xffaaffccffee,v0,v2,v3,v4,v5],[],[],[]),
([v0,v2,v3,v1,v17,0xffffffffff00f050],[],[],[]),
([0xaa88aa88aaccaacc,v2,v3,v7,v4,v5],[],[],[]),
([0xaaaa8c8caaaa8c8c,v2,v3,v1,v17,v5],[],[],[]),
([v0,v2,0xf0f0f0f0f300f300,v1,v4,v11],[],[],[]),
([v0,0xcccccacacccccaca,v3,v1,v22,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffffccccd8d8],[],[],[]),
([v62,v123,v0,v2,v3,v4],[],[],[]),
([v30,0x5555555555445544,v2,v3,v1,v4],[],[],[]),
([v30,0xff00ff00ee00ee,v0,v2,v3,v4],[],[],[]),
([0xffbaffba,v0,v2,v3,v1,v4],[],[],[]),
([0xb0b0a0a0b0b0a0a,v118,v2,v1,v4,v5],[],[],[]),
([0xdcdcdcdc,v121,v0,v3,v1,v4],[],[],[]),
([v27,v0,v2,v207,v4,v5],[],[],[]),
([v0,v2,v208,v209,v4,v5],[],[],[]),
([v0,v2,v149,v1,v4,v143],[],[],[]),
([0xccfcccfc,v121,v0,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff55445040],[],[],[]),
([0xaeaeaeae,v114,v2,v3,v1,v4],[],[],[]),
([0xff0cff0c,v78,v0,v2,v3,v4],[(v12,v2,v5),(v71,v3,v12),(v207,v71,v1),(v78,v1,v12),(0xff0cff0c,v5,v207)],[1],[]),
([0xff30ff30,v192,v0,v2,v3,v4],[],[],[]),
([0xfff3fff2,v0,v2,v3,v1,v4],[],[],[]),
([v28,v254,v0,v2,v1,v4],[],[],[]),
([0x3333fffffcfc,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v210,v1,v4,v211],[],[],[]),
([0xffbbffba,v0,v2,v3,v1,v4],[],[],[]),
([0x5555fffffafa,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,0xffffaaaaffccaa88,v14],[],[],[(3,15)]),
([v0,v2,v3,v1,v212,v32],[],[],[]),
([0xf0f33333030,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v213,v1,v4,v169],[],[],[]),
([v25,v0,v2,v3,v152,v4],[],[],[]),
([v0,0xcccacccacccaccca,v3,v13,v4,v5],[],[],[]),
([v0,v2,0xf0f0f0f0f5a0f5a0,v1,v4,v11],[],[],[]),
([v0,v2,v3,v1,0xff33ff33f020f020,v4],[],[],[]),
([0xaaa0aaf0aaa0aaf0,v2,v3,v7,v4,v5],[],[],[]),
([v28,v84,v0,v2,v7,v4],[],[],[]),
([0xaaa0aaa0aaf0aaf0,v2,v3,v7,v4,v5],[],[],[]),
([v0,v2,0xf0f0f0f0f500f500,v1,v4,v11],[],[],[]),
([v0,v2,v3,v1,0xffff0000ffcc1100,v5],[],[],[]),
([v0,v2,v3,0xff00fc00ff00fc0c,v4,v5],[],[],[]),
([v193,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v170,v1,v4,v144],[],[],[]),
([0xaaaaeeee,v114,v2,v3,v1,v4],[],[],[]),
([v25,0x3333333303000300,v0,v3,v1,v4],[],[],[]),
([0xff44ff44,v78,v0,v2,v3,v4],[(v12,v2,v5),(v114,v0,v12),(v256,v114,v1),(v78,v1,v12),(0xff44ff44,v5,v256)],[1],[]),
([v30,0x5555555505000500,v2,v3,v1,v4],[],[],[]),
([0xff50ff50,v192,v0,v2,v3,v4],[],[],[]),
([v0,v2,v3,v1,v87,v14],[],[],[(3,11),(3,15)]),
([v36,v244,v0,v13,v15,v5],[],[],[]),
([v40,v0,v2,v3,v1,v87],[],[],[(0,6),(0,17)]),
([0xffccf0c0,v0,v2,v3,v10,v5],[],[],[(0,15)]),
([v0,v2,v3,v10,v142],[],[],[(0,18),(4,14),(4,17),(4,19)]),
([v0,v2,v3,v1,v184,v14],[(v17,v0,v4),(v12,v2,v5),(v14,v4,v5),(v87,v17,v12),(v184,v1,v87)],[1],[(0,20)]),
([v0,v2,v3,v100,v214,v16],[(v7,v0,v1),(v11,v3,v5),(v16,v1,v5),(v100,v7,v11),(v214,v4,v100)],[4],[(2,9)]),
([v235,v0,v2,v3,v87,v14],[],[],[(0,10),(3,15)]),
([0x555533330000,v0,v2,v3,v1,v87],[],[],[(0,8)]),
([0x555533330000,v0,v2,v3,v1,v14],[],[],[]),
([v0,v2,v3,v7,v214,v16],[],[],[]),
([v28,v0,v2,v3,v100,v4],[],[],[(0,12)]),
([0x555533332222,v0,v2,v3,v1,v4],[],[],[]),
([0xffccff88,v0,v2,v3,v4,v184],[],[],[(0,19)]),
([v0,0xccccccccccccaaaa,v3,v1,v4,v12],[],[],[]),
([v0,v2,v3,0xff00f030ff00f030,v10,v5],[],[],[]),
([v36,v0,v190,v13,v4,v5],[],[],[]),
([v0,0xccccccaaccccccaa,v3,v13,v4,v5],[],[],[]),
([v0,v2,v3,v226,v10,v5],[],[],[]),
([v40,v0,v2,v3,v10,v26],[],[],[]),
([v40,v0,v2,v10,v16,v32],[],[],[]),
([v51,v0,v2,v3,v21,v16],[(v7,v0,v1),(v16,v1,v5),(v14,v4,v5),(v21,v4,v7),(v51,v14,v21)],[0],[]),
([v40,v0,v2,v15,v10,v16],[(v15,v3,v4),(v10,v4,v1),(v16,v5,v1),(v32,v5,v15),(v40,v3,v32)],[5],[]),
([v0,v2,v3,v119,v21,v16],[],[],[]),
([v0,v2,v3,v1,v212,v14],[],[],[]),
([v25,v73,v0,v3,v4,v10],[],[],[]),
([v0,v2,v3,v1,0xffff0000ff000f00,v32],[],[],[]),
([v0,0xcccccc00ccffcc00,v3,v13,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xffff0000ffcc3300,v14],[],[],[]),
([v25,v0,v2,v3,v10,v215],[],[],[(5,21)]),
([v51,v0,v2,v3,v4,0xffff0055ff000000],[],[],[(1,22)]),
([v30,v0,v2,v3,v4,0xffff0055ff000000],[],[],[]),
([v25,v73,v0,v3,v1,v153],[],[],[]),
([v25,v136,v73,v0,v3,v1],[],[],[]),
([v25,v78,v73,v0,v3,v4],[(v12,v2,v5),(v26,v12,v1),(v73,v2,v26),(v25,v5,v26),(v78,v1,v26)],[1],[]),
([v83,v0,v2,v1,v4,v191],[],[],[]),
([v38,v83,v0,v2,v1,v4],[],[],[]),
([0x44ffffffee,v0,v2,v3,v1,v4],[],[],[]),
([v62,v0,v2,v3,v1,v153],[],[],[]),
([v0,v2,v3,0xff00ff00ff00fa0a,v4,v5],[],[],[]),
([v25,v78,v0,v2,v3,v153],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v78,v1,v26),(v153,v4,v26)],[1],[]),
([v25,v136,v78,v0,v2,v3],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v78,v1,v26),(v136,v4,v26)],[1],[]),
([v38,0x5555555555555500,v2,v3,v1,v4],[],[],[]),
([v65,0x3333333333333300,v0,v3,v1,v4],[],[],[]),
([v65,0xff00ff00ff00cc,v0,v2,v3,v4],[],[],[]),
([v38,0xffff0000ffaa,v0,v2,v3,v1],[],[],[]),
([v51,0xff00aa,v0,v2,v3,v21],[],[],[]),
([0xff0f0f00f0,v0,v2,v3,v1,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff0000f0fc],[],[],[]),
([v0,v2,v3,v1,v245,v154],[],[],[]),
([0xff00ffcc,v78,v0,v2,v3,v4],[(v12,v2,v5),(v78,v12,v1),(0xff000000cc,v78,v4),(v236,0xff000000cc,v1),(0xff00ffcc,v5,v236)],[1],[]),
([v30,v123,v145,v2,v3,v4],[],[],[]),
([0xffbbffaa,v0,v2,v3,v1,v4],[],[],[]),
([v37,0xffff0000fff0,v0,v2,v3,v1],[],[],[]),
([v37,v136,v0,v2,v3,v1],[],[],[]),
([0xffffffffcc,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v171,v1,v4,v172],[],[],[]),
([v31,v186,v0,v2,v3,v1],[],[],[]),
([0xfff2fff2,v0,v2,v3,v1,v4],[],[],[]),
([0xcececece,v95,v0,v3,v1,v4],[],[],[]),
([v0,v2,v246,v216,v4,v5],[],[],[]),
([0xffffff0a,v0,v2,v3,v1,v4],[],[],[]),
([0xff0aff0a,v123,v0,v2,v3,v4],[],[],[]),
([0xff22ff22,v123,v0,v2,v3,v4],[],[],[]),
([0xfffaeeea,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,0xffff0000fffffff0,v194],[],[],[]),
([v0,v2,v247,v217,v4,v5],[],[],[]),
([v51,v0,v2,v3,v10,v16],[(v10,v4,v1),(v21,v0,v10),(v74,v4,v21),(v51,v74,v5),(v16,v1,v5)],[1],[]),
([v0,v2,v3,v1,0xffff0000ff000f00,v14],[],[],[]),
([v0,v2,v3,v257,v4,v16],[(v14,v4,v5),(v32,v3,v14),(v131,v14,v1),(v257,v131,v32),(v16,v1,v5)],[0],[]),
([v51,0xff00aa,v0,v2,v3,v10],[],[],[]),
([0xcfcccfcc,v73,v0,v3,v1,v4],[],[],[]),
([0xccccffcc,v73,v0,v3,v1,v4],[],[],[]),
([v0,0xaaaaaaffaa00aa00,v2,v3,v16,v14],[],[],[]),
([v40,v73,v0,v2,v3,v10],[],[],[]),
([v107,v0,v2,v3,v10,v16],[(v16,v5,v1),(v48,v3,v16),(v28,v5,v48),(v107,v28,v4),(v10,v1,v4)],[1],[]),
([v0,v2,v3,v1,0xffff0000ff005500,v14],[],[],[]),
([v0,v2,v3,v1,0xffff0000ff003300,v14],[],[],[]),
([0xafaaafaa,v145,v2,v3,v1,v4],[],[],[]),
([0xaaaaffaa,v145,v2,v3,v1,v4],[],[],[]),
([0xccffcccc,v128,v0,v3,v1,v4],[],[],[]),
([0xff33ff00,v131,v0,v2,v3,v4],[],[],[]),
([0xccffcccc,v0,v2,v3,v10,v14],[],[],[]),
([v37,v120,v131,v0,v2,v3],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L6 : Array W6Node := Array.mk [
([v6,v9,v1,v4,v5,v41],[(v6,v0,v2),(v9,v0,v3),(v8,v2,v3),(v41,v8,v5)],[0,4],[(0,1),(4,0),(5,0)]),
([v6,v9,v8,v1,v29,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v6,v0,v2),(v29,v6,v1)],[1,3,4],[(0,2),(2,2),(3,1)]),
([v39,v6,v9,v1,v4,v5],[(v6,v0,v2),(v9,v0,v3),(v8,v2,v3),(v39,v8,v5)],[0,2,3],[(0,1),(0,4),(1,4),(2,3),(3,3)]),
([v39,v6,v9,v8,v1,v4,v5],[(v6,v0,v2),(v9,v0,v3),(v8,v2,v3),(v39,v8,v5)],[0,4],[(0,1)]),
([v6,v9,v8,v1,v19,v4,v5],[(v6,v2,v0),(v8,v2,v3),(v9,v0,v3),(v19,v9,v1)],[0,2,4],[(0,2),(0,6),(3,5)]),
([v24,v6,v9,v8,v1,v4,v5],[(v8,v3,v2),(v9,v3,v0),(v6,v2,v0),(v24,v6,v5)],[0,2,4],[(0,4)]),
([v6,v9,v8,v1,v4,v10,v5],[(v9,v3,v0),(v8,v3,v2),(v6,v0,v2),(v10,v1,v4)],[4],[]),
([v0,v6,v8,v1,v4,v248,v5],[],[],[(5,7)]),
([v55,v2,v6,v9,v1,v4,v5],[(v9,v0,v3),(v6,v0,v2),(v34,v3,v6),(v55,v34,v5)],[4],[(0,9),(2,8)]),
([v34,v81,v6,v9,v1,v4,v5],[(v9,v0,v3),(v6,v0,v2),(v34,v3,v6),(v81,v2,v9)],[2,4],[]),
([v34,v6,v9,v1,v4,v5,v12],[(v9,v0,v3),(v6,v0,v2),(v34,v3,v6),(v12,v2,v5)],[4],[(0,9)]),
([v34,v0,v8,v1,v29,v4,v5],[],[],[]),
([v39,v64,v2,v9,v1,v4,v5],[],[],[]),
([v6,v9,v1,v4,v12,v11],[],[],[(0,9),(1,9),(2,10),(2,11),(2,12),(3,11),(3,12),(4,13),(5,13)]),
([v6,v9,v1,v4,v5,v12,v41],[(v6,v0,v2),(v9,v0,v3),(v12,v2,v5),(v41,v3,v12)],[4],[(0,15),(3,14),(4,0)]),
([v0,v8,v1,v13,v4,v46,v5],[],[],[(0,16)]),
([v39,v2,v9,v1,v7,v4,v5],[],[],[]),
([v0,v6,v8,v1,v49,v15,v5],[(v8,v2,v3),(v6,v2,v0),(v15,v3,v4),(v49,v6,v4)],[0,3],[(0,18),(5,17)]),
([v0,v86,v6,v8,v1,v4,v5],[(v8,v2,v3),(v6,v2,v0),(v15,v3,v4),(v86,v6,v15)],[2,3],[(0,11),(0,18)]),
([v0,v86,v8,v1,v4,v15,v5],[(v8,v2,v3),(v6,v2,v0),(v15,v3,v4),(v86,v6,v15)],[2,3],[(0,12)]),
([v60,v2,v9,v1,v7,v4,v5],[],[],[(0,0),(0,13),(4,8)]),
([v24,v6,v3,v9,v1,v4,v12],[],[],[(0,9)]),
([v0,v6,v8,v1,v15,v10,v5],[],[],[]),
([v42,v0,v6,v8,v1,v4,v5],[],[],[(0,17),(2,5)]),
([v56,v0,v6,v8,v1,v4,v5],[],[],[(2,5)]),
([v60,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v19,v9,v1),(v60,v8,v19)],[4],[(0,2)]),
([v31,v0,v2,v9,v8,v1,v4],[(v9,v3,v0),(v8,v3,v2),(v19,v9,v1),(v31,v19,v5)],[4],[(0,6)]),
([v72,v0,v8,v1,v29,v4,v5],[],[],[(2,0)]),
([v33,v2,v6,v1,v4,v46,v5],[],[],[(1,0),(2,19)]),
([v60,v0,v3,v1,v29,v4,v5],[(v6,v2,v0),(v8,v2,v3),(v29,v6,v1),(v60,v8,v29)],[3],[(0,0)]),
([v39,v0,v2,v9,v1,v4,v41],[(v8,v3,v2),(v9,v3,v0),(v41,v8,v5),(v39,v5,v41)],[4],[(0,1),(1,19)]),
([v33,v2,v6,v9,v1,v4,v5],[],[],[(1,2),(2,19),(5,20)]),
([v72,v0,v6,v8,v1,v4,v5],[],[],[(2,2)]),
([v60,v0,v6,v3,v1,v4,v5],[(v6,v2,v0),(v8,v2,v3),(v29,v6,v1),(v60,v8,v29)],[4],[(0,2)]),
([v0,v2,0xfafafafa02020202,v9,v1,v4,v5],[],[],[(3,3)]),
([v24,v39,v0,v6,v3,v1,v4],[],[],[(0,4)]),
([v56,v2,v6,v9,v1,v4,v5],[(v6,v0,v2),(v9,v0,v3),(v49,v6,v4),(v56,v3,v49)],[3],[(1,2)]),
([v27,v2,v6,v9,v1,v4,v5],[],[],[(0,2),(5,21)]),
([v112,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v70,v9,v5),(v112,v8,v70)],[4],[(0,5)]),
([v31,v2,v6,v3,v9,v1,v4],[(v9,v0,v3),(v6,v0,v2),(v19,v9,v1),(v31,v5,v19)],[2,3],[(0,6)]),
([v0,v8,v1,v13,v17,v15,v5],[],[],[(0,22),(0,23)]),
([v33,v6,v3,v1,v4,v5,v12],[],[],[(0,24)]),
([v24,v6,v3,v1,v4,v17,v12],[],[],[(0,25),(0,26)]),
([v0,v8,v13,v15,v10,v5],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1),(v10,v1,v4)],[0],[(0,22),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(1,33),(2,34),(3,34),(4,25),(4,27)]),
([v0,v8,v1,v13,v15,v43,v5],[(v8,v2,v3),(v13,v2,v1),(v15,v3,v4),(v43,v4,v13)],[3],[(0,36),(3,35)]),
([v0,v8,v1,v85,v4,v5],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1),(v85,v13,v15)],[0,1,2,3,5],[(0,23),(0,32),(0,37),(0,39),(1,23),(4,24),(4,26),(4,38),(4,40),(5,26)]),
([v0,v8,v1,v85,v13,v4,v5],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1),(v85,v13,v15)],[2,3,5],[(0,33),(0,36)]),
([v58,v2,v9,v1,v7,v4,v5],[],[],[(0,34),(2,41)]),
([v0,v227,v8,v1,v13,v4,v5],[],[],[(4,42)]),
([v0,v8,v1,v218,v4,v15,v5],[],[],[]),
([v27,v2,v9,v7,v13,v4,v5],[],[],[(0,13),(0,43)]),
([v27,v2,v9,v1,v29,v4,v5],[],[],[(0,0),(4,44)]),
([v27,v88,v2,v9,v1,v4,v5],[(v9,v0,v3),(v7,v0,v1),(v27,v3,v7),(v88,v2,v7)],[3],[(0,43),(1,42)]),
([v24,v114,v6,v3,v1,v4,v12],[(v6,v2,v0),(v12,v2,v5),(v114,v0,v12),(v24,v6,v5)],[0],[]),
([v27,v2,v9,v7,v4,v5,v16],[],[],[(0,34)]),
([v34,v0,v8,v1,v13,v4,v5],[],[],[]),
([v35,v2,v6,v3,v1,v4,v17],[(v6,v0,v2),(v17,v0,v4),(v20,v3,v6),(v35,v20,v5)],[5],[]),
([v35,v0,v2,v8,v1,v4,v15],[(v8,v3,v2),(v15,v3,v4),(v20,v0,v8),(v35,v20,v5)],[5],[]),
([v35,v0,v2,v9,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v20,v2,v9),(v35,v20,v5)],[0,4],[]),
([v55,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v11,v3,v5),(v20,v2,v9),(v55,v20,v11)],[0,4],[]),
([v55,v0,v6,v3,v1,v4,v12],[],[],[(0,9),(1,45)]),
([v0,v2,v9,v1,v4,v11,v26],[(v9,v3,v0),(v11,v3,v5),(v13,v2,v1),(v26,v13,v5)],[5],[(0,46),(2,22)]),
([v28,v0,v6,v3,v1,v4,v12],[(v6,v2,v0),(v12,v2,v5),(v18,v3,v1),(v28,v18,v5)],[0],[(1,47)]),
([v33,v2,v6,v1,v17,v15,v5],[],[],[(1,13),(1,43)]),
([v0,v2,v163,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v12,v2,v5),(v163,v9,v12)],[2,4],[(2,48),(2,49)]),
([v0,v2,v163,v9,v1,v4,v11],[],[],[(3,11)]),
([v0,v2,v163,v1,v4,v12,v11],[],[],[(3,12)]),
([v60,v0,v3,v7,v13,v4,v5],[],[],[(0,13),(3,45)]),
([v25,v2,v3,v9,v7,v4,v5],[],[],[]),
([v72,v0,v8,v1,v13,v4,v5],[],[],[]),
([v60,v0,v3,v1,v13,v4,v5],[(v8,v2,v3),(v13,v2,v1),(v29,v0,v13),(v60,v8,v29)],[1],[]),
([v39,v0,v2,v9,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v41,v2,v11),(v39,v5,v41)],[0,4],[(0,50),(1,15),(1,19)]),
([v60,v88,v2,v9,v1,v4,v5],[(v9,v0,v3),(v7,v0,v1),(v88,v2,v7),(v60,v88,v3)],[3],[(0,0),(1,42)]),
([0xa8a8acaca8a8acac,v0,v2,v8,v1,v4,v5],[],[],[]),
([v42,v0,v8,v1,v13,v4,v5],[],[],[]),
([v31,v0,v2,v9,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v19,v9,v1),(v31,v19,v5)],[0,4],[]),
([v58,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v11,v3,v5),(v19,v9,v1),(v58,v19,v11)],[0,4],[]),
([v63,v0,v6,v3,v1,v4,v12],[(v6,v2,v0),(v12,v2,v5),(v127,v6,v4),(v63,v127,v5)],[1],[(0,25),(1,51)]),
([v33,v2,v9,v1,v7,v4,v5],[],[],[(4,52)]),
([v62,v0,v6,v3,v1,v4,v12],[(v6,v2,v0),(v12,v2,v5),(v29,v6,v1),(v62,v29,v5)],[0],[]),
([v79,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v11,v3,v5),(v46,v9,v4),(v79,v46,v11)],[0,4],[]),
([v0,v2,v9,v1,v4,v148,v11],[(v9,v3,v0),(v11,v3,v5),(v115,v9,v4),(v148,v115,v5)],[0,4,5],[]),
([v0,v130,v2,v8,v1,v15,v5],[],[],[]),
([v0,v2,v9,v1,v188,v4,v11],[],[],[]),
([v0,v2,v9,v4,v10,v11,v16],[(v9,v3,v0),(v11,v3,v5),(v10,v1,v4),(v16,v1,v5)],[5],[(0,53)]),
([v37,v0,v2,v9,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v10,v1,v4),(v37,v10,v5)],[0,4],[(0,54)]),
([v40,v0,v6,v3,v1,v4,v12],[],[],[(0,27)]),
([v0,v2,v185,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v16,v1,v5),(v185,v9,v16)],[1,4],[(0,53),(2,28),(4,55),(5,56)]),
([v0,v2,v185,v9,v1,v4,v11],[],[],[(2,29)]),
([v0,v2,v185,v1,v4,v11,v16],[(v9,v3,v0),(v11,v3,v5),(v16,v1,v5),(v185,v9,v16)],[0],[(2,30)]),
([v101,v0,v2,v1,v15,v10,v5],[],[],[(0,31),(2,51)]),
([v30,v2,v3,v9,v7,v4,v16],[],[],[(0,34),(0,56)]),
([v61,v0,v8,v1,v13,v4,v5],[],[],[]),
([v101,v0,v2,v1,v4,v15,v5],[(v8,v3,v2),(v15,v3,v4),(v59,v1,v15),(v101,v8,v59)],[5],[]),
([v28,v0,v2,v9,v1,v4,v11],[(v9,v3,v0),(v11,v3,v5),(v48,v1,v11),(v28,v5,v48)],[0,4],[(0,35),(0,57)]),
([v57,v2,v9,v1,v7,v4,v5],[(v9,v0,v3),(v7,v0,v1),(v21,v4,v7),(v57,v3,v21)],[3],[]),
([v90,v0,v3,v1,v13,v4,v5],[(v8,v2,v3),(v13,v2,v1),(v26,v5,v13),(v90,v8,v26)],[1],[]),
([v38,v2,v6,v3,v1,v4,v17],[(v6,v0,v2),(v17,v0,v4),(v21,v1,v17),(v38,v5,v21)],[5],[]),
([v25,v0,v6,v3,v1,v4,v12],[],[],[(1,58)]),
([v34,v81,v0,v1,v4,v5],[],[],[]),
([v34,v81,v0,v20,v1,v4,v5],[],[],[(0,59),(0,62),(0,63),(1,61),(2,60),(3,60)]),
([v34,v0,v2,v77,v20,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20),(v77,v20,v1)],[1],[(0,64),(2,61),(2,64)]),
([v35,v64,v2,v3,v20,v1,v4],[(v6,v0,v2),(v20,v6,v3),(v64,v0,v20),(v35,v20,v5)],[1],[(0,60),(1,60)]),
([v34,v0,v2,v113,v20,v1,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20),(v113,v20,v4)],[1],[(0,64),(1,61),(2,62)]),
([v35,v34,v0,v2,v20,v1,v4],[(v8,v3,v2),(v20,v8,v0),(v34,v3,v20),(v35,v20,v5)],[1],[(0,60),(0,63)]),
([v35,v0,v2,v3,v1,v4],[],[],[]),
([v35,v0,v2,v3,v20,v1,v4],[(v8,v2,v3),(v20,v8,v0),(v205,v20,v5),(v35,v205,v20)],[0],[(0,65),(0,66),(1,65),(1,66)]),
([v0,v2,v3,v77,v113,v5],[],[],[]),
([v0,v2,v3,v77,v113,v20,v5],[],[],[(0,64),(0,67),(0,68),(1,64),(2,65),(3,65)]),
([v0,v2,v3,v77,v4,v96,v5],[(v6,v0,v2),(v20,v6,v3),(v77,v20,v1),(v96,v20,v4)],[0],[(0,70),(1,69),(1,72),(2,65),(3,71)]),
([v35,v0,v2,v3,v77,v4],[],[],[]),
([v35,v0,v2,v3,v77,v20,v4],[(v6,v2,v0),(v20,v6,v3),(v77,v20,v1),(v35,v20,v5)],[0],[(0,68),(0,73),(1,66)]),
([v35,v0,v2,v3,v77,v4,v5],[],[],[]),
([v56,v0,v2,v1,v4,v96,v5],[(v9,v3,v0),(v20,v9,v2),(v96,v20,v4),(v56,v3,v96)],[1],[(0,74),(0,76),(1,75),(2,77)]),
([v72,v0,v2,v1,v52,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v52,v20,v1),(v72,v3,v52)],[1],[(0,75),(0,79),(2,75),(2,79),(3,78)]),
([v35,v0,v2,v3,v1,v4,v219],[(v8,v2,v3),(v20,v8,v0),(v219,v20,v5),(v35,v5,v219)],[1],[(0,77),(0,78),(0,80),(0,81),(1,77),(1,80),(1,81)]),
([v0,v2,v3,0xff00fe00ff00fe00,v4,v96,v5],[],[],[(0,76),(0,83),(1,79),(1,84),(2,80),(3,82)]),
([v0,v2,v3,v1,v4,0xfffffffefffffffe,v5],[(v6,v0,v2),(v20,v6,v3),(v52,v20,v1),(0xfffffffefffffffe,v52,v4)],[0],[(0,85),(0,86),(1,85),(2,82),(3,82)]),
([v82,v0,v2,v3,v1,v4],[],[],[]),
([v82,v0,v2,v3,v1,v52,v4],[(v6,v2,v0),(v20,v6,v3),(v52,v20,v1),(v82,v52,v5)],[0],[(0,84),(0,87),(3,81)]),
([v82,v0,v2,v3,v1,v4,v5],[],[],[]),
([v56,v0,v2,v20,v1,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v96,v20,v4),(v56,v3,v96)],[1],[(0,70),(2,77)]),
([v72,v0,v2,v20,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v52,v20,v1),(v72,v3,v52)],[1],[(0,69),(2,69),(3,78)]),
([v35,v0,v2,v3,v1,v52,v4],[(v6,v2,v0),(v20,v6,v3),(v52,v20,v1),(v35,v20,v5)],[5],[(0,89),(1,66),(2,88)]),
([v82,v0,v2,v3,v20,v1,v4],[(v6,v2,v0),(v20,v6,v3),(v52,v20,v1),(v82,v52,v5)],[0,1],[(0,72),(2,89),(3,81)]),
([v35,v0,v2,v3,v1,v258,v4],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5),(v258,v35,v1)],[1],[]),
([0xfefe,v35,v0,v2,v3,v1,v4],[],[],[]),
([v35,v0,v2,v3,v1,v4,v10],[],[],[]),
([v35,v135,v0,v2,v3,v1],[],[],[]),
([v35,v135,v0,v2,v3,v20,v1],[(v8,v3,v2),(v20,v8,v0),(v35,v20,v5),(v135,v20,v4)],[0,5],[(0,73),(0,90)]),
([v35,v135,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,v258,v4,v5],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5),(v258,v35,v1)],[1],[]),
([0xfefe,v0,v2,v3,v1,v4,v5],[],[],[]),
([v35,v0,v2,v3,v1,v4,v16],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5),(v16,v1,v5)],[1],[]),
([v0,v2,v3,0xfefefe00fefefe00,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v10,v1,v4),(0xfefefe00fefefe00,v20,v10)],[1],[]),
([0x101010001010100,v0,v2,v3,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v10,v1,v4),(0x101010001010100,v20,v10)],[0,1,5],[(0,91)]),
([v0,v2,v9,v1,v4,v5,v167],[],[],[]),
([v34,v81,v0,v6,v1,v4,v5],[],[],[]),
([v34,v81,v0,v8,v1,v4,v5],[(v8,v3,v2),(v20,v8,v0),(v34,v3,v20),(v81,v2,v20)],[4],[(0,59)]),
([v34,v0,v2,v9,v77,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20),(v77,v20,v1)],[1,4],[]),
([v35,v64,v2,v6,v3,v1,v4],[(v6,v0,v2),(v20,v6,v3),(v64,v0,v20),(v35,v20,v5)],[1],[(0,60)]),
([v34,v0,v2,v9,v113,v1,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20),(v113,v20,v4)],[1,4],[(1,61)]),
([v35,v34,v0,v2,v8,v1,v4],[(v8,v3,v2),(v20,v8,v0),(v34,v3,v20),(v35,v20,v5)],[1],[(0,60)]),
([v34,v0,v2,v9,v205,v1,v4],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20),(v205,v20,v5)],[1,4],[(0,62)]),
([v35,v34,v0,v2,v9,v1,v4],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20),(v35,v20,v5)],[1,4],[(0,63)]),
([v35,v0,v2,v3,v1,v4,v41],[(v8,v2,v3),(v20,v8,v0),(v41,v8,v5),(v35,v20,v5)],[1,4],[(0,78)]),
([v35,v0,v2,v3,v1,v29,v4],[],[],[]),
([v0,v2,v3,0xfe10fe10fe10fe10,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v195,v6,v1),(0xfe10fe10fe10fe10,v195,v20)],[1],[]),
([v39,v135,v0,v2,v3,v1,v5],[],[],[]),
([v35,v0,v2,v3,v1,v4,v44],[(v6,v2,v0),(v20,v6,v3),(v44,v6,v5),(v35,v20,v5)],[1,3,5],[(0,77),(0,92)]),
([v35,v0,v2,v3,v1,v54,v4],[(v8,v2,v3),(v20,v8,v0),(v54,v8,v1),(v35,v20,v5)],[5],[(0,93)]),
([v35,v0,v2,v3,v1,v19,v4],[(v9,v0,v3),(v20,v9,v2),(v19,v9,v1),(v35,v20,v5)],[2],[(0,94)]),
([v31,v0,v2,v3,v20,v1,v4],[(v9,v0,v3),(v20,v9,v2),(v19,v9,v1),(v31,v19,v5)],[1,5],[(2,93),(3,92),(5,95)]),
([v0,v2,v3,0xfe02fe02fe02fe02,v1,v4,v5],[(v8,v2,v3),(v20,v8,v0),(v196,v8,v1),(0xfe02fe02fe02fe02,v196,v20)],[1],[]),
([v24,0xfe00fe00fe00fe,v0,v2,v3,v4,v5],[],[],[]),
([v24,v135,v0,v2,v3,v1,v5],[],[],[]),
([v35,v0,v2,v3,v8,v1,v4],[],[],[]),
([v0,v2,v6,v3,v77,v113,v5],[(v6,v0,v2),(v20,v6,v3),(v77,v20,v1),(v113,v20,v4)],[3],[(0,64)]),
([v35,v0,v2,v6,v3,v77,v4],[],[],[]),
([v56,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v96,v20,v4),(v56,v3,v96)],[1,4],[]),
([v112,v0,v2,v3,v1,v4,v5],[],[],[]),
([v82,v0,v2,v6,v3,v1,v4],[],[],[]),
([v35,v0,v2,v3,v8,v77,v4],[],[],[]),
([v35,v135,v0,v2,v3,v9,v1],[(v9,v3,v0),(v20,v9,v2),(v135,v20,v4),(v35,v20,v5)],[4],[]),
([v35,v0,v2,v6,v3,v1,v4],[],[],[]),
([v0,v2,v6,v3,v113,v205,v1],[],[],[]),
([v35,v0,v2,v6,v3,v113,v1],[],[],[]),
([v56,v0,v2,v8,v1,v4,v5],[(v8,v3,v2),(v20,v8,v0),(v96,v20,v4),(v56,v3,v96)],[1],[]),
([v72,v0,v2,v9,v1,v4,v5],[(v9,v0,v3),(v20,v9,v2),(v52,v20,v1),(v72,v3,v52)],[1,4],[]),
([v60,v0,v2,v3,v1,v4,v5],[],[],[]),
([v82,v0,v2,v3,v8,v1,v4],[],[],[]),
([v82,v0,v2,v3,v9,v1,v4],[(v9,v0,v3),(v20,v9,v2),(v52,v20,v1),(v82,v52,v5)],[4],[]),
([v55,v35,v0,v2,v9,v1,v4],[(v9,v3,v0),(v20,v9,v2),(v35,v20,v5),(v55,v35,v3)],[0,4],[]),
([v35,v135,v0,v2,v6,v3,v1],[],[],[]),
([v97,v0,v2,v3,v1,v4,v220],[(v8,v2,v3),(v64,v8,v0),(v220,v64,v5),(v97,v5,v220)],[1],[(4,96)]),
([v0,v2,v3,v1,v4,0xffffff0effffff0e,v5],[(v6,v0,v2),(v34,v6,v3),(v165,v34,v1),(0xffffff0effffff0e,v165,v4)],[0],[(0,85),(0,97)]),
([0xff0eff0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([v97,v137,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v97,v64,v5),(v137,v97,v0)],[1],[(4,96)]),
([v0,v2,v3,v1,0xff00ff00ff54ff54,v4,v5],[],[],[]),
([0x3232,v0,v2,v3,v1,v4,v5],[],[],[]),
([v34,v0,v2,v238,v1,v4,v5],[(v6,v0,v2),(v34,v6,v3),(v197,v34,v1),(v238,v197,v3)],[1],[(0,96)]),
([v55,v0,v2,v3,v1,v4,v167],[(v6,v2,v0),(v34,v6,v3),(v167,v34,v5),(v55,v5,v167)],[1],[(0,98),(0,99)]),
([0xff54ff54,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,0xff005400ff005400,v4,0xffff5454ffff5454,v5],[],[],[(3,100),(4,99)]),
([v0,v2,v3,v1,v4,0xffffff54ffffff54,v5],[],[],[(2,100),(3,100)]),
([v187,v0,v2,v3,v1,v4],[],[],[]),
([v187,v0,v2,v3,v1,v173,v4],[(v9,v0,v3),(v81,v9,v2),(v173,v81,v1),(v187,v173,v5)],[0],[]),
([v187,v0,v2,v3,v1,v4,v5],[],[],[]),
([v187,v81,v0,v2,v3,v1,v4],[],[],[]),
([v55,v0,v2,v166,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5),(v166,v55,v3)],[1],[(0,98)]),
([v0,v2,v3,v1,0xff00ff00ff0eff0e,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff00ff00ff32ff32,v4,v5],[(v9,v3,v0),(v81,v9,v2),(0x32323232,v81,v5),(0xff00ff00ff32ff32,0x32323232,v1)],[1],[]),
([0xe0e,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5),(0xe0e,v55,v4)],[1],[(3,101)]),
([v55,v0,v2,v3,v1,v4,v16],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5),(v16,v1,v5)],[1,3],[]),
([v34,v0,v2,v166,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5),(v166,v55,v3)],[1],[(0,98),(3,102)]),
([0xe0e0e000e0e0e00,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xababababab00ab00,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v16,v5,v1),(0xababababab00ab00,v64,v16)],[0],[]),
([v34,v36,v0,v2,v1,v4,v5],[],[],[(0,85)]),
([0xe0e0e0e0e0e0000,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xababab00ababab00,v2,v3,v1,v4,v5],[],[],[]),
([0xf0f02020f0f0202,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v81,v9,v2),(0xffff3232ffff3232,v81,v4),(0xf0f02020f0f0202,v3,0xffff3232ffff3232)],[4],[(2,103)]),
([v39,v0,v2,v3,v1,v4,v220],[(v8,v2,v3),(v64,v8,v0),(v220,v64,v5),(v39,v8,v5)],[1],[(0,103),(1,103),(4,96)]),
([v0,v2,v174,v3,v1,v4,v5],[(v6,v0,v2),(v34,v6,v3),(v197,v34,v1),(v174,v197,v6)],[3],[]),
([v97,v0,v2,v3,v1,v4,v41],[(v8,v2,v3),(v64,v8,v0),(v97,v64,v5),(v41,v8,v5)],[4],[]),
([0xf0f04040f0f0404,v0,v2,v8,v1,v4,v5],[(v8,v3,v2),(v64,v8,v0),(0xffff5454ffff5454,v64,v4),(0xf0f04040f0f0404,v3,0xffff5454ffff5454)],[4],[(0,7),(4,104)]),
([0xf020f020f020f02,v0,v2,v9,v1,v4,v5],[(v9,v0,v3),(v81,v9,v2),(v173,v81,v1),(0xf020f020f020f02,v3,v173)],[4],[(3,105)]),
([v24,v0,v2,v3,v1,v4,v167],[(v6,v2,v0),(v34,v6,v3),(v167,v34,v5),(v24,v6,v5)],[1,5],[(0,98),(0,104),(0,105)]),
([v187,v0,v2,v3,v9,v1,v4],[(v9,v0,v3),(v81,v9,v2),(v173,v81,v1),(v187,v173,v5)],[4],[]),
([v0,v2,v86,v3,v1,v4,v5],[(v6,v0,v2),(v34,v6,v3),(0xe0e00000e0e,v34,v4),(v86,0xe0e00000e0e,v6)],[2,3],[(4,45)]),
([v55,v0,v2,v3,v1,v4,v44],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5),(v44,v6,v5)],[3,5],[]),
([v0,0xababababa8a8a8a8,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v41,v8,v5),(0xababababa8a8a8a8,v64,v41)],[1,4,5],[(2,106),(2,107),(3,107)]),
([v0,0xaba8aba8aba8aba8,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v54,v8,v1),(0xaba8aba8aba8aba8,v64,v54)],[4],[]),
([v31,v81,v0,v2,v3,v1,v4],[],[],[]),
([v0,v138,v2,v1,v4,v5,v41],[],[],[]),
([v33,v118,v2,v1,v4,v5],[(v9,v3,v0),(v46,v9,v4),(v33,v3,v46),(v118,v0,v46)],[5],[(0,108)]),
([v33,v118,v2,v1,v4,v46,v5],[],[],[(2,109)]),
([v33,v0,v2,v1,v22,v46,v5],[],[],[(0,108)]),
([v39,v71,v0,v2,v1,v4],[(v8,v3,v2),(v41,v8,v5),(v71,v3,v41),(v39,v5,v41)],[2],[(0,19)]),
([v39,v71,v0,v2,v1,v4,v41],[],[],[(0,109)]),
([v72,v0,v2,v29,v18,v4,v5],[],[],[]),
([v56,v0,v2,v1,v4,v46,v5],[(v9,v3,v0),(v46,v9,v4),(v96,v2,v46),(v56,v3,v96)],[1],[(1,75)]),
([v82,v0,v2,v3,v1,v29,v4],[],[],[]),
([v0,v2,v3,v1,0xff33ff32ff33ff32,v4,v5],[(v9,v0,v3),(v46,v9,v4),(0x3333323233333232,v2,v46),(0xff33ff32ff33ff32,0x3333323233333232,v1)],[0,1],[(0,110)]),
([0xf0e0f0e,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v29,v6,v1),(v72,v3,v29),(0xf0e0f0e,v72,v5)],[0],[]),
([v0,v2,v3,v1,v4,v12,v103],[(v9,v3,v0),(v46,v9,v4),(v12,v2,v5),(v103,v5,v46)],[1,2],[]),
([v0,v2,v3,v1,0xffaaffaafca8fca8,v4,v5],[(v8,v2,v3),(v41,v8,v5),(v7,v0,v1),(0xffaaffaafca8fca8,v7,v41)],[1,4],[(2,16)]),
([0x3020302,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v137,v2,v3,v1,v4,v41],[(v8,v2,v3),(v41,v8,v5),(v39,v5,v41),(v137,v39,v0)],[0,4],[]),
([v75,v0,v2,v1,v4,v5,v103],[(v9,v3,v0),(v46,v9,v4),(v103,v46,v5),(v75,v3,v103)],[1],[(1,113),(4,112),(5,111)]),
([v57,v0,v2,v1,v4,v91,v5],[(v9,v0,v3),(v46,v9,v4),(v91,v46,v1),(v57,v3,v91)],[1],[(0,111),(0,114),(2,116),(3,115)]),
([0xaaaaaaaaaaa8aaa8,v2,v3,v1,v4,v5,v104],[],[],[(0,118),(0,120),(2,114),(4,85),(4,119),(5,117)]),
([v83,v0,v2,v1,v4,v5],[],[],[]),
([v83,v0,v2,v3,v1,v4,v5],[],[],[]),
([v83,v0,v2,v1,v4,v53,v5],[(v6,v0,v2),(v29,v6,v1),(v53,v29,v4),(v83,v3,v53)],[3],[(0,121),(0,122)]),
([v68,v0,v2,v3,v1,v4,v104],[(v8,v2,v3),(v41,v8,v5),(v104,v41,v1),(v68,v5,v104)],[1],[(0,112),(0,116),(0,120),(5,123)]),
([v62,v0,v2,v3,v1,v4,v124],[(v6,v2,v0),(v29,v6,v1),(v124,v29,v5),(v62,v5,v124)],[1],[(0,113),(0,115),(0,117),(0,123),(0,124)]),
([v0,v2,v3,0xff00ff00ff00fa00,v4,v5,v103],[],[],[(1,124),(3,121),(3,125),(4,118)]),
([v0,v2,v3,v1,v4,v5,0xffffffffffffffee],[(v6,v0,v2),(v29,v6,v1),(v53,v29,v4),(0xffffffffffffffee,v53,v5)],[3],[(0,125),(0,126),(2,125)]),
([v89,v0,v2,v3,v1,v4],[],[],[]),
([v89,v0,v2,v3,v1,v4,v53],[(v6,v0,v2),(v29,v6,v1),(v53,v29,v4),(v89,v53,v5)],[0],[(0,119),(0,122)]),
([v89,v0,v2,v3,v1,v4,v5],[],[],[]),
([v75,v0,v2,v1,v4,v46,v5],[(v9,v3,v0),(v46,v9,v4),(v103,v46,v5),(v75,v3,v103)],[1],[(1,113)]),
([v57,v0,v2,v1,v4,v46,v5],[(v9,v0,v3),(v46,v9,v4),(v91,v46,v1),(v57,v3,v91)],[1],[(3,115)]),
([v83,v0,v2,v1,v29,v4,v5],[],[],[]),
([v68,v0,v2,v3,v1,v4,v41],[(v8,v2,v3),(v41,v8,v5),(v104,v41,v1),(v68,v5,v104)],[1],[(5,123)]),
([v89,v0,v2,v3,v1,v29,v4],[],[],[]),
([v0,0xaaaaffffaaaafefe,v2,v3,v1,v4,v5],[(v8,v3,v2),(v41,v8,v5),(0xffff0000fcfc,v41,v4),(0xaaaaffffaaaafefe,0xffff0000fcfc,v0)],[4],[]),
([v0,v2,v3,v1,0xff00ff00fffffffa,v4,v5],[(v9,v3,v0),(v46,v9,v4),(0xfffffafa,v46,v5),(0xff00ff00fffffffa,0xfffffafa,v1)],[1],[]),
([0xffee,v0,v2,v3,v1,v4,v5],[],[],[(3,127)]),
([v37,v0,v2,v3,v1,v4,v41],[],[],[(0,127)]),
([v0,v2,v3,v1,0xffeeffeeffee0000,v4,v5],[],[],[]),
([0x3030300,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v138,v2,v8,v1,v4,v5],[],[],[]),
([v0,v2,v9,v1,v4,v5,v143],[],[],[]),
([v33,v0,v2,v9,v1,v22,v5],[],[],[]),
([v39,v71,v0,v2,v8,v1,v4],[],[],[]),
([v33,v118,v2,v9,v1,v4,v5],[(v9,v3,v0),(v46,v9,v4),(v33,v3,v46),(v118,v0,v46)],[4,5],[(2,109)]),
([v62,v0,v2,v3,v1,v4,v44],[(v6,v2,v0),(v29,v6,v1),(v44,v6,v5),(v62,v29,v5)],[1,5],[(0,123)]),
([v31,v0,v2,v3,v1,v4,v46],[],[],[]),
([v0,v2,v3,v1,0xff03ff03fc00fc00,v4,v5],[(v8,v2,v3),(v41,v8,v5),(v196,v8,v1),(0xff03ff03fc00fc00,v196,v41)],[0],[]),
([v24,v0,v2,v3,v1,v4,v124],[(v6,v2,v0),(v29,v6,v1),(v24,v6,v5),(v124,v29,v5)],[1,3,5],[(0,128),(0,129)]),
([v0,v2,v174,v3,v29,v4,v5],[],[],[(3,130)]),
([v75,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v46,v9,v4),(v103,v46,v5),(v75,v3,v103)],[1,4],[(1,129)]),
([v57,v0,v2,v9,v1,v4,v5],[(v9,v0,v3),(v46,v9,v4),(v91,v46,v1),(v57,v3,v91)],[1,4],[(3,128)]),
([v90,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v41,v8,v5),(v104,v41,v1),(v90,v8,v104)],[0],[]),
([v83,v0,v2,v6,v1,v4,v5],[],[],[]),
([v89,v0,v2,v6,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,0xffaaffaafffefffe,v4,v5],[],[],[(0,82)]),
([0xccccfefe,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,v148,v12],[(v9,v3,v0),(v115,v9,v4),(v148,v115,v5),(v12,v2,v5)],[2],[(4,131)]),
([0xf0f000e0f0f000e,v0,v2,v3,v1,v4,v5],[],[],[]),
([v108,v0,v2,v3,v1,v4,v148],[(v9,v3,v0),(v115,v9,v4),(v148,v115,v5),(v108,v5,v148)],[1],[(0,132)]),
([v0,v2,v3,v1,v4,0xffffff00fffffffc,v5],[],[],[]),
([0xff00fffa,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xaaaaaaaaaaaafefe,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff00ff00ff00fffa,v4,v5],[],[],[]),
([0xee,v0,v2,v3,v1,v4,v5],[],[],[(3,127)]),
([v108,v0,v2,v3,v1,v239,v5],[(v9,v3,v0),(v115,v9,v4),(v108,v115,v5),(v239,v108,v4)],[1],[(0,132)]),
([v39,v0,v2,v3,v1,v4,v228],[(v8,v3,v2),(v39,v8,v5),(0xfcfc,v39,v4),(v228,0xfcfc,v5)],[1],[(0,133),(2,132)]),
([0xfca8fca8,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v7,v0,v1),(0xfca8fca8,v39,v7)],[3,4],[]),
([v0,v2,v3,v1,0xff11f010ff11f010,v4,v5],[],[],[]),
([v39,v30,v0,v2,v3,v1,v4],[],[],[(0,82),(0,131),(1,134)]),
([0xfcfcfc00,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff11ff11ff110000,v4,v5],[],[],[]),
([v24,v0,v2,v3,v1,v4,0xffffffff00ee00ee],[(v6,v2,v0),(v195,v6,v1),(0xffffffff00ee00ee,v195,v5),(v24,v6,v5)],[1],[(1,132)]),
([v0,v2,v229,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff11ee00ff11ee00,v4,v5],[],[],[]),
([v39,v186,v0,v2,v3,v1,v5],[],[],[]),
([v42,v0,v2,v1,v17,v45,v5],[],[],[(3,135)]),
([v27,v66,v2,v1,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v66,v0,v19),(v27,v3,v19)],[1],[(0,135)]),
([v27,v66,v2,v1,v19,v4,v5],[],[],[(0,137),(0,138),(3,136)]),
([v42,v0,v2,v102,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v42,v3,v45),(v102,v1,v45)],[1],[(4,139)]),
([v31,v66,v2,v3,v1,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v66,v0,v19),(v31,v5,v19)],[1],[(0,138),(3,140)]),
([v24,v95,v0,v3,v1,v4],[],[],[]),
([v24,v95,v0,v3,v1,v4,v44],[],[],[(0,136),(0,139),(0,140)]),
([v27,v0,v2,v13,v19,v4,v5],[],[],[(0,135)]),
([v56,v0,v2,v1,v49,v15,v5],[(v6,v0,v2),(v49,v6,v4),(v15,v3,v4),(v56,v3,v49)],[3],[(0,141)]),
([v0,v2,v3,v102,v17,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v17,v0,v4),(v102,v1,v45)],[4],[(4,142),(5,141)]),
([v31,v0,v2,v3,v13,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v13,v2,v1),(v31,v5,v19)],[0,2],[]),
([v68,v0,v2,v3,v7,v4,v5],[],[],[]),
([v56,v0,v2,v1,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v96,v0,v45),(v56,v3,v96)],[1],[(0,74),(0,143)]),
([v72,v0,v2,v1,v19,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v52,v2,v19),(v72,v3,v52)],[1],[(0,75),(0,144)]),
([v0,v2,v3,v102,v4,v96,v5],[(v8,v3,v2),(v45,v8,v4),(v96,v0,v45),(v102,v45,v1)],[0],[(0,143),(1,147),(2,146),(3,144),(5,145)]),
([v31,v0,v2,v3,v1,v52,v4],[(v9,v0,v3),(v19,v9,v1),(v52,v2,v19),(v31,v19,v5)],[5],[(0,149),(3,92),(4,148)]),
([v82,v0,v2,v3,v1,v54,v4],[],[],[(0,147),(2,149)]),
([v82,v0,v2,v3,v1,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v52,v2,v19),(v82,v52,v5)],[0,2],[]),
([v0,v2,v3,v1,0xff0fff0eff0fff0e,v4,v5],[(v6,v0,v2),(v49,v6,v4),(v56,v3,v49),(0xff0fff0eff0fff0e,v56,v1)],[1],[]),
([0x55545554,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v54,v8,v1),(0x5554555455545554,v0,v54),(0x55545554,0x5554555455545554,v5)],[0],[]),
([v0,v2,v3,v1,0xff33ff33ff32ff32,v4,v5],[(v9,v3,v0),(v70,v9,v5),(0x3333333332323232,v2,v70),(0xff33ff33ff32ff32,0x3333333332323232,v1)],[0],[(0,100)]),
([0xf0f0e0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([v56,v0,v2,v3,v1,v4,v255],[(v6,v0,v2),(v49,v6,v4),(v56,v3,v49),(v255,v49,v5)],[5],[(0,141),(2,142)]),
([v31,0x3332333233323332,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,0xfff0eee0fff0eee0,v4,v5],[],[],[]),
([0x5050404,v0,v2,v3,v1,v4,v5],[(v9,v3,v0),(v70,v9,v5),(v22,v2,v4),(0x5050404,v22,v70)],[1],[(3,150)]),
([v31,v0,v2,v3,v1,v4,v22],[(v9,v0,v3),(v19,v9,v1),(v22,v2,v4),(v31,v19,v5)],[5],[]),
([v31,v0,v2,v3,v1,v4,v12],[(v9,v0,v3),(v19,v9,v1),(v12,v2,v5),(v31,v5,v19)],[2],[]),
([v0,v2,v3,v1,0xffaafca8ffaafca8,v4,v5],[(v8,v3,v2),(v45,v8,v4),(v7,v0,v1),(0xffaafca8ffaafca8,v7,v45)],[1],[]),
([0x5040504,v0,v2,v3,v1,v4,v5],[(v9,v3,v0),(v70,v9,v5),(v13,v2,v1),(0x5040504,v13,v70)],[1,2],[]),
([v24,v114,v2,v3,v1,v4],[],[],[]),
([v24,v114,v2,v3,v1,v4,v44],[],[],[(0,136),(0,151),(0,152)]),
([v27,v0,v2,v1,v126,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19),(v126,v19,v5)],[1],[(0,137),(3,151)]),
([v31,v27,v0,v2,v1,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19),(v31,v19,v5)],[1],[(0,138),(3,152)]),
([v0,v130,v2,v3,v1,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v155,v4,v45),(v130,v155,v0)],[4,5],[(0,153)]),
([v24,0xff00ff00ee00ee,v0,v2,v3,v1,v4],[],[],[]),
([v24,v0,v2,v3,v1,v122],[],[],[(0,142),(3,153)]),
([v24,v0,v2,v3,v1,v122,v44],[(v6,v2,v0),(v44,v6,v5),(v24,v5,v44),(v122,v4,v44)],[1],[(0,139),(0,151)]),
([v24,v164,v0,v2,v3,v1,v44],[(v6,v2,v0),(v44,v6,v5),(v24,v5,v44),(v164,v4,v44)],[1,5],[(0,140),(0,152)]),
([v75,v0,v2,v1,v4,v5,v70],[(v9,v3,v0),(v70,v9,v5),(v103,v70,v4),(v75,v3,v103)],[1],[(1,129),(4,112)]),
([v83,v0,v2,v1,v4,v49,v5],[],[],[(0,154),(1,155)]),
([v57,v0,v2,v1,v19,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v91,v19,v4),(v57,v3,v91)],[1],[(2,116),(3,128)]),
([v0,v2,v3,v102,v4,v5,0xfffffffffffffcfc],[(v8,v3,v2),(v45,v8,v4),(0xfffffffffffffcfc,v45,v5),(v102,v45,v1)],[4],[(4,157),(5,154),(5,156)]),
([v31,v0,v2,v3,v1,v4,v91],[(v9,v0,v3),(v19,v9,v1),(v91,v19,v4),(v31,v19,v5)],[2],[(0,155),(3,158)]),
([v89,v0,v2,v3,v1,v4,v49],[(v6,v0,v2),(v49,v6,v4),(v53,v49,v1),(v89,v53,v5)],[0,1],[]),
([v0,0xaaaaaaaafffefffe,v2,v3,v1,v4,v5],[(v8,v2,v3),(v54,v8,v1),(v68,v54,v5),(0xaaaaaaaafffefffe,v68,v0)],[4],[]),
([v0,v2,v3,v1,0xff00ff00fffffffc,v4,v5],[],[],[]),
([0xfffa,v0,v2,v3,v1,v4,v5],[],[],[]),
([v68,v0,v2,v3,v1,0xfffc0000fffc0000,v5],[],[],[]),
([v31,0xfffa0000fffa,v0,v2,v3,v1,v4],[],[],[]),
([v31,v0,v2,v3,v1,v4],[],[],[]),
([v31,v0,v2,v3,v1,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v126,v19,v5),(v31,v126,v19)],[1],[]),
([0xf0f0f0f0f0f0e0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([v61,v0,v2,v1,v4,v92,v5],[(v8,v3,v2),(v45,v8,v4),(v92,v45,v1),(v61,v3,v92)],[1],[(0,159),(2,161),(3,160)]),
([v31,v0,v2,v3,v1,v4,v116],[(v9,v3,v0),(v70,v9,v5),(v116,v70,v1),(v31,v5,v116)],[1],[(0,160),(0,161),(0,162)]),
([0xfffffffc,v0,v2,v3,v1,v4,v5],[],[],[]),
([v61,v0,v2,v1,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v92,v45,v1),(v61,v3,v92)],[1],[(3,160)]),
([v61,v0,v2,v1,v54,v4,v5],[(v8,v2,v3),(v54,v8,v1),(v92,v54,v4),(v61,v3,v92)],[1],[(2,161)]),
([v31,v0,v2,v3,v1,v4,v70],[(v9,v3,v0),(v70,v9,v5),(v116,v70,v1),(v31,v5,v116)],[1],[(0,162)]),
([v31,v0,v2,0xccccccccfffefffe,v3,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5),(0xccccccccfffefffe,v31,v2)],[2],[]),
([0xf0f0e0e,v198,v0,v2,v3,v1,v4],[(v6,v0,v2),(v49,v6,v4),(v198,v49,v5),(0xf0f0e0e,v198,v3)],[3],[]),
([v31,v0,v2,v3,v1,v4,0xffff0000fffffffa],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5),(0xffff0000fffffffa,v31,v4)],[5],[]),
([0xfffa,v31,v0,v2,v3,v1,v4],[],[],[]),
([v0,0xaaaafffeaaaafffe,v2,v3,v1,v4,v5],[(v8,v2,v3),(v54,v8,v1),(v186,v54,v4),(0xaaaafffeaaaafffe,v186,v0)],[4],[]),
([v0,v2,v3,v1,0xff00ff00ffffffee,v4,v5],[(v6,v0,v2),(v49,v6,v4),(v198,v49,v5),(0xff00ff00ffffffee,v198,v1)],[1],[]),
([v31,v0,v2,v3,v1,v4,v14],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5),(v14,v4,v5)],[5],[]),
([v0,v2,v3,v1,0xfffafffafffa0000,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v14,v4,v5),(0xfffafffafffa0000,v19,v14)],[5],[]),
([0x5050500,v0,v2,v3,v1,v4,v5],[(v9,v3,v0),(v70,v9,v5),(v10,v4,v1),(0x5050500,v70,v10)],[1,5],[]),
([v0,v221,v2,v8,v1,v4,v5],[],[],[]),
([v42,v0,v2,v8,v1,v17,v5],[],[],[(0,17)]),
([v24,v95,v0,v6,v3,v1,v4],[],[],[]),
([v27,v66,v2,v9,v1,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v66,v0,v19),(v27,v3,v19)],[1,4],[(3,136)]),
([v42,v0,v2,v8,v102,v4,v5],[(v8,v3,v2),(v45,v8,v4),(v42,v3,v45),(v102,v1,v45)],[1],[(4,139)]),
([v31,v66,v2,v3,v9,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v66,v0,v19),(v31,v5,v19)],[1,4],[(3,140)]),
([v0,v227,v2,v8,v1,v4,v5],[],[],[]),
([v0,v2,v9,v1,v4,v5,v144],[],[],[]),
([v27,v0,v2,v9,v13,v4,v5],[],[],[]),
([v24,v114,v2,v6,v3,v1,v4],[],[],[]),
([v27,v0,v2,v9,v1,v126,v4],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19),(v126,v19,v5)],[1,4],[(3,151)]),
([v31,v27,v0,v2,v9,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19),(v31,v19,v5)],[1,4],[(3,152)]),
([v0,v2,v3,v1,0xff03fc00ff03fc00,v4,v5],[(v8,v3,v2),(v45,v8,v4),(v196,v8,v1),(0xff03fc00ff03fc00,v196,v45)],[1],[]),
([v0,v2,v86,v3,v1,v49,v5],[(v6,v0,v2),(v49,v6,v4),(v15,v3,v4),(v86,v6,v15)],[0],[(0,18),(5,163)]),
([v31,v0,v2,v3,v9,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v126,v19,v5),(v31,v126,v19)],[4],[]),
([v24,v0,v2,v6,v3,v1,v122],[(v6,v2,v0),(v44,v6,v5),(v122,v44,v4),(v24,v5,v44)],[0],[]),
([v61,v0,v2,v8,v1,v4,v5],[(v8,v3,v2),(v45,v8,v4),(v92,v45,v1),(v61,v3,v92)],[1],[]),
([v101,v0,v2,v3,v1,v4,v5],[],[],[]),
([v58,v31,v0,v2,v9,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5),(v58,v31,v3)],[0,4],[]),
([v0,v2,v3,v1,0xffaafffeffaafffe,v4,v5],[],[],[(2,82)]),
([0xccfeccfe,v0,v2,v3,v1,v4,v5],[(v9,v0,v3),(0xfa00fa00fa00fa,v9,v1),(0xccfeccfeccfeccfe,0xfa00fa00fa00fa,v2),(0xccfeccfe,0xccfeccfeccfeccfe,v5)],[1],[]),
([v0,v2,v3,v1,0xfff0fff0fffefffe,v4,v5],[],[],[(0,82)]),
([0xaaaafefe,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v130,v2,v3,v1,v5,v14],[],[],[]),
([v0,v2,v3,v1,v4,v228,v23],[(v8,v3,v2),(v155,v8,v4),(v228,v155,v5),(v23,v0,v5)],[4],[(4,164)]),
([0xf000f000f0e0f0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffff00ffffffee,v5],[],[],[(0,125)]),
([0xff00ffee,v0,v2,v3,v1,v4,v5],[(v6,v0,v2),(v127,v6,v4),(0xff00ffeeff00ffee,v127,v1),(0xff00ffee,0xff00ffeeff00ffee,v5)],[0],[]),
([v24,v0,v2,v3,v168,v4,v16],[(v6,v2,v0),(v24,v6,v5),(v168,v24,v1),(v16,v1,v5)],[1],[]),
([v0,v2,v3,v1,v4,v150,v11],[(v6,v0,v2),(v127,v6,v4),(v150,v127,v5),(v11,v3,v5)],[3],[(4,165)]),
([0xf0f00000f0f0e0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([v63,v0,v2,v3,v1,v4,v150],[(v6,v0,v2),(v127,v6,v4),(v150,v127,v5),(v63,v5,v150)],[1],[(0,166)]),
([0xff00fffc,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v188,v4,v14],[],[],[]),
([v0,0xaaaaaafeaaaaaafe,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,0xffffffff000000fc],[],[],[]),
([v63,v0,v2,v3,v249,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v63,v24,v4),(v249,v63,v1)],[1],[]),
([v0,v2,v3,v1,v249,v4,v5],[],[],[]),
([v63,v0,v2,v3,0xff00ff00ff001100,v4,v5],[],[],[(3,127)]),
([v63,v0,v2,v3,v1,v4,v16],[(v6,v0,v2),(v127,v6,v4),(v63,v127,v5),(v16,v1,v5)],[1],[(0,167)]),
([v24,v0,v2,v3,v249,v4,v5],[],[],[]),
([v24,v0,v2,v3,v1,v4,v150],[(v6,v2,v0),(v24,v6,v5),(v63,v24,v4),(v150,v63,v5)],[1],[(0,166),(0,168)]),
([0xeee0eee0,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v18,v3,v1),(0xeee0eee0,v24,v18)],[3],[]),
([v0,v2,v3,v1,0xff03ff03aa02aa02,v4,v5],[],[],[]),
([v24,v28,v0,v2,v3,v1,v4],[],[],[(0,82),(0,164)]),
([0xeeeee0e0,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v15,v3,v4),(0xeeeee0e0,v24,v15)],[2,3],[]),
([v0,v2,v3,v1,0xff03aa02ff03aa02,v4,v5],[],[],[]),
([v24,0xfffff0f0,v0,v2,v3,v1,v4],[],[],[(0,169),(1,82),(1,165)]),
([0xeeeeee00,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff03ff03ff030000,v4,v5],[(v8,v2,v3),(v196,v8,v1),(v14,v5,v4),(0xff03ff03ff030000,v196,v14)],[0],[(1,170)]),
([v24,v0,v2,v3,v4,v10,v16],[(v6,v2,v0),(v24,v6,v5),(v10,v1,v4),(v16,v1,v5)],[5],[(0,167),(3,170)]),
([v24,v37,v0,v2,v3,v1,v4],[],[],[(0,125)]),
([0xa0a0e0e0a0a0e0e,v0,v2,v8,v1,v4,v5],[(v8,v3,v2),(v155,v8,v4),(v130,v155,v0),(0xa0a0e0e0a0a0e0e,v130,v3)],[5],[(0,102)]),
([0xf0f00000f0f0a0a,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v175,v9,v5),(v239,v175,v4),(0xf0f00000f0f0a0a,v3,v239)],[0,4],[(2,133)]),
([0xf000f000f0a0f0a,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v175,v9,v5),(v188,v175,v1),(0xf000f000f0a0f0a,v3,v188)],[0,4],[(3,168)]),
([v0,v2,v151,v3,v1,v4,v5],[],[],[(1,51),(4,51)]),
([v0,v2,v6,v3,v249,v4,v5],[],[],[]),
([v24,0x1111111111001100,v0,v2,v3,v1,v4],[],[],[(3,171)]),
([v0,v2,v3,v1,0xfffaffc8fffaffc8,v4,v5],[],[],[]),
([v97,v0,v2,v3,v1,v4,v5],[],[],[]),
([v72,v0,v2,v1,v18,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v52,v6,v18),(v72,v3,v52)],[1],[]),
([v35,v0,v2,v3,v1,v4,v23],[(v8,v2,v3),(v23,v0,v5),(v219,v8,v23),(v35,v5,v219)],[0,1],[]),
([v82,v0,v2,v3,v1,v18,v4],[],[],[]),
([v0,v2,v238,v1,v18,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v197,v6,v18),(v238,v197,v3)],[1,3],[]),
([v0,v2,v3,v1,v4,v220,v23],[(v8,v2,v3),(v23,v0,v5),(v97,v8,v23),(v220,v97,v5)],[0,1],[]),
([v0,v2,v3,v1,v52,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v197,v6,v18),(v52,v197,v18)],[0,3,5],[(0,82),(2,82)]),
([v112,v0,v2,v206,v1,v4,v5],[(v8,v3,v2),(v23,v0,v5),(v112,v8,v23),(v206,v112,v3)],[1],[(0,172)]),
([v0,v2,v3,v1,0xff03ff03ff02ff02,v4,v5],[],[],[]),
([v0,v2,v206,v8,v1,v4,v5],[(v8,v3,v2),(v23,v0,v5),(v112,v8,v23),(v206,v112,v3)],[1],[]),
([v0,v2,0xeeeeeee0eeeeeee0,v3,v1,v4,v5],[],[],[]),
([0x303030303020302,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,0xeeeeeeeefffefffe,v3,v1,v4,v5],[],[],[(0,82)]),
([v0,v2,0xeeee000eeeee000e,v3,v1,v4,v5],[],[],[(4,47)]),
([v33,v2,v6,v1,v4,v15,v5],[],[],[]),
([v0,v2,v163,v1,v4,v5,v41],[],[],[(0,174),(2,173),(3,14)]),
([v39,v0,v2,v9,v1,v4,v12],[],[],[(0,15),(0,174)]),
([v0,v2,v3,v1,0xffeeffe0ffeeffe0,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfffafffaffc8ffc8,v4,v5],[(v9,v3,v0),(v12,v2,v5),(v163,v9,v12),(0xfffafffaffc8ffc8,v163,v1)],[0,1],[]),
([v0,v2,v86,v3,v1,v10,v5],[(v6,v0,v2),(v15,v3,v4),(v86,v6,v15),(v10,v1,v4)],[3],[]),
([v55,v0,v2,v3,v1,v4,v5],[],[],[]),
([v56,v0,v2,v1,v4,v15,v5],[(v6,v0,v2),(v15,v3,v4),(v96,v6,v15),(v56,v3,v96)],[1,5],[]),
([v35,v0,v2,v3,v1,v4,v12],[(v9,v3,v0),(v12,v2,v5),(v219,v9,v12),(v35,v5,v219)],[0,1],[]),
([v82,v0,v2,v3,v1,v13,v4],[(v9,v0,v3),(v13,v2,v1),(v52,v9,v13),(v82,v52,v5)],[1],[]),
([v82,v0,v2,v3,v1,v7,v4],[(v8,v2,v3),(v7,v0,v1),(v52,v8,v7),(v82,v52,v5)],[1],[]),
([v0,v2,v166,v1,v4,v5,v11],[(v6,v2,v0),(v11,v3,v5),(v55,v6,v11),(v166,v55,v3)],[0,1,3],[]),
([v0,v2,v3,v1,v4,v167,v11],[(v6,v2,v0),(v11,v3,v5),(v55,v6,v11),(v167,v55,v5)],[0,1,5],[]),
([v60,v0,v241,v3,v1,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v60,v8,v7),(v241,v60,v2)],[1],[(0,175)]),
([v60,v0,v2,v189,v1,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v60,v8,v7),(v189,v60,v3)],[1],[(0,175)]),
([v0,v2,v3,v1,0xff03ff02ff03ff02,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff11ff10ff11ff10,v4,v5],[],[],[]),
([v0,v2,v237,v8,v1,v4,v5],[(v8,v3,v2),(v17,v0,v4),(v259,v8,v17),(v237,v259,v3)],[1],[]),
([v0,v2,v189,v8,v1,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v60,v8,v7),(v189,v60,v3)],[1],[]),
([v90,v0,v2,v3,v7,v4,v5],[],[],[(4,176)]),
([v0,v2,v149,v8,v1,v4,v5],[(v8,v3,v2),(v17,v0,v4),(v132,v5,v17),(v149,v132,v3)],[2],[(0,134)]),
([v0,v2,0xeeffeefeeeffeefe,v3,v1,v4,v5],[(v6,v0,v2),(v15,v3,v4),(v199,v1,v15),(0xeeffeefeeeffeefe,v199,v6)],[0,1],[(0,178),(2,177),(3,82)]),
([v0,v2,0xee00ee00ee0eee0e,v3,v1,v4,v5],[],[],[]),
([v0,v2,0xeeeeeeeeeeeee0e0,v3,v1,v4,v5],[],[],[(1,46),(4,46)]),
([0x303030203030302,v0,v2,v3,v1,v4,v5],[],[],[]),
([v38,v0,v2,v3,v8,v1,v4],[],[],[]),
([v0,v2,v208,v8,v1,v4,v5],[(v8,v3,v2),(v17,v0,v4),(v230,v17,v1),(v208,v230,v3)],[2],[(5,169)]),
([v0,v2,0xeeeeeeeefffffefe,v3,v1,v4,v5],[],[],[(1,82)]),
([v0,v2,0xeeee0000eeee0e0e,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,0xfefefeccfefefecc,v1,v4,v5],[(v9,v0,v3),(v10,v4,v1),(0xfafafa00fafafa00,v9,v10),(0xfefefeccfefefecc,0xfafafa00fafafa00,v2)],[1,5],[]),
([v0,v2,v3,v1,0xfffafffafffaff00,v4,v5],[(v9,v3,v0),(v14,v4,v5),(0xfafafafafafa0000,v9,v14),(0xfffafffafffaff00,0xfafafafafafa0000,v1)],[0],[]),
([v108,v0,v2,v3,v1,v4,v5],[],[],[]),
([v83,v0,v2,v1,v4,v10,v5],[],[],[]),
([v68,v0,v2,v3,v1,v4,v16],[(v8,v2,v3),(v16,v5,v1),(v104,v8,v16),(v68,v5,v104)],[1],[]),
([v62,v0,v2,v3,v1,v4,v16],[(v6,v2,v0),(v16,v1,v5),(v124,v6,v16),(v62,v5,v124)],[1],[]),
([v89,v0,v2,v3,v1,v4,v10],[],[],[]),
([v0,v2,v3,v1,v4,v228,v14],[(v8,v3,v2),(v14,v5,v4),(0xfcfc,v8,v14),(v228,0xfcfc,v5)],[1],[]),
([v0,v2,v3,v1,v4,v148,v14],[(v9,v3,v0),(v14,v4,v5),(v108,v9,v14),(v148,v108,v5)],[1],[]),
([v0,v2,v3,v1,v4,v53,v5],[(v6,v0,v2),(v10,v1,v4),(0xee000000ee,v6,v10),(v53,0xee000000ee,v10)],[0,3],[(0,85),(0,125)]),
([v0,0xabababababaaabaa,v2,v3,v1,v4,v5],[],[],[]),
([v90,v0,v242,v3,v1,v4,v5],[(v8,v2,v3),(v16,v5,v1),(v90,v8,v16),(v242,v90,v2)],[1],[(0,179)]),
([v90,v0,v2,v243,v1,v4,v5],[(v8,v2,v3),(v16,v5,v1),(v90,v8,v16),(v243,v90,v3)],[1],[(0,179)]),
([v0,v2,v3,v1,0xff03ff03ff03ff00,v4,v5],[],[],[]),
([v0,v2,v260,v8,v1,v4,v5],[(v8,v3,v2),(v14,v5,v4),(v261,v8,v14),(v260,v261,v3)],[1],[]),
([v0,v2,v243,v8,v1,v4,v5],[(v8,v2,v3),(v16,v5,v1),(v90,v8,v16),(v243,v90,v3)],[1],[]),
([v0,v2,0xefefefeeefefefee,v3,v1,v4,v5],[],[],[(0,85)]),
([0xa8a8a8a8a8a8fcfc,v0,v2,v3,v1,v4,v5],[(v8,v3,v2),(v14,v5,v4),(v200,v0,v14),(0xa8a8a8a8a8a8fcfc,v200,v8)],[0,5],[]),
([v0,v2,v6,v3,v10,v16,v14],[(v6,v0,v2),(v10,v1,v4),(v16,v1,v5),(v14,v4,v5)],[1],[(0,167),(0,180)]),
([v0,v2,v151,v3,v1,v4,v16],[],[],[(0,180),(4,53)]),
([v0,v2,0xeeeeeeeeeeeeee00,v3,v1,v4,v5],[],[],[]),
([0x303030303030300,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,0xeeeeeeeeffffffee,v3,v1,v4,v5],[],[],[(0,125)]),
([v0,v2,0xeeee0000eeee00ee,v3,v1,v4,v5],[],[],[(4,54)]),
([v0,v2,v3,0xfefefeaafefefeaa,v1,v4,v5],[(v8,v2,v3),(v10,v1,v4),(v204,v8,v10),(0xfefefeaafefefeaa,v204,v0)],[0,1,5],[(0,181)]),
([v0,v2,v3,v1,0xffeeffeeffeeff00,v4,v5],[],[],[]),
([v63,v0,v2,v3,v1,v4,v5],[(v6,v0,v2),(v14,v4,v5),(v151,v6,v14),(v63,v151,v6)],[1],[(3,127)]),
([v31,v0,v2,v3,v1,v4,v16],[(v9,v3,v0),(v16,v5,v1),(v116,v9,v16),(v31,v5,v116)],[1],[]),
([v0,v2,v3,v1,v4,v10,0xffffffff000000fc],[],[],[]),
([v0,v2,v3,v1,v4,v150,v14],[(v6,v2,v0),(v14,v5,v4),(v63,v6,v14),(v150,v63,v5)],[0,1],[]),
([v0,v2,v3,v1,v4,v92,v5],[(v8,v2,v3),(v10,v1,v4),(0xfc000000fc,v8,v10),(v92,0xfc000000fc,v10)],[1,5],[]),
([v0,0xabababaaabababaa,v2,v3,v1,v4,v5],[],[],[]),
([v101,v0,v2,v190,v1,v4,v5],[(v8,v3,v2),(v10,v4,v1),(v101,v8,v10),(v190,v101,v3)],[1],[(0,182)]),
([v0,v2,v3,v1,0xff11ff11ff11ff00,v4,v5],[],[],[]),
([v0,v2,v190,v8,v1,v4,v5],[(v8,v3,v2),(v10,v4,v1),(v101,v8,v10),(v190,v101,v3)],[1],[]),
([v0,v2,0xefefefefefefeeee,v3,v1,v4,v5],[],[],[]),
([0xa8a8a8fca8a8a8fc,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v10,v1,v4),(v93,v0,v10),(0xa8a8a8fca8a8a8fc,v93,v8)],[0,1,5],[(0,183)]),
([v0,v2,0xeeffeeffeeffeeee,v3,v1,v4,v5],[(v6,v0,v2),(v14,v4,v5),(v131,v1,v14),(0xeeffeeffeeffeeee,v131,v6)],[1],[(0,184),(2,184)]),
([v0,v2,0xee00ee00ee00eeee,v3,v1,v4,v5],[],[],[(3,127)]),
([v0,v2,v3,v1,v17,v12,v32],[(v11,v3,v5),(v12,v2,v5),(v17,v0,v4),(v32,v4,v11)],[1],[(0,185),(3,22)]),
([v69,v0,v2,v3,v7,v4,v5],[],[],[(5,186)]),
([v0,v2,v3,v1,v100,v4,v12],[(v12,v2,v5),(v11,v3,v5),(v7,v0,v1),(v100,v7,v11)],[3],[(1,185),(2,23),(2,187)]),
([v58,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v11,v3,v5),(v7,v0,v1),(v58,v7,v11)],[2,3],[]),
([v42,v0,v2,v1,v17,v15,v5],[],[],[(3,135),(3,188)]),
([v33,v0,v2,v1,v49,v15,v5],[(v17,v0,v4),(v15,v3,v4),(v49,v2,v17),(v33,v3,v17)],[0],[(4,189)]),
([v56,v0,v2,v1,v17,v15,v5],[(v17,v0,v4),(v15,v3,v4),(v49,v2,v17),(v56,v3,v49)],[3],[]),
([v31,v0,v2,v3,v7,v13,v4],[(v7,v0,v1),(v13,v2,v1),(v19,v3,v7),(v31,v5,v19)],[2,4],[]),
([v55,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v11,v3,v5),(v44,v0,v12),(v55,v44,v11)],[2],[]),
([v60,v27,v0,v3,v13,v4,v5],[(v7,v0,v1),(v13,v2,v1),(v27,v3,v7),(v60,v27,v2)],[2],[(0,190)]),
([0xaaaaaaaa8c8c8c8c,v0,v2,v3,v1,v4,v12],[(v11,v3,v5),(v12,v2,v5),(v110,v0,v11),(0xaaaaaaaa8c8c8c8c,v110,v12)],[1,2],[]),
([v0,v2,v3,v1,v146,v15,v5],[(v17,v0,v4),(v15,v3,v4),(v125,v2,v17),(v146,v125,v1)],[0,3],[]),
([v27,v88,v0,v3,v13,v4,v5],[(v7,v0,v1),(v13,v2,v1),(v27,v3,v7),(v88,v2,v7)],[2],[(0,43),(0,190)]),
([v0,v138,v2,v1,v4,v12,v11],[(v11,v3,v5),(v12,v2,v5),(v71,v3,v12),(v138,v71,v0)],[3],[(4,190)]),
([v33,v118,v2,v1,v17,v15,v5],[(v15,v3,v4),(v17,v0,v4),(v33,v3,v17),(v118,v0,v15)],[4],[]),
([v33,v0,v2,v1,v15,v21,v5],[(v15,v3,v4),(v17,v0,v4),(v33,v3,v17),(v21,v1,v17)],[0],[(2,191)]),
([v25,v105,v2,v3,v7,v4,v5],[],[],[(4,192)]),
([v0,v2,v3,v1,v17,v16,v32],[(v15,v3,v4),(v17,v0,v4),(v16,v5,v1),(v32,v5,v15)],[1],[(2,193)]),
([v0,v2,v3,v1,v4,0xffffff00cccccc00,v11],[(v12,v2,v5),(v11,v3,v5),(v10,v1,v4),(0xffffff00cccccc00,v10,v12)],[5],[]),
([v76,v0,v2,v3,v1,v4,v12],[(v11,v3,v5),(v12,v2,v5),(v10,v4,v1),(v76,v10,v11)],[2],[]),
([v57,v0,v2,v3,v13,v4,v5],[(v7,v0,v1),(v13,v2,v1),(v21,v4,v7),(v57,v3,v21)],[2],[]),
([v57,v0,v2,v1,v15,v21,v5],[(v17,v0,v4),(v15,v3,v4),(v21,v1,v17),(v57,v3,v21)],[3],[(0,194)]),
([v40,v0,v2,v1,v4,v12,v32],[],[],[(4,195)]),
([v0,v2,v3,v1,v4,v26,v32],[(v11,v3,v5),(v12,v2,v5),(v32,v4,v11),(v26,v1,v12)],[1],[(0,193),(0,196)]),
([v25,v0,v2,v3,v4,v21,v5],[(v7,v0,v1),(v13,v2,v1),(v21,v4,v7),(v25,v5,v13)],[0],[]),
([v0,v2,v3,v129,v4,v12,v32],[(v11,v3,v5),(v12,v2,v5),(v32,v4,v11),(v129,v1,v32)],[2],[(3,194)]),
([v38,v0,v2,v3,v1,v15,v21],[(v17,v0,v4),(v15,v3,v4),(v21,v1,v17),(v38,v5,v21)],[0,3],[]),
([v30,v0,v2,v3,v7,v4,v26],[(v13,v2,v1),(v7,v0,v1),(v26,v5,v13),(v30,v5,v7)],[0,5],[]),
([v25,v0,v2,v3,v7,v4,v26],[],[],[(0,195),(4,197)]),
([v69,v0,v2,v3,v1,v4,v26],[(v12,v2,v5),(v11,v3,v5),(v26,v1,v12),(v69,v11,v26)],[1,3],[]),
([v40,v0,v2,v1,v4,v12,v11],[(v11,v3,v5),(v12,v2,v5),(v32,v4,v11),(v40,v3,v32)],[5],[(4,195),(5,198)]),
([v57,v0,v2,v1,v17,v15,v5],[(v17,v0,v4),(v15,v3,v4),(v21,v1,v17),(v57,v3,v21)],[3],[]),
([v38,v0,v2,v3,v1,v17,v15],[(v17,v0,v4),(v15,v3,v4),(v21,v1,v17),(v38,v5,v21)],[3,4],[]),
([v69,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v11,v3,v5),(v26,v1,v12),(v69,v11,v26)],[2],[]),
([v0,v201,v2,v3,v1,v4,v12],[],[],[]),
([v25,v0,v2,v3,0xffaaffaa00220022,v4,v5],[],[],[(0,199),(4,197)]),
([v0,v2,v3,v226,v1,v15,v5],[(v17,v0,v4),(v15,v3,v4),(v230,v1,v17),(v226,v230,v15)],[0],[]),
([v25,v74,v0,v2,v3,v4,v5],[],[],[(0,200)]),
([v0,v2,v3,v226,v1,v17,v5],[],[],[(0,192),(0,201)]),
([v75,v0,v2,v1,v17,v15,v5],[(v15,v3,v4),(v17,v0,v4),(v67,v5,v17),(v75,v3,v67)],[0,3],[]),
([v36,v0,v2,v1,v17,v15,v5],[],[],[(3,202)]),
([v80,v0,v2,v3,v1,v4,v12],[(v11,v3,v5),(v12,v2,v5),(v117,v4,v12),(v80,v11,v117)],[2],[]),
([v0,v138,v2,v1,v4,v5,v11],[(v11,v3,v5),(v41,v2,v11),(v71,v3,v41),(v138,v71,v0)],[0],[]),
([v33,v118,v2,v1,v4,v17,v5],[],[],[]),
([v33,v0,v2,v1,v22,v15,v5],[],[],[(0,108),(5,203)]),
([v33,v0,v2,v1,v15,v10,v5],[],[],[(2,204)]),
([v39,v71,v0,v2,v1,v4,v11],[(v11,v3,v5),(v41,v2,v11),(v71,v3,v41),(v39,v5,v41)],[0,2],[(0,109)]),
([v39,v71,v0,v2,v1,v4,v12],[],[],[]),
([v27,v0,v2,v29,v18,v4,v5],[],[],[]),
([v72,v0,v2,v7,v18,v4,v5],[],[],[]),
([v97,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v41,v3,v12),(v23,v0,v5),(v97,v23,v41)],[2,4],[]),
([v31,v0,v2,v3,v1,v29,v4],[],[],[]),
([v0,0xaaaaaaaaacacacac,v2,v3,v1,v4,v5],[(v11,v3,v5),(v41,v2,v11),(v110,v0,v11),(0xaaaaaaaaacacacac,v110,v41)],[1,4],[(2,44),(2,205),(3,206)]),
([v0,v137,v2,v3,v1,v4,v12],[(v12,v2,v5),(v41,v3,v12),(v39,v5,v41),(v137,v39,v0)],[0],[]),
([v0,v2,v3,v1,v225,v4,v11],[],[],[]),
([v108,v0,v2,v3,v1,v17,v5],[(v17,v0,v4),(v46,v3,v17),(v115,v4,v46),(v108,v115,v5)],[0,4],[]),
([v62,v0,v2,v3,v7,v4,v16],[(v7,v0,v1),(v29,v2,v7),(v16,v1,v5),(v62,v5,v29)],[0],[]),
([v62,v0,v2,v3,v1,v4,v26],[(v13,v2,v1),(v29,v0,v13),(v26,v13,v5),(v62,v29,v5)],[1,5],[(0,115)]),
([v38,v0,v2,v3,v1,v29,v4],[],[],[]),
([v0,v2,v3,0xff00fa50ff00fa50,v1,v4,v5],[],[],[]),
([v28,v0,v2,v3,v1,v4,v41],[(v11,v3,v5),(v41,v2,v11),(v48,v11,v1),(v28,v5,v48)],[2],[(5,207)]),
([v62,v0,v2,v3,v1,v4,v47],[(v7,v0,v1),(v29,v2,v7),(v47,v7,v5),(v62,v29,v5)],[1],[(0,113),(0,207)]),
([v0,v2,v3,0xff00fa0aff00fa0a,v1,v4,v5],[(v15,v3,v4),(v46,v0,v15),(v199,v15,v1),(0xff00fa0aff00fa0a,v199,v46)],[4],[]),
([v30,v0,v2,v3,v1,v4,v124],[(v7,v0,v1),(v29,v2,v7),(v30,v7,v5),(v124,v29,v5)],[2,3,5],[(0,208),(0,209)]),
([v75,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v46,v0,v15),(v103,v46,v5),(v75,v3,v103)],[1,5],[]),
([v83,v0,v2,v1,v7,v4,v5],[(v7,v0,v1),(v29,v2,v7),(v53,v29,v4),(v83,v3,v53)],[1],[]),
([v68,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v41,v3,v12),(v104,v41,v1),(v68,v5,v104)],[0,1],[]),
([v80,v0,v2,v3,v1,v4,v5],[],[],[]),
([v89,v0,v2,v3,v1,v7,v4],[(v7,v0,v1),(v29,v2,v7),(v53,v29,v4),(v89,v53,v5)],[1],[]),
([v57,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v46,v0,v15),(v91,v46,v1),(v57,v3,v91)],[1,5],[(3,208)]),
([v83,v0,v2,v1,v13,v4,v5],[(v13,v2,v1),(v29,v0,v13),(v53,v29,v4),(v83,v3,v53)],[1],[]),
([v68,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v41,v2,v11),(v104,v41,v1),(v68,v5,v104)],[0,1],[(5,209)]),
([v69,v0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v41,v2,v11),(v104,v41,v1),(v69,v11,v104)],[2],[]),
([v89,v0,v2,v3,v1,v13,v4],[(v13,v2,v1),(v29,v0,v13),(v53,v29,v4),(v89,v5,v53)],[1],[]),
([v0,v2,v3,v1,0xffafffafffaeffae,v4,v5],[],[],[(2,85)]),
([0xdddddcdc,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xffbbffbbffbaffba,v4,v5],[(v11,v3,v5),(v121,v2,v11),(0xbbbbbbbbbabababa,v121,v0),(0xffbbffbbffbaffba,0xbbbbbbbbbabababa,v1)],[0],[(0,210)]),
([0xcfcfcece,v0,v2,v3,v1,v4,v5],[],[],[]),
([v33,v0,v2,v237,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v259,v33,v2),(v237,v259,v3)],[1],[(0,42),(1,175),(4,212),(5,211)]),
([v0,v2,v3,v1,v4,v147,v11],[(v13,v2,v1),(v105,v0,v13),(v147,v105,v5),(v11,v3,v5)],[3],[(5,213)]),
([0xf0f03020f0f0302,v0,v2,v3,v1,v4,v5],[],[],[]),
([v94,v0,v2,v3,v1,v4,v147],[(v13,v2,v1),(v105,v0,v13),(v147,v105,v5),(v94,v5,v147)],[1],[(4,214)]),
([v0,v2,v3,v1,v4,v147,v14],[(v13,v2,v1),(v105,v0,v13),(v147,v105,v5),(v14,v5,v4)],[1,5],[]),
([v0,v2,v3,v1,v4,0xffffff0fffffff0c,v5],[(v12,v2,v5),(v71,v3,v12),(v207,v71,v1),(0xffffff0fffffff0c,v207,v4)],[0],[]),
([0xff0fff0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([v94,v156,v2,v3,v1,v4,v5],[(v13,v2,v1),(v105,v0,v13),(v94,v105,v5),(v156,v94,v0)],[1],[(4,214)]),
([v0,0xaaaabbbbaaaababa,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff00ff00ff55ff50,v4,v5],[],[],[]),
([0x3322,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v88,v2,v7),(0x332200003322,v88,v4),(0x3322,0x332200003322,v5)],[1,4],[]),
([v33,v0,v2,v208,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(0xf000a000f000a,v33,v1),(v208,0xf000a000f000a,v3)],[1],[(0,214)]),
([v0,v2,v3,v1,v4,v143,v12],[(v17,v0,v4),(v33,v3,v17),(v143,v33,v5),(v12,v2,v5)],[2],[]),
([0xf0f05040f0f0504,v0,v2,v3,v1,v4,v5],[],[],[]),
([v79,v0,v2,v3,v1,v4,v143],[(v17,v0,v4),(v33,v3,v17),(v143,v33,v5),(v79,v5,v143)],[1],[(0,215)]),
([0xff55ff50,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xff30ff30,v0,v2,v3,v1,v176,v4],[(v11,v3,v5),(v121,v2,v11),(v176,v121,v1),(0xff30ff30,v176,v5)],[0],[]),
([0xff30ff30,v121,v0,v2,v3,v1,v4],[],[],[]),
([v0,0xaaaaafafaaaaaeae,v2,v3,v1,v4,v5],[],[],[]),
([v79,v0,v2,v149,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v79,v33,v5),(v149,v79,v3)],[1],[(0,215)]),
([v0,v2,v3,v1,0xff00ff00ff0fff0a,v4,v5],[],[],[]),
([v33,v0,v2,v149,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v79,v33,v5),(v149,v79,v3)],[1],[(0,215),(4,216)]),
([0xf0a0f0a0c080c08,v0,v2,v3,v1,v4,v5],[(v12,v2,v5),(v71,v3,v12),(v7,v0,v1),(0xf0a0f0a0c080c08,v71,v7)],[4],[]),
([v0,0xaaaaafaf88888c8c,v2,v3,v1,v4,v5],[(v15,v3,v4),(v118,v0,v15),(v12,v2,v5),(0xaaaaafaf88888c8c,v118,v12)],[4,5],[]),
([v27,v71,v0,v2,v1,v4,v5],[],[],[(0,213),(2,85)]),
([0xaaaa8c8caaaa8c8c,v0,v2,v3,v1,v22,v5],[],[],[]),
([0xf0f0a0a0c0c0808,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v12,v2,v5),(0xf0f0a0a0c0c0808,v33,v12)],[1,2,4],[(0,24),(3,217)]),
([0xaa88af8caa88af8c,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf0f0a0a0f000a00,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v16,v1,v5),(0xf0f0a0a0f000a00,v33,v16)],[0],[]),
([v0,0xaaaaafafaa00af00,v2,v3,v1,v4,v5],[],[],[]),
([v37,v71,v0,v2,v3,v1,v4],[],[],[]),
([v27,v0,v2,v189,v1,v4,v5],[(v7,v0,v1),(v88,v2,v7),(v189,v88,v3),(v27,v3,v7)],[1],[(0,175),(0,190),(3,218)]),
([0xaeaeaeae,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v71,v3,v12),(v138,v71,v0),(0xaeaeaeae,v138,v5)],[2],[(0,218)]),
([v25,v0,v2,v3,v1,v4,v147],[(v13,v2,v1),(v105,v0,v13),(v147,v105,v5),(v25,v5,v13)],[1],[(4,214),(5,219)]),
([0xff0cff0c,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v71,v3,v12),(v207,v71,v1),(0xff0cff0c,v207,v5)],[2],[(0,219)]),
([v0,v2,v3,v1,v177,v4,v5],[],[],[]),
([v30,v0,v2,v3,v1,v4,0xffffffff33223322],[(v7,v0,v1),(v88,v2,v7),(0xffffffff33223322,v88,v5),(v30,v5,v7)],[1],[(1,215),(5,220)]),
([0xff30ff30,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v121,v2,v11),(v176,v121,v1),(0xff30ff30,v176,v5)],[2,3],[(0,220)]),
([v0,v2,v3,v1,v133,v4,v5],[(v15,v3,v4),(v118,v0,v15),(0x55005000550050,v118,v1),(v133,0x55005000550050,v15)],[3],[]),
([v27,v88,v0,v2,v18,v4,v5],[],[],[]),
([v0,0xaaaaacacaaaaacac,v2,v3,v1,v4,v5],[],[],[(2,189)]),
([v31,v88,v0,v2,v3,v1,v4],[],[],[]),
([v0,0xaaaaafafaaaaa0a0,v2,v3,v1,v4,v5],[],[],[(4,191)]),
([v38,v33,v0,v2,v3,v1,v4],[],[],[]),
([v0,0xaaaaafa0aaaaafa0,v2,v3,v1,v4,v5],[],[],[]),
([v28,v121,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,v178,v17,v5],[(v17,v0,v4),(v18,v3,v1),(v22,v2,v4),(v178,v18,v22)],[2],[]),
([v98,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v18,v3,v1),(v23,v0,v5),(v98,v18,v23)],[2,4],[]),
([0xf0a0c080f0a0c08,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfff3fff2fff3fff2,v4,v5],[(v17,v0,v4),(v18,v3,v1),(v125,v2,v17),(0xfff3fff2fff3fff2,v125,v18)],[0],[(0,221),(1,85)]),
([0xaaa0aaa0bbb0bbb0,v0,v2,v3,v1,v4,v5],[],[],[]),
([v27,v42,v0,v2,v1,v4,v5],[],[],[(0,85)]),
([v28,v0,v2,v3,v7,v4,v12],[],[],[]),
([v80,v0,v2,v3,v1,v17,v5],[],[],[]),
([v0,v2,v3,v1,0xffafffaeffafffae,v4,v5],[],[],[(0,85)]),
([v0,0xaaaabbbba0a0b0b0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v22,v2,v4),(v250,v0,v22),(0xaaaabbbba0a0b0b0,v250,v11)],[3,4,5],[]),
([v0,v139,v2,v3,v1,v4,v12],[(v12,v2,v5),(v18,v3,v1),(v28,v5,v18),(v139,v28,v0)],[2],[]),
([v28,v0,v262,v3,v1,v4,v12],[(v12,v2,v5),(v18,v3,v1),(v28,v5,v18),(v262,v28,v2)],[2],[]),
([v0,v2,v3,v1,v222,v4,v11],[],[],[]),
([v107,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v18,v3,v1),(v28,v5,v18),(v107,v28,v4)],[2],[]),
([v28,v0,v2,v3,v1,v4,v104],[(v12,v2,v5),(v18,v3,v1),(v28,v5,v18),(v104,v28,v12)],[2,4],[(0,222),(5,207)]),
([v94,v123,v0,v2,v3,v4,v5],[(v13,v2,v1),(v23,v0,v5),(v123,v1,v23),(v94,v23,v13)],[0],[(3,223)]),
([v0,v2,v3,v1,v179,v4,v12],[],[],[]),
([v0,v2,v3,v1,0xfffafcf8fffafcf8,v4,v5],[(v7,v0,v1),(v22,v2,v4),(v177,v7,v22),(0xfffafcf8fffafcf8,v3,v177)],[1],[]),
([v0,v2,v3,v1,v4,0xffffffccfff0ffc0,v5],[],[],[]),
([0xffaacc88,v0,v2,v3,v1,v4,v5],[],[],[]),
([v94,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v23,v0,v5),(0xffccffccaa88aa88,v13,v23),(v94,0xffccffccaa88aa88,v13)],[2],[]),
([v83,v0,v2,v1,v4,v22,v5],[(v7,v0,v1),(v22,v2,v4),(v53,v7,v22),(v83,v3,v53)],[5],[]),
([v57,v0,v2,v1,v18,v4,v5],[(v17,v0,v4),(v18,v3,v1),(v91,v17,v18),(v57,v3,v91)],[1],[(2,222)]),
([v62,v0,v2,v3,v1,v4,v23],[(v13,v2,v1),(v23,v0,v5),(v124,v13,v23),(v62,v5,v124)],[0,1],[(0,207)]),
([v89,v0,v2,v3,v1,v4,v22],[(v7,v0,v1),(v22,v2,v4),(v53,v7,v22),(v89,v53,v5)],[5],[]),
([v0,v2,v208,v1,v18,v4,v5],[(v17,v0,v4),(v18,v3,v1),(0xf000a000f000a,v17,v18),(v208,0xf000a000f000a,v3)],[1],[]),
([v0,v2,v3,v1,v4,v147,v23],[(v13,v2,v1),(v23,v0,v5),(v94,v13,v23),(v147,v94,v5)],[0,1],[]),
([v0,0xaaaaaaaaafafaeae,v2,v3,v1,v4,v5],[],[],[]),
([v80,v0,v2,v210,v1,v4,v5],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22),(v210,v80,v3)],[1],[(0,224)]),
([v0,v2,v3,v1,0xff00ff00ff0fff0c,v4,v5],[],[],[]),
([0x3330,v0,v2,v3,v1,v4,v5],[],[],[]),
([v80,v0,v2,v3,v1,v4,v211],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22),(v211,v80,v5)],[1],[(0,224)]),
([v0,v2,v210,v1,v4,v5,v11],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22),(v210,v80,v3)],[0,1],[]),
([v0,v2,v3,v1,v4,v211,v11],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22),(v211,v80,v5)],[0,1,5],[]),
([v0,v2,v3,v1,0xfff0fff0fff0aaa0,v4,v5],[],[],[]),
([0x55555544,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfff0fff0fffffffa,v4,v5],[],[],[(1,125)]),
([v0,v2,v3,0xff00cc00ff0fcc0c,v1,v4,v5],[],[],[]),
([v30,v157,v0,v2,v3,v1,v4],[],[],[(0,125)]),
([v61,v0,v2,v1,v4,v5,v11],[(v11,v3,v5),(v22,v2,v4),(v43,v22,v1),(v61,v3,v43)],[0],[]),
([v65,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v22,v2,v4),(v43,v22,v1),(v65,v5,v43)],[3],[]),
([v0,v2,v3,v1,0xffaaffaaffaacc88,v4,v5],[],[],[]),
([0xf0f0f0c,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xffaaffaaffffffee,v4,v5],[],[],[(0,125)]),
([v0,v2,v3,0xff00f000ff55f050,v1,v4,v5],[(v15,v3,v4),(v23,v0,v5),(v123,v23,v1),(0xff00f000ff55f050,v123,v15)],[1,3],[]),
([v0,v2,v3,v1,0xffbbffbaffbbffba,v4,v5],[(v15,v3,v4),(v7,v0,v1),(v158,v2,v15),(0xffbbffbaffbbffba,v158,v7)],[0],[(0,225),(1,85)]),
([0xaa88aa88af8caf8c,v0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v13,v2,v1),(v110,v0,v11),(0xaa88aa88af8caf8c,v110,v13)],[2],[]),
([v30,v0,v263,v3,v1,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v30,v5,v7),(v263,v30,v2)],[2],[]),
([v0,v140,v2,v3,v1,v15,v5],[],[],[]),
([v0,v2,v3,v1,v152,v4,v11],[],[],[]),
([v51,v0,v2,v3,v1,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v30,v5,v7),(v51,v30,v4)],[2],[]),
([v69,v192,v0,v2,v3,v4,v5],[(v11,v3,v5),(v13,v2,v1),(v192,v1,v11),(v69,v11,v13)],[0],[(3,226)]),
([v0,v2,v3,v1,v17,v26,v14],[(v13,v2,v1),(v17,v0,v4),(v14,v4,v5),(v26,v13,v5)],[1,5],[(0,227),(3,193)]),
([v0,v2,v3,v1,v119,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v14,v5,v4),(v119,v7,v14)],[0],[(1,228)]),
([v40,v0,v2,v1,v4,v15,v12],[(v12,v2,v5),(v15,v3,v4),(v32,v15,v5),(v40,v3,v32)],[5],[]),
([v25,v0,v2,v3,v7,v4,v12],[],[],[]),
([v0,v2,v3,v1,v133,v21,v5],[],[],[(4,229)]),
([v0,v2,v3,v1,0xffeefcecffeefcec,v4,v5],[(v15,v3,v4),(v7,v0,v1),(v133,v7,v15),(0xffeefcecffeefcec,v2,v133)],[1],[]),
([v0,v2,v3,v1,v4,0xffffffaafff0ffa0,v5],[(v17,v0,v4),(v11,v3,v5),(0xffffaaaaf0f0a0a0,v11,v17),(0xffffffaafff0ffa0,0xffffaaaaf0f0a0a0,v1)],[0],[]),
([0xffaaf0a0,v0,v2,v3,v1,v4,v5],[(v15,v3,v4),(v7,v0,v1),(v133,v7,v15),(0xffaaf0a0,v133,v5)],[3],[]),
([v79,v0,v2,v3,v1,v4,v5],[],[],[]),
([v75,v0,v2,v1,v4,v5,v11],[(v17,v0,v4),(v11,v3,v5),(v103,v11,v17),(v75,v3,v103)],[0,1],[]),
([v83,v0,v2,v1,v4,v17,v5],[(v13,v2,v1),(v17,v0,v4),(v53,v17,v13),(v83,v3,v53)],[5],[]),
([v62,v0,v2,v3,v1,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v124,v12,v7),(v62,v5,v124)],[0,1],[]),
([v89,v0,v2,v3,v1,v4,v17],[(v13,v2,v1),(v17,v0,v4),(v53,v17,v13),(v89,v53,v5)],[5],[]),
([v0,0xaaaaaaaaafaeafae,v2,v3,v1,v4,v5],[],[],[]),
([v69,v0,v2,v213,v1,v4,v5],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11),(v213,v69,v3)],[1],[(0,230)]),
([v0,v2,v3,v1,0xff00ff00ff33ff30,v4,v5],[],[],[]),
([0xf0a,v0,v2,v3,v1,v4,v5],[(v15,v3,v4),(v7,v0,v1),(0xf0a00000f0a,v7,v15),(0xf0a,0xf0a00000f0a,v5)],[1,4],[]),
([v69,v0,v2,v3,v1,v4,v169],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11),(v169,v69,v5)],[1],[(0,230)]),
([v0,v2,v213,v1,v4,v5,v11],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11),(v213,v69,v3)],[0,1],[]),
([v0,v2,v3,v1,v4,v169,v11],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11),(v169,v69,v5)],[0,1,5],[]),
([v0,v2,v149,v1,v4,v5,v11],[(v17,v0,v4),(v11,v3,v5),(v79,v11,v17),(v149,v79,v3)],[0,1],[]),
([v0,v2,v3,v1,v4,v143,v11],[(v17,v0,v4),(v11,v3,v5),(v79,v11,v17),(v143,v79,v5)],[0,1,5],[]),
([v0,v2,v3,v1,v4,v215,v11],[(v11,v3,v5),(v13,v2,v1),(v231,v13,v4),(v215,v231,v5)],[3],[(4,231)]),
([v0,v2,v3,v1,0xffaaffffffaaffee,v4,v5],[],[],[(2,125)]),
([v0,v2,v3,0xff00aa00ff0faa0a,v1,v4,v5],[],[],[]),
([v30,0xfffff0f0,v0,v2,v3,v1,v4],[],[],[(1,125),(1,231)]),
([v38,v0,v2,v3,v1,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v21,v7,v4),(v38,v5,v21)],[2],[]),
([v0,v2,v3,v1,0xffaaffaaffaaf0a0,v4,v5],[(v15,v3,v4),(v7,v0,v1),(v32,v15,v5),(0xffaaffaaffaaf0a0,v7,v32)],[1,5],[(1,227),(2,196)]),
([0xf0f0f0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xffaaffaafffffffa,v4,v5],[],[],[(1,125)]),
([v0,v2,v3,0xff00f000ff33f030,v1,v4,v5],[(v12,v2,v5),(v15,v3,v4),(v78,v12,v1),(0xff00f000ff33f030,v78,v15)],[1,3],[]),
([v27,v66,v2,v7,v18,v4,v5],[(v7,v0,v1),(v18,v3,v1),(v27,v3,v7),(v66,v0,v18)],[4],[]),
([v42,v0,v2,v1,v49,v15,v5],[(v15,v3,v4),(v22,v2,v4),(v42,v3,v22),(v49,v0,v22)],[0],[(1,232)]),
([v42,v250,v0,v2,v1,v15,v5],[],[],[]),
([v42,v0,v2,v1,v15,v43,v5],[],[],[(2,233)]),
([v28,v66,v2,v3,v7,v4,v5],[],[],[]),
([v27,v0,v2,v13,v18,v4,v5],[],[],[(0,135)]),
([v56,v0,v2,v1,v22,v15,v5],[(v15,v3,v4),(v22,v2,v4),(v49,v0,v22),(v56,v3,v49)],[3],[]),
([v31,v0,v2,v3,v13,v18,v4],[(v13,v2,v1),(v18,v3,v1),(v19,v0,v18),(v31,v5,v19)],[2],[]),
([v55,v0,v2,v3,v1,v4,v23],[(v11,v3,v5),(v23,v0,v5),(v44,v2,v23),(v55,v11,v44)],[4],[]),
([0xaa8caa8caa8caa8c,v0,v2,v3,v13,v4,v5],[],[],[]),
([v0,v2,v3,v1,v159,v4,v11],[],[],[(0,234)]),
([v0,v2,v3,v1,v4,0xffffff00aaaaaa00,v12],[],[],[]),
([v106,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v23,v0,v5),(v10,v1,v4),(v106,v10,v23)],[2],[]),
([v36,v0,v2,v7,v18,v4,v5],[],[],[]),
([v75,v0,v2,v1,v4,v23,v11],[(v11,v3,v5),(v23,v0,v5),(v67,v4,v23),(v75,v3,v67)],[3,5],[]),
([v79,v0,v2,v3,v1,v4,v23],[(v11,v3,v5),(v23,v0,v5),(v67,v4,v23),(v79,v11,v67)],[4],[]),
([v57,v0,v2,v7,v18,v4,v5],[],[],[]),
([v40,v0,v2,v1,v4,v23,v11],[(v11,v3,v5),(v23,v0,v5),(v32,v4,v11),(v40,v3,v32)],[5],[(5,235)]),
([v38,v0,v2,v3,v1,v17,v22],[(v17,v0,v4),(v22,v2,v4),(v21,v1,v17),(v38,v5,v21)],[2,4],[]),
([v94,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v23,v0,v5),(v26,v1,v12),(v94,v23,v26)],[2,4],[]),
([v0,v2,v3,0xff00cc44ff00cc44,v1,v17,v5],[],[],[]),
([v36,v0,v2,v13,v4,v59,v5],[],[],[(2,236)]),
([v61,v0,v2,v1,v15,v43,v5],[(v15,v3,v4),(v22,v2,v4),(v43,v1,v22),(v61,v3,v43)],[3],[]),
([v75,v0,v2,v3,v1,v4,v12],[],[],[]),
([v28,v0,v2,v3,v7,v4,v48],[(v7,v0,v1),(v18,v3,v1),(v48,v5,v18),(v28,v5,v48)],[4],[(0,236)]),
([v58,v0,v2,v3,v1,v4,v47],[(v11,v3,v5),(v23,v0,v5),(v47,v1,v23),(v58,v11,v47)],[3],[]),
([v36,v0,v2,v13,v18,v4,v5],[],[],[(2,236)]),
([v61,v0,v2,v1,v22,v15,v5],[(v15,v3,v4),(v22,v2,v4),(v43,v1,v22),(v61,v3,v43)],[3],[]),
([v58,v0,v2,v3,v1,v4,v23],[(v11,v3,v5),(v23,v0,v5),(v47,v1,v23),(v58,v11,v47)],[4],[]),
([v0,v232,v2,v3,v13,v4,v5],[],[],[]),
([v0,v2,v3,0xff00f030ff00f030,v1,v15,v5],[(v15,v3,v4),(v22,v2,v4),(v233,v1,v22),(0xff00f030ff00f030,v233,v15)],[0],[]),
([v30,v28,v0,v2,v3,v7,v4],[],[],[]),
([v61,v0,v2,v13,v18,v4,v5],[],[],[]),
([v36,v0,v2,v1,v22,v15,v5],[],[],[(3,237)]),
([v98,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v23,v0,v5),(v48,v1,v11),(v98,v23,v48)],[3,4],[]),
([v27,v66,v2,v1,v7,v4,v5],[],[],[]),
([v42,v0,v2,v1,v15,v10,v5],[],[],[(2,238)]),
([v42,v0,v2,v102,v4,v15,v5],[(v15,v3,v4),(v45,v2,v15),(v42,v3,v45),(v102,v1,v45)],[1,5],[]),
([v31,v66,v2,v3,v1,v7,v4],[(v7,v0,v1),(v19,v3,v7),(v66,v0,v19),(v31,v5,v19)],[1],[(0,138)]),
([v24,v95,v0,v3,v1,v4,v12],[(v12,v2,v5),(v44,v0,v12),(v95,v2,v44),(v24,v5,v44)],[0,4],[(0,136)]),
([v24,v114,v2,v3,v1,v4,v12],[],[],[]),
([v0,v130,v2,v3,v1,v15,v5],[],[],[]),
([v0,v2,v3,v1,v188,v4,v11],[],[],[]),
([v63,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v44,v0,v12),(v24,v5,v44),(v63,v24,v4)],[1,2,5],[]),
([v24,v0,v2,v3,v1,v4,v26],[(v12,v2,v5),(v44,v0,v12),(v24,v5,v44),(v26,v1,v12)],[1,5],[(0,128)]),
([v24,v78,v0,v2,v3,v1,v4],[],[],[]),
([v24,v0,v2,v3,v1,v122,v12],[(v12,v2,v5),(v44,v0,v12),(v24,v5,v44),(v122,v4,v44)],[0,1,4],[(0,151)]),
([v24,v164,v0,v2,v3,v1,v12],[(v12,v2,v5),(v44,v0,v12),(v24,v5,v44),(v164,v4,v44)],[0,1],[(0,152)]),
([v31,v0,v2,v3,v7,v4,v16],[(v7,v0,v1),(v19,v3,v7),(v16,v1,v5),(v31,v5,v19)],[0,4],[]),
([v68,v0,v2,v3,v1,v4,v26],[(v13,v2,v1),(v54,v3,v13),(v26,v13,v5),(v68,v54,v5)],[1],[(0,116)]),
([v31,v0,v2,v3,v1,v4,v21],[(v7,v0,v1),(v19,v3,v7),(v21,v7,v4),(v31,v19,v5)],[3],[(3,239)]),
([v38,v0,v2,v3,v1,v19,v4],[(v7,v0,v1),(v19,v3,v7),(v21,v7,v4),(v38,v21,v5)],[5],[(4,240)]),
([v0,v2,v3,0xff00ee44ff00ee44,v1,v4,v5],[],[],[]),
([v25,v186,v0,v2,v3,v1,v5],[(v13,v2,v1),(v54,v3,v13),(v25,v13,v5),(v186,v54,v4)],[0],[]),
([v31,v0,v2,v3,v1,v4,v47],[(v7,v0,v1),(v19,v3,v7),(v47,v7,v5),(v31,v19,v5)],[1,3],[(0,161)]),
([v0,v2,v3,0xff00fc0cff00fc0c,v1,v4,v5],[(v15,v3,v4),(v45,v2,v15),(v199,v15,v1),(0xff00fc0cff00fc0c,v199,v45)],[1],[]),
([v31,v0,v2,v3,v1,v7,v4],[(v7,v0,v1),(v19,v3,v7),(v126,v19,v5),(v31,v126,v19)],[1],[]),
([v61,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v45,v2,v15),(v92,v45,v1),(v61,v3,v92)],[1,5],[]),
([v31,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v70,v0,v11),(v116,v70,v1),(v31,v5,v116)],[0,1],[]),
([v58,v0,v2,v3,v1,v4,v5],[],[],[]),
([v63,v198,v0,v2,v3,v1,v17],[(v17,v0,v4),(v49,v2,v17),(v198,v49,v5),(v63,v198,v4)],[0,1,4],[]),
([0xcfcecfce,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xafaeafae,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf030f020f030f02,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,v4,v169,v14],[(v13,v2,v1),(v134,v3,v13),(v169,v134,v5),(v14,v5,v4)],[5],[]),
([v0,v2,v3,0xff005500ff005000,v4,0xffff5555ffff5050,v5],[],[],[(3,241)]),
([v0,v2,v3,v1,v4,0xffffff55ffffff44,v5],[],[],[(2,241)]),
([v193,v0,v2,v3,v1,v4],[],[],[]),
([v193,v0,v2,v3,v1,v146,v4],[(v17,v0,v4),(v125,v2,v17),(v146,v125,v1),(v193,v146,v5)],[0],[]),
([v193,v0,v2,v3,v1,v4,v5],[],[],[]),
([v193,v125,v0,v2,v3,v1,v4],[],[],[]),
([v27,v0,v2,0xf0f0fffaf0f0fffa,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(0xf0a00000f0a,v27,v4),(0xf0f0fffaf0f0fffa,0xf0a00000f0a,v3)],[1],[(2,230)]),
([0xf0f05050f0f0404,v0,v2,v3,v1,v4,v5],[],[],[]),
([v58,v0,v2,v3,v1,v4,v144],[(v7,v0,v1),(v27,v3,v7),(v144,v27,v5),(v58,v5,v144)],[1],[(0,242)]),
([0xff33ff30,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xaaaaafaeaaaaafae,v2,v3,v1,v4,v5],[],[],[]),
([v58,v0,v2,v170,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v58,v27,v5),(v170,v58,v3)],[1],[(0,242)]),
([v0,v2,v3,v1,0xff00ff00ff33ff22,v4,v5],[(v17,v0,v4),(v125,v2,v17),(0x33332222,v125,v5),(0xff00ff00ff33ff22,0x33332222,v1)],[1],[]),
([v27,v0,v2,v170,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v58,v27,v5),(v170,v58,v3)],[1],[(0,242),(3,243)]),
([0xf0a0f0a0f0a0000,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v14,v4,v5),(0xf0a0f0a0f0a0000,v27,v14)],[0],[]),
([0xaaaaaa00afafaf00,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xb0b0a0a0b0b0a0a,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v158,v2,v15),(0xbbbbbababbbbbaba,v158,v0),(0xb0b0a0a0b0b0a0a,0xbbbbbababbbbbaba,v3)],[5],[(0,211)]),
([0xdcdcdcdc,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v110,v0,v11),(0xdddddddddcdcdcdc,v110,v2),(0xdcdcdcdc,0xdddddddddcdcdcdc,v5)],[3,4],[(0,212)]),
([0xf0f05050f0f0000,v0,v2,v1,v4,v5,v11],[(v11,v3,v5),(v110,v0,v11),(0xffff5555ffff5050,v110,v4),(0xf0f05050f0f0000,v3,0xffff5555ffff5050)],[0,5],[(4,244)]),
([v25,v0,v2,v3,v1,v4,v169],[(v13,v2,v1),(v134,v3,v13),(v169,v134,v5),(v25,v5,v13)],[1],[(0,230),(0,244),(5,245)]),
([0xff44ff44,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v114,v0,v12),(v256,v114,v1),(0xff44ff44,v256,v5)],[2,4],[(0,245)]),
([v193,v0,v2,v3,v1,v4,v17],[(v17,v0,v4),(v125,v2,v17),(v146,v125,v1),(v193,v146,v5)],[5],[]),
([0xf030f000f030f00,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v158,v2,v15),(v218,v158,v1),(0xf030f000f030f00,v3,v218)],[5],[(3,246)]),
([v30,v0,v2,v3,v1,v4,v144],[(v7,v0,v1),(v27,v3,v7),(v144,v27,v5),(v30,v5,v7)],[1],[(0,242),(0,246),(5,247)]),
([0xff50ff50,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v110,v0,v11),(0xff55ff55ff50ff50,v110,v1),(0xff50ff50,0xff55ff55ff50ff50,v5)],[3,4],[(0,247)]),
([v0,v2,v3,v1,v100,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v58,v27,v5),(v100,v58,v7)],[3,4,5],[(1,248),(2,41),(2,196)]),
([v58,v0,v2,v3,v7,v4,v16],[],[],[(0,34),(1,248)]),
([v0,0xaaaaaaaaafafa0a0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v110,v0,v11),(v32,v11,v4),(0xaaaaaaaaafafa0a0,v110,v32)],[4],[]),
([v38,v27,v0,v2,v3,v1,v4],[],[],[]),
([v0,0xaaaaaaaaafa0afa0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v110,v0,v11),(v48,v11,v1),(0xaaaaaaaaafa0afa0,v110,v48)],[4],[]),
([v36,v0,v2,v13,v15,v10,v5],[],[],[(0,31),(0,249)]),
([v40,v0,v2,v3,v1,v17,v12],[],[],[(0,27),(0,250)]),
([v25,v0,v2,v3,v15,v10,v5],[],[],[(0,251)]),
([v0,v2,v3,v1,v87,v14],[(v17,v0,v4),(v12,v2,v5),(v14,v4,v5),(v87,v17,v12)],[1,2,4],[(0,185),(0,250),(0,253),(0,255),(0,256),(0,257),(1,254),(3,32),(3,251),(3,252)]),
([v0,v2,v3,v1,v87,v17,v14],[],[],[(1,258),(3,33)]),
([v36,v0,v2,v13,v4,v15,v5],[],[],[]),
([v28,v0,v2,v3,v7,v4,v11],[],[],[(0,35),(0,259)]),
([v0,v2,v3,v1,v100,v4,v47],[(v11,v3,v5),(v7,v0,v1),(v47,v5,v7),(v100,v7,v11)],[1],[(1,260),(2,36),(5,259)]),
([v0,v2,v3,v1,v4,v154,v11],[(v7,v0,v1),(v11,v3,v5),(v74,v7,v4),(v154,v74,v5)],[3],[]),
([0xffccf0c0,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v15,v3,v4),(v25,v13,v5),(0xffccf0c0,v25,v15)],[2,3],[(0,196),(0,251)]),
([v0,v2,v3,v1,0xffaaffffffaafffa,v4,v5],[],[],[]),
([v0,v2,v3,0xff00aa00ff33aa22,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xffeefaeaffeefaea,v4,v5],[],[],[(0,37)]),
([v0,v2,v3,v1,v4,v142],[(v13,v2,v1),(v15,v3,v4),(v85,v13,v15),(v142,v85,v5)],[1,5],[(0,187),(0,252),(1,187),(4,261),(5,261)]),
([v0,v2,v3,v1,v100,v214,v5],[(v7,v0,v1),(v11,v3,v5),(v100,v7,v11),(v214,v100,v4)],[3,4,5],[(0,254),(2,39)]),
([v0,v2,v3,v1,v4,v184,v5],[(v17,v0,v4),(v12,v2,v5),(v87,v17,v12),(v184,v87,v1)],[0,1,5],[(0,253)]),
([v235,v0,v2,v3,v4,v87,v5],[(v17,v0,v4),(v12,v2,v5),(v87,v17,v12),(v235,v87,v1)],[2,4],[(0,40),(0,255),(3,196)]),
([v0,v2,v3,v1,v7,v214,v5],[(v7,v0,v1),(v11,v3,v5),(v100,v7,v11),(v214,v100,v4)],[1],[(0,258)]),
([v0,v2,v170,v1,v4,v5,v11],[(v7,v0,v1),(v11,v3,v5),(v58,v7,v11),(v170,v58,v3)],[0,1,3],[]),
([v0,v2,v3,v1,v4,v144,v11],[(v7,v0,v1),(v11,v3,v5),(v58,v7,v11),(v144,v58,v5)],[0,1],[]),
([v36,v0,v2,v1,v15,v43,v5],[],[],[(4,262)]),
([v61,v0,v2,v1,v15,v10,v5],[(v15,v3,v4),(v10,v4,v1),(v43,v2,v10),(v61,v3,v43)],[3],[]),
([v28,v0,v2,v3,v7,v4,v16],[(v7,v0,v1),(v16,v1,v5),(v48,v3,v16),(v28,v5,v48)],[0,4],[(0,236),(4,263)]),
([v58,v0,v2,v3,v1,v4,v16],[(v11,v3,v5),(v16,v5,v1),(v47,v0,v16),(v58,v11,v47)],[1],[]),
([v0,v202,v2,v3,v13,v4,v5],[(v13,v2,v1),(v10,v1,v4),(v36,v3,v10),(v202,v36,v0)],[2],[]),
([v101,v36,v0,v3,v13,v4,v5],[(v13,v2,v1),(v10,v1,v4),(v36,v3,v10),(v101,v36,v2)],[2],[(0,264)]),
([0xaaaaaaaa8888cccc,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v14,v5,v4),(v200,v0,v14),(0xaaaaaaaa8888cccc,v200,v12)],[1,2],[]),
([v36,v244,v0,v2,v1,v15,v5],[(v15,v3,v4),(v10,v4,v1),(v244,v2,v10),(v36,v3,v10)],[3],[(0,249),(1,264)]),
([v0,v160,v2,v1,v4,v11,v16],[(v11,v3,v5),(v16,v5,v1),(v84,v3,v16),(v160,v84,v0)],[3],[(4,264)]),
([v36,v0,v2,v1,v15,v21,v5],[(v15,v3,v4),(v10,v4,v1),(v36,v3,v10),(v21,v0,v10)],[0],[(1,265)]),
([v36,v93,v0,v2,v1,v15,v5],[],[],[]),
([v30,v145,v2,v3,v7,v4,v16],[(v7,v0,v1),(v16,v1,v5),(v145,v0,v16),(v30,v5,v7)],[0],[]),
([v36,v0,v2,v15,v10,v5,v16],[(v15,v3,v4),(v10,v4,v1),(v36,v3,v10),(v16,v1,v5)],[5],[]),
([v57,v0,v2,v1,v15,v10,v5],[(v15,v3,v4),(v10,v4,v1),(v21,v0,v10),(v57,v3,v21)],[3],[]),
([v38,v0,v2,v3,v1,v15,v10],[(v15,v3,v4),(v10,v4,v1),(v21,v0,v10),(v38,v5,v21)],[1,3],[]),
([v25,v0,v2,v3,v7,v4,v16],[],[],[(0,195),(4,266)]),
([v69,v0,v2,v3,v1,v4,v16],[(v11,v3,v5),(v16,v5,v1),(v26,v2,v16),(v69,v11,v26)],[1],[]),
([v0,v180,v2,v3,v1,v4,v12],[],[],[]),
([0xaa88aaccaa88aacc,v0,v2,v3,v13,v4,v5],[],[],[]),
([v40,v0,v2,v3,v1,v17,v16],[],[],[(2,267)]),
([v40,v0,v2,v3,v1,v4,v26],[],[],[(0,267)]),
([v25,v93,v0,v2,v3,v4,v5],[],[],[]),
([v30,v73,v0,v2,v3,v7,v4],[(v7,v0,v1),(v16,v1,v5),(v73,v2,v16),(v30,v5,v7)],[0],[]),
([v40,v0,v2,v3,v7,v4,v16],[],[],[(2,267)]),
([v0,v2,v3,v10,v16,v32],[(v11,v3,v5),(v16,v5,v1),(v10,v4,v1),(v32,v4,v11)],[0,1,3,5],[(0,193),(0,268),(1,267),(2,193),(3,269),(4,267),(5,269)]),
([v0,v2,v3,v7,v21,v16,v14],[(v7,v0,v1),(v16,v1,v5),(v14,v4,v5),(v21,v4,v7)],[0,1],[(0,269),(0,271),(4,270)]),
([v37,v0,v2,v3,v13,v10,v14],[(v13,v2,v1),(v10,v1,v4),(v14,v5,v4),(v37,v5,v10)],[5],[]),
([v0,v2,v3,v1,v212,v17,v14],[(v17,v0,v4),(v14,v4,v5),(v16,v1,v5),(v212,v17,v16)],[0],[(1,271)]),
([v0,v2,v3,v1,v212,v16,v14],[(v17,v0,v4),(v14,v4,v5),(v16,v1,v5),(v212,v17,v16)],[0],[]),
([v51,v0,v2,v3,v7,v4,v16],[(v7,v0,v1),(v16,v1,v5),(v14,v4,v5),(v51,v7,v14)],[1],[(0,269),(1,272)]),
([v76,v0,v2,v3,v4,v10,v16],[(v11,v3,v5),(v16,v5,v1),(v10,v4,v1),(v76,v11,v10)],[1],[(3,272)]),
([v40,v0,v2,v1,v4,v16,v32],[],[],[(0,268),(4,273)]),
([v38,v0,v2,v3,v1,v21,v14],[(v17,v0,v4),(v14,v4,v5),(v21,v1,v17),(v38,v5,v21)],[0],[(1,269)]),
([v37,v0,v2,v3,v1,v10,v32],[(v15,v3,v4),(v10,v4,v1),(v32,v5,v15),(v37,v5,v10)],[5],[]),
([v25,v0,v2,v3,v4,v10,v26],[],[],[(0,273),(2,269),(3,274)]),
([v51,v0,v2,v3,v1,v21,v5],[(v17,v0,v4),(v14,v4,v5),(v21,v1,v17),(v51,v14,v21)],[0],[(0,269)]),
([v40,v0,v2,v1,v4,v11,v16],[(v11,v3,v5),(v16,v5,v1),(v32,v4,v11),(v40,v3,v32)],[5],[(2,270),(4,273),(4,275)]),
([v30,v0,v2,v3,v4,v21,v16],[(v7,v0,v1),(v16,v1,v5),(v21,v4,v7),(v30,v5,v7)],[0,5],[(0,269),(3,276)]),
([v38,v0,v2,v3,v1,v17,v14],[(v17,v0,v4),(v14,v4,v5),(v21,v1,v17),(v38,v5,v21)],[0,1,4],[]),
([v51,v0,v2,v3,v1,v17,v5],[(v17,v0,v4),(v14,v4,v5),(v21,v1,v17),(v51,v21,v14)],[0,4],[]),
([v51,v74,v0,v2,v3,v4,v16],[(v7,v0,v1),(v16,v1,v5),(v74,v4,v7),(v51,v74,v5)],[0,1],[(0,269),(0,278),(2,277)]),
([v25,v0,v2,v3,v4,0xffffff0000330000,v5],[(v13,v2,v1),(v10,v1,v4),(v25,v5,v13),(0xffffff0000330000,v25,v10)],[1],[(2,278),(3,274)]),
([v0,v2,v3,v1,v253,v4,v14],[],[],[]),
([v0,v2,v3,v1,v253,v4,v12],[(v12,v2,v5),(v14,v5,v4),(v78,v1,v12),(v253,v78,v14)],[1],[(1,274),(4,279)]),
([v30,v74,v0,v2,v3,v4,v16],[(v7,v0,v1),(v16,v1,v5),(v74,v4,v7),(v30,v7,v5)],[0],[(0,279),(2,277)]),
([v99,v0,v2,v1,v4,v11,v16],[(v11,v3,v5),(v16,v5,v1),(v50,v4,v16),(v99,v3,v50)],[3,5],[]),
([v37,v0,v2,v3,v1,v17,v14],[(v17,v0,v4),(v14,v4,v5),(v50,v1,v14),(v37,v5,v50)],[0,4],[]),
([v76,v0,v2,v3,v1,v4,v16],[(v11,v3,v5),(v16,v5,v1),(v50,v4,v16),(v76,v11,v50)],[1],[]),
([v0,v140,v2,v3,v1,v12,v14],[],[],[]),
([v0,v2,v3,v1,v152,v17,v14],[(v17,v0,v4),(v14,v4,v5),(v132,v5,v17),(v152,v132,v1)],[1],[(3,277)]),
([v40,v0,v2,v129,v4,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v40,v3,v32),(v129,v1,v32)],[1],[(1,280),(4,280)]),
([v38,v93,v2,v3,v1,v4,v21],[(v7,v0,v1),(v21,v7,v4),(v93,v0,v21),(v38,v5,v21)],[1],[(2,281),(3,281)]),
([v25,v73,v0,v3,v1,v4],[(v12,v2,v5),(v26,v12,v1),(v73,v2,v26),(v25,v5,v26)],[0,1],[(0,195),(0,273)]),
([v25,v73,v0,v3,v1,v4,v26],[(v12,v2,v5),(v26,v12,v1),(v73,v2,v26),(v25,v5,v26)],[1],[(0,280),(0,281),(0,282)]),
([v75,v0,v2,v1,v4,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v103,v0,v32),(v75,v3,v103)],[1],[(5,111)]),
([v83,v0,v2,v1,v4,v21,v5],[],[],[(0,283),(0,284)]),
([v0,v2,v3,v129,v4,v5,v103],[(v15,v3,v4),(v32,v15,v5),(v103,v0,v32),(v129,v32,v1)],[2],[(1,286),(3,283),(3,285)]),
([v38,v0,v2,v3,v1,v4,v53],[(v7,v0,v1),(v21,v7,v4),(v53,v2,v21),(v38,v21,v5)],[3],[(0,284),(4,287)]),
([v89,v0,v2,v3,v1,v4,v21],[(v7,v0,v1),(v21,v7,v4),(v53,v2,v21),(v89,v53,v5)],[0,2],[]),
([v0,0xafafafafafaeafae,v2,v3,v1,v4,v5],[(v12,v2,v5),(v26,v12,v1),(v254,v3,v26),(0xafafafafafaeafae,v254,v0)],[4],[]),
([v0,v2,v3,v1,0xff33ff33ff33ff30,v4,v5],[(v11,v3,v5),(v32,v11,v4),(0x3333333333333030,v2,v32),(0xff33ff33ff33ff30,0x3333333333333030,v1)],[0],[]),
([v57,v0,v2,v3,v1,v4,v191],[(v17,v0,v4),(v21,v17,v1),(v57,v3,v21),(v191,v21,v5)],[5],[(0,194)]),
([v38,v57,v0,v2,v3,v1,v4],[],[],[]),
([v0,v201,v2,v3,v1,v5,v32],[],[],[]),
([v0,v2,v3,v1,v223,v4,v32],[],[],[]),
([v25,v78,v0,v2,v3,v4],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v78,v1,v26)],[1],[]),
([v25,v78,v0,v2,v3,v4,v26],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v78,v1,v26)],[1],[(0,282),(0,288),(0,289)]),
([v25,v0,v2,v3,v1,v153,v26],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v153,v4,v26)],[1],[(0,280),(0,288)]),
([v25,v136,v0,v2,v3,v1,v26],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v136,v4,v26)],[1],[(0,281),(0,289)]),
([v38,v0,v2,v3,v1,v4],[],[],[]),
([v38,v0,v2,v3,v1,v4,v21],[(v7,v0,v1),(v21,v7,v4),(v191,v21,v5),(v38,v191,v21)],[1],[]),
([v99,v0,v2,v1,v4,v5,v141],[(v15,v3,v4),(v32,v15,v5),(v141,v32,v1),(v99,v3,v141)],[1],[(1,291),(3,290),(4,291)]),
([0xf0f0f0f0f0f0f0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([v65,v0,v2,v3,v1,v4,v109],[(v12,v2,v5),(v26,v12,v1),(v109,v26,v4),(v65,v5,v109)],[1],[(0,291),(0,292),(2,293)]),
([v38,v0,v2,v3,v1,v4,v111],[(v7,v0,v1),(v21,v7,v4),(v111,v21,v5),(v38,v5,v111)],[1],[(0,290),(0,293),(1,293)]),
([v99,v0,v2,v1,v4,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v141,v32,v1),(v99,v3,v141)],[1],[(3,290)]),
([v65,v0,v2,v3,v1,v4,v26],[(v12,v2,v5),(v26,v12,v1),(v109,v26,v4),(v65,v5,v109)],[1],[(2,293)]),
([v38,v0,v2,0xccccccccffffffee,v3,v1,v4],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5),(0xccccccccffffffee,v38,v2)],[2],[]),
([0xf0f0f0a,v38,v0,v2,v3,v1,v4],[(v17,v0,v4),(v21,v17,v1),(v38,v21,v5),(0xf0f0f0a,v38,v3)],[3],[]),
([v51,v38,v0,v2,v3,v1,v21],[(v17,v0,v4),(v21,v17,v1),(v38,v21,v5),(v51,v38,v4)],[0],[(0,294)]),
([v0,0xaaaaffffaaaaffee,v2,v3,v1,v4,v5],[(v13,v2,v1),(v26,v13,v5),(v136,v26,v4),(0xaaaaffffaaaaffee,v136,v0)],[4],[]),
([v0,v180,v2,v1,v4,v5,v11],[(v11,v3,v5),(v32,v11,v4),(v40,v3,v32),(v180,v40,v0)],[0],[]),
([v40,v0,v2,v1,v4,v15,v16],[(v15,v3,v4),(v32,v15,v5),(v40,v3,v32),(v16,v1,v5)],[5],[(0,270)]),
([v25,v73,v0,v3,v1,v13,v4],[(v13,v2,v1),(v26,v13,v5),(v73,v2,v26),(v25,v13,v5)],[1],[]),
([v40,v0,v2,v129,v4,v15,v5],[(v15,v3,v4),(v32,v15,v5),(v40,v3,v32),(v129,v1,v32)],[1,5],[(1,280)]),
([v38,v93,v2,v3,v1,v7,v4],[(v7,v0,v1),(v21,v7,v4),(v93,v0,v21),(v38,v5,v21)],[1],[(2,281)]),
([v25,v73,v0,v3,v1,v4,v12],[(v12,v2,v5),(v26,v12,v1),(v73,v2,v26),(v25,v5,v26)],[0,1],[(0,282)]),
([v0,v156,v2,v3,v1,v4,v12],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v156,v25,v0)],[0],[]),
([v0,v201,v2,v3,v1,v15,v5],[],[],[]),
([v0,v2,v3,v1,v223,v4,v11],[],[],[]),
([v25,v0,v2,v3,v4,v10,v12],[],[],[]),
([v25,v78,v0,v2,v3,v13,v4],[(v13,v2,v1),(v26,v13,v5),(v78,v1,v26),(v25,v5,v13)],[1],[]),
([v25,v0,v2,v3,v1,v153,v12],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v153,v4,v26)],[0,1],[(0,288)]),
([v25,v136,v0,v2,v3,v1,v12],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26),(v136,v4,v26)],[0,1],[(0,289)]),
([v38,v0,v2,v3,v1,v4,v47],[(v7,v0,v1),(v21,v7,v4),(v47,v7,v5),(v38,v21,v5)],[1,5],[(0,293)]),
([v0,v2,v3,v1,0xff00ff00ff0ff000,v4,v5],[(v11,v3,v5),(v32,v11,v4),(v192,v11,v1),(0xff00ff00ff0ff000,v192,v32)],[1,5],[(1,276)]),
([v0,v2,v3,v1,v119,v21,v5],[],[],[(0,271),(5,295)]),
([v38,v0,v2,v3,v1,v7,v4],[(v7,v0,v1),(v21,v7,v4),(v191,v21,v5),(v38,v191,v21)],[1],[]),
([v99,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v32,v15,v5),(v141,v32,v1),(v99,v3,v141)],[1,5],[]),
([v65,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v26,v12,v1),(v109,v26,v4),(v65,v5,v109)],[0,1],[]),
([v76,v0,v2,v3,v1,v4,v5],[],[],[]),
([v51,v38,v0,v2,v3,v1,v17],[(v17,v0,v4),(v21,v17,v1),(v38,v21,v5),(v51,v38,v4)],[0,1,4],[]),
([0xa0a0a0a0f0e0f0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xccccffee,v0,v2,v3,v1,v4,v5],[],[],[(3,296)]),
([0xa0f0a0f0a0e0a0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xccffccee,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v230,v17,v1),(0xccffcceeccffccee,v230,v2),(0xccffccee,0xccffcceeccffccee,v5)],[1],[]),
([0xf0f000f0f0f000c,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf0f00000f0f0f0c,v0,v2,v3,v1,v4,v5],[],[],[]),
([v51,v0,v2,v3,v1,v4,v154],[(v7,v0,v1),(v74,v7,v4),(v154,v74,v5),(v51,v5,v154)],[1],[(0,297)]),
([v0,0xaaaaaaaaaaaaffee,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xaaaaaaffaaaaaaee,v2,v3,v1,v4,v5],[],[],[]),
([v51,v0,v2,v3,v1,v245,v5],[(v7,v0,v1),(v74,v7,v4),(v51,v74,v5),(v245,v51,v4)],[1],[(0,297)]),
([v25,v0,v2,v3,v1,v4,v215],[(v13,v2,v1),(v25,v13,v5),(0xffcc,v25,v4),(v215,0xffcc,v5)],[1],[(0,277),(2,297),(5,298)]),
([v30,v0,v2,v3,v1,v4,v154],[(v7,v0,v1),(v74,v7,v4),(v154,v74,v5),(v30,v5,v7)],[1],[(0,297)]),
([v0,v2,v3,v1,v119,v4,v5],[(v7,v0,v1),(v74,v7,v4),(v51,v74,v5),(v119,v51,v7)],[0],[(1,272)]),
([v0,v2,v3,v1,0xff00ff00ff33cc00,v4,v5],[],[],[]),
([v57,v0,v2,v1,v4,v59,v5],[(v15,v3,v4),(v59,v15,v1),(v91,v0,v59),(v57,v3,v91)],[1],[(0,111),(2,222),(3,208)]),
([v83,v0,v2,v1,v4,v43,v5],[],[],[]),
([v68,v0,v2,v3,v1,v4,v48],[(v11,v3,v5),(v48,v11,v1),(v104,v2,v48),(v68,v5,v104)],[1],[(0,112),(5,209)]),
([v89,v0,v2,v3,v1,v4,v43],[],[],[]),
([v0,0xafafafafafafaeae,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff0fff0fff0fff0a,v4,v5],[],[],[]),
([v28,0x3333333333303330,v0,v2,v3,v1,v4],[],[],[]),
([v30,0x3333333333223322,v0,v2,v3,v1,v4],[],[],[]),
([v30,v145,v2,v3,v1,v4],[],[],[]),
([v30,v145,v2,v3,v1,v4,v47],[],[],[(0,299)]),
([v28,v84,v0,v2,v1,v4],[(v11,v3,v5),(v48,v11,v1),(v84,v3,v48),(v28,v5,v48)],[1],[(0,236)]),
([v28,v84,v0,v2,v1,v4,v48],[],[],[(5,299)]),
([v61,v0,v2,v1,v4,v59,v5],[(v15,v3,v4),(v59,v15,v1),(v92,v2,v59),(v61,v3,v92)],[1],[(0,159)]),
([v31,v0,v2,v3,v1,v4,v48],[(v11,v3,v5),(v48,v11,v1),(v116,v0,v48),(v31,v5,v116)],[1,4],[(0,160)]),
([v0,0xafafafaeafafafae,v2,v3,v1,v4,v5],[(v13,v2,v1),(v43,v13,v4),(v61,v3,v43),(0xafafafaeafafafae,v61,v0)],[4],[]),
([v0,v2,v3,v1,0xff33ff33ff33ff22,v4,v5],[(v17,v0,v4),(v67,v17,v5),(0x3333333333332222,v2,v67),(0xff33ff33ff33ff22,0x3333333333332222,v1)],[0],[(0,241)]),
([v30,v123,v0,v2,v3,v4],[],[],[]),
([v30,v123,v0,v2,v3,v4,v47],[],[],[(0,299)]),
([v0,v140,v2,v3,v1,v5,v117],[(v12,v2,v5),(v117,v12,v4),(v161,v4,v117),(v140,v161,v0)],[4,5],[]),
([v99,v0,v2,v1,v4,v59,v5],[(v15,v3,v4),(v59,v15,v1),(v141,v59,v5),(v99,v3,v141)],[1],[(1,291)]),
([v65,v0,v2,v3,v1,v4,v117],[(v12,v2,v5),(v117,v12,v4),(v109,v117,v1),(v65,v5,v109)],[1],[(0,292)]),
([v0,0xaaaaaaaaffffffee,v2,v3,v1,v4,v5],[(v13,v2,v1),(v43,v13,v4),(v65,v43,v5),(0xaaaaaaaaffffffee,v65,v0)],[4],[]),
([v0,0xaaaaffffaaaafffa,v2,v3,v1,v4,v5],[],[],[]),
([v0,v160,v2,v1,v4,v5,v11],[(v11,v3,v5),(v48,v11,v1),(v84,v3,v48),(v160,v84,v0)],[0],[]),
([v30,v145,v2,v3,v1,v7,v4],[],[],[]),
([v28,v84,v0,v2,v1,v4,v11],[(v11,v3,v5),(v48,v11,v1),(v84,v3,v48),(v28,v5,v48)],[0,1],[(5,299)]),
([v0,v139,v2,v3,v1,v4,v11],[(v11,v3,v5),(v48,v11,v1),(v28,v5,v48),(v139,v28,v0)],[0],[]),
([v0,v232,v2,v3,v1,v15,v5],[],[],[]),
([v30,v123,v0,v2,v3,v7,v4],[],[],[]),
([0xa0a0f0e0a0a0f0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xaaaaffee,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xa0a0f0f0a0a0e0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xccffccfc,v0,v2,v3,v1,v4,v5],[(v15,v3,v4),(v199,v15,v1),(0xccffccfcccffccfc,v199,v2),(0xccffccfc,0xccffccfcccffccfc,v5)],[1],[]),
([0xf0f00000f0f0f0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf000f000f0f0f0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xccfcccfc,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v192,v11,v1),(0xccffccffccfcccfc,v192,v2),(0xccfcccfc,0xccffccffccfcccfc,v5)],[1,3],[(0,216)]),
([0xaaaaeeee,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v161,v12,v4),(v140,v161,v0),(0xaaaaeeee,v140,v5)],[2,5],[(0,243)]),
([0xff00ffcc,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v161,v12,v4),(v236,v161,v1),(0xff00ffcc,v236,v5)],[2,5],[(0,298)]),
([v0,v2,v3,v1,0xffbbffbbffbbffaa,v4,v5],[(v7,v0,v1),(v14,v4,v5),(v128,v2,v14),(0xffbbffbbffbbffaa,v128,v7)],[0],[(0,300)]),
([0xaa88aa88aa88ffcc,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v14,v5,v4),(v200,v0,v14),(0xaa88aa88aa88ffcc,v200,v13)],[2],[]),
([v0,v2,v3,v1,0xffafffafffafffaa,v4,v5],[],[],[]),
([v0,0xaaaaaaff888888cc,v2,v3,v1,v4,v5],[(v12,v2,v5),(v10,v1,v4),(v93,v0,v10),(0xaaaaaaff888888cc,v93,v12)],[1,2,5],[]),
([v0,v162,v2,v3,v1,v4,v12],[(v12,v2,v5),(v10,v1,v4),(v37,v5,v10),(v162,v37,v0)],[2],[]),
([v37,v0,v2,v171,v1,v4,v11],[(v11,v3,v5),(v10,v4,v1),(v37,v5,v10),(v171,v37,v3)],[3],[]),
([v0,v181,v2,v3,v1,v15,v5],[],[],[]),
([v37,v0,v2,v3,v1,v4,v109],[(v12,v2,v5),(v10,v1,v4),(v37,v5,v10),(v109,v37,v12)],[2],[(0,302),(1,301)]),
([v51,v131,v0,v2,v3,v4,v5],[],[],[(3,303)]),
([v0,v2,v3,v1,0xffeeffeeffeeaaaa,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfffafffafffaf0f0,v4,v5],[(v7,v0,v1),(v14,v4,v5),(v119,v7,v14),(0xfffafffafffaf0f0,v3,v119)],[0,1],[]),
([v0,v2,v3,v1,v212,v14],[],[],[]),
([v51,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v14,v4,v5),(v119,v7,v14),(v51,v119,v7)],[4],[]),
([v65,v0,v2,v3,v1,v4,v14],[(v13,v2,v1),(v14,v5,v4),(v109,v13,v14),(v65,v5,v109)],[1],[(3,301)]),
([v38,v0,v2,v3,v1,v4,v16],[(v17,v0,v4),(v16,v1,v5),(v111,v17,v16),(v38,v5,v111)],[1,5],[(2,302)]),
([v0,v2,v3,v1,v4,v215,v14],[(v13,v2,v1),(v14,v5,v4),(0xffcc,v13,v14),(v215,0xffcc,v5)],[0,1],[]),
([v0,v2,v3,v1,v4,v154,v14],[(v7,v0,v1),(v14,v4,v5),(v51,v7,v14),(v154,v51,v5)],[1],[]),
([v0,v2,v3,v1,v4,v5,v111],[(v7,v0,v1),(v14,v4,v5),(v51,v7,v14),(v111,v51,v14)],[5],[]),
([v0,0xaaaaaaaaafafafaa,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xaaaaafafaaaaafaa,v2,v3,v1,v4,v5],[],[],[]),
([v76,v0,v2,v171,v1,v4,v5],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10),(v171,v76,v3)],[1],[(0,304)]),
([v76,v0,v2,v3,v1,v4,v172],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10),(v172,v76,v5)],[1],[(0,304)]),
([v0,v2,v171,v1,v4,v5,v11],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10),(v171,v76,v3)],[0,1],[]),
([v0,v2,v3,v1,v4,v172,v11],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10),(v172,v76,v5)],[0,1,5],[]),
([v27,v66,v2,v1,v18,v4,v5],[],[],[]),
([v24,v95,v0,v3,v1,v4,v23],[],[],[]),
([v31,v0,v2,v3,v1,v54,v4],[(v18,v3,v1),(v19,v0,v18),(v54,v2,v18),(v31,v19,v5)],[5],[(0,305)]),
([v0,0xaaaab8b8aaaab8b8,v2,v3,v1,v4,v5],[],[],[(3,232)]),
([v31,v251,v0,v2,v3,v1,v4],[],[],[]),
([v24,v114,v2,v3,v1,v4,v23],[(v23,v0,v5),(v44,v2,v23),(v114,v0,v44),(v24,v5,v44)],[0,2],[(0,136)]),
([v27,v0,v2,v1,v18,v126,v4],[(v18,v3,v1),(v19,v0,v18),(v27,v3,v19),(v126,v19,v5)],[1],[(0,137)]),
([v31,v27,v0,v2,v1,v18,v4],[(v18,v3,v1),(v19,v0,v18),(v27,v3,v19),(v31,v19,v5)],[1],[(0,138)]),
([v0,v130,v2,v3,v1,v22,v5],[],[],[]),
([v24,v0,v2,v3,v1,v4,v47],[(v23,v0,v5),(v44,v2,v23),(v24,v5,v44),(v47,v1,v23)],[1],[(0,129)]),
([v24,v123,v0,v2,v3,v1,v4],[],[],[]),
([v24,v0,v2,v3,v1,v122,v23],[(v23,v0,v5),(v44,v2,v23),(v24,v5,v44),(v122,v4,v44)],[0,1,2],[(0,139)]),
([v24,v164,v0,v2,v3,v1,v23],[(v23,v0,v5),(v44,v2,v23),(v24,v5,v44),(v164,v4,v44)],[0,1],[(0,140)]),
([v30,v0,v2,v3,v1,v4,v44],[(v23,v0,v5),(v44,v2,v23),(v47,v23,v1),(v30,v5,v47)],[2,5],[(0,209)]),
([v31,v0,v2,v3,v1,v4,v59],[],[],[]),
([v0,v2,v3,0xff00ee22ff00ee22,v1,v4,v5],[(v22,v2,v4),(v49,v0,v22),(v233,v22,v1),(0xff00ee22ff00ee22,v233,v49)],[4],[]),
([v28,v186,v0,v2,v3,v1,v5],[],[],[]),
([v0,v2,v3,0xff00fc30ff00fc30,v1,v4,v5],[(v22,v2,v4),(v45,v3,v22),(v233,v22,v1),(0xff00fc30ff00fc30,v233,v45)],[1],[]),
([v31,v0,v2,v3,v1,v18,v4],[],[],[]),
([v61,v0,v2,v1,v18,v4,v5],[(v18,v3,v1),(v54,v2,v18),(v92,v54,v4),(v61,v3,v92)],[1],[]),
([v31,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v70,v3,v23),(v116,v70,v1),(v31,v5,v116)],[0,1],[]),
([v98,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xdddcdddc,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfff3fff3fff2fff2,v4,v5],[(v23,v0,v5),(v95,v2,v23),(v206,v95,v3),(0xfff3fff3fff2fff2,v206,v1)],[0],[(0,306)]),
([0xafafaeae,v0,v2,v3,v1,v4,v5],[],[],[]),
([v42,v0,v2,0xf5f5f4f4f5f5f4f4,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(0x505040405050404,v42,v0),(0xf5f5f4f4f5f5f4f4,0x505040405050404,v3)],[1],[(2,172),(4,307)]),
([0xf0f03030f0f0202,v0,v2,v3,v1,v4,v5],[],[],[]),
([v98,v0,v2,v3,v1,v4,v224],[(v18,v3,v1),(v66,v0,v18),(v224,v66,v5),(v98,v5,v224)],[1],[(4,308)]),
([v0,v2,v3,v1,v4,0xffffff0fffffff0a,v5],[(v23,v0,v5),(v182,v3,v23),(v264,v182,v1),(0xffffff0fffffff0a,v264,v4)],[0],[(0,309)]),
([0xff0fff0c,v0,v2,v3,v1,v4,v5],[],[],[]),
([v98,v139,v2,v3,v1,v4,v5],[(v18,v3,v1),(v66,v0,v18),(v98,v66,v5),(v139,v98,v0)],[1],[(4,308)]),
([v0,0xaaaabbbaaaaabbba,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xff00ff00ff55ff44,v4,v5],[],[],[]),
([v42,v0,v2,v246,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(0xf000c000f000c,v42,v1),(v246,0xf000c000f000c,v3)],[1],[(0,308)]),
([0xf030f030f020f02,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xff55ff44,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xff22ff22,v0,v2,v3,v1,v159,v4],[(v23,v0,v5),(v95,v2,v23),(v159,v95,v1),(0xff22ff22,v159,v5)],[0],[]),
([0xff22ff22,v95,v0,v2,v3,v1,v4],[],[],[]),
([v42,v0,v2,v210,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v80,v42,v5),(v210,v80,v3)],[1],[(0,224)]),
([0xf0f0c0c0a0a0808,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xaaa0bbb0aaa0bbb0,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf0f0c0c0f000c00,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,0xaaaabbbbaa00bb00,v2,v3,v1,v4,v5],[],[],[]),
([0xcececece,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v182,v3,v23),(0xcfcfcfcfcececece,v182,v2),(0xcececece,0xcfcfcfcfcececece,v5)],[4],[(0,307)]),
([v28,v0,v2,v3,v1,v4,v224],[(v18,v3,v1),(v66,v0,v18),(v224,v66,v5),(v28,v5,v18)],[1],[(4,308),(5,310)]),
([0xff0aff0a,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v182,v3,v23),(v264,v182,v1),(0xff0aff0a,v264,v5)],[4],[(0,310)]),
([v0,v2,v3,v1,v178,v4,v5],[],[],[]),
([v28,v0,v2,v3,v1,v4,0xffffffff33303330],[(v18,v3,v1),(v251,v2,v18),(0xffffffff33303330,v251,v5),(v28,v5,v18)],[1],[(1,224),(5,311)]),
([0xff22ff22,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v95,v2,v23),(v159,v95,v1),(0xff22ff22,v159,v5)],[4],[(0,311)]),
([v0,0xaaaabbbbaaaa8888,v2,v3,v1,v4,v5],[],[],[(4,233)]),
([v0,0xaaaabb88aaaabb88,v2,v3,v1,v4,v5],[],[],[]),
([v30,v95,v0,v2,v3,v1,v4],[],[],[]),
([v0,v2,v3,v1,0xfffaeeeafffaeeea,v4,v5],[(v18,v3,v1),(v22,v2,v4),(v178,v18,v22),(0xfffaeeeafffaeeea,v0,v178)],[0],[(0,312)]),
([v0,v2,v3,v1,v4,0xffffffccffaaff88,v5],[],[],[]),
([0xfff0ccc0,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v246,v1,v18,v4,v5],[(v22,v2,v4),(v18,v3,v1),(0xf000c000f000c,v22,v18),(v246,0xf000c000f000c,v3)],[1,3],[]),
([v0,v2,v3,v1,v4,v224,v23],[(v18,v3,v1),(v23,v0,v5),(v98,v18,v23),(v224,v98,v5)],[0,1],[]),
([v0,v2,v3,v1,0xfff0fff0fffffffc,v4,v5],[],[],[]),
([v0,v2,v3,0xff00cc00ff55cc44,v1,v4,v5],[],[],[]),
([v28,v84,v0,v2,v1,v18,v4],[],[],[]),
([v30,v145,v2,v3,v1,v4,v23],[(v23,v0,v5),(v47,v23,v1),(v145,v0,v47),(v30,v5,v47)],[0,1],[(0,299)]),
([v0,v252,v2,v3,v1,v22,v5],[],[],[]),
([v0,v140,v2,v3,v1,v22,v5],[],[],[]),
([v30,v123,v0,v2,v3,v4,v23],[],[],[]),
([v0,v2,v3,v1,0xff00ff00ff55aa00,v4,v5],[],[],[]),
([v99,v0,v2,v1,v18,v4,v5],[(v18,v3,v1),(v59,v18,v4),(v141,v59,v5),(v99,v3,v141)],[1],[]),
([v38,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v47,v23,v1),(v111,v47,v4),(v38,v5,v111)],[0,1],[]),
([v106,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xa0a0a0a0f0f0e0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xccccfffc,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xa0f0a0e0a0f0a0e,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xaaaafffa,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf0f000f0f0f000a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf000f000f0f0f0c,v0,v2,v3,v1,v4,v5],[],[],[]),
([v107,v0,v2,v3,v1,v4,v194],[(v18,v3,v1),(v203,v18,v4),(v194,v203,v5),(v107,v5,v194)],[1],[(0,313)]),
([v0,0xaaaaaaaaaaaafffa,v2,v3,v1,v4,v5],[],[],[]),
([v28,v0,v2,v3,v1,v4,v194],[(v18,v3,v1),(v28,v18,v5),(v107,v28,v4),(v194,v107,v5)],[1],[(0,313)]),
([v0,v2,v3,v1,v179,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfff3fff3fff3fff0,v4,v5],[(v18,v3,v1),(v14,v5,v4),(v128,v2,v14),(0xfff3fff3fff3fff0,v128,v18)],[0],[]),
([0xaaa0aaa0aaa0fff0,v0,v2,v3,v1,v4,v5],[],[],[]),
([v0,v2,v3,v1,0xfffafffafffaaaaa,v4,v5],[(v18,v3,v1),(v14,v4,v5),(v179,v18,v14),(0xfffafffafffaaaaa,v0,v179)],[0],[]),
([v107,v0,v2,v3,v1,v4,v5],[],[],[]),
([v65,v0,v2,v3,v1,v4,v16],[(v22,v2,v4),(v16,v5,v1),(v109,v22,v16),(v65,v5,v109)],[1],[]),
([v38,v0,v2,v3,v1,v4,v10],[],[],[]),
([v0,v2,v3,v1,v4,v194,v14],[(v18,v3,v1),(v14,v5,v4),(v107,v18,v14),(v194,v107,v5)],[1],[]),
([v106,v162,v2,v3,v1,v4,v5],[(v23,v0,v5),(v10,v1,v4),(v106,v23,v10),(v162,v106,v0)],[1],[(4,314)]),
([v0,0xaaaabbbbaaaabbaa,v2,v3,v1,v4,v5],[],[],[]),
([v106,v0,v2,v3,v1,v4,v234],[(v23,v0,v5),(v10,v1,v4),(v106,v23,v10),(v234,v106,v5)],[1],[(4,314)]),
([v0,v2,v247,v1,v18,v4,v5],[(v18,v3,v1),(v14,v4,v5),(0xf000f000f0000,v18,v14),(v247,0xf000f000f0000,v3)],[1,3],[]),
([v0,v2,v3,v1,v4,v234,v23],[(v23,v0,v5),(v10,v1,v4),(v106,v23,v10),(v234,v106,v5)],[0,1],[]),
([v25,v73,v0,v3,v1,v4,v16],[(v16,v5,v1),(v26,v2,v16),(v73,v2,v16),(v25,v5,v26)],[0],[]),
([v28,v0,v2,v3,v1,v4,v26],[(v16,v5,v1),(v26,v2,v16),(v48,v3,v16),(v28,v5,v48)],[1,2],[(0,222)]),
([v30,v0,v2,v3,v1,v4,v26],[(v16,v1,v5),(v26,v2,v16),(v47,v0,v16),(v30,v5,v47)],[1,2,5],[(0,208)]),
([v38,v0,v2,v3,v1,v4,v43],[],[],[]),
([v0,0xaaaaaaaaaaaaf0f0,v2,v3,v1,v4,v5],[(v14,v4,v5),(v32,v3,v14),(v200,v0,v14),(0xaaaaaaaaaaaaf0f0,v200,v32)],[0],[(3,265)]),
([v38,v36,v0,v2,v3,v1,v4],[],[],[]),
([v0,v201,v2,v3,v1,v5,v14],[],[],[]),
([v0,v2,v3,v1,v223,v4,v14],[],[],[]),
([v51,v0,v2,v3,v1,v10,v5],[(v10,v4,v1),(v21,v0,v10),(v74,v4,v21),(v51,v74,v5)],[1],[(0,315)]),
([v25,v0,v2,v3,v4,v10,v16],[],[],[(0,273),(2,315),(3,316)]),
([v25,v78,v0,v2,v3,v4,v16],[(v16,v5,v1),(v26,v2,v16),(v25,v5,v26),(v78,v1,v26)],[1,2],[(0,282)]),
([v25,v0,v2,v3,v1,v153,v16],[(v16,v5,v1),(v26,v2,v16),(v25,v5,v26),(v153,v4,v26)],[0,1],[(0,280)]),
([v25,v136,v0,v2,v3,v1,v16],[(v16,v5,v1),(v26,v2,v16),(v25,v5,v26),(v136,v4,v26)],[0,1],[(0,281)]),
([v0,v2,v3,v10,v21,v16,v14],[(v10,v4,v1),(v21,v0,v10),(v14,v4,v5),(v16,v1,v5)],[0,1,4,5],[(0,315),(1,315),(4,268)]),
([v37,v0,v2,v3,v1,v21,v14],[(v10,v4,v1),(v21,v0,v10),(v14,v4,v5),(v37,v5,v10)],[0,5],[]),
([v38,v0,v2,v3,v1,v10,v14],[(v10,v4,v1),(v21,v0,v10),(v14,v4,v5),(v38,v5,v21)],[1],[(1,315)]),
([v37,v0,v2,v3,v1,v4,v26],[(v16,v5,v1),(v26,v2,v16),(v50,v16,v4),(v37,v5,v50)],[1,2],[(0,302)]),
([v38,v0,v2,v3,v1,v4,v50],[(v10,v1,v4),(v21,v0,v10),(v50,v10,v5),(v38,v21,v5)],[1,4],[(0,290),(2,302),(3,302)]),
([v0,v2,v3,v257,v1,v4,v5],[(v14,v4,v5),(v32,v3,v14),(v131,v14,v1),(v257,v131,v32)],[0,1,5],[(0,317)]),
([v51,v38,v0,v2,v3,v1,v10],[(v10,v4,v1),(v21,v0,v10),(v38,v21,v5),(v51,v38,v4)],[1],[(0,318)]),
([0xb0b0b0b0b0a0b0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xddddddcc,v0,v2,v3,v1,v4,v5],[],[],[]),
([v40,v0,v2,v260,v1,v4,v5],[(v14,v5,v4),(v40,v3,v14),(v261,v40,v2),(v260,v261,v3)],[1],[(1,179),(1,319)]),
([0xf0f03030f0f0300,v0,v2,v3,v1,v4,v5],[],[],[]),
([v40,v0,v2,v247,v1,v4,v5],[(v14,v4,v5),(v40,v3,v14),(0xf000f000f0000,v40,v1),(v247,0xf000f000f0000,v3)],[1],[(0,314),(1,320),(4,320)]),
([v0,0xaaaaaaffaa00aa00,v2,v3,v4,v5,v16],[],[],[(0,321)]),
([v40,v73,v0,v2,v3,v1,v4],[],[],[(0,322)]),
([v40,v0,v2,v3,v10,v16],[(v14,v5,v4),(v40,v3,v14),(v16,v1,v5),(v10,v1,v4)],[0,3,5],[(0,267),(0,268),(0,322),(2,267),(2,322),(3,321),(5,321)]),
([v37,v40,v0,v2,v3,v1,v10],[(v14,v4,v5),(v40,v3,v14),(v10,v1,v4),(v37,v5,v10)],[5],[]),
([v36,v0,v2,0xf5f5f5f0f5f5f5f0,v1,v4,v5],[(v10,v4,v1),(v93,v0,v10),(0xf5f5f5f0f5f5f5f0,v93,v3),(v36,v3,v10)],[1],[(2,179)]),
([v37,v0,v2,v3,v1,v4,v234],[(v10,v1,v4),(v93,v0,v10),(v234,v93,v5),(v37,v5,v10)],[1],[(4,314)]),
([v0,0xaaaaaaccaaaaaacc,v2,v3,v1,v4,v5],[],[],[]),
([v28,v73,v0,v2,v3,v1,v4],[(v16,v5,v1),(v73,v2,v16),(v48,v3,v16),(v28,v5,v48)],[1],[]),
([v30,v73,v0,v2,v3,v1,v4],[(v16,v1,v5),(v73,v2,v16),(v47,v0,v16),(v30,v5,v47)],[1],[]),
([v40,v0,v2,v3,v10,v16,v14],[(v14,v5,v4),(v40,v3,v14),(v16,v1,v5),(v10,v1,v4)],[0,1,3,5],[(0,268)]),
([v37,v93,v0,v2,v3,v1,v14],[(v10,v4,v1),(v93,v0,v10),(v14,v5,v4),(v37,v5,v10)],[5],[]),
([v0,0xaaaaaaffaaaaaa00,v2,v3,v1,v4,v5],[],[],[]),
([v37,v40,v0,v2,v3,v1,v4],[],[],[]),
([v30,v145,v2,v3,v1,v4,v16],[],[],[]),
([v28,v84,v0,v2,v1,v4,v16],[],[],[]),
([v0,0xaaaaaaaaaaaacccc,v2,v3,v1,v4,v5],[],[],[(2,262)]),
([v0,v2,v3,v1,v222,v4,v14],[(v14,v5,v4),(v117,v2,v14),(v157,v5,v117),(v222,v157,v1)],[5],[]),
([v107,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v48,v3,v16),(v28,v5,v48),(v107,v28,v4)],[1],[(0,323)]),
([v28,v0,v2,v3,v4,v10,v16],[],[],[(0,323),(3,324)]),
([v30,v123,v0,v2,v3,v4,v16],[(v16,v1,v5),(v47,v0,v16),(v123,v1,v47),(v30,v5,v47)],[1,4],[(0,299)]),
([v0,v2,v3,v10,v43,v16,v14],[(v10,v1,v4),(v43,v2,v10),(v16,v1,v5),(v14,v4,v5)],[0,1,2],[(1,323),(2,315)]),
([v30,v0,v2,v3,v4,v10,v16],[(v16,v1,v5),(v47,v0,v16),(v10,v1,v4),(v30,v5,v47)],[5],[(0,315),(3,325)]),
([v65,v0,v2,v3,v4,v10,v16],[(v10,v1,v4),(v43,v2,v10),(v16,v1,v5),(v65,v5,v43)],[0],[(2,315)]),
([v0,v140,v2,v3,v1,v5,v14],[],[],[]),
([v0,v2,v3,v1,v152,v4,v14],[(v14,v4,v5),(v67,v0,v14),(v132,v5,v67),(v152,v132,v1)],[1,5],[]),
([v51,v0,v2,v3,v1,v4,v16],[(v16,v1,v5),(v47,v0,v16),(v30,v5,v47),(v51,v30,v4)],[1],[(0,315)]),
([v65,v0,v2,v3,v1,v10,v14],[],[],[(1,323)]),
([v37,v0,v2,v3,v1,v4,v48],[(v16,v5,v1),(v48,v3,v16),(v50,v16,v4),(v37,v5,v50)],[3],[(0,301)]),
([v65,v0,v2,v3,v1,v4,v50],[(v10,v1,v4),(v43,v2,v10),(v50,v10,v5),(v65,v43,v5)],[1],[(0,291),(3,301)]),
([v0,v2,v3,0xff00ff00ff00aaaa,v1,v4,v5],[(v14,v4,v5),(v67,v0,v14),(v131,v14,v1),(0xff00ff00ff00aaaa,v131,v67)],[4],[]),
([0xb0b0b0a0b0b0b0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xafafafaa,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xb0b0b0b0b0b0a0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xcfcfcfcc,v0,v2,v3,v1,v4,v5],[],[],[]),
([v36,v0,v2,v190,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v101,v36,v2),(v190,v101,v3)],[1],[(0,182),(0,264),(3,326)]),
([0xf0f05050f0f0500,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xf030f030f030f00,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xff33ff00,v0,v2,v3,v1,v183,v4],[(v14,v5,v4),(v128,v2,v14),(v183,v128,v1),(0xff33ff00,v183,v5)],[0],[]),
([0xff33ff00,v128,v0,v2,v3,v1,v4],[],[],[]),
([v36,v0,v2,v171,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v76,v36,v5),(v171,v76,v3)],[1],[(0,304),(3,327),(4,328)]),
([0xcfcccfcc,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v84,v3,v16),(v242,v84,v2),(0xcfcccfcc,v242,v5)],[1],[(0,319)]),
([0xafaaafaa,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v84,v3,v16),(v160,v84,v0),(0xafaaafaa,v160,v5)],[1],[(0,326)]),
([v37,v0,v2,v3,v1,v4,v172],[(v10,v4,v1),(v36,v3,v10),(v172,v36,v5),(v37,v5,v10)],[1],[(0,304),(4,329)]),
([0xff33ff00,v0,v2,v3,v1,v4,v14],[(v14,v5,v4),(v128,v2,v14),(v183,v128,v1),(0xff33ff00,v183,v5)],[5],[(0,329)]),
([v36,v0,v2,v3,v10,v16,v14],[(v10,v4,v1),(v36,v3,v10),(v16,v1,v5),(v14,v4,v5)],[1,5],[]),
([v0,0xaaaaaaaaaaaaff00,v2,v3,v1,v4,v5],[],[],[]),
([v37,v84,v0,v2,v3,v1,v4],[],[],[]),
([v0,v181,v2,v3,v1,v16,v14],[],[],[(3,330)]),
([v37,v120,v0,v2,v3,v10,v16],[(v16,v1,v5),(v10,v1,v4),(v37,v5,v10),(v120,v4,v16)],[1,5],[]),
([v0,0xafafafafafafafaa,v2,v3,v1,v4,v5],[],[],[]),
([v37,v99,v0,v2,v3,v1,v4],[],[],[]),
([v37,v120,v0,v2,v3,v1],[],[],[]),
([v37,v120,v0,v2,v3,v1,v50],[],[],[(0,331)]),
([v0,v181,v2,v3,v1,v5,v14],[],[],[]),
([v37,v120,v0,v2,v3,v1,v10],[],[],[]),
([v37,v120,v0,v2,v3,v1,v14],[(v14,v5,v4),(v50,v14,v1),(v37,v5,v50),(v120,v4,v50)],[1],[(0,331)]),
([0xa0a0a0a0f0f0f0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xa0f0a0f0a0f0a0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xa0a0f0f0a0a0f0a,v0,v2,v3,v1,v4,v5],[],[],[]),
([0xccccffcc,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v120,v16,v4),(0xccccffffccccffcc,v120,v2),(0xccccffcc,0xccccffffccccffcc,v5)],[1],[(0,320)]),
([0xccffcccc,v0,v2,v3,v1,v4,v14],[(v14,v5,v4),(v131,v14,v1),(0xccffccffccffcccc,v131,v2),(0xccffcccc,0xccffccffccffcccc,v5)],[1],[(0,328),(0,330)]),
([0xaaaaffaa,v0,v2,v3,v1,v4,v16],[(v16,v1,v5),(v120,v16,v4),(v181,v120,v0),(0xaaaaffaa,v181,v5)],[1],[(0,327)])
]

set_option maxRecDepth 100000 in

def g6_L7 : Array W6Node := Array.mk [
([v6,v9,v8,v1,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v6,v0,v2)],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5),(2,0),(2,2),(2,3),(2,4),(2,5),(2,6),(3,0),(3,2),(3,3),(3,4),(3,5),(3,6),(4,1),(4,4),(4,5),(5,4),(5,5)]),
([v34,v0,v6,v8,v1,v4,v5],[(v8,v2,v3),(v6,v2,v0),(v34,v3,v6)],[1,2,3,4],[(0,7),(0,11),(2,8),(2,9),(2,10),(3,12)]),
([v0,v6,v8,v1,v4,v15,v5],[(v8,v2,v3),(v6,v2,v0),(v15,v3,v4)],[0,2,3,4,5],[(0,17),(0,18),(0,19),(0,22),(1,15),(2,0),(2,8),(2,13),(3,16),(3,20),(4,10),(4,14),(4,21)]),
([v0,v2,v9,v8,v1,v19,v4,v5],[(v9,v3,v0),(v8,v3,v2),(v19,v9,v1)],[0,2,4],[(0,4),(0,25),(0,26),(1,17),(1,24),(4,23)]),
([v24,v2,v6,v3,v9,v1,v4,v5],[(v6,v0,v2),(v9,v0,v3),(v24,v6,v5)],[0,2,3,4],[(0,5),(0,8),(0,21)]),
([v0,v2,v9,v1,v4,v5,v41],[(v8,v3,v2),(v9,v3,v0),(v41,v8,v5)],[0,2,3,4],[(0,0),(0,30),(2,15),(3,28),(4,27),(4,29)]),
([v0,v2,v9,v8,v1,v4,v46,v5],[(v9,v3,v0),(v8,v3,v2),(v46,v9,v4)],[2,4,5],[(1,1),(1,11),(1,32),(1,33),(2,30),(5,31)]),
([v39,v0,v2,v9,v1,v4,v5],[(v8,v3,v2),(v9,v3,v0),(v39,v8,v5)],[0,2,3,4],[(0,2),(0,16),(0,30),(0,34),(1,35)]),
([v39,v0,v2,v9,v8,v1,v4,v5],[(v8,v3,v2),(v9,v3,v0),(v39,v8,v5)],[0,4],[(0,3),(0,12),(0,30)]),
([v0,v2,v9,v8,v1,v4,v45,v5],[(v8,v3,v2),(v9,v3,v0),(v45,v8,v4)],[1,4,5],[(2,38),(3,4),(3,37),(3,39),(5,36)]),
([v24,v0,v6,v3,v8,v1,v4,v5],[(v6,v2,v0),(v8,v2,v3),(v24,v6,v5)],[0,3,4],[(0,5),(0,35)]),
([v0,v2,v9,v8,v1,v4,v10,v5],[(v9,v3,v0),(v8,v3,v2),(v10,v1,v4)],[4],[(0,6),(1,22)]),
([v0,v2,v9,v8,v1,v4,v5,v14],[(v9,v3,v0),(v8,v3,v2),(v14,v4,v5)],[4],[(3,6)]),
([v0,v8,v1,v13,v4,v15,v5],[(v8,v3,v2),(v15,v3,v4),(v13,v2,v1)],[0,1,2,3,5],[(0,15),(0,40),(0,43),(0,44),(0,45),(0,46),(1,15),(1,40),(1,44),(1,46),(2,47),(3,47),(4,41),(4,42),(5,41),(5,42)]),
([v27,v2,v9,v1,v7,v4,v5],[(v9,v0,v3),(v7,v0,v1),(v27,v3,v7)],[1,3,4,5],[(0,20),(0,47),(0,50),(0,51),(0,52),(0,54),(2,48),(3,53),(4,49)]),
([v0,v2,v9,v20,v1,v4,v5,v11],[(v9,v3,v0),(v11,v3,v5),(v20,v2,v9)],[0,1,2,4,5],[(0,58),(0,59),(2,57),(3,56),(4,55)]),
([v34,v0,v6,v3,v1,v4,v5,v12],[(v6,v2,v0),(v12,v2,v5),(v34,v3,v6)],[0,2,3,4],[(0,10),(0,60)]),
([v0,v2,v9,v1,v13,v4,v5,v11],[(v9,v3,v0),(v11,v3,v5),(v13,v2,v1)],[0,1,4],[(0,61),(4,15),(4,40)]),
([v0,v2,v9,v1,v4,v22,v5,v11],[(v9,v3,v0),(v11,v3,v5),(v22,v2,v4)],[0,4,5],[(1,62)]),
([v0,v2,v9,v1,v4,v12,v11],[(v9,v3,v0),(v11,v3,v5),(v12,v2,v5)],[0,2,3,4,5],[(0,13),(0,61),(0,64),(0,65),(0,66),(1,60),(2,40),(3,63),(4,67),(5,50),(5,68)]),
([v0,v2,v9,v1,v4,v5,v11,v41],[(v9,v3,v0),(v11,v3,v5),(v41,v2,v11)],[0,2,4],[(0,71),(1,14),(3,28),(4,69),(4,70),(5,51)]),
([v33,v2,v6,v3,v1,v4,v5],[(v6,v0,v2),(v17,v0,v4),(v33,v3,v17)],[2,3,4,5],[(0,28),(0,41),(1,72),(5,73)]),
([v33,v2,v6,v3,v1,v4,v17,v5],[(v6,v0,v2),(v17,v0,v4),(v33,v3,v17)],[2,3,4,5],[(0,28),(0,63),(1,20),(1,52)]),
([v0,v2,v9,v1,v19,v4,v5,v11],[(v9,v3,v0),(v11,v3,v5),(v19,v9,v1)],[0,4],[(0,75),(0,76),(4,74)]),
([v24,v2,v6,v3,v1,v4,v17,v5],[(v6,v0,v2),(v17,v0,v4),(v24,v6,v5)],[0,4,5],[(0,42),(2,77)]),
([v0,v2,v9,v1,v4,v46,v5,v11],[(v9,v3,v0),(v11,v3,v5),(v46,v9,v4)],[0,4,5],[(0,80),(1,79),(5,78)]),
([v39,v0,v2,v8,v1,v4,v15,v5],[(v8,v3,v2),(v15,v3,v4),(v39,v8,v5)],[0,5],[(2,81)]),
([v24,v0,v6,v3,v1,v4,v12],[(v6,v2,v0),(v12,v2,v5),(v24,v6,v5)],[0,1,2,4],[(0,21),(0,42),(0,53),(0,60),(0,77),(1,83),(3,82)]),
([v0,v2,v9,v1,v4,v10,v5,v11],[(v9,v3,v0),(v11,v3,v5),(v10,v1,v4)],[0,4,5],[(0,84),(0,85)]),
([v0,v2,v9,v1,v4,v11,v16],[(v9,v3,v0),(v11,v3,v5),(v16,v1,v5)],[0,1,3,4,5],[(0,61),(0,84),(0,87),(0,88),(0,89),(1,77),(1,86),(2,22),(2,43),(2,90),(5,54),(5,91)]),
([v0,v2,v9,v1,v4,v5,v11,v48],[(v9,v3,v0),(v11,v3,v5),(v48,v1,v11)],[0,4],[(0,94),(2,93),(4,44),(4,92)]),
([v30,v2,v3,v9,v1,v7,v4,v5],[(v9,v0,v3),(v7,v0,v1),(v30,v5,v7)],[0,1,3,4],[(0,47),(0,91)]),
([v0,v2,v9,v1,v4,v5,v11,v32],[(v9,v3,v0),(v11,v3,v5),(v32,v4,v11)],[0,1,4,5],[(1,98),(3,97),(4,96),(5,95)]),
([v25,v0,v3,v8,v1,v13,v4,v5],[(v8,v2,v3),(v13,v2,v1),(v25,v5,v13)],[0,1,3],[]),
([v34,v0,v2,v20,v1,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20)],[1,2,4],[(0,99),(0,100),(0,101),(0,103),(0,104),(2,99),(2,100),(2,103),(2,104),(3,102)]),
([v0,v2,v3,v77,v20,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v77,v20,v1)],[0,1,2,3,4,5],[(0,101),(0,107),(0,108),(0,109),(0,110),(0,111),(0,112),(1,103),(2,107),(2,108),(2,109),(2,110),(2,111),(2,112),(3,105),(3,106),(4,103)]),
([v0,v2,v3,v1,v52,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v52,v20,v1)],[0,1,2,3,4,5],[(0,114),(0,117),(0,118),(0,119),(0,120),(1,113),(1,116),(2,117),(2,118),(2,119),(2,120),(3,105),(3,115),(4,113),(4,116)]),
([v0,v2,v3,v20,v1,v52,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v52,v20,v1)],[0,1,5],[(0,122),(0,123),(0,124),(1,109),(1,121),(2,123),(2,124),(3,106),(3,115),(4,109),(4,121)]),
([v35,v0,v2,v3,v1,v4],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0,1,2,3,4,5],[(0,125),(0,126),(0,127),(1,125),(1,126)]),
([v35,v0,v2,v3,v20,v1,v4],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0,1,2,3,4,5],[(0,102),(0,104),(0,110),(0,111),(0,123),(0,128),(0,129),(0,130),(1,104),(1,110),(1,111),(1,123),(1,128),(1,129),(1,130)]),
([v35,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0,1,2,3,4,5],[(0,115),(0,131),(0,132),(0,133),(1,131),(1,132),(1,133)]),
([v35,v0,v2,v3,v20,v1,v4,v5],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0],[(0,112),(0,115),(1,112),(2,130),(3,130)]),
([v0,v2,v3,v20,v1,v4,v10,v5],[(v6,v0,v2),(v20,v6,v3),(v10,v1,v4)],[0,1,5],[(0,117),(0,127),(0,134),(0,135),(2,133),(3,133),(4,132)]),
([v34,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20)],[1,2,3,4],[(0,59),(0,99),(0,136),(1,137),(2,55)]),
([v34,v0,v2,v9,v20,v1,v4,v5],[(v9,v3,v0),(v20,v9,v2),(v34,v3,v20)],[1,2,4],[(0,100),(0,139),(0,141),(0,143),(0,144),(1,137),(2,138),(2,142),(3,140)]),
([v34,v0,v2,v6,v20,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v34,v6,v3)],[1,3],[(0,137),(2,137)]),
([v0,v2,v3,v20,v1,v29,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v29,v6,v1)],[0,1,3,5],[(0,122),(0,146),(2,146),(3,145)]),
([v39,v0,v2,v3,v20,v1,v4,v5],[(v8,v2,v3),(v20,v8,v0),(v39,v8,v5)],[0,1,4,5],[(0,148),(1,148),(4,147)]),
([v0,v2,v3,v20,v1,v19,v4,v5],[(v9,v0,v3),(v20,v9,v2),(v19,v9,v1)],[0,1,2,5],[(0,151),(0,152),(1,121),(2,150),(3,149)]),
([v24,v0,v2,v3,v20,v1,v4,v5],[(v6,v2,v0),(v20,v6,v3),(v24,v6,v5)],[0,1,3,5],[(0,154),(0,155),(5,153)]),
([v0,v2,v6,v3,v77,v20,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v77,v20,v1)],[3],[(0,101),(0,157),(0,158),(1,141),(2,157),(2,158),(3,156),(4,141)]),
([v0,v2,v6,v3,v1,v52,v4,v5],[(v6,v0,v2),(v20,v6,v3),(v52,v20,v1)],[0,5],[(0,161),(1,159),(2,161),(3,156),(3,160),(4,159)]),
([v35,v0,v2,v3,v8,v1,v4],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0,1,2,3,4,5],[(0,57),(0,150),(1,57),(1,150),(4,154),(5,154)]),
([v35,v0,v2,v3,v8,v20,v1,v4],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0,4],[(0,102),(0,142),(0,162),(1,142),(1,162),(2,163),(3,163)]),
([v35,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v20,v8,v0),(v35,v20,v5)],[0,4],[(0,145)]),
([v0,v2,v6,v3,v113,v20,v1,v5],[(v6,v0,v2),(v20,v6,v3),(v113,v20,v4)],[3],[(0,103),(0,157),(0,165),(0,166),(1,139),(2,164),(3,162),(4,143)]),
([v0,v2,v6,v3,v1,v4,v96,v5],[(v6,v0,v2),(v20,v6,v3),(v96,v20,v4)],[0,1],[(1,168),(1,171),(2,164),(3,169),(3,170),(5,167)]),
([v35,v0,v2,v6,v3,v1,v4],[(v6,v2,v0),(v20,v6,v3),(v35,v20,v5)],[0,1,2,3,4,5],[(0,56),(0,146),(1,151),(1,172),(2,155),(3,148)]),
([v35,v0,v2,v6,v3,v20,v1,v4],[(v6,v2,v0),(v20,v6,v3),(v35,v20,v5)],[0,3],[(0,104),(0,140),(0,158),(0,166),(0,173),(1,144),(1,163)]),
([v35,v0,v2,v6,v3,v1,v4,v5],[(v6,v2,v0),(v20,v6,v3),(v35,v20,v5)],[0,2,3],[(0,149),(1,58),(1,59)]),
([v0,v2,v3,v1,v165,v4,v5],[(v6,v0,v2),(v34,v6,v3),(v165,v34,v1)],[0,1,2,3,4,5],[(0,175),(0,176),(2,175),(2,176),(3,174)]),
([v34,v0,v2,v3,v1,v165,v4,v5],[(v6,v0,v2),(v34,v6,v3),(v165,v34,v1)],[1],[(3,174)]),
([v97,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v97,v64,v5)],[0,1,2,3,4,5],[(0,174),(0,177),(0,178),(1,178),(2,179),(3,179)]),
([v97,v64,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v97,v64,v5)],[0],[(0,174),(4,180)]),
([v0,v2,v3,v1,v173,v4,v5],[(v9,v0,v3),(v81,v9,v2),(v173,v81,v1)],[0,1,2,3,4,5],[(0,185),(0,186),(0,187),(1,175),(2,182),(2,184),(3,181),(4,183)]),
([v34,v0,v2,v3,v1,v4,v248,v5],[(v6,v0,v2),(v34,v6,v3),(v248,v34,v4)],[0,5],[(1,188),(2,181)]),
([v55,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5)],[0,1,2,3,4,5],[(0,181),(0,189),(0,190),(0,192),(0,193),(1,179),(1,191)]),
([v55,v34,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5)],[0],[(0,181),(0,194)]),
([v34,v0,v2,v3,v1,v4,v10,v5],[(v6,v0,v2),(v34,v6,v3),(v10,v1,v4)],[3,5],[(0,175),(0,195),(0,197),(2,193),(3,196),(4,179)]),
([v34,v0,v2,v3,v1,v4,v5,v14],[],[],[(0,192),(0,198),(3,184),(3,199)]),
([v0,v2,v6,v3,v1,v165,v4,v5],[(v6,v0,v2),(v34,v6,v3),(v165,v34,v1)],[1,2,3,4],[(1,200),(3,201),(4,200)]),
([v97,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v97,v64,v5)],[0],[(0,203),(4,202)]),
([v0,v2,v6,v3,v1,v4,v248,v5],[(v6,v0,v2),(v34,v6,v3),(v248,v34,v4)],[0,2,3,4,5],[(0,7),(1,205),(1,207),(2,206),(5,204)]),
([v55,v0,v2,v6,v3,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v55,v34,v5)],[0,4],[(0,8),(0,60),(0,209),(2,208)]),
([v34,v0,v2,v3,v1,v29,v4,v5],[(v6,v0,v2),(v34,v6,v3),(v29,v6,v1)],[1,4],[(0,11),(2,11),(3,203),(3,210)]),
([v39,v64,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v64,v8,v0),(v39,v8,v5)],[0,4],[(0,12),(0,201),(1,12),(4,180)]),
([v34,v0,v2,v3,v1,v4,v49,v5],[(v6,v0,v2),(v34,v6,v3),(v49,v6,v4)],[0,5],[(1,212),(2,209),(3,211)]),
([v24,v34,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v34,v6,v3),(v24,v6,v5)],[0,3],[(0,194),(0,206)]),
([v33,v0,v2,v1,v4,v46,v5],[(v9,v3,v0),(v46,v9,v4),(v33,v3,v46)],[1,4,5],[(0,28),(0,214),(0,215),(0,216),(1,29),(2,213),(2,217),(2,218)]),
([v0,v2,v3,v1,v4,v23,v41],[(v8,v2,v3),(v41,v8,v5),(v23,v0,v5)],[0,2,3,4],[(0,203),(2,216),(3,216),(4,219)]),
([v0,v2,v3,v1,v29,v52,v4,v5],[(v6,v0,v2),(v29,v6,v1),(v52,v3,v29)],[0,3,5],[(0,114),(0,221),(1,220),(2,221),(3,145),(4,220)]),
([v72,v0,v2,v3,v1,v4,v5],[(v6,v0,v2),(v29,v6,v1),(v72,v3,v29)],[0,1,2,3,4,5],[(0,114),(0,223),(1,222),(2,223),(4,222)]),
([v72,v0,v2,v3,v1,v29,v4,v5],[(v6,v0,v2),(v29,v6,v1),(v72,v3,v29)],[1,2,3,4],[(0,27),(0,29),(0,114),(0,219),(2,27),(2,29),(3,203)]),
([v0,v2,v3,v1,v7,v4,v5,v41],[(v8,v2,v3),(v41,v8,v5),(v7,v0,v1)],[1],[(0,225),(0,226),(2,15),(2,117),(3,224),(5,223)]),
([v39,v0,v2,v3,v1,v4,v41],[(v8,v2,v3),(v41,v8,v5),(v39,v5,v41)],[0,1,2,3,4],[(0,30),(0,203),(0,217),(0,218),(0,227),(1,30),(1,217),(1,218)]),
([v0,v2,v3,v1,v4,v53,v5],[(v6,v0,v2),(v29,v6,v1),(v53,v29,v4)],[0,1,2,3,4,5],[(0,117),(0,231),(0,232),(0,233),(0,237),(0,238),(0,239),(0,240),(1,229),(2,235),(3,230),(3,234),(4,224),(4,228),(4,236)]),
([v0,v2,v3,v1,v29,v4,v53,v5],[(v6,v0,v2),(v29,v6,v1),(v53,v29,v4)],[0,3,5],[(0,243),(0,245),(1,242),(2,235),(3,244),(4,241)]),
([v62,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v29,v6,v1),(v62,v29,v5)],[0,1,2,3,4,5],[(0,223),(0,235),(0,248),(1,247),(3,246)]),
([v62,v0,v2,v3,v1,v29,v4,v5],[(v6,v2,v0),(v29,v6,v1),(v62,v29,v5)],[0],[(0,235)]),
([v0,v2,v3,v1,v29,v4,v5,v14],[(v6,v0,v2),(v29,v6,v1),(v14,v4,v5)],[1],[(0,237),(0,248),(0,250),(3,249),(3,251)]),
([v33,v0,v2,v9,v1,v4,v5],[(v9,v3,v0),(v46,v9,v4),(v33,v3,v46)],[1,3,4,5],[(0,31),(0,78),(0,80),(0,253),(0,254),(1,33),(2,217),(2,252),(2,255)]),
([v33,v0,v2,v9,v1,v4,v46,v5],[(v9,v3,v0),(v46,v9,v4),(v33,v3,v46)],[1,4,5],[(0,256),(2,218),(2,255)]),
([v39,v0,v2,v3,v8,v1,v4,v41],[(v8,v2,v3),(v41,v8,v5),(v39,v8,v5)],[0,1],[(0,255),(1,255)]),
([v0,v2,v3,v1,v29,v4,v49,v5],[(v6,v0,v2),(v29,v6,v1),(v49,v6,v4)],[0,1,5],[(1,258),(2,257),(3,244)]),
([v24,v0,v2,v3,v1,v29,v4,v5],[(v6,v2,v0),(v29,v6,v1),(v24,v6,v5)],[0],[(0,260),(5,259)]),
([v0,v2,v6,v3,v29,v18,v4,v5],[(v6,v0,v2),(v29,v6,v1),(v18,v3,v1)],[1,3],[(0,261),(1,254),(3,203),(4,254)]),
([v72,v0,v2,v6,v3,v1,v4,v5],[(v6,v0,v2),(v29,v6,v1),(v72,v3,v29)],[1,2,3,4],[(0,32),(0,33),(0,122),(2,32),(2,33)]),
([v0,v2,v6,v3,v1,v4,v53,v5],[(v6,v0,v2),(v29,v6,v1),(v53,v29,v4)],[0,3,5],[(0,265),(0,266),(1,263),(2,260),(3,264),(4,262)]),
([v62,v0,v2,v6,v3,v1,v4,v5],[(v6,v2,v0),(v29,v6,v1),(v62,v29,v5)],[0,1],[(0,79),(0,257),(1,80)]),
([v0,v137,v2,v3,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v137,v39,v0)],[0,1,2,3,4,5],[(0,177),(0,267),(1,267),(2,268),(3,268)]),
([v39,v0,v137,v2,v3,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v137,v39,v0)],[0,4],[(0,177),(0,227)]),
([v97,v39,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v97,v39,v0)],[4],[(0,177),(0,201),(0,203)]),
([v0,v2,v3,v1,v225,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v225,v39,v1)],[0,1,2,3,4,5],[(0,267),(0,272),(2,273),(3,269),(3,271),(4,270)]),
([v39,v0,v2,v3,v1,v225,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v225,v39,v1)],[1],[(3,271)]),
([v108,v0,v2,v3,v1,v4,v5],[(v9,v3,v0),(v115,v9,v4),(v108,v115,v5)],[0,1,2,3,4,5],[(0,179),(0,271),(0,275),(0,277),(1,276),(2,274)]),
([v108,v115,v0,v2,v3,v1,v4,v5],[(v9,v3,v0),(v115,v9,v4),(v108,v115,v5)],[0],[(0,271),(2,278)]),
([v39,v0,v2,v3,v1,v7,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v7,v0,v1)],[0,1],[(0,16),(0,267),(0,279),(0,281),(3,179),(3,269),(4,280)]),
([v39,v0,v2,v3,v1,v4,v10,v5],[],[],[(0,272),(0,282),(4,276),(4,283)]),
([v0,v137,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v137,v39,v0)],[0,4],[(0,227),(4,180)]),
([v0,v2,v6,v3,v1,v4,0xffff00eeffff00ee,v5],[(v6,v0,v2),(v195,v6,v1),(0xffff00eeffff00ee,v195,v4)],[1,5],[(2,284),(4,81)]),
([v108,v0,v2,v3,v9,v1,v4,v5],[(v9,v3,v0),(v115,v9,v4),(v108,v115,v5)],[4],[(3,285)]),
([v39,v0,v2,v3,v1,v54,v4,v5],[(v8,v2,v3),(v39,v8,v5),(v54,v8,v1)],[5],[(0,287),(4,286)]),
([v24,v195,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v195,v6,v1),(v24,v6,v5)],[0,1],[(0,284),(3,278)]),
([v42,v0,v2,v1,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v42,v3,v45)],[1,2,5],[(0,288),(0,291),(3,289),(3,290),(3,292),(4,293),(4,294)]),
([v0,v2,v3,v1,v4,v12,v70],[(v9,v3,v0),(v70,v9,v5),(v12,v2,v5)],[0,1,2,3,4],[(0,224),(1,209),(2,288),(2,297),(3,296),(4,299),(5,295),(5,298)]),
([v0,v2,v3,v1,v19,v52,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v52,v2,v19)],[0,2,5],[(0,301),(0,303),(0,305),(1,113),(2,304),(3,149),(4,300),(4,302)]),
([v56,v0,v2,v3,v1,v4,v5],[(v6,v0,v2),(v49,v6,v4),(v56,v3,v49)],[0,1,2,3,4,5],[(0,113),(0,306),(0,309),(3,307),(4,308)]),
([v56,v0,v2,v3,v1,v4,v49,v5],[(v6,v0,v2),(v49,v6,v4),(v56,v3,v49)],[3,5],[(0,113),(0,296),(0,310),(1,311),(2,209)]),
([v0,v2,v3,v1,v18,v4,v49,v5],[(v6,v0,v2),(v49,v6,v4),(v18,v3,v1)],[0],[(0,117),(0,312),(1,314),(3,307),(4,313)]),
([v0,v2,v3,v1,v7,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v7,v0,v1)],[1],[(0,117),(0,316),(2,317),(3,315),(5,309)]),
([v27,v0,v2,v1,v19,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19)],[1,4],[(0,289),(0,290),(0,295),(0,320),(0,321),(3,318),(3,319)]),
([v24,v0,v2,v3,v1,v4,v44],[(v6,v2,v0),(v44,v6,v5),(v24,v5,v44)],[0,1,2,3,4,5],[(0,209),(0,260),(0,293),(0,294),(0,318),(0,319),(0,323),(0,324),(0,325),(0,326),(3,322)]),
([v0,v2,v3,v1,v19,v4,v91,v5],[(v9,v0,v3),(v19,v9,v1),(v91,v19,v4)],[0,2,5],[(0,329),(0,331),(1,328),(1,332),(2,234),(3,257),(3,260),(4,330),(5,327)]),
([v68,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v54,v8,v1),(v68,v54,v5)],[0,1,2,3,4,5],[(0,234),(0,299),(0,307),(0,333),(1,334),(2,335)]),
([v68,v0,v2,v3,v1,v54,v4,v5],[(v8,v2,v3),(v54,v8,v1),(v68,v54,v5)],[0],[(0,234),(0,336),(2,337),(5,323)]),
([v0,v2,v3,v102,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v102,v45,v1)],[0,1,2,3,4,5],[(0,291),(0,297),(0,302),(0,330),(1,336),(3,320),(3,338),(3,339),(4,324),(4,325),(5,310)]),
([v0,v2,v3,v1,v4,v92,v5],[(v8,v2,v3),(v54,v8,v1),(v92,v54,v4)],[0,1,2,3,4,5],[(0,117),(0,341),(0,343),(1,341),(2,338),(2,342),(3,338),(3,342),(4,237),(4,340)]),
([v0,v2,v3,v1,v19,v4,v5,v116],[(v9,v0,v3),(v19,v9,v1),(v116,v19,v5)],[0],[(0,339),(0,342),(2,345),(4,344),(5,346)]),
([v31,v0,v2,v3,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0,1,2,3,4,5],[(0,314),(0,347),(0,349),(0,350),(1,348)]),
([v31,v0,v2,v3,v1,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0,1,2,3,4,5],[(0,292),(0,298),(0,303),(0,311),(0,321),(0,331),(0,337),(3,326)]),
([v31,v0,v2,v3,v1,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0,1,2,3,4,5],[(0,315),(0,335),(0,342),(0,353),(1,309),(1,352),(2,351)]),
([v31,v0,v2,v3,v1,v19,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0],[(0,342)]),
([v0,v2,v3,v1,v19,v4,v5,v14],[(v9,v0,v3),(v19,v9,v1),(v14,v4,v5)],[0],[(0,335),(0,353),(0,354),(1,237),(5,355)]),
([v42,v0,v2,v8,v1,v4,v5],[(v8,v3,v2),(v45,v8,v4),(v42,v3,v45)],[1,2,3,5],[(0,23),(0,74),(0,356),(0,357),(2,38),(4,293),(4,358)]),
([v42,v0,v2,v8,v1,v4,v45,v5],[(v8,v3,v2),(v45,v8,v4),(v42,v3,v45)],[1,5],[(0,360),(3,359),(3,361),(4,294),(4,358)]),
([v27,v0,v2,v9,v1,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19)],[1,3,4],[(0,25),(0,37),(0,76),(0,363),(0,364),(2,362),(3,318),(3,365)]),
([v27,v0,v2,v9,v1,v19,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v27,v3,v19)],[1,4],[(0,359),(0,366),(0,367),(3,319),(3,365)]),
([v24,v0,v2,v6,v3,v1,v4,v44],[(v6,v2,v0),(v44,v6,v5),(v24,v6,v5)],[0,1,5],[(0,358),(0,365)]),
([v0,v2,v3,v1,v19,v4,v5,v70],[(v9,v0,v3),(v19,v9,v1),(v70,v9,v5)],[0,1],[(0,346),(5,346)]),
([v24,v0,v2,v3,v1,v4,v49,v5],[(v6,v0,v2),(v49,v6,v4),(v24,v6,v5)],[0,5],[(5,368)]),
([v0,v2,v6,v3,v1,v4,v44,v11],[(v6,v2,v0),(v44,v6,v5),(v11,v3,v5)],[0,3,5],[(0,209),(2,17),(2,369),(3,357),(4,364)]),
([v56,v0,v2,v6,v3,v1,v4,v5],[(v6,v0,v2),(v49,v6,v4),(v56,v3,v49)],[2,3,4,5],[(0,24),(0,36),(0,121),(1,25),(4,38)]),
([v68,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v54,v8,v1),(v68,v5,v54)],[0,1],[(0,244),(5,323)]),
([v0,v2,v6,v3,v1,v122,v5,v44],[(v6,v2,v0),(v44,v6,v5),(v122,v44,v4)],[0],[(0,325),(0,371),(3,360),(4,366),(4,370)]),
([v0,v2,v6,v3,v1,v4,v5,0xffffffffffffeeee],[],[],[(1,370),(3,372),(3,373),(4,370),(5,372)]),
([v31,v0,v2,v3,v9,v1,v4],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0,1,2,3,4,5],[(0,26),(0,39),(0,152),(0,212),(0,258),(0,374),(2,287)]),
([v31,v0,v2,v3,v9,v1,v19,v4],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0,1,4],[(0,361),(0,367),(3,326)]),
([v31,v0,v2,v3,v9,v1,v4,v5],[(v9,v0,v3),(v19,v9,v1),(v31,v19,v5)],[0,1,3,4],[(0,75),(0,76),(0,346)]),
([v0,v130,v2,v3,v1,v4,v5],[(v8,v3,v2),(v155,v8,v4),(v130,v155,v0)],[0,1,2,3,4,5],[(0,375),(0,378),(0,379),(3,376),(4,189),(4,377)]),
([v24,v0,v2,v3,v166,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v166,v24,v3)],[0,3],[(0,189),(3,322)]),
([v55,v24,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v55,v24,v3)],[3],[(0,189),(0,206),(0,209)]),
([v0,v2,v3,v1,v168,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v168,v24,v1)],[0,1,2,3,4,5],[(0,377),(0,381),(0,382),(1,277),(2,383),(3,380)]),
([v24,v0,v2,v3,v1,v168,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v168,v24,v1)],[1],[(0,260),(0,384),(1,277)]),
([v108,v175,v0,v2,v3,v1,v4,v5],[(v9,v3,v0),(v175,v9,v5),(v108,v175,v4)],[5],[(0,277),(1,284)]),
([v0,v2,v3,v1,v188,v4,v5],[(v9,v3,v0),(v175,v9,v5),(v188,v175,v1)],[0,1,2,3,4,5],[(0,389),(1,382),(1,386),(2,375),(2,388),(3,385),(3,387)]),
([v24,v0,v2,v3,v1,v4,v240,v5],[(v6,v2,v0),(v24,v6,v5),(v240,v24,v4)],[5],[(2,387)]),
([v63,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v63,v24,v4)],[0,1,2,3,4,5],[(0,192),(0,276),(0,387),(0,392),(0,393),(0,394),(0,395),(2,387),(2,395),(3,390),(3,391)]),
([v63,v24,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v63,v24,v4)],[1,5],[(0,396),(0,397),(2,387)]),
([v24,v0,v2,v3,v1,v18,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v18,v3,v1)],[0,1],[(0,377),(0,398),(0,400),(1,179),(3,380),(5,399)]),
([v24,v0,v2,v3,v1,v4,v15,v5],[(v6,v2,v0),(v24,v6,v5),(v15,v3,v4)],[0,5],[(0,192),(0,401),(0,403),(2,385),(3,375),(5,402)]),
([v24,v0,v2,v3,v1,v4,v10,v5],[(v6,v2,v0),(v24,v6,v5),(v10,v1,v4)],[0,5],[(0,276),(0,382),(0,404),(0,406),(0,407),(2,395),(5,405)]),
([v24,v0,v2,v3,v1,v4,v16],[(v6,v2,v0),(v24,v6,v5),(v16,v1,v5)],[0,1,2,3,4,5],[(0,193),(0,260),(0,384),(0,395),(0,406),(1,389),(3,379)]),
([v0,v130,v2,v3,v8,v1,v4,v5],[(v8,v3,v2),(v155,v8,v4),(v130,v155,v0)],[4,5],[(0,82),(0,322),(0,408),(4,194)]),
([v0,v2,v6,v3,v1,v168,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v168,v24,v1)],[0,1],[(1,409),(3,278)]),
([v0,v2,v6,v3,v1,v4,v240,v5],[(v6,v2,v0),(v24,v6,v5),(v240,v24,v4)],[0,5],[(1,83),(1,410),(2,397)]),
([v63,v0,v2,v6,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v63,v24,v4)],[1],[(0,77),(0,411),(0,412),(2,77)]),
([v24,v127,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5),(v127,v6,v4)],[0,5],[(0,397),(2,397)]),
([v24,v0,v2,v6,v3,v1,v4,v16],[(v6,v2,v0),(v24,v6,v5),(v16,v1,v5)],[0,1],[(0,260),(0,413)]),
([v0,v2,v174,v3,v1,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v174,v6,v18)],[0,1,2,3,4,5],[(0,398),(1,414),(2,398),(4,414)]),
([v0,v2,v174,v6,v3,v1,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v174,v6,v18)],[1,3],[(0,261),(3,415)]),
([v0,v2,v174,v3,v1,v18,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v174,v6,v18)],[1,3],[(3,160)]),
([v0,v2,v3,v1,v18,v52,v4,v5],[(v6,v0,v2),(v18,v3,v1),(v52,v6,v18)],[0,5],[(0,416),(0,418),(2,418),(3,415),(3,417)]),
([v97,v0,v2,v3,v1,v4,v5,v23],[(v8,v2,v3),(v23,v0,v5),(v97,v8,v23)],[0,4],[(0,420),(4,419),(4,421)]),
([v112,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v23,v0,v5),(v112,v8,v23)],[0,1,2,3,4,5],[(0,422),(0,423),(1,422),(1,423),(2,313),(3,313)]),
([v112,v0,v2,v3,v8,v1,v4,v5],[],[],[(0,424),(1,424),(4,421)]),
([v112,v0,v2,v3,v1,v4,v5,v23],[(v8,v2,v3),(v23,v0,v5),(v112,v8,v23)],[0,4],[(4,202)]),
([v0,v2,v6,v3,v1,v4,v59,v5],[],[],[(0,117),(0,425),(3,426),(4,179)]),
([v28,v0,v2,v6,v3,v1,v4,v5],[(v6,v2,v0),(v18,v3,v1),(v28,v18,v5)],[0],[(0,62),(0,398),(0,400),(0,427),(1,313),(2,428)]),
([v0,v2,v9,v1,v4,v5,v12,v41],[(v9,v3,v0),(v12,v2,v5),(v41,v3,v12)],[0,3,4],[(0,14),(0,430),(0,431),(3,429),(4,29)]),
([v0,v2,v86,v3,v1,v4,v5],[(v6,v0,v2),(v15,v3,v4),(v86,v6,v15)],[0,1,2,3,4,5],[(0,401),(0,432),(0,434),(3,279),(4,64),(4,433)]),
([v0,v2,v86,v6,v3,v1,v4,v5],[(v6,v0,v2),(v15,v3,v4),(v86,v6,v15)],[2,3,4,5],[(0,18),(0,369),(2,435),(4,65)]),
([v0,v2,v86,v3,v1,v4,v15,v5],[(v6,v0,v2),(v15,v3,v4),(v86,v6,v15)],[2,3,4,5],[(0,19),(3,169),(4,66),(4,430)]),
([v0,v2,v3,v1,v7,v52,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v52,v8,v7)],[0,1,5],[(0,439),(2,438),(3,437),(4,436),(5,435)]),
([v55,v0,v2,v3,v1,v4,v5,v11],[(v6,v2,v0),(v11,v3,v5),(v55,v6,v11)],[0,3],[(0,440),(0,441),(4,421)]),
([v60,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v60,v8,v7)],[0,1,2,3,4,5],[(0,226),(0,442),(0,443),(1,444),(2,317),(4,445)]),
([v60,v0,v2,v3,v8,v1,v4,v5],[],[],[(0,421),(0,447),(1,446)]),
([v60,v0,v2,v3,v1,v7,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v60,v8,v7)],[1,2,4],[(0,20),(0,29),(0,67),(4,208)]),
([v0,v2,v6,v3,v1,v4,v11,v16],[(v6,v2,v0),(v11,v3,v5),(v16,v1,v5)],[1,3],[(0,193),(1,224),(2,22),(2,434),(5,448)]),
([v30,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v7,v0,v1),(v30,v5,v7)],[0,2],[(0,226),(0,279),(0,281),(1,449),(4,450),(5,451)]),
([v0,v2,v6,v3,v1,v4,v5,v32],[(v6,v0,v2),(v15,v3,v4),(v32,v15,v5)],[1],[(0,192),(0,452),(1,61),(3,117),(3,453),(3,454),(4,61)]),
([v25,v0,v2,v3,v9,v1,v4,v5],[(v9,v0,v3),(v13,v2,v1),(v25,v13,v5)],[0,4],[(0,68),(0,317),(1,401),(1,403),(1,456),(3,457),(4,455)]),
([v0,v2,v229,v3,v1,v4,v5],[(v6,v0,v2),(v10,v1,v4),(v229,v6,v10)],[0,1,2,3,4,5],[(0,195),(0,404),(1,458),(4,459)]),
([v0,v2,v229,v6,v3,v1,v4,v5],[],[],[(4,460)]),
([v0,v2,v229,v3,v1,v4,v10,v5],[(v6,v0,v2),(v10,v1,v4),(v229,v6,v10)],[1],[(3,264)]),
([v0,v2,v3,v1,v4,v10,v53,v5],[(v6,v0,v2),(v10,v1,v4),(v53,v6,v10)],[0,3],[(0,461),(0,464),(2,463),(3,462),(4,460)]),
([v108,v0,v2,v3,v1,v4,v5,v14],[],[],[(0,466),(2,465),(3,467)]),
([v90,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v16,v5,v1),(v90,v8,v16)],[0,1,2,3,4,5],[(0,448),(0,468),(0,469),(0,470),(1,471),(2,135),(2,355)]),
([v90,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v16,v5,v1),(v90,v8,v16)],[0,1],[(0,473),(1,472),(4,467),(5,413)]),
([v90,v0,v2,v3,v1,v4,v5,v16],[(v8,v2,v3),(v16,v5,v1),(v90,v8,v16)],[0,1],[(4,285)]),
([v36,v0,v2,v6,v3,v1,v4,v5],[(v6,v0,v2),(v10,v1,v4),(v36,v3,v10)],[3],[(0,135),(0,195),(0,197),(0,474),(5,475)]),
([v0,v2,v6,v3,v4,v10,v5,v16],[(v6,v0,v2),(v10,v1,v4),(v16,v1,v5)],[0,5],[(0,406),(0,476),(2,406)]),
([v0,v2,v6,v3,v1,v4,v16,v14],[(v6,v2,v0),(v16,v1,v5),(v14,v5,v4)],[1],[(0,395),(0,476),(0,477),(4,84)]),
([v0,v2,v6,v3,v1,v4,v5,v50],[],[],[(0,237),(0,276),(0,478),(3,479)]),
([v37,v0,v2,v6,v3,v1,v4,v5],[(v6,v0,v2),(v10,v1,v4),(v37,v10,v5)],[0],[(0,404),(0,407),(0,480),(1,85),(1,355),(2,481)]),
([v0,v2,v151,v3,v1,v4,v5],[(v6,v0,v2),(v14,v4,v5),(v151,v6,v14)],[0,1,2,3,4,5],[(0,198),(0,477),(0,483),(1,87),(2,477),(3,282),(3,482),(4,87)]),
([v0,v2,v151,v6,v3,v1,v4,v5],[],[],[(0,484),(1,88),(4,88)]),
([v0,v2,v151,v3,v1,v4,v5,v14],[(v6,v0,v2),(v14,v4,v5),(v151,v6,v14)],[0,5],[(1,89),(3,373),(4,89)]),
([v0,v2,v3,v1,v4,v10,v92,v5],[],[],[(2,485),(3,485),(4,484)]),
([v63,v0,v2,v3,v1,v4,v5,v14],[(v6,v0,v2),(v14,v4,v5),(v63,v6,v14)],[0,1,5],[(0,487),(2,487),(3,486),(3,488)]),
([v101,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v10,v1,v4),(v101,v8,v10)],[0,1,2,3,4,5],[(0,135),(0,251),(0,489),(0,490),(1,490),(4,491)]),
([v101,v0,v2,v3,v8,v1,v4,v5],[],[],[(0,488),(0,492),(1,492)]),
([v101,v0,v2,v3,v1,v4,v10,v5],[],[],[(0,90),(1,90),(4,411)]),
([v40,v0,v2,v6,v3,v1,v4,v5],[],[],[(0,86),(0,198),(0,493),(2,86),(3,135),(3,494)]),
([v37,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v10,v1,v4),(v37,v5,v10)],[0],[(0,249),(0,251),(0,282),(4,495),(4,496)]),
([v0,v2,v3,v1,v7,v4,v12,v11],[(v12,v2,v5),(v11,v3,v5),(v7,v0,v1)],[1,2,3],[(0,499),(0,500),(1,224),(1,497),(2,40),(5,498)]),
([v0,v2,v3,v1,v4,v12,v44,v11],[(v12,v2,v5),(v11,v3,v5),(v44,v0,v12)],[2,3,4,5],[(0,505),(2,502),(2,503),(3,501),(4,295),(4,504)]),
([v27,v0,v2,v3,v13,v4,v5],[(v7,v0,v1),(v13,v2,v1),(v27,v3,v7)],[0,1,2,3,4],[(0,295),(0,506),(1,508),(2,498),(5,507)]),
([v27,v0,v2,v3,v7,v13,v4,v5],[(v7,v0,v1),(v13,v2,v1),(v27,v3,v7)],[1,2,3,4],[(0,50),(0,67),(0,295),(0,509)]),
([v33,v0,v2,v1,v17,v15,v5],[(v15,v3,v4),(v17,v0,v4),(v33,v3,v17)],[0,1,3,4,5],[(0,63),(0,502),(0,511),(0,512),(1,67),(1,509),(2,510),(3,513)]),
([v0,v2,v3,v1,v4,v10,v12,v11],[(v12,v2,v5),(v11,v3,v5),(v10,v1,v4)],[2,3],[(0,515),(0,516),(1,515),(1,516),(2,514),(3,514)]),
([v0,v2,v3,v1,v4,v12,v32],[(v11,v3,v5),(v12,v2,v5),(v32,v4,v11)],[0,1,2,3,5],[(0,224),(0,497),(0,519),(0,520),(0,522),(1,61),(1,526),(2,514),(3,518),(3,523),(4,524),(4,525),(5,517),(5,521)]),
([v0,v2,v3,v1,v4,v12,v11,v26],[(v12,v2,v5),(v11,v3,v5),(v26,v1,v12)],[1,2,3,5],[(0,530),(1,527),(2,512),(2,528),(2,529),(5,525)]),
([v25,v0,v2,v3,v7,v4,v5],[(v13,v2,v1),(v7,v0,v1),(v25,v5,v13)],[0,1,2,4,5],[(0,68),(0,498),(0,521),(0,525),(0,532),(0,534),(3,531),(4,533)]),
([v25,v0,v2,v3,v7,v13,v4,v5],[(v13,v2,v1),(v7,v0,v1),(v25,v5,v13)],[0,2,4],[(0,513),(0,525),(4,535)]),
([v0,v2,v3,v1,v4,v12,v11,v48],[(v12,v2,v5),(v11,v3,v5),(v48,v1,v11)],[1,2,3],[(1,538),(2,537),(3,536)]),
([v30,v0,v2,v3,v7,v13,v4,v5],[(v13,v2,v1),(v7,v0,v1),(v30,v5,v7)],[0,2,4],[(0,524)]),
([v33,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v46,v0,v15),(v33,v3,v46)],[0,1,3,4,5],[(0,214),(0,429),(0,541),(0,542),(1,70),(2,539),(5,540)]),
([v33,v0,v2,v1,v4,v15,v46,v5],[(v15,v3,v4),(v46,v0,v15),(v33,v3,v46)],[1,4,5],[(0,215),(2,543),(5,540)]),
([v33,v0,v2,v1,v4,v17,v46,v5],[(v17,v0,v4),(v46,v3,v17),(v33,v3,v17)],[1,3,5],[(0,540),(2,544)]),
([v0,v2,v3,v1,v4,v23,v12,v41],[(v12,v2,v5),(v41,v3,v12),(v23,v0,v5)],[2,3,4],[(0,547),(2,216),(3,541),(4,545),(4,546)]),
([v0,v2,v3,v1,v29,v19,v4,v5],[(v7,v0,v1),(v29,v2,v7),(v19,v3,v7)],[0,1,2,3],[(0,301),(0,548),(1,220)]),
([v27,v0,v2,v3,v1,v29,v4,v5],[(v7,v0,v1),(v29,v2,v7),(v27,v3,v7)],[1,2],[(0,29),(0,51),(0,545),(5,549)]),
([v72,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v29,v2,v7),(v72,v3,v29)],[1,2,3,4],[(0,301),(0,546),(2,69),(2,70),(3,547)]),
([v39,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v41,v3,v12),(v39,v5,v41)],[0,1,2,3,4],[(0,217),(0,431),(0,544),(0,547),(0,550),(1,71),(1,551),(2,552)]),
([v39,v0,v2,v3,v1,v4,v12,v41],[(v12,v2,v5),(v41,v3,v12),(v39,v5,v41)],[0,1,3],[(0,218),(0,544),(1,543)]),
([v0,v2,v3,v1,v4,v12,v41,v14],[(v12,v2,v5),(v41,v3,v12),(v14,v5,v4)],[2,3,5],[(2,552),(3,542),(4,553)]),
([v0,v2,v3,v1,v29,v4,v21,v5],[(v7,v0,v1),(v29,v2,v7),(v21,v7,v4)],[0,1,2,5],[(0,555),(1,242),(2,554)]),
([v25,v0,v2,v3,v1,v29,v4,v5],[(v13,v2,v1),(v29,v0,v13),(v25,v13,v5)],[0,1],[(4,556)]),
([v0,v2,v3,v1,v29,v4,v43,v5],[(v13,v2,v1),(v29,v0,v13),(v43,v13,v4)],[4,5],[(2,558),(3,557),(4,241)]),
([v30,v0,v2,v3,v1,v29,v4,v5],[(v7,v0,v1),(v29,v2,v7),(v30,v7,v5)],[0],[(0,560),(4,559)]),
([v0,v2,v3,v1,v7,v4,v53,v5],[(v7,v0,v1),(v29,v2,v7),(v53,v29,v4)],[0,1,3],[(0,562),(0,565),(3,563),(4,561),(5,564)]),
([v62,v0,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v29,v0,v13),(v62,v29,v5)],[0,1,4],[(0,554)]),
([v0,v2,v3,v1,v7,v4,v5,v124],[(v7,v0,v1),(v29,v2,v7),(v124,v29,v5)],[0,1,3,5],[(0,560),(2,567),(2,570),(4,566),(5,568),(5,569)]),
([v62,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v29,v2,v7),(v62,v29,v5)],[0,1,2],[(0,553),(0,558),(1,552)]),
([v0,v138,v2,v3,v1,v4,v5],[(v12,v2,v5),(v71,v3,v12),(v138,v71,v0)],[0,1,2,3,4,5],[(0,571),(1,573),(2,574),(3,572),(4,443)]),
([v33,v0,v2,0xcfcfcececfcfcece,v3,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(0xcfcfcececfcfcece,v33,v2)],[2],[(1,443),(2,213)]),
([v60,v88,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v88,v2,v7),(v60,v88,v3)],[3],[(0,29),(0,72),(0,443),(1,575)]),
([v0,v2,v3,v1,v209,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v209,v33,v1)],[0,1,2,3,4,5],[(0,581),(1,577),(2,571),(2,580),(3,576),(3,578),(3,579)]),
([v33,v0,v2,v3,v1,v209,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v209,v33,v1)],[1],[(3,578)]),
([v94,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v105,v0,v13),(v94,v105,v5)],[0,1,2,3,4,5],[(0,317),(0,578),(0,582),(1,584),(2,585),(3,583)]),
([v94,v105,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v105,v0,v13),(v94,v105,v5)],[0,1,2],[(0,578),(4,586)]),
([v0,v2,v3,v1,v176,v4,v5],[(v11,v3,v5),(v121,v2,v11),(v176,v121,v1)],[0,1,2,3,4,5],[(0,573),(0,591),(1,580),(2,590),(3,587),(3,589),(4,588)]),
([v33,v0,v2,v3,v1,v4,v5,v143],[(v17,v0,v4),(v33,v3,v17),(v143,v33,v5)],[0,5],[(0,589),(4,592)]),
([v79,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v79,v33,v5)],[0,1,2,3,4,5],[(0,589),(0,594),(0,595),(1,226),(1,585),(2,593)]),
([v79,v33,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v79,v33,v5)],[0],[(0,589),(0,596)]),
([v33,v0,v2,v3,v1,v13,v4,v5],[(v17,v0,v4),(v33,v3,v17),(v13,v2,v1)],[1,3],[(2,571),(2,597),(2,599),(3,317),(3,576),(5,598)]),
([v33,v0,v2,v3,v1,v22,v5],[(v17,v0,v4),(v33,v3,v17),(v22,v2,v4)],[2,3,4,5],[(0,216),(5,600)]),
([v33,v0,v2,v3,v1,v4,v5,v12],[(v17,v0,v4),(v33,v3,v17),(v12,v2,v5)],[0],[(0,41),(0,587),(0,601),(1,226),(4,573),(5,602)]),
([v33,v0,v2,v3,v1,v4,v5,v16],[(v17,v0,v4),(v33,v3,v17),(v16,v1,v5)],[1,5],[(0,603),(1,585),(2,580),(2,605),(3,579),(5,604)]),
([v0,v138,v2,v3,v1,v4,v5,v12],[(v12,v2,v5),(v71,v3,v12),(v138,v71,v0)],[0,3,4],[(0,213),(0,510),(0,607),(4,606)]),
([v0,v2,v3,v1,v209,v4,v17,v5],[(v17,v0,v4),(v33,v3,v17),(v209,v33,v1)],[1,3,5],[(2,609),(3,608)]),
([v94,v0,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v105,v0,v13),(v94,v105,v5)],[1,2],[(2,610)]),
([v0,v2,v3,v1,v176,v4,v5,v11],[(v11,v3,v5),(v121,v2,v11),(v176,v121,v1)],[0,1,2],[(0,612),(5,611)]),
([v79,v0,v2,v3,v1,v4,v17,v5],[(v17,v0,v4),(v33,v3,v17),(v79,v33,v5)],[4,5],[(5,613)]),
([v33,v0,v2,v3,v1,v17,v22,v5],[(v17,v0,v4),(v33,v3,v17),(v22,v2,v4)],[2,3,4],[(0,216),(1,614)]),
([v33,v0,v2,v3,v1,v4,v49,v5],[(v17,v0,v4),(v33,v3,v17),(v49,v2,v17)],[0,5],[(0,502),(1,616),(5,615)]),
([v27,v88,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v88,v2,v7),(v27,v3,v7)],[1,2,3],[(0,52),(0,509),(0,606),(0,614),(1,575)]),
([v33,v0,v2,v3,v1,v4,v21,v5],[(v17,v0,v4),(v33,v3,v17),(v21,v1,v17)],[0,5],[(0,512),(0,618),(5,617)]),
([v25,v105,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v105,v0,v13),(v25,v5,v13)],[0,1,4],[(0,513),(0,608),(4,586)]),
([v33,v0,v2,v3,v1,v17,v5,v14],[(v17,v0,v4),(v33,v3,v17),(v14,v4,v5)],[0,3,4],[]),
([v33,v0,v2,v3,v1,v4,v5,v67],[],[],[(4,620),(5,619)]),
([v30,v88,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v88,v2,v7),(v30,v7,v5)],[0,2],[(0,611),(1,596)]),
([v0,v2,v3,v1,v18,v4,v23,v12],[(v12,v2,v5),(v18,v3,v1),(v23,v0,v5)],[2,4],[(0,622),(2,621)]),
([v27,v0,v2,v3,v1,v4,v22,v5],[(v7,v0,v1),(v22,v2,v4),(v27,v3,v7)],[3,5],[(0,623),(0,626),(1,624),(2,317),(3,625)]),
([v0,v2,v3,v1,v7,v22,v15,v5],[(v7,v0,v1),(v22,v2,v4),(v15,v3,v4)],[1,2,3],[(3,627),(4,224),(5,628)]),
([v42,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v22,v2,v4),(v42,v3,v22)],[1,3],[(0,623),(0,626),(0,629),(3,622),(5,313),(5,630)]),
([v28,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v18,v3,v1),(v28,v5,v18)],[0,1,2,3,4],[(0,62),(0,622),(0,627),(0,631),(0,632),(0,634),(0,635),(1,633)]),
([v28,v0,v2,v3,v1,v18,v4,v12],[(v12,v2,v5),(v18,v3,v1),(v28,v5,v18)],[0,2],[(0,635),(5,636)]),
([v0,v2,v3,v1,v18,v4,v12,v14],[(v12,v2,v5),(v18,v3,v1),(v14,v5,v4)],[2,5],[(0,634),(0,637)]),
([v0,v2,v3,v1,v177,v4,v5],[(v7,v0,v1),(v22,v2,v4),(v177,v7,v22)],[0,1,2,3,4,5],[(0,623),(0,638),(0,640),(5,639)]),
([v0,v2,v3,v1,v177,v7,v4,v5],[(v7,v0,v1),(v22,v2,v4),(v177,v7,v22)],[1,4],[(2,641)]),
([v0,v2,v3,v1,v177,v4,v22,v5],[(v7,v0,v1),(v22,v2,v4),(v177,v7,v22)],[5],[(5,564)]),
([v0,v2,v3,v1,v18,v4,v91,v5],[(v17,v0,v4),(v18,v3,v1),(v91,v17,v18)],[0,2,5],[(0,643),(1,642),(1,645),(2,635),(3,641),(3,644)]),
([v94,v0,v2,v3,v1,v4,v5,v23],[(v13,v2,v1),(v23,v0,v5),(v94,v13,v23)],[0,1,2],[(0,636),(0,647),(2,467),(4,646)]),
([v80,v0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22)],[0,1,2,3,4,5],[(0,313),(0,628),(0,648),(0,649),(0,650),(0,652),(1,651)]),
([v80,v0,v2,v3,v1,v4,v5,v11],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22)],[0],[(0,653),(0,654),(5,467)]),
([v80,v0,v2,v3,v1,v4,v22,v5],[(v11,v3,v5),(v22,v2,v4),(v80,v11,v22)],[5],[(5,610)]),
([v0,v2,v3,v1,v18,v4,v5,v67],[],[],[(0,655),(1,237),(2,651),(3,656)]),
([v30,v0,v2,v3,v1,v4,v22,v5],[(v7,v0,v1),(v22,v2,v4),(v30,v7,v5)],[0,5],[(0,585),(0,640),(0,659),(1,657),(5,658)]),
([v0,v2,v3,v1,v7,v4,v5,v117],[(v7,v0,v1),(v22,v2,v4),(v117,v22,v5)],[1,4],[(0,237),(0,585),(0,662),(5,660),(5,661),(5,663)]),
([v28,v0,v2,v3,v1,v4,v17,v5],[(v17,v0,v4),(v18,v3,v1),(v28,v18,v5)],[0,5],[(1,640),(1,659),(1,664),(2,634),(2,651),(5,665)]),
([v27,v0,v2,v3,v1,v4,v5,v12],[(v7,v0,v1),(v12,v2,v5),(v27,v3,v7)],[0,3],[(0,226),(0,500),(0,597),(0,599),(4,666),(5,667)]),
([v30,v0,v2,v3,v1,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v30,v5,v7)],[0,1,2,3,4,5],[(0,500),(0,560),(0,668),(0,671),(1,670),(3,669)]),
([v30,v0,v2,v3,v1,v7,v4,v12],[(v7,v0,v1),(v12,v2,v5),(v30,v5,v7)],[0,1,2],[(0,524),(0,560),(5,672)]),
([v0,v2,v3,v1,v7,v4,v12,v14],[(v7,v0,v1),(v12,v2,v5),(v14,v5,v4)],[1,2,5],[(0,671),(0,674),(1,514),(2,673)]),
([v0,v2,v3,v1,v7,v15,v21,v5],[(v15,v3,v4),(v7,v0,v1),(v21,v7,v4)],[0,1,3,5],[(0,677),(2,526),(3,676),(4,675)]),
([v0,v2,v3,v1,v133,v4,v5],[(v15,v3,v4),(v7,v0,v1),(v133,v7,v15)],[0,1,2,3,4,5],[(0,678),(0,680),(3,597),(5,679)]),
([v0,v2,v3,v1,v133,v7,v4,v5],[(v15,v3,v4),(v7,v0,v1),(v133,v7,v15)],[1,3,4,5],[(0,677),(2,569)]),
([v0,v2,v3,v1,v133,v4,v15,v5],[(v15,v3,v4),(v7,v0,v1),(v133,v7,v15)],[3,5],[(5,681)]),
([v0,v2,v3,v1,v7,v4,v91,v5],[(v15,v3,v4),(v7,v0,v1),(v91,v7,v15)],[0,1,2],[(1,683),(1,685),(3,684),(5,681),(5,682)]),
([v69,v0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11)],[0,1,2,3,4,5],[(0,317),(0,498),(0,686),(0,687),(0,690),(1,688),(2,689)]),
([v69,v0,v2,v3,v1,v13,v4,v5],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11)],[0,1,2],[(0,526),(2,613)]),
([v69,v0,v2,v3,v1,v4,v5,v11],[(v11,v3,v5),(v13,v2,v1),(v69,v13,v11)],[0,1,2],[(0,672),(0,691),(0,692),(4,467)]),
([v79,v0,v2,v3,v1,v4,v5,v11],[(v17,v0,v4),(v11,v3,v5),(v79,v11,v17)],[0],[(0,693),(0,694),(3,467)]),
([v30,v0,v2,v3,v1,v4,v15,v5],[(v15,v3,v4),(v7,v0,v1),(v30,v7,v5)],[0,5],[(0,680),(0,689),(0,698),(2,695),(3,696),(5,697)]),
([v0,v2,v3,v1,v7,v4,v5,v32],[(v15,v3,v4),(v7,v0,v1),(v32,v15,v5)],[1,5],[(0,689),(0,700),(1,237),(1,673),(2,520),(3,699),(5,701)]),
([v25,v0,v2,v3,v1,v4,v17,v5],[(v13,v2,v1),(v17,v0,v4),(v25,v13,v5)],[0,1,5],[(0,521),(1,680),(1,698),(1,702),(2,585),(2,671),(5,703)]),
([v27,v0,v2,v7,v18,v4,v5],[(v7,v0,v1),(v18,v3,v1),(v27,v3,v7)],[1,3,4],[(0,545),(0,614),(0,704)]),
([v42,v0,v2,v1,v22,v15,v5],[(v15,v3,v4),(v22,v2,v4),(v42,v3,v22)],[0,1,2,3,5],[(0,705),(0,706),(0,707),(3,704),(3,708)]),
([v0,v2,v3,v1,v4,v23,v12,v70],[(v12,v2,v5),(v23,v0,v5),(v70,v3,v23)],[1,2,3,4],[(1,712),(2,288),(3,705),(3,710),(5,709),(5,711)]),
([v42,v0,v2,v3,v1,v17,v5],[(v17,v0,v4),(v22,v2,v4),(v42,v3,v22)],[1,2,3,4,5],[(0,288),(0,628),(3,713),(4,714)]),
([v42,v0,v2,v3,v1,v17,v22,v5],[(v17,v0,v4),(v22,v2,v4),(v42,v3,v22)],[2,3,4],[(0,288),(5,706)]),
([v0,v2,v3,v1,v4,v10,v23,v12],[(v12,v2,v5),(v23,v0,v5),(v10,v1,v4)],[2,4],[(0,715),(0,716)]),
([v0,v2,v3,v1,v4,v23,v12,v47],[(v12,v2,v5),(v23,v0,v5),(v47,v1,v23)],[1,2,4],[(1,718),(1,719),(4,717)]),
([v28,v0,v2,v3,v13,v18,v4,v5],[(v13,v2,v1),(v18,v3,v1),(v28,v5,v18)],[0,2],[]),
([v0,v2,v3,v1,v4,v23,v12,v26],[(v12,v2,v5),(v23,v0,v5),(v26,v1,v12)],[1,2,4,5],[(0,723),(1,721),(2,722),(4,720)]),
([v25,v0,v2,v3,v13,v18,v4,v5],[(v13,v2,v1),(v18,v3,v1),(v25,v5,v13)],[0,2],[(4,724)]),
([v0,v2,v3,v1,v4,v12,v67],[(v12,v2,v5),(v23,v0,v5),(v67,v4,v23)],[0,1,2,4,5],[(0,224),(0,727),(1,729),(3,726),(4,728),(5,725)]),
([v0,v2,v3,v1,v4,v23,v12,v67],[(v12,v2,v5),(v23,v0,v5),(v67,v4,v23)],[2,4],[(1,732),(3,707),(3,731),(4,728),(5,730)]),
([v28,v0,v2,v3,v7,v4,v5],[(v7,v0,v1),(v18,v3,v1),(v28,v5,v18)],[0,1,3,4,5],[(0,627),(0,728),(0,735),(1,628),(2,733),(4,734)]),
([v28,v0,v2,v3,v7,v18,v4,v5],[(v7,v0,v1),(v18,v3,v1),(v28,v5,v18)],[0,4],[(0,708),(0,728)]),
([v0,v2,v3,v1,v4,v23,v12,v117],[(v12,v2,v5),(v23,v0,v5),(v117,v4,v12)],[2,4],[(1,738),(3,737),(5,736)]),
([v30,v0,v2,v3,v7,v18,v4,v5],[(v7,v0,v1),(v18,v3,v1),(v30,v5,v7)],[0,4],[(0,735)]),
([v42,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v45,v2,v15),(v42,v3,v45)],[0,1,2,3,5],[(0,501),(0,740),(3,289),(3,739)]),
([v42,v0,v2,v1,v4,v15,v45,v5],[(v15,v3,v4),(v45,v2,v15),(v42,v3,v45)],[1,2,5],[(0,741),(3,290),(3,739),(3,742),(4,743)]),
([v56,v0,v2,v3,v1,v4,v17,v5],[(v17,v0,v4),(v49,v2,v17),(v56,v3,v49)],[2,3,5],[(0,220),(0,503),(2,505)]),
([v27,v0,v2,v1,v7,v19,v4,v5],[(v7,v0,v1),(v19,v3,v7),(v27,v3,v7)],[1,3],[(0,739),(3,744)]),
([v24,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v44,v0,v12),(v24,v5,v44)],[0,1,3,4,5],[(0,318),(0,505),(0,744),(0,747),(0,748),(0,749),(1,746),(3,745)]),
([v24,v0,v2,v3,v1,v4,v12,v44],[(v12,v2,v5),(v44,v0,v12),(v24,v5,v44)],[0,1,4],[(0,319),(0,743),(0,744),(0,750),(0,751)]),
([v0,v2,v3,v1,v4,v12,v44,v14],[(v12,v2,v5),(v44,v0,v12),(v14,v5,v4)],[2,4,5],[(0,747),(3,740),(4,752)]),
([v0,v2,v3,v1,v19,v4,v21,v5],[(v7,v0,v1),(v19,v3,v7),(v21,v7,v4)],[0,3,5],[(0,329),(0,754),(0,755),(2,753),(3,748)]),
([v25,v0,v2,v3,v1,v54,v4,v5],[(v13,v2,v1),(v54,v3,v13),(v25,v13,v5)],[0,5],[(0,757),(4,756),(5,749)]),
([v0,v2,v3,v1,v19,v4,v5,v47],[(v7,v0,v1),(v19,v3,v7),(v47,v7,v5)],[0,3],[(0,758),(2,345)]),
([v30,v0,v2,v3,v1,v19,v4,v5],[(v7,v0,v1),(v19,v3,v7),(v30,v7,v5)],[0,3],[(4,759)]),
([v68,v0,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v54,v3,v13),(v68,v54,v5)],[0,1,3],[(0,753)]),
([v0,v2,v3,v102,v4,v15,v45,v5],[(v15,v3,v4),(v45,v2,v15),(v102,v45,v1)],[2,5],[(0,741),(3,320),(3,760),(4,750)]),
([v0,v2,v3,v1,v7,v4,v5,v116],[(v7,v0,v1),(v19,v3,v7),(v116,v19,v5)],[1],[(0,760),(4,761),(5,762),(5,763)]),
([v31,v0,v2,v3,v1,v7,v4],[(v7,v0,v1),(v19,v3,v7),(v31,v19,v5)],[0,1,2,3,4,5],[(0,504),(0,548),(0,616),(0,754),(1,764),(2,757)]),
([v31,v0,v2,v3,v1,v7,v19,v4],[(v7,v0,v1),(v19,v3,v7),(v31,v19,v5)],[0,1,3],[(0,321),(0,742),(3,751)]),
([v31,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v19,v3,v7),(v31,v19,v5)],[0,1,3],[(0,752),(0,758),(3,747)]),
([v0,v227,v2,v3,v1,v4,v5],[(v13,v2,v1),(v134,v3,v13),(v227,v134,v0)],[0,1,2,3,4,5],[(0,766),(1,666),(2,442),(2,765),(4,624)]),
([v27,v0,v2,v241,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v241,v27,v2)],[2],[(0,442)]),
([v60,v27,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v60,v27,v2)],[2],[(0,442),(0,506),(0,606)]),
([v0,v2,v3,v1,v146,v4,v5],[(v17,v0,v4),(v125,v2,v17),(v146,v125,v1)],[0,1,2,3,4,5],[(0,508),(0,624),(0,767),(0,771),(0,772),(0,773),(2,770),(3,690),(3,768),(4,769)]),
([v27,v0,v2,v3,v1,v4,0xffff0f0affff0f0a,v5],[(v7,v0,v1),(v27,v3,v7),(0xffff0f0affff0f0a,v27,v4)],[0,5],[(1,774),(2,690)]),
([v69,v134,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v134,v3,v13),(v69,v134,v5)],[0,1,2],[(0,690),(2,775)]),
([v0,v2,v3,v1,v218,v4,v5],[(v15,v3,v4),(v158,v2,v15),(v218,v158,v1)],[0,1,2,3,4,5],[(0,666),(0,778),(3,777),(4,770),(4,776)]),
([v27,v0,v2,v3,v1,v4,v5,v144],[(v7,v0,v1),(v27,v3,v7),(v144,v27,v5)],[0],[(0,777)]),
([v58,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v58,v27,v5)],[0,1,2,3,4,5],[(0,226),(0,500),(0,689),(0,777),(0,780),(1,781),(2,779)]),
([v58,v27,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v58,v27,v5)],[0],[(0,777),(0,782)]),
([v27,v0,v2,v3,v1,v4,v5,v14],[(v7,v0,v1),(v27,v3,v7),(v14,v4,v5)],[5],[(0,689),(0,783),(2,768),(3,770),(5,784)]),
([v0,v227,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v134,v3,v13),(v227,v134,v0)],[1,2,3,4],[(0,48),(1,785),(3,786),(4,575)]),
([v0,v2,v3,v1,v146,v4,v17,v5],[(v17,v0,v4),(v125,v2,v17),(v146,v125,v1)],[0,1,2,4,5],[(0,790),(2,789),(3,788),(4,787)]),
([v0,v2,v3,v1,v218,v4,v15,v5],[(v15,v3,v4),(v158,v2,v15),(v218,v158,v1)],[1,2,5],[(0,49),(0,791),(2,793),(3,792)]),
([v58,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v58,v27,v5)],[0,1,4],[(0,47),(0,729),(0,794),(0,795)]),
([v27,v0,v2,v3,v7,v4,v5,v16],[(v7,v0,v1),(v27,v3,v7),(v16,v1,v5)],[0,1,3,4],[(0,54),(0,795)]),
([v27,v0,v2,v3,v1,v4,v21,v5],[(v7,v0,v1),(v27,v3,v7),(v21,v7,v4)],[0,5],[(0,797),(2,526),(5,796)]),
([v25,v134,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v134,v3,v13),(v25,v13,v5)],[0,3],[(0,788),(2,775)]),
([v27,v0,v2,v3,v1,v4,v5,v47],[(v7,v0,v1),(v27,v3,v7),(v47,v7,v5)],[0],[(0,729),(5,798)]),
([v30,v27,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7),(v30,v7,v5)],[0,3],[(0,782),(0,792)]),
([v0,v2,v3,v1,v17,v12,v14],[(v17,v0,v4),(v12,v2,v5),(v14,v4,v5)],[0,1,2,4,5],[(0,497),(0,673),(0,800),(0,802),(0,803),(1,795),(2,673),(2,803),(3,43),(3,799),(3,801),(4,795),(5,799),(5,801)]),
([v0,v2,v3,v1,v7,v4,v11,v47],[(v11,v3,v5),(v7,v0,v1),(v47,v5,v7)],[0,1,3],[(0,729),(0,806),(2,44),(4,804),(5,805)]),
([v25,v0,v2,v3,v1,v4,v15,v5],[(v13,v2,v1),(v15,v3,v4),(v25,v13,v5)],[0,5],[(0,801),(0,808),(2,689),(2,807),(3,809),(5,810)]),
([v0,v2,v3,v1,v100,v4,v5],[(v7,v0,v1),(v11,v3,v5),(v100,v7,v11)],[0,1,2,3,4,5],[(0,499),(0,813),(1,601),(1,802),(1,814),(1,815),(2,45),(2,808),(2,811),(2,812),(5,499)]),
([v0,v2,v3,v1,v100,v7,v4,v5],[(v7,v0,v1),(v11,v3,v5),(v100,v7,v11)],[0,1,3,4,5],[(0,763),(0,806),(0,816),(1,803),(2,46)]),
([v58,v0,v2,v3,v1,v4,v5,v11],[(v7,v0,v1),(v11,v3,v5),(v58,v7,v11)],[0,3],[(0,817),(0,818),(2,488)]),
([v0,v2,v3,v1,v4,v12,v14,v67],[(v12,v2,v5),(v14,v5,v4),(v67,v0,v14)],[2,4,5],[(1,822),(3,819),(3,820),(4,821),(5,725)]),
([v36,v0,v2,v3,v13,v4,v5],[(v13,v2,v1),(v10,v1,v4),(v36,v3,v10)],[0,1,2,3,5],[(0,725),(0,823),(0,824),(2,448),(5,825)]),
([v36,v0,v2,v3,v13,v4,v10,v5],[(v13,v2,v1),(v10,v1,v4),(v36,v3,v10)],[1,2,3,5],[(0,725),(0,799),(1,90),(1,826)]),
([v36,v0,v2,v1,v15,v10,v5],[(v15,v3,v4),(v10,v4,v1),(v36,v3,v10)],[0,1,3,5],[(0,90),(0,799),(0,819),(0,826),(0,828),(0,829),(0,831),(2,827),(3,830)]),
([v0,v2,v3,v1,v4,v12,v14,v32],[(v12,v2,v5),(v14,v5,v4),(v32,v3,v14)],[0,1,2,3,5],[(0,519),(1,835),(3,828),(3,832),(3,833),(4,834)]),
([v40,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v14,v5,v4),(v40,v3,v14)],[0,1,2,3,5],[(0,86),(0,519),(0,800),(0,836),(0,839),(2,838),(4,448),(4,841),(5,837),(5,840)]),
([v40,v0,v2,v3,v1,v4,v12,v14],[(v12,v2,v5),(v14,v5,v4),(v40,v3,v14)],[0,2,3,5],[(0,519),(3,829)]),
([v0,v2,v3,v1,v17,v16,v14],[(v17,v0,v4),(v14,v4,v5),(v16,v1,v5)],[0,1,4,5],[(0,514),(0,673),(0,838),(0,846),(0,847),(1,842),(1,844),(1,848),(3,845),(4,84),(4,843),(4,849),(5,831)]),
([v0,v2,v3,v1,v4,v16,v32],[(v11,v3,v5),(v16,v5,v1),(v32,v4,v11)],[0,1,3,5],[(0,514),(0,520),(0,843),(0,850),(1,673),(1,839),(2,852),(3,851),(3,854),(4,853)]),
([v0,v2,v3,v1,v4,v12,v26,v14],[(v12,v2,v5),(v14,v5,v4),(v26,v1,v12)],[1,2,5],[(1,855),(2,857),(2,858),(4,844),(4,856),(5,853)]),
([v25,v0,v2,v3,v4,v10,v5],[(v13,v2,v1),(v10,v1,v4),(v25,v5,v13)],[0,1,2,5],[(0,521),(0,801),(0,840),(0,853),(0,860),(2,859),(5,861)]),
([v25,v0,v2,v3,v13,v4,v10,v5],[(v13,v2,v1),(v10,v1,v4),(v25,v5,v13)],[0,2,5],[(0,853),(2,848),(2,863),(5,862)]),
([v0,v2,v3,v1,v4,v12,v14,v50],[(v12,v2,v5),(v14,v5,v4),(v50,v1,v14)],[1,2,5],[(1,864),(1,866),(2,865)]),
([v37,v0,v2,v3,v1,v15,v10,v5],[(v15,v3,v4),(v10,v4,v1),(v37,v5,v10)],[0,1,3,5],[(0,852),(1,845)]),
([v30,v0,v2,v3,v7,v4,v16],[(v7,v0,v1),(v16,v1,v5),(v30,v5,v7)],[0,1,4,5],[(0,91),(0,524),(0,795),(0,830),(0,841),(0,848),(0,856),(0,863),(1,868),(3,867)]),
([v40,v0,v2,v1,v4,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v40,v3,v32)],[0,1,5],[(0,519),(0,850),(0,869),(1,871),(1,872),(2,519),(2,850),(3,870),(4,871),(4,872)]),
([v0,v2,v3,v1,v4,v21,v53,v5],[(v7,v0,v1),(v21,v7,v4),(v53,v2,v21)],[0,2,3],[(0,874),(0,876),(0,877),(1,229),(2,554),(3,753),(4,873),(4,875)]),
([v57,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v21,v17,v1),(v57,v3,v21)],[0,1,2,3,4,5],[(0,229),(0,453),(0,517),(0,701),(2,878),(4,879)]),
([v57,v0,v2,v3,v1,v4,v21,v5],[(v17,v0,v4),(v21,v17,v1),(v57,v3,v21)],[3,5],[(0,229),(0,518),(0,880),(0,881),(2,526)]),
([v25,v0,v2,v3,v1,v4,v26],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26)],[0,1,2],[(0,525),(0,526),(0,853),(0,871),(0,872),(0,884),(0,885),(0,886),(0,887),(1,883),(2,854),(3,882)]),
([v0,v2,v3,v129,v4,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v129,v32,v1)],[0,1,2,3,4,5],[(0,522),(0,869),(0,875),(1,886),(2,522),(2,875),(3,880),(3,888),(3,889),(4,886),(5,880)]),
([v0,v2,v3,v1,v4,v5,v111],[(v7,v0,v1),(v21,v7,v4),(v111,v21,v5)],[0,1,2,3,4,5],[(0,237),(0,888),(0,891),(0,893),(1,237),(1,891),(2,892),(3,892),(4,890)]),
([v0,v2,v3,v1,v4,v21,v5,v111],[(v7,v0,v1),(v21,v7,v4),(v111,v21,v5)],[0],[(0,889),(0,893),(2,895),(3,895),(4,894)]),
([v38,v0,v2,v3,v1,v4],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,2,3,4,5],[(0,454),(0,896),(0,897),(1,896),(1,897)]),
([v38,v0,v2,v3,v1,v4,v21],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,2,3,4,5],[(0,523),(0,870),(0,876),(0,881),(0,898),(1,523),(1,876),(1,881),(1,898),(2,887),(3,887)]),
([v38,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,2,3,4,5],[(0,699),(0,701),(0,893),(1,699),(1,701),(2,899),(3,899)]),
([v38,v0,v2,v3,v1,v4,v21,v5],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,5],[(0,851),(0,854),(0,893),(1,851),(1,854)]),
([v40,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v32,v15,v5),(v40,v3,v32)],[0,1,3,5],[(0,675),(0,901),(1,96),(1,871),(1,902),(2,527),(2,721),(2,855),(2,900)]),
([v40,v0,v2,v1,v4,v15,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v40,v3,v32)],[0,1,5],[(0,903),(1,872),(1,902),(3,904),(4,905)]),
([v57,v0,v2,v3,v1,v4,v17,v5],[(v17,v0,v4),(v21,v17,v1),(v57,v3,v21)],[1,3,5],[(0,242),(0,528),(2,530)]),
([v57,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v21,v7,v4),(v57,v3,v21)],[1,3,4,5],[(0,95),(0,329),(0,720),(2,96),(3,723)]),
([v25,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26)],[0,1,2],[(0,98),(0,530),(0,676),(0,723),(0,884),(0,906),(0,909),(1,908),(2,858),(3,907),(5,910)]),
([v25,v0,v2,v3,v1,v4,v12,v26],[(v12,v2,v5),(v26,v12,v1),(v25,v5,v26)],[0,1],[(0,885),(0,905),(0,911),(0,912),(5,910)]),
([v25,v0,v2,v3,v1,v13,v4,v26],[(v13,v2,v1),(v26,v13,v5),(v25,v13,v5)],[0,1],[(0,902),(0,910)]),
([v0,v2,v3,v1,v4,v21,v5,v47],[(v7,v0,v1),(v21,v7,v4),(v47,v7,v5)],[0,1,5],[(0,913),(2,895)]),
([v30,v0,v2,v3,v1,v4,v21,v5],[(v7,v0,v1),(v21,v7,v4),(v30,v7,v5)],[0,1,5],[(0,854),(0,856),(5,914)]),
([v0,v2,v3,v1,v7,v21,v5,v14],[(v7,v0,v1),(v21,v7,v4),(v14,v4,v5)],[0,1,5],[(0,844),(0,854),(0,915),(3,909),(4,901)]),
([v0,v2,v3,v129,v4,v15,v5,v32],[(v15,v3,v4),(v32,v15,v5),(v129,v32,v1)],[0,5],[(0,903),(1,886),(3,916),(4,911)]),
([v0,v2,v3,v1,v7,v4,v5,v111],[(v7,v0,v1),(v21,v7,v4),(v111,v21,v5)],[1],[(0,916),(3,918),(4,917),(5,919)]),
([v38,v0,v2,v3,v1,v7,v4],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,2,3,4,5],[(0,555),(0,755),(0,797),(1,97),(1,529),(1,618),(1,722),(1,920)]),
([v38,v0,v2,v3,v1,v7,v4,v21],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,5],[(0,904),(2,887),(3,912)]),
([v38,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v21,v7,v4),(v38,v21,v5)],[0,1,5],[(0,913),(1,857),(1,858)]),
([v0,v156,v2,v3,v1,v4,v5],[(v13,v2,v1),(v25,v13,v5),(v156,v25,v0)],[0,1,2,3,4,5],[(0,582),(0,921),(1,456),(1,702),(2,922),(4,455)]),
([v25,v0,v156,v2,v3,v1,v4,v5],[(v13,v2,v1),(v25,v13,v5),(v156,v25,v0)],[0,1,4],[(0,582)]),
([v94,v25,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v25,v13,v5),(v94,v25,v0)],[0,1,2,4],[(0,582),(0,608)]),
([v0,v201,v2,v3,v1,v4,v5],[(v11,v3,v5),(0xffff0000f0f0,v11,v4),(v201,0xffff0000f0f0,v0)],[0,1,2,3,4,5],[(0,531),(0,809),(1,923),(2,456),(3,924),(4,687)]),
([v25,v0,v2,v3,v213,v1,v4,v5],[(v13,v2,v1),(v25,v13,v5),(v213,v25,v3)],[0,3],[(0,687),(3,882)]),
([v69,v25,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v25,v13,v5),(v69,v25,v3)],[0,1,2,3],[(0,526),(0,687),(0,788)]),
([v0,v2,v3,v1,v223,v4,v5],[(v15,v3,v4),(0xfffff0f0,v15,v5),(v223,0xfffff0f0,v1)],[0,1,2,3,4,5],[(0,702),(1,926),(2,809),(3,807),(3,927),(4,925)]),
([v25,v0,v2,v3,v1,v4,0xffff0000ffffffcc,v5],[(v13,v2,v1),(v25,v13,v5),(0xffff0000ffffffcc,v25,v4)],[0,1,5],[(1,883),(2,927)]),
([v51,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v74,v7,v4),(v51,v74,v5)],[0,1,2,3,4,5],[(0,585),(0,671),(0,689),(0,927),(0,930),(2,928),(3,929)]),
([v51,v74,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v74,v7,v4),(v51,v74,v5)],[0,1,4,5],[(0,854),(0,859),(0,927),(2,931)]),
([v0,v156,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v25,v13,v5),(v156,v25,v0)],[0,1,4],[(4,586)]),
([v0,v201,v2,v3,v1,v4,v5,v11],[(v11,v3,v5),(0xffff0000f0f0,v11,v4),(v201,0xffff0000f0f0,v0)],[0,4,5],[(0,882),(5,775)]),
([v0,v2,v3,v1,v223,v4,v15,v5],[(v15,v3,v4),(0xfffff0f0,v15,v5),(v223,0xfffff0f0,v1)],[0,1,5],[(0,883),(3,932)]),
([v51,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v74,v7,v4),(v51,v74,v5)],[1,4,5],[(0,848),(0,854),(0,933)]),
([v25,v0,v2,v3,v1,v4,v43,v5],[(v13,v2,v1),(v25,v13,v5),(v43,v13,v4)],[0],[(5,934)]),
([v30,v74,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v74,v7,v4),(v30,v7,v5)],[0,1,5],[(0,863),(0,932),(2,931)]),
([v0,v2,v3,v1,v4,v43,v53,v5],[(v13,v2,v1),(v43,v13,v4),(v53,v0,v43)],[0,3,4],[(0,936),(0,938),(1,935),(2,558),(2,560),(3,635),(3,937),(4,228)]),
([v75,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v67,v17,v5),(v75,v3,v67)],[0,1,2,3,4,5],[(0,228),(0,727),(0,940),(1,426),(2,939),(3,656)]),
([v75,v0,v2,v3,v1,v4,v5,v67],[(v17,v0,v4),(v67,v17,v5),(v75,v3,v67)],[3],[(0,228),(1,942),(4,941)]),
([v36,v0,v2,v1,v4,v59,v5],[(v15,v3,v4),(v59,v15,v1),(v36,v3,v59)],[1,5],[(0,725),(2,945),(2,946),(3,943),(3,944)]),
([v0,v2,v3,v1,v4,v43,v92,v5],[(v13,v2,v1),(v43,v13,v4),(v92,v3,v43)],[3],[(0,341),(1,947),(2,758),(3,948)]),
([v61,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v43,v13,v4),(v61,v3,v43)],[0,1,2,3,4,5],[(0,341),(0,660),(0,663),(0,949),(2,426),(4,950)]),
([v61,v0,v2,v3,v1,v4,v43,v5],[(v13,v2,v1),(v43,v13,v4),(v61,v3,v43)],[3,5],[(0,341),(0,726),(2,729)]),
([v28,v0,v2,v3,v1,v4,v48],[(v11,v3,v5),(v48,v11,v1),(v28,v5,v48)],[1,3,4],[(0,635),(0,728),(0,941),(0,945),(0,946),(5,951),(5,952)]),
([v30,v0,v2,v3,v1,v4,v47],[(v7,v0,v1),(v47,v7,v5),(v30,v5,v47)],[1,3,4,5],[(0,560),(0,729),(0,942),(0,943),(0,944),(0,951),(0,952),(3,953)]),
([v0,v2,v3,v1,v4,v43,v5,v109],[(v13,v2,v1),(v43,v13,v4),(v109,v43,v5)],[0],[(0,892),(1,954),(2,913),(5,955)]),
([v65,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v43,v13,v4),(v65,v43,v5)],[0,1,2,3,4,5],[(0,656),(0,661),(0,663),(0,892),(0,956),(3,957)]),
([v65,v0,v2,v3,v1,v4,v43,v5],[(v13,v2,v1),(v43,v13,v4),(v65,v43,v5)],[0],[(0,892)]),
([v36,v0,v2,v1,v4,v15,v5],[(v15,v3,v4),(v59,v15,v1),(v36,v3,v59)],[0,1,3,5],[(0,93),(0,537),(0,737),(0,804),(2,958),(3,943),(3,959)]),
([v36,v0,v2,v1,v4,v15,v59,v5],[(v15,v3,v4),(v59,v15,v1),(v36,v3,v59)],[1,5],[(2,960),(3,944),(3,959)]),
([v75,v0,v2,v3,v1,v4,v17,v5],[(v17,v0,v4),(v67,v17,v5),(v75,v3,v67)],[0,3,5],[(0,241),(0,536),(1,942),(2,538)]),
([v61,v0,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v43,v13,v4),(v61,v3,v43)],[1,2,3,5],[(0,92),(0,345),(0,736),(1,93),(3,738)]),
([v28,v0,v2,v3,v1,v4,v11],[(v11,v3,v5),(v48,v11,v1),(v28,v5,v48)],[0,1,3,4,5],[(0,94),(0,557),(0,620),(0,738),(0,805),(0,961),(1,538),(2,962),(5,951),(5,963)]),
([v28,v0,v2,v3,v1,v4,v11,v48],[(v11,v3,v5),(v48,v11,v1),(v28,v5,v48)],[0,1],[(0,960),(5,952),(5,963)]),
([v30,v0,v2,v3,v1,v7,v4,v47],[(v7,v0,v1),(v47,v7,v5),(v30,v7,v5)],[0,1],[(0,959),(0,963)]),
([v65,v0,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v43,v13,v4),(v65,v5,v43)],[0,1,5],[(0,895)]),
([v0,v252,v2,v3,v1,v4,v5],[(v13,v2,v1),(v231,v13,v4),(v252,v231,v0)],[0,1,2,3,4,5],[(0,964),(0,965),(1,450),(4,449),(4,594),(4,657)]),
([v30,v0,v2,v263,v3,v1,v4,v5],[(v7,v0,v1),(v30,v7,v5),(v263,v30,v2)],[0,2],[(0,560),(0,668),(1,594)]),
([v79,v132,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v132,v17,v5),(v79,v132,v3)],[3],[(0,594),(1,611)]),
([v0,v140,v2,v3,v1,v4,v5],[(v12,v2,v5),(v161,v12,v4),(v140,v161,v0)],[0,1,2,3,4,5],[(0,669),(0,696),(0,966),(3,450),(3,967),(4,780)]),
([v30,v0,v2,v3,v170,v1,v4,v5],[(v7,v0,v1),(v30,v7,v5),(v170,v30,v3)],[0,3],[(0,780),(3,953)]),
([v58,v30,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v30,v7,v5),(v58,v30,v3)],[3],[(0,729),(0,780),(0,792)]),
([v0,v2,v3,v1,v152,v4,v5],[(v17,v0,v4),(v132,v17,v5),(v152,v132,v1)],[0,1,2,3,4,5],[(0,657),(0,670),(0,969),(1,930),(1,968),(2,696),(3,695)]),
([v30,v0,v2,v3,v1,v4,v245,v5],[(v7,v0,v1),(v30,v7,v5),(v245,v30,v4)],[5],[(0,930)]),
([v51,v30,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v30,v7,v5),(v51,v30,v4)],[1,4,5],[(0,930),(0,932)]),
([v0,v252,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v231,v13,v4),(v252,v231,v0)],[1,4,5],[(3,970),(4,596)]),
([v0,v140,v2,v3,v1,v4,v5,v12],[(v12,v2,v5),(v161,v12,v4),(v140,v161,v0)],[0,4,5],[(0,867),(0,953),(0,971),(4,782)]),
([v0,v2,v3,v1,v152,v4,v17,v5],[(v17,v0,v4),(v132,v17,v5),(v152,v132,v1)],[0,1,5],[(0,868),(2,972),(3,931)]),
([v36,v0,v2,v3,v1,v4,v5,v12],[(v12,v2,v5),(v10,v1,v4),(v36,v3,v10)],[0],[(0,251),(0,516),(2,603),(4,973),(5,974)]),
([v40,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v14,v4,v5),(v40,v3,v14)],[1,5],[(0,783),(0,842),(0,975),(2,839),(3,716),(3,976),(5,355)]),
([v37,v0,v2,v3,v1,v4,v12],[(v12,v2,v5),(v10,v1,v4),(v37,v5,v10)],[0,1,2,4,5],[(0,249),(0,516),(0,605),(0,716),(0,977),(0,980),(1,85),(1,978),(3,979)]),
([v37,v0,v2,v3,v1,v4,v10,v12],[(v12,v2,v5),(v10,v1,v4),(v37,v5,v10)],[0,1,2],[(0,980),(1,852),(4,981)]),
([v0,v2,v3,v1,v119,v4,v5],[(v7,v0,v1),(v14,v4,v5),(v119,v7,v14)],[0,1,2,3,4,5],[(0,674),(0,783),(0,983),(1,603),(1,984),(2,982),(3,515)]),
([v0,v2,v3,v1,v119,v7,v4,v5],[(v7,v0,v1),(v14,v4,v5),(v119,v7,v14)],[0,1,4,5],[(0,915),(0,985),(1,846)]),
([v0,v2,v3,v1,v119,v4,v5,v14],[(v7,v0,v1),(v14,v4,v5),(v119,v7,v14)],[0,5],[(1,847),(5,919)]),
([v0,v2,v3,v1,v4,v10,v5,v109],[(v12,v2,v5),(v10,v1,v4),(v109,v12,v10)],[0],[(0,980),(2,987),(4,985),(5,986)]),
([v51,v0,v2,v3,v1,v4,v5,v14],[(v7,v0,v1),(v14,v4,v5),(v51,v7,v14)],[1,4,5],[(0,981),(0,989),(0,990),(2,988)]),
([v76,v0,v2,v3,v1,v4,v5],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10)],[0,1,2,3,4,5],[(0,251),(0,355),(0,516),(0,991),(0,993),(0,994),(2,992)]),
([v76,v0,v2,v3,v1,v4,v5,v11],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10)],[0],[(0,995),(0,996),(3,990)]),
([v76,v0,v2,v3,v1,v4,v10,v5],[(v11,v3,v5),(v10,v4,v1),(v76,v11,v10)],[1],[(0,849),(5,933)]),
([v42,v0,v2,v1,v4,v22,v45,v5],[(v22,v2,v4),(v45,v3,v22),(v42,v3,v22)],[1,3,5],[(3,997),(4,998)]),
([v0,v2,v3,v1,v19,v54,v4,v5],[(v18,v3,v1),(v19,v0,v18),(v54,v2,v18)],[0,2,4,5],[(0,999),(1,300),(2,999),(4,300)]),
([v42,v0,v2,v3,v1,v4,v49,v5],[(v22,v2,v4),(v49,v0,v22),(v42,v3,v22)],[0,5],[(0,705),(1,1001),(5,1000)]),
([v56,v0,v2,v3,v1,v4,v22,v5],[(v22,v2,v4),(v49,v0,v22),(v56,v3,v49)],[3,4,5],[(0,300),(0,710),(2,712)]),
([v27,v0,v2,v1,v18,v4,v5],[(v18,v3,v1),(v19,v0,v18),(v27,v3,v19)],[1,3,4],[(0,289),(0,709),(0,997)]),
([v27,v0,v2,v1,v18,v19,v4,v5],[(v18,v3,v1),(v19,v0,v18),(v27,v3,v19)],[1,4],[(0,290),(0,997),(0,1003),(0,1004),(3,1002)]),
([v24,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v44,v2,v23),(v24,v5,v44)],[0,1,2,3,4,5],[(0,293),(0,712),(0,998),(0,1006),(0,1007),(3,1005)]),
([v24,v0,v2,v3,v1,v4,v23,v44],[(v23,v0,v5),(v44,v2,v23),(v24,v5,v44)],[0,1,2],[(0,294),(0,998),(0,1002),(0,1008),(0,1009)]),
([v0,v2,v3,v1,v19,v4,v59,v5],[(v18,v3,v1),(v19,v0,v18),(v59,v18,v4)],[0,4,5],[(0,1011),(2,937),(3,1006),(3,1010),(5,327)]),
([v28,v0,v2,v3,v1,v54,v4,v5],[(v18,v3,v1),(v54,v2,v18),(v28,v18,v5)],[0,5],[(0,635),(0,1013),(4,1012),(5,1007)]),
([v0,v2,v3,v1,v19,v4,v5,v48],[(v18,v3,v1),(v19,v0,v18),(v48,v18,v5)],[0,4],[(0,948),(4,344)]),
([v28,v0,v2,v3,v1,v19,v4,v5],[(v18,v3,v1),(v19,v0,v18),(v28,v18,v5)],[0,4],[(4,1014)]),
([v68,v0,v2,v3,v1,v18,v4,v5],[(v18,v3,v1),(v54,v2,v18),(v68,v54,v5)],[0,2],[(0,937)]),
([v0,v2,v3,v102,v4,v22,v45,v5],[(v22,v2,v4),(v45,v3,v22),(v102,v45,v1)],[3,5],[(0,291),(3,1003),(3,1015),(4,1008)]),
([v0,v2,v3,v1,v18,v4,v92,v5],[],[],[(0,1016),(2,1015),(3,1017),(3,1018)]),
([v31,v0,v2,v3,v1,v18,v4],[(v18,v3,v1),(v19,v0,v18),(v31,v19,v5)],[0,1,2,3,4,5],[(0,711),(0,999),(0,1001),(0,1011),(2,1013)]),
([v31,v0,v2,v3,v1,v18,v19,v4],[(v18,v3,v1),(v19,v0,v18),(v31,v19,v5)],[0,4],[(0,292),(0,1004),(3,1009)]),
([v31,v0,v2,v3,v1,v18,v4,v5],[(v18,v3,v1),(v19,v0,v18),(v31,v19,v5)],[0,4],[(0,948)]),
([v0,v221,v2,v3,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v221,v42,v0)],[0,1,2,3,4,5],[(0,629),(0,1021),(3,1019),(4,422),(4,1020)]),
([v42,v0,v221,v2,v3,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v221,v42,v0)],[4],[(4,422)]),
([v112,v182,v0,v2,v3,v1,v4,v5],[(v23,v0,v5),(v182,v3,v23),(v112,v182,v2)],[2],[(1,422),(2,1022)]),
([v0,v2,v3,v1,v216,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v216,v42,v1)],[0,1,2,3,4,5],[(0,629),(0,1026),(2,1025),(3,1024),(4,1023)]),
([v42,v0,v2,v3,v1,v216,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v216,v42,v1)],[1],[(3,1024)]),
([v98,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v66,v0,v18),(v98,v66,v5)],[0,1,2,3,4,5],[(0,622),(0,1024),(0,1027),(1,313),(1,1029),(2,651),(2,1028)]),
([v98,v66,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v66,v0,v18),(v98,v66,v5)],[0],[(0,1024),(4,1030)]),
([v0,v2,v3,v1,v159,v4,v5],[(v23,v0,v5),(v95,v2,v23),(v159,v95,v1)],[0,1,2,3,4,5],[(0,714),(0,1020),(0,1031),(0,1033),(1,1025),(2,1032),(3,652)]),
([v42,v0,v2,v3,v1,v4,v5,v211],[(v22,v2,v4),(v42,v3,v22),(v211,v42,v5)],[0,5],[(0,652),(4,1034)]),
([v80,v42,v0,v2,v3,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v80,v42,v5)],[0],[(0,652),(0,1035)]),
([v42,v0,v2,v3,v1,v4,v5,v23],[(v22,v2,v4),(v42,v3,v22),(v23,v0,v5)],[0],[(0,313),(0,1036),(4,1020),(5,1037)]),
([v42,v0,v2,v3,v1,v4,v5,v16],[(v22,v2,v4),(v42,v3,v22),(v16,v1,v5)],[1],[(0,1038),(1,651),(2,1025),(5,1039)]),
([v0,v221,v2,v3,v1,v4,v22,v5],[(v22,v2,v4),(v42,v3,v22),(v221,v42,v0)],[3,4,5],[(2,1040),(5,1022)]),
([v0,v2,v3,v1,v216,v4,v22,v5],[(v22,v2,v4),(v42,v3,v22),(v216,v42,v1)],[1,3,5],[(2,1042),(3,1041)]),
([v98,v0,v2,v3,v1,v18,v4,v5],[],[],[(2,1043)]),
([v0,v2,v3,v1,v159,v4,v5,v23],[(v23,v0,v5),(v95,v2,v23),(v159,v95,v1)],[0,1,2],[(0,1045),(5,1044)]),
([v42,v250,v0,v2,v3,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22),(v250,v0,v22)],[3,4,5],[(0,706),(0,1022),(5,706),(5,1022)]),
([v42,v0,v2,v3,v1,v4,v43,v5],[(v22,v2,v4),(v42,v3,v22),(v43,v1,v22)],[5],[(0,707),(5,1046)]),
([v28,v66,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v66,v0,v18),(v28,v5,v18)],[0,1,4],[(0,708),(0,1041),(4,1030)]),
([v42,v0,v2,v3,v1,v4,v5,v117],[],[],[(4,1048),(5,1047)]),
([v28,v251,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v251,v2,v18),(v28,v18,v5)],[0,2],[(0,1044),(1,1035)]),
([v0,v2,v3,v1,v178,v4,v5],[(v18,v3,v1),(v22,v2,v4),(v178,v18,v22)],[0,1,2,3,4,5],[(0,621),(0,1049),(0,1051),(1,621),(4,1036),(4,1050)]),
([v0,v2,v3,v1,v178,v18,v4,v5],[(v18,v3,v1),(v22,v2,v4),(v178,v18,v22)],[3],[(2,1018)]),
([v98,v0,v2,v3,v1,v4,v5,v23],[(v18,v3,v1),(v23,v0,v5),(v98,v18,v23)],[0,4],[(0,1053),(2,488),(4,1052)]),
([v28,v0,v2,v3,v1,v4,v22,v5],[(v18,v3,v1),(v22,v2,v4),(v28,v18,v5)],[5],[(0,651),(0,1051),(1,1054),(5,1055)]),
([v75,v0,v2,v3,v1,v4,v5,v23],[(v23,v0,v5),(v67,v23,v4),(v75,v3,v67)],[0,3,5],[(0,327),(0,718),(0,719),(4,941)]),
([v61,v0,v2,v3,v1,v4,v22,v5],[(v22,v2,v4),(v43,v22,v1),(v61,v3,v43)],[1,3,5],[(0,344),(0,731),(2,732)]),
([v36,v0,v2,v1,v18,v4,v5],[(v18,v3,v1),(v59,v18,v4),(v36,v3,v59)],[1,3,5],[(0,717),(0,730),(2,945),(2,1056)]),
([v36,v0,v2,v1,v18,v4,v59,v5],[(v18,v3,v1),(v59,v18,v4),(v36,v3,v59)],[1,5],[(2,946),(2,1056),(3,1057)]),
([v30,v0,v2,v3,v1,v4,v23],[(v23,v0,v5),(v47,v23,v1),(v30,v5,v47)],[0,1,3,5],[(0,732),(0,951),(0,1010),(0,1048),(0,1060),(1,719),(2,1058),(3,1059)]),
([v30,v0,v2,v3,v1,v4,v23,v47],[(v23,v0,v5),(v47,v23,v1),(v30,v5,v47)],[0,1],[(0,952),(0,1057),(0,1060)]),
([v28,v0,v2,v3,v1,v18,v4,v48],[(v18,v3,v1),(v48,v18,v5),(v28,v18,v5)],[0,1],[(0,1056),(5,1060)]),
([v0,v2,v3,v1,v4,v43,v5,v117],[(v22,v2,v4),(v43,v22,v1),(v117,v22,v5)],[0,1],[(0,955),(5,955)]),
([v28,v0,v2,v3,v1,v4,v59,v5],[],[],[(5,1061)]),
([v0,v2,v3,v1,v18,v4,v5,v141],[],[],[(0,1062),(3,1063),(3,1064)]),
([v65,v0,v2,v3,v1,v4,v22,v5],[(v22,v2,v4),(v43,v22,v1),(v65,v43,v5)],[0,1,5],[(0,955)]),
([v0,v139,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v139,v28,v0)],[0,1,2,3,4,5],[(0,427),(0,631),(0,1027),(1,664),(1,1065),(2,1066)]),
([v28,v0,v139,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v139,v28,v0)],[0,4],[(0,1027)]),
([v98,v28,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v98,v28,v0)],[4],[(0,1027),(0,1041)]),
([v0,v232,v2,v3,v1,v4,v5],[(v18,v3,v1),(v203,v18,v4),(v232,v203,v0)],[0,1,2,3,4,5],[(0,733),(0,1068),(1,1067),(2,427),(4,649),(4,1054)]),
([v28,v0,v2,v262,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v262,v28,v2)],[0,2],[(0,632),(0,635),(1,649)]),
([v80,v157,v0,v2,v3,v1,v4,v5],[(v22,v2,v4),(v157,v22,v5),(v80,v157,v3)],[3],[(0,649),(1,1044)]),
([v0,v2,v3,v1,v222,v4,v5],[(v22,v2,v4),(v157,v22,v5),(v222,v157,v1)],[0,1,2,3,4,5],[(0,633),(0,664),(0,1054),(0,1070),(3,1071),(4,1069)]),
([v28,v0,v2,v3,v1,v4,0xffff0000fffffff0,v5],[(v18,v3,v1),(v28,v18,v5),(0xffff0000fffffff0,v28,v4)],[5],[(2,1071)]),
([v107,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v107,v28,v4)],[0,1,2,3,4,5],[(0,634),(0,651),(0,1071),(0,1072),(2,634),(2,651),(2,1071),(2,1072)]),
([v107,v28,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v107,v28,v4)],[5],[(0,1073),(2,1071)]),
([v0,v139,v2,v3,v1,v18,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v139,v28,v0)],[0,4],[(4,1030)]),
([v0,v232,v2,v3,v1,v18,v4,v5],[(v18,v3,v1),(v203,v18,v4),(v232,v203,v0)],[4,5],[(4,1035)]),
([v0,v2,v3,v1,v222,v4,v22,v5],[(v22,v2,v4),(v157,v22,v5),(v222,v157,v1)],[0,1,5],[(3,1073)]),
([v107,v0,v2,v3,v1,v18,v4,v5],[],[],[(0,1074)]),
([v28,v203,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5),(v203,v18,v4)],[0,5],[(0,1073),(2,1073)]),
([v36,v0,v2,v3,v1,v4,v5,v23],[(v23,v0,v5),(v10,v4,v1),(v36,v3,v10)],[0],[(0,355),(2,1038),(4,1075),(5,1076)]),
([v0,v2,v3,v1,v179,v4,v5],[(v18,v3,v1),(v14,v4,v5),(v179,v18,v14)],[0,1,2,3,4,5],[(0,637),(0,1077),(1,1038),(2,637),(2,1077),(3,715),(4,1038),(5,715)]),
([v0,v2,v3,v1,v179,v18,v4,v5],[(v18,v3,v1),(v14,v4,v5),(v179,v18,v14)],[3],[(0,1078)]),
([v0,v2,v3,v1,v179,v4,v5,v14],[],[],[(3,1064)]),
([v0,v2,v3,v1,v4,v10,v5,v111],[],[],[(0,1080),(2,1079),(3,1079),(4,1078)]),
([v107,v0,v2,v3,v1,v4,v5,v14],[],[],[(0,1081),(2,1081),(3,990)]),
([v106,v0,v2,v3,v1,v4,v5],[(v23,v0,v5),(v10,v1,v4),(v106,v23,v10)],[0,1,2,3,4,5],[(0,355),(0,716),(0,1082),(0,1084),(1,355),(1,716),(2,1083),(3,1083)]),
([v106,v0,v2,v3,v1,v4,v5,v23],[(v23,v0,v5),(v10,v1,v4),(v106,v23,v10)],[0,4],[(0,990),(0,1086),(4,1085)]),
([v106,v0,v2,v3,v1,v4,v10,v5],[],[],[(4,1074)]),
([v40,v0,v2,v1,v4,v5,v14,v32],[(v14,v4,v5),(v32,v3,v14),(v40,v3,v14)],[0,1,3,5],[(1,1087),(4,1087)]),
([v0,v2,v3,v1,v4,v21,v43,v5],[(v10,v1,v4),(v21,v0,v10),(v43,v2,v10)],[0,2,4],[(0,1090),(1,935),(2,1089),(3,1088),(4,873)]),
([v36,v0,v2,v3,v1,v4,v21,v5],[(v10,v4,v1),(v21,v0,v10),(v36,v3,v10)],[0,1],[(0,828),(0,1092),(5,1091)]),
([v57,v0,v2,v3,v1,v4,v10,v5],[(v10,v4,v1),(v21,v0,v10),(v57,v3,v21)],[3,4,5],[(0,832),(0,935),(2,835)]),
([v25,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v26,v2,v16),(v25,v5,v26)],[0,1,2],[(0,834),(0,835),(0,871),(0,1087),(0,1096),(1,1094),(2,1095),(3,1093)]),
([v25,v0,v2,v3,v1,v4,v16,v26],[(v16,v5,v1),(v26,v2,v16),(v25,v5,v26)],[0,1,2],[(0,872),(0,1087),(0,1097),(0,1098),(0,1099)]),
([v0,v2,v3,v1,v4,v16,v26,v14],[(v16,v5,v1),(v26,v2,v16),(v14,v5,v4)],[0,1,2,5],[(1,850),(2,1095),(2,1100),(2,1101),(2,1102),(5,1096)]),
([v0,v2,v3,v1,v4,v21,v5,v50],[(v10,v1,v4),(v21,v0,v10),(v50,v10,v5)],[0,4],[(0,1104),(2,1103),(3,1103),(4,894)]),
([v37,v0,v2,v3,v1,v4,v21,v5],[(v10,v1,v4),(v21,v0,v10),(v37,v10,v5)],[0,1,4,5],[(0,1101),(1,1101),(4,1105)]),
([v0,v2,v3,v129,v4,v5,v14,v32],[(v14,v4,v5),(v32,v3,v14),(v129,v32,v1)],[0,3,5],[(0,869),(1,1098),(3,1080),(4,1098)]),
([v38,v0,v2,v3,v1,v4,v10],[(v10,v1,v4),(v21,v0,v10),(v38,v21,v5)],[0,1,2,3,4,5],[(0,833),(0,1090),(0,1092),(0,1106),(1,833),(1,1090),(1,1092),(1,1106)]),
([v38,v0,v2,v3,v1,v4,v10,v21],[(v10,v1,v4),(v21,v0,v10),(v38,v21,v5)],[0,1,4,5],[(0,870),(2,1099),(3,1099)]),
([v38,v0,v2,v3,v1,v4,v10,v5],[(v10,v1,v4),(v21,v0,v10),(v38,v21,v5)],[0,1,4,5],[(0,1095),(0,1102),(0,1104),(1,1095),(1,1102)]),
([v0,v180,v2,v3,v1,v4,v5],[(v14,v4,v5),(v40,v3,v14),(v180,v40,v0)],[0,1,2,3,4,5],[(0,493),(0,836),(0,975),(1,1107),(3,1108),(4,470)]),
([v40,v0,v180,v2,v3,v1,v4,v5],[(v14,v4,v5),(v40,v3,v14),(v180,v40,v0)],[4],[(4,470)]),
([v90,v73,v0,v2,v3,v1,v4,v5],[(v16,v5,v1),(v73,v2,v16),(v90,v73,v3)],[0,1,3],[(0,470),(1,1109)]),
([v0,v2,v3,v1,v217,v4,v5],[(v14,v4,v5),(v40,v3,v14),(v217,v40,v1)],[0,1,2,3,4,5],[(0,975),(1,1110),(2,975),(3,1084),(4,1110)]),
([v40,v0,v2,v3,v1,v217,v4,v5],[(v14,v4,v5),(v40,v3,v14),(v217,v40,v1)],[1],[(3,1084)]),
([v106,v93,v0,v2,v3,v1,v4,v5],[(v10,v1,v4),(v93,v0,v10),(v106,v93,v5)],[0],[(0,1084),(4,1111)]),
([v40,v0,v2,v3,v1,v4,v16],[(v14,v5,v4),(v40,v3,v14),(v16,v1,v5)],[0,1,3,5],[(0,838),(0,839),(0,842),(0,850),(0,1113),(0,1114),(2,1115),(5,1112)]),
([v0,v180,v2,v3,v1,v4,v5,v14],[(v14,v4,v5),(v40,v3,v14),(v180,v40,v0)],[3,4],[(5,1116)]),
([v0,v2,v3,v1,v217,v4,v5,v14],[(v14,v4,v5),(v40,v3,v14),(v217,v40,v1)],[1,3],[(3,1117)]),
([v40,v0,v2,v3,v1,v4,v5,v67],[],[],[(1,1120),(3,1118),(4,1119)]),
([v36,v93,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v93,v0,v10),(v36,v3,v10)],[1,3,4],[(0,829),(0,1116),(4,1109)]),
([v40,v0,v2,v3,v1,v4,v16,v14],[(v14,v5,v4),(v40,v3,v14),(v16,v1,v5)],[0,1,3,5],[(0,850),(0,1121),(3,1122)]),
([v40,v0,v2,v3,v1,v4,v5,v50],[],[],[(0,1124),(2,1124),(3,1123)]),
([v37,v93,v0,v2,v3,v1,v4,v5],[(v10,v1,v4),(v93,v0,v10),(v37,v5,v10)],[0,1,4,5],[(0,1117),(0,1122),(1,1122),(4,1111)]),
([v75,v0,v2,v3,v1,v4,v5,v14],[(v14,v4,v5),(v67,v0,v14),(v75,v3,v67)],[3,4],[(0,873)]),
([v36,v0,v2,v1,v4,v10,v59,v5],[(v10,v4,v1),(v59,v3,v10),(v36,v3,v10)],[1,3],[(2,1126),(3,1125)]),
([v0,v2,v3,v1,v4,v43,v59,v5],[(v10,v1,v4),(v43,v2,v10),(v59,v3,v10)],[2,3],[(0,947),(1,947)]),
([v36,v0,v2,v3,v1,v4,v43,v5],[(v10,v1,v4),(v43,v2,v10),(v36,v3,v10)],[1],[(0,819),(5,1127)]),
([v61,v0,v2,v3,v1,v4,v10,v5],[(v10,v1,v4),(v43,v2,v10),(v61,v3,v43)],[2,3,5],[(0,820),(0,947),(2,822)]),
([v28,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v48,v3,v16),(v28,v5,v48)],[0,1,3,4],[(0,821),(0,945),(0,1088),(0,1119),(0,1126),(0,1129),(0,1130),(1,1128)]),
([v28,v0,v2,v3,v1,v4,v16,v48],[(v16,v5,v1),(v48,v3,v16),(v28,v5,v48)],[1,3],[(0,946),(0,1126),(5,1131)]),
([v0,v2,v3,v1,v4,v16,v48,v14],[(v16,v5,v1),(v48,v3,v16),(v14,v5,v4)],[1,3,5],[(0,1129),(4,1132),(4,1134),(5,1133)]),
([v30,v0,v2,v3,v1,v4,v16],[(v16,v1,v5),(v47,v0,v16),(v30,v5,v47)],[0,1,3,4,5],[(0,822),(0,943),(0,1089),(0,1120),(0,1125),(0,1133),(0,1137),(1,1136),(3,1135)]),
([v30,v0,v2,v3,v1,v4,v16,v47],[(v16,v1,v5),(v47,v0,v16),(v30,v5,v47)],[1,4],[(0,944),(0,1125),(0,1131)]),
([v0,v2,v3,v1,v4,v16,v47,v14],[(v16,v1,v5),(v47,v0,v16),(v14,v5,v4)],[1,4,5],[(0,1137),(2,1132),(2,1138),(5,1130)]),
([v0,v2,v3,v1,v4,v43,v5,v50],[(v10,v1,v4),(v43,v2,v10),(v50,v10,v5)],[0,2],[(0,1140),(1,954),(3,1139)]),
([v37,v0,v2,v3,v1,v4,v43,v5],[(v10,v1,v4),(v43,v2,v10),(v37,v10,v5)],[0],[(0,980),(4,1141)]),
([v65,v0,v2,v3,v1,v4,v10,v5],[(v10,v1,v4),(v43,v2,v10),(v65,v43,v5)],[0,1,2,5],[(0,1134),(0,1138),(0,1140),(2,1137),(3,1129)]),
([v0,v202,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v202,v36,v0)],[0,1,2,3,4,5],[(0,474),(0,823),(0,1143),(1,1142),(2,469),(4,1075)]),
([v36,v0,v202,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v202,v36,v0)],[4],[(2,469)]),
([v90,v84,v0,v2,v3,v1,v4,v5],[(v16,v5,v1),(v84,v3,v16),(v90,v84,v2)],[0,1,2],[(0,469),(2,1116)]),
([v0,v160,v2,v3,v1,v4,v5],[(v16,v5,v1),(v84,v3,v16),(v160,v84,v0)],[0,1,2,3,4,5],[(1,973),(1,1144),(2,474),(2,1145),(4,490)]),
([v36,v0,v2,0xcfcfcfcccfcfcfcc,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(0xcfcfcfcccfcfcfcc,v36,v2)],[2],[(1,490)]),
([v101,v36,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v101,v36,v2)],[2],[(0,824),(0,1146),(1,490)]),
([v0,v2,v3,v1,v183,v4,v5],[(v14,v5,v4),(v128,v2,v14),(v183,v128,v1)],[0,1,2,3,4,5],[(0,973),(0,1075),(0,1148),(0,1149),(3,994),(4,1147)]),
([v36,v0,v2,v3,v1,v4,v5,v172],[(v10,v4,v1),(v36,v3,v10),(v172,v36,v5)],[0,5],[(0,994),(4,1150)]),
([v76,v36,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v76,v36,v5)],[0],[(0,994),(0,1151)]),
([v0,v202,v2,v3,v1,v4,v10,v5],[(v10,v4,v1),(v36,v3,v10),(v202,v36,v0)],[3,4,5],[(2,1152),(4,1109)]),
([v0,v160,v2,v3,v1,v4,v5,v16],[(v16,v5,v1),(v84,v3,v16),(v160,v84,v0)],[0,1,3,4],[(0,827),(0,1153),(4,1146)]),
([v0,v2,v3,v1,v183,v4,v5,v14],[(v14,v5,v4),(v128,v2,v14),(v183,v128,v1)],[0,1,2],[(0,1155),(3,1154)]),
([v36,v244,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v244,v2,v10)],[1,2,3],[(0,826),(0,1146),(1,826),(1,1146)]),
([v36,v0,v2,v3,v4,v10,v5,v16],[(v10,v4,v1),(v36,v3,v10),(v16,v1,v5)],[0,1,3,5],[(0,831),(0,849),(0,1156)]),
([v36,v0,v2,v3,v1,v10,v5,v14],[(v10,v4,v1),(v36,v3,v10),(v14,v4,v5)],[0,1,3],[(0,1156)]),
([v36,v0,v2,v3,v1,v4,v5,v50],[],[],[(2,1158),(5,1157)]),
([v37,v36,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10),(v37,v10,v5)],[0,3],[(0,1151),(0,1154)]),
([v0,v2,v3,v10,v16,v14],[(v16,v5,v1),(v14,v5,v4),(v10,v1,v4)],[0,1,2,3,4,5],[(0,476),(0,843),(0,1100),(0,1114),(0,1121),(0,1132),(0,1156),(1,476),(1,843),(1,1114),(1,1121),(1,1132),(1,1156),(2,1100),(2,1132),(2,1156),(3,1100),(3,1132),(3,1156),(4,476),(4,843),(4,1114),(4,1121),(4,1132),(4,1156),(5,1132),(5,1156)]),
([v37,v0,v2,v3,v1,v10,v14],[(v14,v4,v5),(v10,v4,v1),(v37,v5,v10)],[0,1,5],[(0,845),(0,852),(0,1101),(0,1115),(0,1122),(1,849),(1,1160),(2,1159)]),
([v0,v2,v3,v1,v4,v5,v50,v111],[(v10,v1,v4),(v50,v10,v5),(v111,v0,v50)],[4],[(0,1104),(2,980),(2,1140),(3,980),(3,1140),(4,890)]),
([v99,v0,v2,v3,v1,v4,v5],[(v14,v4,v5),(v50,v14,v1),(v99,v3,v50)],[0,1,2,3,4,5],[(0,479),(0,890),(0,1161),(2,479),(2,1161)]),
([v99,v0,v2,v3,v1,v4,v5,v50],[(v14,v4,v5),(v50,v14,v1),(v99,v3,v50)],[3],[(0,890),(0,1162),(2,1162)]),
([v37,v0,v2,v3,v1,v4,v50],[(v16,v5,v1),(v50,v16,v4),(v37,v5,v50)],[1,4,5],[(0,980),(0,1162),(0,1163),(0,1164),(1,980),(1,1162),(1,1163),(1,1164)]),
([v99,v0,v2,v3,v1,v4,v5,v14],[(v14,v4,v5),(v50,v14,v1),(v99,v3,v50)],[1,3],[(0,894)]),
([v99,v0,v2,v3,v1,v4,v10,v5],[(v10,v4,v1),(v50,v10,v5),(v99,v3,v50)],[0,3,5],[(0,954),(0,1162),(2,864),(2,866)]),
([v37,v0,v2,v3,v1,v4,v16],[(v16,v5,v1),(v50,v16,v4),(v37,v5,v50)],[0,1,4,5],[(0,866),(0,1103),(0,1139),(0,1158),(0,1163),(1,865),(1,1124),(2,1166),(3,1165)]),
([v37,v0,v2,v3,v1,v4,v16,v50],[(v16,v5,v1),(v50,v16,v4),(v37,v5,v50)],[1,5],[(0,1164),(1,1167),(2,1166)]),
([v37,v0,v2,v3,v1,v4,v10,v50],[(v10,v1,v4),(v50,v10,v5),(v37,v10,v5)],[0,1],[(0,1166),(1,1166)]),
([v0,v162,v2,v3,v1,v4,v5],[(v10,v1,v4),(v37,v10,v5),(v162,v37,v0)],[0,1,2,3,4,5],[(0,480),(0,977),(0,1082),(0,1168),(1,480),(1,977),(1,1168)]),
([v37,v0,v162,v2,v3,v1,v4,v5],[(v10,v1,v4),(v37,v10,v5),(v162,v37,v0)],[0,4],[(0,1082)]),
([v106,v37,v0,v2,v3,v1,v4,v5],[(v10,v1,v4),(v37,v10,v5),(v106,v37,v0)],[4],[(0,1082),(0,1117)]),
([v0,v181,v2,v3,v1,v4,v5],[(v16,v1,v5),(v120,v16,v4),(v181,v120,v0)],[0,1,2,3,4,5],[(0,979),(0,1170),(1,495),(1,1169),(2,480),(4,993)]),
([v37,v0,v2,0xccccccccffffffcc,v3,v1,v4,v5],[(v10,v1,v4),(v37,v10,v5),(0xccccccccffffffcc,v37,v2)],[0,2],[(0,980),(1,978),(1,993)]),
([v76,v37,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v37,v10,v5),(v76,v37,v3)],[3],[(0,993),(0,1154)]),
([v0,v162,v2,v3,v1,v4,v10,v5],[(v10,v1,v4),(v37,v10,v5),(v162,v37,v0)],[0,1,4,5],[(2,1171),(3,1171),(4,1111)]),
([v0,v181,v2,v3,v1,v4,v5,v16],[(v16,v1,v5),(v120,v16,v4),(v181,v120,v0)],[1,4,5],[(0,1159),(0,1173),(3,1172),(4,1151)])
]

def g6_L8 : Array W6Node := Array.mk [
([v0,v2,v9,v8,v1,v4,v5],[(v9,v3,v0),(v8,v3,v2)],[0,1,2,3,4,5],[(0,0),(0,3),(0,5),(0,6),(0,7),(0,8),(0,9),(0,11),(0,12),(1,1),(1,2),(1,10),(2,3),(2,5),(2,6),(2,7),(2,8),(2,9),(2,11),(3,4),(4,1),(4,2),(4,10),(5,4)]),
([v0,v2,v9,v1,v4,v5,v11],[(v9,v3,v0),(v11,v3,v5)],[0,1,2,3,4,5],[(0,5),(0,15),(0,17),(0,18),(0,19),(0,20),(0,23),(0,25),(0,28),(0,29),(0,30),(0,32),(1,16),(1,27),(2,2),(2,13),(2,26),(3,21),(3,22),(3,24),(4,33),(5,14),(5,31)]),
([v0,v2,v3,v20,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3)],[0,1,2,3,4,5],[(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(1,34),(1,35),(1,36),(1,37),(2,38),(2,39),(2,40),(2,41),(2,42),(3,38),(3,39),(3,40),(3,41),(3,42),(4,34),(4,35),(4,36),(4,37)]),
([v0,v2,v6,v3,v20,v1,v4,v5],[(v6,v0,v2),(v20,v6,v3)],[0,1,2,3,4,5],[(0,34),(0,45),(0,46),(0,49),(0,50),(0,51),(0,55),(0,56),(0,57),(0,58),(0,59),(1,15),(1,43),(1,44),(1,48),(2,49),(2,55),(2,56),(2,57),(2,58),(2,59),(3,47),(3,52),(3,53),(3,54),(4,15),(4,43),(4,44),(4,48)]),
([v34,v0,v2,v3,v1,v4,v5],[(v6,v0,v2),(v34,v6,v3)],[0,1,2,3,4,5],[(0,34),(0,60),(0,61),(0,65),(0,66),(0,67),(0,68),(0,69),(1,64),(2,65),(2,66),(2,67),(2,68),(3,62),(3,63),(4,64)]),
([v34,v0,v2,v6,v3,v1,v4,v5],[(v6,v0,v2),(v34,v6,v3)],[0,1,2,3,4,5],[(0,1),(0,16),(0,34),(0,45),(0,70),(0,72),(0,73),(0,74),(0,76),(0,77),(2,1),(2,16),(2,72),(2,73),(2,76),(2,77),(3,71),(3,75)]),
([v0,v2,v3,v1,v29,v4,v5],[(v6,v0,v2),(v29,v6,v1)],[0,1,2,3,4,5],[(0,36),(0,80),(0,81),(0,82),(0,85),(0,86),(0,87),(0,88),(0,89),(1,78),(2,85),(2,86),(2,87),(2,88),(3,5),(3,79),(3,83),(3,84),(4,78),(5,5),(5,83)]),
([v0,v2,v6,v3,v1,v29,v4,v5],[(v6,v0,v2),(v29,v6,v1)],[0,1,2,3,4,5],[(0,46),(0,51),(0,74),(0,93),(0,94),(0,95),(0,96),(0,97),(0,98),(1,6),(1,25),(1,90),(1,91),(2,93),(2,94),(2,97),(2,98),(3,84),(3,92),(4,6),(4,25),(4,90),(4,91)]),
([v39,v0,v2,v3,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5)],[0,1,2,3,4,5],[(0,7),(0,62),(0,84),(0,99),(0,100),(0,101),(0,102),(0,103),(0,106),(0,107),(1,7),(1,102),(1,103),(1,106),(2,104),(2,105),(3,104),(3,105)]),
([v39,v0,v2,v3,v8,v1,v4,v5],[(v8,v2,v3),(v39,v8,v5)],[0,1,2,3,4,5],[(0,8),(0,26),(0,47),(0,71),(0,75),(0,84),(0,92),(0,108),(0,111),(1,8),(1,26),(1,111),(2,110),(3,110),(4,109),(4,112),(5,109),(5,112)]),
([v0,v2,v3,v1,v19,v4,v5],[(v9,v0,v3),(v19,v9,v1)],[0,1,2,3,4,5],[(0,36),(0,115),(0,120),(0,122),(0,127),(0,128),(0,129),(0,130),(0,131),(0,132),(1,85),(1,116),(1,117),(1,118),(2,123),(2,124),(2,126),(3,121),(4,113),(4,119),(4,125),(5,114)]),
([v0,v2,v6,v3,v1,v4,v49,v5],[(v6,v0,v2),(v49,v6,v4)],[0,1,2,3,4,5],[(0,56),(0,76),(0,93),(0,97),(0,139),(0,141),(0,144),(1,3),(1,23),(1,48),(1,135),(1,136),(1,138),(1,145),(1,146),(1,147),(2,121),(2,137),(2,140),(2,143),(3,111),(3,142),(5,9),(5,133),(5,134)]),
([v24,v0,v2,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5)],[0,1,2,3,4,5],[(0,66),(0,121),(0,149),(0,150),(0,151),(0,152),(0,155),(0,156),(0,157),(0,158),(0,159),(0,160),(0,161),(1,104),(1,153),(1,154),(3,148)]),
([v24,v0,v2,v6,v3,v1,v4,v5],[(v6,v2,v0),(v24,v6,v5)],[0,1,2,3,4,5],[(0,4),(0,10),(0,24),(0,27),(0,49),(0,73),(0,77),(0,94),(0,112),(0,121),(0,137),(0,139),(0,163),(0,164),(0,165),(0,166),(0,167),(1,110),(3,162)]),
([v0,v2,v6,v3,v1,v18,v4,v5],[(v6,v0,v2),(v18,v3,v1)],[0,1,2,3,4,5],[(0,36),(0,51),(0,95),(0,118),(0,158),(0,168),(0,169),(0,170),(0,171),(0,176),(0,177),(1,18),(2,118),(2,158),(2,176),(2,177),(3,62),(3,71),(3,79),(3,172),(3,173),(3,174),(3,175),(4,18)]),
([v0,v2,v6,v3,v1,v4,v15,v5],[(v6,v0,v2),(v15,v3,v4)],[0,1,2,3,4,5],[(0,2),(0,56),(0,159),(0,176),(0,179),(0,180),(0,181),(0,189),(1,17),(1,36),(1,190),(2,66),(2,73),(2,140),(2,183),(2,187),(3,83),(3,106),(3,119),(3,182),(3,184),(3,185),(3,186),(3,188),(4,5),(4,19),(4,114),(4,178)]),
([v0,v2,v6,v3,v1,v4,v10,v5],[(v6,v0,v2),(v10,v1,v4)],[0,1,2,3,4,5],[(0,42),(0,68),(0,85),(0,97),(0,160),(0,176),(0,191),(0,192),(0,193),(0,194),(0,199),(0,200),(0,202),(0,203),(1,11),(1,28),(2,161),(2,167),(2,187),(2,201),(3,196),(3,197),(3,198),(4,12),(4,104),(4,110),(4,132),(4,195)]),
([v0,v2,v6,v3,v1,v4,v5,v14],[(v6,v0,v2),(v14,v4,v5)],[0,1,2,3,4,5],[(0,69),(0,89),(0,144),(0,156),(0,165),(0,189),(0,201),(0,202),(0,204),(0,205),(0,206),(0,208),(0,212),(1,29),(2,201),(3,11),(3,42),(3,107),(3,126),(3,207),(3,209),(3,210),(3,211),(3,213),(4,29),(5,11)]),
([v0,v2,v3,v1,v4,v12,v11],[(v12,v2,v5),(v11,v3,v5)],[0,1,2,3,4,5],[(0,19),(0,114),(0,214),(0,215),(0,219),(0,220),(0,221),(0,224),(1,19),(1,114),(1,214),(1,215),(1,220),(1,221),(1,224),(2,218),(3,218),(4,216),(4,217),(4,222),(4,223),(4,225),(5,216),(5,217),(5,222),(5,223),(5,225)]),
([v0,v2,v3,v1,v7,v29,v4,v5],[(v7,v0,v1),(v29,v2,v7)],[0,1,2,3,4,5],[(0,182),(0,230),(0,231),(0,232),(0,236),(0,239),(0,240),(0,242),(0,243),(1,78),(1,228),(2,237),(2,238),(2,241),(3,178),(3,229),(3,233),(3,234),(3,235),(4,226),(4,227),(5,20)]),
([v33,v0,v2,v3,v1,v4,v5],[(v17,v0,v4),(v33,v3,v17)],[0,1,2,3,4,5],[(0,21),(0,78),(0,245),(0,247),(0,248),(0,252),(0,253),(0,254),(0,255),(0,256),(0,257),(0,258),(1,184),(1,246),(2,244),(3,249),(3,250),(4,251)]),
([v33,v0,v2,v3,v1,v4,v17,v5],[(v17,v0,v4),(v33,v3,v17)],[0,1,2,3,4,5],[(0,22),(0,78),(0,218),(0,228),(0,260),(0,263),(0,264),(0,265),(0,267),(0,269),(0,270),(1,186),(1,266),(1,271),(2,259),(3,261),(3,268),(4,262)]),
([v0,v2,v3,v1,v7,v4,v22,v5],[(v7,v0,v1),(v22,v2,v4)],[0,1,2,3,4,5],[(0,85),(0,119),(0,240),(0,273),(0,274),(0,275),(0,279),(0,280),(0,281),(0,288),(0,289),(1,118),(1,282),(1,287),(1,290),(2,249),(2,261),(2,283),(3,272),(3,276),(3,277),(3,278),(5,18),(5,284),(5,285),(5,286)]),
([v0,v2,v3,v1,v7,v4,v15,v5],[(v15,v3,v4),(v7,v0,v1)],[0,1,2,3,4,5],[(0,119),(0,274),(0,295),(0,296),(0,297),(0,298),(0,299),(0,304),(0,305),(1,85),(1,255),(1,306),(2,17),(2,300),(2,301),(2,302),(3,83),(3,214),(3,242),(3,289),(3,291),(3,292),(3,293),(3,294),(4,220),(5,253),(5,263),(5,303)]),
([v0,v2,v3,v1,v4,v23,v12],[(v12,v2,v5),(v23,v0,v5)],[0,1,2,3,4,5],[(0,79),(0,114),(0,229),(0,272),(0,309),(0,312),(0,313),(0,315),(0,317),(0,318),(0,321),(2,256),(2,264),(2,310),(2,311),(3,274),(3,308),(4,307),(4,319),(4,320),(4,322),(5,314),(5,316)]),
([v0,v2,v3,v1,v7,v19,v4,v5],[(v7,v0,v1),(v19,v3,v7)],[0,1,2,3,4,5],[(0,120),(0,182),(0,230),(0,299),(0,326),(0,330),(0,332),(0,333),(0,336),(0,337),(0,338),(0,339),(1,265),(1,325),(2,331),(2,334),(3,215),(3,327),(3,328),(3,329),(4,323),(4,324),(4,335)]),
([v27,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v27,v3,v7)],[0,1,2,3,4,5],[(0,120),(0,184),(0,216),(0,273),(0,291),(0,341),(0,342),(0,344),(0,347),(0,348),(0,349),(0,350),(1,343),(2,300),(2,340),(2,345),(4,346)]),
([v27,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v27,v3,v7)],[0,1,2,3,4,5],[(0,14),(0,120),(0,186),(0,217),(0,231),(0,266),(0,307),(0,326),(0,354),(0,355),(0,356),(0,358),(0,359),(1,352),(2,301),(2,351),(2,357),(4,353)]),
([v0,v2,v3,v1,v7,v4,v5,v11],[(v7,v0,v1),(v11,v3,v5)],[0,1,2,3,4,5],[(0,83),(0,214),(0,305),(0,336),(0,348),(0,354),(0,361),(0,363),(0,364),(0,365),(1,257),(1,317),(1,360),(2,13),(2,126),(2,362),(3,257),(3,317),(4,362),(5,83),(5,214),(5,305),(5,336),(5,348),(5,354),(5,361),(5,364),(5,365)]),
([v0,v2,v3,v1,v4,v12,v14],[(v12,v2,v5),(v14,v5,v4)],[0,1,2,3,4,5],[(0,220),(0,235),(0,278),(0,294),(0,317),(0,329),(0,360),(0,366),(0,370),(0,371),(0,372),(0,375),(0,378),(1,29),(1,187),(1,374),(2,269),(2,373),(3,369),(3,379),(4,355),(4,380),(5,367),(5,368),(5,376),(5,377)]),
([v0,v2,v3,v1,v4,v21,v5],[(v7,v0,v1),(v21,v7,v4)],[0,1,2,3,4,5],[(0,85),(0,382),(0,383),(0,384),(0,387),(0,388),(0,389),(0,390),(0,391),(0,392),(1,85),(1,382),(1,383),(1,384),(2,385),(3,385),(4,189),(4,220),(4,305),(4,374),(4,381),(4,386),(5,220),(5,305),(5,374)]),
([v0,v2,v3,v1,v7,v4,v21,v5],[(v7,v0,v1),(v21,v7,v4)],[0,1,2,3,4,5],[(0,236),(0,240),(0,295),(0,299),(0,330),(0,356),(0,396),(0,400),(0,401),(0,402),(0,404),(0,405),(0,406),(0,407),(1,267),(1,395),(2,385),(2,399),(3,221),(3,315),(3,375),(3,397),(3,398),(4,393),(4,394),(4,403),(5,32)]),
([v25,v0,v2,v3,v1,v4,v5],[(v13,v2,v1),(v25,v13,v5)],[0,1,2,3,4,5],[(0,190),(0,222),(0,249),(0,300),(0,306),(0,362),(0,376),(0,385),(0,408),(0,409),(0,410),(0,412),(0,413),(0,415),(1,414),(2,416),(2,417),(3,411)]),
([v25,v0,v2,v3,v1,v13,v4,v5],[(v13,v2,v1),(v25,v13,v5)],[0,1,2,3,4,5],[(0,33),(0,223),(0,237),(0,261),(0,268),(0,301),(0,316),(0,331),(0,357),(0,377),(0,385),(0,399),(0,418),(0,422),(1,420),(2,421),(2,423),(3,419)]),
([v0,v2,v3,v1,v4,v43,v5],[(v13,v2,v1),(v43,v13,v4)],[0,1,2,3,4,5],[(0,85),(0,126),(0,424),(0,428),(0,429),(0,430),(0,433),(0,434),(0,435),(1,176),(1,427),(2,387),(2,432),(3,431),(4,287),(4,317),(4,425),(4,426),(5,289)]),
([v0,v2,v3,v1,v7,v4,v5,v47],[(v7,v0,v1),(v47,v7,v5)],[0,1,2,3,4,5],[(0,242),(0,332),(0,336),(0,358),(0,361),(0,400),(0,404),(0,432),(0,442),(1,270),(1,438),(2,238),(2,422),(2,439),(2,443),(3,321),(4,436),(4,437),(5,30),(5,224),(5,440),(5,441)]),
([v30,v0,v2,v3,v1,v4,v5],[(v7,v0,v1),(v30,v7,v5)],[0,1,2,3,4,5],[(0,188),(0,288),(0,292),(0,304),(0,348),(0,416),(0,432),(0,445),(0,448),(0,449),(0,451),(0,452),(1,253),(1,446),(1,450),(2,444),(3,447)]),
([v30,v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1),(v30,v7,v5)],[0,1,2,3,4,5],[(0,31),(0,225),(0,239),(0,271),(0,293),(0,322),(0,333),(0,354),(0,359),(0,380),(0,401),(0,421),(0,423),(0,432),(0,442),(1,263),(1,455),(2,453),(3,454)]),
([v0,v2,v3,v1,v7,v4,v5,v14],[(v7,v0,v1),(v14,v4,v5)],[0,1,2,3,4,5],[(0,89),(0,132),(0,289),(0,294),(0,305),(0,350),(0,387),(0,402),(0,404),(0,416),(0,421),(0,457),(0,460),(0,461),(0,462),(0,464),(1,258),(1,373),(3,219),(3,312),(3,456),(3,458),(3,459),(3,463),(4,374),(5,28),(5,465),(5,466),(5,467)]),
([v0,v2,v3,v1,v18,v19,v4,v5],[(v18,v3,v1),(v19,v0,v18)],[0,1,2,3,4,5],[(0,171),(0,282),(0,469),(0,472),(0,473),(0,476),(0,478),(0,479),(0,483),(0,484),(0,485),(1,470),(1,471),(2,477),(2,480),(2,482),(3,474),(3,475),(4,113),(4,468),(4,481),(5,309)]),
([v42,v0,v2,v3,v1,v4,v5],[(v22,v2,v4),(v42,v3,v22)],[0,1,2,3,4,5],[(0,113),(0,275),(0,284),(0,310),(0,486),(0,487),(0,489),(0,490),(0,494),(0,495),(0,496),(0,497),(2,173),(2,488),(3,491),(3,492),(4,493)]),
([v42,v0,v2,v3,v1,v4,v22,v5],[(v22,v2,v4),(v42,v3,v22)],[0,1,2,3,4,5],[(0,113),(0,286),(0,308),(0,311),(0,468),(0,470),(0,498),(0,499),(0,502),(0,503),(0,505),(1,506),(2,175),(3,500),(3,504),(4,501)]),
([v0,v2,v3,v1,v18,v4,v22,v5],[(v18,v3,v1),(v22,v2,v4)],[0,1,2,3,4,5],[(0,118),(0,126),(0,482),(0,507),(0,508),(0,510),(1,118),(1,482),(1,508),(1,510),(2,272),(2,287),(2,491),(2,500),(2,509),(3,272),(3,287),(3,491),(3,500),(3,509),(4,496),(5,496)]),
([v0,v2,v3,v1,v18,v4,v59,v5],[(v18,v3,v1),(v59,v18,v4)],[0,1,2,3,4,5],[(0,282),(0,476),(0,482),(0,513),(0,514),(0,519),(0,520),(1,503),(1,512),(1,518),(1,521),(2,431),(2,478),(2,517),(3,313),(3,515),(3,516),(4,505),(5,318),(5,511)]),
([v28,v0,v2,v3,v1,v4,v5],[(v18,v3,v1),(v28,v18,v5)],[0,1,2,3,4,5],[(0,177),(0,276),(0,290),(0,319),(0,431),(0,491),(0,510),(0,522),(0,523),(0,524),(0,526),(0,529),(0,530),(0,531),(1,284),(1,527),(1,528),(2,525)]),
([v28,v0,v2,v3,v1,v18,v4,v5],[(v18,v3,v1),(v28,v18,v5)],[0,1,2,3,4,5],[(0,277),(0,314),(0,320),(0,431),(0,477),(0,479),(0,500),(0,504),(0,506),(0,517),(0,519),(0,532),(0,535),(0,536),(1,286),(1,534),(2,533)]),
([v0,v2,v3,v1,v18,v4,v5,v14],[(v18,v3,v1),(v14,v4,v5)],[0,1,2,3,4,5],[(0,132),(0,278),(0,287),(0,520),(0,530),(0,535),(0,538),(0,539),(0,540),(0,542),(1,497),(2,132),(2,278),(2,287),(3,312),(3,387),(3,537),(3,541),(3,543),(3,544),(3,545),(4,497),(5,312),(5,537)]),
([v0,v2,v3,v1,v4,v10,v21,v5],[(v10,v1,v4),(v21,v0,v10)],[0,1,2,3,4,5],[(0,194),(0,541),(0,547),(0,548),(0,549),(0,553),(0,554),(0,556),(0,557),(0,558),(1,194),(1,547),(1,548),(1,549),(2,550),(2,551),(2,552),(3,550),(3,551),(3,552),(4,370),(4,381),(4,546),(4,555),(5,370)]),
([v40,v0,v2,v3,v1,v4,v5],[(v14,v4,v5),(v40,v3,v14)],[0,1,2,3,4,5],[(0,212),(0,371),(0,381),(0,457),(0,559),(0,560),(0,562),(0,563),(0,565),(1,196),(1,561),(2,371),(2,457),(2,559),(2,560),(2,565),(3,543),(3,564),(4,196),(4,561)]),
([v40,v0,v2,v3,v1,v4,v5,v14],[(v14,v4,v5),(v40,v3,v14)],[0,1,2,3,4,5],[(0,372),(0,381),(0,546),(0,566),(0,567),(0,568),(0,570),(0,571),(1,198),(2,372),(2,566),(2,568),(2,570),(3,545),(3,569),(3,572),(4,198),(5,569)]),
([v0,v2,v3,v1,v4,v10,v43,v5],[(v10,v1,v4),(v43,v2,v10)],[0,1,2,3,4,5],[(0,194),(0,207),(0,463),(0,547),(0,575),(0,576),(0,577),(0,584),(0,585),(0,586),(1,427),(1,574),(2,581),(2,582),(2,583),(3,578),(3,579),(3,580),(4,366),(4,568),(4,573)]),
([v36,v0,v2,v3,v1,v4,v5],[(v10,v4,v1),(v36,v3,v10)],[0,1,2,3,4,5],[(0,199),(0,209),(0,367),(0,427),(0,456),(0,465),(0,537),(0,587),(0,588),(0,591),(0,592),(0,594),(0,595),(2,196),(2,589),(2,590),(4,593)]),
([v36,v0,v2,v3,v1,v4,v10,v5],[(v10,v4,v1),(v36,v3,v10)],[0,1,2,3,4,5],[(0,211),(0,368),(0,369),(0,427),(0,467),(0,548),(0,569),(0,574),(0,576),(0,596),(0,599),(0,600),(0,601),(0,602),(0,603),(2,198),(2,597),(4,598)]),
([v0,v2,v3,v1,v4,v16,v14],[(v16,v5,v1),(v14,v5,v4)],[0,1,2,3,4,5],[(0,201),(0,373),(0,374),(0,552),(0,565),(0,570),(0,580),(0,583),(0,604),(1,201),(1,373),(1,374),(1,552),(1,565),(1,570),(1,580),(1,583),(2,601),(2,605),(3,601),(3,605),(4,200),(4,600),(5,600)]),
([v0,v2,v3,v1,v4,v5,v50],[(v10,v1,v4),(v50,v10,v5)],[0,1,2,3,4,5],[(0,202),(0,387),(0,606),(0,607),(0,608),(0,609),(1,202),(1,607),(1,608),(2,387),(2,606),(2,609),(3,387),(3,606),(3,609),(4,202),(4,607),(4,608)]),
([v0,v2,v3,v1,v4,v10,v5,v50],[(v10,v1,v4),(v50,v10,v5)],[0,1,2,3,4,5],[(0,463),(0,541),(0,553),(0,584),(0,602),(0,609),(0,611),(0,614),(1,463),(1,584),(1,602),(1,611),(2,612),(2,613),(3,612),(3,613),(4,378),(4,571),(4,610),(5,378)]),
([v37,v0,v2,v3,v1,v4,v5],[(v10,v1,v4),(v37,v10,v5)],[0,1,2,3,4,5],[(0,203),(0,213),(0,458),(0,465),(0,543),(0,609),(0,615),(0,616),(0,617),(0,619),(0,620),(1,203),(1,458),(1,465),(1,619),(1,620),(2,618),(3,618)]),
([v37,v0,v2,v3,v1,v4,v10,v5],[(v10,v1,v4),(v37,v10,v5)],[0,1,2,3,4,5],[(0,379),(0,459),(0,467),(0,545),(0,554),(0,572),(0,585),(0,603),(0,605),(0,609),(0,614),(0,621),(1,379),(1,459),(1,467),(1,585),(1,603),(1,605),(2,622),(3,622)])
]

def g6_L9 : Array W6Node := Array.mk [
([v0,v2,v6,v3,v1,v4,v5],[(v6,v0,v2)],[0,1,2,3,4,5],[(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(1,0),(1,1),(1,10),(2,11),(2,12),(2,13),(2,15),(2,16),(3,8),(3,9),(4,0),(4,1),(4,10)]),
([v0,v2,v3,v1,v7,v4,v5],[(v7,v0,v1)],[0,1,2,3,4,5],[(0,6),(0,10),(0,19),(0,22),(0,23),(0,25),(0,26),(0,27),(0,28),(0,30),(0,31),(0,35),(0,36),(0,37),(0,38),(1,20),(1,21),(2,32),(2,33),(2,34),(3,18),(3,24),(3,29),(4,15),(4,23),(5,1)]),
([v0,v2,v3,v1,v18,v4,v5],[(v18,v3,v1)],[0,1,2,3,4,5],[(0,10),(0,14),(0,39),(0,42),(0,43),(0,44),(0,45),(0,46),(1,22),(1,34),(1,40),(1,41),(2,10),(2,39),(2,42),(2,43),(2,44),(2,45),(3,24),(4,22),(4,34),(4,40),(4,41),(5,24)]),
([v0,v2,v3,v1,v4,v10,v5],[(v10,v1,v4)],[0,1,2,3,4,5],[(0,16),(0,30),(0,34),(0,47),(0,50),(0,51),(0,52),(0,54),(0,55),(0,56),(0,57),(1,16),(1,34),(1,50),(1,51),(1,52),(2,53),(3,53),(4,17),(4,29),(4,38),(4,46),(4,48),(4,49),(5,29),(5,38)])
]

def g6_L10 : Array W6Node := Array.mk [
([v0,v2,v3,v1,v4,v5],[],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(5,1)])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_3_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_3 : ∀ i < g6_L3.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : g6_L3.size = 2 := by decide +kernel
  exact checkBlockW6_at g6_chk_3_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_1 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 16 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 i = true := by
  intro i hi
  have hsz : g6_L4.size = 23 := by decide +kernel
  have hi' : i < 23 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW6_at g6_chk_4_0 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_4_1 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_1 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_2 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_3 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_4 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_5 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_6 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_7 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_8 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_9 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_10 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_11 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_12 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_13 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_14 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_15 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_16 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_17 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_18 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_19 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_20 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 320 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 i = true := by
  intro i hi
  have hsz : g6_L5.size = 332 := by decide +kernel
  have hi' : i < 332 := hsz ▸ hi
  by_cases h : i < 176
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 48
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW6_at g6_chk_5_0 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_5_1 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_2 i (by omega) (by omega)
      ·
        by_cases h : i < 80
        ·
          by_cases h : i < 64
          ·
            exact checkBlockW6_at g6_chk_5_3 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_5_4 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_5 i (by omega) (by omega)
    ·
      by_cases h : i < 144
      ·
        by_cases h : i < 128
        ·
          by_cases h : i < 112
          ·
            exact checkBlockW6_at g6_chk_5_6 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_5_7 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_8 i (by omega) (by omega)
      ·
        by_cases h : i < 160
        ·
          exact checkBlockW6_at g6_chk_5_9 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_10 i (by omega) (by omega)
  ·
    by_cases h : i < 256
    ·
      by_cases h : i < 224
      ·
        by_cases h : i < 208
        ·
          by_cases h : i < 192
          ·
            exact checkBlockW6_at g6_chk_5_11 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_5_12 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_13 i (by omega) (by omega)
      ·
        by_cases h : i < 240
        ·
          exact checkBlockW6_at g6_chk_5_14 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_15 i (by omega) (by omega)
    ·
      by_cases h : i < 304
      ·
        by_cases h : i < 288
        ·
          by_cases h : i < 272
          ·
            exact checkBlockW6_at g6_chk_5_16 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_5_17 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_18 i (by omega) (by omega)
      ·
        by_cases h : i < 320
        ·
          exact checkBlockW6_at g6_chk_5_19 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_20 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_1 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_2 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_3 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_4 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_5 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_6 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_7 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_8 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_9 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_10 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_11 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_12 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_13 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_14 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_15 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_16 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_17 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_18 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_19 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_20 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_21 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_22 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_23 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_24 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_25 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_26 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_27 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_28 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_29 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_30 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_31 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_32 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 512 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_33 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 528 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_34 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 544 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_35 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 560 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_36 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 576 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_37 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 592 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_38 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 608 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_39 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 624 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_40 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 640 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_41 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 656 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_42 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 672 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_43 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 688 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_44 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 704 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_45 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 720 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_46 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 736 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_47 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 752 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_48 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 768 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_49 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 784 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_50 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 800 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_51 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 816 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_52 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 832 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_53 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 848 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_54 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 864 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_55 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 880 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_56 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 896 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_57 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 912 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_58 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 928 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_59 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 944 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_60 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 960 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_61 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 976 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_62 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 992 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_63 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1008 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_64 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1024 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_65 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1040 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_66 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1056 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_67 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1072 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_68 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1088 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_69 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1104 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_70 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1120 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_71 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1136 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_72 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1152 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_73 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 1168 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : g6_L6.size = 1174 := by decide +kernel
  have hi' : i < 1174 := hsz ▸ hi
  by_cases h : i < 592
  ·
    by_cases h : i < 304
    ·
      by_cases h : i < 160
      ·
        by_cases h : i < 80
        ·
          by_cases h : i < 48
          ·
            by_cases h : i < 32
            ·
              by_cases h : i < 16
              ·
                exact checkBlockW6_at g6_chk_6_0 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_1 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_2 i (by omega) (by omega)
          ·
            by_cases h : i < 64
            ·
              exact checkBlockW6_at g6_chk_6_3 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_4 i (by omega) (by omega)
        ·
          by_cases h : i < 128
          ·
            by_cases h : i < 112
            ·
              by_cases h : i < 96
              ·
                exact checkBlockW6_at g6_chk_6_5 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_6 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_7 i (by omega) (by omega)
          ·
            by_cases h : i < 144
            ·
              exact checkBlockW6_at g6_chk_6_8 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_9 i (by omega) (by omega)
      ·
        by_cases h : i < 240
        ·
          by_cases h : i < 208
          ·
            by_cases h : i < 192
            ·
              by_cases h : i < 176
              ·
                exact checkBlockW6_at g6_chk_6_10 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_11 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_12 i (by omega) (by omega)
          ·
            by_cases h : i < 224
            ·
              exact checkBlockW6_at g6_chk_6_13 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_14 i (by omega) (by omega)
        ·
          by_cases h : i < 272
          ·
            by_cases h : i < 256
            ·
              exact checkBlockW6_at g6_chk_6_15 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_16 i (by omega) (by omega)
          ·
            by_cases h : i < 288
            ·
              exact checkBlockW6_at g6_chk_6_17 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_18 i (by omega) (by omega)
    ·
      by_cases h : i < 448
      ·
        by_cases h : i < 384
        ·
          by_cases h : i < 352
          ·
            by_cases h : i < 336
            ·
              by_cases h : i < 320
              ·
                exact checkBlockW6_at g6_chk_6_19 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_20 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_21 i (by omega) (by omega)
          ·
            by_cases h : i < 368
            ·
              exact checkBlockW6_at g6_chk_6_22 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_23 i (by omega) (by omega)
        ·
          by_cases h : i < 416
          ·
            by_cases h : i < 400
            ·
              exact checkBlockW6_at g6_chk_6_24 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_25 i (by omega) (by omega)
          ·
            by_cases h : i < 432
            ·
              exact checkBlockW6_at g6_chk_6_26 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_27 i (by omega) (by omega)
      ·
        by_cases h : i < 528
        ·
          by_cases h : i < 496
          ·
            by_cases h : i < 480
            ·
              by_cases h : i < 464
              ·
                exact checkBlockW6_at g6_chk_6_28 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_29 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_30 i (by omega) (by omega)
          ·
            by_cases h : i < 512
            ·
              exact checkBlockW6_at g6_chk_6_31 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_32 i (by omega) (by omega)
        ·
          by_cases h : i < 560
          ·
            by_cases h : i < 544
            ·
              exact checkBlockW6_at g6_chk_6_33 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_34 i (by omega) (by omega)
          ·
            by_cases h : i < 576
            ·
              exact checkBlockW6_at g6_chk_6_35 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_36 i (by omega) (by omega)
  ·
    by_cases h : i < 896
    ·
      by_cases h : i < 752
      ·
        by_cases h : i < 672
        ·
          by_cases h : i < 640
          ·
            by_cases h : i < 624
            ·
              by_cases h : i < 608
              ·
                exact checkBlockW6_at g6_chk_6_37 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_38 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_39 i (by omega) (by omega)
          ·
            by_cases h : i < 656
            ·
              exact checkBlockW6_at g6_chk_6_40 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_41 i (by omega) (by omega)
        ·
          by_cases h : i < 720
          ·
            by_cases h : i < 704
            ·
              by_cases h : i < 688
              ·
                exact checkBlockW6_at g6_chk_6_42 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_43 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_44 i (by omega) (by omega)
          ·
            by_cases h : i < 736
            ·
              exact checkBlockW6_at g6_chk_6_45 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_46 i (by omega) (by omega)
      ·
        by_cases h : i < 832
        ·
          by_cases h : i < 800
          ·
            by_cases h : i < 784
            ·
              by_cases h : i < 768
              ·
                exact checkBlockW6_at g6_chk_6_47 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_48 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_49 i (by omega) (by omega)
          ·
            by_cases h : i < 816
            ·
              exact checkBlockW6_at g6_chk_6_50 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_51 i (by omega) (by omega)
        ·
          by_cases h : i < 864
          ·
            by_cases h : i < 848
            ·
              exact checkBlockW6_at g6_chk_6_52 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_53 i (by omega) (by omega)
          ·
            by_cases h : i < 880
            ·
              exact checkBlockW6_at g6_chk_6_54 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_55 i (by omega) (by omega)
    ·
      by_cases h : i < 1040
      ·
        by_cases h : i < 976
        ·
          by_cases h : i < 944
          ·
            by_cases h : i < 928
            ·
              by_cases h : i < 912
              ·
                exact checkBlockW6_at g6_chk_6_56 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_57 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_58 i (by omega) (by omega)
          ·
            by_cases h : i < 960
            ·
              exact checkBlockW6_at g6_chk_6_59 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_60 i (by omega) (by omega)
        ·
          by_cases h : i < 1008
          ·
            by_cases h : i < 992
            ·
              exact checkBlockW6_at g6_chk_6_61 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_62 i (by omega) (by omega)
          ·
            by_cases h : i < 1024
            ·
              exact checkBlockW6_at g6_chk_6_63 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_64 i (by omega) (by omega)
      ·
        by_cases h : i < 1120
        ·
          by_cases h : i < 1088
          ·
            by_cases h : i < 1072
            ·
              by_cases h : i < 1056
              ·
                exact checkBlockW6_at g6_chk_6_65 i (by omega) (by omega)
              ·
                exact checkBlockW6_at g6_chk_6_66 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_67 i (by omega) (by omega)
          ·
            by_cases h : i < 1104
            ·
              exact checkBlockW6_at g6_chk_6_68 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_69 i (by omega) (by omega)
        ·
          by_cases h : i < 1152
          ·
            by_cases h : i < 1136
            ·
              exact checkBlockW6_at g6_chk_6_70 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_71 i (by omega) (by omega)
          ·
            by_cases h : i < 1168
            ·
              exact checkBlockW6_at g6_chk_6_72 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_73 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_1 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_2 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_3 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_4 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_5 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_6 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_7 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_8 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_9 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_10 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_11 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_12 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_13 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_14 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_15 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_16 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_17 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_18 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_19 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_20 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_21 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_22 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_23 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_24 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_25 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_26 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_27 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_28 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_29 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_30 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_31 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_32 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 512 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_33 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 528 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_34 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 544 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_35 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 560 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_36 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 576 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_37 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 592 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_38 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 608 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 i = true := by
  intro i hi
  have hsz : g6_L7.size = 623 := by decide +kernel
  have hi' : i < 623 := hsz ▸ hi
  by_cases h : i < 320
  ·
    by_cases h : i < 160
    ·
      by_cases h : i < 80
      ·
        by_cases h : i < 48
        ·
          by_cases h : i < 32
          ·
            by_cases h : i < 16
            ·
              exact checkBlockW6_at g6_chk_7_0 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_1 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_2 i (by omega) (by omega)
        ·
          by_cases h : i < 64
          ·
            exact checkBlockW6_at g6_chk_7_3 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_4 i (by omega) (by omega)
      ·
        by_cases h : i < 128
        ·
          by_cases h : i < 112
          ·
            by_cases h : i < 96
            ·
              exact checkBlockW6_at g6_chk_7_5 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_6 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_7 i (by omega) (by omega)
        ·
          by_cases h : i < 144
          ·
            exact checkBlockW6_at g6_chk_7_8 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_9 i (by omega) (by omega)
    ·
      by_cases h : i < 240
      ·
        by_cases h : i < 208
        ·
          by_cases h : i < 192
          ·
            by_cases h : i < 176
            ·
              exact checkBlockW6_at g6_chk_7_10 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_11 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_12 i (by omega) (by omega)
        ·
          by_cases h : i < 224
          ·
            exact checkBlockW6_at g6_chk_7_13 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_14 i (by omega) (by omega)
      ·
        by_cases h : i < 288
        ·
          by_cases h : i < 272
          ·
            by_cases h : i < 256
            ·
              exact checkBlockW6_at g6_chk_7_15 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_16 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_17 i (by omega) (by omega)
        ·
          by_cases h : i < 304
          ·
            exact checkBlockW6_at g6_chk_7_18 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_19 i (by omega) (by omega)
  ·
    by_cases h : i < 480
    ·
      by_cases h : i < 400
      ·
        by_cases h : i < 368
        ·
          by_cases h : i < 352
          ·
            by_cases h : i < 336
            ·
              exact checkBlockW6_at g6_chk_7_20 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_21 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_22 i (by omega) (by omega)
        ·
          by_cases h : i < 384
          ·
            exact checkBlockW6_at g6_chk_7_23 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_24 i (by omega) (by omega)
      ·
        by_cases h : i < 448
        ·
          by_cases h : i < 432
          ·
            by_cases h : i < 416
            ·
              exact checkBlockW6_at g6_chk_7_25 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_26 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_27 i (by omega) (by omega)
        ·
          by_cases h : i < 464
          ·
            exact checkBlockW6_at g6_chk_7_28 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_29 i (by omega) (by omega)
    ·
      by_cases h : i < 560
      ·
        by_cases h : i < 528
        ·
          by_cases h : i < 512
          ·
            by_cases h : i < 496
            ·
              exact checkBlockW6_at g6_chk_7_30 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_7_31 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_32 i (by omega) (by omega)
        ·
          by_cases h : i < 544
          ·
            exact checkBlockW6_at g6_chk_7_33 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_34 i (by omega) (by omega)
      ·
        by_cases h : i < 592
        ·
          by_cases h : i < 576
          ·
            exact checkBlockW6_at g6_chk_7_35 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_36 i (by omega) (by omega)
        ·
          by_cases h : i < 608
          ·
            exact checkBlockW6_at g6_chk_7_37 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_38 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_1 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_2 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_3 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 48 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 i = true := by
  intro i hi
  have hsz : g6_L8.size = 58 := by decide +kernel
  have hi' : i < 58 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW6_at g6_chk_8_0 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_8_1 i (by omega) (by omega)
  ·
    by_cases h : i < 48
    ·
      exact checkBlockW6_at g6_chk_8_2 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_8_3 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_9 : ∀ i < g6_L9.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 i = true := by
  intro i hi
  have hsz : g6_L9.size = 4 := by decide +kernel
  exact checkBlockW6_at g6_chk_9_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_10_0 : checkBlockW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_10 : ∀ i < g6_L10.size, checkNodeW6 goal6 6 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 i = true := by
  intro i hi
  have hsz : g6_L10.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_10_0 i (Nat.zero_le _) (by omega)

theorem g6_L3_sound : ∀ i < g6_L3.size, ¬ live (basicOps 64) goal6 3 (g6_L3[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound (fun j hj => by simp at hj) g6_chk_3

theorem g6_L4_sound : ∀ i < g6_L4.size, ¬ live (basicOps 64) goal6 4 (g6_L4[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L3_sound g6_chk_4

theorem g6_L5_sound : ∀ i < g6_L5.size, ¬ live (basicOps 64) goal6 5 (g6_L5[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L4_sound g6_chk_5

theorem g6_L6_sound : ∀ i < g6_L6.size, ¬ live (basicOps 64) goal6 6 (g6_L6[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L5_sound g6_chk_6

theorem g6_L7_sound : ∀ i < g6_L7.size, ¬ live (basicOps 64) goal6 7 (g6_L7[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L6_sound g6_chk_7

theorem g6_L8_sound : ∀ i < g6_L8.size, ¬ live (basicOps 64) goal6 8 (g6_L8[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L7_sound g6_chk_8

theorem g6_L9_sound : ∀ i < g6_L9.size, ¬ live (basicOps 64) goal6 9 (g6_L9[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L8_sound g6_chk_9

theorem g6_L10_sound : ∀ i < g6_L10.size, ¬ live (basicOps 64) goal6 10 (g6_L10[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L9_sound g6_chk_10

set_option maxRecDepth 100000 in

theorem g6_sublists : rows6.sublists.filter (fun ws => cover 64 jumps6 goal6 ws) = [rows6] := by decide +kernel

theorem g6_top_match : sameSet (rows6.map (actB 64 (g6_pow[0]?.getD []))) (g6_L10[0]?.getD ([], [], [], [])).1 = true := by decide +kernel

theorem g6_no_build : ¬ build (basicOps 64) goal6 10 rows6.toFinset :=

  no_build_of_top g6_G_valid (by decide) g6_sublists g6_top_match (g6_L10_sound 0 (by decide))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W6 := BitVec 64
abbrev basicOps6 (a b : W6) : Finset W6 := (ops 64 a b).toFinset

def holds (av : Finset W6) (z : W6) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W6} {z a : W6} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W6} {z : W6} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W6) (z : W6) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps6 a b, holds (insert w av) z

theorem reachable_not {av : Finset W6} {z : W6} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset W6} {x y : W6} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W6) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W6) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y); rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W6) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64); rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W6) (hw : w ∈ basicOps6 a b) (z : W6) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps6, ops] : a &&& b ∈ basicOps6 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps6, ops] : a &&& ~~~b ∈ basicOps6 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps6, ops] : b &&& ~~~a ∈ basicOps6 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps6, ops] : a ||| b ∈ basicOps6 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W6} {x y : W6} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit6 (k : Fin 64) (z : W6) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit6 (w : List W6) (i : ℕ) (k : Fin 64) :
    (w.map (bit6 k)).getD i false = bit6 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit6]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W6) (g : Gate) : W6 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W6) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit6 k)) g = (w ++ [action w g]).map (bit6 k) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W6)[k.val] = false := by simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit6, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit6, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W6} {w : List W6} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

theorem gate_reach (w : List W6) (av : Finset W6) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W6, x ||| (0 : W6) = x from fun x => BitVec.or_zero,
    show ∀ x : W6, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W6) (av : Finset W6) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit6 k))).getD out false = bit6 k goal6) :
    ∃ t, (t = goal6 ∨ t = ~~~goal6) ∧ build basicOps6 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal6 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil, read_bit6, bit6] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal6 ≠ 0) zero)
    · exact False.elim ((by decide : goal6 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W6 => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit6 k))).getD out false = bit6 k goal6 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W6) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def F (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4278124266 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem sample6_ok : ∀ k : Fin 64, F (fun i => (rows6.getD i.val 0)[k.val]) = goal6[k.val] := by decide +kernel

def idxs64 : List ℕ := List.range 64
theorem idxs64_spec : idxs64.length = 64 ∧ ∀ idx ∈ idxs64, idx < 64 := by decide
theorem projS64_goal6 : projS 64 idxs64 goal6 = goal6 := by decide +kernel
theorem projS64_rows6_sub : rows6.all (fun w => projS 64 idxs64 w == 0 || rows6.contains (projS 64 idxs64 w)) = true := by decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows6, holds rows6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (rows6.map (bit6 k))).getD o false = bit6 k goal6 := by
    let x (i : Fin 6) : Bool := bit6 k (rows6.getD i.val 0)
    have same : List.ofFn x = rows6.map (bit6 k) := by
      apply List.ext_getElem
      · simp [rows6]
      · intro i hi hj
        have hlt : i < rows6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows6.map (bit6 k)) = bit6 k goal6
    rw [← same, he]
    exact sample6_ok k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows6 rows6.toFinset init evaluate
  obtain ⟨s, hs, hl⟩ := compress (build_mono_k low run)
  have hpt : projS 64 idxs64 t = goal6 := by
    rcases ht with rfl | rfl
    · exact projS64_goal6
    · rw [projS_not 64 (by decide) idxs64 idxs64_spec.1 idxs64_spec.2]; exact projS64_goal6
  have hb64 := live_restrict (by decide : 0 < 64) idxs64 idxs64_spec.1 idxs64_spec.2
    (fun a b z hz => List.mem_toFinset.mp hz) hpt (by decide : goal6 ≠ 0) hl
  have hsub64 : nonZeroImg (projS 64 idxs64) s ⊆ rows6.toFinset := by
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu
    obtain ⟨hne, v, hv, rfl⟩ := hu
    have h1 := List.all_eq_true.mp projS64_rows6_sub v (List.mem_toFinset.mp (hs hv))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact g6_no_build (build_mono_k (Nat.sub_le _ _) (build_mono_av hsub64 hb64))

def wg : List Gate := [
  ⟨.or, [2, 0]⟩,
  ⟨.and, [6, 1]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [5, 3]⟩,
  ⟨.or, [3, 0]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.and, [10, 8]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [4, 11]⟩,
  ⟨.or, [14, 12]⟩,
  ⟨.and, [13, 15]⟩,
  ⟨.or, [16, 7]⟩
]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_39529_aux

open PEqualNP.Outside.L_meta_39529_aux in
theorem PEqualNP.Outside.L_meta_39529 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276943080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsz, hev⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, legal g := fun g hg => by
      have hf := hfan g hg
      refine ⟨?_, hf.2⟩
      simpa using hf.1
    have hb := bound C.gates C.output hleg hev
    have hclen : C.gates.length ≤ s := hsz
    have hl : (⟨wg, 17⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 12 := rfl
    exact ⟨⟨wg, 17⟩, wfits, by omega, weval⟩
  · refine ⟨C, fun g hg => ⟨?_, (hfan g hg).2⟩, hsz, hev⟩
    have hf := (hfan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
    rcases hf with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
