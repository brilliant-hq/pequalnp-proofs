import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46362_aux
namespace CoreSigned

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old

end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
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

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.and,[6,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[6,2]⟩, ⟨.and,[9,8]⟩,
    ⟨.or,[9,8]⟩, ⟨.and,[11,4]⟩, ⟨.or,[12,0]⟩, ⟨.or,[1,5]⟩, ⟨.and,[14,13]⟩,
    ⟨.or,[15,10]⟩],16⟩

theorem size : witness.size = 11 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4294901482 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfffefeeafeecfee8
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4294901482 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
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

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfffefeeafeecfee8 : W) 9 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 9 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfffefeeafeecfee8 : BitVec 64) 9 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901482 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901482 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix

namespace SignedProjection
def ew0 : Word := 0x1010000010100000
def ew1 : Word := 0x1100000011000000
def ew2 : Word := 0x1111000000000000
def ew3 : Word := 0x1010101000000000
def ew4 : Word := 0x1100110000000000
def ew5 : Word := 0x404040400000000
def ew6 : Word := 0x500050000000000
def ew7 : Word := 0x505000000000000
def ew8 : Word := 0x44004400000000
def ew9 : Word := 0x50005000000000
def ew10 : Word := 0x55000000000000
def ew11 : Word := 0x444400000000
def ew12 : Word := 0x505000000000
def ew13 : Word := 0x550000000000
def ew14 : Word := 0x202000002020000
def ew15 : Word := 0x300000003000000
def ew16 : Word := 0x303000000000000
def ew17 : Word := 0xa0a
def ew18 : Word := 0xc0c
def ew19 : Word := 0xf00
def ew20 : Word := 0x4444444400000000
def ew21 : Word := 0x5050505000000000
def ew22 : Word := 0x5500550000000000
def ew23 : Word := 0x5555000000000000
def ew24 : Word := 0xa0a000000000a0a
def ew25 : Word := 0xc0c000000000c0c
def ew26 : Word := 0xf00000000000f00
def ew27 : Word := 0xf0f000000000000
def ew28 : Word := 0x2222000022220000
def ew29 : Word := 0x3030000030300000
def ew30 : Word := 0x3300000033000000
def ew31 : Word := 0x3333000000000000
def ew32 : Word := 0xa000a000a000a
def ew33 : Word := 0xc000c000c000c
def ew34 : Word := 0xf0000000f0000
def ew35 : Word := 0xf000f00000000
def ew36 : Word := 0xa0a0a0a0a0a0a0a
def ew37 : Word := 0xc0c0c0c0c0c0c0c
def ew38 : Word := 0xf000f000f000f00
def ew39 : Word := 0xf0f00000f0f0000
def ew40 : Word := 0xf0f0f0f00000000
def ew41 : Word := 0xaaaaaaaaaaaaaaaa
def ew42 : Word := 0xcccccccccccccccc
def ew43 : Word := 0xf0f0f0f0f0f0f0f0
def ew44 : Word := 0xff00ff00ff00ff00
def ew45 : Word := 0xffff0000ffff0000
def ew46 : Word := 0xffffffff00000000
def ew47 : Word := 0x5454545400000000
def ew48 : Word := 0x5544554400000000
def ew49 : Word := 0x5555444400000000
def ew50 : Word := 0x5550555000000000
def ew51 : Word := 0x5555505000000000
def ew52 : Word := 0x5555550000000000
def ew53 : Word := 0x5554555400000000
def ew54 : Word := 0x54005400000000
def ew55 : Word := 0x5555545400000000
def ew56 : Word := 0x545400000000
def ew57 : Word := 0x504050400000000
def ew58 : Word := 0x5555554400000000
def ew59 : Word := 0x554400000000
def ew60 : Word := 0x505040400000000
def ew61 : Word := 0x55004400000000
def ew62 : Word := 0x1110111000000000
def ew63 : Word := 0x5555555000000000
def ew64 : Word := 0x555000000000
def ew65 : Word := 0x1111101000000000
def ew66 : Word := 0x55005000000000
def ew67 : Word := 0x1111110000000000
def ew68 : Word := 0x505050000000000
def ew69 : Word := 0x555400000000
def ew70 : Word := 0x55005400000000
def ew71 : Word := 0x505050400000000
def ew72 : Word := 0x1111111000000000
def ew73 : Word := 0xe0e0e0e0e0e0e0e
def ew74 : Word := 0xf0a0f0a0f0a0f0a
def ew75 : Word := 0x500050005000500
def ew76 : Word := 0xf0f0a0a0f0f0a0a
def ew77 : Word := 0x505000005050000
def ew78 : Word := 0xf0c0f0c0f0c0f0c
def ew79 : Word := 0x300030003000300
def ew80 : Word := 0xf0f0f0f0c0c0c0c
def ew81 : Word := 0x303030300000000
def ew82 : Word := 0xf0e0f0e0f0e0f0e
def ew83 : Word := 0xe000e000e000e
def ew84 : Word := 0x302030203020302
def ew85 : Word := 0xf0a0f0a00000000
def ew86 : Word := 0xd0c0d0c0d0c0d0c
def ew87 : Word := 0x504050405040504
def ew88 : Word := 0xf0c00000f0c0000
def ew89 : Word := 0xb0a0b0a0b0a0b0a
def ew90 : Word := 0xc080c080f0a0f0a
def ew91 : Word := 0xa080f0c0a080f0c
def labelsBlock0 : Array Nat := #[
  0x3860,
  0x34c0,
  0x1c50,
  0x1,
  0x38c0,
  0x38a0,
  0x32c0,
  0x5,
  0x2104,
  0x1208,
  0x308,
  0xb1,
  0x904,
  0x304,
  0xb5,
  0x2144
]
def labelsBlock1 : Array Nat := #[
  0x1944,
  0x2688,
  0x2388,
  0x1240,
  0x12d,
  0x1c60,
  0x3450,
  0x1006,
  0x2690,
  0x9,
  0x100a,
  0x2aa0,
  0x2a88,
  0xd,
  0x100e,
  0x3288
]
def labelsBlock2 : Array Nat := #[
  0x11,
  0x1012,
  0x2ca0,
  0x2c90,
  0x15,
  0x3490,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29,
  0x2d,
  0x31,
  0x35,
  0x39,
  0x3d
]
def labelsBlock3 : Array Nat := #[
  0x41,
  0x45,
  0x49,
  0x4d,
  0x51,
  0x55,
  0x59,
  0x5d,
  0x61,
  0x65,
  0x69,
  0x6d,
  0x71,
  0x75,
  0x79,
  0x7d
]
def labelsBlock4 : Array Nat := #[
  0x81,
  0x85,
  0x89,
  0x8d,
  0x91,
  0x95,
  0x99,
  0x9d,
  0xa1,
  0xa5,
  0xa9,
  0xad,
  0x300,
  0x3084,
  0x2100,
  0x1200
]
def labelsBlock5 : Array Nat := #[
  0x3048,
  0x920,
  0xa20,
  0xb9,
  0x1016,
  0xbd,
  0xa08,
  0xc1,
  0xc5,
  0x1960,
  0xc9,
  0x101a,
  0x2180,
  0xcd,
  0xd1,
  0x110c
]
def labelsBlock6 : Array Nat := #[
  0xd5,
  0xd9,
  0x1022,
  0x1244,
  0xdd,
  0xe1,
  0x1344,
  0x102a,
  0xe5,
  0xe9,
  0x2884,
  0x1824,
  0x29a0,
  0xed,
  0xf1,
  0xf5
]
def labelsBlock7 : Array Nat := #[
  0xf9,
  0xfd,
  0x101,
  0x900,
  0x31c0,
  0x105,
  0x2828,
  0x109,
  0x1124,
  0x530022,
  0x730022,
  0x10d,
  0x111,
  0x2228,
  0x115,
  0x1848
]
def labelsBlock8 : Array Nat := #[
  0x1a60,
  0x119,
  0x11d,
  0xa00,
  0x531022,
  0x731022,
  0x121,
  0x1304,
  0x2308,
  0x1a20,
  0x2a20,
  0x2a08,
  0x1904,
  0x2920,
  0x125,
  0xb20
]
def labelsBlock9 : Array Nat := #[
  0x129,
  0x1320,
  0x2320,
  0x2048,
  0x510,
  0x101e,
  0x504,
  0x1414,
  0x1550,
  0x1026,
  0x608,
  0x610,
  0x2418,
  0xc10,
  0xc20,
  0x102e
]
def labelsBlock10 : Array Nat := #[
  0x1544,
  0x2218
]
def labelsGet (i : Nat) : Nat :=
  if i < 80 then
    if i < 32 then
      if i < 16 then
        labelsBlock0.getD (i-0) 3
      else
        labelsBlock1.getD (i-16) 3
    else
      if i < 48 then
        labelsBlock2.getD (i-32) 3
      else
        if i < 64 then
          labelsBlock3.getD (i-48) 3
        else
          labelsBlock4.getD (i-64) 3
  else
    if i < 128 then
      if i < 96 then
        labelsBlock5.getD (i-80) 3
      else
        if i < 112 then
          labelsBlock6.getD (i-96) 3
        else
          labelsBlock7.getD (i-112) 3
    else
      if i < 144 then
        labelsBlock8.getD (i-128) 3
      else
        if i < 160 then
          labelsBlock9.getD (i-144) 3
        else
          labelsBlock10.getD (i-160) 3
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x1111000011110000,⟨16,by decide⟩,0x1110000010000000,[ew0,ew1,ew2],3,lh 2 [0,1,2,3] [0xd900]⟩,
  ⟨0x1111111100000000,⟨32,by decide⟩,0x1110100000000000,[ew3,ew4,ew2],3,fun _ => 3⟩,
  ⟨0x505050500000000,⟨32,by decide⟩,0x504040000000000,[ew5,ew6,ew7],3,fun _ => 3⟩,
  ⟨0x55005500000000,⟨32,by decide⟩,0x54004000000000,[ew8,ew9,ew10],3,fun _ => 3⟩,
  ⟨0x555500000000,⟨32,by decide⟩,0x544000000000,[ew11,ew12,ew13],3,fun _ => 3⟩,
  ⟨0x303000003030000,⟨16,by decide⟩,0x302000002000000,[ew14,ew15,ew16],3,fun _ => 3⟩,
  ⟨0xf0f,⟨0,by decide⟩,0xe08,[ew17,ew18,ew19],3,fun _ => 3⟩,
  ⟨0x5555555500000000,⟨32,by decide⟩,0x5554544000000000,[ew20,ew21,ew22,ew23],6,lh 3 [4,5,1,6,7] [0x8d2000249000]⟩,
  ⟨0xf0f000000000f0f,⟨0,by decide⟩,0xf0e000000000e08,[ew24,ew25,ew26,ew27],6,fun _ => 3⟩,
  ⟨0x3333000033330000,⟨16,by decide⟩,0x3332000032200000,[ew28,ew29,ew30,ew31],6,fun _ => 3⟩,
  ⟨0xf000f000f000f,⟨0,by decide⟩,0xe000a000c0008,[ew32,ew33,ew34,ew35],3,lh 3 [8,9,10,6,11] [0x89a249000000]⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xf0e0e0a0e0c0e08,[ew36,ew37,ew38,ew39,ew40],7,lh 3 [9,10,8,12,13,14] [0x451451000000,0x14c2cb200]⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfffefeeafeecfee8,[ew41,ew42,ew43,ew44,ew45,ew46],9,lh 3 [16,15,17,18,19,8,9,20] [0x249249249249,0x240000015c692400,0x38d24800000338d2,0x7]⟩
]
def viewsGet (i : Nat) : Option View :=
  viewsBlock0[(i-0)]?
def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew0,ew1,ew2],lh 3 [1,4,0,22,21,2] [0x483112144265808,0x1522c946b71b]⟩,
  ⟨7,6,[ew20,ew21,ew22,ew23],lh 5 [4,5,1,6,23,27,34,26,35,30,37,24,33,17,28,31,25,29,32,36,38,39] [0x22c4282dab20c42,0x895c520c0038da3,0x2142148dc321400,0x615e520c2190de3,0x398009990638800,0xa09423982148902,0x4a1486194638821,0x6202148140a8020]⟩,
  ⟨7,5,[ew20,ew21,ew47,ew22,ew23],lh 5 [4,5,23,35,37,24,17,26,28,31,6,1,30,33,40,41,42,43,44,45,46,47] [0x28947318a228842,0x1000e420a001c4a,0x1042f4a4a109508,0x3000212cc259525,0x3042618ce004063,0x60006210e10c484,0x6842c18e6004863,0x1906d212a10d084,0x30840400020]⟩,
  ⟨7,5,[ew20,ew21,ew22,ew48,ew23],lh 5 [5,1,23,34,37,27,28,30,17,31,6,26,4,33,40,48,49,44,50,51,52,53] [0x2a0a2085c841421,0x28947318a228842,0x1000f4a4a001c4a,0x1986380c2609525,0x1ac6388c2b084e1,0x80012046000641,0x31082130c260c83,0x69086000e424c00,0xd002a425000]⟩,
  ⟨7,5,[ew20,ew21,ew22,ew23,ew49],lh 5 [4,1,23,34,6,35,31,33,17,28,26,30,5,41,48,27,54,46,55,56,52,57] [0x22082085a841021,0x22482001c949000,0x208873188220842,0x1800328c2001c4f,0x982180466184a1,0xa8218846a18ce3,0x1800980a628e43,0x2c00a00ab294e5,0x2130c2616a5]⟩,
  ⟨7,5,[ew20,ew21,ew22,ew50,ew23],lh 5 [5,6,34,35,27,26,31,37,30,23,24,1,4,33,42,49,44,58,59,60,61,62] [0x942a1094e50442,0xa02418c8f20463,0xc4244909020521,0x218810002609000,0x1256818c45114a5,0x2801239c40020ab,0x19c652b069608e2,0x698c3001073cc00,0xd002a635000]⟩,
  ⟨7,5,[ew20,ew21,ew22,ew23,ew51],lh 5 [4,6,1,27,26,37,35,28,33,23,24,30,5,43,54,46,63,59,34,64,61,65] [0x902a1094d50442,0x9c230006718400,0x1a0612842e08ca5,0x1c0614842f08d23,0x118440022630800,0x124482944411084,0x1400980c532092,0x2c00a00eb39906,0x4230a961ea7]⟩,
  ⟨7,5,[ew20,ew21,ew22,ew23,ew52],lh 5 [1,6,4,5,30,24,17,27,34,33,23,26,51,56,52,66,60,64,61,67,35,37] [0x9825000a628400,0x9027108ec38442,0x3a4e118c2d09c63,0x2bca15042e09545,0x10081091040042,0x4250018c1102063,0x34cc05801201966,0x1284918c4411084,0x42546a1a494]⟩,
  ⟨7,4,[ew21,ew47,ew22,ew48,ew23],lh 4 [5,37,28,27,1,17,26,24,6,4,68,30] [0x3b1010757652a244,0x101991010883623,0x101]⟩,
  ⟨7,4,[ew21,ew47,ew22,ew23,ew49],lh 4 [4,35,6,17,1,31,26,24,5,69,33,27] [0x1073763593101044,0x11001b226522a10,0x8810]⟩,
  ⟨7,4,[ew20,ew47,ew22,ew50,ew23],lh 4 [5,34,35,24,23,17,31,1,37,4,6,68,30] [0x1c3060533432b2a1,0x802991080771421,0x605]⟩,
  ⟨7,4,[ew20,ew47,ew22,ew23,ew51],lh 4 [4,1,28,37,24,35,23,5,6,69,17,33,34] [0x50a4464393202081,0x25005c116311b10,0x7720]⟩,
  ⟨7,4,[ew20,ew21,ew22,ew53,ew23],lh 4 [5,34,35,27,28,6,1,37,4,24,31,33,70] [0x1430a05542323191,0xb07028810706621,0xc]⟩,
  ⟨7,4,[ew54,ew20,ew21,ew22,ew23],lh 4 [4,5,34,27,37,24,6,17,1,35,31] [0x5241419088726653,0x41702031a1503032,0x100421]⟩,
  ⟨7,4,[ew20,ew21,ew22,ew23,ew55],lh 4 [4,1,6,35,24,37,5,28,27,17,34,30,71] [0x3082422520702141,0xc00b3003a1511910,0x66]⟩,
  ⟨7,4,[ew56,ew20,ew21,ew22,ew23],lh 4 [4,1,5,6,35,24,17,27,34,37,28] [0x5192404081617353,0x121040523230a031,0x200462]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨7,4,[ew21,ew22,ew48,ew23,ew49],lh 4 [1,34,6,28,27,4,31,30,5,72,33] [0x1001100101100110,0x27622a4347369355,0x8842]⟩,
  ⟨7,4,[ew20,ew21,ew48,ew50,ew23],lh 4 [5,34,27,35,23,28,31,1,37,4,68,6,26] [0x1c20605224b321a1,0x803993410807731,0x605]⟩,
  ⟨7,4,[ew57,ew20,ew21,ew22,ew23],lh 4 [5,1,35,27,37,28,24,6,4,34,31] [0x6104048852917736,0x10152130a0523231,0x40240]⟩,
  ⟨7,4,[ew20,ew21,ew48,ew23,ew52],lh 4 [4,1,5,27,17,23,28,34,6,72,33,35,37] [0x7063353292803141,0x5200a4116721210,0xc2b0]⟩,
  ⟨7,4,[ew20,ew21,ew22,ew23,ew58],lh 4 [4,1,5,6,27,34,17,24,26,73,28,35,37] [0x5073423230403161,0xb0200a9118521210,0xc2]⟩,
  ⟨7,4,[ew59,ew20,ew21,ew22,ew23],lh 4 [4,1,6,34,27,28,5,37,35,17] [0x9166805031314242,0x1310304227204021,0x500731]⟩,
  ⟨7,4,[ew20,ew21,ew22,ew49,ew51],lh 4 [4,1,6,28,35,23,37,5,69,27,31,26,34] [0x40a2259220302181,0x30034004c1611b10,0x7765]⟩,
  ⟨7,4,[ew60,ew20,ew21,ew22,ew23],lh 4 [4,6,35,34,24,37,1,31,5,27,28] [0x4388750202661914,0x532030411510a013,0x200237]⟩,
  ⟨7,4,[ew20,ew21,ew22,ew49,ew52],lh 4 [4,1,5,6,17,23,34,72,27,31,30,35,37] [0x6093358230703141,0xb0200a4114621210,0xc225]⟩,
  ⟨7,4,[ew61,ew20,ew21,ew22,ew23],lh 4 [5,1,6,34,27,35,4,31,37,17] [0x9180706613132424,0x1013314020254521,0x70530]⟩,
  ⟨7,4,[ew62,ew20,ew21,ew22,ew23],lh 4 [5,34,35,6,28,31,17,1,4,37,27] [0x61050588247716a3,0x9021145030324231,0x90210]⟩,
  ⟨7,4,[ew20,ew22,ew50,ew23,ew51],lh 4 [1,35,6,34,27,37,4,30,5,74,33] [0x4323422520402141,0x7500a3137159166,0x8830]⟩,
  ⟨7,4,[ew20,ew21,ew50,ew23,ew52],lh 4 [4,5,34,6,35,24,27,26,1,74,33,37] [0x5434613130603252,0x7100a4227219180,0xb140]⟩,
  ⟨7,4,[ew20,ew21,ew22,ew23,ew63],lh 4 [4,5,1,6,27,34,24,23,75,17,35,28,31] [0x8337413130403262,0xb0100a9251212050,0xc1]⟩,
  ⟨7,4,[ew64,ew20,ew21,ew22,ew23],lh 3 [4,1,6,27,34,35,5,24] [0x611e76a2886169a,0x502c26110349a]⟩,
  ⟨7,4,[ew65,ew20,ew21,ew22,ew23],lh 4 [4,1,37,17,28,27,35,6,31,5,34] [0x31992804041a1377,0x1310605282405051,0x600621]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨7,4,[ew20,ew21,ew22,ew51,ew52],lh 4 [4,5,1,6,37,24,27,26,74,34,30,35] [0x5334613130603252,0xb0100a4227912080,0x4117]⟩,
  ⟨7,4,[ew66,ew20,ew21,ew22,ew23],lh 3 [5,1,6,27,34,37,4,24] [0x3691e68a3630c4d3,0xa2c04190b082]⟩,
  ⟨7,4,[ew67,ew20,ew21,ew22,ew23],lh 4 [4,5,1,28,17,6,31,24,34,35,37] [0x721a160903242455,0x2120807161303042,0x100381]⟩,
  ⟨7,4,[ew68,ew20,ew21,ew22,ew23],lh 3 [4,5,6,35,24,37,1,27] [0xe1488d3430f6514,0x101d34b0c728a]⟩,
  ⟨7,3,[ew47,ew48,ew50,ew23],lh 4 [5,34,35,23,1,37,4,26,28,31] [0x6623105044132117,0x9080502]⟩,
  ⟨7,3,[ew47,ew22,ew49,ew51],lh 4 [4,1,35,37,23,28,5,26,34] [0x2002811431171020,0x66345005]⟩,
  ⟨7,3,[ew69,ew20,ew21,ew22],lh 3 [4,5,1,6,27,34,35,24] [0x6206bac082a92e1,0x85]⟩,
  ⟨7,3,[ew70,ew20,ew21,ew23],lh 3 [4,5,1,6,27,34,35,24] [0x18596bac01150118,0x14a]⟩,
  ⟨7,3,[ew21,ew48,ew49,ew52],lh 4 [4,5,1,34,23,28,17,30,35,37] [0x1007622531212030,0x91148004]⟩,
  ⟨7,3,[ew71,ew20,ew22,ew23],lh 3 [4,5,1,6,34,27,24,35] [0x7a5962828c10259a,0x40]⟩,
  ⟨7,3,[ew20,ew50,ew51,ew52],lh 3 [4,5,35,6,27,26,24,30] [0x5405207c9a859620,0x89]⟩,
  ⟨7,3,[ew72,ew21,ew22,ew23],lh 3 [4,5,1,6,27,34,24,35] [0x7a514282cc103593,0x40]⟩,
  ⟨10,3,[ew32,ew33,ew34,ew35],lh 4 [10,9,8,13,78,79,6,76,77,80,15] [0x5513442001817006,0x12a23293]⟩,
  ⟨11,7,[ew36,ew37,ew38,ew39,ew40],lh 6 [26,12,0,10,13,84,8,5,9,81,4,91,6,82,27,98,86,89,92,16,28,83,85,87,77,88,90,93,94,95,96,97,19] [0x34d543103009349,0x3283149104003,0x4d3009409589041,0x1516580031c75c3,0x822c36830111d1,0x12092012186003,0x514144041003186,0x70441014d0416ce,0x1cc14c20c1441dd,0x14408414420414c,0x7c400e08e00e78c,0x14a1c72c12012e0,0x1812c11c114a208,0xa18600a08a2c1,0x823c81862c1082,0x3c80823c71863c7]⟩,
  ⟨11,6,[ew36,ew37,ew73,ew38,ew39,ew40],lh 5 [26,9,12,0,10,13,8,5,84,86,4,18,102,81,98,103,99,100,82,101,95,104,105] [0x239a82948020010,0x2531108892200d,0x4280208109044,0x58d6b3188321004,0x28840048ae290c4,0x29ce54950214d29,0x28ca50858763034,0x7a9454140318000,0x41cef10aca55529,0xc68085073a021,0x1044031803180c6,0x11842389410a8e7,0x98221894632863,0x1184e631c63]⟩,
  ⟨11,6,[ew36,ew37,ew38,ew74,ew39,ew40],lh 5 [13,26,9,0,5,81,8,19,12,82,16,103,84,89,108,27,91,10,98,86,100,106,107,109,110,104,111,80,112,113] [0x280014a68001529,0x2ca2b420a12ac35,0x689ad0d8a212d71,0x70dce318a329425,0x4a129ba408414c5,0x3000c80ec39f00,0x390e711c0421f47,0x799ef0ec0600040,0x409010cd1299f80,0x519482114252884,0x8084a18c2630463,0xf6102118213084,0x1184118c2108463,0x21888631063]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨11,6,[ew75,ew36,ew37,ew38,ew39,ew40],lh 5 [0,10,82,103,5,8,9,13,26,19,12,116,16,92,27,98,84,86,81,114,91,115,77,117,95,118,119,120] [0x988434a50393c21,0x18e2f5460210ce7,0xa108331a0420cc6,0x400032950000ca5,0x69da1104273b442,0x90234546a50461,0x8021405645ad16,0x3a8e1285605acab,0x1104719c4a10ae2,0x48122319244a4d8,0x518c2d25c073919,0x6158a211866309b,0x314ac000652a000,0x60008529000]⟩,
  ⟨11,6,[ew36,ew37,ew38,ew76,ew40],lh 5 [26,13,84,86,0,16,107,5,82,9,77,121,8,27,28,10,118] [0x1080082102908,0x18a50286a02821,0x598e6028a501866,0x5a98c018860080f,0x104a10198602884,0x10463120a512063,0x104e110521120e7,0x34100048112129,0x10d23004410348d,0x10ce311525114e5,0x398e0388400d83,0x59c845a56900c83,0x5a48401c07]⟩,
  ⟨11,6,[ew77,ew36,ew37,ew38,ew40],lh 5 [26,10,8,13,5,9,12,0,91,27,19,81,122,84,28,4,92,86,89,82,123,124,80,125] [0x69129001b261032,0x6914a4152541545,0x411c4411e4415c5,0x610e461445415ef,0x2d4a014e761042,0x2c630054100463,0x2deb02ccb005e1,0x4042004e1004c6,0x68cc660441040f0,0xa8e236ccc6a4e31,0x24490241600c43,0x38f70184200d03,0x18e70384e]⟩,
  ⟨11,6,[ew36,ew37,ew38,ew78,ew39,ew40],lh 5 [92,84,9,8,0,28,82,86,10,89,5,128,27,26,103,81,91,77,98,12,101,109,117,104,126,123,127,13,118,125,129] [0x4086311440180,0x580f295f5780a0,0x60086a117401a0,0x64091252188051,0x48d202000302489,0x348ce294c13383a,0x5a96b108ca339db,0x60d8c0f16359846,0x388e10ccf29ac2b,0x38ce751c221054a,0xfa07210a32949d,0x80c611082108442,0x10c70211a31b484,0x2211431a884]⟩,
  ⟨11,6,[ew79,ew36,ew37,ew38,ew39,ew40],lh 5 [81,0,103,9,5,8,10,86,13,19,84,89,92,6,28,26,98,12,130,82,91,110,107,124,131,95,80,125] [0x7800231a40008c6,0x10a303c5429c108,0x5108218d4420863,0xa0422295e1088a5,0x2006498c830120,0x308c038015018e6,0x5c0b22d6ab0080,0x5956c0b1852ac2b,0x41102560473a048,0x4852818d244a479,0x38c69525a16b55a,0x394e721c431a884,0x194a7085c57383b,0x30848529021]⟩,
  ⟨11,6,[ew36,ew37,ew38,ew39,ew80],lh 5 [26,10,84,0,118,5,12,8,81,9,89,80,132,16,28,86,6,107,13] [0x6010040102210,0x20c8005c102008,0x521004c6021c8,0x4010292a02811,0x461004e10286a,0x111ce12cc6028ea,0x110a412dcb110c4,0x1112412ca562d2b,0x119290005261064,0x118a51352d134a5,0x3cef03c6f034ed,0x61463630e703463,0x63614e7]⟩,
  ⟨11,6,[ew81,ew36,ew37,ew38,ew39],lh 5 [84,9,0,26,8,4,82,13,92,91,5,10,81,89,133,86,16,19,12,27,112,119,107] [0x491a449104189a2,0x18c73708e718908,0x489e2488a2491ef,0x7094271024490a5,0x1a0c80114470821,0x20e81accb02ce7,0x1b0aca32101acab,0x34161b02caae0b,0x1ca50312c1b42d,0x1de7018a6019e6,0x45510442101946,0x154a0482171826,0x495201421]⟩,
  ⟨11,5,[ew37,ew73,ew38,ew74,ew39,ew40],lh 5 [9,12,10,8,81,13,5,0,82,135,134,99,95,26,106,84,86,136] [0x614452aca150508,0x23c240b8a368d29,0x808871900601044,0x100c008ce1080c0,0xce014462]⟩,
  ⟨11,5,[ew36,ew73,ew38,ew78,ew39,ew40],lh 5 [18,8,82,13,86,5,0,9,99,10,127,137,138,135,81,134,84,26,12,125] [0x8006042004781c2,0x1c4825292002407,0x90d8c0896b38862,0x6b4a32066129ca4,0x314c1304c1]⟩,
  ⟨11,5,[ew36,ew37,ew38,ew82,ew39,ew40],lh 5 [8,13,10,9,12,81,102,91,92,107,0,86,19,118,4,120,125,84,26,15] [0x48902114a228825,0x604245840a00843,0x791c4081a0098c1,0x1c7119c8081083,0x6098c12]⟩,
  ⟨11,5,[ew83,ew36,ew37,ew38,ew39,ew40],lh 4 [8,13,5,9,0,82,10,81,4,12,107,118] [0x432329815156767,0x462a26776151504,0x2310b01232155104,0x3043404023]⟩,
  ⟨11,5,[ew36,ew37,ew74,ew78,ew39,ew40],lh 5 [108,82,86,12,9,0,8,5,89,81,127,137,139,140,134,10,106,13,118,26] [0x40060041e0005c1,0x884415292002408,0x1885309a415ac81,0x6b483630c2390e2,0x29ca4298a3]⟩,
  ⟨11,5,[ew79,ew36,ew37,ew74,ew39,ew40],lh 5 [81,8,13,19,9,5,12,0,106,82,140,86,139,4,10,107,80] [0x528a46992901908,0x781c010c40384e6,0x1886210c2708004,0xaca42ac6180443,0x852918c]⟩,
  ⟨11,5,[ew84,ew36,ew37,ew38,ew39,ew40],lh 5 [12,9,5,10,86,8,19,81,136,80,13,91,26,76,107,125,139] [0x104040114638ce3,0x11a3198ac2ac41,0x2010828c6170404,0x100c54a42208880,0x221041078001]⟩,
  ⟨11,5,[ew81,ew36,ew37,ew38,ew74,ew39],lh 5 [9,81,13,12,8,0,19,82,5,141,27,91,142,106,10,107,86,120] [0x2ac852914448481,0xb42711c8028185,0x308671840f03823,0x4470188c611842,0x802003]⟩,
  ⟨11,5,[ew36,ew37,ew38,ew85,ew74,ew39],lh 4 [9,82,81,0,19,16,8,5,13,106,10,107,118,86,26] [0xb2a223625298484,0x701411413c141152,0x30e37050d536361,0x70706]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨11,5,[ew36,ew37,ew86,ew38,ew39,ew40],lh 5 [8,10,92,9,0,82,12,86,115,137,118,143,81,16,77,13,91,84,120] [0x421a21042c58425,0x299e50884110dc2,0x398a052929194e6,0x90c80200711c0e6,0x8020080200e3]⟩,
  ⟨11,5,[ew75,ew36,ew37,ew78,ew39,ew40],lh 5 [92,8,10,86,9,82,5,0,127,12,140,116,81,4,125,77,13,118] [0x310c368ca34218b,0x84000845185c3,0x21a0510002011e0,0x3a54a224a188486,0xe1384e1]⟩,
  ⟨11,5,[ew81,ew75,ew36,ew37,ew38,ew39],lh 4 [8,0,10,19,82,9,12,5,27,81,86,76,115,77,120] [0x7001108010010110,0x237575a643439205,0x334344625d2c62b2,0x65e64]⟩,
  ⟨11,5,[ew77,ew36,ew37,ew38,ew78,ew40],lh 5 [92,82,8,81,9,5,10,86,0,107,137,91,144,127,13,118,12,125] [0x2ac852914420520,0x198063048228985,0xb46000c03180c3,0x144f03844f0b827,0x812047]⟩,
  ⟨11,5,[ew79,ew77,ew36,ew37,ew38,ew40],lh 4 [8,5,9,0,81,13,92,10,12,76,86,82,107,131,80] [0x303088b546461212,0x56201021121221c1,0xe0da57307744a99,0x30305]⟩,
  ⟨11,5,[ew87,ew36,ew37,ew38,ew39,ew40],lh 4 [9,92,8,28,27,12,0,13,135,10,91,84,77,120] [0x620b0a3535474791,0x1610c01351147162,0xd072428804353521,0x260623230]⟩,
  ⟨11,5,[ew36,ew37,ew38,ew88,ew78,ew40],lh 5 [81,9,82,8,10,92,28,0,5,137,86,27,107,127,13,118,12,125,84] [0x580200040108b,0x1184d014a028005,0xa0c23bc4e12521,0x1a0720a871540c8,0x719c61]⟩,
  ⟨11,5,[ew36,ew89,ew37,ew38,ew39,ew40],lh 5 [81,12,9,8,5,13,86,0,143,82,10,107,19,91,26,80,125] [0x580200190828140,0x98ac4a40718002,0x314ee3b48220826,0x204a379444110c1,0x4320c2380c22]⟩,
  ⟨11,4,[ew73,ew74,ew78,ew39,ew40],lh 4 [8,82,0,10,9,5,127,106,12,145,146,99,136,13,135] [0xaa01994181773166,0xee5dcc03545483bb,0x2020202d]⟩,
  ⟨11,4,[ew36,ew90,ew37,ew38,ew39],lh 4 [0,9,8,81,13,78,82,19,141,107,27,120,12] [0x5195533537432080,0x4664210120020a40,0xc1b16716]⟩,
  ⟨11,4,[ew91,ew36,ew37,ew38,ew40],lh 4 [5,9,10,82,92,79,86,8,107,137,81,147,125] [0x1001100101900820,0x5335244246a64323,0x67c757b5]⟩,
  ⟨12,9,[ew41,ew42,ew43,ew44,ew45,ew46],lh 6 [149,153,9,159,19,148,16,22,81,152,8,155,157,158,0,18,17,150,154,82,160,5,13,86,12,37,92,24,28,151,95,156,98,161,120,125] [0x10f00f58f005104,0xf41000559600f,0x451005405005445,0x81860055c500f,0x880051850085c8,0x908900901d008,0x28a0091c9008008,0x928901a1da01a,0x44b04b492056451,0x4b60b05649204b,0x5cb0536130535d7,0x4409e05365304b,0x1c4053082044644,0x1b1db01b01f004,0x30c812618004044,0xd230c0cd60d0cd,0x940d46590cd08d,0xd42940cd64d0d4,0x1c70d02900d01e1,0x4656204c08c0d4,0x1c604c555046086,0x1c1dc01c3a3006,0x38e00228200638e,0x238e015295015]⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 32 then
    if i < 16 then
      nodesBlock0[(i-0)]?
    else
      nodesBlock1[(i-16)]?
  else
    if i < 48 then
      nodesBlock2[(i-32)]?
    else
      if i < 64 then
        nodesBlock3[(i-48)]?
      else
        nodesBlock4[(i-64)]?
def fastViews : QFast.Table View := ⟨13,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨76,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,36,0,0,0,40,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,52,0,0,0,56,0,0,0,60,0,0,0]
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,34,0,0,0,40,0,0,0,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,50,0,0,0,56,0,0,0,58,0,0,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,34,0,0,0,36,0,0,0,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,50,0,0,0,52,0,0,0,54,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,34,0,0,0,36,0,0,0,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,0,0,0,42,0,0,0,44,0,0,0,46,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,17,0,0,0,24,0,0,0,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,49,0,0,0,56,0,0,0,57,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,2,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,9,0,0,0,10,0,0,0,11,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,3,0,8,0,9,0,10,0,11,0,48,0,49,0,50,0,51,0,56,0,57,0,58,0,59,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,17,0,20,0,21,0,24,0,25,0,28,0,29,0,48,0,49,0,52,0,53,0,56,0,57,0,60,0,61,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap3)
  | 5 => some (0, aliasMap4)
  | 6 => some (0, aliasMap5)
  | 8 => some (7, aliasMap6)
  | 9 => some (7, aliasMap7)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 13 = true := by decide +kernel
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 13 = true := blockRoots_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 47 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_47 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 47 28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_75 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 75 1 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 75 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 47 28 blockNodes_0 blockNodes_47
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 76 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 75 1 joinNodes_0_0 blockNodes_75
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 76 = true := joinNodes_1_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfffefeeafeecfee8 : Word) && vk v == 9 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfffefeeafeecfee8 : BitVec 64) 9 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 12) = true := by decide +kernel
  cases ev : QFast.get fastViews 12 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_46362_aux

open PEqualNP.Outside.L_meta_46362_aux in
theorem PEqualNP.Outside.L_meta_46362 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901482 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901482 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
