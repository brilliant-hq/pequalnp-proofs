import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46284_aux
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
  ⟨[⟨.or,[3,4]⟩, ⟨.or,[4,5]⟩, ⟨.and,[2,7]⟩, ⟨.or,[1,8]⟩, ⟨.or,[3,5]⟩,
    ⟨.or,[9,10]⟩, ⟨.and,[1,2]⟩, ⟨.or,[10,12]⟩, ⟨.and,[6,9]⟩, ⟨.and,[13,14]⟩,
    ⟨.or,[0,15]⟩, ⟨.and,[11,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4278124202 * 2 ^ 32 + 4276678280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfefefeaafee8ee88
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4278124202 * 2 ^ 32 + 4276678280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfefefeaafee8ee88 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfefefeaafee8ee88 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276678280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276678280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
def ew0 : Word := 0x1000100010001000
def ew1 : Word := 0x1010000010100000
def ew2 : Word := 0x1010101000000000
def ew3 : Word := 0x40404040
def ew4 : Word := 0x50005000
def ew5 : Word := 0x50500000
def ew6 : Word := 0x44000000440000
def ew7 : Word := 0x50000000500000
def ew8 : Word := 0x55000000000000
def ew9 : Word := 0x44440000
def ew10 : Word := 0x55000000
def ew11 : Word := 0x20002000200020
def ew12 : Word := 0x30000000300000
def ew13 : Word := 0x30003000000000
def ew14 : Word := 0x202000002020
def ew15 : Word := 0x300000003000
def ew16 : Word := 0x303000000000
def ew17 : Word := 0x20202020
def ew18 : Word := 0x30003000
def ew19 : Word := 0x30300000
def ew20 : Word := 0x22000000220000
def ew21 : Word := 0x33000000000000
def ew22 : Word := 0xa0000000a0000
def ew23 : Word := 0xc0000000c0000
def ew24 : Word := 0xf000000000000
def ew25 : Word := 0xa0a
def ew26 : Word := 0xc0c
def ew27 : Word := 0xf00
def ew28 : Word := 0xa000a0
def ew29 : Word := 0xc000c0
def ew30 : Word := 0xf00000
def ew31 : Word := 0xa000a000a000a0
def ew32 : Word := 0x84008400840084
def ew33 : Word := 0xa5000000a50000
def ew34 : Word := 0xa500a500000000
def ew35 : Word := 0x4444000044440000
def ew36 : Word := 0x4040101040401010
def ew37 : Word := 0x4400110044001100
def ew38 : Word := 0x4444111100000000
def ew39 : Word := 0x222200002222
def ew40 : Word := 0x303000003030
def ew41 : Word := 0x330000003300
def ew42 : Word := 0x333300000000
def ew43 : Word := 0x4444444400000000
def ew44 : Word := 0x4040404010101010
def ew45 : Word := 0x4400440011001100
def ew46 : Word := 0x4444000011110000
def ew47 : Word := 0x808080802020202
def ew48 : Word := 0xc0c0c0c00000000
def ew49 : Word := 0xc000c0003000300
def ew50 : Word := 0xc0c000003030000
def ew51 : Word := 0x88008800220022
def ew52 : Word := 0xcc00cc00000000
def ew53 : Word := 0xc000c000300030
def ew54 : Word := 0xcc000000330000
def ew55 : Word := 0x4004400440044004
def ew56 : Word := 0x5000500050005000
def ew57 : Word := 0x5005000050050000
def ew58 : Word := 0x5005500500000000
def ew59 : Word := 0x2200220000220022
def ew60 : Word := 0x3000300000300030
def ew61 : Word := 0x3300330000000000
def ew62 : Word := 0x3300000000330000
def ew63 : Word := 0x2020202020202020
def ew64 : Word := 0x3000300030003000
def ew65 : Word := 0x3030000030300000
def ew66 : Word := 0x3030303000000000
def ew67 : Word := 0xa0a0a0a0
def ew68 : Word := 0xc0c0c0c0
def ew69 : Word := 0xf000f000
def ew70 : Word := 0xf0f00000
def ew71 : Word := 0xaa000000aa0000
def ew72 : Word := 0xcc000000cc0000
def ew73 : Word := 0xf0000000f00000
def ew74 : Word := 0xff000000000000
def ew75 : Word := 0xaaaa0000
def ew76 : Word := 0xcccc0000
def ew77 : Word := 0xff000000
def ew78 : Word := 0x1111444400000000
def ew79 : Word := 0x1111000022220000
def ew80 : Word := 0x1010404020208080
def ew81 : Word := 0x1100440022008800
def ew82 : Word := 0x8008200280082002
def ew83 : Word := 0xc00c0000c00c0000
def ew84 : Word := 0xc0003000c0003000
def ew85 : Word := 0xc00c300300000000
def ew86 : Word := 0x505050500000000
def ew87 : Word := 0x404040408080808
def ew88 : Word := 0x50005000a000a00
def ew89 : Word := 0x50500000a0a0000
def ew90 : Word := 0x1100110011001100
def ew91 : Word := 0x1040104010401040
def ew92 : Word := 0x1144000011440000
def ew93 : Word := 0x1144114400000000
def ew94 : Word := 0x4444444444444444
def ew95 : Word := 0x5050505050505050
def ew96 : Word := 0x5500550055005500
def ew97 : Word := 0x5555000055550000
def ew98 : Word := 0x5555555500000000
def ew99 : Word := 0xa0a0a0a0a0a0a0a
def ew100 : Word := 0xc0c0c0c0c0c0c0c
def ew101 : Word := 0xf000f000f000f00
def ew102 : Word := 0xf0f00000f0f0000
def ew103 : Word := 0xf0f0f0f00000000
def ew104 : Word := 0xaaaa0000aaaa
def ew105 : Word := 0xcccc0000cccc
def ew106 : Word := 0xf0f00000f0f0
def ew107 : Word := 0xff000000ff00
def ew108 : Word := 0xffff00000000
def ew109 : Word := 0xaaaaaaaaaaaaaaaa
def ew110 : Word := 0xcccccccccccccccc
def ew111 : Word := 0xf0f0f0f0f0f0f0f0
def ew112 : Word := 0xff00ff00ff00ff00
def ew113 : Word := 0xffff0000ffff0000
def ew114 : Word := 0xffffffff00000000
def ew115 : Word := 0x80008000800080
def ew116 : Word := 0xa400a400a400a4
def ew117 : Word := 0x4000400040004
def ew118 : Word := 0xa0000000a00000
def ew119 : Word := 0xa500a000a500a0
def ew120 : Word := 0xa0000000a0
def ew121 : Word := 0x5000000050000
def ew122 : Word := 0xa000a000000000
def ew123 : Word := 0xa500a500a000a0
def ew124 : Word := 0x5000500000000
def ew125 : Word := 0x84000000840000
def ew126 : Word := 0xa5008400a50084
def ew127 : Word := 0x8400000084
def ew128 : Word := 0x21000000210000
def ew129 : Word := 0x84008400000000
def ew130 : Word := 0xa500a500840084
def ew131 : Word := 0x840084
def ew132 : Word := 0x21002100000000
def ew133 : Word := 0xa5000000000000
def ew134 : Word := 0xa500a500a50000
def ew135 : Word := 0xa50000
def ew136 : Word := 0xa500000000
def ew137 : Word := 0xa5008000a50080
def ew138 : Word := 0x25000000250000
def ew139 : Word := 0xa500a500800080
def ew140 : Word := 0x25002500000000
def ew141 : Word := 0xa4000000a40000
def ew142 : Word := 0xa4000000a4
def ew143 : Word := 0xa400a400000000
def ew144 : Word := 0xa400a4
def ew145 : Word := 0xa4008400a40084
def ew146 : Word := 0x4008400040084
def ew147 : Word := 0xa500a500a00000
def ew148 : Word := 0x500a500000000
def ew149 : Word := 0x84008000840080
def ew150 : Word := 0x21002000210020
def ew151 : Word := 0xa500a000000000
def ew152 : Word := 0xa500a0
def ew153 : Word := 0xa400a400840084
def ew154 : Word := 0x4000400840084
def ew155 : Word := 0xa500a000a50000
def ew156 : Word := 0x5000000a50000
def ew157 : Word := 0x84008400800080
def ew158 : Word := 0x21002100200020
def ew159 : Word := 0xa5000000a00000
def ew160 : Word := 0xa5000000a0
def ew161 : Word := 0xa500a500000084
def ew162 : Word := 0xa5002100000000
def ew163 : Word := 0xa500a500210000
def ew164 : Word := 0x8400a500000000
def ew165 : Word := 0xa5000000a50084
def ew166 : Word := 0xa5000000210000
def ew167 : Word := 0xa5002100a50000
def ew168 : Word := 0x84000000a50000
def ew169 : Word := 0x84008400a50084
def ew170 : Word := 0x84008400000084
def ew171 : Word := 0x8400a500840084
def ew172 : Word := 0x84000000840084
def ew173 : Word := 0x3020302030203020
def ew174 : Word := 0x3030202030302020
def ew175 : Word := 0x3030303020202020
def ew176 : Word := 0x3030300030303000
def ew177 : Word := 0x3030303030003000
def ew178 : Word := 0x3030303030300000
def ew179 : Word := 0x3030302030303020
def ew180 : Word := 0x302000003020
def ew181 : Word := 0x3030303030203020
def ew182 : Word := 0x30203020
def ew183 : Word := 0x30002000300020
def ew184 : Word := 0x3030303030302020
def ew185 : Word := 0x30302020
def ew186 : Word := 0x30003000200020
def ew187 : Word := 0x303000002020
def ew188 : Word := 0x1010100010101000
def ew189 : Word := 0x3030303030303000
def ew190 : Word := 0x30303000
def ew191 : Word := 0x1010101010001000
def ew192 : Word := 0x303000003000
def ew193 : Word := 0x1010101010100000
def ew194 : Word := 0x30003000300000
def ew195 : Word := 0x30303020
def ew196 : Word := 0x303000003020
def ew197 : Word := 0x30003000300020
def ew198 : Word := 0x1010101010101000
def ew199 : Word := 0x1111000000000000
def ew200 : Word := 0x1111444422220000
def ew201 : Word := 0x444400000000
def ew202 : Word := 0x22220000
def ew203 : Word := 0x1010404000000000
def ew204 : Word := 0x1111444420208080
def ew205 : Word := 0x101040400000000
def ew206 : Word := 0x20208080
def ew207 : Word := 0x1100440000000000
def ew208 : Word := 0x1111444422008800
def ew209 : Word := 0x11004400000000
def ew210 : Word := 0x22008800
def ew211 : Word := 0x1010000020200000
def ew212 : Word := 0x1111404022228080
def ew213 : Word := 0x101000002020000
def ew214 : Word := 0x404000008080
def ew215 : Word := 0x1100000022000000
def ew216 : Word := 0x1111440022228800
def ew217 : Word := 0x11000000220000
def ew218 : Word := 0x440000008800
def ew219 : Word := 0x1000400020008000
def ew220 : Word := 0x1110444022208880
def ew221 : Word := 0x10004000200080
def ew222 : Word := 0x100040002000800
def ew223 : Word := 0x1111440022008800
def ew224 : Word := 0x440022008800
def ew225 : Word := 0x1010404020200000
def ew226 : Word := 0x101040402020000
def ew227 : Word := 0x1100440022000000
def ew228 : Word := 0x11004400220000
def ew229 : Word := 0x1010444420208080
def ew230 : Word := 0x1010000020208080
def ew231 : Word := 0x1100440022208880
def ew232 : Word := 0x1100440002000800
def ew233 : Word := 0x1111000022228080
def ew234 : Word := 0x1111000002020000
def ew235 : Word := 0x1010404022208880
def ew236 : Word := 0x1010404000200080
def ew237 : Word := 0x1111000022228800
def ew238 : Word := 0x1111000000220000
def ew239 : Word := 0x1110440022208800
def ew240 : Word := 0x100440002008800
def ew241 : Word := 0x1111444420200000
def ew242 : Word := 0x101444400000000
def ew243 : Word := 0x1010400020208000
def ew244 : Word := 0x101040002020800
def ew245 : Word := 0x1111444400220000
def ew246 : Word := 0x1100444400000000
def ew247 : Word := 0x1010444020208880
def ew248 : Word := 0x1010004020200080
def ew249 : Word := 0x1111444400008800
def ew250 : Word := 0x1111004400000000
def ew251 : Word := 0x1111400022228000
def ew252 : Word := 0x111000002220000
def ew253 : Word := 0x1111444420008000
def ew254 : Word := 0x111044400000000
def ew255 : Word := 0x1100110000000000
def ew256 : Word := 0x44004400000000
def ew257 : Word := 0x5544554455445544
def ew258 : Word := 0x5555555544444444
def ew259 : Word := 0x5050000050500000
def ew260 : Word := 0x5555555555005500
def ew261 : Word := 0x55445544
def ew262 : Word := 0x55005500440044
def ew263 : Word := 0x1111111111001100
def ew264 : Word := 0x808080808080808
def ew265 : Word := 0xe0e0e0e0e0e0e0e
def ew266 : Word := 0x202020202020202
def ew267 : Word := 0x404040404040404
def ew268 : Word := 0xf080f080f080f08
def ew269 : Word := 0xe000e000e000e
def ew270 : Word := 0xeeeeeeeeeeeeeeee
def ew271 : Word := 0xffaaffaaffaaffaa
def ew272 : Word := 0xffffffffaaaaaaaa
def ew273 : Word := 0xffccffccffccffcc
def ew274 : Word := 0x3333000033330000
def ew275 : Word := 0xffffffffcccccccc
def ew276 : Word := 0xf000f000f000f0
def ew277 : Word := 0xf0f00000f0f00000
def ew278 : Word := 0xffffffffff00ff00
def ew279 : Word := 0xffeeffeeffeeffee
def ew280 : Word := 0xee00ee00ee00ee
def ew281 : Word := 0x1111000011110000
def ew282 : Word := 0xffffffffeeeeeeee
def ew283 : Word := 0xeeeeeeee
def ew284 : Word := 0xff50ff50ff50ff50
def ew285 : Word := 0x3322332233223322
def ew286 : Word := 0x50005000500050
def ew287 : Word := 0xffffffffffaaffaa
def ew288 : Word := 0xffaaffaa
def ew289 : Word := 0xddddccccddddcccc
def ew290 : Word := 0x3333333322222222
def ew291 : Word := 0xff00ff00aa00aa
def ew292 : Word := 0xffffffffffccffcc
def ew293 : Word := 0xffccffcc
def ew294 : Word := 0xbbbbaaaabbbbaaaa
def ew295 : Word := 0xff00ff00cc00cc
def ew296 : Word := 0xaafaaafaaafaaafa
def ew297 : Word := 0xfafaaaaafafaaaaa
def ew298 : Word := 0x3333333333003300
def ew299 : Word := 0xffffffffffeeffee
def ew300 : Word := 0xffeeffee
def ew301 : Word := 0xffffffff00ee00ee
def ew302 : Word := 0xff00ff00ee00ee
def ew303 : Word := 0xff00ff00ffeeffee
def ew304 : Word := 0xee00ee
def ew305 : Word := 0xffffffff33223322
def ew306 : Word := 0x33223322
def ew307 : Word := 0x3333333333223322
def ew308 : Word := 0xccccccccffeeffee
def ew309 : Word := 0xff33ff33ff22ff22
def ew310 : Word := 0xccffccffcceeccee
def ew311 : Word := 0xffffffff55445544
def ew312 : Word := 0x5555555555445544
def ew313 : Word := 0xaaaaaaaaffeeffee
def ew314 : Word := 0xff55ff55ff44ff44
def ew315 : Word := 0xaaffaaffaaeeaaee
def ew316 : Word := 0xddddddddddccddcc
def ew317 : Word := 0xbbbbbbbbbbaabbaa
def labelsBlock0 : Array Nat := #[
  0x3450,
  0x2c90,
  0x1c30,
  0x1,
  0x2580,
  0x3288,
  0x32c0,
  0x3248,
  0x5,
  0x2ca0,
  0x2590,
  0x2c30,
  0x1016,
  0x3490,
  0x105,
  0x3ce0
]
def labelsBlock1 : Array Nat := #[
  0x2e98,
  0x38a8,
  0x261c,
  0x1b1,
  0x1618,
  0x2c98,
  0x2e9,
  0x2a88,
  0x2aa0,
  0x2f5,
  0x304,
  0x120c,
  0xa08,
  0x308,
  0x319,
  0x2114
]
def labelsBlock2 : Array Nat := #[
  0x1c50,
  0x300,
  0x2104,
  0x1544,
  0x335,
  0x9,
  0x1548,
  0x714,
  0x708,
  0xd,
  0x11,
  0x700,
  0x15,
  0x19,
  0x121c,
  0x1514
]
def labelsBlock3 : Array Nat := #[
  0x1540,
  0x1d,
  0x21,
  0x1500,
  0x25,
  0x29,
  0x221c,
  0x2514,
  0x2d,
  0x31,
  0x2500,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x1714
]
def labelsBlock4 : Array Nat := #[
  0x45,
  0x49,
  0x4d,
  0x51,
  0x55,
  0x59,
  0x5d,
  0x3208,
  0x61,
  0x65,
  0x69,
  0x6d,
  0x71,
  0x75,
  0x79,
  0x7d
]
def labelsBlock5 : Array Nat := #[
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
  0x3240,
  0xb1,
  0xb5,
  0x2780
]
def labelsBlock6 : Array Nat := #[
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0x1748,
  0xc9,
  0xcd,
  0xd1,
  0xd5,
  0xd9,
  0x2788,
  0xdd,
  0xe1,
  0xe5,
  0x2714,
  0xe9
]
def labelsBlock7 : Array Nat := #[
  0xed,
  0x35c0,
  0xf1,
  0xf5,
  0xf9,
  0xfd,
  0x101,
  0x1002,
  0xd30,
  0xd14,
  0x109,
  0x1012,
  0x1550,
  0x10d,
  0x111,
  0x101a
]
def labelsBlock8 : Array Nat := #[
  0x115,
  0x119,
  0x11d,
  0x121,
  0x125,
  0x129,
  0x12d,
  0x131,
  0x135,
  0x139,
  0x13d,
  0x141,
  0x145,
  0x149,
  0x14d,
  0x151
]
def labelsBlock9 : Array Nat := #[
  0x155,
  0x159,
  0x15d,
  0x161,
  0x165,
  0x169,
  0x16d,
  0x171,
  0x175,
  0x179,
  0x17d,
  0x181,
  0x185,
  0x189,
  0x18d,
  0x191
]
def labelsBlock10 : Array Nat := #[
  0x195,
  0x199,
  0x19d,
  0x1a1,
  0x1a5,
  0x1a9,
  0x1ad,
  0x110c,
  0x1b5,
  0x2654,
  0x3864,
  0x1b9,
  0x1bd,
  0x300c,
  0x1c1,
  0x220c
]
def labelsBlock11 : Array Nat := #[
  0x1c5,
  0x1c9,
  0x1cd,
  0x260c,
  0x34c0,
  0x1d1,
  0x1944,
  0x1d5,
  0x222c,
  0x1d9,
  0x1dd,
  0x1e1,
  0x1e5,
  0x1e9,
  0x111c,
  0x3498
]
def labelsBlock12 : Array Nat := #[
  0x1ed,
  0x3488,
  0x1f1,
  0x1f5,
  0x1f9,
  0x1fd,
  0x112c,
  0x201,
  0x205,
  0x3c98,
  0x209,
  0x20d,
  0x2a98,
  0x211,
  0x215,
  0x1d44
]
def labelsBlock13 : Array Nat := #[
  0x219,
  0x38d0,
  0x225,
  0x229,
  0x22d,
  0x231,
  0x235,
  0x239,
  0x23d,
  0x241,
  0x245,
  0x249,
  0x24d,
  0x251,
  0x255,
  0x259
]
def labelsBlock14 : Array Nat := #[
  0x25d,
  0x261,
  0x265,
  0x269,
  0x26d,
  0x271,
  0x275,
  0x279,
  0x221,
  0x27d,
  0x281,
  0x285,
  0x289,
  0x28d,
  0x291,
  0x2e88
]
def labelsBlock15 : Array Nat := #[
  0x21d,
  0x295,
  0x299,
  0x29d,
  0x2a1,
  0x2a5,
  0x2a9,
  0x2ad,
  0x2b1,
  0x2b5,
  0x2b9,
  0x2bd,
  0x2c1,
  0x2c5,
  0x2c9,
  0x2cd
]
def labelsBlock16 : Array Nat := #[
  0x2d1,
  0x2d5,
  0x2d9,
  0x2dd,
  0x2e1,
  0x2e5,
  0x1648,
  0x38c8,
  0x1c48,
  0x2ed,
  0x2f1,
  0x1650,
  0x2f9,
  0x100a,
  0x1032,
  0x2fd
]
def labelsBlock17 : Array Nat := #[
  0xa20,
  0x1006,
  0x1c60,
  0x1046,
  0x301,
  0x3298,
  0x1228,
  0x1a48,
  0x305,
  0x100e,
  0xe30,
  0x1a60,
  0xe18,
  0x106a,
  0x309,
  0x2828
]
def labelsBlock18 : Array Nat := #[
  0x2228,
  0x30d,
  0x311,
  0x401032,
  0x421046,
  0x315,
  0xc28,
  0x1608,
  0x920,
  0x31d,
  0x321,
  0x325,
  0x329,
  0x1022,
  0x904,
  0x1824
]
def labelsBlock19 : Array Nat := #[
  0x1348,
  0x1026,
  0x1066,
  0x2180,
  0x1344,
  0x103e,
  0x1124,
  0x32d,
  0x2284,
  0x900,
  0x2100,
  0x1a20,
  0x1904,
  0x2144,
  0x3104,
  0x1308
]
def labelsBlock20 : Array Nat := #[
  0x2308,
  0x1304,
  0x331,
  0x1024,
  0x2024,
  0x104e,
  0x339,
  0x106e,
  0x60c,
  0x718,
  0x33d,
  0x341,
  0x1056,
  0x345,
  0x3144,
  0x349
]
def labelsBlock21 : Array Nat := #[
  0x1052,
  0x50c,
  0x34d,
  0x351,
  0x355,
  0x359,
  0xd04,
  0x35d,
  0x361,
  0x105a,
  0x365,
  0x2388,
  0x369,
  0x36d,
  0x510056,
  0x371
]
def labelsBlock22 : Array Nat := #[
  0x375,
  0x379,
  0x1076,
  0x37d,
  0x510052,
  0x381,
  0x385,
  0x389,
  0x38d,
  0x51005a,
  0x720056,
  0x391,
  0x102e,
  0x1072,
  0x914,
  0xc24
]
def labelsBlock23 : Array Nat := #[
  0x2884,
  0x1960,
  0x29a0,
  0x51004e,
  0x395,
  0x399,
  0x39d,
  0x3a1,
  0x520052,
  0x3a5,
  0x3a9,
  0x3ad,
  0x3b1,
  0x3b5,
  0x3b9,
  0x72004e
]
def labelsBlock24 : Array Nat := #[
  0x730052,
  0x31c0,
  0x53004e,
  0x3bd,
  0x530056,
  0x3c1,
  0x3c5,
  0x3c9,
  0x3cd,
  0x3d1,
  0x3d5,
  0x52006e,
  0x3d9,
  0x3dd,
  0x521052,
  0xa18
]
def labelsBlock25 : Array Nat := #[
  0x3e1,
  0x3e5,
  0x3e9,
  0x73006e,
  0x3ed,
  0x731052,
  0x54006e,
  0x531056,
  0x3f1,
  0x3f5,
  0x3f9,
  0x3fd,
  0x401,
  0x62106e,
  0x405,
  0x43106e
]
def labelsBlock26 : Array Nat := #[
  0x409,
  0x54206e,
  0x53104e,
  0x40d,
  0x411,
  0x102a,
  0x415,
  0x419,
  0x41d,
  0x421,
  0x148110052,
  0x425,
  0x429,
  0x42d,
  0x148510052,
  0x431
]
def labelsBlock27 : Array Nat := #[
  0x435,
  0x439,
  0x14c510056,
  0x43d,
  0x441,
  0x445,
  0x449,
  0x149110052,
  0x44d,
  0x451,
  0x455,
  0x459,
  0x45d,
  0x461,
  0x62006e,
  0x61004e
]
def labelsBlock28 : Array Nat := #[
  0x189110052,
  0x465,
  0x101e,
  0x510076,
  0x1cd110052,
  0x14d110056,
  0x469,
  0x105e,
  0x46d,
  0x471,
  0x475,
  0x479,
  0x64006e,
  0x63004e,
  0x18d110056,
  0x47d
]
def labelsBlock29 : Array Nat := #[
  0x103a,
  0x481,
  0x543076,
  0x485,
  0x489,
  0x48d,
  0x52106e,
  0x1062,
  0x620052,
  0x2638,
  0x148520052,
  0x491,
  0x495,
  0x499,
  0x501056,
  0x520072
]
def labelsBlock30 : Array Nat := #[
  0x49d,
  0x150520052,
  0x4a1,
  0x530076,
  0x4a5,
  0x4a9,
  0x72006e,
  0x701056,
  0x1d0520052,
  0x4ad,
  0x541072,
  0x4b1,
  0x4b5,
  0x541076,
  0x4b9,
  0x4bd
]
def labelsBlock31 : Array Nat := #[
  0x4c1,
  0x4c5,
  0x4c9,
  0x602056,
  0x2824,
  0x14c51004e,
  0x4cd,
  0x4d1,
  0x14d11004e,
  0x4d5,
  0x4d9,
  0x4dd,
  0x64206e,
  0x18d11004e,
  0x4e1,
  0x630056
]
def labelsBlock32 : Array Nat := #[
  0x50306e,
  0x610056,
  0x145330052,
  0x61005a,
  0x540072,
  0x521072,
  0x540076,
  0x4e5,
  0x531076,
  0x14c530056,
  0x4e9,
  0x4ed,
  0x4f1,
  0x4f5,
  0x501052,
  0x4f9
]
def labelsBlock33 : Array Nat := #[
  0x150530056,
  0x4fd,
  0x50105a,
  0x74006e,
  0x1d0530056,
  0x501,
  0x70105a,
  0x701052,
  0x505,
  0x14c53004e,
  0x509,
  0x50d,
  0x542072,
  0x502052,
  0x15053004e,
  0x511
]
def labelsBlock34 : Array Nat := #[
  0x74206e,
  0x1d053004e,
  0x515,
  0x702052,
  0x150121052,
  0x519,
  0x71004e,
  0x710056,
  0x1d0121052,
  0x51d,
  0x15152006e,
  0x521,
  0x19152006e,
  0x525,
  0x1042,
  0x63104e
]
def labelsBlock35 : Array Nat := #[
  0x631056,
  0x50204e,
  0x601056,
  0x141331052,
  0x60105a,
  0x529,
  0x150131056,
  0x52d,
  0x531,
  0x2658,
  0x73004e,
  0x1d0131056,
  0x535,
  0x71005a,
  0x710052,
  0x539
]
def labelsBlock36 : Array Nat := #[
  0x15094006e,
  0x53d,
  0x541,
  0x512052,
  0x15494006e,
  0x545,
  0x1d494006e,
  0x549,
  0x104a,
  0x73104e,
  0x712052,
  0x502056,
  0x60104e,
  0x602052,
  0x52004e,
  0x520056
]
def labelsBlock37 : Array Nat := #[
  0x530052,
  0x15013104e,
  0x54d,
  0x551,
  0x1d013104e,
  0x555,
  0x720052,
  0x730056,
  0x15414206e,
  0x559,
  0x1d414206e,
  0x55d,
  0x721052,
  0x731056,
  0xc1c,
  0x184c
]
def labelsBlock38 : Array Nat := #[
  0x52148110052,
  0x288c,
  0x561,
  0x80c,
  0x565,
  0x569,
  0x56d,
  0x571,
  0x575,
  0x579,
  0x57d,
  0x581,
  0x585,
  0x704,
  0x589,
  0x1920
]
def labelsBlock39 : Array Nat := #[
  0x18c510056,
  0x2108,
  0x58d,
  0x591,
  0x1c4910052,
  0x595,
  0x599,
  0x15162006e,
  0x14d21004e,
  0x59d,
  0x1d0910052,
  0x1c40,
  0x1c10,
  0x14964006e,
  0x14523004e,
  0xe20
]
def labelsBlock40 : Array Nat := #[
  0x1504,
  0x2a20,
  0x5a1,
  0x5a5,
  0x5a9,
  0x5ad,
  0x5b1,
  0x2920,
  0x18c51004e,
  0xd20,
  0x5b5,
  0x5b9,
  0x5bd,
  0x15172006e,
  0x14d301056,
  0x150920072
]
def labelsBlock41 : Array Nat := #[
  0x5c1,
  0x14c131056,
  0x5c5,
  0x2a08,
  0x5c9,
  0x5cd,
  0x5d1,
  0x5d5,
  0x5d9,
  0x2a80,
  0x1c8520052,
  0x1640,
  0x1610,
  0x14164206e,
  0x145120052,
  0x145230056
]
def labelsBlock42 : Array Nat := #[
  0x5dd,
  0x1d094006e,
  0x5e1,
  0x1cc53004e,
  0x2380,
  0x5e5,
  0x14974006e,
  0x14513004e,
  0x149301052,
  0x150b4006e,
  0x5e9,
  0x1cc530056,
  0x14174206e,
  0x145130056,
  0x145302052,
  0x14d31004e
]
def labelsBlock43 : Array Nat := #[
  0x14d310056,
  0x141121052,
  0x14123104e,
  0x141231056,
  0x5ed,
  0x14533004e,
  0x14954006e,
  0x149310052,
  0x14c73004e,
  0x5f1,
  0x1cc131056,
  0x141131056,
  0x14133104e,
  0x141312052,
  0x14154206e,
  0x145330056
]
def labelsBlock44 : Array Nat := #[
  0x145320052,
  0x14113104e,
  0x141331056,
  0x141321052,
  0x280c,
  0x1320,
  0x2320,
  0xc0c,
  0x2224,
  0x908,
  0x3244,
  0x2c14,
  0x1510,
  0xa00,
  0x2028,
  0x2904
]
def labelsBlock45 : Array Nat := #[
  0xb20,
  0x2c20,
  0x2c10,
  0x3280,
  0x2304,
  0xb08,
  0x200c
]
def labelsGet (i : Nat) : Nat :=
  if i < 368 then
    if i < 176 then
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
    else
      if i < 272 then
        if i < 224 then
          if i < 192 then
            labelsBlock11.getD (i-176) 3
          else
            if i < 208 then
              labelsBlock12.getD (i-192) 3
            else
              labelsBlock13.getD (i-208) 3
        else
          if i < 240 then
            labelsBlock14.getD (i-224) 3
          else
            if i < 256 then
              labelsBlock15.getD (i-240) 3
            else
              labelsBlock16.getD (i-256) 3
      else
        if i < 320 then
          if i < 288 then
            labelsBlock17.getD (i-272) 3
          else
            if i < 304 then
              labelsBlock18.getD (i-288) 3
            else
              labelsBlock19.getD (i-304) 3
        else
          if i < 336 then
            labelsBlock20.getD (i-320) 3
          else
            if i < 352 then
              labelsBlock21.getD (i-336) 3
            else
              labelsBlock22.getD (i-352) 3
  else
    if i < 544 then
      if i < 448 then
        if i < 400 then
          if i < 384 then
            labelsBlock23.getD (i-368) 3
          else
            labelsBlock24.getD (i-384) 3
        else
          if i < 416 then
            labelsBlock25.getD (i-400) 3
          else
            if i < 432 then
              labelsBlock26.getD (i-416) 3
            else
              labelsBlock27.getD (i-432) 3
      else
        if i < 496 then
          if i < 464 then
            labelsBlock28.getD (i-448) 3
          else
            if i < 480 then
              labelsBlock29.getD (i-464) 3
            else
              labelsBlock30.getD (i-480) 3
        else
          if i < 512 then
            labelsBlock31.getD (i-496) 3
          else
            if i < 528 then
              labelsBlock32.getD (i-512) 3
            else
              labelsBlock33.getD (i-528) 3
    else
      if i < 640 then
        if i < 592 then
          if i < 560 then
            labelsBlock34.getD (i-544) 3
          else
            if i < 576 then
              labelsBlock35.getD (i-560) 3
            else
              labelsBlock36.getD (i-576) 3
        else
          if i < 608 then
            labelsBlock37.getD (i-592) 3
          else
            if i < 624 then
              labelsBlock38.getD (i-608) 3
            else
              labelsBlock39.getD (i-624) 3
      else
        if i < 688 then
          if i < 656 then
            labelsBlock40.getD (i-640) 3
          else
            if i < 672 then
              labelsBlock41.getD (i-656) 3
            else
              labelsBlock42.getD (i-672) 3
        else
          if i < 704 then
            labelsBlock43.getD (i-688) 3
          else
            if i < 720 then
              labelsBlock44.getD (i-704) 3
            else
              labelsBlock45.getD (i-720) 3
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x1010101010101010,⟨4,by decide⟩,0x1010100010000000,[ew0,ew1,ew2],3,lh 2 [0,1,2,3] [0xd900]⟩,
  ⟨0x50505050,⟨4,by decide⟩,0x50404000,[ew3,ew4,ew5],3,fun _ => 3⟩,
  ⟨0x55000000550000,⟨16,by decide⟩,0x54000000400000,[ew6,ew7,ew8],3,fun _ => 3⟩,
  ⟨0x55550000,⟨16,by decide⟩,0x54400000,[ew9,ew5,ew10],3,fun _ => 3⟩,
  ⟨0x30003000300030,⟨4,by decide⟩,0x30002000200000,[ew11,ew12,ew13],3,fun _ => 3⟩,
  ⟨0x303000003030,⟨4,by decide⟩,0x302000002000,[ew14,ew15,ew16],3,fun _ => 3⟩,
  ⟨0x30303030,⟨4,by decide⟩,0x30202000,[ew17,ew18,ew19],3,fun _ => 3⟩,
  ⟨0x33000000330000,⟨16,by decide⟩,0x32000000200000,[ew20,ew12,ew21],3,fun _ => 3⟩,
  ⟨0xf0000000f0000,⟨16,by decide⟩,0xe000000080000,[ew22,ew23,ew24],3,fun _ => 3⟩,
  ⟨0xf0f,⟨0,by decide⟩,0xe08,[ew25,ew26,ew27],3,fun _ => 3⟩,
  ⟨0xf000f0,⟨4,by decide⟩,0xe00080,[ew28,ew29,ew30],3,fun _ => 3⟩,
  ⟨0xa500a500a500a5,⟨0,by decide⟩,0xa400a000a00080,[ew31,ew32,ew33,ew34],5,lh 3 [4,5,6,7,8] [0x810208610208]⟩,
  ⟨0x4444111144441111,⟨0,by decide⟩,0x4444100044400000,[ew35,ew36,ew37,ew38],5,fun _ => 3⟩,
  ⟨0x333300003333,⟨0,by decide⟩,0x322200002200,[ew39,ew40,ew41,ew42],4,lh 3 [9,1,10,11,12] [0x880240680240]⟩,
  ⟨0x4444444411111111,⟨0,by decide⟩,0x4444440010000000,[ew43,ew44,ew45,ew46],4,fun _ => 3⟩,
  ⟨0xc0c0c0c03030303,⟨0,by decide⟩,0xc0c0c0802000200,[ew47,ew48,ew49,ew50],4,fun _ => 3⟩
]
def viewsBlock1 : Array View := #[
  ⟨0xcc00cc00330033,⟨0,by decide⟩,0xcc008800200000,[ew51,ew52,ew53,ew54],4,fun _ => 3⟩,
  ⟨0x5005500550055005,⟨0,by decide⟩,0x5004500050004000,[ew55,ew56,ew57,ew58],5,fun _ => 3⟩,
  ⟨0x3300330000330033,⟨0,by decide⟩,0x3200320000200000,[ew59,ew60,ew61,ew62],4,fun _ => 3⟩,
  ⟨0x3030303030303030,⟨4,by decide⟩,0x3030302030202000,[ew63,ew64,ew65,ew66],6,lh 3 [13,0,1,10,14] [0x8d2000249000]⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xf0e0e080,[ew67,ew68,ew69,ew70],6,fun _ => 3⟩,
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xfe000000e80000,[ew71,ew72,ew73,ew74],6,fun _ => 3⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xfee80000,[ew75,ew76,ew70,ew77],6,fun _ => 3⟩,
  ⟨0x1111444422228888,⟨3,by decide⟩,0x101004400020000,[ew78,ew79,ew80,ew81],5,lh 3 [15,16,17,18,19] [0x8d2000249000]⟩,
  ⟨0xc00c3003c00c3003,⟨0,by decide⟩,0xc00c3002c0082000,[ew82,ew83,ew84,ew85],6,fun _ => 3⟩,
  ⟨0x50505050a0a0a0a,⟨1,by decide⟩,0x40404000a080a08,[ew86,ew87,ew88,ew89],4,fun _ => 3⟩,
  ⟨0x1144114411441144,⟨2,by decide⟩,0x1044100010400000,[ew90,ew91,ew92,ew93],4,lh 3 [9,7,20,21,22] [0x8c0480240240]⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5454540054404400,[ew94,ew95,ew96,ew97,ew98],7,lh 3 [11,23,5,9,24,25] [0x2249000000000000,0x163649292]⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0e0e0a0e080e08,[ew99,ew100,ew101,ew102,ew103],6,lh 3 [26,27,5,7,28,29,30] [0x4406c06c0440440,0x1a8120088]⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xfeaa0000ee88,[ew104,ew105,ew106,ew107,ew108],6,fun _ => 3⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfefefeaafee8ee88,[ew109,ew110,ew111,ew112,ew113,ew114],10,lh 4 [5,29,26,31,32,33,34,35,36] [0x0,0x6125333344443333,0x121012101210121,0x8121712141214121]⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    viewsBlock1[(i-16)]?
def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew0,ew1,ew2],lh 3 [1,13,0,11,32,2] [0x483112144265808,0x1522c946b71b]⟩,
  ⟨11,5,[ew31,ew32,ew33,ew34],lh 6 [6,39,5,47,7,55,40,4,48,37,38,41,42,43,44,45,46,49,50,51,52,53,54,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73] [0x2c604a247007,0x3c608638704d306,0xd34880824480d0,0x5c7156546104506,0xc1686159607107,0x7400c37000806c1,0x1048011457c109e,0x8c1101880140840,0x166942102903145,0xa031039c2]⟩,
  ⟨11,4,[ew115,ew32,ew31,ew33,ew34],lh 4 [5,4,6,7,48,47,39,40,74,75,76,77,38,55] [0x521cb3a390807162,0x541141041322d020,0x300]⟩,
  ⟨11,4,[ew32,ew31,ew116,ew33,ew34],lh 4 [5,7,47,55,6,4,38,39,40,78,79,80,81] [0x551313020244876,0x21c1b0a093131202,0x100]⟩,
  ⟨11,4,[ew11,ew32,ew31,ew33,ew34],lh 4 [5,47,7,6,55,4,39,40,43] [0x1873424210105563,0x1424210102334030,0x200]⟩,
  ⟨11,4,[ew117,ew32,ew31,ew33,ew34],lh 4 [55,39,4,5,7,47,48,6,40,43] [0x1912404035358271,0x20623621040153,0x403]⟩,
  ⟨11,4,[ew32,ew118,ew31,ew33,ew34],lh 4 [55,39,40,5,4,6,82,83,48,47,84,85,46,7] [0x1050153121241761,0x40223cb0a09382,0xd03]⟩,
  ⟨11,4,[ew32,ew31,ew33,ew119,ew34],lh 4 [55,39,6,7,48,40,5,38,86,87,46,47,88,89] [0x1020911812212117,0xc303066030455b4a,0xd0]⟩,
  ⟨11,4,[ew120,ew32,ew31,ew33,ew34],lh 4 [55,39,6,5,7,40,48,47,38,51] [0x2118040473551212,0x40696310201231,0x403]⟩,
  ⟨11,4,[ew121,ew32,ew31,ew33,ew34],lh 4 [7,55,47,39,40,6,48,5,4,51] [0x4348010172645353,0x2101092401013252,0x10]⟩,
  ⟨11,4,[ew32,ew122,ew31,ew33,ew34],lh 4 [47,5,39,40,7,92,90,91,38,4,93,94,55,54] [0x5542201032382762,0x34d0101c4b1a093,0x411]⟩,
  ⟨11,4,[ew32,ew31,ew33,ew34,ew123],lh 4 [5,4,47,39,55,6,7,95,96,97,54,40,98,99] [0x9338355402027131,0xc2002b141a1021,0x66d]⟩,
  ⟨11,4,[ew28,ew32,ew31,ew33,ew34],lh 4 [6,39,5,47,7,4,40,55,58] [0x110743232661010,0x3854523510011001,0x422]⟩,
  ⟨11,4,[ew124,ew32,ew31,ew33,ew34],lh 4 [39,6,40,55,47,5,4,7,58] [0x2021735454621010,0x3832254203130110,0x435]⟩,
  ⟨11,4,[ew125,ew32,ew31,ew33,ew34],lh 4 [7,100,55,47,39,40,5,6,4,101] [0x1418020266151574,0x3102031350202439,0x320]⟩,
  ⟨11,4,[ew32,ew31,ew33,ew126,ew34],lh 4 [7,100,55,4,6,39,40,47,101,5] [0x1160202559481314,0x2020277102031136,0x20]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨11,4,[ew127,ew32,ew31,ew33,ew34],lh 4 [7,100,47,55,40,39,6,5,102,103,4,63] [0x1a16908072414155,0x2103021240303b62,0x230]⟩,
  ⟨11,4,[ew128,ew32,ew31,ew33,ew34],lh 4 [48,7,5,100,55,39,47,6,104,105,63,40] [0x3030918166030375,0x40140b2021414a25,0x122]⟩,
  ⟨11,4,[ew129,ew32,ew31,ew33,ew34],lh 4 [106,48,5,47,39,7,6,107,55] [0x101552323010164,0x3100102104872323,0x322]⟩,
  ⟨11,4,[ew32,ew31,ew33,ew34,ew130],lh 4 [106,6,48,5,47,7,107,39,55] [0x3207151631141201,0x3344334200220020,0x854]⟩,
  ⟨11,4,[ew131,ew32,ew31,ew33,ew34],lh 4 [106,5,6,48,47,39,100,7,108,109,55,110] [0x2302779181606055,0x430030130b2a1224,0x411]⟩,
  ⟨11,4,[ew132,ew32,ew31,ew33,ew34],lh 4 [4,5,39,106,47,48,7,6,111,112,55,110] [0x3020a69181030372,0x450050150b622412,0x411]⟩,
  ⟨11,4,[ew32,ew31,ew133,ew33,ew34],lh 4 [4,39,6,113,55,5,48,7,114,47] [0x1424122112212010,0x7455433603300330,0x948]⟩,
  ⟨11,4,[ew32,ew31,ew33,ew34,ew134],lh 4 [113,40,7,39,6,5,114,47,55] [0x3443242334431010,0x5256100112021001,0x827]⟩,
  ⟨11,4,[ew135,ew32,ew31,ew33,ew34],lh 4 [48,40,39,6,55,47,7,113,115,116,5,71] [0x1010665501019282,0x770100124342332,0xba4]⟩,
  ⟨11,4,[ew136,ew32,ew31,ew33,ew34],lh 4 [48,7,39,47,40,4,5,6,117,118,55,113,71] [0x4040a16650509282,0x1b0300417122373,0xc13]⟩,
  ⟨11,3,[ew32,ew31,ew137,ew34],lh 3 [4,5,6,48,47,7,46,55] [0x4603058a9728c430,0x149]⟩,
  ⟨11,3,[ew138,ew32,ew31,ew34],lh 3 [4,5,6,48,47,7,40,55] [0x3a97430a4c21844c,0xc0]⟩,
  ⟨11,3,[ew32,ew31,ew33,ew139],lh 3 [4,5,6,48,47,7,38,55] [0x4603058a9728c430,0x149]⟩,
  ⟨11,3,[ew140,ew32,ew31,ew33],lh 3 [4,5,6,48,7,47,38,55] [0x28d43630d0c3517,0xb]⟩,
  ⟨11,3,[ew32,ew31,ew141,ew34],lh 4 [4,5,7,47,38,55,40,6,58] [0x130252517136044,0x21138002]⟩,
  ⟨11,3,[ew142,ew32,ew31,ew34],lh 3 [5,6,47,7,48,4,38,55] [0x464f336403b50401,0x11f]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨11,3,[ew32,ew31,ew143,ew33],lh 4 [5,47,48,38,55,7,6,4,40] [0x7742010166548233,0x5011020]⟩,
  ⟨11,3,[ew144,ew32,ew31,ew33],lh 3 [4,5,6,47,7,55,38,48] [0x28b436661e28aa2,0xb]⟩,
  ⟨11,3,[ew31,ew145,ew33,ew34],lh 3 [55,40,39,4,38,5,6,7] [0x4305aa0c132144b,0x1c5]⟩,
  ⟨11,3,[ew146,ew31,ew33,ew34],lh 4 [55,40,39,5,6,38,48,4,7] [0x1361204024321215,0x80300701]⟩,
  ⟨11,3,[ew32,ew31,ew33,ew147],lh 3 [55,40,39,5,4,6,46,7] [0x1012f142855a28c,0x1c3]⟩,
  ⟨11,3,[ew148,ew32,ew31,ew33],lh 4 [55,39,40,5,6,46,4,7,38] [0x2128073060020140,0x23551431]⟩,
  ⟨11,3,[ew149,ew31,ew33,ew34],lh 4 [55,39,40,6,46,48,4,7,38,5] [0x6544103019312218,0x70700605]⟩,
  ⟨11,3,[ew150,ew31,ew33,ew34],lh 3 [55,40,39,5,6,46,7,38] [0x1812ed1024e2e51,0x183]⟩,
  ⟨11,3,[ew32,ew31,ew33,ew151],lh 4 [55,40,39,6,46,38,48,4,7,5] [0x1644203023321215,0x90800701]⟩,
  ⟨11,3,[ew152,ew32,ew31,ew33],lh 4 [55,39,6,5,4,46,40,7,38] [0x2118037060040210,0x43551231]⟩,
  ⟨11,3,[ew31,ew153,ew33,ew34],lh 4 [7,47,40,39,5,38,46,51,54,55] [0x3141208017163225,0x4010903]⟩,
  ⟨11,3,[ew154,ew31,ew33,ew34],lh 4 [47,7,55,40,39,54,38,5,46,51] [0x908121240703436,0x12102155]⟩,
  ⟨11,3,[ew32,ew31,ew155,ew34],lh 3 [5,47,40,7,39,92,54,38] [0x14f6208b5c041517,0xc0]⟩,
  ⟨11,3,[ew156,ew32,ew31,ew34],lh 4 [5,47,7,40,55,92,54,38,39] [0x3837200101101001,0x42665524]⟩,
  ⟨11,3,[ew157,ew31,ew33,ew34],lh 3 [6,39,4,47,5,54,55] [0x3c9551a201201048,0xe4]⟩,
  ⟨11,3,[ew158,ew31,ew33,ew34],lh 3 [6,39,4,5,47,92,55] [0x4c954e2201201048,0x15b]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨11,3,[ew32,ew31,ew159,ew34],lh 3 [40,6,39,5,47,4,7] [0x41680e044a44a081,0x19b]⟩,
  ⟨11,3,[ew160,ew32,ew31,ew34],lh 4 [6,39,5,4,40,7,47,54,51] [0x110622544321010,0x83371001]⟩,
  ⟨11,3,[ew125,ew31,ew126,ew34],lh 4 [100,55,40,39,7,63,6,92,4,58] [0x1030087161530202,0x414109]⟩,
  ⟨11,3,[ew32,ew31,ew33,ew161],lh 3 [47,7,100,55,6,95,63,40] [0x4590872cbc20554,0x19]⟩,
  ⟨11,3,[ew32,ew31,ew33,ew162],lh 3 [47,7,100,55,6,39,63,40] [0x4590872cbc20554,0x19]⟩,
  ⟨11,3,[ew32,ew31,ew33,ew163],lh 4 [48,7,100,55,63,40,47,39,6] [0x5005131344872020,0x66132001]⟩,
  ⟨11,3,[ew32,ew164,ew31,ew33],lh 3 [5,48,47,55,7,100] [0x82859082a698e3,0x81]⟩,
  ⟨11,3,[ew129,ew31,ew33,ew130],lh 3 [106,48,5,47,7,110] [0x24c804222c4d3041,0x3]⟩,
  ⟨11,3,[ew32,ew31,ew165,ew34],lh 3 [6,106,48,47,5,39,55,110] [0x344a311e06b43088,0xe4]⟩,
  ⟨11,3,[ew32,ew31,ew166,ew34],lh 3 [6,39,106,48,5,47] [0x569351a201201048,0x164]⟩,
  ⟨11,3,[ew32,ew31,ew167,ew34],lh 3 [4,39,6,106,48,47,5] [0x5804603291291408,0x176]⟩,
  ⟨11,3,[ew168,ew32,ew31,ew34],lh 4 [4,39,5,48,47,6,106,7,110] [0x6010422420305121,0x30031871]⟩,
  ⟨11,3,[ew32,ew31,ew133,ew134],lh 3 [113,39,6,55,4,40,71] [0x3a058042d3291408,0x6]⟩,
  ⟨11,3,[ew169,ew31,ew33,ew34],lh 3 [7,113,40,55,47,39,6,71] [0x340844a0c3935451,0x38]⟩,
  ⟨11,3,[ew170,ew31,ew33,ew34],lh 4 [47,113,40,6,7,39,55,5,71] [0x102443650302121,0x8702112]⟩,
  ⟨11,3,[ew171,ew31,ew33,ew34],lh 3 [5,48,47,7,40,39,55,113] [0x22f940879d082861,0x80]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨11,3,[ew172,ew31,ew33,ew34],lh 4 [48,47,7,40,5,55,6,113,71] [0x1003252544613030,0x18210270]⟩,
  ⟨19,6,[ew63,ew64,ew65,ew66],lh 5 [13,0,1,10,119,124,11,123,2,12,32,120,127,121,47,55,122,125,126,128,129,130] [0x22c4282dab20c42,0x895c520c0038da3,0x2142148dc321400,0x615e520c2190de3,0x3a8009a90838800,0xa08c23a82148902,0x4a0c6628c638821,0x62021480c0a8020]⟩,
  ⟨19,5,[ew63,ew64,ew173,ew65,ew66],lh 5 [13,0,119,11,2,120,121,123,47,55,10,1,12,127,131,132,133,134,135,136,137,138] [0x28947318a228842,0x1000e420a001c4a,0x1042f4a4a109508,0x3000212cc259529,0x30426210e004084,0x6000618ce10c463,0x6842c2126004884,0x20c6d18ea10d063,0x40840300020]⟩,
  ⟨19,5,[ew63,ew64,ew65,ew174,ew66],lh 5 [0,1,119,11,32,124,47,12,121,55,10,123,13,127,131,139,140,135,141,142,143,144] [0x2a0a2085c841421,0x28947318a228842,0x1000f4a4a001c4a,0x218848102609525,0x22c848902b084e1,0x80011848000641,0x30c62130c261063,0x68c66000e31cc00,0xd002a31d000]⟩,
  ⟨19,5,[ew63,ew64,ew65,ew66,ew175],lh 5 [13,1,119,2,10,32,55,127,121,47,123,12,0,132,139,124,145,137,146,147,143,148] [0x22082085a841021,0x22482001c949000,0x208873188220842,0x2800518c2001c4f,0x9821804a628461,0xa821884aa294e5,0x18009806619645,0x2c00a006b18ce3,0x2130c260ea3]⟩,
  ⟨19,5,[ew63,ew64,ew65,ew176,ew66],lh 5 [0,10,124,123,32,2,11,55,12,119,120,1,13,127,133,140,135,149,150,151,152,153] [0x8c2a2114e50481,0xa0222944f104a1,0xc4224885010521,0x11c410002708800,0x225682948320c63,0x18012318800206b,0x298c31b0a9610c6,0x69ce50010634c00,0xd002a73d000]⟩,
  ⟨19,5,[ew63,ew64,ew65,ew66,ew177],lh 5 [13,10,1,124,123,11,47,2,127,119,120,12,0,134,145,137,154,150,32,155,152,156] [0x902a1094d50442,0x98230006618400,0x1a0612842e08ca5,0x1c0614842f08d23,0x11c440022738800,0x124482944411084,0x1400980e52a092,0x2c00a00cb31d07,0x4230a961aa6]⟩,
  ⟨19,5,[ew63,ew64,ew65,ew66,ew178],lh 5 [1,10,13,0,12,120,121,124,32,127,119,123,142,147,143,157,151,155,152,158,2,11] [0x9825000a628400,0x9027108ec38442,0x3a4e118c2d09c63,0x2bca15042e09545,0x10081091040042,0x4250018c1102063,0x34cc05801201966,0x1284918c4411084,0x42546a1a494]⟩,
  ⟨19,4,[ew64,ew173,ew65,ew174,ew66],lh 4 [0,11,47,124,1,121,123,120,10,13,159,12] [0x3b1010757652a244,0x101991010883623,0x101]⟩,
  ⟨19,4,[ew64,ew173,ew65,ew66,ew175],lh 4 [13,2,10,55,1,121,123,120,0,160,127,124] [0x1075765393101044,0x11001b226322a20,0x8810]⟩,
  ⟨19,4,[ew63,ew173,ew65,ew176,ew66],lh 4 [0,2,55,11,120,10,119,32,1,13,159,121,12] [0x1c2020b44641a155,0x303993030887617,0x202]⟩,
  ⟨19,4,[ew63,ew173,ew65,ew66,ew177],lh 4 [13,1,47,11,120,119,2,0,10,160,121,127,32] [0x60a4454393202081,0x26003c115311b10,0x7720]⟩,
  ⟨19,4,[ew63,ew64,ew65,ew179,ew66],lh 4 [0,2,11,32,124,47,10,1,13,120,55,127,161] [0x1540a06651414393,0xb02028820207713,0xc]⟩,
  ⟨19,4,[ew180,ew63,ew64,ew65,ew66],lh 4 [13,0,11,124,32,120,10,121,1,2,55] [0x5421219088746653,0x21704031a1503034,0x100221]⟩,
  ⟨19,4,[ew63,ew64,ew65,ew66,ew181],lh 4 [13,1,10,11,55,2,0,120,47,124,32,12,162] [0x5092422320802171,0xc00b5003a1311410,0x66]⟩,
  ⟨19,4,[ew182,ew63,ew64,ew65,ew66],lh 4 [13,1,0,10,2,120,121,124,32,11,47] [0x5192404081617353,0x121040523230a031,0x200462]⟩
]
def nodesBlock5 : Array Node := #[
  ⟨19,4,[ew64,ew65,ew174,ew66,ew175],lh 4 [1,32,10,55,124,13,47,12,0,163,127] [0x1001100102100110,0x27322a4647639355,0x8842]⟩,
  ⟨19,4,[ew63,ew64,ew174,ew176,ew66],lh 4 [0,124,11,32,55,2,10,119,1,13,159,47,123] [0x5c1040b1176613a3,0x202995720208853,0x404]⟩,
  ⟨19,4,[ew183,ew63,ew64,ew65,ew66],lh 4 [0,1,11,124,2,47,120,10,13,32,55] [0x6102028854917736,0x10154130a0543431,0x20220]⟩,
  ⟨19,4,[ew63,ew64,ew174,ew66,ew178],lh 4 [13,1,0,124,121,119,47,32,10,163,127,2,11] [0x7063353292803141,0x5200a4116721210,0xc2b0]⟩,
  ⟨19,4,[ew63,ew64,ew65,ew66,ew184],lh 4 [13,1,0,10,124,32,121,120,123,164,55,2,11] [0x5073423230403161,0xb0200a9118521210,0xc2]⟩,
  ⟨19,4,[ew185,ew63,ew64,ew65,ew66],lh 4 [13,1,10,124,32,11,47,0,2,121] [0x9177806041413232,0x1410403225203021,0x600551]⟩,
  ⟨19,4,[ew63,ew64,ew65,ew175,ew177],lh 4 [13,1,10,11,47,119,55,2,0,160,124,123,32] [0x706225a220402191,0x40067003c1311b10,0x8835]⟩,
  ⟨19,4,[ew186,ew63,ew64,ew65,ew66],lh 4 [13,10,2,11,55,120,1,0,32,124,47] [0x5177430202661915,0x382020411310a018,0x200334]⟩,
  ⟨19,4,[ew63,ew64,ew65,ew175,ew178],lh 4 [13,1,0,10,121,119,55,32,163,124,12,2,11] [0x7063359230803141,0xb0200a4116721210,0xc225]⟩,
  ⟨19,4,[ew187,ew63,ew64,ew65,ew66],lh 4 [0,1,10,124,32,2,13,55,11,121] [0x9180706614142323,0x1014513020253221,0x70540]⟩,
  ⟨19,4,[ew188,ew63,ew64,ew65,ew66],lh 4 [0,10,2,11,32,47,55,121,1,13,124] [0x71060699258847a1,0x3024256010125114,0x30330]⟩,
  ⟨19,4,[ew63,ew65,ew176,ew66,ew177],lh 4 [10,1,124,2,11,32,13,12,0,165,127] [0x2005200401210320,0x17411a5337349466,0x8851]⟩,
  ⟨19,4,[ew63,ew64,ew176,ew66,ew178],lh 4 [13,10,0,2,32,120,124,123,1,165,127,11] [0x5113621210601451,0x7200a3437429280,0xb230]⟩,
  ⟨19,4,[ew63,ew64,ew65,ew66,ew189],lh 4 [13,0,1,10,124,11,120,119,166,2,121,47,55] [0x8337413130403262,0xb01005a251212090,0xc1]⟩,
  ⟨19,4,[ew190,ew63,ew64,ew65,ew66],lh 3 [13,1,10,124,2,32,0,120] [0x611e76820a6969a,0x402526910349a]⟩,
  ⟨19,4,[ew191,ew63,ew64,ew65,ew66],lh 4 [13,1,11,47,55,124,10,121,0,2,32] [0x71882403031a1766,0x1410905242305051,0x900221]⟩
]
def nodesBlock6 : Array Node := #[
  ⟨19,4,[ew63,ew64,ew65,ew177,ew178],lh 4 [13,0,1,10,11,120,124,123,165,32,12,2] [0x5334613130603252,0xb0100a4227912080,0x4117]⟩,
  ⟨19,4,[ew192,ew63,ew64,ew65,ew66],lh 3 [0,1,10,124,11,32,13,120] [0x3691e6083634d4d3,0x824041b4b082]⟩,
  ⟨19,4,[ew193,ew63,ew64,ew65,ew66],lh 4 [13,0,1,55,121,47,10,32,2,11,120] [0xa219130805242466,0x2120703131505042,0x100371]⟩,
  ⟨19,4,[ew194,ew63,ew64,ew65,ew66],lh 3 [13,0,10,11,120,2,1,124] [0xe1488b2c5176514,0x101b2cd14728a]⟩,
  ⟨19,3,[ew173,ew174,ew176,ew66],lh 4 [0,11,2,10,119,1,13,55,123,32] [0x6624101055943328,0x7070101]⟩,
  ⟨19,3,[ew173,ew65,ew175,ew177],lh 4 [13,1,11,2,119,0,123,32,55,47] [0x3002711421161030,0x55249008]⟩,
  ⟨19,3,[ew195,ew63,ew64,ew65],lh 3 [13,0,1,10,124,11,120,2] [0x6206b2a082a92e1,0x87]⟩,
  ⟨19,3,[ew196,ew63,ew64,ew66],lh 3 [13,0,1,10,124,11,2,120] [0x18596baa01190118,0x14a]⟩,
  ⟨19,3,[ew64,ew174,ew175,ew178],lh 4 [13,0,1,32,119,55,121,12,2,11] [0x1007622531212030,0x91148004]⟩,
  ⟨19,3,[ew197,ew63,ew65,ew66],lh 3 [13,0,1,10,11,124,120,2] [0x4a5962828c1c259a,0x40]⟩,
  ⟨19,3,[ew63,ew176,ew177,ew178],lh 3 [13,0,10,11,124,123,120,12] [0x5605207c93851420,0xc9]⟩,
  ⟨19,3,[ew198,ew64,ew65,ew66],lh 3 [13,0,1,10,124,11,120,2] [0x5a514382cc103593,0x40]⟩,
  ⟨23,5,[ew78,ew79,ew80,ew81],lh 6 [167,17,35,182,18,15,16,170,175,23,191,168,169,171,172,173,174,176,54,177,178,179,180,181,183,184,185,186,187,188,189,190,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208] [0x34704c2c4000,0x44808240404f387,0x5955040824c4152,0x6871996040c35c8,0x7417082486c70c3,0x8ca8a180a09f781,0xe6940180900140,0xa800e9a011819c1,0xc5b451acac2249,0xc021afb85]⟩,
  ⟨23,4,[ew80,ew81,ew199,ew79,ew78],lh 4 [15,16,35,167,182,17,18,209,210,211,212,170,169] [0x2002800320021007,0xb655411413411a91,0x36c]⟩,
  ⟨23,4,[ew80,ew81,ew79,ew78,ew200],lh 4 [15,16,17,182,35,18,209,191,213,214,215,216,169,170,167] [0x9008400470021006,0x2d2cb11a31131321,0x55e]⟩,
  ⟨23,4,[ew201,ew80,ew81,ew79,ew78],lh 4 [15,16,182,167,17,18,35,217,218,209,219,170,173] [0x1009554412128070,0x211213216006a003,0xcb3]⟩
]
def nodesBlock7 : Array Node := #[
  ⟨23,4,[ew202,ew80,ew81,ew79,ew78],lh 4 [15,16,182,35,17,18,167,170,209,193,173] [0x1008756421213030,0x2112124130039004,0xa45]⟩,
  ⟨23,4,[ew203,ew80,ew81,ew79,ew78],lh 4 [191,16,182,17,175,15,18,54,35,173] [0x1212640303121255,0x4241410308470303,0x900]⟩,
  ⟨23,4,[ew80,ew81,ew79,ew78,ew204],lh 4 [182,191,16,18,167,15,35,17,193,54,175] [0x16635918172050,0x1144313022003202,0xa34]⟩,
  ⟨23,4,[ew205,ew80,ew81,ew79,ew78],lh 4 [17,16,167,182,23,35,18,15,175,191,179] [0x1414860202434375,0x231131201a659050,0x200]⟩,
  ⟨23,4,[ew206,ew80,ew81,ew79,ew78],lh 4 [16,180,17,167,18,182,35,220,221,222,223,23,191,175,179] [0x1b0144a292807061,0x350050320e1dc112,0x322]⟩,
  ⟨23,4,[ew80,ew207,ew81,ew79,ew78],lh 4 [15,17,167,180,175,16,191,35,179,18,170,184,182] [0x8007600130033003,0x4c4b1212a9121255,0x241]⟩,
  ⟨23,4,[ew80,ew81,ew79,ew78,ew208],lh 4 [15,17,167,170,16,35,180,175,193,184,182] [0x5005530380016006,0x1122132a43494214,0x772]⟩,
  ⟨23,4,[ew209,ew80,ew81,ew79,ew78],lh 4 [167,191,35,182,17,180,175,15,170,16,224] [0x2373661010935252,0xa83413128721010,0x44]⟩,
  ⟨23,4,[ew210,ew80,ew81,ew79,ew78],lh 4 [17,23,35,175,191,15,167,225,226,182,227,228,170,224] [0x2151c3b0a0918272,0x6d13140123524040,0x600]⟩,
  ⟨23,4,[ew211,ew81,ew79,ew78],lh 4 [23,17,35,175,167,15,182,170,229,230,191,231,232,233,234] [0xa211292500585200,0x402e25335d5232cb,0x706360106446110,0x4131171434676030,0x47]⟩,
  ⟨23,4,[ew211,ew80,ew81,ew79,ew78],lh 5 [23,17,167,35,175,204,239,54,179,182,235,236,191,237,238,190,231] [0x711a46056050063,0x21073c02f318a5,0x8211240048041]⟩,
  ⟨23,4,[ew80,ew81,ew79,ew212,ew78],lh 4 [175,182,16,23,35,170,191,18,17,190,232] [0x1127074a46492323,0x506088102131132,0x505]⟩,
  ⟨23,4,[ew213,ew81,ew79,ew78],lh 4 [182,15,193,170,16,175,35,190,231,240,241,242,210,219] [0x7121606141100644,0x2263615113165698,0x4330504b40220a04,0x3252232c55033455,0xd3]⟩,
  ⟨23,4,[ew213,ew80,ew81,ew79,ew78],lh 4 [170,182,191,16,175,15,18,167,231,193] [0x3131040472131355,0x4040132126060928,0x22]⟩,
  ⟨23,4,[ew214,ew80,ew81,ew79,ew78],lh 4 [15,167,170,182,35,16,18,175,240,191,193] [0x4004626291535380,0x1272351314004a01,0x172]⟩,
  ⟨23,4,[ew80,ew215,ew81,ew79,ew78],lh 4 [35,15,167,191,175,170,182,17,198,16] [0x110323201100110,0x2545492854547266,0x233]⟩
]
def nodesBlock8 : Array Node := #[
  ⟨23,4,[ew80,ew81,ew79,ew216,ew78],lh 4 [15,17,170,35,175,182,241,243,244,198,16,167] [0x3003800761013003,0x42114b12425a5159,0x242]⟩,
  ⟨23,4,[ew217,ew80,ew81,ew79,ew78],lh 4 [15,35,17,170,175,182,167,245,246,242,16,201] [0x1001837362551010,0x43434b2a10019202,0x322]⟩,
  ⟨23,4,[ew218,ew80,ew81,ew79,ew78],lh 4 [15,167,170,35,191,182,17,247,248,23,249,250,201,175] [0x3003b2a266958070,0x12d25c5130034141,0x144]⟩,
  ⟨23,4,[ew219,ew80,ew81,ew79,ew78],lh 4 [175,35,23,17,182,15,16,251,252,253,254,204,191,54,167] [0x314ba09083736255,0x4020244210d1c11,0xe03]⟩,
  ⟨23,4,[ew80,ew81,ew220,ew79,ew78],lh 4 [15,17,170,167,191,175,18,16,182,204,35] [0x48860054001a0709,0x3252513132676141,0x312]⟩,
  ⟨23,4,[ew221,ew80,ew81,ew79,ew78],lh 4 [167,170,18,191,17,15,182,35,16,207] [0x956212130308675,0x121240402121303,0x41]⟩,
  ⟨23,4,[ew222,ew80,ew81,ew79,ew78],lh 4 [167,16,170,18,17,15,191,182,35,207] [0x918232340407155,0x211310413232606,0x42]⟩,
  ⟨23,3,[ew211,ew81,ew79,ew78],lh 4 [182,167,35,18,170,209,191,180,204] [0x4081012372612050,0x134103]⟩,
  ⟨23,3,[ew213,ew81,ew79,ew78],lh 4 [182,18,35,170,209,167,180,191,204] [0x3080072162554402,0x313101]⟩,
  ⟨23,3,[ew213,ew81,ew199,ew78],lh 4 [15,16,167,182,209,17,255,191,18,170] [0x1761200250024001,0x983113]⟩,
  ⟨23,3,[ew80,ew79,ew223,ew78],lh 3 [15,16,17,182,167,35,255] [0x3894851a05203c02,0xc9]⟩,
  ⟨23,3,[ew224,ew80,ew79,ew78],lh 3 [15,16,167,182,191,35,17,18] [0x2a0580264b2b1608,0xbc]⟩,
  ⟨23,3,[ew225,ew81,ew79,ew78],lh 4 [15,16,17,35,167,182,169,209,191] [0x1421300380021007,0x42665115]⟩,
  ⟨23,3,[ew226,ew81,ew79,ew78],lh 4 [15,16,17,182,35,169,209,191,170] [0x1321400420076001,0x82553113]⟩,
  ⟨23,3,[ew80,ew227,ew79,ew78],lh 4 [15,16,17,35,167,182,169,209,191] [0x1421300380021007,0x42665115]⟩,
  ⟨23,3,[ew228,ew80,ew79,ew78],lh 4 [15,16,182,17,35,169,209,191,170] [0x7003211213216010,0x83554004]⟩
]
def nodesBlock9 : Array Node := #[
  ⟨23,3,[ew229,ew81,ew79,ew78],lh 4 [15,16,182,35,167,169,209,17,191,18] [0x1421300380071006,0x49552112]⟩,
  ⟨23,3,[ew230,ew81,ew79,ew78],lh 3 [15,16,17,35,167,182,191] [0x4a4d311603c02601,0x112]⟩,
  ⟨23,3,[ew201,ew213,ew81,ew78],lh 3 [15,16,182,169,167,17,209] [0x44a804c016ca2a8]⟩,
  ⟨23,3,[ew80,ew231,ew79,ew78],lh 4 [180,16,17,167,182,23,191,175,179] [0x1321800760020510,0x32234114]⟩,
  ⟨23,3,[ew80,ew232,ew79,ew78],lh 4 [180,16,17,167,182,23,191,35,179] [0x1321800760020510,0x32234114]⟩,
  ⟨23,3,[ew80,ew81,ew233,ew78],lh 4 [180,16,17,167,182,23,191,35,179] [0x1321800760020510,0x32234114]⟩,
  ⟨23,3,[ew80,ew81,ew234,ew78],lh 4 [180,16,17,167,182,23,191,54,179] [0x1321800760020510,0x32234114]⟩,
  ⟨23,3,[ew210,ew209,ew80,ew79],lh 4 [17,182,191,35,184,256,257,180,175] [0x2083736010135141,0x202020]⟩,
  ⟨23,3,[ew235,ew81,ew79,ew78],lh 4 [23,17,191,35,175,167,15,182,170,256] [0x210348321217060,0x51159004]⟩,
  ⟨23,3,[ew236,ew81,ew79,ew78],lh 3 [23,17,35,191,15,182,167,175] [0x6a050c85e2659420,0x189]⟩,
  ⟨23,3,[ew80,ew81,ew237,ew78],lh 3 [23,17,35,191,15,182,167,175] [0x6a050c85e2659420,0x189]⟩,
  ⟨23,3,[ew80,ew81,ew238,ew78],lh 3 [23,17,35,191,15,175,167,257] [0x6e050c8562659420,0x189]⟩,
  ⟨23,3,[ew211,ew239,ew79,ew78],lh 4 [23,17,167,175,182,35,258,15,259] [0x4004021083736150,0x2112]⟩,
  ⟨23,3,[ew240,ew211,ew79,ew78],lh 4 [23,17,167,182,35,15,191,180,175] [0x4874613003021050,0x2112]⟩,
  ⟨23,3,[ew213,ew211,ew81,ew78],lh 4 [23,17,167,191,182,35,258,175,260] [0x3730602112201051,0x400483]⟩,
  ⟨23,3,[ew211,ew81,ew79,ew241],lh 3 [23,17,167,35,182,15,180,191] [0x44a8040886f9c28]⟩
]
def nodesBlock10 : Array Node := #[
  ⟨23,3,[ew242,ew211,ew81,ew79],lh 3 [23,17,167,35,182,15,259,260] [0x88e58c0a28412b]⟩,
  ⟨23,3,[ew80,ew239,ew79,ew78],lh 4 [23,17,15,175,182,167,35,258,179,191] [0x910832371216020,0x51154004]⟩,
  ⟨23,3,[ew240,ew80,ew79,ew78],lh 4 [23,17,191,35,182,179,167,15,54] [0x2121400402100370,0x61165583]⟩,
  ⟨23,3,[ew80,ew81,ew79,ew241],lh 4 [23,17,191,54,179,182,167,204,239] [0x210443321218070,0x61165005]⟩,
  ⟨23,3,[ew242,ew80,ew81,ew79],lh 4 [17,23,54,179,182,167,204,239,191,35,260] [0x7766050814143322,0x1501a090]⟩,
  ⟨23,3,[ew213,ew81,ew216,ew78],lh 3 [15,35,193,170,175,190,16,182] [0x69471fc88068201]⟩,
  ⟨23,3,[ew217,ew213,ew81,ew78],lh 3 [15,35,193,170,175,182,261] [0x47080480724ea208,0x3]⟩,
  ⟨23,3,[ew243,ew81,ew79,ew78],lh 4 [15,17,35,167,198,170,191,182,175] [0x1344200261012002,0x31135857]⟩,
  ⟨23,3,[ew244,ew81,ew79,ew78],lh 4 [17,35,15,170,191,198,175,167,182] [0x455122107041221,0x30063638]⟩,
  ⟨23,3,[ew80,ew81,ew79,ew245],lh 4 [17,15,191,170,35,175,18,182,167] [0x202611320204114,0x80053537]⟩,
  ⟨23,3,[ew80,ew81,ew246,ew79],lh 4 [15,17,35,167,170,198,261,182,175] [0x4847610120022002,0x13131355]⟩,
  ⟨23,3,[ew247,ew81,ew79,ew78],lh 4 [35,15,167,191,17,182,201,170,175] [0x6652011032440110,0x23327875]⟩,
  ⟨23,3,[ew248,ew81,ew79,ew78],lh 4 [35,15,17,191,198,201,170,167,182,175] [0x5544011032320110,0x72276968]⟩,
  ⟨23,3,[ew80,ew81,ew79,ew249],lh 4 [23,17,15,35,191,167,201,182,170] [0x610322341413020,0x51158007]⟩,
  ⟨23,3,[ew80,ew81,ew79,ew250],lh 4 [35,15,167,191,198,201,23,17,175,170] [0x5544011032320110,0x77329866]⟩,
  ⟨23,3,[ew80,ew81,ew251,ew78],lh 4 [23,17,15,35,191,16,167,198,182,170] [0x5570322341413020,0x61169008]⟩
]
def nodesBlock11 : Array Node := #[
  ⟨23,3,[ew252,ew80,ew81,ew78],lh 4 [16,17,167,191,23,35,182,198,54,170] [0x404211220701331,0x60065985]⟩,
  ⟨23,3,[ew80,ew81,ew79,ew253],lh 3 [175,182,16,17,191,54,35,167] [0x21044ac288e3451,0x1c3]⟩,
  ⟨23,3,[ew254,ew80,ew81,ew79],lh 4 [175,182,35,17,23,54,16,167,204,191] [0x2181073001600250,0x41149223]⟩,
  ⟨23,2,[ew213,ew223,ew78],lh 2 [15,16,167,182] [0xd78281]⟩,
  ⟨23,2,[ew209,ew235,ew79],lh 3 [17,191,182,184,175] [0x20820889a]⟩,
  ⟨23,2,[ew209,ew80,ew238],lh 3 [17,191,35,180,175] [0x20820889a]⟩,
  ⟨23,2,[ew213,ew239,ew78],lh 2 [23,17,167,182] [0xc39684]⟩,
  ⟨23,2,[ew242,ew239,ew79],lh 2 [23,167,17,182] [0x189933]⟩,
  ⟨23,2,[ew213,ew242,ew81],lh 3 [23,17,191,167,182] [0x10260864a]⟩,
  ⟨23,2,[ew213,ew81,ew246],lh 2 [35,15,193,170] [0xee1414]⟩,
  ⟨26,4,[ew90,ew91,ew92,ew93],lh 4 [263,262,2,9,7,11,5,21,20,264,265,266,71] [0x788030719733011,0x40050a4472208002,0x322161122366b550,0x6252151343353141,0x24c65664]⟩,
  ⟨26,3,[ew91,ew255,ew92,ew93],lh 3 [2,263,9,264,7,71,21,11] [0x5839c086940c2651,0x5]⟩,
  ⟨26,3,[ew256,ew91,ew92,ew93],lh 3 [2,263,9,264,21,5,7] [0x5a1a4c30b18082a1]⟩,
  ⟨27,7,[ew94,ew95,ew96,ew97,ew98],lh 5 [119,7,267,269,2,5,11,24,23,9,274,273,262,28,20,32,279,6,272,275,268,1,270,271,276,277,278,280,281] [0x9290098201d29,0xa1d08009ef01d8c,0x1c87189ad01ea7,0xb1ca500884188a2,0x44d1b9c21008c2,0x29ef1b1085c832,0xc24a59b1ec9a90a,0x25ce1a8aa029d9,0x5a421024c65a821,0x1c09a1b5ce028c6,0x5c0301b4841c1d0,0x5b4cd1a028da0c8,0xe14c519425590c4,0x59024]⟩,
  ⟨27,6,[ew94,ew95,ew96,ew257,ew97,ew98],lh 5 [5,11,9,119,282,7,274,284,262,23,2,180,279,24,269,283,13,0,285,20,21,267,32,273,286] [0x6a1041108843442,0x20c8e4a48320c74,0x7a9ef0008a23875,0x685ad2b5e179004,0x324c63890943ca5,0x30cc6199635a0e7,0x5800b52c4012c6b,0x11442088c530942,0x380031d8e339821,0x6158751d806314a,0x7420c0b1254a421,0xbc62e001d083800,0x98432087118c821,0x1329401080a0]⟩,
  ⟨27,6,[ew94,ew95,ew96,ew97,ew98,ew258],lh 5 [9,262,119,2,5,24,28,32,7,6,274,23,273,270,269,1,11,287,267,20,288,289,285,290,281] [0x284220004109400,0x49925394a6325ef,0x290a91a52449465,0x2b4ac420a228851,0x5194a39c2633052,0x902118404204e7,0x20001002808060,0x8001014250441,0x3cce719cc42284a,0x5a16bad0c831866,0x5b96bb2cee39986,0x260844206c19ee7,0x234847106d18d03,0x21410d80dc3]⟩
]
def nodesBlock12 : Array Node := #[
  ⟨27,6,[ew94,ew259,ew95,ew96,ew97,ew98],lh 5 [267,23,9,32,5,11,7,119,6,0,272,269,273,270,275,291,274,2,292,277,28] [0x435003800d020e8,0x41d001000702042,0x40a1a94150060,0x5108078004028ea,0x18082a106400a0,0x70c6b084eb83442,0x39e2d211631b821,0x6252c295894b0a5,0x90c620884312c21,0x618c23896421cf3,0x90874a44630929,0x198c15846420d63,0x614b429426084a1,0xc31885290c6]⟩,
  ⟨27,6,[ew94,ew95,ew96,ew97,ew98,ew260],lh 5 [262,9,267,5,23,2,282,273,11,269,24,20,1,119,272,275,270,7,274,287,289,285,293,288,28] [0x70006918c013821,0x11046630c430982,0x32cc22884b118a6,0x11c4a4295498902,0x1584a6a955509a2,0x30012102c08080,0x942018c0500461,0x200138428080e0,0x34017842d081e0,0x2148918d2529063,0x240874208921cf7,0x1a06348ca829cf8,0x1a46348d69594e5,0x93c5108ad2b]⟩,
  ⟨27,5,[ew261,ew94,ew95,ew96,ew97,ew98],lh 5 [20,1,272,9,23,24,13,0,267,274,279,295,262,11,294,278,28,5] [0x5114448d2342045,0x10443709a701806,0x90452880600881,0x785831b16b00c24,0x113820109c20]⟩,
  ⟨27,5,[ew94,ew95,ew96,ew97,ew258,ew260],lh 4 [288,9,20,7,262,287,11,2,6,274,267,119,269,28,285] [0x5ba5282505084141,0x1391192421401035,0x7626d3600c027043,0x366e3772]⟩,
  ⟨27,5,[ew262,ew94,ew95,ew96,ew97,ew98],lh 4 [6,272,32,2,11,7,9,262,20,23] [0x5483839276760101,0x110010110067054,0x2845453736262710,0x3453254232]⟩,
  ⟨27,5,[ew263,ew94,ew95,ew96,ew97,ew98],lh 4 [2,7,11,1,20,274,262,9,279,267,24] [0x21040438385656aa,0x1240409383699521,0x427717507353612,0x210212104]⟩,
  ⟨28,6,[ew99,ew100,ew101,ew102,ew103],lh 5 [301,7,5,296,34,272,302,26,28,304,305,308,182,29,307,24,23,303,306,309,297,298,299,33,300,167,310,288] [0xb34adab4e7a0ca3,0xcc303508c0cf7,0xc51034c600d08,0xd430244902411,0x5382e9388492429,0x150801cc752489,0x154501d07014c5,0x144202c0b02c59,0x9bc8f53c2152c8b,0x301a018429ac2b,0x302c018060304c,0x300c040300401b,0x8840082102884,0x21]⟩,
  ⟨28,5,[ew264,ew99,ew100,ew101,ew102,ew103],lh 5 [34,296,302,28,272,5,301,305,314,315,316,29,26,311,309,312,313,303,287,310,288,317,318] [0x394c5309a361161,0xc0611848f381c0,0x20c4312100084b1,0x129531101202525,0x581500814]⟩,
  ⟨28,5,[ew99,ew100,ew265,ew101,ew102,ew103],lh 5 [302,34,29,5,26,28,7,319,320,321,301,312,296,27,272,167,322,305,309,306,310,288] [0x3b4422804c1104b,0x214052388840447,0x88200518260a52f,0x741866190d43,0x186308035]⟩,
  ⟨28,5,[ew266,ew99,ew100,ew101,ew102,ew103],lh 5 [7,28,5,34,272,302,29,315,296,26,301,305,33,27,319,310,288] [0x58942284a149106,0x114250b0c418060,0x2048128c030384d,0x44f0806021ce2,0x4018410]⟩,
  ⟨28,5,[ew267,ew99,ew100,ew101,ew102,ew103],lh 5 [28,7,34,296,302,5,26,314,321,29,272,305,301,33,303,310,288] [0x2b0ab0100451923,0x19003034c308822,0x3008021ce218cae,0x80af0044112105,0x44110030]⟩,
  ⟨28,4,[ew99,ew100,ew268,ew102,ew103],lh 5 [34,296,272,302,5,315,316,312,28,29,303,7,26,287,310,288,317,318] [0x914148428088e2,0x2948260c4302c01,0x181e3319c3101a0,0x88200]⟩,
  ⟨28,4,[ew269,ew99,ew100,ew102,ew103],lh 4 [302,26,7,28,272,29,34,310,288,319,316,323,324,167,321] [0x882077a004303003,0x1ed152c599b51414,0x26261621]⟩,
  ⟨30,10,[ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [325,11,9,332,5,35,29,327,23,47,296,272,182,2,336,7,26,334,39,262,1,279,329,304,6,32,33,307,302,28,24,121,34,326,328,330,331,27,333,335,337,338,339,287,340,341,342,343,277,288,0,344,345] [0x2da84640600a2ca,0x1ca08a00a41a1c6,0x1451d64d6016162,0x90a30c1c62088ca,0x3460c630c1ca208,0x1d73570d72651c6,0x4511c6041986249,0x3864511db0419db,0x1520124e8010082,0x127120104d3012,0x55500b514a4b75d,0xd810400b34b0d8,0x451a8b10b01834d,0x1e041b1e3eb010,0x7c20c530c3903cf,0x57eeb4230c002,0x104005270bc2104,0x3858050022420c5,0x41382802002041,0xd93590c8108005,0xcb10c834d0d9104,0xd43d4cc804839c,0x3cf389049395055,0x3893c9d040410c4]⟩,
  ⟨30,9,[ew109,ew110,ew270,ew111,ew112,ew113,ew114],lh 6 [325,327,35,5,26,47,11,23,29,7,9,350,34,2,302,304,308,182,356,262,329,28,39,1,332,347,119,0,296,32,354,336,121,312,346,272,337,348,279,349,351,352,353,355,357,358,359,360,361] [0x104048048000021,0x1c04805c000,0x4d40140820484c8,0x54554008082054,0x38804155506238e,0x4f1450480c3048,0x24f04814804f0cf,0x5924905931904f,0x6304404404f30f,0x164e4004084041,0x3960044d3016096,0x5d7025555016,0xc3004144004984,0x40c4010150010,0x186027249010190,0x28a010250000,0x8200028a000082,0xa684512d875d000,0x34d2d838e6aa5d7,0x2d834d2d814569e,0x24949f186ade145,0x49f30c6ae186b6c,0x1c700a80a0021c7,0xa0c300280200a,0x34d0020c2002342,0xa6db00230200a,0xc70026c200a30c,0x2d10d12d13512c7,0x18749130c2c7347,0x48e18e2c7247bc7,0x1832c3243485186,0x485245c03]⟩,
  ⟨30,9,[ew95,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [365,327,325,26,35,302,11,47,29,336,5,2,34,296,272,334,304,308,182,362,20,121,55,282,1,28,332,307,39,7,24,23,329,262,284,363,364,354,40,27,337,167,287,366,31,310,288] [0xc30410a0041360,0x820c30825d7082,0x610411210825d7,0x9238a24da145041,0x1c701a618000145,0x1c701a2cb000,0x1860003cf0252cb,0x91860003cf009,0x3880480c304d38d,0x4804804d0c3048,0x608041066040104,0x4d60d04d14d048,0x1e7048508048145,0x481c7050510050,0x19b05b30c050190,0x310405030c05b,0x301c11c01c0a8,0x8e659083143003,0x1ce08365908e14e,0x911d109152908e,0x76a09131108e514,0x9175d09e31e09e,0x14500256b004145,0x28a004555000,0x1c700428a0041c4,0x25ac004304002,0x28a00459600030c,0x4d22924d22ed4d5,0x1ae2525924d52cb,0x25218625f59f25f,0x18624a3ca24b186,0x24b3cf24a]⟩
]
def nodesBlock13 : Array Node := #[
  ⟨30,9,[ew109,ew110,ew111,ew112,ew271,ew113,ew114],lh 6 [327,332,371,26,262,7,5,34,2,120,11,35,376,182,47,267,272,274,296,302,369,39,121,325,9,370,269,20,24,365,354,336,346,367,368,29,337,372,351,373,374,334,287,375,366,377,28,310,378,379,380,381] [0x4100200c3012412,0x121120120c3000,0x2cb0091090092e1,0x9009000022012,0x230090090014d3,0x1438e0096c9001,0x29400938e0146d4,0x192990191c7014,0x1240832cb0141c7,0x831040952d5095,0x4d00509500954d5,0x8f5cf043043090,0xa0f0835c39c3983,0x4f18f08320868f,0xa4304318308f20f,0x9c1c7adc16a083,0x5ac04b4cb303145,0x8b5960514d1091,0x7510915d1684744,0x581860845c4b51,0x208044184084204,0x9828a304144098,0xd084284318145,0x561af00002e00d,0x20804d18d04d20d,0x7028a30d145056,0x18630d28d041145,0x4118604138e05e,0x28a31f14505e38e,0x31f1c76b3145cb1,0x1c70461453081c7,0x308148046]⟩,
  ⟨30,9,[ew97,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [354,327,35,332,47,383,329,9,26,262,7,29,34,267,23,334,296,28,272,121,11,279,39,308,182,302,384,55,307,24,274,304,325,365,345,382,20,336,319,337,167,287,366,310,288,317] [0x20804101f0412df,0x20802334d000,0x2490211c702034d,0x21249000082020,0x38e00355500038e,0x41104003555000,0x28a0003cf041064,0x2528a0003cf022,0x34b04b20805034d,0x4b24b05021004b,0x8b046246046082,0x5065004654604b,0x46046659050550,0x41066040104046,0x29c05c30c046286,0x14808204630c05c,0x249156096156267,0xd2451156656148,0x1120d6451152652,0x171170170e8012,0x2a9157317012012,0x69728a15d31d89d,0x45e15e4ea0c2451,0x70071424d30de,0x1070020c2002102,0x1476c7682302007,0x1131426db687307,0x181180180eb013,0x52c6986d8013013,0x6985140ce6ce0ce,0x5140033ed004514,0x43cf000]⟩,
  ⟨30,9,[ew109,ew110,ew111,ew112,ew113,ew114,ew272],lh 6 [327,336,35,386,26,334,5,302,47,23,388,2,262,272,28,385,9,121,347,10,370,55,39,308,182,24,325,332,307,345,20,34,273,365,1,354,175,29,337,387,389,357,390,391,392,379,393,394,11] [0x35201210401c35c,0x1231201c104012,0x82013313013082,0x141c7013253012,0x7940131c7014394,0xf78f00f208014,0xf000024014208,0xf00f0017df00f,0x3260c4082001025,0xc430c0d60960d6,0x1c79cd38e0d61d6,0xc42042842490cd,0x1840d7217297186,0x59a190d7157744,0x68d0440440d9159,0xc4684a84a440cd,0x45004224980dacd,0xc24510502490d0,0x1820c2202050186,0x421420d0208042,0x5420501450d0555,0xc268204c84c0c2,0x2110cc68c042842,0x2982182982cb291,0xb090581582912d1,0x47047062145062,0x6c9b87b4728e6ce,0x4b54b80ebce289,0x145046555046145,0x2866c674b8cb04b,0x528b6cb7468c6,0x30005]⟩,
  ⟨30,9,[ew109,ew110,ew111,ew112,ew273,ew113,ew114],lh 6 [325,332,35,395,47,11,29,2,282,307,262,296,272,329,334,398,284,274,9,55,124,283,279,23,7,5,28,327,20,34,24,123,365,354,336,348,372,351,396,397,387,294,21,26,287,399,302,278,288,400,401,402] [0x30c0068c60c930c,0xc628a0090090c6,0x820cd28d00d082,0x4b90b0cd68d006,0x6c904d04d0cb68b,0xcb6cb98b94b0c9,0x1140c61c77d49d4,0x461060d41d4054,0x149a0938e0c6146,0xc08c3c63860c9,0x28a0080880082a9,0x800800002a00c,0x2b0c86c80015d7,0x1571c008108001,0x75500871c015115,0x1e75e01e62c015,0x42d00a68a015618,0x2410011691011,0x811011011002802,0x12652002002011,0x104002659002102,0x124d2002602012,0x6d00024d3012612,0x5010400002e0d0,0x1c70561160561ef,0x571703d64d6050,0x1043d61450574d7,0x411040411c7061,0x1453e24d30611c7,0x3e21457f375dcb1,0x14505938e3c7145,0x3c738e059]⟩,
  ⟨30,9,[ew274,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [354,325,124,403,20,11,35,39,262,302,182,296,272,274,29,23,332,334,9,26,28,34,5,7,55,327,307,405,24,121,365,47,345,404,308,336,321,287,366,278,288] [0x38e0210820d938e,0xd94d30d9082000,0x18601e208001022,0x1e186000208001,0x3cf01028a0003cf,0xd911f01028a000,0x45100014500001f,0x23451000145020,0x30c04e4d30c2302,0xce2080424d30ce,0x1860c2208042186,0x40b2490c23c204e,0x10b4022490cb50b,0xc21040024020cb,0x5550cb14b00b00b,0x6cb5550da15a81a,0x18704720804c18c,0x4724704c20c047,0x50704c24904c514,0x104007007047,0x5e5047547000064,0x475d705c55c05c,0x24d04d766046514,0x1259204675d04d,0x10400d59600d10d,0x5261204d5cd012,0x10404d6180525d2,0xa10a00a427009,0x1686ca60a009009,0x6ca14540f60f40f,0x145016456004145,0x4451016]⟩,
  ⟨30,9,[ew109,ew110,ew111,ew112,ew113,ew114,ew275],lh 6 [325,336,9,406,274,24,7,5,296,302,47,6,2,407,29,262,329,23,304,307,182,121,345,327,1,332,35,20,127,365,354,349,328,375,28,27,389,357,408,409,287,26,366,310,288,410,400,411,412,11] [0x14e00e7ce0c8145,0xce3ce0080080ce,0x69a0d03d00106a0,0x8482480d045000e,0x6d03502490c8888,0xd26d23522a30d0,0x9130d219259028a,0x520520d3193053,0x5ce9939530c85c8,0x50827089c80ce,0x3cf0000820003cf,0x544500b249005,0x28500b44b005245,0xb28b00b1cb005,0xb0000280051c5,0xcb5cb00118600b,0x56a00f44f001029,0xf555004444004,0x1c70042840021c2,0x418400228a004,0x4002182002002,0x2002004744004,0x28a004004002742,0x35429435432b355,0xb6c05419435530c,0x49049058186058,0x651bd8b98349649,0x4c04c714c09351,0x18c047587047187,0x34764758c78c04c,0x5c634c64c587787,0x310c6]⟩,
  ⟨30,9,[ew276,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [365,325,39,413,274,47,55,336,329,2,296,11,302,29,332,272,9,5,334,304,28,308,182,23,7,327,26,307,20,24,35,414,121,354,167,287,342,310,288] [0x34d01f2080d934d,0x69a0d9208000,0x8200069a001082,0x1e0d911e001,0x2490010200d95d7,0x24900e145000,0x186000492021145,0x7186000492007,0x3cf0480820ca3ca,0xca10a04a08a0c8,0xa0c8104008048,0x38a30a0c850800a,0x24d38d30c0ca514,0xd32533931450cd,0x1860d32d338d14d,0x1d31930db2db1db,0x10200204200f10f,0x4230200f00f002,0x50204f30c04f514,0x55722042142042,0x2d504271c055155,0x5d2dd05d623055,0x400030c055618,0x10450001024004,0x150004444004145,0x10190004604010,0x451004186010610,0x39645639626538c,0x2e61d619638c249,0x1d62cb1d71971d7,0x2cb1d14911c92cb,0x1c94921d1]⟩,
  ⟨30,9,[ew109,ew110,ew277,ew111,ew112,ew113,ew114],lh 5 [365,354,325,9,5,267,29,302,296,415,272,26,0,32,124,11,336,23,34,332,327,334,182,307,7,24,416,287,35,47,277,288] [0x499461196b4a148,0x3b4e49a861216b,0x49866018064ba8e,0x18064b8630384e,0x4a2289a2d649a26,0xba6e4a08899ac6,0x4a1e80a0284b884,0x822a84ddf785eb5,0x14450144502c0b,0x144502c6b02c0b,0x114e502c0b01465,0x11625128ea12a31,0x9445094850a82a,0x1671b12aaa0a88a,0x4d06312b1816659,0x4dad000e70001c,0x4d08404dad000e7,0x418c002520041d,0xe70418c00252,0x9ad00ce300dad,0xc03000840041e,0xe4300d8300252,0xb66d09c840098c,0x81d8709c270b484,0x81def84591845ff,0x91ef09184085ef,0xc18c]⟩,
  ⟨30,9,[ew109,ew110,ew111,ew112,ew113,ew114,ew278],lh 6 [336,332,418,35,2,9,417,11,1,329,296,23,47,304,308,5,272,26,29,39,307,24,262,327,325,20,421,6,365,354,360,328,378,27,392,379,419,420,337,167,287,410,400,422,423,288,279,7] [0x41279245118a40a,0x19215208a451192,0xc31895890890df,0x4a80a1892c9012,0x10904904918a2ca,0x18d10d04d321189,0x89418d1cd04930c,0xd00d1941d4014,0x5ca9148d418d5cd,0x9114569295218a,0x5960930d30935a6,0x502cb093213091,0x3100532d3090210,0x8e30e04e667090,0xa6808e1ce050659,0xe00e0951d5015,0x61bad5a9508e60e,0x32cb691b1109b,0x2080052cb085205,0x831030053cf083,0x30851040033c3,0x50050851c7003,0x6050037030831c3,0x83603005705085,0x3cf0411040483c8,0x2d048108041,0x5c80001c7008048,0x41c400002e188,0x400f1c700f04f,0x4404404c74c004,0x5c704c04c044744,0x102f187]⟩,
  ⟨30,8,[ew110,ew270,ew111,ew112,ew271,ew113,ew114],lh 6 [371,350,5,120,34,47,26,35,262,302,7,11,29,327,304,426,308,2,9,296,39,325,274,369,121,329,182,347,55,332,272,312,269,368,119,370,424,425,367,427,366,28,310,428,429,317] [0x1c734d35e3464de,0x141d4014208006,0x24014254006208,0x6006000249001,0x54600639f00055f,0x644602038e006,0x86010150010082,0x2528a0102d0006,0x5930102900002cb,0x35830031e6013,0x26105d0610131c7,0x5d249043883003,0x543003303000555,0x4344305d30c003,0x83057457057082,0x9e31043d72d7043,0x2473d31048a32cb,0x16256016628007,0x64700830c007618,0x865900730c007,0x82008148012092,0x8108012145008,0x71c012104012712,0x34d369358659008,0x15a05a46a058145,0x3c970904945105a,0x2da04110406b2cb,0x4e14505b09b3da,0x28e05b14504e08e,0x81b28ab1b1043ce,0x28a3c512d3cc10c,0x3c528a042102042]⟩,
  ⟨30,8,[ew109,ew270,ew111,ew112,ew273,ew113,ew114],lh 6 [395,325,350,35,47,11,329,282,9,304,28,39,34,2,26,430,279,272,7,284,5,327,283,308,262,347,332,23,0,312,123,20,274,21,119,24,296,424,294,431,302,278,432,285,433] [0x618001024009451,0x66060060c3009,0x250062860090c3,0x600600028a002,0x5460062dd00055d,0x67c601e2cb006,0x1040097c9009109,0x1930c009149006,0x81100930c019159,0x478070470e6051,0x2a109a0a10510c3,0x9a28a087887007,0x547007387000555,0x8734709a38e007,0x104096356096104,0x9e330c3d6156087,0x28a3d14928a3145,0x4828a0484c8043,0x2c80433830434d3,0x432cb04838e048,0x514043103048508,0x43483048104043,0x143048492048145,0x410680132cb043,0x110090369093104,0x3d049009334d090,0x15009b31b09b145,0x9734d08b1043d0,0x31708b34d097117,0x7ac30caea1453d7,0x7143c41453ce14e,0x3c471c094145094]⟩,
  ⟨30,8,[ew109,ew270,ew111,ew112,ew113,ew114,ew275],lh 6 [406,325,35,302,356,7,26,9,6,434,47,2,24,5,329,304,312,308,327,182,29,121,23,274,361,28,119,336,39,20,127,32,1,287,296,328,262,279,425,27,175,435,310,288,436,432,437,438,11] [0x1d4001022014314,0xe90e00e0a3014,0xc300e94e014082,0xe0c3000659026,0x74f00f2a700e74e,0xf14f00e28a00f,0xf010150010028,0x1019000049200f,0x5d701e186010490,0x415d704108204c,0xcc2487df04c082,0x2480c368c820a4c,0x2c824828868c2cc,0x11b12160c28c248,0x145108688008161,0x818800049211b,0xc311b186008488,0x470c3047547042,0x282047347042555,0x4728a04234d042,0x145047047042142,0x42182042042047,0x71c047186047707,0x2532ea25528a042,0x1532552cb253293,0x116156116b2b113,0xb56243451103103,0x793bc3259186b96,0x60d10d14d10b10b,0x60b18b10b14510d,0x45160d18624d44d,0x4107000545124b]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew279,ew113,ew114],lh 6 [371,395,350,47,329,34,272,274,308,9,28,35,182,0,296,29,11,302,180,2,304,39,439,13,7,55,5,20,327,347,262,24,121,23,26,325,332,336,124,123,27,337,267,269,167,287,366,32,119,310,288,440,285,441,442] [0x18f04f20804e18e,0x4f24f04e20e04f,0x2cf0442440442cb,0x4e30e04428404f,0x70404430404e28a,0x44684067066044,0xc30546d40540e8,0x5d145054414044,0x2cb05414505d41d,0x152d50157a9022,0x28a01545502279e,0x1528a006446046,0xc602b02a046706,0x80c80086ec006,0x62d0081480066db,0x861801f15f01f,0x44700782e00b28a,0x1201200b820007,0x8d20070070078c7,0x120d2009689012,0x6070090c301269a,0x9609009649007,0xaf051711007659,0x8c4f10910c30b0,0x64c0914d308c0cc,0xa16610a143258c,0x4d30825d758c410,0x824d30a45d70a4,0x34dd334105a534d,0x5831455a5145db5,0x34d09714509734d,0x583]⟩,
  ⟨30,8,[ew109,ew110,ew270,ew111,ew112,ew279,ew113,ew114],lh 6 [34,35,350,5,395,371,329,11,39,302,9,20,2,262,28,47,121,29,26,274,180,182,304,308,7,0,327,23,119,13,347,123,269,439,325,356,312,296,328,27,272,337,167,435,332,443,32,444,445] [0x445492444444124,0x6644a445125444,0x19b19104118d186,0x18624910e385249,0x3e718b19f11f19a,0x5875863cf58b596,0x49600078779e000,0x369481484128484,0x20921234d201208,0x20838e14924438e,0x2ea20f22016021a,0x5c05c82cb5cf5d7,0x4d761814002b618,0x34d1534c534d153,0x8e38271c082085,0x2c230c082b0469a,0x1c708b2c230c08b,0x84001c1c7b58621,0x4132494d04c1241,0x141062054154050,0x50c50a0ca522501,0x28100128c2940c3,0x69004704a00a287,0x54c3100c3702b90,0x1d501540c4150d5,0x75d54755b01b6c7,0x830c275d0830c2,0x30659bc0023659,0xd90cf0008c0,0x3d93c3]⟩,
  ⟨30,8,[ew280,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [447,446,350,272,35,26,11,32,9,2,47,296,29,5,329,274,1,34,55,7,448,304,308,327,24,262,119,20,325,347,39,332,336,302,449,328,27,287] [0x2cb04130c0572cb,0x410c305730c041,0x1450570c3057145,0x1c10400020801c,0x41000010401c208,0x822490826a1057,0x34d09f24909f34d,0x6a2451520186082,0x61852049269a186,0x4c0cc04c14504b,0x12304c20c04b145,0x4c10404e64e04e,0x1cb04b04b04e1ce,0x4e24e04e04e04b,0x28a0556d50552a4,0x5d45105519504e,0x10405545105d19d,0x1e11e01e659003,0x30051c5005659,0x50050431c3003,0x2960166db003283,0x164560036c3016,0x4d30184580184e5,0xf1c7004004016,0x3480041c400f00f,0xf34d00f28f008,0x48800f4cf00828a,0xf4920084c8008,0x28708724909028a,0x507487090249087,0x186090490090190,0x8d4cd509186507,0x5094c908d186]⟩,
  ⟨30,8,[ew281,ew109,ew110,ew270,ew111,ew112,ew113,ew114],lh 6 [32,11,274,451,7,28,350,9,403,35,20,5,383,302,329,29,26,39,34,47,304,308,327,0,262,361,347,23,2,354,452,450,269,332,325,356,312,296,328,27,272,337,167] [0x8164102037d63cf,0x1c7183856216303,0x3020831c7882083,0x334d18000334d,0x410c37164dc180,0x8d75c30416575c3,0x3cc4103c83c8224,0x2663d83cc2253c8,0x38038f24939838e,0x38e34e20000634d,0x4d350a5144e738a,0x68169a49251750e,0x408228408414492,0x618449451629409,0x30d34614544d450,0x5552aa453451145,0x10455255128a553,0x302095104312499,0xc24930208c249,0x145180006145180,0xc618328a743746,0x11904164411e041,0x142080009145784,0x8a0872c7240002,0x1c21021ca1c22cb,0x2cb0810471071c1,0x1431402cb006005,0x5b11b6c1040100,0x4b2c42ca041001,0x28410b]⟩
]
def nodesBlock14 : Array Node := #[
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew282],lh 6 [386,406,9,35,5,24,308,356,2,23,370,304,7,34,453,28,274,29,329,302,20,39,334,32,47,121,182,307,55,332,327,262,26,325,354,361,328,27,296,127,337,167,272,273,366,310,288,454,440,455,456,457,317,11,119] [0x15105118605b15b,0x5109105b19b051,0xc30520920520e4,0x4a4d3052252051,0x10a0524d304a24a,0x4b50b04b62504a,0x34a04b30b04a618,0x4b34d04a30c04a,0xc306706604b78b,0x150d50157e8020,0x3cf0154d50207df,0x153cf0054c5005,0x606006529005605,0x6346005514006,0x30c00534d045305,0x2b02a046786006,0x3d001066c0033cf,0x2102003659010,0x502003104003503,0x2702003303002,0x1000371c002302,0x2002002842010,0x22d399104010850,0x39920839a11a39a,0x5891c9bee1da71a,0x3977571d71d71c9,0xc97389749c49c09,0x1c45b41c8348cd7,0x8881c85961c4344,0x8c48843847448c8,0x1f5056796388748,0x1f6]⟩,
  ⟨30,8,[ew109,ew110,ew270,ew111,ew112,ew113,ew114,ew282],lh 6 [5,35,28,302,7,32,2,406,34,9,386,274,262,329,47,39,356,20,308,29,26,23,304,347,327,453,119,55,350,127,273,361,325,451,312,307,328,427,27,24,337,431,167,443,336,288,458,444,459,11] [0x4ca5144c74c71e2,0x644cc4ca1e34c7,0x34235304134c34d,0x34d0c31c20a50c3,0x38e5915963a6340,0x5c45d720858458d,0x51d1dd5d85d6208,0x3285015071e7507,0x3c33d430c3c13cf,0x3cf0822830e9082,0x45148e49246a3ce,0x28820710448848f,0x2de29e498492104,0x30c28b2ca30c28b,0x68516b08264514a,0x1994517c6199082,0x69a41041f451646,0x410b07618404110,0x4b08b2c5141082,0x46049009045,0x25b241101246241,0x24b28b05b6c9109,0x2e02c9289260,0xc60c5000146183,0xd521556eb436c3,0x71556f5457050d0,0x410e20e170155,0x6846384380200,0x60819c18084001c,0x690c48]⟩,
  ⟨30,8,[ew283,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [461,460,24,11,9,35,302,47,29,26,2,356,274,182,370,5,462,0,307,304,308,329,28,39,327,262,20,121,32,332,325,119,23,354,361,463,464,34,328,27,337,167,366,310] [0x492041208058492,0x41082058208041,0x249058082058249,0x1e14500010401e,0x71c00014501e104,0x91f71c7e318641d,0x1c78a128a41d34d,0x8a11c741d28a41d,0x922cb7e5058451,0x48088048249052,0x166048648052249,0x48145055655055,0x58e04e186055595,0x4e68e05518604e,0x1c70536930531e7,0x4e04e0530d304e,0x14505305304e0c3,0x17157017668009,0x596017197009659,0x17596002182002,0x1d40146a90021c2,0x140d400269a014,0x140420c3002002,0xc6ea005186014,0x3c40056db00c18c,0xc3cf00c1cc004,0xc400c00c0041c4,0xc0cc004004004,0x3cd40d2ab41b3cf,0x2cd44d41b28a40d,0xcd2e04602e00c3,0x2cf4512ca0ca2cd,0x2ca4512cf0cf]⟩,
  ⟨30,8,[ew109,ew110,ew270,ew111,ew112,ew113,ew114,ew278],lh 6 [35,23,47,11,9,418,417,5,350,304,356,329,39,1,26,308,29,347,2,262,20,325,327,332,119,336,421,466,451,312,296,428,27,272,436,432,465,454,458,440,444,467,468,469,288,302,7] [0x40538e40640619d,0x41340519e406,0x2c12d00102d32cb,0x2cb18b18104819f,0x822542490a02d4,0x44345119124324b,0x451191256249189,0x1a1386389189456,0x30030c4d3380386,0x34804130d30e4d3,0x51430230c04114d,0x3c33cc50c3c23cf,0x3cf14f1430ca162,0x14e1555641633d5,0x14410500014410e,0x3480415cd345000,0x826d249704120d,0x6430db0825d2497,0x6192992830ca9a5,0xadaa98629a27698,0x10104434400101a,0x1c008210710034d,0xc4005004084007,0x50000c3105104,0x1c0540105104544,0x4812071c8492047,0x2830c120128ab01,0x1c20c328ab41581,0x70208a0870c71c8,0x880877071c81c2,0x20ab83583]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew284,ew113,ew114],lh 6 [447,470,274,47,26,120,472,11,284,35,272,362,2,55,29,32,282,9,296,304,34,308,5,327,20,7,307,325,24,1,334,399,354,332,336,329,27,287,302,471,473] [0x41004e104052410,0x5209205211204e,0x249045085045249,0x4504504e208052,0x5e304e04e045205,0x455c504504504e,0xe404560504e04e,0x450c3053613053,0x1da05a5140531d3,0x408205351405a,0x4010082010010,0xa2080043c4004,0x6c400420400a3ca,0xa6ca00a00a004,0x61800a0ca004004,0xa60a0150d5015,0x51c01c665015515,0x901f01565901c,0x20900200204221f,0x420420495c9009,0x5910096c90425c2,0x25960020c2011,0x3510026420110c3,0x234d011651011,0xc32e72e60485c8,0x2cf0cf2cf30c2c8,0x1e818f34f2c830c,0x18f1c719d35d19d,0xc32e130c2e00c3,0x1a234d2e030c2e1,0x1c718634d1861c7,0x19679618c1c71a2,0x18c79e1961c7]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew271,ew273,ew113,ew114],lh 6 [371,395,35,47,28,332,302,20,34,262,120,282,11,7,370,5,272,121,9,369,283,474,327,279,182,0,325,24,284,55,368,123,21,269,23,424,29,294,26,287,399,475,476,285,477] [0x41004006304e410,0x4e24904e04e041,0x8204a24a04a082,0x4506404a10a04e,0x58a04a19e04159e,0x4a1ca05f18604a,0xc30531d30530c3,0x4e20805331304a,0x9005320804e30e,0xb08b00b265010,0x1200006a0010249,0x2110400b68b04b,0xcb00502604b18b,0x140d40141c700b,0x36701421400b1c7,0x1434d01b21b01b,0x102002728009104,0x218200971c002,0x451009186009449,0x20c20123d2002,0x3420120c30023cf,0x12212012752002,0x45104159600275d,0x1a451044584044,0x3d71570c31443cf,0x5573571440c3157,0x30c86234da62208,0x1581c71460c6544,0x2181461c71580d8,0x7ec208aea34d558,0x65954730c546306,0x54765914f30c14f]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew271,ew279,ew113,ew114],lh 6 [34,47,272,371,262,395,35,120,302,5,20,7,9,478,121,39,180,296,26,369,11,308,0,327,269,55,13,370,24,274,2,182,123,479,119,481,483,332,376,367,368,29,267,287,366,28,310,480,325,482,484,485] [0x4450820d2491082,0x1071c69d1311452,0x1c51c5168446187,0x1cd1691c51cd208,0x411ca1e01601d7,0x4d44c70414ca4d3,0x1930006d46db000,0x1123c63cf104486,0x880821423c83d2,0x6020c20c30cf0cf,0x42603a825c2603,0x8a09505554a282,0x2dc01c70bad5015,0x21d74eb0620854b,0x1831840c418e39d,0x1108501031060c6,0x24c403404844103,0x30105024940140c,0x64c00c319304004,0x5ce145b4e14e119,0x7deb8e04188d88e,0x50864821e79f05f,0x5d721450d000bd4,0x34104d2490c3c05,0x232cb34104d249,0x69a8c00182cbc40,0x90a2a569a94a2a4,0x33596c8b2e6596,0x256241000980,0x56049]⟩,
  ⟨30,8,[ew285,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [371,486,267,47,487,302,296,35,29,262,28,5,7,329,11,274,34,9,488,304,6,182,327,334,20,121,55,2,269,325,347,23,365,354,332,336,26,489,328,27,366,310,288] [0x208041186056208,0x56082056186041,0x1c7020249000724,0x201c701d24901d,0x28a05614504128a,0x1212cb01d145056,0xc31222cb1220c3,0x7254104a330c121,0x864a35d771c30c,0x48088048048046,0x1e6048248046046,0x481c704d24d04d,0x28604614604d28d,0x4d60d04d145046,0xc30536130530e7,0x5e41005339304d,0x1c705341005e39e,0x21c2002249014,0x28a002142014249,0x4228a000145004,0xc20026020000c3,0x2402004618002,0x30c014414014314,0xf668007145002,0x2d100765900f14f,0xf2cb00f0cf011,0x69100f30f0110c3,0xf69a011311011,0xd51156e91190c3,0x4956951196db115,0x38e11f69f11f3aa,0x10b5cb49b38e495,0x49b5d710b38e]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew271,ew113,ew114,ew275],lh 6 [47,7,24,274,371,406,6,262,302,20,369,120,9,5,407,376,370,35,121,296,182,332,327,325,269,2,336,127,490,479,493,483,425,367,368,29,287,26,366,28,310,491,476,492,494,495,440,484,496,497,498,34] [0x4c5082105813082,0x1cb2d18531d34c5,0x2c52c51624d144b,0x2ce1632c52ce208,0x28928a0002c9,0x40141015028128b,0x41015029628a14a,0x1c709144a14a416,0x1882021c7111444,0x186106088082102,0x106097082102197,0x180186246080086,0x46106104902242,0x2073c49465863c1,0x1d24832030d2987,0x1c37030d70c7707,0x34d0c00cc34c1d7,0x304303043300003,0x3037430c40cc041,0x1480c40cc74c304,0x519a080001459c8,0xa54054219654014,0x55248f48f0413ce,0x20e20e555acea92,0xe24938001e249,0x413edb1a041780,0xc2fb9b61868f68f,0x493c96f26f1618,0x7c024104d38d341,0x1500d7cd355340,0x104cc1581]⟩,
  ⟨30,8,[ew286,ew109,ew110,ew111,ew112,ew271,ew113,ew114],lh 6 [267,5,479,26,274,371,7,11,413,121,20,272,120,296,34,2,376,35,9,499,369,0,47,55,182,327,302,370,24,262,365,123,119,325,332,483,368,29,287,366,28,310] [0x20c32027d934d,0x11d1400020c3140,0x4c2819249082759,0x282041142859219,0x38e8ca28204188a,0x41554238e415542,0x3480001430cd000,0x10c31144d10d343,0x30830822435134c,0x313225308313249,0x59650a51459630a,0x6d56db38e51550c,0x4401400d10d4394,0x14b0da0c3083011,0x50031432da2cb,0x2c01402c52cb14b,0x28a0160002802d6,0x70e71c1a600e00b,0x10426745a680186,0x8409e79124911a,0x10a112052142144,0x48418448a484041,0x2091175d2192497,0x60fa49041208a09,0x1d85d824f3d8058,0x416071d05d7407,0x4cf3d30414cf3d3,0x1d01864071d0186,0x1c704618f1c7407,0x3c6181]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew271,ew113,ew114,ew278],lh 6 [417,376,262,501,23,332,11,267,9,5,20,121,47,302,39,120,26,369,368,296,35,327,1,24,182,272,336,421,269,288,428,367,29,500,337,480,287,491,476,502,503,7] [0x65901e410013653,0x13093013410000,0x51400f08f00f51f,0x502000f10f013,0x29101130c00f28f,0x1119100f30c011,0x11012192012021,0x12352000555011,0x51401b34d012552,0xce50e0ce0a20d0,0x10e0c75870d0082,0x7071040ce5968ce,0x30c1472870ce30e,0xc718714e28a0c7,0x470d7197057964,0x9d79970c7347047,0x1026c7a100d934d,0x481040c8588042,0x2820482490c2582,0xc82880422420c2,0x480c8188042042,0x423420c2182048,0x2cb04834d0c82c8,0x14530c1442440c2,0x5d144304145249,0x4470400419d05a,0x2cb00055505a186,0x5a2cb004544004,0x18904914904a186,0x14a2cb04a04a049,0x6181492cb149609,0x4506900661814a]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew287],lh 6 [417,504,376,35,388,347,23,47,26,262,120,11,9,272,20,2,182,369,34,308,24,5,121,55,334,302,267,325,296,327,39,365,354,332,367,29,421,287,494,440,455,505,506,366,310,288,28,273,7,269] [0x34500520801c35c,0x524501c208005,0xc300a24a00a0e2,0xa40a005185005,0x38a00540500a186,0x113910111c700a,0x4850112d100a1ca,0x114920052cb005,0xc3024023011751,0x5e0de05e249048,0x186048648048249,0x10818804d64d10d,0x1d311338e04d1cd,0x5349310d38d053,0x930544940949a5,0xa149d405a6da093,0x66ba9aa5a0546d4,0x8c64c04c58c083,0x1c308c54c043596,0x4c1c7083555043,0x49204c5cc083483,0x897c90435d708c,0x6c90837c30436c3,0x1103ec1161c7049,0x5d01163cf1101d0,0x865c60062ed090,0x12e0067460902cb,0x9561508f2cb12f,0x80e08f6180952cb,0x10f80f10f84f10e,0xb001875810e84e,0xb1]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew271,ew113,ew114,ew287],lh 6 [262,34,9,267,272,5,2,20,417,376,120,11,182,388,302,47,39,24,121,296,26,35,369,370,327,334,504,269,371,421,479,273,483,332,429,367,368,307,337,475,482,287,495,484,507,23,310,336,7] [0x508104894513113,0xa2958d30134d4,0x2882882244d554a,0x28d22528828d38e,0x3cf5875963cf287,0x5cb5d704158b58a,0x55d21d5d85d6041,0x415410026515,0x10e1049c440e414,0x104a040da0d0350,0x1c310f1036c311a,0xc10c41c70cf3c3,0xc3243441451aa9,0xb0345c451ad10dc,0x8e38248200e003,0x82682009000492,0x1c7085080680089,0x10421c7005140,0x2cb0810422cb,0x70009e08270201e,0x48514822d488480,0x31218630530c1ae,0x2cc2410482cb301,0x34515f35f31830c,0x24d18634514d186,0x6182410496db249,0x159146046249bc8,0x187807199645045,0x6191e11c68061a1,0x6c9c19]⟩,
  ⟨30,8,[ew288,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [508,376,509,7,511,347,182,5,2,26,35,9,23,274,267,308,120,369,296,262,47,272,327,302,20,121,307,325,269,1,0,24,365,354,332,510,336,34,167,366,310] [0x69a00049201669a,0x9b38e016492000,0x3cf71c38e723249,0x9b28a0602cb09b,0x75d06028a09b2cb,0x1675d016186000,0x2081211c7064186,0x1212081221c7122,0x38e0417250160c3,0x5385005249012,0x28a0054c5012249,0x52850104d0010,0x30c010190005305,0x10210005185010,0x514011211011514,0x50050110d1010,0x2890110110050c3,0x8e28a08e4d3089,0x30c0895c90894d3,0x10930c0955d5115,0x50f10f626095515,0x8f78f11561808f,0xcf09f79f05f0c3,0x8d66704a5d704f,0x1cb08a65904d5cd,0x4d1c708d60d04b,0x78b04d0cd08b60b,0x8d78d04b0c308b,0x1c61062281191c7,0x460c6119208106,0x4600c0cc04c10c,0x470c3048048046,0x480c8047107]⟩,
  ⟨30,8,[ew109,ew110,ew289,ew111,ew112,ew113,ew114],lh 6 [512,383,354,267,296,304,35,20,47,34,28,262,302,11,513,274,5,7,9,329,283,121,182,327,55,514,515,307,6,23,334,365,325,332,336,328,26,366,310,288] [0xc30050050040c3,0x45c4004004005,0x40055c5005005,0x131a30052c5004,0x2930051860132d3,0x4284004304013,0x2050041c401330c,0x42040051c7005,0x35b01b249004344,0x35c300424901b,0x2cb0541860820a4,0x542cb043183043,0x314054294043303,0x82208043283054,0x1c70832080031c3,0x5c451043243082,0x18604345105c25c,0x601860602cb05f,0x28a3a130c05f2cb,0x3a128a38e30c38e,0x2080001c7017208,0x6622490171c7082,0x45169a24969a451,0x4f56504628a662,0x41204655504f28f,0x8f41008f1cf092,0x61204f24f0921d2,0x4f618052252052,0x4160963a6095410,0x656616095095096,0x34d39d61d39d367,0x9079008834d656,0x8879e09034d]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew273,ew113,ew114,ew272],lh 6 [35,395,272,47,5,386,9,10,370,283,274,2,279,55,385,20,24,23,334,28,388,284,307,262,34,398,347,327,325,332,273,282,336,285,123,516,517,518,455,520,175,29,294,21,26,399,302,278,519,440,7] [0x59a09a68168e082,0x5c71c00165d6581,0x2012074c7580587,0x2076c71c11c84c8,0x3c81c11c86c8201,0x2030ce3ce3830c8,0x399618381381068,0x5ea080099069381,0x145ac25d77c07df,0xb026c25134c2142,0xc924f3c20c2505,0x40540960908f3c9,0x409709245250610,0x4d3245250710405,0x1554a4ca295b57,0xa8ca2852808c0,0x10400f006106005,0x18d18060018f180,0x18a90a00d346606,0x6d529c28690619c,0x30bbd5104145b95,0x44c34c54b2cc10c,0x74c319311351454,0x31431175145444c,0x2d40c350b2e50c3,0x492661c2034d94b,0x9a1c5e89e819819,0x4833437a17a68a2,0x9cb0d2484344112,0x2dd2c49c411d10b,0x41c92052]⟩
]
def nodesBlock15 : Array Node := #[
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew272,ew275],lh 6 [386,406,7,274,5,24,34,521,302,6,9,35,28,2,334,47,385,175,262,10,370,20,327,325,121,182,345,307,55,32,336,500,127,287,273,493,29,26,366,310,494,522,23,523,519,524,525] [0x15105105105b145,0x5149105b05b051,0x2cb0534930532cb,0x54208053313051,0x554053208054314,0x505500503cf054,0x640500900543cf,0x5019f04159f05e,0x2cb060186050590,0x2cb000492005,0x305009208005492,0x930c005205005,0x3c90095490053c5,0x5e1005555009,0x820095c90490a1,0x1e025049189022,0x20300362600b208,0xa10a00b618003,0x3ca0031040033c3,0xa5ca00308300a,0x1830035c300a08a,0xa18600a70a003,0x3671d810400371c,0x1d834d1d91191d9,0x82a59a191cc082,0x1dd38e89dacc1ea,0xb881cc186b4cb0c,0x1c408468d8cd81d,0x18d1cd08d6848c4,0x6841861c438468d,0x38e0415961cd38e,0x1738e042582042]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew272,ew282],lh 6 [5,9,35,386,20,24,23,32,406,308,274,34,385,28,2,334,347,10,302,370,47,455,39,26,262,327,121,182,526,55,528,388,307,273,516,530,518,175,29,127,337,167,272,366,310,527,529,317,7,119,325] [0x8101504175e0145,0x611442090610817,0x4d24911d1402091,0x513113452493353,0x2254d450c10c314,0x30831c2cb308308,0x9522731931c226,0x6185825966285c2,0x15214534d592597,0x24912915415634d,0x20524b245104254,0xc30c90c914b2c5,0xa896495438490c9,0x34a29aac234d543,0x8408100109a68a,0x422c2044042000,0xca09d7412c105d,0x2832810c104304a,0x28188104304a88a,0x1b6ceb1a000283,0x1ad19b75b68e39b,0x1877871dc1c62c6,0x7c71e11c6786195,0x1ee1c67c6195187,0x3c02c000fbc42c4,0x8c001e0048c410f,0x1f00e90e11e100,0xc0f20f39f380900,0x65955cc4f64f208,0xc3c88]⟩,
  ⟨30,8,[ew290,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [386,531,47,35,29,282,28,7,370,535,262,55,34,267,274,272,532,302,9,5,307,2,329,182,304,327,121,334,332,1,20,273,325,23,365,354,534,26,533,464,11,328,366,310,288,536] [0x104041514059104,0x593cf059514041,0xc302228a0007e5,0x220c302028a020,0x1867e645141c186,0x92355541c75d9df,0x8241c55541c082,0x592cb0411c7923,0x3cf0202e80591c7,0x443c4044044054,0xe9044284054054,0x440c3056296056,0x7480485d7056756,0x48788056456048,0x88058798058082,0x483080581d8048,0xc305830c0481c7,0x50c500528a00f,0x18500d45100f28f,0xd186005445005,0x8200d78d005085,0xd30d00578500d,0x1cd00030c0091c7,0xe6aa00318604d,0x4d200369a00e18e,0xe4d300e08e012,0x2d200e30e012092,0xe2cb012312012,0x4d741756b41a4d3,0x25731741a555417,0x2512616e1261b6c,0x2536db2422c2251,0x2426db2532cb]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew272,ew278],lh 6 [417,388,537,272,47,11,2,1,26,336,35,23,9,385,34,308,274,347,10,500,55,334,262,20,327,332,5,39,307,175,421,273,540,288,29,337,167,454,527,536,519,538,539,279] [0xd101120801c0c3,0x1159101c208011,0x29101259201228a,0x130130122d2011,0x5d30120120132d3,0xd5cd00d104013,0x2200d14d013104,0xd39d00061d009,0x28801e38e00d60d,0x9b29b09b5a3088,0x2c30881c8088596,0x482cb0831c3043,0x10f04f5e4083103,0x831430435d708f,0x9c308f14598f94f,0xa43a0308f38f7c3,0x2cb788a8808338e,0x24c2cb08c1cc24a,0x18624c69a08a1c7,0x8c18625069a090,0x80c08c145250810,0x24a38a09014524c,0x51425039009050c,0x4118604710708a,0x661047187041104,0x47647007161041,0x26b00751405f145,0x44644046146249,0x504046646044144,0x46506046546044,0x555000618044555,0x59555005605005]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew272,ew287],lh 6 [35,23,2,272,388,5,262,24,20,417,385,9,55,26,10,34,541,39,308,182,334,347,370,47,455,302,327,121,542,267,386,307,273,516,518,274,175,296,421,522,543,310,28,11,269,332] [0x3550d554d35f0c3,0x18e3800158d57cd,0x59964e04e54000e,0x5d6096399396056,0x2645975ca20a297,0x2892903cf289289,0x1826629a290265,0x18d440451186340,0xd90c304145944d,0x4922080d70d1051,0x9c748f483203497,0xdc0d24121cf1c7,0x7438031dc1c7607,0xa1d1de1c760775e,0x2c104b6cb00105d,0x1402002c52c06db,0x30b00f00b208005,0x19018030c2cf3cb,0x186706010000700,0x7860210007801a1,0x4c54d30a96c5146,0x412414cc4db082,0x10110411341304c,0x604a81681604801,0x50530c154142302,0x105144142102094,0x84088888084085,0xad4254204202882,0x69a610b14694249,0x104b49]⟩,
  ⟨30,8,[ew291,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [544,547,545,11,5,388,347,272,9,28,35,120,2,34,274,26,369,308,296,279,47,39,32,55,327,262,20,307,325,273,24,334,6,365,23,354,332,546,336,337,167,287,523,278] [0x4920006db018492,0x9c1c70186db000,0x82075d1c77653cf,0x9c28a06120809c,0x4e206128a09c208,0x16330c145762018,0x10416430c164104,0x1834d0000c3163,0x1c706634d0180c3,0x61c60063cf012,0x28a0062060123cf,0x628600b20b00b,0x4cb00b00b0064c6,0xb10b00600600b,0x514010110010514,0x63460100d000b,0x28a0103500060c3,0x9529509566708f,0x24909559508f659,0x155249087587147,0x5111516a8087507,0x910d114769a091,0x5109e0de05eaa9,0x8e596059249051,0x10809959604e24e,0x4e10408e68e048,0x5c804e34e088688,0x8e5d704834d088,0x11315332b149104,0x495c914930c153,0xc30415d70410c3,0x447c404c0c3009,0x4c7df0440c3]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew273,ew279,ew113,ew114],lh 6 [296,395,47,272,28,274,34,329,11,371,2,35,55,20,350,180,9,0,285,304,283,5,279,262,7,13,347,282,24,284,23,123,517,325,327,548,520,332,398,307,27,294,21,26,269,287,399,302,119,278,288,549] [0x70c71c11c00c0,0x5c71cb1c05c0001,0x100710400b007,0x10411c11c0100,0x6700101205f001,0x4cd4d30a800d012,0x69a1864c84c0082,0x5e90cb0d3186688,0x249a835d76cb6db,0xac3043384103243,0x83489b03043389,0xcd35409450d343,0x61c19c718b54194,0x10515db8b104518,0x14914b24b2dd745,0x14f80f2c92c5245,0x5503e13c5805161,0x40208f5553c23d0,0x31061040c405605,0x44249bc404414c,0x58ac4408248ec04,0xc9631610a296096,0x6258821e31e788,0x38a28e082041881,0x22330c38a28e082,0x6598c821f30c488,0x90a2a565994a2a4,0x1b3451488226451,0x18655154d186986,0x351455]⟩,
  ⟨30,8,[ew257,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [550,395,35,47,124,551,11,307,262,23,272,39,26,302,5,34,182,9,552,20,308,327,121,55,2,123,325,7,24,274,334,365,354,332,336,29,553,285,287,366,310,288] [0x30c041663055104,0x30c04128a055,0x20801f08205528a,0x1f20801a08201a,0x34d04124905534d,0x1600c305524901a,0x38e1610c316138e,0x9641864a23cf160,0x28a4a21866593cf,0x4128a04030c044,0x8404720804430c,0x47082044208044,0x249045410047247,0x474c7047407041,0xc30444d30440c4,0x473c7044184047,0x820443c4047187,0xb08b00b20800c,0x24a00b34b00c208,0xb24b00a34d04a,0xd40144d300b0cb,0x143d400b4cb014,0x6db01c3dc01c6e6,0x1d5a700234d014,0x39100259601d35d,0x238e0020c2011,0x5d10023c20110c3,0x25d70113d1011,0xd01506281560c3,0x4905d0156618150,0x1861495c91491a9,0x14e78e498186490,0x49879e14e186]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew292],lh 6 [418,554,407,9,2,11,398,282,35,6,7,329,47,274,5,23,296,307,1,29,304,279,20,262,327,272,124,28,285,365,325,354,332,432,328,476,27,519,440,555,294,26,421,278,302,127,34,123] [0x653013853050650,0x535d3010010053,0x20804b5cb00b222,0x908d004b3cb013,0x10b08b08b0503d0,0x5459409432404b,0x95105415408b30c,0x194194051151191,0x61171199105a61a,0x190c371a9da051,0x5d70072070075e8,0x73c7009492019,0x3070093c9007492,0x930c009589007,0x289007147007596,0x728a009145009,0x6c802a029049609,0xd6cd00d492008,0x58d003383008492,0x358300d38e00d,0x28300314300d28d,0x874800d14d003,0x788003743003783,0x9512b09b38e008,0x29509b104095395,0x18f28f00f145195,0xac04f60f195155,0x18e28e1841440ad,0x7cc18428418e14e,0x847c408480408c,0x1ae04a60a08c80c,0x1af]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew273,ew113,ew114,ew292],lh 6 [47,35,329,124,7,9,11,274,418,285,282,2,398,296,407,307,5,29,23,284,279,20,395,283,262,554,28,24,272,517,325,520,332,328,21,6,287,421,399,1,278,127,123,327,336,34] [0x35171144944d70d,0x602081851151348,0x349342482441042,0x8364308e08d48d,0x5420c90c2642089,0x800835550c00c2,0xcf18f3c93c3183,0x58f3c93c35830cc,0x29861c0410c90cf,0x28822271860a04a,0x22329928e69a288,0x5c05d755528028e,0x6db1245c65ca54a,0x2256d66d71046c6,0x1da1c74e605a689,0x1c72070480414d3,0x71501412011c8,0x1c41c50051d0407,0x47186144145185,0x78115d14578505d,0x4d04082274d94c1,0x5132cb5105142e8,0x194484492186504,0x3800093a9496494,0x30e2cb38000e2cb,0x5ab30410c26a30c,0x40410018030cb19,0x2c07c0004010186,0x58402000b7cb2e0,0x24cb44]⟩,
  ⟨30,8,[ew293,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [559,35,5,560,282,1,556,262,398,124,29,28,34,6,272,296,20,9,47,279,325,2,334,24,23,0,327,123,307,274,365,354,332,557,558,336,11,433,477,278] [0x2496e128a19a249,0x145d719a28a89b,0x38e0005d700038e,0x141c701e041014,0x61801e1c7014041,0x146180142cb000,0x4100df0822232cb,0xdf4100e00820e0,0x38e2086e419a596,0x18a38e00a94a189,0x4118a1c7009009,0xa0411891c7009,0x2cf0cf98f18a2cb,0x18f40f0ca0ca18f,0x4921894100c9489,0x21c30c18f64f0cf,0x4120f30c19c65c,0x40440041c700e,0x2c400d14500e1c7,0xd2cd004145004,0x48d00d40d004484,0x430400440400d,0x400d30d00d00d,0x1d1450072cb004,0x9100114501d2dd,0x1082001481011,0x651001301011491,0x1641011311011,0x930d35670c5082,0x2133130c55550d3,0x2130053052050c5,0x202582215315213,0x215596202302]⟩,
  ⟨30,8,[ew109,ew294,ew110,ew111,ew112,ew113,ew114],lh 6 [403,561,354,47,11,272,369,124,35,20,26,28,9,262,302,562,274,34,39,308,121,5,182,327,7,55,563,564,385,24,23,334,279,365,325,332,336,29,287,366,310,288] [0x1470020250075c7,0x14500128a007,0x20700630c00728a,0x6208007347007,0x806006386007807,0x24900738e006,0xc30062490060c6,0x1c451006106002,0x14500644601c11c,0x14504128a017,0x20806134d01728a,0x6120806234d062,0x2cb3cf38e3e32cb,0x2493e338e3cf,0xc30172490170c3,0x6db4516a4104082,0x2086a44516db104,0x5221205234d04a,0x2cb05239204a34d,0x522d2045385045,0xd30932490850c5,0x53113005245093,0x61805d11d05d626,0x505270482cb053,0x54c0485140502d0,0x905550900d008c,0x64c05061008c0c3,0x5065904c60c04c,0xd60963e80940c3,0x696656094094096,0x1043de65e3de129,0x957d5083104696,0x837df095104]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew275,ew282],lh 6 [35,406,5,7,9,304,386,302,6,28,2,24,370,20,47,32,307,329,274,262,356,121,182,127,23,566,407,361,273,490,325,493,119,327,296,287,26,366,310,288,565,567,496,568,569,34] [0x4052cb1411502d0,0x4d14404504d0401,0x3071d1251400011,0x14c34c4471cc24c,0xc530e38534514e,0x14114c0c3301305,0x157057141141041,0x4d32c0017062141,0x2071cb4d3180006,0x3882482c71cb249,0x34d20e2083482ce,0x5030c81881868cb,0x708048506908048,0x252495940249706,0xe004084015552,0x1000c010e100082,0x1800060040c4106,0x6004184106100,0x48474411e112752,0x9658a99508249e,0x6289d60d654a296,0x60f64f3d43d80d8,0x68f1d71c9649269,0x3eb3c76871ea1cf,0xc26c2083b0d50d,0x6c209908a6ca343,0x9a08a7ca299282,0xb4304329a2827c2,0x61814803043186,0x41841]⟩,
  ⟨30,8,[ew258,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [570,406,24,47,26,302,35,262,120,574,5,334,7,34,274,296,571,28,124,23,308,55,20,9,327,182,127,332,325,39,121,2,365,354,573,29,572,367,366,310,288,575] [0x1040416a30583cf,0x104041082058,0x1c7020186058082,0x201c701c18601c,0x1456a445141b145,0x8a10c341b4d369a,0x28a41b0c341b28a,0x4130c0582cb8a1,0x8f05830c01c2cb,0x4108204010404f,0x1a504f1cf04f104,0x4f1860481c8048,0x4480481480524d3,0x48588052145048,0xc30525960520d2,0x4934d052312048,0x18605234d04130c,0x1d19d01d1c7004,0x4510041440041c7,0x4444002142002,0xd40145960020c2,0x14354002582014,0x314002342042302,0xe7a6006451014,0x29700679e00e14e,0xe28a00e0ce017,0x55700e34e0170c3,0xe55501734d017,0xd94197e74050c3,0x2595594057df419,0x2452532d3253a68,0x24a2cb243543245,0x2432cb24a555]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew275,ew278],lh 6 [418,407,11,2,7,296,9,576,288,6,35,329,287,5,29,274,304,1,20,325,332,262,336,47,127,421,540,493,436,328,491,454,565,575,494,577,578,26,302] [0x30e00e70e1c5305,0x1ce18e0050051ce,0x28a1cb54b00b29d,0x457851cb20b00e,0xcb04b04b1c5205,0x1d00d00505d71cb,0x7d01c508504b5cb,0x6058451d0082810,0x1048c58851d0110,0xc18664e90e1c5,0x55500028a000555,0xc20c00945100c,0xcc00920900c451,0x90c900948900c,0x251c908900c492,0x91090004d3016,0x20a0191040094c9,0xf20f00f45100a,0x48f00634600a451,0x648600f34d00f,0x68600608600f68f,0xa10400f082006,0x4ca0061060064c6,0x410c304834d00a,0x5140480c304134d,0x48508008082041,0x5a61c8108058082,0x4d50d043083596,0x6d204350304d082,0x436c3043103052,0x1020004d3052104,0x541040024c2002]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew275,ew292],lh 6 [9,418,2,407,47,6,7,274,307,35,28,5,296,24,329,1,29,304,279,23,579,406,580,127,124,262,20,421,490,325,493,123,437,328,492,27,524,567,496,581,287,272,278,288,302,11,327,332] [0x31035042040c145,0xe389850010301,0x32230e28e40924e,0x8ce08e38338c28a,0x191384111091444,0x454448188224211,0x30858822520c58c,0x548226218558317,0x5964d000627608,0x3453cf359641249,0x10d14a28d3cf34a,0x35a34510515a14d,0x154186141141068,0x5b155154069156,0x1ca1c73cf24a29b,0x2c710700b0093cf,0x401c61c01041cb,0x1c11c7047006000,0x247047001000040,0x74901c00074025c,0x4844920aa284109,0x4d306b48648a082,0xd30c30d25124c6,0x5c3b135535c35d3,0x8b0cb2c62c2502,0xcb2c32c20c2086,0x8308478408308b,0xb46586103102782,0x56e7d47c6546041,0xc3bd6]⟩
]
def nodesBlock16 : Array Node := #[
  ⟨30,8,[ew295,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [585,6,7,407,582,262,11,586,282,35,2,20,296,274,5,29,182,329,302,9,272,304,325,47,121,307,327,127,32,365,354,332,583,584,28,334,336,438,27,525,366,310] [0x30c6e03cf11a30c,0x1651411a3cf85b,0x41000514000041,0x1614501d249016,0x41001d145016249,0xde28a0c36e211a,0x2cb0df28a0df2cb,0x160820001860de,0x411e40820161a3,0x10f04100f94f10c,0x24910f14500c00c,0xf249111151011,0x71c0cc48c111711,0x1112d10d149210c,0x5d71152d50d55e6,0x1d99d91150950d1,0x2491d51d5119099,0x8248008145014,0x8001492014154,0x1001008488008,0x5c10012c10085c8,0x81880082cb001,0x82001186001081,0xd628005485008,0x39300561800d48d,0xd38e00d2cd013,0x19300d08d0132d3,0xd18d013093013,0x3900d02a90d838e,0x1d00900d828a0d0,0x1901c70821c7186,0x1ce08e1ca18a010,0x1ca08a1ce18e]⟩,
  ⟨30,8,[ew109,ew296,ew110,ew111,ew112,ew113,ew114],lh 6 [413,365,588,124,274,589,2,47,11,34,24,9,28,329,26,35,182,587,302,39,272,308,5,327,121,55,10,325,20,7,23,334,354,332,336,29,337,167,287,366,310,288] [0x28a00102300d5cd,0xd28d00d38d003,0x3c30002cb003383,0x13cf0032c3003,0x30c011410003303,0xd18d003403000,0x1c70031830031c3,0x1a24900320300d,0x28a00324901a21a,0x8228a08238e09b,0x3cf00010409b38e,0x413cf017104017,0x30c09b49201730c,0x460186017492000,0x1c74611864611c7,0x145249162208460,0x104162249145208,0x531130530a404e,0x30c09349304e04e,0x93313094494094,0x195095725094194,0x9525509471c095,0x75d08a24a08a766,0x4462704f492095,0x58b04f618004484,0x445960441c404b,0x64b04424404b1c7,0x4465904b24b04b,0x1d04501a84581c7,0x150650458186450,0x20815e65e15e229,0x1567d6146208150,0x1467df156208]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew297,ew112,ew113,ew114],lh 6 [415,124,9,365,5,47,590,35,354,39,121,11,592,272,28,7,55,591,26,23,334,308,182,327,302,24,325,332,336,29,337,287,310,288] [0x34d006492001341,0x82001481000,0x1c70010810011c1,0x301d0015c1003,0x4d301128a0014c1,0x104001281000,0x145001104001141,0xc5140012c1008,0x920015010002cb,0xc90890c919e0d2,0x18918d68d0d20d2,0x18d18d189689189,0x61818d38d189609,0x20914918938e18d,0x109215155215104,0x1993df1952d5209,0x21953cf1992d9,0xc70c70075c7002,0x2820c73870025c2,0xc728a0c23820c2,0x1040c7147002102,0xc73c70c21450c7,0x4100c23c20c2402,0x45128a45b38e0c7,0x10445b28a45138e,0x17104017145000,0x41031c3cf208145,0x31c41030c3cf30c,0x15621646020a145,0x31641620a20a216,0x2cb3134133132e1,0x2045042052cb316,0x2055142042cb]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew278,ew287],lh 6 [35,417,11,1,347,47,376,9,5,26,369,39,120,388,262,23,20,308,2,272,307,421,24,593,267,418,540,273,466,332,269,327,304,337,287,577,594,467,595,288,302,34] [0x5044c41092544d4,0x38c300004384509,0x3013043c410010c,0x14c40c10110c3cf,0x8a30530a40a285,0x28128408410110a,0x295055281281041,0x3a1240255060281,0x2c32c938e2c02cb,0x2cb3cb4c30d33cf,0x40b4454514102c5,0x5825968e244244b,0x4d3916457451191,0x9496196095494d7,0xf018998259249,0x2000c31cf3c70c7,0x4920080004801c8,0x1c61c7087006007,0x1c75c7006000080,0x64039a3805c01c6,0xc80ce64e01a000,0x9c348334820d492,0x43182083343186,0x6cd6c3043186a03,0x48808220d212082,0x34820d205345486,0x15d15071014d148,0xa4204241d405705,0x5f786782042346,0x417c1]⟩,
  ⟨30,8,[ew260,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [417,598,29,596,274,23,47,11,182,599,272,334,124,39,2,308,9,35,20,5,327,26,262,121,55,421,325,34,302,24,267,365,354,332,296,597,336,337,287,578,366,310,288] [0x79e000662014082,0x65955566328a0da,0x10405f4510da28a,0x5f1040da4510da,0x208000145014208,0x260186014145064,0x38e26118626138e,0x1c70142cb260,0x28a0141c70412cb,0x228200255500c,0x44c00210200c54c,0x244200c10c00c,0x145009208002142,0x2482002202000,0x18200c49200c18c,0x12cb0021c2002,0x1040022c20001c7,0xcd10d0cd5a50ca,0x14a0cd70d0ca596,0x24d1450ca71c24a,0x18f24f4920cd18d,0xcf6cf24d48d0cf,0x4f0dd6dd05d9e6,0xc45e805614504f,0x4d00d65d7044144,0x444d30c4184050,0x6100446c40d0186,0xc46180506d00d0,0x1882483a9257186,0x4860825738e248,0x1c70456050051ea,0x532d304e1c7048,0x4e2cb0531c7]⟩,
  ⟨30,8,[ew109,ew110,ew111,ew112,ew113,ew114,ew278,ew292],lh 6 [47,418,23,9,2,11,35,282,6,307,407,304,329,274,398,5,1,29,296,417,262,600,421,124,24,20,272,540,127,466,332,123,465,328,502,27,538,594,467,601,294,26,288,28,7,327,325] [0x491611460452618,0x50c306851511481,0x4a248c08c44618c,0x8cc64c30a312082,0x14b30000b64b2c0,0x2ce2c914926424b,0x2c954926524b54b,0x4c92662574d72d6,0x1d4a1a0c35e75c9,0x1c8410694507187,0x72020874101c2,0x1cf1c800820f207,0x1c8145201207147,0x562012010411c1,0x182096069213216,0xc641034234d410,0x34f3cd00d0cf,0xc10c3143341343,0xc304318118d14d,0x4319b1860460c1,0x800060460db0c3,0xa8210428000a104,0x54238514228238e,0x70a7024c238eac2,0x10f14f3ca3c4144,0x28410a10028010e,0x11e10074000a004,0xb0554501e004744,0x4ed7ce7c54c528e,0x41b95]⟩,
  ⟨30,8,[ew298,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [418,274,26,11,2,7,604,605,602,296,267,329,1,35,5,23,47,304,28,9,279,29,325,262,20,284,307,327,421,365,354,332,603,558,272,336,503,539,399,278] [0x55572024921b555,0x21b08221b24985c,0x4101d34d000722,0x1d04101634d016,0x3cf00030c0163cf,0x1de41001630c1a3,0x1041df4101df104,0xc30161451de,0x2890160c3186145,0x21528a015082209,0x34d209041009082,0x934d20b04b00b,0x30c1c990920b30b,0x20b10b1cb1cb209,0x40b2111111d1410,0x19a95a2110d11cb,0x4119119121a0da,0xa04a00a5ca002,0x4920023020025d7,0x249200030c007,0x10a00a60a002102,0x20c200261800a,0x1420000c3006145,0x1666017492002,0x393017659001481,0x138e001601013,0xd3001141013613,0x10c3013145013,0x3941d41271d938e,0x1941541d91041d4,0xd418f14f00f0c3,0x18e1451840c4194,0x18414418e0c3]⟩,
  ⟨30,7,[ew270,ew111,ew271,ew273,ew113,ew114],lh 6 [371,35,606,11,47,350,262,34,39,5,608,329,26,7,9,607,304,308,325,269,327,119,2,29,272,28,20,0,274,21,364,368,123,395,609,312,347,610,611,328,27,612,613,285,614] [0x702002186018718,0x49d018186002,0x65900248200265d,0x221f56051f4de,0x5824de208842502,0x54f58f4cf104542,0x1c728f0cf142104,0x2a634d5620c3962,0x5c10012e70065d7,0x13010062cb001,0x208006306006206,0x110100e24e001,0x1c100e10e001249,0xe1c700e0ce001,0x2230125230010c1,0x1220884b50b00b,0x25015012814b249,0x29035014b104150,0xc34e434da641c7,0x15169a14c10c297,0x1d114c68c151111,0x82c1c7aea34d291,0x6c92960c328c0cc,0x2966db1490c3149]⟩,
  ⟨30,7,[ew270,ew111,ew112,ew271,ew113,ew114,ew275],lh 6 [120,6,7,5,26,9,302,312,29,262,35,274,2,121,47,308,434,426,20,329,304,371,39,182,269,296,368,119,325,327,406,127,367,28,310,615,613,616,175,617,11] [0x2802c000a819145,0x6c000668141a64a,0x7001701046040,0x40300047040700,0x44000e00130c04e,0x20016c1042040,0x174104f040740,0x1862cd2ca18a00f,0x2d32c920828d34b,0x2450c52534cb208,0x8914c1490c324c,0x255245082155149,0x58510415614a10b,0xc379e84d4d3296,0x18c3170d75cc88d,0x3510824508c6086,0x10495090d104351,0x50e388492190190,0x99409420e214494,0x6182112070871e7,0x7c41076071c41df,0x834030c2092452,0x1030cf0ce104482,0x555a023cf38f3c3]⟩,
  ⟨30,7,[ew110,ew270,ew111,ew112,ew271,ew113,ew114,ew282],lh 5 [302,274,26,29,47,370,2,34,9,35,7,312,368,350,319,24,337,610,167,273,386,500,296,40,28,618,619,320,584,317,11] [0x5ac4088849825e5,0x989475084690862,0x194740158c48525,0x4162a8b521885,0x420280991708469,0x18862600142021,0x1b9c41e800680f9,0x310fd3f06369f67,0x1e39884]⟩,
  ⟨30,7,[ew110,ew270,ew111,ew271,ew113,ew114,ew278],lh 6 [11,262,5,9,29,2,304,1,501,120,308,302,121,39,26,369,368,347,35,426,182,296,47,20,274,119,417,312,269,421,327,350,272,337,167,615,613,620,332,500,618,34] [0x84e48e69a80e54e,0x1db38104d48d341,0x70410d1c73446c8,0x5ca58a29788d58d,0x4c88ca00a357,0x94890a2ca288288,0x4950c33883882cb,0x1c7552549609252,0x9841091c7244248,0x24f14f3c2089149,0x104289cf00f242,0x40b41d6593d33d0,0x1c110474b2d0650,0x83047058104607,0xc50c1082045043,0x32030c00c1201,0x2cb0cc0c12c1040,0x18514408204c303,0x64c6105146086,0x786180191711440,0x18c19179144c446,0x14200009f085000,0x30c09409630c153,0x7d3a40514594502]⟩,
  ⟨30,7,[ew110,ew270,ew111,ew112,ew271,ew113,ew114,ew287],lh 6 [26,47,9,35,296,302,34,262,20,347,11,621,312,371,368,623,272,337,612,182,167,617,622,504,307,558,366,342,23,310,273,175,29,317,7] [0x134802cb440400,0x54000150024030c,0xc20c258000d006,0x4460411714438e,0x64410d10a1843cf,0xc21c30c76c5685,0x1c20870c2083083,0x286285141741705,0x24625f048048785,0x1880412011a1060,0x22]⟩,
  ⟨30,7,[ew109,ew270,ew111,ew112,ew273,ew113,ew114,ew282],lh 5 [47,2,34,24,29,28,26,274,9,7,35,40,312,320,21,350,285,307,328,610,127,406,287,272,302,288,11] [0x630859916b91223,0xa11ad11081010c4,0x30c7528dce51d43,0x29cb71887600403,0x420483850a31cca,0x10401060c7420e7,0x10401040a579459,0xa449140c67a449,0x1a48400]⟩,
  ⟨30,7,[ew109,ew270,ew111,ew112,ew113,ew114,ew292],lh 6 [35,11,47,7,5,282,6,9,329,1,26,28,279,554,39,304,312,2,327,29,272,308,285,274,23,262,434,20,296,418,328,613,27,175,302,34,430] [0x79365374d713513,0x6084c0008648200,0x20d20d61868d7c8,0x8f6cf3c28086c8,0x5040d84f04f202,0x40a40d4923cd3d0,0x145d458a290490,0x2495005055c5140,0x18b2c524914b146,0x86451182185445,0x41183185045142,0x18a18d4921430c6,0x2402cb58a286486,0x1070092572cb5c9,0x1c21c0104002087,0x470c71c11c00c3,0x28a1ce1c0280001,0x31144b10400e387,0x4c0cc2d144c10c,0x38c3013090c3241,0x10310204159a88c,0x10238e0830c4044,0x55509554438e115,0x5a48c3]⟩,
  ⟨30,7,[ew293,ew109,ew270,ew111,ew112,ew113,ew114],lh 6 [34,308,35,47,282,329,0,1,279,5,9,28,272,6,312,2,29,262,23,304,39,20,24,26,556,274,624,327,325,430,119,11,285,296,559,614,294] [0x40138e05005b38e,0x59604c05a5966d0,0x51150128178c301,0x201481051454094,0xd404805c492708,0x5d55410c3055057,0x85030c7607d7017,0x445142090451898,0x6988c5485402085,0xc5545158158492,0x1931431535534c3,0x4c000e18e380013,0x8464410290c64c,0x1c710b10d1c7302,0x3433443c434b2c4,0x3441841030cd3cf,0x2cb10000d186340,0x871d92cb6471c2,0x2822490830ca24a,0xa286282000283,0x20f3cb24908618a,0x1c80082cf3c8248,0x21d2070001da,0xc6189009246243]⟩,
  ⟨30,7,[ew109,ew270,ew111,ew112,ew279,ew113,ew114,ew275],lh 5 [35,302,24,26,274,7,9,47,28,2,180,312,29,319,625,395,287,13,356,71,296,123,27,175,21,6,32,288,626,269,167,0] [0xaac280ac0401282,0x1b18f73aec6b6cb,0x49c591205801004,0x21003109e514207,0x318a6528ca00140,0x84e90e82031800,0x9262988508084bb,0x1ce6538fa391785,0x1f19c7e]⟩
]
def nodesBlock17 : Array Node := #[
  ⟨30,7,[ew109,ew270,ew111,ew112,ew113,ew275,ew278],lh 6 [11,35,288,7,6,5,2,287,9,329,304,26,576,47,1,39,308,434,274,29,262,325,418,20,312,127,119,356,296,328,615,27,175,336,421,464,558,302] [0x75321358c7131d3,0x894c1049509241,0x24c24c08244c789,0x34a5ca28d7c9189,0x28b28c00024d,0x60c80a0ca64b2ca,0x50749228c2980d8,0x38e1d41d6492594,0x10208738e1c21c4,0x1c4186117107187,0x410b10c0001d7,0x10312269a84b2c4,0x3810829030c48c4,0x14804e05208248e,0x206201145046048,0x3c82cb20f2012c1,0xc32152010c104f,0x446182145055048,0x913cf086191145,0xc36400023cf080,0x1501460006db942,0xcd44d190405000,0x550343345445143,0x403400540003010]⟩,
  ⟨30,7,[ew109,ew270,ew111,ew112,ew113,ew114,ew275,ew292],lh 5 [29,9,47,35,28,7,1,24,2,20,40,319,580,406,287,71,26,296,328,616,23,175,127,627,272,558,434,285,302,11,123] [0x100149814a90220,0x36c003005a816b,0x1208621861186e0,0x3b7073b0a773848,0x9423404c430f27,0x4106108c6108c61,0x1709b2688531082,0x289291092913de5,0x10878bd]⟩,
  ⟨30,7,[ew295,ew109,ew270,ew111,ew112,ew113,ew114],lh 6 [7,35,6,11,282,29,302,26,9,2,5,39,272,20,304,182,262,308,32,274,582,47,327,628,329,312,121,285,434,325,584,337,28,296,585,328,175] [0x1477871c51d6516,0x3071c21d730c585,0x2d07c72076c2087,0x80b18b1d040b20b,0x55144d34b54b71b,0x7400110d12cd2d1,0x84508244001d0c3,0x4186018c5410894,0x706185485141058,0x545345146194492,0xe15514e34e395,0x39439901965490e,0x3044c410104c4cc,0x484106102492301,0x8d084244086084,0x840c410d102249,0x1861000020c3080,0x5a6931934da4c1,0x20128a049048288,0x8203201001209,0x3c924628a043048,0xcf00f18918f28f,0xc33c33d70005c3,0x24000a0ca280289]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew299],lh 6 [47,9,329,11,274,2,272,35,302,296,23,26,29,304,34,455,39,28,308,5,182,262,307,7,24,55,334,20,327,504,453,121,325,332,471,328,13,27,124,554,337,167,287,267,366,310,288,32,0,439] [0x2cc18c30b2c9189,0x5420878cc54c24b,0x2482422823071c2,0x942902088209289,0xcd08000d6cd340,0x34e3960d658e38d,0xa0b1c73e7996716,0x2102d55501d0415,0x411446206191450,0x6d201249ba46006,0x398617a9239219b,0x3ddad87184975d8,0x7c420411fb07451,0x4d31001014c11df,0x590445c4040004,0x4f7621196415c1,0x760801741060,0x205154014505b48,0xca64a283b94654,0xc33debca70a503,0x15a6930c34da4c5,0x84578516114f7a2,0x3f1c1a71a7a1]⟩,
  ⟨30,7,[ew300,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [35,5,9,26,24,302,0,307,47,29,509,23,329,296,304,308,2,182,272,462,28,20,121,556,325,439,327,262,39,274,336,332,32,334,455,337,167,366,310] [0x2571c75c925a1c7,0x1042830d8104689,0x60000a0826030ca,0x15e2cb280018082,0x417851532e0645,0x4c821f0417c8213,0xc710466285a186,0x821c30c9104243,0x24000c08c300009,0x30d50d34514c50c,0x4e38820d04d305,0x1d71ce18e34834e,0x8c3000397387187,0x1430db6dc01c71b,0xd40d2152494503,0x54f20f3d5912212,0x18410a10f18f495,0x7569401453ca3c4,0x204201659d15d,0x280095080041015,0x6002282086080,0x411051450996041,0x18b2d32d1191590,0x4605065045944b,0x4064014c1]⟩,
  ⟨30,7,[ew300,ew109,ew110,ew111,ew112,ew279,ew113,ew114],lh 5 [29,26,35,24,9,302,23,347,47,182,2,13,0,5,34,621,321,180,327,336,307,27,337,6,167,366,342,1,310,455,439] [0x1104408c2301c07,0x7394d5367249926,0x19200104008c23,0xb04073800aa8280,0x84301b8423185ef,0x88851d172508c61,0xe17651108220844,0xeb10b42ca6314a8,0xc5b11e]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew279,ew113,ew114,ew282],lh 6 [302,29,26,34,35,9,13,274,47,28,2,312,321,180,356,308,328,307,27,7,296,337,6,167,287,272,366,342,32,310,288,350,285,455,439,332,336,11] [0x10474013c12cb,0xc104a481441009,0x242087547501053,0x60230c5c2582080,0x10d6c0689642083,0x105144144105344,0x87407001c5147,0x20680001f003780,0x92388e0e10ce206,0x94328618a206183]⟩,
  ⟨30,7,[ew109,ew110,ew270,ew111,ew112,ew113,ew114,ew299],lh 6 [302,29,26,9,47,1,11,34,35,2,40,320,28,7,317,312,296,328,182,23,27,13,629,272,337,167,630,327,558,275,325,32,270,350,0] [0x4a29105004204f,0x2c70415540414d2,0x820d809709604b,0x1cd08211908c00c,0x1401480c80da08d,0x6c7187184244240,0x2032040c500501c,0x10901e0c37460c3,0x18e39f000145000,0x221a1104804]⟩,
  ⟨30,7,[ew300,ew109,ew110,ew270,ew111,ew112,ew113,ew114],lh 5 [47,35,29,26,1,5,9,0,28,302,347,2,274,439,32,40,325,269,356,332,336,34,312,296,272,337,626,455] [0xa4db21c4701284a,0x14057392409826,0x13de115c4315aa7,0x1894a100a02a509,0x14084a1230e438,0x22081605833e865,0x6102d3ece058168,0x2c0131826080c4,0x29c08210eb]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew301],lh 6 [32,23,272,9,5,274,2,329,55,296,7,35,24,307,29,304,20,34,39,308,26,47,631,325,632,453,327,262,448,336,332,328,27,337,167,11,464] [0x50e082394389082,0xc71cb7ce0ce254,0x25624700738b2c7,0x8071071d61c9000,0x28f1d554f40f3d5,0x3d144d28d35144f,0x24d68d356349689,0x2d249b8542cb256,0x8109201251b6d2,0x882542481042002,0x4530904135534d0,0x4ca28c44c30a313,0x8c5cc3183025c2,0x4514000b041098,0x1501431032c0005,0xc52850d00c5104,0x6051482032830c8,0x1571436030d70c5,0x180100006181104,0x201059040200046,0x5904074001c001,0x10620601c001741,0x64618a18420810a,0x19e18464411e106,0x91c8c8688]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew282,ew278],lh 6 [288,9,35,11,2,34,287,500,47,304,7,308,332,29,329,274,5,334,26,20,39,1,453,307,576,262,537,55,356,27,296,127,337,167,272,273,633,32,464] [0x48d18d352497197,0x4e38208d04d5d2,0x1d81ce00e34234e,0x747107398387007,0xc91c82094c9248,0x1c51c92897d8789,0x81208224514728a,0x554499654094519,0x500006546180014,0x4cb20b2d3846206,0x14b8da88b0cb193,0x2ca28614518a18b,0x54f00f3d5542000,0x410093081401095,0x4304f68f053042,0x422823c33c1681,0x41009b6c128105b,0x4116410584100,0xc030000301630c,0xc471c940145903,0x10c1080c320c204,0x444145111108145,0x9830d144c58c211,0x311443]⟩,
  ⟨30,7,[ew302,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [35,272,32,26,11,2,47,329,274,5,296,29,545,34,9,55,304,308,262,7,582,325,334,634,327,453,307,39,20,24,23,354,332,336,455,337,167,287] [0x2d428a50b2d828a,0x413030d504160b,0x54000c2085430cc,0x79809e300015208,0x14580619f145662,0x5d65a11047c61a0,0xca041856597104,0x2082830cb0412c3,0x2c00072071c000b,0x1ca082294287087,0x1504061871471d4,0x68d3501101c61d0,0x8c300040d35a11a,0x830d249b01b6d2,0xcc0c108104c043,0x71119145c901181,0x35d75395135105c,0x2020923124534dd,0xe24e002088308,0x340386380249006,0xf3ce34e38f380,0x142249085099249,0x3cf5c41023cf645,0x253245104084117,0x153149104]⟩,
  ⟨30,7,[ew302,ew109,ew110,ew111,ew112,ew113,ew114,ew282],lh 5 [24,29,9,26,35,370,32,2,47,34,5,55,621,635,274,302,356,464,327,332,27,296,337,167,272,636,633,455,453,317,11] [0x208821806009425,0x9c9715c14751de6,0x94a10888118060,0xb02a1094a109e81,0xc07b806000d8c,0x110826b4c4c0060,0xca0c87084e20844,0x3a13d4f36632746,0x1e49d08]⟩,
  ⟨30,7,[ew109,ew110,ew270,ew111,ew112,ew113,ew282,ew278],lh 5 [29,26,288,47,11,35,9,2,34,274,1,320,621,321,7,350,312,307,618,27,5,127,55,287,337,167,273,336,119,464,302] [0x148003141100410,0xad7605400a4c00,0x6e4215082c66037,0x515254b90e0e82d,0xea39b20ce338942,0x3192628cc512448,0x111e719c65318a4,0x78ce719c8327844,0x2084]⟩,
  ⟨30,7,[ew302,ew109,ew110,ew270,ew111,ew112,ew113,ew114],lh 5 [29,11,47,26,32,9,35,2,34,7,285,274,319,621,321,327,584,325,634,356,336,332,23,312,296,328,619,272,337,167,453] [0xad2721a8710400f,0x4044711ec4314c5,0xb90600305d01,0x1a028031820009a,0x774632286d6f07b,0x22886599694250e,0x590c90a422388fe,0x11c41294c5308a4,0x20a42148487]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew303,ew113,ew114],lh 6 [11,5,272,274,0,307,9,296,6,2,28,35,638,329,304,121,180,182,26,47,20,39,29,302,24,637,325,439,327,262,354,332,336,328,27,337,366,32,462,464,310] [0x496618592485618,0x18d34b856196152,0x1d75cd28d58b2cd,0x1c5705357347287,0x471591477071d9,0x1d34ce50e393887,0x38500515914e00e,0x2d555d8d22cb399,0x8a2955d549d755,0x8868854a2825c2,0x4c220c20268208c,0x945084d3214202,0x8800020c202002,0x2830cf90b28a08c,0xda0d03102cf3c3,0x40604641a403303,0x303194190041414,0xc00c6306180183,0xa0f0419e694f70f,0x1113c9251051449,0x44045b1046c0011,0x25f0417c925e041,0x1046c0020104789,0x4410900980001b,0x244101001]⟩
]
def nodesBlock18 : Array Node := #[
  ⟨30,7,[ew109,ew270,ew111,ew112,ew113,ew114,ew278,ew292],lh 5 [23,272,347,35,11,47,9,5,304,1,308,2,40,417,639,315,640,296,620,287,421,285,288,28,127,7,123,26,325] [0x408409018c18a21,0x535021210411048,0x28409025ce18542,0xb6a10d024991ef,0x30e102992048141,0x5946630c6630c66,0x39c9805c0405965,0x2648539ca539cab,0x737a]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew278,ew299],lh 6 [29,9,47,5,26,272,274,307,296,35,23,40,621,321,641,2,11,34,328,124,337,1,167,287,267,364,418,288,302,642,466,332,643,327,464] [0x2002cb480200108,0x71c0003080008,0x30c5044c70071c0,0x5c534d585105155,0x18960410514438e,0x181046046181246,0x3c2681059241049,0x9d29c29029b3c2,0xc37820c30820c3,0x2286041145f]⟩,
  ⟨30,7,[ew304,ew109,ew110,ew111,ew112,ew113,ew114,ew278],lh 5 [29,272,26,9,35,274,47,5,23,296,11,2,307,621,321,641,644,645,327,455,337,167,287,288,32,0] [0x20c831044102409,0x106728a8c731e08,0x300094a08521441,0xa080c6000c6000b,0xb05cea8441409ad,0x28c8529041089ef,0x59883190a319465,0x32ce75610a45d66,0x19518e7]⟩,
  ⟨30,7,[ew263,ew109,ew110,ew270,ew111,ew112,ew113,ew114],lh 5 [11,47,29,1,26,35,2,9,7,302,34,28,274,40,621,321,646,285,327,455,312,124,328,267,337,167] [0x1a4e53967289202,0x1500a028c130469,0x12469135b615444,0x760972280a108c1,0x5208f7e48b4ac8e,0x304cb1ac6561588,0x284e360ca802001,0x181060982039ca7,0x102000]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew271,ew273,ew113,ew114,ew287],lh 5 [296,272,262,20,9,47,23,302,11,34,35,611,368,647,639,21,371,285,612,367,307,421,294,26,287,417,288,28,317,7] [0x63280012605ae40,0xa81ad48003280e0,0x186e1305ef73ac1,0x51a210c029c0425,0x20882111421284a,0x298e63644420844,0x38ca33ecc9368a3,0x18d1c444e782128,0x1d40ca5]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew271,ew113,ew114,ew292],lh 6 [35,47,272,11,5,6,9,7,121,262,120,554,23,28,296,369,368,302,1,279,327,182,20,285,282,501,613,367,29,407,500,26,34,474] [0x38b08264b68e08e,0x24a2806ce24e38b,0x74b70a30a38000a,0x28f58f3c104a58a,0xd040b78f0cf281,0x41140b5143cb3d0,0x2420005d1450510,0x492089258018609,0x14d34249208d085,0x85041156142042,0xc51471420c2096,0x5d97c54450871c5,0x24034001248934d,0x104001006106252,0x1831801c0181180,0x1804400030c61c6,0x104008206451188,0x3410531134c104d,0x4cc1cc3030d31d3,0x50c30830b5144c3,0x1071010c35c820c,0x1012080471c40c3,0x555055544208115,0x5e1803]⟩,
  ⟨30,7,[ew293,ew109,ew110,ew111,ew271,ew113,ew114],lh 6 [182,262,47,20,282,272,35,279,34,28,1,55,0,6,296,120,5,368,9,648,369,121,556,24,23,302,327,273,11,285,474,614,29,560,294] [0x38045100e01a451,0x5d74c51405c068e,0x541540180005153,0x13618001055186,0x826c71c0600007,0x6430c0082003015,0x7ce14579d719219,0x413963961454d6,0x38618f04f3c618e,0x8f0cf85680f24f,0x3143c20940d4502,0x508211311448214,0x44184101885185,0x28a10910d28a141,0x343344084349244,0x3442041030cd082,0x24911310d20d353,0x4a28624918a281,0x4814100430d2412,0x20848b481201483,0x1c208941004b2d2,0x2c7307242087407,0x2cb1cb1ca30c28b,0xcc3102cb40c303]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew271,ew279,ew113,ew114,ew278],lh 6 [296,272,23,262,47,11,9,20,26,302,180,5,649,395,621,641,35,288,13,376,367,29,123,2,500,337,21,267,167,287,1,650,464,34] [0x54030c500201200,0x5600117100580,0x5a38e64124000d,0x3dd04111c11b042,0x28341008804120f,0x1860c628a18a0c3,0x1c409e0831860c3,0x489082345091444,0x8094c57c54c7487,0x1472cb1c72cb149,0x21]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew279,ew113,ew114,ew287],lh 6 [26,302,296,347,35,9,34,47,13,272,621,371,180,262,20,307,5,29,337,267,167,287,285,366,342,1,310,288,28,376,455,504,325,336,7] [0x83085102089002,0xc20d01c33c30c2,0x24128a489443083,0x5400075004c0009,0x6015c158000b006,0x14414410530410c,0x68164134514d105,0x1c87010466c1047,0x8607cb19e19d1c8,0x88638820e1c6206]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew271,ew113,ew114,ew299],lh 5 [272,302,9,296,6,20,34,7,35,47,26,262,649,11,367,368,29,651,267,366,342,479,371,28,310,652,327,584,483,332,0] [0x1846f631c350143,0x14466398692a470,0x10002280052c4b,0xcc322008400084,0x109024204b42174,0x85380dc3610aa8,0x398e92a4b90b4cd,0x3f4a5e1cc72ef46,0x1e]⟩,
  ⟨30,7,[ew300,ew109,ew110,ew111,ew112,ew271,ew113,ew114],lh 6 [302,26,35,47,296,9,5,6,24,0,370,20,649,621,262,376,464,509,371,325,336,7,367,368,29,337,366,342,28,310,650,455,481] [0x8504804810a10a,0x51349101000f085,0x480485492c62c6,0x19810011730c584,0x35904428a103183,0xc70411c100800d,0x1a0011c70461c7,0x8508214e08239b,0xdd01c002145,0x25f2432c32c025e,0x31890e0]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew305],lh 6 [267,24,28,262,47,329,304,9,35,11,34,274,2,296,23,5,20,307,302,325,182,504,121,55,334,29,653,327,365,354,332,27,366,310,654,7,488,269] [0x35901965a64d00d,0xc514820d0c335a,0x352485085348205,0x7c53c515214d082,0x246144106406184,0x18a29125144a286,0x1916d145a4466c6,0x2000030c120819a,0x420404800430c0,0x1101002081492,0x280050040100010,0x15001281055040,0x14c10550404c0,0x8b2d6808082015,0x2c42c73c721658b,0x1cb28b1c410b3cf,0x7032d75c728a1d7,0xd30c77071d31c3,0x31411450c856104,0x5ce3893945d458c,0x3953824c250924e,0x3cc2490a208e4ce,0x75031860f2493d8,0x41e40c74c31e310,0x9648d86d8]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew271,ew113,ew275,ew278],lh 6 [7,47,11,288,121,262,287,9,35,6,5,302,576,120,296,369,1,501,368,407,20,269,332,2,421,655,615,367,29,500,26,376,127,584,336] [0x38c18644c68e18e,0x14d3486ce1ce38c,0x4cc70d0cd38820d,0x4f5cf3c104d5cd,0x9248c74f08f341,0x48b48c0003cc3d2,0x14620860b2d2000,0x410185191208445,0x2430c6410183189,0x509049254246046,0x2cb7d1789089194,0x6000092c9240251,0x1480c32104050c3,0x28a141147287150,0x1c21c86481c11c5,0x1c52c5202087647,0x28a1441072cb1c4,0xc105328a4c1043,0x835430c20a0555,0xc410c000842,0x296281082884103,0x110405604a082,0x10404000a104280,0x580002104080011]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew271,ew113,ew114,ew275,ew292],lh 5 [28,296,9,47,368,1,35,20,302,5,24,6,406,262,640,71,11,616,367,29,121,287,7,272,421,127,285,569,123,332] [0x1866108a410ae2b,0x230242042420429,0x48c05015a268a84,0x141855d5655523,0x108c6108ce70c45,0x2940338c06108c6,0x7ece80019a00320,0x4420341d0339c6f,0x751c]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew275,ew287],lh 6 [175,35,288,20,7,6,9,262,120,11,2,287,369,325,5,47,34,334,302,182,504,121,55,296,576,24,493,29,421,26,376,656,366,310,28,657,273,269] [0x5c02c0018017659,0x1c82010401805d8,0x212200080001008,0x3c80c8012008082,0x24c20f3cc0cc30f,0x31040024001000c,0x1cb04b7186cc10c,0x4922c71d4041507,0x14214b4922c2085,0xc53c514314b3cf,0x34d7947454052c3,0x7c4105345144154,0x5460861951870a0,0x3810430c63861d5,0x1961814011830c1,0x47107056586410,0x38e1cd1c110404d,0x54a2933934ca855,0x242582089093593,0x2499238821024c9,0x29144e24939138a,0xca68a284283683,0x35144445434d0c4,0x944111]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew271,ew113,ew275,ew287],lh 5 [296,47,35,302,6,20,287,262,9,7,34,11,371,269,617,367,368,182,307,334,421,26,366,288,310,273,336] [0x441001de0019c0,0x350005cc0128412,0x90c62106619c47,0x1d8692119521884,0x4204810907108e2,0x18c381dc6742122,0x6a9a1284b94ad4b,0x61421284a50e92a,0x254a]⟩
]
def nodesBlock19 : Array Node := #[
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew275,ew299],lh 6 [296,20,9,35,28,47,302,307,29,24,262,7,640,659,71,34,6,328,124,287,26,658,366,342,490,325,310,288,32,569,493,407,660,327,269] [0x8002440008210,0x71c0001140200,0x2832824870071c0,0x253045045106106,0x9711611525424b,0x820c30820cc301,0x18605a0590c3603,0x15c10610418d35b,0x4178504114e39d,0x228602cf3df]⟩,
  ⟨30,7,[ew306,ew109,ew110,ew111,ew112,ew113,ew114,ew275],lh 5 [47,9,28,29,302,24,262,7,296,20,35,307,319,71,661,662,327,455,328,287,267,366,310,288,0] [0x20946519c540d03,0x1963079c0902482,0xc8820c6190505,0x3050b5a06b58d8c,0x2cd2049444290c1,0x384c009855150a7,0x388160282151821,0x35a701042208f7,0x1838129]⟩,
  ⟨30,7,[ew262,ew109,ew110,ew111,ew112,ew271,ew113,ew114],lh 5 [26,6,302,35,34,296,262,7,47,20,9,621,272,11,663,285,327,455,367,368,124,366,342,32,310] [0x788c330c20081c5,0x4e4391284a230,0x2d0a22cca691801,0x12d66090e429528,0x21004000818c,0x518633585510021,0x4605710d4a1a863,0x390e84a12d23442,0x721d24]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew271,ew113,ew114,ew278,ew292],lh 6 [35,296,5,9,47,272,20,11,1,23,24,649,600,417,641,262,288,302,620,29,500,421,664,294,665,287,501,285,26,28,584,7,123] [0x4c12cb00104a48a,0x4c047501046101,0x1405c058104d541,0x645084085608148,0x83dc15b15a38e,0xc30030000cf,0x1842000c30000c3,0x35d249307210404,0x821860821de249,0x4601df1c4082106,0x11]⟩,
  ⟨30,7,[ew298,ew109,ew110,ew111,ew271,ew113,ew114],lh 6 [11,7,35,28,47,1,267,121,20,5,296,39,302,26,120,9,262,369,279,182,602,501,327,274,666,2,368,285,558,272,366,310,367,29,605,500,337] [0x28c70c30a316516,0x8c55b74c34d58a,0x3175c70871d778c,0x1470c71c51d80c3,0x1134d97c71076c5,0x5400130531d9653,0x34a18a4c0018041,0x40a28d35418654d,0x28208e40e38280a,0x10e20e89484e0ce,0x11384111211444,0x45445a01a6948d1,0x40b08b2d090d082,0x1452c32c6146350,0x18818b10b1830cb,0x460062c8206104,0xc3181055000601,0x4051420c3085150,0x3c224908820f24f,0x4f3c03c20413c8,0x48410324908000f,0x120520c4112252,0x480485041140,0x201049009241248]⟩,
  ⟨30,7,[ew307,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [267,28,29,35,7,296,20,262,302,47,34,329,274,5,504,9,304,11,325,182,121,55,2,602,327,532,307,23,334,365,354,332,488,24,455,27,366,310,288] [0x1570825c5158082,0x1c73a2858000605,0x7430d21c74830dd,0x219041388212041,0x1867c925e186488,0x38a29210478925f,0x8500548a2a0104,0x1c2157142002097,0x8308b1cb2c30c2,0x20504114814b04b,0x1904098cb18b2c8,0x68a2901102c9250,0x1ce0c340a41a11a,0x2003871c00c0007,0x104e208641040,0x18024000600e249,0x28a804100280646,0x31490304100410e,0x30f34f0d450c04c,0x10c3c63cc34d306,0x31554f10f3d53cc,0x5933534d695434d,0x55b6d1993553516,0x35c3564514d145b,0x59c70d451]⟩,
  ⟨30,7,[ew307,ew109,ew110,ew111,ew112,ew113,ew114,ew287],lh 5 [47,35,296,347,262,20,302,267,9,34,23,334,182,504,26,269,327,325,29,656,455,366,310,288,28,317,7] [0x62824091c710c43,0x8c16f5b4050158a,0x188430902410c62,0x2064210c6201405,0x99ca0280e651c81,0x8101354cda1ceb,0x58c44208142028,0x281394e0c64dcc6,0x1a49400]⟩,
  ⟨30,7,[ew307,ew109,ew110,ew111,ew112,ew271,ew113,ew114],lh 5 [296,302,47,7,262,35,34,267,20,9,285,24,371,504,649,11,327,558,336,325,622,368,29,667,668,366,28,310] [0xb0a42916b04410,0x30c48122726b02a,0x55ce28007a00c3,0x280661810205801,0x11daa39c2a0dca7,0x2143909cc33e047,0x912922484490a5,0x4090f33c2116c5a,0x330d0619862]⟩,
  ⟨30,7,[ew109,ew110,ew308,ew111,ew112,ew113,ew114],lh 6 [35,7,28,9,1,29,5,26,329,20,0,272,307,304,13,2,182,296,39,308,262,302,47,670,669,325,327,509,671,365,336,354,332,328,27,267,269,337,167,310] [0x1c52c51471d12d1,0x68515814c68c447,0x200845505318305,0x448088140008508,0x248215551082455,0x21658d24d356888,0x34c04c31830d04d,0x791b8c7687358,0x1d4512012494947,0x8b54b2c2092552,0x5934c998b58b482,0x5c10532932c9253,0x1d0c34c105b28a,0x1047400190c3640,0x78209c1045c209e,0x26038e80925f38e,0x28a5c105928a7c9,0xc410008264105b,0x3183004003083,0x400ce38018600e,0xa0030430ca0c0,0x3d019040f9c4186,0x4411c11005010f,0x18118f5cf417404,0x3c13c6706]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew272,ew292],lh 6 [7,35,9,2,11,282,28,6,385,274,500,47,5,175,554,10,23,34,1,55,334,327,272,262,20,285,307,279,29,398,26,537,278,302,521] [0x68d58d34e35a596,0x5cf3c104d08d68e,0x28e28f40f34104f,0x2ca0ca3ce3ca40a,0x10828b2880c820b,0x21120e55574e708,0x5d6041651448548,0x4925975c5045157,0x1c6185492146147,0x6072cb1d81c52c5,0x1071c01c5105158,0x65f787447140007,0x49189252481186,0x30c258242302052,0x84089009098089,0x81441244102002,0x30c0534c2451093,0x1830db31b6c3806,0x190010404106006,0x1036628504d0184,0xc000c104300003,0x5034c30d40cb4d3,0x54001450e5552d4,0x654500]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew272,ew275,ew287],lh 5 [47,20,9,175,262,35,23,24,34,302,182,307,184,500,287,273,386,310,11,7,2,296,55,421,26,672,366,288,28,417,269] [0x63143288a358c6b,0xb8ec36b6a305003,0x8020328ca21485,0x16b273c30779dce,0x120821104408882,0x4ed218c485290a2,0x4000f0c93192f,0x9ca48e840008021,0x1e42213]⟩,
  ⟨30,7,[ew291,ew109,ew110,ew111,ew112,ew113,ew275],lh 5 [7,6,28,47,34,175,35,287,11,32,120,274,262,20,307,673,9,369,5,2,325,296,545,334,493,23,273,521,558,26,547] [0x39cfad5ee702a0,0xa042039c01050e7,0x18d46328630180,0xc186b77ac8042,0x100f42303181ad,0x2bcae0878420100,0x518c5615cf71425,0x53d45114a62a98a,0x88c6a6a8af2a84a,0x290b1445431c5b1,0xb318131a2421508,0x388e14842c658c6,0xb42719c2211d27,0xf5ba1204ed38461,0x324cb12d6949842,0x80c6b949635c250,0x5a1702420882c8b,0x14e6918d3348863,0x4a1022084812489,0x9def22125794c84]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew272,ew275,ew292],lh 5 [175,20,7,9,35,47,1,28,262,24,307,500,406,287,34,368,2,29,127,674,272,421,278,521,285,302,580,11,558] [0x1de020c805000a,0x32405ae20040a0,0x94e63990441260,0x322a9a24496b425,0x191031886808cc7,0x308c1b048319083,0x288a20e4d835ce2,0x66c42d142129421,0xe77042]⟩,
  ⟨30,7,[ew295,ew109,ew110,ew111,ew112,ew113,ew272],lh 6 [6,7,282,262,11,500,20,302,274,5,34,35,55,47,9,334,175,2,182,307,10,272,675,32,385,121,582,327,28,285,521,273,29,586,294,366,310] [0x4ca14529329b145,0x55558000a54a6d3,0x3030ca2ca280016,0x70c1cc2830cc2cc,0x34f3c618c34c79d,0x3c13d610430618f,0x4130007c104f10f,0xd04da4d001041a,0x40b2d40d450b2d0,0x1c55c51471d45d4,0x19860d345185507,0x85a81805814d158,0xc22c20838952cb,0x1c20960801c7543,0x6002342016002,0x210208618034d,0x1c3081040104001,0xd96481c82198c3,0x38824920620e24e,0x4e384388048386,0x49191924920420e,0x497041651452252,0x1115c45d2052484,0x441449109241251]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew272,ew282,ew278],lh 5 [9,26,47,274,2,500,20,307,35,23,34,676,175,621,665,273,24,288,388,32,11,7,29,127,55,337,167,287,272,677,406,464] [0x394a7381075ac27,0xc158cb96c511045,0x8b42739216b721,0x18d018403c0bc3b,0x630006018c08,0x4c6241104800103,0x2184234e7d4a64f,0xaabd4a1884310c6,0xafaa55]⟩,
  ⟨30,7,[ew302,ew109,ew110,ew111,ew112,ew113,ew114,ew272],lh 5 [47,26,35,9,307,272,34,32,370,24,2,23,635,262,20,336,464,545,386,325,332,175,29,337,167,636,677,455,528,317,11] [0x10c430942522088,0x944d033c0a0296b,0x410431102509693,0x158862540a01088,0x8418004a508457,0x1b1871152928529,0x34636886310c40,0x31f9b39cda3e4e7,0x1e33800700dd]⟩
]
def nodesBlock20 : Array Node := #[
  ⟨30,7,[ew109,ew110,ew111,ew112,ew309,ew113,ew114],lh 6 [262,11,267,282,5,35,329,7,302,296,307,2,34,9,47,121,304,325,182,272,1,20,679,55,29,678,327,24,274,365,354,332,27,294,287,366,28,532,285,310,680] [0x2984d861960a4ca,0x618514a000299,0x248206506285146,0x246686188189509,0x549199189689259,0x24e39055040e809,0x30a04a28c310050,0x1430c085315340c,0xd60c22084c0003,0xc2442096083208,0x3830960834430d6,0xd5542382095083,0x1db31b6c7882302,0x21c70f8c0208087,0x15114074014f3dc,0xd10d011005745,0x30034e34010400e,0x175cd30d357340,0x9cf1049a590f68f,0x5d23cb2d211248b,0x4810545d4501052,0x2df1047cb2de104,0x1c75810511c778b,0x1071cb041441068,0x2c71c4041]⟩,
  ⟨30,7,[ew290,ew109,ew110,ew111,ew112,ew113,ew278],lh 6 [272,11,35,500,262,2,47,34,267,307,288,1,7,55,29,681,329,304,274,9,5,20,473,332,282,334,540,532,535,26,273,537,584,302] [0x24f38e3c924138e,0x1047de741001049,0x68208110404205a,0x2c128104b05728a,0x1455c61811415cb,0x4704f30c046197,0x3890008071c130c,0x10424f24e00038f,0x242090110402089,0x4032c30cf0d02d0,0x55144618354340f,0xc70d13110c60d1,0x100082447443303,0x2cb004118098604,0x20a2802c000a008,0x8188215200180,0x1c000c0081c8015,0x49648228a20c200,0x493513096592292,0x1c24d54d2514495,0x8d3531c74cd4c2,0x15b5146c5156514,0x34d71c85634d585,0x199645345159146]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew272,ew278,ew292],lh 5 [9,2,35,500,11,272,47,20,1,274,307,175,417,288,34,312,262,29,421,682,294,665,287,537,285,26,28,23,127,600,7,558] [0x50c6a1404a515e5,0x1b2435ae2319cc3,0x386a82a0a0a0263,0x164b82dca4b10e1,0x124004812900928,0x684e13880010800,0x304c62737a4110d,0x67884e982131821,0xe77c84]⟩,
  ⟨30,7,[ew298,ew109,ew110,ew111,ew112,ew113,ew272],lh 6 [47,11,274,7,35,2,39,1,28,307,55,175,26,34,10,500,308,9,279,23,334,20,385,267,262,537,602,5,327,683,272,285,336,119,29,604,278] [0x24d2cb34935c2cb,0x10d65f78d30c709,0x34208a10a28208d,0x1e04d36471ca4ca,0x1450514a00a287,0x50151d0c3285154,0x2c95c98410540c3,0x8924c30b5cb2cc,0x24410e60e384109,0x38f20f3da3ce20e,0x55658000f54f39a,0x8da8960563c0016,0x30610619860c104,0x1c77482061c6318,0x415546006188199,0x417041195190010,0x2085c30d0050403,0x1071022020871c4,0x26db0800916d1,0xd14414420c2440,0x485908000081051,0x520d2205152012,0x454814930d34c1,0x143140041003005]⟩,
  ⟨30,7,[ew307,ew109,ew110,ew111,ew112,ew113,ew114,ew272],lh 5 [47,35,28,307,262,20,23,34,302,9,347,267,386,542,24,269,332,325,175,29,672,455,366,310,317,11] [0x41824091cb1a86a,0x6b0ef3b00501506,0x40c240906a50e30,0xcc671c86501506,0x394050090241024,0x4845612db55acf4,0x1129205290a420,0x8c6108c610817,0x1939400280f8]⟩,
  ⟨30,7,[ew109,ew110,ew310,ew111,ew112,ew113,ew114],lh 6 [35,28,11,7,2,29,329,5,26,20,39,274,9,296,32,279,307,304,34,308,6,262,47,684,325,327,545,284,23,685,365,354,332,336,686,328,27,272,285,337,167] [0x205505148210510,0x64515714d64d408,0x1808c5545357345,0x346046140006546,0x24619718d041357,0x196591251456906,0x490090412491091,0x899a948648452,0x21554a00a2959c8,0x5a38e74104a38a,0x5934c9a0a58a281,0x5030d3493289253,0x1e2cb4c30d4494,0x38e7800182cb600,0x60105a38e741058,0x26010480925f104,0x828830e10827c9,0x2db2c00418430e2,0xc1cc01b6cb04b,0xc03043001c7004,0x200c0cc302300,0x4f1cf3c41011c7,0xdc70208f0cf044,0x1c31c40823c23dc,0x103107087]⟩,
  ⟨30,7,[ew300,ew109,ew110,ew111,ew112,ew273,ew113,ew114],lh 5 [35,9,272,20,296,307,47,28,29,0,24,23,13,279,556,395,327,336,11,294,21,26,302,278,285,548,5] [0x4011284a41505,0x330cc8c1ee6adab,0x22001004a240a49,0x2908c310a421504,0x354471504098085,0xe13894a10cc3,0x3802100c0308021,0x30cc75ace71dc76,0x9d24794e123]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew311],lh 6 [124,370,47,11,35,302,7,9,272,347,308,274,182,2,26,327,39,24,23,262,554,28,20,5,121,365,325,354,332,287,687,366,310,288,688,34,552,455] [0x38920924e380208,0x4d30041094c900e,0x45149549244240,0x81581245141541,0xc0042040580002,0x140010c1054040,0x13c10540403c0,0x1104134ce10e014,0x215550150393390,0x588088415408148,0xca21620a08a296,0x2861910d144674a,0x2913d145444a3ca,0x14b2d87c414529e,0x2c22c75c711860b,0x1cb18b1c208b5d7,0x6442c32c71871c3,0x11a1076471da1c4,0x34c08c30d805082,0x19248384c18c14d,0x49448c3cc3030d2,0x18d0c33223123d2,0x6c23461970c35c6,0x9c08d6cd35c342,0x9648c33c3]⟩,
  ⟨30,7,[ew312,ew109,ew110,ew111,ew112,ew113,ew114],lh 6 [35,124,302,11,272,262,28,20,34,39,554,47,5,26,9,327,308,182,7,55,2,596,571,24,121,274,23,334,365,325,354,332,552,307,455,167,287,366,310,288] [0x10f34d2a284f041,0x3c411534d284,0x70515d00074515c,0x19608228618f082,0x2cb7c71de2cb3c6,0x2830cf2087871df,0x3411043c30e0208,0x14504d34a10454d,0x54000114504004a,0x8a186582081186,0x1c104b04a1c7042,0x8082010c158b2c1,0x14400004820a0c3,0x89105149009245,0x246244082106189,0x1d02d04078c92c9,0x2175d2910210247,0x658940180412497,0xe30e018619099,0x48038738030c007,0x134ce48e393380,0x51131145498230c,0x4da6839d14d1094,0x31b3140c34430da,0x51b6cc0c3]⟩,
  ⟨30,7,[ew109,ew313,ew110,ew111,ew112,ew113,ew114],lh 6 [47,5,23,34,9,39,296,35,24,274,26,329,302,262,0,308,55,182,304,121,2,29,28,689,325,690,327,556,272,334,20,365,336,691,354,332,124,455,328,27,337,310,317] [0x54670695b915695,0x34618a29571c54a,0x1871cb34b2c7986,0x30658618c18b08b,0x7924809cb78b2cc,0x5c30d23922c0012,0x2982084830db38e,0x10460a29920864a,0x7c71d81046071df,0x5a10825d65a0082,0x418c0022041816,0x5c30da38e880023,0xa0a1c76830db38e,0x30528d3451c514d,0x14214830c202085,0x14f00f3c1045005,0xc821920f0cf141,0x25310d30c3d93c8,0x2440413534c9309,0xc9100109049240,0x2504040c4110109,0x511011454a53013,0x4020a10914114d4,0x5da94414457442,0x51d741401]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew275,ew282,ew278],lh 5 [29,9,1,47,2,274,20,7,307,262,35,288,287,127,26,386,407,11,34,368,27,500,296,273,566,692,32,464] [0x2e600054040008,0x420160341501280,0x1986b12c4952540,0x28927631f7639c6,0x84a5084a129422,0x10b04310c9084e5,0x20cc61e8f910a0d,0x91df188c8419063,0x7d9e12]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew282,ew292],lh 5 [29,47,9,28,2,35,7,1,307,274,23,24,406,262,20,287,71,328,368,296,455,272,26,278,407,285,302,11,34,580,327,332] [0x2a4000a2040008,0x32600210001020,0x7114751da568a80,0x396cbaaccb7bdc1,0x124a211845088e3,0x38c61b8ca949522,0x840c1d0f231e066,0xe1b660908120424,0xffbac]⟩,
  ⟨30,7,[ew302,ew109,ew110,ew111,ew112,ew113,ew114,ew275],lh 5 [6,35,7,262,296,29,2,24,274,9,47,32,307,319,71,20,302,336,464,582,406,327,332,287,26,692,285,566,34] [0xa02801c07290a4,0xa4c521454651a0b,0x214280a080282d5,0x610ac609ad514a4,0x1c07380611848c,0x48d081e00205ce0,0x5052908d291a463,0x32f7a5ac5911946,0x1c119ef339c2]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew314,ew113,ew114],lh 6 [35,120,124,28,274,47,11,5,39,272,24,55,9,694,262,327,2,34,308,279,1,20,7,296,26,370,23,334,693,365,325,354,332,167,287,302,571,285,278,288,695] [0x60d28a71861728a,0x38104001738e5d8,0x4d0420c35c0001,0x423c208d0810c1,0x1c108d0813c104d,0x451421c2085081,0x459199651442182,0x820e38a000091,0x2430c850828e388,0x2483c8203209509,0x14921c2093c924d,0x255552152495849,0x58a44a296892452,0xc41145000c3496,0x11e100740014004,0x10c1cc01e004744,0x5843153041c7115,0x10b2cc58c30b304,0x9831c79648c33c3,0x2d30d04131d34d0,0x4c619a2da6869d3,0x42014581041f145,0x2cb34618f2cb7d0,0x1db1c51853c61a8,0x15b6c7186]⟩,
  ⟨30,7,[ew258,ew109,ew110,ew111,ew112,ew113,ew278],lh 5 [35,11,287,120,288,262,2,34,124,39,1,20,47,7,55,26,308,9,5,296,576,332,696,571,274,334,29,127,540,574,269,302] [0xa08417869bd067a,0x943c00022159ef,0x9035bd78528400,0xaad61306a420761,0xb43639c2b5d4c6,0xb3df310bcd684e7,0x180132966f7d042,0x1d0682126000ca3,0x4310358d1440c83,0x19c686a06c62168,0x494a20010740da3,0x11089524452a409,0x82d69625244894a,0x135b03c12b4c190,0xc29452120d808e2,0x30119440a56098,0x8ba203822c88252,0xb98ca9480e744e7,0xef7ea7394635e52,0x66726718d9331ce]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew275,ew278,ew287],lh 5 [262,2,296,20,9,11,287,35,47,288,307,421,1,593,418,7,312,175,304,26,697,388,302,273,34,269] [0x5084a380e011a06,0x12c511294210d02,0x40d0962580380f2,0x50c672cc66cca3,0x14843840120084,0xa85014008400084,0x184630dd3649525,0x760a568c2118c21,0xf7e4a5]⟩
]
def nodesBlock21 : Array Node := #[
  ⟨30,7,[ew260,ew109,ew110,ew111,ew112,ew113,ew275],lh 6 [7,29,288,124,287,11,9,302,20,35,262,274,5,2,34,6,47,182,576,325,121,55,596,334,296,421,493,698,336,464,26,598,366,310] [0x13593499600058,0x2404c4100640004,0x60132494c6180,0x1c1c74820801c0,0x20000d01a208002,0x501b38e68d340,0x43104745140380,0x2810d20c1101052,0x4904328a0c90c1,0x520826c71c1081,0x2030d00c1201047,0x4e043143050403,0x2842490ce0c1141,0x1c710a29624958a,0x3c20841c710210f,0x20f40f3c83c4410,0x827d678f14f108,0x29450b08b2d480a,0x18b30c2c82c6306,0x38e19518b38b188,0x44d85430c2d5546,0x9155150d351311,0x145445142542085,0x3575cc14531730d]⟩,
  ⟨30,7,[ew312,ew109,ew110,ew111,ew112,ew113,ew114,ew275],lh 5 [24,28,124,35,20,302,47,9,262,7,406,558,580,659,71,34,307,332,327,627,48,674,455,287,26,366,310,288,569] [0x950340c0b02a02,0x6292b4a88621825,0x28a881204098a51,0xb0849a88c4110a1,0x20020014034004c,0x38c390e00905c06,0x8ce718ce719c63,0x314212b5bb0849a,0xf79884339dc]⟩,
  ⟨30,7,[ew109,ew315,ew110,ew111,ew112,ew113,ew114],lh 6 [35,47,11,302,272,34,39,26,329,2,307,262,274,9,32,304,308,5,55,182,29,20,7,121,325,700,701,327,582,24,334,699,365,28,354,332,336,296,584,328,27,337,167,287,366,310] [0x50a10499c9546d4,0x2ca2871d4104507,0x2800082c82009ca,0xdc38e7c30c8388,0x54f3c1a08548203,0x28514f08f20104f,0x1d81043c514a08a,0x30c6071d9104647,0x80001830c600020,0xdc38e7c385b3a1,0x2498c10622496c3,0x685164082881063,0xa4700090515a082,0xc61cb2c600618b,0x1991840c3119106,0x550050415a86046,0x15d756ad0150195,0x317b0b0cb41659d,0xd44d0175cc0cc,0x580341040451001,0x1248d58d352340,0x2530534c9b57041,0x4926820934935c9,0x45e4490824c209a,0x25e791082]⟩,
  ⟨30,7,[ew109,ew110,ew111,ew112,ew113,ew114,ew287,ew292],lh 6 [24,1,20,262,35,47,9,307,11,274,296,272,5,2,369,417,639,288,302,312,29,455,294,665,287,418,285,26,28,7,34,600,327,325] [0x3811031033804c0,0x2871c81c21471c1,0x41058054a28f50a,0x180850805c1001,0x446cb68b2d92c0,0x246189189246109,0x3451030c40c6183,0x492701201451345,0x8508c30234c308,0x8607cf788748142]⟩,
  ⟨30,7,[ew307,ew109,ew110,ew111,ew112,ew113,ew114,ew278],lh 5 [47,35,1,11,29,296,262,23,20,9,267,307,2,5,26,418,269,602,417,327,325,697,285,593,288,302,34] [0x11c26099ca290a4,0x944701bc0802047,0x28826098a421693,0x590ab58c0802082,0x400e2388c13048b,0x11d57b2943a8d00,0x484694852102447,0x664431618060029,0x1a181ad031ad]⟩,
  ⟨30,7,[ew109,ew110,ew316,ew111,ew112,ew113,ew114],lh 6 [124,29,302,282,34,262,20,272,47,11,6,274,5,35,9,702,327,28,7,182,121,55,2,1,347,23,334,703,365,325,354,332,26,596,285,294,704,366,310,288] [0x11c704f0401c7,0x40104f04040000f,0xd00114100f001,0x805c004d040140,0x18100208f5d76c2,0x48040180008001,0x118258604100240,0x3478a1807407004,0x1c51433430c58c7,0x4430830d10ca082,0x208286283203291,0x2922831030c618a,0x15c34d0d248a10a,0x8270515d34d745,0x41145b0823d1450,0x19f2087c619e208,0x1043d2490104786,0x2d49450824124a4,0x2ce30e15450b08b,0x10b38638b30c2c6,0x2d554e10e39538b,0x5933134d699430c,0x5596499d3553516,0x31a3162494c9259,0x59a68c249]⟩,
  ⟨30,7,[ew312,ew109,ew110,ew111,ew112,ew113,ew114,ew278],lh 5 [272,35,124,26,11,262,47,20,274,9,23,5,417,2,600,307,584,558,325,327,664,682,455,287,288,302,34] [0x530a12840300de2,0x73091230e639950,0xa08250946018272,0xb0844a88c211c4a,0x3806000ca12844e,0x4046000c04b8006,0x485094a12842428,0x26544561a769c29,0x1a2196b3356b]⟩,
  ⟨30,7,[ew109,ew317,ew110,ew111,ew112,ew113,ew114],lh 6 [267,47,26,28,262,35,302,11,34,7,296,274,9,307,20,120,705,369,325,5,182,121,55,2,327,602,23,334,365,706,354,332,707,29,558,367,366,310,288] [0x8a00a89984a60a,0x30a282299000402,0x28514f10f3c58ca,0x18f0cf3c63cd0c3,0x39144104d38d346,0x3483511d1341051,0x9800044820d1c7,0x104602099000402,0x70515210448515c,0x19d0c34061920c3,0x38e7c105e38e486,0x40821224978105f,0x2142488220249,0x180084100145004,0x30d01867430c0,0x8004000e002042,0x20880924020008e,0x2d59040c4009250,0x2cc4cc11554b0cb,0x24b30104b4d32c1,0x2d658c24c31630b,0x5d4054517955041,0x59a687994594557,0x4db4d71c75071da,0x5db6d31c7]⟩,
  ⟨30,6,[ew270,ew111,ew271,ew273,ew113,ew114,ew282],lh 5 [609,35,29,26,34,9,7,274,47,2,312,319,320,350,285,321,21,368,708,607,40,337,27,167,11] [0x180111001009c20,0x104530101202500,0x29425084a11d474,0x5d84312947294e1,0x7dc6e109ac6104b,0x2188e18da62188f,0x60c942126]⟩,
  ⟨30,6,[ew270,ew111,ew271,ew273,ew113,ew114,ew287],lh 5 [262,9,47,35,611,347,20,11,26,34,21,368,709,710,371,285,312,175,29,317,7] [0x4116b2914a18461,0x7908e6b52463044,0x80011800300c65,0x416100042000420,0x118522a4b111845,0x3ccef421c749d26,0x50e6108c6]⟩,
  ⟨30,6,[ew270,ew111,ew271,ew113,ew114,ew292],lh 5 [47,5,606,6,9,11,7,262,39,29,35,1,304,312,327,26,285,308,611,2,274,711,34,608] [0x92942a084aaca92,0x1a5225ac4910d6b,0x100039cc6018a62,0x118c329466188a2,0x83de370c6f1c1ce,0x3acea4a54b59d29,0x20087084e039024,0x394e43108521cc7,0x5210479088229ef,0x4800c0b18002421,0x6158d335a52b0cc,0x8210d735a86c1ce,0x18c128426080a5,0x46214203108108,0x217b1a31]⟩,
  ⟨30,6,[ew293,ew270,ew111,ew271,ew113,ew114],lh 5 [308,34,606,262,5,0,304,2,1,6,9,611,39,29,35,312,20,368,274,624,119,648,273,11,285,608] [0xa2d608c40b04e31,0xc0c73183601c0,0xb18c078006055ef,0x64200200100308c,0x139cb52f38b8021,0x13c494216e58a42,0x4c1223892f48908,0x4852228850124e7,0x921036b441124a5,0x19c6a228681c9ad,0x5154308d4750c84,0x31ced210651a821,0x40426299a769886,0x21487084c1320a5,0xe529021]⟩,
  ⟨30,6,[ew270,ew111,ew271,ew113,ew275,ew278],lh 5 [26,47,9,120,6,5,121,304,29,11,262,7,1,302,274,296,35,288,308,2,708,712,269,119,421,464,558,127,584] [0x7c1e370c7083c42,0x22103630681918c,0x184249908120e63,0x180044a48020d23,0xd35a4c908da62f4,0x5314e421cc62908,0x1044a29541508a2,0x725220084913800,0x518c26b446129aa,0x4042729ce10a0a5,0xe0007b1ce0aeed5,0x398f15c62631d67,0xca45014b228400,0xac25318ab584c1,0x2c093252b580c0]⟩,
  ⟨30,6,[ew270,ew111,ew271,ew113,ew114,ew275,ew292],lh 5 [9,47,29,1,35,296,368,302,20,649,304,623,406,640,319,713,71,11,367,7,285,569,123,26] [0x5ac2550d434a640,0x398cc298c529a65,0x200046b42018862,0x738222000420004,0x3884ca09ef10c62,0xa1010a101842a1,0x2e7b1e31]⟩,
  ⟨30,6,[ew270,ew111,ew112,ew271,ew113,ew275,ew287],lh 5 [296,6,302,9,47,20,262,26,175,35,649,708,371,7,11,714,367,366,342,288,310,273,29] [0x80011016b52a00,0x6842c0042000420,0x198c33252890a22,0xa0a6830c6648c69,0x21485a89c770844,0x2148529ec83a1ef,0x1a73b0a4]⟩,
  ⟨30,6,[ew110,ew270,ew111,ew271,ew113,ew282,ew278],lh 5 [1,9,47,29,35,26,2,11,274,302,712,321,7,296,715,319,350,370,287,337,167,273,500] [0xa1465528a198651,0x2048162585a956b,0x739ad1184618060,0xa0241040400d36,0x41ef1008841101,0x308c711c6000ce0,0x1273c046]⟩
]
def nodesBlock22 : Array Node := #[
  ⟨30,6,[ew302,ew110,ew270,ew111,ew271,ew113,ew114],lh 5 [302,47,26,29,34,296,32,9,28,310,621,7,649,623,647,640,319,320,285,368,342,274,11,272,337,167,367,35,317] [0x56809800514840,0x258804a42018108,0xc84661194ac0ae2,0x2998cd156458841,0x30dce215ad09465,0x8f67391ef09cc3,0x24e063120e10]⟩,
  ⟨30,6,[ew270,ew111,ew271,ew113,ew114,ew278,ew292],lh 5 [296,29,9,47,35,5,312,11,26,649,623,611,417,640,319,262,1,20,500,285,308,328,40,712,7,123,302] [0x52a20080104a5e0,0xa000c9816b01e40,0x208446b462b06a1,0x738612084420844,0x418cc098c109ae1,0x194a8194a3194a3,0x348c9f07]⟩,
  ⟨30,6,[ew307,ew270,ew111,ew112,ew271,ew113,ew114],lh 5 [296,26,267,47,34,29,302,9,272,621,337,312,167,7,649,647,640,35,11,319,320,182,285,347,367,366,342,328,40,28,310,317] [0xdaa15292900508,0xb481630615ac37,0x100021000273b00,0xd1b267bda200840,0x89cf184067e1765,0x19644918c3f0fa5,0x64f929421673]⟩,
  ⟨30,6,[ew300,ew109,ew270,ew111,ew112,ew113,ew275],lh 5 [47,9,28,26,0,1,7,35,274,29,24,2,302,175,13,34,40,319,287,288,296] [0x384e1928ca6b526,0x199ef038ce14c46,0x2582626103a68a,0x114e83a86419231,0x288641900b02c45,0x581010a028004a8,0x32018529160]⟩,
  ⟨30,6,[ew312,ew270,ew111,ew112,ew113,ew114,ew275],lh 5 [24,35,124,29,302,9,47,296,40,328,319,175,48,659,28,71,26,23,625,308,327,366,310,288,569,167,34] [0x192234a50800ce7,0xa0c735ae431994a,0x8401000263020,0x92a11000210002,0x94a1094a128425,0x239c46b6e421ac4,0x350343267bf06]⟩,
  ⟨30,6,[ew312,ew110,ew270,ew111,ew112,ew113,ew114],lh 5 [302,35,26,29,34,274,2,9,28,124,47,296,40,328,27,320,621,321,7,313,314,312,327,23,13,0,33,337,167,716,288,317] [0x6b58cb0d6ba8862,0x1e5ef73b03182e3,0xe090040210d8b42,0x424250964490a31,0x28694227a649a73,0x30027384e131c25,0x144fa804f000a]⟩,
  ⟨30,6,[ew307,ew109,ew270,ew111,ew112,ew113,ew114],lh 5 [29,34,35,11,26,302,47,274,267,2,9,28,7,272,337,167,40,319,717,312,327,621,321,33,328,27,317] [0x73aa4a11ad98080,0x2302c7bec42acab,0xc80ab28210c02e0,0x2a04711c2c08231,0x389030a0c942652,0x4986a5094232847,0xc3d0c6118526]⟩,
  ⟨30,6,[ew302,ew109,ew110,ew111,ew113,ew282,ew278],lh 5 [500,26,2,288,29,9,47,35,274,718,302,621,287,640,32,34,5,332,55,27,296,337,167,272] [0x194e308d2920083,0x824352a2318a02,0xa00029800538024,0x8ac15aea120004,0x2a1ad3142c606e1,0x11846308e841d05,0x1ee7b8c2]⟩,
  ⟨30,6,[ew302,ew109,ew110,ew111,ew113,ew114,ew278],lh 5 [35,26,9,23,296,272,47,29,307,5,11,2,302,321,288,327,337,167,287,32,34] [0x80309465390e3,0x78d8c7286a1acc3,0x22cc40080409425,0x82003a10722104,0x94a10aa416b621,0x8400084010002,0x2933252632526]⟩,
  ⟨30,6,[ew300,ew109,ew110,ew111,ew112,ew113,ew278],lh 5 [296,11,23,26,35,29,9,47,272,274,2,5,321,307,287,288,34,327,337,302] [0x204261b8612b4a1,0x884300ace178822,0x280020188001460,0x192442800502ce0,0x1a1036316812043,0x218c43252622522,0xea51e6251d42]⟩,
  ⟨30,6,[ew109,ew110,ew111,ew303,ew113,ew114,ew278],lh 5 [29,35,26,9,47,1,23,307,302,5,11,641,28,288,272,124,2,337,167,287,327,719] [0x7980608c201004e,0x1ce001ce004080,0x11242314c510621,0x298a6621825ae62,0x8c6808c6118423,0x41514515ad22485,0x2aa225242292a]⟩,
  ⟨30,6,[ew109,ew110,ew111,ew112,ew113,ew301,ew278],lh 5 [29,26,272,274,296,47,35,2,11,5,9,288,23,328,337,640,32,327,34] [0x1080029a008024,0x108020004024a0,0x11522088410a9c1,0x30c660884110422,0x30c66198c378c69,0x2a20c4316b394e5,0x248444a7394e8]⟩,
  ⟨30,6,[ew317,ew110,ew270,ew111,ew112,ew113,ew114],lh 6 [29,296,302,34,307,47,26,28,9,312,40,621,321,7,649,623,640,327,328,32,27,5,11,0,720,337,167,367,366,342,35,310,288,317] [0x480040011180249,0x1550009308028a,0x2cb646601017580,0x34630c6861c21c2,0x10104438e6c1343,0x7070441013cf144,0x788203410148747,0x8430838020857c5,0x143]⟩,
  ⟨30,6,[ew300,ew109,ew110,ew111,ew271,ew113,ew278],lh 5 [35,11,1,296,302,272,47,26,20,0,9,13,500,267,721,34,649,262,23,288,29,337,665,167] [0x5ce6b4e163061,0x205ef0ad0b98432,0x30e8384003394e3,0x288a0a94891a4cb,0x144e4290a6b9ac2,0x3080a5014002a20,0x1044a08212448]⟩,
  ⟨30,6,[ew312,ew110,ew111,ew112,ew271,ew113,ew114],lh 5 [302,26,20,47,34,262,272,124,9,296,649,367,29,621,48,11,314,368,327,647,337,33,287,366,342,313,310,317] [0x881205ad4a304c1,0x4926410c439258c,0xa9c27080c06b686,0xc02e0092c108c41,0x2a105414a8738e5,0x189e478003d0320,0x44d8a1021c62]⟩,
  ⟨30,6,[ew302,ew109,ew110,ew111,ew271,ew113,ew114],lh 5 [302,296,272,35,9,32,47,34,26,20,11,621,321,262,722,368,28,327,310,29,337,717,287,317] [0x10604090078401,0x28e0048c088010,0x306610906140902,0x1156ba082a38429,0x2b447b098c48aa5,0x2a46420c83191a3,0xc7b99ce394c5]⟩
]
def nodesBlock23 : Array Node := #[
  ⟨30,6,[ew307,ew109,ew111,ew112,ew113,ew275,ew287],lh 5 [47,6,288,262,175,20,9,35,302,296,26,34,7,267,369,325,29,366,310,28] [0x890108ce1091c1,0x38dec5854a00425,0x224050108240883,0x30c0618a2282524,0x10240198c3398c7,0x14052826240848,0x1ab634a0]⟩,
  ⟨30,6,[ew307,ew109,ew111,ew112,ew113,ew114,ew275],lh 5 [24,20,35,28,302,47,7,9,262,29,307,26,296,640,659,71,124,287,327,366,310,288,569,267,34] [0x200030204004140,0x9016b89806284a0,0x284a120c8312048,0x10e636252c49946,0x11ce211ce66b427,0x20c6473aa420681,0x317284257bec1]⟩,
  ⟨30,6,[ew300,ew109,ew110,ew111,ew112,ew113,ew275],lh 5 [7,296,47,24,9,302,262,28,29,35,20,124,32,319,26,287,71,34,327,27,310] [0x4912078c035ad00,0x9001150010630a0,0x284280912108d03,0x310c40a1016b661,0x21dce5094339465,0xa092632446110c7,0x4a508a7394e2]⟩,
  ⟨30,6,[ew109,ew308,ew111,ew112,ew113,ew114,ew275],lh 5 [29,47,302,1,26,35,7,24,9,307,296,723,287,267,71,124,328,262,28,20,327,310,167,724] [0x148400460079c07,0x5252a0252004c20,0x5ac2710c432a0a7,0x1a0656b49431d8c,0x291042990609428,0x1106211866186a1,0x2e4092c4738c1]⟩,
  ⟨30,6,[ew109,ew110,ew111,ew112,ew113,ew305,ew275],lh 5 [29,47,296,28,35,7,20,302,9,262,287,24,724,366,310,327,34] [0x8400248010002,0x100020084001820,0x304c119c6749124,0xa08368d8b2ad4a,0x704884112841504,0x298e319c6739461,0x2052bc26304a1]⟩,
  ⟨30,6,[ew315,ew110,ew111,ew112,ew271,ew113,ew114],lh 5 [34,296,272,302,29,307,47,26,35,9,649,368,623,621,321,640,11,319,327,20,0,337,167,287,366,342,328,40,725,310,317] [0x1856b52901388e1,0x50016326120432,0x21485388476b6a2,0xc8f03102e073ac2,0x425287bcc9d9745,0x3120080c66e9b83,0xc0f008501231]⟩,
  ⟨30,6,[ew312,ew110,ew111,ew271,ew113,ew114,ew278],lh 5 [23,124,47,296,26,9,35,5,649,367,29,500,302,621,641,272,640,24,20,11,327,337,167,287,34] [0xd4a4a50819223,0xa0c6c5ae6318a43,0x20ac2004016b6a4,0x802023de473ae4,0x314a6314a684045,0x80010800110420,0x30c11ce211ce2]⟩,
  ⟨30,6,[ew307,ew109,ew111,ew112,ew113,ew272,ew275],lh 5 [267,24,20,34,28,262,9,302,47,7,175,35,26,726,23,287,29,366,310] [0x3842e595610a9a1,0x1858c7a42940901,0x4090a390ea5956a,0x118a48906018209,0x9080630ca6314c5,0x488e02008939082,0x601800200c48]⟩,
  ⟨30,6,[ew312,ew110,ew111,ew112,ew113,ew272,ew275],lh 5 [302,124,47,20,175,35,262,7,9,28,307,368,29,500,26,334,366,310,313] [0x5ad24314c55108a,0x6b48f3918c18864,0x1886248120314c5,0x120c0801ce384e1,0x880a84142841d06,0x8c094824100402,0x273844318822]⟩,
  ⟨30,6,[ew302,ew109,ew110,ew111,ew113,ew272,ew278],lh 5 [23,32,9,47,262,20,26,34,35,500,272,11,302,324,24,2,288,29] [0x9003000e025a0,0x3818c82c0b03c60,0x1946941109328c9,0x28c88220e13862b,0x288c150546328a3,0x194221108211044,0xe138427094a3]⟩,
  ⟨30,6,[ew312,ew110,ew111,ew112,ew113,ew272,ew278],lh 5 [272,500,47,11,262,274,9,124,308,2,35,307,29,34,175,302,312,20,288] [0x5842b0a88104001,0x7382d1858c08a21,0x9024000802880,0x214a44000d00d00,0x218c4298c5314a6,0x38def19e4748922,0xe319c49488e3]⟩,
  ⟨30,6,[ew302,ew109,ew110,ew111,ew113,ew275,ew278],lh 5 [296,9,29,20,35,11,7,2,287,32,1,288,262,302,47,636,718,332,27,26] [0x20541522081004a,0x32dad8ad6519c67,0x1e402048000840,0x611841000201445,0x184c84266519c67,0x19521098a10902c,0xc9325ef339c3]⟩,
  ⟨30,6,[ew307,ew109,ew111,ew112,ew113,ew275,ew278],lh 5 [287,262,47,11,7,29,9,267,35,2,288,296,1,20,312,26,325,33,175,302] [0x6000a4050003960,0x810041800f13440,0x2b4452a96a40501,0xa98129245894a3,0x98c4198c830446,0x3a66419c6748922,0xe321c89488e3]⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 192 then
    if i < 96 then
      if i < 48 then
        if i < 16 then
          nodesBlock0[(i-0)]?
        else
          if i < 32 then
            nodesBlock1[(i-16)]?
          else
            nodesBlock2[(i-32)]?
      else
        if i < 64 then
          nodesBlock3[(i-48)]?
        else
          if i < 80 then
            nodesBlock4[(i-64)]?
          else
            nodesBlock5[(i-80)]?
    else
      if i < 144 then
        if i < 112 then
          nodesBlock6[(i-96)]?
        else
          if i < 128 then
            nodesBlock7[(i-112)]?
          else
            nodesBlock8[(i-128)]?
      else
        if i < 160 then
          nodesBlock9[(i-144)]?
        else
          if i < 176 then
            nodesBlock10[(i-160)]?
          else
            nodesBlock11[(i-176)]?
  else
    if i < 288 then
      if i < 240 then
        if i < 208 then
          nodesBlock12[(i-192)]?
        else
          if i < 224 then
            nodesBlock13[(i-208)]?
          else
            nodesBlock14[(i-224)]?
      else
        if i < 256 then
          nodesBlock15[(i-240)]?
        else
          if i < 272 then
            nodesBlock16[(i-256)]?
          else
            nodesBlock17[(i-272)]?
    else
      if i < 336 then
        if i < 304 then
          nodesBlock18[(i-288)]?
        else
          if i < 320 then
            nodesBlock19[(i-304)]?
          else
            nodesBlock20[(i-320)]?
      else
        if i < 352 then
          nodesBlock21[(i-336)]?
        else
          if i < 368 then
            nodesBlock22[(i-352)]?
          else
            nodesBlock23[(i-368)]?
def fastViews : QFast.Table View := ⟨31,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨381,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,0,0,0,4,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,14,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,30,0,0,0]
def aliasMap1 : Array Nat := #[0,0,0,0,16,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,50,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,54,0,0,0]
def aliasMap2 : Array Nat := #[0,0,0,0,16,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,30,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,4,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,37,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,53,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,4,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,37,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,45,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,4,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,29,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,16,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,49,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,53,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,16,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,19,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,49,0,0,0,0,0,0,0,50,0,0,0,0,0,0,0,51,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,11,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,4,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,23,0,0,0]
def aliasMap10 : Array Nat := #[0,0,4,0,0,18,0,22,0,0,0,0,0,0,0,0,8,0,12,0,0,26,0,30,0,0,0,0,0,0,0,0,32,0,36,0,0,50,0,54,0,0,0,0,0,0,0,0,40,0,44,0,0,58,0,62,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,34,0,0,4,38,0,0,8,42,0,0,12,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,50,0,0,20,54,0,0,24,58,0,0,28,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[59,25,0,0,43,9,0,0,58,24,0,0,42,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,17,0,0,35,1,0,0,50,16,0,0,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,34,0,0,4,38,0,0,1,35,0,0,5,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,50,0,0,20,54,0,0,17,51,0,0,21,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,2,0,0,12,0,14,0,0,0,0,0,0,0,0,16,0,18,0,0,28,0,30,0,0,0,0,0,0,0,0,32,0,34,0,0,44,0,46,0,0,0,0,0,0,0,0,48,0,50,0,0,60,0,62,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[0,40,0,0,16,56,0,0,1,41,0,0,17,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,44,0,0,20,60,0,0,5,45,0,0,21,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,0,0,0,4,5,0,0,0,0,0,0,6,7,0,0,0,0,0,0,12,13,0,0,0,0,0,0,14,15,0,0,0,0,0,0,20,21,0,0,0,0,0,0,22,23,0,0,0,0,0,0,28,29,0,0,0,0,0,0,30,31,0,0]
def aliasMap17 : Array Nat := #[0,0,0,0,16,17,0,0,0,0,0,0,18,19,0,0,0,0,0,0,20,21,0,0,0,0,0,0,22,23,0,0,0,0,0,0,48,49,0,0,0,0,0,0,50,51,0,0,0,0,0,0,52,53,0,0,0,0,0,0,54,55,0,0]
def aliasMap18 : Array Nat := #[0,0,0,0,16,17,0,0,0,0,0,0,18,19,0,0,0,0,0,0,20,21,0,0,0,0,0,0,22,23,0,0,0,0,0,0,24,25,0,0,0,0,0,0,26,27,0,0,0,0,0,0,28,29,0,0,0,0,0,0,30,31,0,0]
def aliasMap19 : Array Nat := #[0,0,0,0,0,1,0,0,0,0,0,0,18,19,0,0,0,0,0,0,12,13,0,0,0,0,0,0,30,31,0,0,0,0,0,0,32,33,0,0,0,0,0,0,50,51,0,0,0,0,0,0,44,45,0,0,0,0,0,0,62,63,0,0]
def aliasMap20 : Array Nat := #[27,25,0,0,11,9,0,0,58,56,0,0,42,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19,17,0,0,3,1,0,0,50,48,0,0,34,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,1,8,9,0,0,0,0,2,3,10,11,0,0,0,0,4,5,12,13,0,0,0,0,6,7,14,15,0,0,0,0,32,33,40,41,0,0,0,0,34,35,42,43,0,0,0,0,36,37,44,45,0,0,0,0,38,39,46,47,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap3)
  | 5 => some (0, aliasMap4)
  | 6 => some (0, aliasMap5)
  | 7 => some (0, aliasMap6)
  | 8 => some (0, aliasMap7)
  | 9 => some (0, aliasMap8)
  | 10 => some (0, aliasMap9)
  | 12 => some (11, aliasMap10)
  | 14 => some (13, aliasMap11)
  | 15 => some (13, aliasMap12)
  | 16 => some (13, aliasMap13)
  | 17 => some (11, aliasMap14)
  | 18 => some (13, aliasMap15)
  | 20 => some (19, aliasMap16)
  | 21 => some (19, aliasMap17)
  | 22 => some (19, aliasMap18)
  | 24 => some (19, aliasMap19)
  | 25 => some (13, aliasMap20)
  | 29 => some (28, aliasMap21)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_27 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 27 4 = true := by decide +kernel
theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 31 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 27 4 blockRoots_0 blockRoots_27
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 31 = true := joinRoots_0_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_118 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 118 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_182 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 182 25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_207 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 207 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_214 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 214 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_221 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 221 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_228 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 228 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_235 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 235 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_242 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 242 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_249 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 249 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_256 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 256 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_275 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 275 15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_290 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 290 17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_307 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 307 13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_320 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 320 13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_333 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 333 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_347 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 347 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_374 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 374 7 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 118 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 64 54 blockNodes_0 blockNodes_64
theorem joinNodes_0_118 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 118 89 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 118 64 25 blockNodes_118 blockNodes_182
theorem joinNodes_0_207 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 207 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 207 7 7 blockNodes_207 blockNodes_214
theorem joinNodes_0_221 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 221 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 221 7 7 blockNodes_221 blockNodes_228
theorem joinNodes_0_235 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 235 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 235 7 7 blockNodes_235 blockNodes_242
theorem joinNodes_0_249 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 249 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 249 7 7 blockNodes_249 blockNodes_256
theorem joinNodes_0_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 27 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 263 12 15 blockNodes_263 blockNodes_275
theorem joinNodes_0_290 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 290 30 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 290 17 13 blockNodes_290 blockNodes_307
theorem joinNodes_0_320 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 320 27 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 320 13 14 blockNodes_320 blockNodes_333
theorem joinNodes_0_347 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 347 34 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 347 27 7 blockNodes_347 blockNodes_374
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 207 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 118 89 joinNodes_0_0 joinNodes_0_118
theorem joinNodes_1_207 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 207 28 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 207 14 14 joinNodes_0_207 joinNodes_0_221
theorem joinNodes_1_235 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 235 28 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 235 14 14 joinNodes_0_235 joinNodes_0_249
theorem joinNodes_1_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 57 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 263 27 30 joinNodes_0_263 joinNodes_0_290
theorem joinNodes_1_320 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 320 61 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 320 27 34 joinNodes_0_320 joinNodes_0_347
theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 235 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 207 28 joinNodes_1_0 joinNodes_1_207
theorem joinNodes_2_235 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 235 85 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 235 28 57 joinNodes_1_235 joinNodes_1_263
theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 320 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 235 85 joinNodes_2_0 joinNodes_2_235
theorem joinNodes_4_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 381 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 320 61 joinNodes_3_0 joinNodes_1_320
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 381 = true := joinNodes_4_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfefefeaafee8ee88 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfefefeaafee8ee88 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 30) = true := by decide +kernel
  cases ev : QFast.get fastViews 30 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_46284_aux

open PEqualNP.Outside.L_meta_46284_aux in
theorem PEqualNP.Outside.L_meta_46284 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276678280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276678280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
