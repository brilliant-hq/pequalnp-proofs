import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19137_aux

abbrev Term := ℕ × ℕ

def Val (t : Term) := t.1 &&& t.2

def Total : List Term → ℕ
  | [] => 0
  | t::ts => Val t ||| Total ts

theorem total_append (xs ys : List Term) : Total (xs++ys) = Total xs ||| Total ys := by
  induction xs with
  | nil => simp [Total]
  | cons t xs ih => simp only [List.cons_append,Total,ih,Nat.or_assoc]

theorem fold_total (ts : List Term) (start : ℕ) :
    ts.foldl (fun z t => z ||| t.1 &&& t.2) start = start ||| Total ts := by
  induction ts generalizing start with
  | nil => simp [Total]
  | cons t ts ih => simp only [List.foldl_cons,ih,Total,Val,Nat.or_assoc]

def Constructed (base gs : List ℕ) : Prop := ∀ i : Fin gs.length,
  ∃ x∈base++gs.take i.val, ∃ y∈base++gs.take i.val, gs.get i=x|||y

def Ready (base gs : List ℕ) : Prop := gs.Nodup ∧ (∀ w∈gs,w∉base) ∧ Constructed base gs

theorem construct_more (base gs : List ℕ) (h : Constructed base gs)
    (a b : ℕ) (ha : a∈base++gs) (hb : b∈base++gs) :
    Constructed base (gs++[a|||b]) := by
  intro i
  by_cases lt : i.val<gs.length
  · obtain ⟨x,hx,y,hy,eq⟩ := h ⟨i.val,lt⟩
    rw [List.take_append_of_le_length lt.le]
    refine ⟨x,hx,y,hy,?_⟩
    simpa only [List.get_eq_getElem,List.getElem_append_left lt] using eq
  · have len : i.val=gs.length := by have hh := i.isLt; simp at hh; omega
    have take : (gs++[a|||b]).take i.val=gs := by simp [len]
    rw [take]
    refine ⟨a,ha,b,hb,?_⟩
    simp [List.get_eq_getElem,List.getElem_append_right (by omega : gs.length≤i.val),len]

theorem extendDisjunction (base gs : List ℕ) (ok : Ready base gs) (a b : ℕ)
    (ha : a∈base++gs) (hb : b∈base++gs) :
    ∃ gs', Ready base gs' ∧ (∀x∈base++gs,x∈base++gs') ∧
      a|||b∈base++gs' ∧ gs'.length≤gs.length+1 := by
  by_cases haveIt : a|||b∈base++gs
  · exact ⟨gs,ok,fun _ h=>h,haveIt,by omega⟩
  · have fresh : a|||b∉gs := fun h=>haveIt (List.mem_append_right _ h)
    have notbase : a|||b∉base := fun h=>haveIt (List.mem_append_left _ h)
    refine ⟨gs++[a|||b],⟨?_,?_,construct_more base gs ok.2.2 a b ha hb⟩,?_,by simp,by simp⟩
    · simp [List.nodup_append,ok.1]
      intro x hx eq
      exact fresh (eq ▸ hx)
    · intro w hw
      rcases List.mem_append.mp hw with h|h
      · exact ok.2.1 w h
      · simp only [List.mem_singleton] at h
        exact h.symm ▸ notbase
    · intro w hw
      rcases List.mem_append.mp hw with h|h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)

def Safe (base gs : List ℕ) (bad : ℕ) (ts : List Term) := ∀ t∈ts,
  t.1∈base ∧ t.2∈base++gs ∧ Val t &&& bad=0

theorem group (base : List ℕ) (bad : ℕ) (ts : List Term)
    (given : ∀ t∈ts,t.1∈base ∧ t.2∈base ∧ Val t &&& bad=0) :
    ∃ gs ys, Ready base gs ∧ (ys.map Prod.fst).Nodup ∧
      (ys.map Prod.fst).toFinset=(ts.map Prod.fst).toFinset ∧
      gs.length+ys.length≤ts.length ∧ Safe base gs bad ys ∧ Total ys=Total ts := by
  induction ts with
  | nil => exact ⟨[],[],⟨by simp,by simp,by simp [Constructed]⟩,by simp,rfl,by simp,by simp [Safe],rfl⟩
  | cons t ts ih =>
    obtain ⟨gs,ys,ready,distinct,keys,cost,safe,eval⟩ :=
      ih (fun u hu=>given u (List.mem_cons_of_mem _ hu))
    obtain ⟨left,right,clear⟩ := given t (by simp)
    by_cases seen : t.1∈ys.map Prod.fst
    · obtain ⟨v,hv,eq⟩ := List.mem_map.mp seen
      obtain ⟨p,s,shape⟩ := List.append_of_mem hv
      obtain ⟨_,vr,vc⟩ := safe v hv
      obtain ⟨gs',ready',keep,joined,bound⟩ :=
        extendDisjunction base gs ready t.2 v.2 (List.mem_append_left _ right) vr
      let w : Term := (t.1,t.2|||v.2)
      let ys' := p++w::s
      have mapEq : ys'.map Prod.fst=ys.map Prod.fst := by simp [ys',w,shape,eq]
      have lengthEq : ys'.length=ys.length := by simp [ys',shape]
      have unionVal : Val w=Val t ||| Val v := by simp [Val,w,Nat.and_or_distrib_left,eq]
      refine ⟨gs',ys',ready',mapEq ▸ distinct,?_,by simp only [List.length_cons]; omega,?_,?_⟩
      · rw [mapEq,List.map_cons,List.toFinset_cons,←keys,Finset.insert_eq_of_mem (List.mem_toFinset.mpr seen)]
      · intro u hu
        have old (mem : u∈ys) := safe u mem
        have lift (mem : u∈ys) := And.intro (old mem).1 (And.intro (keep _ (old mem).2.1) (old mem).2.2)
        rcases List.mem_append.mp hu with h|h
        · exact lift (shape ▸ List.mem_append_left _ h)
        · rcases List.mem_cons.mp h with e|e
          · subst u
            exact ⟨left,joined,by rw [unionVal,Nat.and_or_distrib_right,clear,vc]; rfl⟩
          · exact lift (shape ▸ List.mem_append_right _ (List.mem_cons_of_mem _ e))
      · change Total (p++w::s) = Total (t::ts)
        rw [total_append,Total,unionVal,Total,←eval,shape,total_append,Total]
        ac_rfl
    · refine ⟨gs,t::ys,ready,by simp [seen,distinct],by simp [keys],by simp; omega,?_,by simp [Total,eval]⟩
      intro v hv
      rcases List.mem_cons.mp hv with e|h
      · subst v
        exact ⟨left,List.mem_append_left _ right,clear⟩
      · exact safe v h

end PEqualNP.Outside.L_meta_19137_aux

open PEqualNP.Outside.L_meta_19137_aux

theorem PEqualNP.Outside.L_meta_19137 : (∀ (x1 : List ℕ) (x2 : List (ℕ × ℕ)) (x3 x4 : ℕ),   x2 ≠ [] →     (∀ x6 ∈ x2, x6.1 ∈ x1 ∧ x6.2 ∈ x1 ∧ x6.1 &&& x6.2 &&& x3 = (0 : ℕ)) →       ∃ (x7 : List ℕ) (x8 : List (ℕ × ℕ)),         x7.Nodup ∧           (∀ x9 ∈ x7, x9 ∉ x1) ∧             x8 ≠ [] ∧               x7.length + (2 : ℕ) * x8.length ≤ x2.length + (List.map Prod.fst x2).toFinset.card ∧                 (∀ (x9 : Fin x7.length),                     have x10 : List ℕ := x1 ++ List.take (↑x9) x7;                     ∃ x11 ∈ x10, ∃ x12 ∈ x10, x7.get x9 = x11 ||| x12) ∧                   (∀ x9 ∈ x8, x9.1 ∈ x1 ++ x7 ∧ x9.2 ∈ x1 ++ x7 ∧ x9.1 &&& x9.2 &&& x3 = (0 : ℕ)) ∧ List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x8 = List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x2) := by
  intro base ts bad start ne data
  obtain ⟨gs,ys,ready,distinct,keys,cost,safe,eval⟩ := group base bad ts data
  have card : (ts.map Prod.fst).toFinset.card=ys.length := by
    rw [←keys,List.toFinset_card_of_nodup distinct,List.length_map]
  have yn : ys≠[] := by
    rintro rfl
    cases ts with
    | nil => contradiction
    | cons t ts =>
      have h : t.1∈(([] : List Term).map Prod.fst).toFinset := by rw [keys]; simp
      simp at h
  refine ⟨gs,ys,ready.1,ready.2.1,yn,by omega,ready.2.2,?_,?_⟩
  · intro t ht
    obtain ⟨h₁,h₂,h₃⟩ := safe t ht
    exact ⟨List.mem_append_left _ h₁,h₂,h₃⟩
  · rw [fold_total,fold_total,eval]
