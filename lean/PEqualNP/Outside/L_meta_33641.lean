import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.BitIndices
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Bertrand

namespace PEqualNP.Outside.L_meta_33641

abbrev BitTape := List Bool
abbrev TapeMap := BitTape → BitTape
abbrev NVec := List ℕ
abbrev NMat := List NVec
open Function renaming update → upd, update_self → upd_self, update_of_ne → upd_ne, iterate_succ_apply → iter_succ, iterate_succ_apply' → iter_succ', iterate_add_apply → iter_add
open Sum renaming inl → injL, inr → injR
open Turing.TM2 renaming stepAux → stepAuxT, step → tmStep
open List renaming length_cons → len_cons, map_cons → mapC, length_map → len_map, length_append → len_app, length_nil → len_nil, getD_eq_getElem?_getD → getDOpt, getElem?_append_left → getLeftOpt, getElem?_eq_getElem → getOptEq, length_singleton → len_one, getElem_map → at_map, getElem_range → at_range, mem_singleton → mem_one, mem_append → mem_app, sum_eq_zero_iff_forall_eq_nat → sumZeroList, getElem_mem → at_mem, mem_map → mem_mapL, map_map → mapMap, map_nil → mapN, length_replicate → len_rep
open Finset renaming mem_insert → mem_ins, mem_singleton → mem_oneF, mem_filter → mem_filt, mem_univ → mem_all, mem_union → mem_un, disjoint_left → disj_leftF, card_le_card → card_monoF, mem_insert_of_mem → mem_ins_of
open Polynomial renaming eval_add → evalAddP, eval_mul → evalMulP, eval_C → evalCP, eval_X → evalXP
open Fin renaming ext_iff → fin_eq

namespace PT
namespace Lib
abbrev CPTs (f:TapeMap):Prop:= PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) f
end Lib
section
namespace Lib.Machines
open Turing
theorem iterate_none {σ:Type} (f:σ→ Option σ) (n:ℕ) :
    (flip bind f)^[n] none=none:= by
  induction n with
  | zero =>rfl
  | succ n ih =>rw [iter_succ]; exact ih
theorem simulate {σ τ:Type} (f:σ→ Option σ) (g:τ→ Option τ) (emb:σ→ τ)
    (h:∀ c c',f c=some c'→ g (emb c)=some (emb c')) :
    ∀ (n:ℕ) (a b:σ),(flip bind f)^[n] (some a)=some b →
      (flip bind g)^[n] (some (emb a))=some (emb b):= by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have:a=b:= Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [iter_succ] at hab ⊢
    cases hfa:f a with
    | none =>
      have e:flip bind f (some a)=none:= hfa
      rw [e,iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind f (some a)=some c:= hfa
      have e':flip bind g (some (emb a))=some (emb c):= h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab
section pushes
variable {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
def pushes:TM2.Stmt Γ Λ σ→ ℕ
  | .push _ _ q =>pushes q+1
  | .peek _ _ q =>pushes q
  | .pop _ _ q =>pushes q
  | .load _ q =>pushes q
  | .branch _ q₁ q₂ =>max (pushes q₁) (pushes q₂)
  | .goto _ =>0
  | .halt =>0
theorem stepAux_length (q:TM2.Stmt Γ Λ σ) (v:σ) (S:∀ k,List (Γ k)) (k:K) :
    ((stepAuxT q v S).stk k).length≤ (S k).length+pushes q:= by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [stepAuxT,pushes]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [upd_self,len_cons]; omega
    · rw [upd_ne h]; omega
  | peek k' f q ih =>exact ih _ _
  | pop k' f q ih =>
    simp only [stepAuxT,pushes]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [upd_self,List.length_tail]; omega
    · rw [upd_ne h]
  | load a q ih =>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [stepAuxT,pushes]
    cases f v
    · exact (ih₂ v S).trans (by have:= le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have:= le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f =>simp [stepAuxT,pushes]
  | halt =>simp [stepAuxT,pushes]
end pushes
noncomputable def maxPush (tm:FinTM2):ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l =>pushes (tm.m l)
theorem step_length (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h:tmStep tm.m c=some c') (k:tm.K) :
    (c'.stk k).length≤ (c.stk k).length+maxPush tm:= by
  obtain ⟨l,v,S⟩:= c
  cases l with
  | none =>simp [tmStep] at h
  | some l =>
    simp only [tmStep,Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have:pushes (tm.m l)≤ maxPush tm :=
      Finset.le_sup (f:= fun l =>pushes (tm.m l)) (@mem_all tm.Λ tm.ΛFin l)
    simpa using this
theorem run_length (tm:FinTM2) (k:tm.K) :
    ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (tmStep tm.m))^[n] (some a)=some b →
      (b.stk k).length≤ (a.stk k).length+maxPush tm * n:= by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have:a=b:= Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [iter_succ] at hab
    cases hfa:tmStep tm.m a with
    | none =>
      have e:flip bind (tmStep tm.m) (some a)=none:= hfa
      rw [e,iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind (tmStep tm.m) (some a)=some c:= hfa
      rw [e] at hab
      have h1:= ih c b hab
      have h2:= step_length tm a c hfa k
      rw [Nat.mul_succ]; omega
theorem initList_eq (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main,tm.initialState,upd (fun _ =>[]) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):= by
  unfold initList
  congr 1
  funext k
  by_cases h:k=tm.k₀
  · subst h; simp
  · simp [h]
theorem haltList_eq (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none,tm.initialState,upd (fun _ =>[]) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):= by
  unfold haltList
  congr 1
  funext k
  by_cases h:k=tm.k₁
  · subst h; simp
  · simp [h]
theorem eval_mono (p:Polynomial ℕ) {x y:ℕ} (h:x≤ y):p.eval x≤ p.eval y:= by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [evalAddP,evalAddP]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial,Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def pushList:BitTape→ TM2.Stmt (fun _:Unit =>Bool) Unit Bool
  | [] =>.halt
  | a :: l =>.push () (fun _ =>a) (pushList l)
def constListProg (l:BitTape):Unit→ TM2.Stmt (fun _:Unit =>Bool) Unit Bool :=
  fun _ =>.pop () (fun _ o =>o.isSome)
    (.branch (fun s =>s)
      (.load (fun _ =>false) (.goto fun _ =>()))
      (pushList l.reverse))
def constList (l:BitTape):FinTM2 where
  K:= Unit
  k₀:= ()
  k₁:= ()
  Γ _:= Bool
  Λ:= Unit
  main:= ()
  σ:= Bool
  initialState:= false
  m:= constListProg l
abbrev CLCfg:Type:= TM2.Cfg (fun _:Unit =>Bool) Unit Bool
theorem update_unit (S T:BitTape) :
    upd (fun _:Unit =>S) () T=fun _ =>T:= by
  funext k
  simp
theorem pushList_stepAux (l:BitTape) (v:Bool) (S:BitTape) :
    stepAuxT (pushList l) v (fun _:Unit =>S) =
      (⟨none,v,fun _ =>l.reverse ++ S⟩:CLCfg):= by
  induction l generalizing S with
  | nil =>rfl
  | cons a l ih =>
    simp only [pushList,stepAuxT]
    rw [update_unit,ih]
    simp
theorem constList_cons (l:BitTape) (x:Bool) (a:BitTape) :
    tmStep (constListProg l) (⟨some (),false,fun _ =>x :: a⟩:CLCfg) =
      some ⟨some (),false,fun _ =>a⟩:= by
  simp only [tmStep,constListProg,stepAuxT]
  rw [update_unit]
  simp
theorem constList_nil (l:BitTape) :
    tmStep (constListProg l) (⟨some (),false,fun _ =>[]⟩:CLCfg) =
      some ⟨none,false,fun _ =>l⟩:= by
  simp only [tmStep,constListProg,stepAuxT]
  rw [update_unit]
  simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  rw [pushList_stepAux]
  simp
theorem constList_loop (l:BitTape) (a:BitTape) :
    (flip bind (tmStep (constListProg l)))^[a.length+1]
        (some (⟨some (),false,fun _ =>a⟩:CLCfg)) =
      some ⟨none,false,fun _ =>l⟩:= by
  induction a with
  | nil =>exact constList_nil l
  | cons x a ih =>
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (constListProg l))
        (some (⟨some (),false,fun _ =>x :: a⟩:CLCfg)) =
        some ⟨some (),false,fun _ =>a⟩:= constList_cons l x a
    rw [e,ih]
theorem constList_run (l:BitTape) (a:BitTape) :
    (flip bind (tmStep (constListProg l)))^[a.length+1]
        (some (initList (constList l) a))=some (haltList (constList l) l):= by
  refine (congrArg (fun c =>(flip bind (tmStep (constListProg l)))^[a.length+1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (tmStep (constListProg l)))^[a.length+1]
    (some (⟨some (),false,upd (fun _ =>[]) () a⟩:CLCfg)) =
    some (⟨none,false,upd (fun _ =>[]) () l⟩:CLCfg)
  rw [update_unit,update_unit]
  exact constList_loop l a
theorem constList_polyTime (l:BitTape) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) (fun _:BitTape =>l)) :=
  ⟨{
    tm:= constList l
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= Polynomial.X+1
    outputsFun:= fun a =>
      { steps:= a.length+1
        evals_in_steps:= by
          have hm:∀ l:BitTape,List.map (Equiv.refl Bool).invFun l=l:= fun l => by simp
          exact (congrArg (fun x =>(flip bind (tmStep (constListProg l)))^[a.length+1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x =>some (haltList (constList l) x)) (hm l).symm))
        steps_le_m:= by simp } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
section update
variable {ι:Type} [DecidableEq ι] {β:ι→ Type}
theorem update3_fst (E:∀ i,β i) {a b c:ι} (hab:a ≠ b) (hac:a ≠ c)
    (x x':β a) (y:β b) (z:β c) :
    upd (upd (upd (upd E a x) b y) c z) a x' =
      upd (upd (upd E a x') b y) c z:= by
  rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
theorem update3_snd (E:∀ i,β i) {a b c:ι} (hbc:b ≠ c)
    (x:β a) (y y':β b) (z:β c) :
    upd (upd (upd (upd E a x) b y) c z) b y' =
      upd (upd (upd E a x) b y') c z:= by
  rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:= Option (M1.K ⊕ M2.K)
abbrev CΓ:CK M1 M2→ Type
  | none =>M2.Γ M2.k₀
  | some (injL k) =>M1.Γ k
  | some (injR k) =>M2.Γ k
abbrev CΛ:Type:= M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ:Type:= M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q =>.push (some (injL k)) (fun s =>f s.1) (tr1 q)
  | .peek k f q =>.peek (some (injL k)) (fun s o =>(f s.1 o,s.2)) (tr1 q)
  | .pop k f q =>.pop (some (injL k)) (fun s o =>(f s.1 o,s.2)) (tr1 q)
  | .load a q =>.load (fun s =>(a s.1,s.2)) (tr1 q)
  | .branch f q₁ q₂ =>.branch (fun s =>f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f =>.goto (fun s =>injL (f s.1))
  | .halt =>.goto (fun _ =>injR (injR false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q =>.push (some (injR k)) (fun s =>f s.2.1) (tr2 q)
  | .peek k f q =>.peek (some (injR k)) (fun s o =>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .pop k f q =>.pop (some (injR k)) (fun s o =>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .load a q =>.load (fun s =>(s.1,a s.2.1,s.2.2)) (tr2 q)
  | .branch f q₁ q₂ =>.branch (fun s =>f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f =>.goto (fun s =>injR (injL (f s.2.1)))
  | .halt =>.halt
variable (M1 M2)
def tA (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀)→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none =>.goto (fun _ =>injR (injL M2.main))
  | some d =>
    .pop (some (injL M1.k₁)) (fun s o =>(s.1,s.2.1,o.map φ))
      (.branch (fun s =>s.2.2.isSome)
        (.push none (fun s =>s.2.2.getD d) (.goto fun _ =>injR (injR false)))
        (.goto fun _ =>injR (injR true)))
def tB:Option (M2.Γ M2.k₀)→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none =>.goto (fun _ =>injR (injL M2.main))
  | some d =>
    .pop none (fun s o =>(s.1,s.2.1,o))
      (.branch (fun s =>s.2.2.isSome)
        (.push (some (injR M2.k₀)) (fun s =>s.2.2.getD d)
          (.goto fun _ =>injR (injR true)))
        (.goto fun _ =>injR (injL M2.main)))
def prog (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)) :
    CΛ M1 M2→ TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | injL l =>tr1 (M1.m l)
  | injR (injL l) =>tr2 (M2.m l)
  | injR (injR false) =>tA M1 M2 φ d
  | injR (injR true) =>tB M1 M2 d
def comp (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2 :=
  haveI:= M1.kFin
  haveI:= M2.kFin
  haveI:= M1.ΛFin
  haveI:= M2.ΛFin
  haveI:= M1.σFin
  haveI:= M2.σFin
  haveI:= M2.Γk₀Fin
  { K:= CK M1 M2
    k₀:= some (injL M1.k₀)
    k₁:= some (injR M2.k₁)
    Γ:= CΓ M1 M2
    Λ:= CΛ M1 M2
    main:= injL M1.main
    σ:= Cσ M1 M2
    initialState:= (M1.initialState,M2.initialState,none)
    Γk₀Fin:= M1.Γk₀Fin
    m:= prog M1 M2 φ d }
variable {M1 M2}
def embStk1 (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none =>[]
  | some (injL k) =>S k
  | some (injR _) =>[]
def embStk2 (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none =>[]
  | some (injL _) =>[]
  | some (injR k) =>S k
theorem embStk1_update (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)) :
    (embStk1 (upd S k x):∀ k,List (CΓ M1 M2 k)) =
      upd (embStk1 S) (some (injL k)) x:= by
  funext j
  rcases j with _ | j | j
  · rw [upd_ne (by simp)]; rfl
  · by_cases h:j=k
    · subst h
      rw [upd_self]
      show upd S j x j=x
      rw [upd_self]
    · rw [upd_ne (by simpa using h)]
      show upd S k x j=S j
      rw [upd_ne h]
  · rw [upd_ne (by simp)]; rfl
theorem embStk2_update (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)) :
    (embStk2 (upd S k x):∀ k,List (CΓ M1 M2 k)) =
      upd (embStk2 S) (some (injR k)) x:= by
  funext j
  rcases j with _ | j | j
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · by_cases h:j=k
    · subst h
      rw [upd_self]
      show upd S j x j=x
      rw [upd_self]
    · rw [upd_ne (by simpa using h)]
      show upd S k x j=S j
      rw [upd_ne h]
theorem embStk1_nil :
    (embStk1 (fun _ =>[]):∀ k,List (CΓ M1 M2 k))=fun _ =>[]:= by
  funext j; rcases j with _ | j | j <;> rfl
theorem embStk2_nil :
    (embStk2 (fun _ =>[]):∀ k,List (CΓ M1 M2 k))=fun _ =>[]:= by
  funext j; rcases j with _ | j | j <;> rfl
def emb1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (injR (injR false)) injL),(c.var,w),embStk1 c.stk⟩
def emb2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l =>injR (injL l)),(u,c.var,b),embStk2 c.stk⟩
theorem sim1 (w:M2.σ × Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
    (S:∀ k,List (M1.Γ k)) :
    stepAuxT (tr1 q) ((v,w):Cσ M1 M2) (embStk1 S)=emb1 w (stepAuxT q v S):= by
  induction q generalizing v S with
  | push k f q ih =>
    have:= ih v (upd S k (f v :: S k))
    rw [embStk1_update] at this
    exact this
  | peek k f q ih =>exact ih _ _
  | pop k f q ih =>
    have:= ih (f v (S k).head?) (upd S k (S k).tail)
    rw [embStk1_update] at this
    exact this
  | load a q ih =>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1,stepAuxT]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f =>rfl
  | halt =>rfl
theorem sim2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
    (S:∀ k,List (M2.Γ k)) :
    stepAuxT (tr2 q) ((u,v,b):Cσ M1 M2) (embStk2 S)=emb2 u b (stepAuxT q v S):= by
  induction q generalizing v S with
  | push k f q ih =>
    have:= ih v (upd S k (f v :: S k))
    rw [embStk2_update] at this
    exact this
  | peek k f q ih =>exact ih _ _
  | pop k f q ih =>
    have:= ih (f v (S k).head?) (upd S k (S k).tail)
    rw [embStk2_update] at this
    exact this
  | load a q ih =>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2,stepAuxT]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f =>rfl
  | halt =>rfl
variable (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
theorem step1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h:tmStep M1.m c=some c') :
    tmStep (prog M1 M2 φ d) (emb1 w c)=some (emb1 w c'):= by
  obtain ⟨l,v,S⟩:= c
  cases l with
  | none =>simp [tmStep] at h
  | some l =>
    simp only [tmStep,Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)
theorem step2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h:tmStep M2.m c=some c') :
    tmStep (prog M1 M2 φ d) (emb2 u b c)=some (emb2 u b c'):= by
  obtain ⟨l,v,S⟩:= c
  cases l with
  | none =>simp [tmStep] at h
  | some l =>
    simp only [tmStep,Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k) :=
  upd (upd (upd (fun _ =>[])
    (some (injL M1.k₁)) l) none t) (some (injR M2.k₀)) u
theorem st_fst (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (injL M1.k₁))=l:= by
  unfold st
  rw [upd_ne (by simp),upd_ne (by simp),upd_self]
theorem st_snd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:= by
  unfold st
  rw [upd_ne (by simp),upd_self]
theorem st_thd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (injR M2.k₀))=u:= by
  unfold st
  rw [upd_self]
theorem st_set_fst (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    upd (st l t u:∀ k,List (CΓ M1 M2 k)) (some (injL M1.k₁)) l'=st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _
theorem st_set_snd (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)) :
    upd (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u :=
  update3_snd _ (by simp) _ _ _ _
theorem st_set_thd (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)) :
    upd (st l t u:∀ k,List (CΓ M1 M2 k)) (some (injR M2.k₀)) u'=st l t u' :=
  Function.update_idem _ _ _
theorem st_start (l:List (M1.Γ M1.k₁)) :
    (st l [] []:∀ k,List (CΓ M1 M2 k)) =
      upd (fun _ =>[]:∀ k,List (CΓ M1 M2 k)) (some (injL M1.k₁)) l:= by
  unfold st
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [upd_ne (by simp)]
  · rw [upd_ne (by simp),upd_ne (by simp)]
theorem st_end (u:List (M2.Γ M2.k₀)) :
    (st [] [] u:∀ k,List (CΓ M1 M2 k)) =
      upd (fun _ =>[]:∀ k,List (CΓ M1 M2 k)) (some (injR M2.k₀)) u:= by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [upd_ne (by simp)]
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {M1 M2:FinTM2} (φ:M1.Γ M1.k₁→ M2.Γ M2.k₀)
abbrev CCfg (M1 M2:FinTM2):Type:= TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
theorem stepA_cons (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    tmStep (prog M1 M2 φ (some dd))
        (⟨some (injR (injR false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2) =
      some ⟨some (injR (injR false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩:= by
  simp only [tmStep,prog,tA,stepAuxT]
  rw [st_fst]
  simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst,st_snd,st_set_snd]
theorem stepA_nil (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (t u:List (M2.Γ M2.k₀)) :
    tmStep (prog M1 M2 φ (some dd))
        (⟨some (injR (injR false)),(v1,v2,b),st [] t u⟩:CCfg M1 M2) =
      some ⟨some (injR (injR true)),(v1,v2,none),st [] t u⟩:= by
  simp only [tmStep,prog,tA,stepAuxT]
  rw [st_fst]
  simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
  rw [st_set_fst]
theorem stepB_cons (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)) :
    tmStep (prog M1 M2 φ (some dd))
        (⟨some (injR (injR true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2) =
      some ⟨some (injR (injR true)),(v1,v2,some x),st [] t (x :: u)⟩:= by
  simp only [tmStep,prog,tB,stepAuxT]
  rw [st_snd]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
  rw [st_set_snd,st_thd,st_set_thd]
theorem stepB_nil (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (u:List (M2.Γ M2.k₀)) :
    tmStep (prog M1 M2 φ (some dd))
        (⟨some (injR (injR true)),(v1,v2,b),st [] [] u⟩:CCfg M1 M2) =
      some ⟨some (injR (injL M2.main)),(v1,v2,none),st [] [] u⟩:= by
  simp only [tmStep,prog,tB,stepAuxT]
  rw [st_snd]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [st_set_snd]
theorem loopA (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)) :
    ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (tmStep (prog M1 M2 φ (some dd))))^[l.length+1]
          (some (⟨some (injR (injR false)),(v1,v2,b),st l t u⟩:CCfg M1 M2)) =
        some ⟨some (injR (injR true)),(v1,v2,none),st [] ((l.map φ).reverse ++ t) u⟩:= by
  intro l
  induction l with
  | nil =>intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (prog M1 M2 φ (some dd)))
        (some (⟨some (injR (injR false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2)) =
        some ⟨some (injR (injR false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e,ih]
    simp
theorem loopB (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) :
    ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (tmStep (prog M1 M2 φ (some dd))))^[t.length+1]
          (some (⟨some (injR (injR true)),(v1,v2,b),st [] t u⟩:CCfg M1 M2)) =
        some ⟨some (injR (injL M2.main)),(v1,v2,none),st [] [] (t.reverse ++ u)⟩:= by
  intro t
  induction t with
  | nil =>intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (prog M1 M2 φ (some dd)))
        (some (⟨some (injR (injR true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2)) =
        some ⟨some (injR (injR true)),(v1,v2,some x),st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e,ih]
    simp
theorem transfer (d:Option (M2.Γ M2.k₀)) (hd:d=none→ IsEmpty (M2.Γ M2.k₀))
    (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)) :
    ∃ n,n≤ 2 * o.length+2 ∧
      (flip bind (tmStep (prog M1 M2 φ d)))^[n]
          (some (⟨some (injR (injR false)),(v1,v2,none),
            upd (fun _ =>[]:∀ k,List (CΓ M1 M2 k)) (some (injL M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (injR (injL M2.main)),(v1,v2,none),
          upd (fun _ =>[]:∀ k,List (CΓ M1 M2 k)) (some (injR M2.k₀))
            (o.map φ)⟩:= by
  cases d with
  | none =>
    have:= hd rfl
    have ho:o=[]:= by
      cases o with
      | nil =>rfl
      | cons x _ =>exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1,by omega,?_⟩
    show some _=some _
    simp only [prog,tA,stepAuxT,mapN]
    rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length+1+(o.length+1),by simp; omega,?_⟩
    rw [iter_add,← st_start,loopA,loopB,← st_end]
    simp
theorem emb1_init (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:= by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_,_,embStk1 _⟩:CCfg M1 M2)=_
  rw [embStk1_update,embStk1_nil]
  rfl
theorem emb1_halt (w:M2.σ × Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (injR (injR false)),(M1.initialState,w),
        upd (fun _ =>[]:∀ k,List (CΓ M1 M2 k)) (some (injL M1.k₁)) o⟩ :
        CCfg M1 M2):= by
  rw [haltList_eq]
  show (⟨_,_,embStk1 _⟩:CCfg M1 M2)=_
  rw [embStk1_update,embStk1_nil]
  rfl
theorem emb2_init (u:M1.σ) (i:List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (injR (injL M2.main)),(u,M2.initialState,none),
        upd (fun _ =>[]:∀ k,List (CΓ M1 M2 k)) (some (injR M2.k₀)) i⟩ :
        CCfg M1 M2):= by
  rw [initList_eq]
  show (⟨_,_,embStk2 _⟩:CCfg M1 M2)=_
  rw [embStk2_update,embStk2_nil]
  rfl
theorem emb2_halt (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:= by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_,_,embStk2 _⟩:CCfg M1 M2)=_
  rw [embStk2_update,embStk2_nil]
  rfl
theorem comp_run (d:Option (M2.Γ M2.k₀)) (hd:d=none→ IsEmpty (M2.Γ M2.k₀))
    (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
    (h1:(flip bind (tmStep M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
    (h2:(flip bind (tmStep M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n,n≤ s1+(2 * o1.length+2)+s2∧o1.length≤ i.length+maxPush M1 * s1 ∧
      (flip bind (tmStep (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2):= by
  have p1:= simulate (tmStep M1.m) (tmStep (prog M1 M2 φ d))
    (emb1 (M2.initialState,none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d,emb1_halt] at p1
  obtain ⟨nt,hnt,pt⟩:= transfer φ d hd M1.initialState M2.initialState o1
  have p2:= simulate (tmStep M2.m) (tmStep (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init,emb2_halt φ d] at p2
  refine ⟨s2+(nt+s1),by omega,?_,?_⟩
  · have:= run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq,initList_eq] at this
    simp only [upd_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h:M1.k₁=M1.k₀
    · rw [h,upd_self]
    · rw [upd_ne h]; simp
  · rw [iter_add,iter_add,p1,pt,p2]
    rfl
theorem comp_polyTime {α β γ αΓ βΓ γΓ:Type} (ea:α→ List αΓ) (eb:β→ List βΓ)
    (ec:γ→ List γΓ) (f:α→ β) (g:β→ γ) (c1:TM2ComputableInPolyTime ea eb f)
    (c2:TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a =>g (f a))):= by
  classical
  let φ:c1.tm.Γ c1.tm.k₁→ c2.tm.Γ c2.tm.k₀ :=
    fun x =>c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d:Option (c2.tm.Γ c2.tm.k₀) :=
    if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd:d=none→ IsEmpty (c2.tm.Γ c2.tm.k₀):= by
    intro h
    by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d,hn] at h
    · exact not_nonempty_iff.mp hn
  let T:Polynomial ℕ :=
    c1.time+(Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time)
  have key:∀ a,∃ n,n≤ T.eval (ea a).length ∧
      (flip bind (tmStep (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))):= by
    intro a
    have r1:= c1.outputsFun a
    have r2:= c2.outputsFun (f a)
    have hφ:(List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)):= by
      rw [mapMap]
      refine List.map_congr_left fun y _ =>?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2:(flip bind (tmStep c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):= by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n,hn,hlen,hrun⟩:= comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n,hn.trans ?_,hrun⟩
    have b1:= r1.steps_le_m
    have b2:= r2.steps_le_m
    simp only [len_map] at hlen
    have hmul:maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time:= Nat.mul_le_mul_left _ b1
    have b3:Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length+maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time:= eval_mono _ (by omega)
    simp only [T,evalAddP,evalMulP,evalCP,
      evalXP,Polynomial.eval_comp,len_map]
    omega
  exact ⟨{
    tm:= comp c1.tm c2.tm φ d
    inputAlphabet:= c1.inputAlphabet
    outputAlphabet:= c2.outputAlphabet
    time:= T
    outputsFun:= fun a =>
      ⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {Γ₀ Γ₁:Type}
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool→ Type
  | some false =>Γ₀
  | none =>Option Γ₀
  | some true =>Γ₁
def fmProg (φ:Γ₀→ Option Γ₁) (d:Option Γ₁):Bool→ TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o =>o)
      (.branch (fun s =>s.isSome)
        (.push none (fun s =>s) (.goto fun _ =>false))
        (.goto fun _ =>true))
  | true =>
    .pop none (fun _ o =>o.join)
      (.branch (fun s =>s.isSome)
        (.branch (fun s =>(s.bind φ).isSome)
          (match d with
            | some dd =>.push (some true) (fun s =>(s.bind φ).getD dd) (.goto fun _ =>true)
            | none =>.goto fun _ =>true)
          (.goto fun _ =>true))
        .halt)
def fm [Fintype Γ₀] (φ:Γ₀→ Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:= Option Bool
  k₀:= some false
  k₁:= some true
  Γ:= FΓ Γ₀ Γ₁
  Λ:= Bool
  main:= false
  σ:= Option Γ₀
  initialState:= none
  Γk₀Fin:= inferInstanceAs (Fintype Γ₀)
  m:= fmProg φ d
def fst3 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k) :=
  upd (upd (upd (fun _ =>[])
    (some false) l) none t) (some true) u
theorem fst3_fst (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u (some false)=l:= by
  unfold fst3
  rw [upd_ne (by simp),upd_ne (by simp),upd_self]
theorem fst3_snd (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u none=t:= by
  unfold fst3
  rw [upd_ne (by simp),upd_self]
theorem fst3_thd (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u (some true)=u:= by
  unfold fst3
  rw [upd_self]
theorem fst3_set_fst (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    upd (fst3 l t u) (some false) l'=fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _
theorem fst3_set_snd (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁) :
    upd (fst3 l t u) none t'=fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _
theorem fst3_set_thd (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁) :
    upd (fst3 l t u) (some true) u'=fst3 l t u' :=
  Function.update_idem _ _ _
theorem fst3_start (l:List Γ₀) :
    (fst3 l [] []:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      upd (fun _ =>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:= by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [upd_ne (by simp)]
  · rw [upd_ne (by simp),upd_ne (by simp)]
theorem fst3_end (u:List Γ₁) :
    (fst3 [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      upd (fun _ =>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:= by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [upd_ne (by simp)]
abbrev FCfg (Γ₀ Γ₁:Type):Type:= TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ:Γ₀→ Option Γ₁) (d:Option Γ₁)
theorem fmA_cons (b:Option Γ₀) (x:Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (fmProg φ d) (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some false,some x,fst3 l (some x :: t) u⟩:= by
  simp only [tmStep,fmProg,stepAuxT]
  rw [fst3_fst]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
  rw [fst3_set_fst,fst3_snd,fst3_set_snd]
theorem fmA_nil (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (fmProg φ d) (⟨some false,b,fst3 [] t u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some true,none,fst3 [] t u⟩:= by
  simp only [tmStep,fmProg,stepAuxT]
  rw [fst3_fst]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [fst3_set_fst]
theorem fmB_cons (hd:d=none→ ∀ x,φ x=none) (b:Option Γ₀) (x:Γ₀)
    (t:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (fmProg φ d) (⟨some true,b,fst3 [] (some x :: t) u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some true,some x,fst3 [] t ((φ x).toList ++ u)⟩:= by
  simp only [tmStep,fmProg,stepAuxT]
  rw [fst3_snd]
  simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
    Bool.cond_true,Option.bind_some]
  rw [fst3_set_snd]
  cases hφ:φ x with
  | none =>simp
  | some y =>
    cases d with
    | none =>rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some,Bool.cond_true,stepAuxT,
        Option.toList_some,List.singleton_append]
      rw [fst3_thd,fst3_set_thd]
      simp [hφ]
theorem fmB_nil (b:Option Γ₀) (u:List Γ₁) :
    tmStep (fmProg φ d) (⟨some true,b,fst3 [] [] u⟩:FCfg Γ₀ Γ₁) =
      some ⟨none,none,fst3 [] [] u⟩:= by
  simp only [tmStep,fmProg,stepAuxT]
  rw [fst3_snd]
  simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]
theorem fmLoopA (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
      (flip bind (tmStep (fmProg φ d)))^[l.length+1]
          (some (⟨some false,b,fst3 l t u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some true,none,fst3 [] (l.reverse.map some ++ t) u⟩:= by
  intro l
  induction l with
  | nil =>intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (fmProg φ d))
        (some (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some false,some x,fst3 l (some x :: t) u⟩:= fmA_cons φ d b x l t u
    rw [e,ih]
    simp
theorem fmLoopB (hd:d=none→ ∀ x,φ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
      (flip bind (tmStep (fmProg φ d)))^[t.length+1]
          (some (⟨some true,b,fst3 [] (t.map some) u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨none,none,fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩:= by
  intro t
  induction t with
  | nil =>intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (fmProg φ d))
        (some (⟨some true,b,fst3 [] ((x :: t).map some) u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some true,some x,fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e,ih]
    cases hφ:φ x <;> simp [hφ]
theorem fm_run [Fintype Γ₀] (hd:d=none→ ∀ x,φ x=none) (l:List Γ₀) :
    (flip bind (tmStep (fmProg φ d)))^[l.length+1+(l.length+1)]
        (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):= by
  refine (congrArg (fun c =>(flip bind (tmStep (fmProg φ d)))^[l.length+1+(l.length+1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (tmStep (fmProg φ d)))^[l.length+1+(l.length+1)]
    (some (⟨some false,none,upd (fun _ =>[]) (some false) l⟩:FCfg Γ₀ Γ₁)) =
    some (⟨none,none,upd (fun _ =>[]) (some true) (l.filterMap φ)⟩:FCfg Γ₀ Γ₁)
  rw [iter_add,← fst3_start,fmLoopA,← fst3_end]
  have:= fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
theorem filterMap_polyTime {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (φ:αΓ→ Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f):= by
  classical
  let d:Option βΓ:= if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:d=none→ ∀ x,φ x=none:= by
    intro hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ:φ x with
      | none =>rfl
      | some y =>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:= fm φ d
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= Polynomial.C 2 * Polynomial.X+Polynomial.C 2
    outputsFun:= fun a =>
      { steps:= (ea a).length+1+((ea a).length+1)
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          have:= fm_run φ d hd (ea a)
          exact (congrArg (fun l =>(flip bind (tmStep (fmProg φ d)))^[(ea a).length+1 +
            ((ea a).length+1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l =>some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:= by
          simp only [evalAddP,evalMulP,evalCP,
            evalXP]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive TPK:Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq
instance:Fintype TPK :=
  Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x => by cases x <;> simp)
inductive TPL:Type
  | a | b | c | e
  deriving DecidableEq
instance:Fintype TPL :=
  Fintype.ofList [.a,.b,.c,.e] (fun x => by cases x <;> simp)
variable {Γ₀ Γ₁:Type}
abbrev TPΓ (Γ₀ Γ₁:Type):TPK→ Type
  | .inp =>Γ₀
  | .t1 =>Option Γ₀
  | .t2 =>Option Γ₀
  | .t3 =>Option Γ₀
  | .out =>Γ₁
def tpWrite (φ:Γ₀→ Option Γ₁) (d:Option Γ₁) (lbl:TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s =>(s.bind φ).isSome)
    (match d with
      | some dd =>.push .out (fun s =>(s.bind φ).getD dd) (.goto fun _ =>lbl)
      | none =>.goto fun _ =>lbl)
    (.goto fun _ =>lbl)
def tpProg (φ₁ φ₂:Γ₀→ Option Γ₁) (d:Option Γ₁) :
    TPL→ TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o =>o)
      (.branch (fun s =>s.isSome)
        (.push .t1 (fun s =>s) (.goto fun _ =>.a))
        (.goto fun _ =>.b))
  | .b =>
    .pop .t1 (fun _ o =>o.join)
      (.branch (fun s =>s.isSome)
        (.push .t2 (fun s =>s) (tpWrite φ₂ d .b))
        (.goto fun _ =>.c))
  | .c =>
    .pop .t2 (fun _ o =>o.join)
      (.branch (fun s =>s.isSome)
        (.push .t3 (fun s =>s) (.goto fun _ =>.c))
        (.goto fun _ =>.e))
  | .e =>
    .pop .t3 (fun _ o =>o.join)
      (.branch (fun s =>s.isSome)
        (tpWrite φ₁ d .e)
        .halt)
def tp [Fintype Γ₀] (φ₁ φ₂:Γ₀→ Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:= TPK
  k₀:= .inp
  k₁:= .out
  Γ:= TPΓ Γ₀ Γ₁
  Λ:= TPL
  main:= .a
  σ:= Option Γ₀
  initialState:= none
  Γk₀Fin:= inferInstanceAs (Fintype Γ₀)
  m:= tpProg φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
  | .inp =>l
  | .t1 =>a
  | .t2 =>b
  | .t3 =>c
  | .out =>u
theorem st5_set_inp (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    upd (st5 l a b c u) .inp l'=st5 l' a b c u:= by
  funext k; cases k <;> simp [st5]
theorem st5_set_t1 (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁) :
    upd (st5 l a b c u) .t1 a'=st5 l a' b c u:= by
  funext k; cases k <;> simp [st5]
theorem st5_set_t2 (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁) :
    upd (st5 l a b c u) .t2 b'=st5 l a b' c u:= by
  funext k; cases k <;> simp [st5]
theorem st5_set_t3 (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁) :
    upd (st5 l a b c u) .t3 c'=st5 l a b c' u:= by
  funext k; cases k <;> simp [st5]
theorem st5_set_out (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁) :
    upd (st5 l a b c u) .out u'=st5 l a b c u':= by
  funext k; cases k <;> simp [st5]
theorem st5_start (l:List Γ₀) :
    (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      upd (fun _ =>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:= by
  funext k; cases k <;> simp [st5]
theorem st5_end (u:List Γ₁) :
    (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      upd (fun _ =>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:= by
  funext k; cases k <;> simp [st5]
abbrev TPCfg (Γ₀ Γ₁:Type):Type:= TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂:Γ₀→ Option Γ₁) (d:Option Γ₁)
theorem tpA_cons (s:Option Γ₀) (x:Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
    (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:= by
  simp [tmStep,tpProg,stepAuxT,st5,st5_set_inp,st5_set_t1]
theorem tpA_nil (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .b,none,st5 [] a b c u⟩:= by
  simp [tmStep,tpProg,stepAuxT,st5,st5_set_inp]
theorem tpB_cons (hd:d=none→ ∀ x,φ₂ x=none) (s:Option Γ₀) (x:Γ₀)
    (a b c:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x :: a) b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .b,some x,st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩:= by
  cases hφ:φ₂ x with
  | none =>
    cases d <;>
      simp [tmStep,tpProg,tpWrite,stepAuxT,st5,st5_set_t1,st5_set_t2,hφ]
  | some y =>
    cases d with
    | none =>rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [tmStep,tpProg,tpWrite,stepAuxT,st5,st5_set_t1,st5_set_t2,
        st5_set_out,hφ]
theorem tpB_nil (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .c,none,st5 [] [] b c u⟩:= by
  simp [tmStep,tpProg,stepAuxT,st5,st5_set_t1]
theorem tpC_cons (s:Option Γ₀) (x:Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x :: b) c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .c,some x,st5 [] [] b (some x :: c) u⟩:= by
  simp [tmStep,tpProg,stepAuxT,st5,st5_set_t2,st5_set_t3]
theorem tpC_nil (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .e,none,st5 [] [] [] c u⟩:= by
  simp [tmStep,tpProg,stepAuxT,st5,st5_set_t2]
theorem tpE_cons (hd:d=none→ ∀ x,φ₁ x=none) (s:Option Γ₀) (x:Γ₀)
    (c:List (Option Γ₀)) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x :: c) u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList ++ u)⟩:= by
  cases hφ:φ₁ x with
  | none =>
    cases d <;>
      simp [tmStep,tpProg,tpWrite,stepAuxT,st5,st5_set_t3,hφ]
  | some y =>
    cases d with
    | none =>rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [tmStep,tpProg,tpWrite,stepAuxT,st5,st5_set_t3,st5_set_out,hφ]
theorem tpE_nil (s:Option Γ₀) (u:List Γ₁) :
    tmStep (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨none,none,st5 [] [] [] [] u⟩:= by
  simp [tmStep,tpProg,stepAuxT,st5,st5_set_t3]
theorem tpLoopA (b c:List (Option Γ₀)) (u:List Γ₁) :
    ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1]
          (some (⟨some .a,s,st5 l a b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .b,none,st5 [] (l.reverse.map some ++ a) b c u⟩:= by
  intro l
  induction l with
  | nil =>intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (tpProg φ₁ φ₂ d))
        (some (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:= tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e,ih]
    simp
theorem tpLoopB (hd:d=none→ ∀ x,φ₂ x=none) (c:List (Option Γ₀)) :
    ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (tmStep (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .c,none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩:= by
  intro t
  induction t with
  | nil =>intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (tpProg φ₁ φ₂ d))
        (some (⟨some .b,s,st5 [] ((x :: t).map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .b,some x,st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e,ih]
    cases hφ:φ₂ x <;> simp [hφ]
theorem tpLoopC (u:List Γ₁) :
    ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (tmStep (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .e,none,st5 [] [] [] (t.reverse.map some ++ c) u⟩:= by
  intro t
  induction t with
  | nil =>intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (tpProg φ₁ φ₂ d))
        (some (⟨some .c,s,st5 [] [] ((x :: t).map some) c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .c,some x,st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e,ih]
    simp
theorem tpLoopE (hd:d=none→ ∀ x,φ₁ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (tmStep (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩:= by
  intro t
  induction t with
  | nil =>intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (tpProg φ₁ φ₂ d))
        (some (⟨some .e,s,st5 [] [] [] ((x :: t).map some) u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e,ih]
    cases hφ:φ₁ x <;> simp [hφ]
theorem tp_run [Fintype Γ₀] (hd₁:d=none→ ∀ x,φ₁ x=none)
    (hd₂:d=none→ ∀ x,φ₂ x=none) (l:List Γ₀) :
    (flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
        (l.length+1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)):= by
  refine (congrArg (fun c =>(flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1 +
    (l.length+1)+(l.length+1)+(l.length+1)]
    (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
  show (flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
      (l.length+1)]
    (some (⟨some .a,none,upd (fun _ =>[]) .inp l⟩:TPCfg Γ₀ Γ₁)) =
    some (⟨none,none,upd (fun _ =>[]) .out
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)
  have hA:(flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .a,none,st5 l [] [] [] []⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:= by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB:(flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:= by
    have:= tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC:(flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:= by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE:(flip bind (tmStep (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩:= by
    have:= tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [iter_add,iter_add,iter_add,
    ← st5_start,hA,hB,hC,hE,st5_end]
theorem twoPass_polyTime {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (φ₁ φ₂:αΓ→ Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):= by
  classical
  let d:Option βΓ:= if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ φ:αΓ→ Option βΓ,d=none→ ∀ x,φ x=none:= by
    intro φ hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ:φ x with
      | none =>rfl
      | some y =>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:= tp φ₁ φ₂ d
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= Polynomial.C 4 * Polynomial.X+Polynomial.C 4
    outputsFun:= fun a =>
      { steps:= (ea a).length+1+((ea a).length+1)+((ea a).length+1) +
          ((ea a).length+1)
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          have:= tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l =>(flip bind (tmStep (tpProg φ₁ φ₂ d)))^[(ea a).length+1 +
            ((ea a).length+1)+((ea a).length+1)+((ea a).length+1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l =>some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:= by
          simp only [evalAddP,evalMulP,evalCP,
            evalXP]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive FX
  | I | W | T | O
  deriving DecidableEq
instance:Fintype FX :=
  Fintype.ofList [FX.I,FX.W,FX.T,FX.O] (fun x => by cases x <;> simp)
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq
instance:Fintype FL :=
  Fintype.ofList [FL.l1,FL.l2,FL.l3,FL.l4,FL.l5] (fun x => by cases x <;> simp)
variable (M:FinTM2)
abbrev FstΓ:M.K ⊕ FX→ Type
  | injL k =>M.Γ k
  | injR FX.I =>Bool ⊕ Bool
  | injR FX.W =>Bool
  | injR FX.T =>Bool
  | injR FX.O =>Bool ⊕ Bool
abbrev FstΛ:Type:= M.Λ ⊕ FL
abbrev Fstσ:Type:= M.σ × Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool)→ Bool
  | none =>false
  | some (injL b) =>b
  | some (injR b) =>b
def isFst:Option (Bool ⊕ Bool)→ Bool
  | some (injL _) =>true
  | _ =>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ→ TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q =>.push (injL k) (fun s =>f s.1) (trF q)
  | .peek k f q =>.peek (injL k) (fun s o =>(f s.1 o,s.2)) (trF q)
  | .pop k f q =>.pop (injL k) (fun s o =>(f s.1 o,s.2)) (trF q)
  | .load a q =>.load (fun s =>(a s.1,s.2)) (trF q)
  | .branch f q₁ q₂ =>.branch (fun s =>f s.1) (trF q₁) (trF q₂)
  | .goto f =>.goto (fun s =>injL (f s.1))
  | .halt =>.goto (fun _ =>injR FL.l3)
variable (M)
def firstProg (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool) :
    FstΛ M→ TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | injL l =>trF (M.m l)
  | injR FL.l1 =>
    .pop (injR FX.I) (fun s o =>(s.1,o))
      (.branch (fun s =>s.2.isSome)
        (.branch (fun s =>isFst s.2)
          (.push (injR FX.T) (fun s =>bit s.2) (.goto fun _ =>injR FL.l1))
          (.push (injR FX.W) (fun s =>bit s.2) (.goto fun _ =>injR FL.l1)))
        (.goto fun _ =>injR FL.l2))
  | injR FL.l2 =>
    .pop (injR FX.T) (fun s o =>(s.1,o.map injL))
      (.branch (fun s =>s.2.isSome)
        (.push (injL M.k₀) (fun s =>e₀ (bit s.2)) (.goto fun _ =>injR FL.l2))
        (.goto fun _ =>injL M.main))
  | injR FL.l3 =>
    .pop (injR FX.W) (fun s o =>(s.1,o.map injL))
      (.branch (fun s =>s.2.isSome)
        (.push (injR FX.O) (fun s =>injR (bit s.2)) (.goto fun _ =>injR FL.l3))
        (.goto fun _ =>injR FL.l4))
  | injR FL.l4 =>
    .pop (injL M.k₁) (fun s o =>(s.1,o.map fun y =>injL (e₁ y)))
      (.branch (fun s =>s.2.isSome)
        (.push (injR FX.T) (fun s =>bit s.2) (.goto fun _ =>injR FL.l4))
        (.goto fun _ =>injR FL.l5))
  | injR FL.l5 =>
    .pop (injR FX.T) (fun s o =>(s.1,o.map injL))
      (.branch (fun s =>s.2.isSome)
        (.push (injR FX.O) (fun s =>injL (bit s.2)) (.goto fun _ =>injR FL.l5))
        .halt)
def firstM (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool):FinTM2 :=
  haveI:= M.kFin
  haveI:= M.ΛFin
  haveI:= M.σFin
  { K:= M.K ⊕ FX
    k₀:= injR FX.I
    k₁:= injR FX.O
    Γ:= FstΓ M
    Λ:= FstΛ M
    main:= injR FL.l1
    σ:= Fstσ M
    initialState:= (M.initialState,none)
    Γk₀Fin:= inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:= firstProg M e₀ e₁ }
variable {M}
def fstk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
    (o:List (Bool ⊕ Bool)):∀ k,List (FstΓ M k)
  | injL k =>S k
  | injR FX.I =>i
  | injR FX.W =>w
  | injR FX.T =>t
  | injR FX.O =>o
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
  (o:List (Bool ⊕ Bool))
theorem fstk_set_M (k:M.K) (x:List (M.Γ k)) :
    upd (fstk S i w t o) (injL k) x=fstk (upd S k x) i w t o:= by
  funext j
  rcases j with j | j
  · by_cases h:j=k
    · subst h
      rw [upd_self]
      show x=upd S j x j
      rw [upd_self]
    · rw [upd_ne (by simpa using h)]
      show S j=upd S k x j
      rw [upd_ne h]
  · rw [upd_ne (by simp)]; cases j <;> rfl
theorem fstk_set_I (i':List (Bool ⊕ Bool)) :
    upd (fstk S i w t o) (injR FX.I) i'=fstk S i' w t o:= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
theorem fstk_set_W (w':BitTape) :
    upd (fstk S i w t o) (injR FX.W) w'=fstk S i w' t o:= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
theorem fstk_set_T (t':BitTape) :
    upd (fstk S i w t o) (injR FX.T) t'=fstk S i w t' o:= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
  · rw [upd_ne (by simp)]; rfl
theorem fstk_set_O (o':List (Bool ⊕ Bool)) :
    upd (fstk S i w t o) (injR FX.O) o'=fstk S i w t o':= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
end fstk
abbrev FCfg1 (M:FinTM2):Type:= TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)
def embF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
    (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):FCfg1 M :=
  ⟨some (c.l.elim (injR FL.l3) injL),(c.var,b),fstk c.stk i w t o⟩
theorem simF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
    (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    stepAuxT (trF q) ((v,b):Fstσ M) (fstk S i w t o) =
      embF b i w t o (stepAuxT q v S):= by
  induction q generalizing v S with
  | push k f q ih =>
    have:= ih v (upd S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih =>exact ih _ _
  | pop k f q ih =>
    have:= ih (f v (S k).head?) (upd S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih =>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF,stepAuxT]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f =>rfl
  | halt =>rfl
theorem stepF (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool) (b:Option (Bool ⊕ Bool))
    (i:List (Bool ⊕ Bool)) (w t:BitTape) (o:List (Bool ⊕ Bool))
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:tmStep M.m c=some c') :
    tmStep (firstProg M e₀ e₁) (embF b i w t o c)=some (embF b i w t o c'):= by
  obtain ⟨l,v,S⟩:= c
  cases l with
  | none =>simp [tmStep] at h
  | some l =>
    simp only [tmStep,Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
theorem iter_trans {σ:Type} (f:σ→ Option σ) {a b:ℕ} {x y z:σ}
    (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z) :
    (flip bind f)^[b+a] (some x)=some z:= by
  rw [iter_add,h₁,h₂]
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool)
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
  (o:List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k:M.K):fstk S i w t o (injL k)=S k:= rfl
@[simp] theorem fstk_I:fstk S i w t o (injR FX.I)=i:= rfl
@[simp] theorem fstk_W:fstk S i w t o (injR FX.W)=w:= rfl
@[simp] theorem fstk_T:fstk S i w t o (injR FX.T)=t:= rfl
@[simp] theorem fstk_O:fstk S i w t o (injR FX.O)=o:= rfl
end fstk
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:BitTape) (o:List (Bool ⊕ Bool))
theorem f1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l1),(v,b),fstk S (injL a :: i) w t o⟩:FCfg1 M) =
      some ⟨some (injR FL.l1),(v,some (injL a)),fstk S i w (a :: t) o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_I,fstk_set_T,isFst,bit]
theorem f1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l1),(v,b),fstk S (injR a :: i) w t o⟩:FCfg1 M) =
      some ⟨some (injR FL.l1),(v,some (injR a)),fstk S i (a :: w) t o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_I,fstk_set_W,isFst,bit]
theorem f1_nil (b:Option (Bool ⊕ Bool)) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l1),(v,b),fstk S [] w t o⟩:FCfg1 M) =
      some ⟨some (injR FL.l2),(v,none),fstk S [] w t o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_I]
theorem loop1:∀ (i:List (Bool ⊕ Bool)) (w t:BitTape) (b:Option (Bool ⊕ Bool)),
    (flip bind (tmStep (firstProg M e₀ e₁)))^[i.length+1]
        (some (⟨some (injR FL.l1),(v,b),fstk S i w t o⟩:FCfg1 M)) =
      some ⟨some (injR FL.l2),(v,none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩:= by
  intro i
  induction i with
  | nil =>intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [len_cons,iter_succ]
    cases x with
    | inl a =>
      have e:flip bind (tmStep (firstProg M e₀ e₁))
          (some (⟨some (injR FL.l1),(v,b),fstk S (injL a :: i) w t o⟩:FCfg1 M)) =
          some ⟨some (injR FL.l1),(v,some (injL a)),fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e,ih]; simp [List.filterMap_cons]
    | inr a =>
      have e:flip bind (tmStep (firstProg M e₀ e₁))
          (some (⟨some (injR FL.l1),(v,b),fstk S (injR a :: i) w t o⟩:FCfg1 M)) =
          some ⟨some (injR FL.l1),(v,some (injR a)),fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e,ih]; simp [List.filterMap_cons]
theorem f2_cons (b:Option (Bool ⊕ Bool)) (a:Bool) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M) =
      some ⟨some (injR FL.l2),(v,some (injL a)),
        fstk (upd S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_T,fstk_set_M,bit]
theorem f2_nil (b:Option (Bool ⊕ Bool)) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l2),(v,b),fstk S [] w [] o⟩:FCfg1 M) =
      some ⟨some (injL M.main),(v,none),fstk S [] w [] o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_T]
theorem loop2:∀ (t:BitTape) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    (flip bind (tmStep (firstProg M e₀ e₁)))^[t.length+1]
        (some (⟨some (injR FL.l2),(v,b),fstk S [] w t o⟩:FCfg1 M)) =
      some ⟨some (injL M.main),(v,none),
        fstk (upd S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩:= by
  intro t
  induction t with
  | nil =>
    intro S b
    have:upd S M.k₀ (([]:BitTape).reverse.map e₀ ++ S M.k₀)=S:= by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (firstProg M e₀ e₁))
        (some (⟨some (injR FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M)) =
        some ⟨some (injR FL.l2),(v,some (injL a)),
          fstk (upd S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:= f2_cons e₀ e₁ v S w o b a t
    rw [e,ih]; simp
theorem f3_cons (b:Option (Bool ⊕ Bool)) (a:Bool) (w:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M) =
      some ⟨some (injR FL.l3),(v,some (injL a)),fstk S [] w [] (injR a :: o)⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_W,fstk_set_O,bit]
theorem f3_nil (b:Option (Bool ⊕ Bool)) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l3),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
      some ⟨some (injR FL.l4),(v,none),fstk S [] [] [] o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_W]
theorem loop3:∀ (w:BitTape) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (tmStep (firstProg M e₀ e₁)))^[w.length+1]
        (some (⟨some (injR FL.l3),(v,b),fstk S [] w [] o⟩:FCfg1 M)) =
      some ⟨some (injR FL.l4),(v,none),fstk S [] [] [] (w.reverse.map injR ++ o)⟩:= by
  intro w
  induction w with
  | nil =>intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (firstProg M e₀ e₁))
        (some (⟨some (injR FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M)) =
        some ⟨some (injR FL.l3),(v,some (injL a)),fstk S [] w [] (injR a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e,ih]; simp
theorem f4_cons (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l4),(v,b),fstk (upd S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (injR FL.l4),(v,some (injL (e₁ y))),
        fstk (upd S M.k₁ m) [] [] (e₁ y :: t) o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_T,fstk_set_M,bit]
theorem f4_nil (b:Option (Bool ⊕ Bool)) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l4),(v,b),fstk (upd S M.k₁ []) [] [] t o⟩:FCfg1 M) =
      some ⟨some (injR FL.l5),(v,none),fstk (upd S M.k₁ []) [] [] t o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_M]
theorem loop4:∀ (m:List (M.Γ M.k₁)) (t:BitTape) (b:Option (Bool ⊕ Bool)),
    (flip bind (tmStep (firstProg M e₀ e₁)))^[m.length+1]
        (some (⟨some (injR FL.l4),(v,b),fstk (upd S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (injR FL.l5),(v,none),
        fstk (upd S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩:= by
  intro m
  induction m with
  | nil =>intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (firstProg M e₀ e₁))
        (some (⟨some (injR FL.l4),(v,b),fstk (upd S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (injR FL.l4),(v,some (injL (e₁ y))),
          fstk (upd S M.k₁ m) [] [] (e₁ y :: t) o⟩:= f4_cons e₀ e₁ v S o b y m t
    rw [e,ih]; simp
theorem f5_cons (b:Option (Bool ⊕ Bool)) (a:Bool) (t:BitTape) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M) =
      some ⟨some (injR FL.l5),(v,some (injL a)),fstk S [] [] t (injL a :: o)⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_T,fstk_set_O,bit]
theorem f5_nil (b:Option (Bool ⊕ Bool)) :
    tmStep (firstProg M e₀ e₁)
        (⟨some (injR FL.l5),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
      some ⟨none,(v,none),fstk S [] [] [] o⟩:= by
  simp [tmStep,firstProg,stepAuxT,fstk_set_T]
theorem loop5:∀ (t:BitTape) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (tmStep (firstProg M e₀ e₁)))^[t.length+1]
        (some (⟨some (injR FL.l5),(v,b),fstk S [] [] t o⟩:FCfg1 M)) =
      some ⟨none,(v,none),fstk S [] [] [] (t.reverse.map injL ++ o)⟩:= by
  intro t
  induction t with
  | nil =>intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (firstProg M e₀ e₁))
        (some (⟨some (injR FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M)) =
        some ⟨some (injR FL.l5),(v,some (injL a)),fstk S [] [] t (injL a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e,ih]; simp
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (e₁:M.Γ M.k₁→ Bool)
theorem fstk_nil:(fstk (fun _ =>[]) [] [] [] []:∀ k,List (FstΓ M k))=fun _ =>[]:= by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl
theorem fstk_nil_I (i:List (Bool ⊕ Bool)) :
    (fstk (fun _ =>[]) i [] [] []:∀ k,List (FstΓ M k)) =
      upd (fun _ =>[]:∀ k,List (FstΓ M k)) (injR FX.I) i :=
  (fstk_set_I (fun _ =>[]) [] [] [] [] i).symm.trans (by rw [fstk_nil])
theorem fstk_nil_O (o:List (Bool ⊕ Bool)) :
    (fstk (fun _ =>[]) [] [] [] o:∀ k,List (FstΓ M k)) =
      upd (fun _ =>[]:∀ k,List (FstΓ M k)) (injR FX.O) o :=
  (fstk_set_O (fun _ =>[]) [] [] [] [] o).symm.trans (by rw [fstk_nil])
theorem embF_init (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
    (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (injL M.main),(M.initialState,b),
        fstk (upd (fun _ =>[]) M.k₀ l) i w t o⟩:FCfg1 M):= by
  rw [initList_eq]; rfl
theorem embF_halt (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:BitTape)
    (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (injR FL.l3),(M.initialState,b),
        fstk (upd (fun _ =>[]) M.k₁ m) i w t o⟩:FCfg1 M):= by
  rw [haltList_eq]; rfl
theorem filterMap_const_none {γ δ:Type} (l:List γ) :
    l.filterMap (fun _ =>(none:Option δ))=[]:= by
  induction l with
  | nil =>rfl
  | cons a l ih =>simp
theorem encodePair_left (x w:BitTape) :
    (encodePair (x,w)).filterMap Sum.getLeft?=x:= by
  have h1:(Sum.getLeft? ∘ (injL:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=some:= rfl
  have h2:(Sum.getLeft? ∘ (injR:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=fun _ =>none:= rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,filterMap_const_none,List.append_nil]
theorem encodePair_right (x w:BitTape) :
    (encodePair (x,w)).filterMap Sum.getRight?=w:= by
  have h1:(Sum.getRight? ∘ (injL:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=fun _ =>none:= rfl
  have h2:(Sum.getRight? ∘ (injR:Bool→ Bool ⊕ Bool):Bool→ Option Bool)=some:= rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,filterMap_const_none,List.nil_append]
theorem encodePair_length (x w:BitTape) :
    (encodePair (x,w)).length=x.length+w.length:= by
  simp [encodePair]
theorem first_run (x w0:BitTape) (m:List (M.Γ M.k₁)) (s:ℕ)
    (h:(flip bind (tmStep M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)) :
    ∃ n,n≤ s+2 * x.length+2 * w0.length+2 * m.length+5 ∧
      (flip bind (tmStep (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):= by
  have q1:(flip bind (tmStep (firstProg M e₀ e₁)))^[(encodePair (x,w0)).length+1]
      (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
      some (⟨some (injR FL.l2),(M.initialState,none),
        fstk (fun _ =>[]) [] w0.reverse x.reverse []⟩:FCfg1 M):= by
    have:= loop1 e₀ e₁ M.initialState (fun _ =>[]) [] (encodePair (x,w0)) [] [] none
    rw [encodePair_left,encodePair_right,List.append_nil,List.append_nil,fstk_nil_I] at this
    exact (congrArg (fun c =>(flip bind (tmStep (firstProg M e₀ e₁)))^[
      (encodePair (x,w0)).length+1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x,w0)))).trans this
  have q2:(flip bind (tmStep (firstProg M e₀ e₁)))^[x.reverse.length+1]
      (some (⟨some (injR FL.l2),(M.initialState,none),
        fstk (fun _ =>[]) [] w0.reverse x.reverse []⟩:FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))):= by
    have:= loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ =>[]) none
    rw [embF_init]
    simpa using this
  have q3:= simulate (tmStep M.m) (tmStep (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4:(flip bind (tmStep (firstProg M e₀ e₁)))^[w0.reverse.length+1]
      (some (⟨some (injR FL.l3),(M.initialState,none),
        fstk (upd (fun _ =>[]) M.k₁ m) [] w0.reverse [] []⟩:FCfg1 M)) =
      some (⟨some (injR FL.l4),(M.initialState,none),
        fstk (upd (fun _ =>[]) M.k₁ m) [] [] [] (w0.map injR)⟩:FCfg1 M):= by
    have:= loop3 e₀ e₁ M.initialState (upd (fun _ =>[]) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5:(flip bind (tmStep (firstProg M e₀ e₁)))^[m.length+1]
      (some (⟨some (injR FL.l4),(M.initialState,none),
        fstk (upd (fun _ =>[]) M.k₁ m) [] [] [] (w0.map injR)⟩:FCfg1 M)) =
      some (⟨some (injR FL.l5),(M.initialState,none),
        fstk (fun _ =>[]) [] [] (m.reverse.map e₁) (w0.map injR)⟩:FCfg1 M):= by
    have:= loop4 e₀ e₁ M.initialState (fun _ =>[]) (w0.map injR) m [] none
    simpa using this
  have q6:(flip bind (tmStep (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length+1]
      (some (⟨some (injR FL.l5),(M.initialState,none),
        fstk (fun _ =>[]) [] [] (m.reverse.map e₁) (w0.map injR)⟩:FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):= by
    have:= loop5 e₀ e₁ M.initialState (fun _ =>[]) (m.reverse.map e₁) (w0.map injR) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_,?_,iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length,List.length_reverse,len_map]
  omega
theorem first_polyTime (f:TapeMap)
    (c:TM2ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p:BitTape × BitTape =>(f p.1,p.2))):= by
  let e₀:Bool→ c.tm.Γ c.tm.k₀:= c.inputAlphabet.invFun
  let e₁:c.tm.Γ c.tm.k₁→ Bool:= c.outputAlphabet
  let T:Polynomial ℕ :=
    c.time+Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X+Polynomial.C 5
  have key:∀ p:BitTape × BitTape,∃ n,n≤ T.eval (encodePair p).length ∧
      (flip bind (tmStep (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1,p.2))):= by
    rintro ⟨x,w⟩
    have hs:∃ s,s≤ Polynomial.eval x.length c.time ∧
        (flip bind (tmStep c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
    obtain ⟨s,b1,h⟩:= hs
    obtain ⟨n,hn,hrun⟩:= first_run e₀ e₁ x w _ s h
    have hm:(List.map c.outputAlphabet.invFun (f x)).map e₁=f x:= by
      rw [mapMap]
      conv_rhs =>rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ =>c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n,hn.trans ?_,hrun⟩
    have h':= h
    rw [haltList_eq,initList_eq] at h'
    have hlen:= run_length c.tm c.tm.k₁ s _ _ h'
    simp only [upd_self,len_map] at hlen
    have hin:((upd (fun _ =>[]:∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length≤ x.length:= by
      by_cases hk:c.tm.k₁=c.tm.k₀
      · rw [hk,upd_self,len_map]
      · rw [upd_ne hk]; simp
    have b2:Polynomial.eval x.length c.time≤ Polynomial.eval (x.length+w.length) c.time :=
      eval_mono _ (by omega)
    have hmul:maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length+w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T,evalAddP,evalMulP,evalCP,
      evalXP,encodePair_length,len_map]
    omega
  exact ⟨{
    tm:= firstM c.tm e₀ e₁
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= T
    outputsFun:= fun p =>
      { steps:= Classical.choose (key p)
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          exact (congrArg (fun l =>(flip bind (tmStep (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l =>some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1,p.2))).symm))
        steps_le_m:= (Classical.choose_spec (key p)).1 } }⟩
end Lib.Machines
end
section
namespace Lib.Machines.Iter
open Turing
inductive IX
  | I | C | T | O
  deriving DecidableEq
instance:Fintype IX :=
  Fintype.ofList [IX.I,IX.C,IX.T,IX.O] (fun x => by cases x <;> simp)
inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq
instance:Fintype IL :=
  Fintype.ofList [IL.l1,IL.l2,IL.l3,IL.l4,IL.l5,IL.l6] (fun x => by cases x <;> simp)
variable (M:FinTM2)
abbrev ItΓ:M.K ⊕ IX→ Type
  | injL k =>M.Γ k
  | injR IX.I =>Bool ⊕ Bool
  | injR IX.C =>Bool
  | injR IX.T =>Bool
  | injR IX.O =>Bool
abbrev ItΛ:Type:= M.Λ ⊕ IL
abbrev Itσ:Type:= M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ→ TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q =>.push (injL k) (fun s =>f s.1) (trI q)
  | .peek k f q =>.peek (injL k) (fun s o =>(f s.1 o,s.2)) (trI q)
  | .pop k f q =>.pop (injL k) (fun s o =>(f s.1 o,s.2)) (trI q)
  | .load a q =>.load (fun s =>(a s.1,s.2)) (trI q)
  | .branch f q₁ q₂ =>.branch (fun s =>f s.1) (trI q₁) (trI q₂)
  | .goto f =>.goto (fun s =>injL (f s.1))
  | .halt =>.goto (fun _ =>injR IL.l4)
variable (M)
def iterProg (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool) :
    ItΛ M→ TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | injL l =>trI (M.m l)
  | injR IL.l1 =>
    .pop (injR IX.I) (fun s o =>(s.1,o))
      (.branch (fun s =>s.2.isSome)
        (.branch (fun s =>isFst s.2)
          (.push (injR IX.T) (fun s =>bit s.2) (.goto fun _ =>injR IL.l1))
          (.push (injR IX.C) (fun s =>bit s.2) (.goto fun _ =>injR IL.l1)))
        (.goto fun _ =>injR IL.l2))
  | injR IL.l2 =>
    .pop (injR IX.T) (fun s o =>(s.1,o.map injL))
      (.branch (fun s =>s.2.isSome)
        (.push (injL M.k₀) (fun s =>e₀ (bit s.2)) (.goto fun _ =>injR IL.l2))
        (.goto fun _ =>injR IL.l3))
  | injR IL.l3 =>
    .pop (injR IX.C) (fun s o =>(s.1,o.map injL))
      (.branch (fun s =>s.2.isSome)
        (.goto fun _ =>injL M.main)
        (.goto fun _ =>injR IL.l5))
  | injR IL.l4 =>
    .pop (injL M.k₁) (fun s o =>(s.1,o.map fun y =>injL (e₁ y)))
      (.branch (fun s =>s.2.isSome)
        (.push (injR IX.T) (fun s =>bit s.2) (.goto fun _ =>injR IL.l4))
        (.goto fun _ =>injR IL.l2))
  | injR IL.l5 =>
    .pop (injL M.k₀) (fun s o =>(s.1,o.map fun y =>injL (d₀ y)))
      (.branch (fun s =>s.2.isSome)
        (.push (injR IX.T) (fun s =>bit s.2) (.goto fun _ =>injR IL.l5))
        (.goto fun _ =>injR IL.l6))
  | injR IL.l6 =>
    .pop (injR IX.T) (fun s o =>(s.1,o.map injL))
      (.branch (fun s =>s.2.isSome)
        (.push (injR IX.O) (fun s =>bit s.2) (.goto fun _ =>injR IL.l6))
        .halt)
def iterM (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool):FinTM2 :=
  haveI:= M.kFin
  haveI:= M.ΛFin
  haveI:= M.σFin
  { K:= M.K ⊕ IX
    k₀:= injR IX.I
    k₁:= injR IX.O
    Γ:= ItΓ M
    Λ:= ItΛ M
    main:= injR IL.l1
    σ:= Itσ M
    initialState:= (M.initialState,none)
    Γk₀Fin:= inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:= iterProg M e₀ d₀ e₁ }
variable {M}
def istk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape) :
    ∀ k,List (ItΓ M k)
  | injL k =>S k
  | injR IX.I =>i
  | injR IX.C =>cn
  | injR IX.T =>t
  | injR IX.O =>o
section istk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape)
@[simp] theorem istk_M (k:M.K):istk S i cn t o (injL k)=S k:= rfl
@[simp] theorem istk_I:istk S i cn t o (injR IX.I)=i:= rfl
@[simp] theorem istk_C:istk S i cn t o (injR IX.C)=cn:= rfl
@[simp] theorem istk_T:istk S i cn t o (injR IX.T)=t:= rfl
@[simp] theorem istk_O:istk S i cn t o (injR IX.O)=o:= rfl
theorem istk_set_M (k:M.K) (x:List (M.Γ k)) :
    upd (istk S i cn t o) (injL k) x=istk (upd S k x) i cn t o:= by
  funext j
  rcases j with j | j
  · by_cases h:j=k
    · subst h
      rw [upd_self]
      show x=upd S j x j
      rw [upd_self]
    · rw [upd_ne (by simpa using h)]
      show S j=upd S k x j
      rw [upd_ne h]
  · rw [upd_ne (by simp)]; cases j <;> rfl
theorem istk_set_I (i':List (Bool ⊕ Bool)) :
    upd (istk S i cn t o) (injR IX.I) i'=istk S i' cn t o:= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
theorem istk_set_C (cn':BitTape) :
    upd (istk S i cn t o) (injR IX.C) cn'=istk S i cn' t o:= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
theorem istk_set_T (t':BitTape) :
    upd (istk S i cn t o) (injR IX.T) t'=istk S i cn t' o:= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
  · rw [upd_ne (by simp)]; rfl
theorem istk_set_O (o':BitTape) :
    upd (istk S i cn t o) (injR IX.O) o'=istk S i cn t o':= by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_ne (by simp)]; rfl
  · rw [upd_self]; rfl
end istk
abbrev ICfg (M:FinTM2):Type:= TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def embI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape)
    (c:TM2.Cfg M.Γ M.Λ M.σ):ICfg M :=
  ⟨some (c.l.elim (injR IL.l4) injL),(c.var,b),istk c.stk i cn t o⟩
theorem simI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape)
    (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    stepAuxT (trI q) ((v,b):Itσ M) (istk S i cn t o) =
      embI b i cn t o (stepAuxT q v S):= by
  induction q generalizing v S with
  | push k f q ih =>
    have:= ih v (upd S k (f v :: S k))
    rw [← istk_set_M] at this
    exact this
  | peek k f q ih =>exact ih _ _
  | pop k f q ih =>
    have:= ih (f v (S k).head?) (upd S k (S k).tail)
    rw [← istk_set_M] at this
    exact this
  | load a q ih =>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI,stepAuxT]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f =>rfl
  | halt =>rfl
theorem stepI (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool)
    (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape)
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:tmStep M.m c=some c') :
    tmStep (iterProg M e₀ d₀ e₁) (embI b i cn t o c)=some (embI b i cn t o c'):= by
  obtain ⟨l,v,S⟩:= c
  cases l with
  | none =>simp [tmStep] at h
  | some l =>
    simp only [tmStep,Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)
theorem embI_init (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape)
    (l:List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (injL M.main),(M.initialState,b),
        istk (upd (fun _ =>[]) M.k₀ l) i cn t o⟩:ICfg M):= by
  rw [initList_eq]; rfl
theorem embI_halt (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape)
    (m:List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (injR IL.l4),(M.initialState,b),
        istk (upd (fun _ =>[]) M.k₁ m) i cn t o⟩:ICfg M):= by
  rw [haltList_eq]; rfl
theorem istk_nil:(istk (fun _ =>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _ =>[]:= by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl
theorem istk_nil_I (i:List (Bool ⊕ Bool)) :
    (istk (fun _ =>[]) i [] [] []:∀ k,List (ItΓ M k)) =
      upd (fun _ =>[]:∀ k,List (ItΓ M k)) (injR IX.I) i :=
  (istk_set_I (fun _ =>[]) [] [] [] [] i).symm.trans (by rw [istk_nil])
theorem istk_nil_O (o:BitTape) :
    (istk (fun _ =>[]) [] [] [] o:∀ k,List (ItΓ M k)) =
      upd (fun _ =>[]:∀ k,List (ItΓ M k)) (injR IX.O) o :=
  (istk_set_O (fun _ =>[]) [] [] [] [] o).symm.trans (by rw [istk_nil])
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
theorem i1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l1),(v,b),istk S (injL a :: i) cn t o⟩:ICfg M) =
      some ⟨some (injR IL.l1),(v,some (injL a)),istk S i cn (a :: t) o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_I,istk_set_T,isFst,bit]
theorem i1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l1),(v,b),istk S (injR a :: i) cn t o⟩:ICfg M) =
      some ⟨some (injR IL.l1),(v,some (injR a)),istk S i (a :: cn) t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_I,istk_set_C,isFst,bit]
theorem i1_nil (b:Option (Bool ⊕ Bool)) (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l1),(v,b),istk S [] cn t o⟩:ICfg M) =
      some ⟨some (injR IL.l2),(v,none),istk S [] cn t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_I]
theorem iloop1 (o:BitTape) :
    ∀ (i:List (Bool ⊕ Bool)) (cn t:BitTape) (b:Option (Bool ⊕ Bool)),
    ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[i.length+1]
        (some (⟨some (injR IL.l1),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨some (injR IL.l2),(v,none),
        istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩:= by
  intro i
  induction i with
  | nil =>intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [len_cons,iter_succ]
    cases x with
    | inl a =>
      have e:(flip bind (tmStep (iterProg M e₀ d₀ e₁)))
          (some (⟨some (injR IL.l1),(v,b),istk S (injL a :: i) cn t o⟩:ICfg M)) =
          some ⟨some (injR IL.l1),(v,some (injL a)),istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih]; simp [List.filterMap_cons]
    | inr a =>
      have e:(flip bind (tmStep (iterProg M e₀ d₀ e₁)))
          (some (⟨some (injR IL.l1),(v,b),istk S (injR a :: i) cn t o⟩:ICfg M)) =
          some ⟨some (injR IL.l1),(v,some (injR a)),istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih]; simp [List.filterMap_cons]
theorem i2_cons (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
      some ⟨some (injR IL.l2),(v,some (injL a)),
        istk (upd S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_T,istk_set_M,bit]
theorem i2_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l2),(v,b),istk S i cn [] o⟩:ICfg M) =
      some ⟨some (injR IL.l3),(v,none),istk S i cn [] o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_T]
theorem iloop2 (i:List (Bool ⊕ Bool)) (cn o:BitTape) :
    ∀ (t:BitTape) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (injR IL.l2),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨some (injR IL.l3),(v,none),
        istk (upd S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) i cn [] o⟩:= by
  intro t
  induction t with
  | nil =>
    intro S b
    have:upd S M.k₀ (([]:BitTape).reverse.map e₀ ++ S M.k₀)=S:= by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [len_cons,iter_succ]
    have e:(flip bind (tmStep (iterProg M e₀ d₀ e₁)))
        (some (⟨some (injR IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
        some ⟨some (injR IL.l2),(v,some (injL a)),
          istk (upd S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      i2_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih]; simp
theorem i3_cons (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l3),(v,b),istk S i (a :: cn) t o⟩:ICfg M) =
      some ⟨some (injL M.main),(v,some (injL a)),istk S i cn t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_C]
theorem i3_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l3),(v,b),istk S i [] t o⟩:ICfg M) =
      some ⟨some (injR IL.l5),(v,none),istk S i [] t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_C]
theorem i4_cons (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
    (i:List (Bool ⊕ Bool)) (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l4),(v,b),istk (upd S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (injR IL.l4),(v,some (injL (e₁ y))),
        istk (upd S M.k₁ m) i cn (e₁ y :: t) o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_T,istk_set_M,bit]
theorem i4_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l4),(v,b),istk (upd S M.k₁ []) i cn t o⟩:ICfg M) =
      some ⟨some (injR IL.l2),(v,none),istk (upd S M.k₁ []) i cn t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_M]
theorem iloop4 (i:List (Bool ⊕ Bool)) (cn o:BitTape) :
    ∀ (m:List (M.Γ M.k₁)) (t:BitTape) (b:Option (Bool ⊕ Bool)),
    ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (injR IL.l4),(v,b),istk (upd S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (injR IL.l2),(v,none),
        istk (upd S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩:= by
  intro m
  induction m with
  | nil =>intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [len_cons,iter_succ]
    have e:(flip bind (tmStep (iterProg M e₀ d₀ e₁)))
        (some (⟨some (injR IL.l4),(v,b),
          istk (upd S M.k₁ (y :: m)) i cn t o⟩:ICfg M)) =
        some ⟨some (injR IL.l4),(v,some (injL (e₁ y))),
          istk (upd S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      i4_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih]; simp
theorem i5_cons (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
    (i:List (Bool ⊕ Bool)) (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l5),(v,b),istk (upd S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (injR IL.l5),(v,some (injL (d₀ y))),
        istk (upd S M.k₀ m) i cn (d₀ y :: t) o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_T,istk_set_M,bit]
theorem i5_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l5),(v,b),istk (upd S M.k₀ []) i cn t o⟩:ICfg M) =
      some ⟨some (injR IL.l6),(v,none),istk (upd S M.k₀ []) i cn t o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_M]
theorem iloop5 (i:List (Bool ⊕ Bool)) (cn o:BitTape) :
    ∀ (m:List (M.Γ M.k₀)) (t:BitTape) (b:Option (Bool ⊕ Bool)),
    ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (injR IL.l5),(v,b),istk (upd S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (injR IL.l6),(v,none),
        istk (upd S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩:= by
  intro m
  induction m with
  | nil =>intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [len_cons,iter_succ]
    have e:(flip bind (tmStep (iterProg M e₀ d₀ e₁)))
        (some (⟨some (injR IL.l5),(v,b),
          istk (upd S M.k₀ (y :: m)) i cn t o⟩:ICfg M)) =
        some ⟨some (injR IL.l5),(v,some (injL (d₀ y))),
          istk (upd S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      i5_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih]; simp
theorem i6_cons (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
      some ⟨some (injR IL.l6),(v,some (injL a)),istk S i cn t (a :: o)⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_T,istk_set_O,bit]
theorem i6_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:BitTape) :
    tmStep (iterProg M e₀ d₀ e₁)
        (⟨some (injR IL.l6),(v,b),istk S i cn [] o⟩:ICfg M) =
      some ⟨none,(v,none),istk S i cn [] o⟩:= by
  simp [tmStep,iterProg,stepAuxT,istk_set_T]
theorem iloop6 (i:List (Bool ⊕ Bool)) (cn:BitTape) :
    ∀ (t o:BitTape) (b:Option (Bool ⊕ Bool)),
    ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (injR IL.l6),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨none,(v,none),istk S i cn [] (t.reverse ++ o)⟩:= by
  intro t
  induction t with
  | nil =>intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [len_cons,iter_succ]
    have e:(flip bind (tmStep (iterProg M e₀ d₀ e₁)))
        (some (⟨some (injR IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
        some ⟨some (injR IL.l6),(v,some (injL a)),istk S i cn t (a :: o)⟩ :=
      i6_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih]; simp
theorem update_nil_nil (k:M.K) :
    upd (fun _ =>[]:∀ k,List (M.Γ k)) k []=fun _ =>[] :=
  Function.update_eq_self k (fun _ =>[]:∀ k,List (M.Γ k))
theorem main_loop (g:TapeMap) (k:ℕ) (p:Polynomial ℕ)
    (hk:∀ y:BitTape,(g y).length≤ y.length+k)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:BitTape,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤ p.eval z.length ∧
      (flip bind (tmStep M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z) :
    ∀ (cn z:BitTape) (L:ℕ) (b:Option (Bool ⊕ Bool)),z.length+k * cn.length≤ L →
      ∃ n,n≤ cn.length * (p.eval L+2 * L+3)+2 * L+3 ∧
        ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (injR IL.l3),(M.initialState,b),
              istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:ICfg M)) =
          some ⟨none,(M.initialState,none),
            istk (fun _ =>[]) [] [] [] (g^[cn.length] z)⟩:= by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz:((z.map e₀).reverse.map d₀).reverse=z:= by
      rw [List.map_reverse,List.reverse_reverse,mapMap]
      conv_rhs =>rw [← List.map_id z]
      exact List.map_congr_left fun a _ =>hd a
    have q1:((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (injR IL.l3),(M.initialState,b),
          istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:ICfg M)) =
        some ⟨some (injR IL.l5),(M.initialState,none),
          istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2:= iloop5 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil,List.append_nil] at q2
    have q3:= iloop6 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil,hz] at q3
    refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse,len_map,len_nil] at hL ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s,m,hs,hm,hmg⟩:= hrun z
    rw [len_cons] at hL
    have hgz:(g z).length≤ z.length+k:= hk z
    have hkk:k * (cn.length+1)=k * cn.length+k:= Nat.mul_succ _ _
    have hml:m.length=(g z).length:= by rw [← hmg,len_map]
    have q1:((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (injR IL.l3),(M.initialState,b),
          istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩:ICfg M)) =
        some (embI (some (injL a)) [] cn [] [] (initList M (z.map e₀))):= by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2:= simulate (tmStep M.m) (tmStep (iterProg M e₀ d₀ e₁))
      (embI (some (injL a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (injL a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3:= iloop4 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] cn [] m [] (some (injL a))
    rw [update_nil_nil,List.append_nil,List.map_reverse,hmg] at q3
    have q4:= iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ =>[]) none
    rw [List.append_nil,List.reverse_reverse] at q4
    obtain ⟨n,hn,q5⟩:= ih (g z) L none (by omega)
    have e:g^[(a :: cn).length] z=g^[cn.length] (g z):= iter_succ g _ z
    rw [e]
    refine ⟨_,?_,iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp:p.eval z.length≤ p.eval L:= eval_mono p (by omega)
    rw [List.length_reverse,len_cons,Nat.succ_mul]
    generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢
    omega
theorem iter_run (g:TapeMap) (k:ℕ) (p:Polynomial ℕ)
    (hk:∀ y:BitTape,(g y).length≤ y.length+k)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:BitTape,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤ p.eval z.length ∧
      (flip bind (tmStep M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z)
    (y u:BitTape) (L:ℕ) (hL:y.length+k * u.length≤ L) :
    ∃ n,n≤ u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5 ∧
      ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)):= by
  have q1:((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
      some (⟨some (injR IL.l2),(M.initialState,none),
        istk (fun _ =>[]) [] u.reverse y.reverse []⟩:ICfg M):= by
    have:= iloop1 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] (encodePair (y,u)) [] [] none
    rw [encodePair_left,encodePair_right,List.append_nil,List.append_nil,istk_nil_I] at this
    exact (congrArg (fun c =>((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
  have q2:= iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ =>[]) none
  rw [List.append_nil,List.reverse_reverse] at q2
  obtain ⟨n,hn,q3⟩:= main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3':((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (injR IL.l3),(M.initialState,none),
        istk (upd (fun _ =>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length,List.length_reverse]
  omega
theorem iter_polyTime (g:TapeMap)
    (c:Turing.TM2ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) g)
    (k:ℕ) (hk:∀ y:BitTape,(g y).length≤ y.length+k) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>g^[p.2.length] p.1)):= by
  let e₀:Bool→ c.tm.Γ c.tm.k₀:= c.inputAlphabet.invFun
  let d₀:c.tm.Γ c.tm.k₀→ Bool:= c.inputAlphabet
  let e₁:c.tm.Γ c.tm.k₁→ Bool:= c.outputAlphabet
  let W:Polynomial ℕ:= Polynomial.X+Polynomial.C k * Polynomial.X
  let T:Polynomial ℕ :=
    Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3) +
      Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
  have hd:∀ a,d₀ (e₀ a)=a:= fun a =>c.inputAlphabet.right_inv a
  have hrun:∀ z:BitTape,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
      s≤ c.time.eval z.length ∧
      (flip bind (tmStep c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m)∧m.map e₁=g z:= by
    intro z
    refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
    rw [mapMap]
    conv_rhs =>rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ =>c.outputAlphabet.right_inv y
  have key:∀ q:BitTape × BitTape,∃ n,n≤ T.eval (encodePair q).length ∧
      (flip bind (tmStep (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):= by
    rintro ⟨y,u⟩
    have hku:k * u.length≤ k * (y.length+u.length):= Nat.mul_le_mul_left _ (by omega)
    obtain ⟨n,hn,hr⟩:= iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
      (y.length+u.length+k * (y.length+u.length)) (by omega)
    refine ⟨n,hn.trans ?_,hr⟩
    simp only [T,W,evalAddP,evalMulP,evalCP,
      evalXP,Polynomial.eval_comp,encodePair_length]
    have hmul:u.length * (Polynomial.eval (y.length+u.length+k * (y.length+u.length))
          c.time+2 * (y.length+u.length+k * (y.length+u.length))+3) ≤
        (y.length+u.length) * (Polynomial.eval
          (y.length+u.length+k * (y.length+u.length)) c.time +
            2 * (y.length+u.length+k * (y.length+u.length))+3) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize k * (y.length+u.length)=B at hmul ⊢
    omega
  exact ⟨{
    tm:= iterM c.tm e₀ d₀ e₁
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= T
    outputsFun:= fun q =>
      { steps:= Classical.choose (key q)
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          exact (congrArg (fun l =>(flip bind (tmStep (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l =>some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m:= (Classical.choose_spec (key q)).1 } }⟩
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→ M.Γ M.k₀) (d₀:M.Γ M.k₀→ Bool) (e₁:M.Γ M.k₁→ Bool)
theorem main_loop_bdd (g:TapeMap) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:BitTape,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤ p.eval z.length ∧
      (flip bind (tmStep M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z) :
    ∀ (cn z:BitTape) (L:ℕ) (b:Option (Bool ⊕ Bool)),
      (∀ j≤ cn.length,(g^[j] z).length≤ L) →
      ∃ n,n≤ cn.length * (p.eval L+2 * L+3)+2 * L+3 ∧
        ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (injR IL.l3),(M.initialState,b),
              istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:ICfg M)) =
          some ⟨none,(M.initialState,none),
            istk (fun _ =>[]) [] [] [] (g^[cn.length] z)⟩:= by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz:((z.map e₀).reverse.map d₀).reverse=z:= by
      rw [List.map_reverse,List.reverse_reverse,mapMap]
      conv_rhs =>rw [← List.map_id z]
      exact List.map_congr_left fun a _ =>hd a
    have q1:((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (injR IL.l3),(M.initialState,b),
          istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:ICfg M)) =
        some ⟨some (injR IL.l5),(M.initialState,none),
          istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2:= iloop5 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil,List.append_nil] at q2
    have q3:= iloop6 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil,hz] at q3
    refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3⟩
    have hz0:z.length≤ L:= hL 0 (Nat.zero_le _)
    simp only [List.length_reverse,len_map,len_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s,m,hs,hm,hmg⟩:= hrun z
    rw [len_cons] at hL
    have hz0:z.length≤ L:= hL 0 (Nat.zero_le _)
    have hgz:(g z).length≤ L:= hL 1 (by omega)
    have hml:m.length=(g z).length:= by rw [← hmg,len_map]
    have q1:((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (injR IL.l3),(M.initialState,b),
          istk (upd (fun _ =>[]) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩:ICfg M)) =
        some (embI (some (injL a)) [] cn [] [] (initList M (z.map e₀))):= by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2:= simulate (tmStep M.m) (tmStep (iterProg M e₀ d₀ e₁))
      (embI (some (injL a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (injL a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3:= iloop4 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] cn [] m [] (some (injL a))
    rw [update_nil_nil,List.append_nil,List.map_reverse,hmg] at q3
    have q4:= iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ =>[]) none
    rw [List.append_nil,List.reverse_reverse] at q4
    obtain ⟨n,hn,q5⟩:= ih (g z) L none (fun j hj => by
      have:= hL (j+1) (by omega)
      rwa [iter_succ] at this)
    have e:g^[(a :: cn).length] z=g^[cn.length] (g z):= iter_succ g _ z
    rw [e]
    refine ⟨_,?_,iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp:p.eval z.length≤ p.eval L:= eval_mono p (by omega)
    rw [List.length_reverse,len_cons,Nat.succ_mul]
    generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢
    omega
theorem iter_run_bdd (g:TapeMap) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:BitTape,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤ p.eval z.length ∧
      (flip bind (tmStep M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z)
    (y u:BitTape) (L:ℕ) (hL:∀ j≤ u.length,(g^[j] y).length≤ L) :
    ∃ n,n≤ u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5 ∧
      ((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)):= by
  have q1:((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
      some (⟨some (injR IL.l2),(M.initialState,none),
        istk (fun _ =>[]) [] u.reverse y.reverse []⟩:ICfg M):= by
    have:= iloop1 e₀ d₀ e₁ M.initialState (fun _ =>[]) [] (encodePair (y,u)) [] [] none
    rw [encodePair_left,encodePair_right,List.append_nil,List.append_nil,istk_nil_I] at this
    exact (congrArg (fun c =>((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
  have q2:= iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ =>[]) none
  rw [List.append_nil,List.reverse_reverse] at q2
  obtain ⟨n,hn,q3⟩:= main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3':((flip bind (tmStep (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (injR IL.l3),(M.initialState,none),
        istk (upd (fun _ =>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_,?_,iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length,List.length_reverse]
  omega
theorem iterate_length_measure (g:TapeMap) (m:BitTape→ ℕ)
    (hm:∀ y:BitTape,m (g y)≤ m y)
    (hg:∀ y:BitTape,(g y).length≤ y.length+m y) (y:BitTape) :
    ∀ j:ℕ,m (g^[j] y)≤ m y∧(g^[j] y).length≤ y.length+j * m y:= by
  intro j
  induction j with
  | zero =>simp
  | succ j ih =>
    rw [iter_succ',Nat.succ_mul]
    have h1:= hm (g^[j] y)
    have h2:= hg (g^[j] y)
    obtain ⟨i1,i2⟩:= ih
    generalize j * m y=A at i2 ⊢
    exact ⟨by omega,by omega⟩
theorem measure_arith (A B L V y u:ℕ) (hLV:L≤ V) (hAB:A≤ B) :
    A+2 * L+2 * y+u+5≤ B+2 * V+3 * (y+u)+5:= by
  omega
theorem iter_polyTime_measure (g:TapeMap)
    (c:Turing.TM2ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) g)
    (m:BitTape→ ℕ) (a:ℕ)
    (hm:∀ y:BitTape,m (g y)≤ m y)
    (hg:∀ y:BitTape,(g y).length≤ y.length+m y)
    (ha:∀ y:BitTape,m y≤ a * y.length+a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:BitTape =>x) (fun p:BitTape × BitTape =>g^[p.2.length] p.1)):= by
  let e₀:Bool→ c.tm.Γ c.tm.k₀:= c.inputAlphabet.invFun
  let d₀:c.tm.Γ c.tm.k₀→ Bool:= c.inputAlphabet
  let e₁:c.tm.Γ c.tm.k₁→ Bool:= c.outputAlphabet
  let W:Polynomial ℕ :=
    Polynomial.X+Polynomial.X * (Polynomial.C a * Polynomial.X+Polynomial.C a)
  let T:Polynomial ℕ :=
    Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3) +
      Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
  have hd:∀ a,d₀ (e₀ a)=a:= fun a =>c.inputAlphabet.right_inv a
  have hrun:∀ z:BitTape,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
      s≤ c.time.eval z.length ∧
      (flip bind (tmStep c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m)∧m.map e₁=g z:= by
    intro z
    refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
    rw [mapMap]
    conv_rhs =>rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ =>c.outputAlphabet.right_inv y
  have key:∀ q:BitTape × BitTape,∃ n,n≤ T.eval (encodePair q).length ∧
      (flip bind (tmStep (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):= by
    rintro ⟨y,u⟩
    have hL:∀ j≤ u.length,
        (g^[j] y).length≤ y.length+u.length * (a * y.length+a):= by
      intro j hj
      have h1:= (iterate_length_measure g m hm hg y j).2
      have h2:j * m y≤ u.length * (a * y.length+a):= Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n,hn,hr⟩:= iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
      (y.length+u.length * (a * y.length+a)) hL
    have hLV:y.length+u.length * (a * y.length+a) ≤
        (y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp:= eval_mono c.time hLV
    have hmul:u.length * (Polynomial.eval (y.length+u.length * (a * y.length+a)) c.time +
          2 * (y.length+u.length * (a * y.length+a))+3) ≤
        (y.length+u.length) * (Polynomial.eval
          ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a))
            c.time +
            2 * ((y.length+u.length) +
              (y.length+u.length) * (a * (y.length+u.length)+a))+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n,hn.trans ?_,hr⟩
    simp only [T,W,evalAddP,evalMulP,evalCP,
      evalXP,Polynomial.eval_comp,encodePair_length]
    exact measure_arith _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm:= iterM c.tm e₀ d₀ e₁
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= T
    outputsFun:= fun q =>
      { steps:= Classical.choose (key q)
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          exact (congrArg (fun l =>(flip bind (tmStep (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l =>some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m:= (Classical.choose_spec (key q)).1 } }⟩
end Lib.Machines.Iter
end
section
namespace Lib.Machines
open PEqualNP.Library
open Turing
inductive MulK
  | I | A | B | C | O
  deriving DecidableEq
instance:Fintype MulK :=
  Fintype.ofList [.I,.A,.B,.C,.O] (fun x => by cases x <;> simp)
inductive MulL
  | split | outer | copy | back | clean
  deriving DecidableEq
instance:Fintype MulL :=
  Fintype.ofList [.split,.outer,.copy,.back,.clean] (fun x => by cases x <;> simp)
abbrev MulΓ:MulK→ Type
  | .I =>Bool ⊕ Bool
  | .A =>Bool
  | .B =>Bool
  | .C =>Bool
  | .O =>Bool
def mulProg:MulL→ TM2.Stmt MulΓ MulL (Option Bool)
  | .split =>
    .pop .I (fun _ o =>o.map Sum.isLeft)
      (.branch (fun s =>s.isSome)
        (.branch (fun s =>s == some true)
          (.push .A (fun _ =>true) (.goto fun _ =>.split))
          (.push .B (fun _ =>true) (.goto fun _ =>.split)))
        (.goto fun _ =>.outer))
  | .outer =>
    .pop .A (fun _ o =>o)
      (.branch (fun s =>s.isSome)
        (.goto fun _ =>.copy)
        (.goto fun _ =>.clean))
  | .copy =>
    .pop .B (fun _ o =>o)
      (.branch (fun s =>s.isSome)
        (.push .C (fun _ =>true) (.push .O (fun _ =>true) (.goto fun _ =>.copy)))
        (.goto fun _ =>.back))
  | .back =>
    .pop .C (fun _ o =>o)
      (.branch (fun s =>s.isSome)
        (.push .B (fun _ =>true) (.goto fun _ =>.back))
        (.goto fun _ =>.outer))
  | .clean =>
    .pop .B (fun _ o =>o)
      (.branch (fun s =>s.isSome)
        (.goto fun _ =>.clean)
        .halt)
def mulTM:FinTM2 where
  K:= MulK
  k₀:= .I
  k₁:= .O
  Γ:= MulΓ
  Λ:= MulL
  main:= .split
  σ:= Option Bool
  initialState:= none
  Γk₀Fin:= inferInstanceAs (Fintype (Bool ⊕ Bool))
  m:= mulProg
def mstk (i:List (Bool ⊕ Bool)) (a b c o:BitTape):∀ k,List (MulΓ k)
  | .I =>i
  | .A =>a
  | .B =>b
  | .C =>c
  | .O =>o
@[simp] theorem mstk_I (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mstk i a b c o .I=i:= rfl
@[simp] theorem mstk_A (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mstk i a b c o .A=a:= rfl
@[simp] theorem mstk_B (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mstk i a b c o .B=b:= rfl
@[simp] theorem mstk_C (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mstk i a b c o .C=c:= rfl
@[simp] theorem mstk_O (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mstk i a b c o .O=o:= rfl
@[simp] theorem mstk_set_I (i i':List (Bool ⊕ Bool)) (a b c o:BitTape) :
    upd (mstk i a b c o) .I i'=mstk i' a b c o:= by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_A (i:List (Bool ⊕ Bool)) (a a' b c o:BitTape) :
    upd (mstk i a b c o) .A a'=mstk i a' b c o:= by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_B (i:List (Bool ⊕ Bool)) (a b b' c o:BitTape) :
    upd (mstk i a b c o) .B b'=mstk i a b' c o:= by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_C (i:List (Bool ⊕ Bool)) (a b c c' o:BitTape) :
    upd (mstk i a b c o) .C c'=mstk i a b c' o:= by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_O (i:List (Bool ⊕ Bool)) (a b c o o':BitTape) :
    upd (mstk i a b c o) .O o'=mstk i a b c o':= by
  funext k; cases k <;> simp [mstk]
theorem mstk_start (i:List (Bool ⊕ Bool)) :
    mstk i [] [] [] []=upd (fun _ =>[]:∀ k,List (MulΓ k)) .I i:= by
  funext k; cases k <;> simp [mstk]
theorem mstk_end (o:BitTape) :
    mstk [] [] [] [] o=upd (fun _ =>[]:∀ k,List (MulΓ k)) .O o:= by
  funext k; cases k <;> simp [mstk]
abbrev MulCfg:Type:= TM2.Cfg MulΓ MulL (Option Bool)
abbrev mulStep:Option MulCfg→ Option MulCfg:= flip bind (tmStep mulProg)
theorem split_inl (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mulStep (some ⟨some .split,s,mstk (injL y :: i) a b c o⟩) =
      some ⟨some .split,some true,mstk i (true :: a) b c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem split_inr (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mulStep (some ⟨some .split,s,mstk (injR y :: i) a b c o⟩) =
      some ⟨some .split,some false,mstk i a (true :: b) c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem split_nil (s:Option Bool) (a b c o:BitTape) :
    mulStep (some ⟨some .split,s,mstk [] a b c o⟩) =
      some ⟨some .outer,none,mstk [] a b c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem outer_cons (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mulStep (some ⟨some .outer,s,mstk i (y :: a) b c o⟩) =
      some ⟨some .copy,some y,mstk i a b c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem outer_nil (s:Option Bool) (i:List (Bool ⊕ Bool)) (b c o:BitTape) :
    mulStep (some ⟨some .outer,s,mstk i [] b c o⟩) =
      some ⟨some .clean,none,mstk i [] b c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem copy_cons (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mulStep (some ⟨some .copy,s,mstk i a (y :: b) c o⟩) =
      some ⟨some .copy,some y,mstk i a b (true :: c) (true :: o)⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem copy_nil (s:Option Bool) (i:List (Bool ⊕ Bool)) (a c o:BitTape) :
    mulStep (some ⟨some .copy,s,mstk i a [] c o⟩) =
      some ⟨some .back,none,mstk i a [] c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem back_cons (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mulStep (some ⟨some .back,s,mstk i a b (y :: c) o⟩) =
      some ⟨some .back,some y,mstk i a (true :: b) c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem back_nil (s:Option Bool) (i:List (Bool ⊕ Bool)) (a b o:BitTape) :
    mulStep (some ⟨some .back,s,mstk i a b [] o⟩) =
      some ⟨some .outer,none,mstk i a b [] o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem clean_cons (s:Option Bool) (y:Bool) (i:List (Bool ⊕ Bool)) (a b c o:BitTape) :
    mulStep (some ⟨some .clean,s,mstk i a (y :: b) c o⟩) =
      some ⟨some .clean,some y,mstk i a b c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
theorem clean_nil (s:Option Bool) (i:List (Bool ⊕ Bool)) (a c o:BitTape) :
    mulStep (some ⟨some .clean,s,mstk i a [] c o⟩) =
      some ⟨none,none,mstk i a [] c o⟩:= by
  simp [mulStep,flip,tmStep,mulProg,stepAuxT]
abbrev rep (n:ℕ):BitTape:= List.replicate n true
theorem rep_succ (n:ℕ):true :: rep n=rep (n+1):= rfl
theorem splitLoopW (a:BitTape) :
    ∀ (w:BitTape) (b:ℕ) (s:Option Bool),
      mulStep^[w.length+1] (some ⟨some .split,s,mstk (w.map injR) a (rep b) [] []⟩) =
        some ⟨some .outer,none,mstk [] a (rep (w.length+b)) [] []⟩:= by
  intro w
  induction w with
  | nil =>intro b s; simpa using split_nil s a (rep b) [] []
  | cons y w ih =>
    intro b s
    rw [len_cons,iter_succ,mapC,split_inr,rep_succ,ih]
    rw [show w.length+(b+1)=w.length+1+b from by omega]
theorem splitLoopX (w:BitTape) :
    ∀ (x:BitTape) (a:ℕ) (s:Option Bool),
      mulStep^[x.length+(w.length+1)]
          (some ⟨some .split,s,mstk (x.map injL ++ w.map injR) (rep a) [] [] []⟩) =
        some ⟨some .outer,none,mstk [] (rep (x.length+a)) (rep w.length) [] []⟩:= by
  intro x
  induction x with
  | nil =>
    intro a s
    simpa using splitLoopW (rep a) w 0 s
  | cons y x ih =>
    intro a s
    rw [len_cons,show x.length+1+(w.length+1)=(x.length+(w.length+1))+1
      from by omega,iter_succ,mapC,List.cons_append,split_inl,
      rep_succ,ih]
    rw [show x.length+(a+1)=x.length+1+a from by omega]
theorem copyLoop (a:BitTape) :
    ∀ (b c o:ℕ) (s:Option Bool),
      mulStep^[b+1] (some ⟨some .copy,s,mstk [] a (rep b) (rep c) (rep o)⟩) =
        some ⟨some .back,none,mstk [] a [] (rep (b+c)) (rep (b+o))⟩:= by
  intro b
  induction b with
  | zero =>intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
  | succ b ih =>
    intro c o s
    rw [iter_succ,← rep_succ b,copy_cons,rep_succ,rep_succ,ih]
    rw [show b+(c+1)=b+1+c from by omega,show b+(o+1)=b+1+o from by omega]
theorem backLoop (a o:BitTape) :
    ∀ (c b:ℕ) (s:Option Bool),
      mulStep^[c+1] (some ⟨some .back,s,mstk [] a (rep b) (rep c) o⟩) =
        some ⟨some .outer,none,mstk [] a (rep (c+b)) [] o⟩:= by
  intro c
  induction c with
  | zero =>intro b s; simpa using back_nil s [] a (rep b) o
  | succ c ih =>
    intro b s
    rw [iter_succ,← rep_succ c,back_cons,rep_succ,ih]
    rw [show c+(b+1)=c+1+b from by omega]
theorem outerLoop (b:ℕ) :
    ∀ (a o:ℕ) (s:Option Bool),
      mulStep^[a * (2 * b+3)+1] (some ⟨some .outer,s,mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .clean,none,mstk [] [] (rep b) [] (rep (a * b+o))⟩:= by
  intro a
  induction a with
  | zero =>intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
  | succ a ih =>
    intro o s
    rw [show (a+1) * (2 * b+3)+1=(a * (2 * b+3)+1)+((b+1)+((b+1)+1))
      from by ring,iter_add mulStep (a * (2 * b+3)+1),
      iter_add mulStep (b+1) ((b+1)+1),
      iter_succ mulStep (b+1),← rep_succ a,outer_cons]
    have h1:mulStep^[b+1]
        (some ⟨some .copy,some true,mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .back,none,mstk [] (rep a) [] (rep b) (rep (b+o))⟩ :=
      copyLoop (rep a) b 0 o (some true)
    rw [h1]
    have h2:mulStep^[b+1]
        (some ⟨some .back,none,mstk [] (rep a) [] (rep b) (rep (b+o))⟩) =
        some ⟨some .outer,none,mstk [] (rep a) (rep b) [] (rep (b+o))⟩ :=
      backLoop (rep a) (rep (b+o)) b 0 none
    rw [h2,ih]
    rw [show a * b+(b+o)=(a+1) * b+o from by ring]
theorem cleanLoop (o:BitTape) :
    ∀ (b:ℕ) (s:Option Bool),
      mulStep^[b+1] (some ⟨some .clean,s,mstk [] [] (rep b) [] o⟩) =
        some ⟨none,none,mstk [] [] [] [] o⟩:= by
  intro b
  induction b with
  | zero =>intro s; simpa using clean_nil s [] [] [] o
  | succ b ih =>
    intro s
    rw [iter_succ,← rep_succ b,clean_cons,ih]
def mulSteps (x w:ℕ):ℕ:= (w+1)+((x * (2 * w+3)+1)+(x+(w+1)))
theorem mul_run (x w:BitTape) :
    (flip bind (tmStep mulProg))^[mulSteps x.length w.length]
        (some (initList mulTM (x.map injL ++ w.map injR))) =
      some (haltList mulTM (rep (x.length * w.length))):= by
  refine (congrArg (fun c =>(flip bind (tmStep mulProg))^[mulSteps x.length w.length]
    (some c)) (initList_eq mulTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
  show mulStep^[mulSteps x.length w.length]
    (some (⟨some .split,none,upd (fun _ =>[]) .I
      (x.map injL ++ w.map injR)⟩:MulCfg)) =
    some (⟨none,none,upd (fun _ =>[]) .O (rep (x.length * w.length))⟩:MulCfg)
  rw [← mstk_start,← mstk_end,mulSteps,iter_add mulStep (w.length+1),
    iter_add mulStep (x.length * (2 * w.length+3)+1)]
  have h1:mulStep^[x.length+(w.length+1)]
      (some ⟨some .split,none,mstk (x.map injL ++ w.map injR) [] [] [] []⟩) =
      some ⟨some .outer,none,mstk [] (rep x.length) (rep w.length) [] []⟩ :=
    splitLoopX w x 0 none
  rw [h1]
  have h2:mulStep^[x.length * (2 * w.length+3)+1]
      (some ⟨some .outer,none,mstk [] (rep x.length) (rep w.length) [] []⟩) =
      some ⟨some .clean,none,mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
    outerLoop w.length x.length 0 none
  rw [h2,cleanLoop]
theorem mul_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>List.replicate (p.1.length * p.2.length) true)):= by
  exact ⟨{
    tm:= mulTM
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= Polynomial.C 2 * Polynomial.X ^ 2+Polynomial.C 5 * Polynomial.X+Polynomial.C 3
    outputsFun:= fun p =>
      { steps:= mulSteps p.1.length p.2.length
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          have:= mul_run p.1 p.2
          exact (congrArg (fun l =>(flip bind (tmStep mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
            (this.trans (congrArg (fun l =>some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m:= by
          simp only [evalAddP,evalMulP,evalCP,
            evalXP,Polynomial.eval_pow,encodePair,len_app,
            len_map,mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length),Nat.zero_le (p.1.length * p.2.length)] } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open PEqualNP.Library
private theorem filterMap_map_some {α β γ:Type} (h:α→ β) (φ:β→ Option γ) (g:α→ γ)
    (hφ:∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ=l.map g:= by
  induction l with
  | nil =>rfl
  | cons a l ih =>simp [hφ,ih]
private theorem filterMap_map_none {α β γ:Type} (h:α→ β) (φ:β→ Option γ)
    (hφ:∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ=[]:= by
  induction l with
  | nil =>rfl
  | cons a l ih =>simp [hφ,ih]
theorem cpt_comp {α β γ αΓ βΓ γΓ:Type} {ea:α→ List αΓ} {eb:β→ List βΓ}
    {ec:γ→ List γΓ} {f:α→ β} {g:β→ γ}
    (hf:PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg:PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a =>g (f a)):= by
  obtain ⟨c1⟩:= hf
  obtain ⟨c2⟩:= hg
  exact comp_polyTime ea eb ec f g c1 c2
theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:BitTape × BitTape =>(p.2,p.1)):= by
  refine twoPass_polyTime _ _ _
    (fun s:Bool ⊕ Bool =>Sum.elim (fun _ =>none) (fun b =>some (injL b)) s)
    (fun s:Bool ⊕ Bool =>Sum.elim (fun b =>some (injR b)) (fun _ =>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [filterMap_map_none injL _ (fun _ =>rfl) x,
    filterMap_map_some injR _ injL (fun _ =>rfl) w,
    filterMap_map_some injL _ injR (fun _ =>rfl) x,
    filterMap_map_none injR _ (fun _ =>rfl) w]
  simp
theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      PEqualNP.Library.encodePair (fun x:BitTape =>(x,x)):= by
  refine twoPass_polyTime _ _ _
    (fun b:Bool =>some (injL b)) (fun b:Bool =>some (injR b)) ?_
  intro x
  have h1:= filterMap_map_some (fun b:Bool =>b) (fun b:Bool =>some (injL (β:= Bool) b))
    injL (fun _ =>rfl) x
  have h2:= filterMap_map_some (fun b:Bool =>b) (fun b:Bool =>some (injR (α:= Bool) b))
    injR (fun _ =>rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair,h1,h2]
theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:BitTape =>x) (fun p:BitTape × BitTape =>p.1):= by
  refine filterMap_polyTime _ _ _
    (fun s:Bool ⊕ Bool =>Sum.elim (fun b =>some b) (fun _ =>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [filterMap_map_some injL _ (fun b =>b) (fun _ =>rfl) x,
    filterMap_map_none injR _ (fun _ =>rfl) w]
  simp
theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:BitTape =>x) (fun p:BitTape × BitTape =>p.2):= by
  refine filterMap_polyTime _ _ _
    (fun s:Bool ⊕ Bool =>Sum.elim (fun _ =>none) (fun b =>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [filterMap_map_none injL _ (fun _ =>rfl) x,
    filterMap_map_some injR _ (fun b =>b) (fun _ =>rfl) w]
  simp
theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:BitTape =>x) (fun p:BitTape × BitTape =>p.1 ++ p.2):= by
  refine filterMap_polyTime _ _ _
    (fun s:Bool ⊕ Bool =>Sum.elim (fun b =>some b) (fun b =>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [filterMap_map_some injL _ (fun b =>b) (fun _ =>rfl) x,
    filterMap_map_some injR _ (fun b =>b) (fun _ =>rfl) w]
  simp
theorem cpt_first {f:TapeMap}
    (hf:PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:BitTape × BitTape =>(f p.1,p.2)):= by
  obtain ⟨c⟩:= hf
  exact first_polyTime f c
theorem cpt_second {g:TapeMap}
    (hg:PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:BitTape × BitTape =>(p.1,g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap
theorem cpt_pair {f g:TapeMap}
    (hf:PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) f)
    (hg:PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      PEqualNP.Library.encodePair (fun x:BitTape =>(f x,g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)
theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) (fun x:BitTape =>x):= by
  refine filterMap_polyTime _ _ _ (fun b:Bool =>some b) ?_
  intro x
  have h:= filterMap_map_some (fun b:Bool =>b) (fun b:Bool =>some b) (fun b =>b)
    (fun _ =>rfl) x
  simp only [List.map_id'] at h
  exact h.symm
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
theorem output_length_poly (f:TapeMap)
    (hf:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) f) :
    ∃ q:Polynomial ℕ,∀ x:BitTape,(f x).length≤ q.eval x.length:= by
  obtain ⟨c⟩:= hf
  refine ⟨Polynomial.X+Polynomial.C (maxPush c.tm) * c.time,fun x =>?_⟩
  obtain ⟨⟨steps,hev⟩,hle⟩:= c.outputsFun x
  have hev':(flip bind (tmStep c.tm.m))^[steps]
      (some (⟨some c.tm.main,c.tm.initialState,upd (fun _ =>[]) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩:TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none,c.tm.initialState,upd (fun _ =>[]) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩:TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ):= by
    rw [← initList_eq,← haltList_eq]; exact hev
  have key:= run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [upd_self,len_map] at key
  have hin:((upd (fun _ =>([]:List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x):∀ k,List (c.tm.Γ k)) c.tm.k₁).length≤ x.length:= by
    by_cases hk:c.tm.k₁=c.tm.k₀
    · rw [hk]; simp
    · rw [upd_ne hk]; simp
  rw [evalAddP,evalXP,evalMulP,evalCP]
  calc (f x).length≤ x.length+maxPush c.tm * steps:= key.trans (by omega)
    _≤ x.length+maxPush c.tm * c.time.eval x.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def fstRun {Γ₀ Γ₁ Q:Type} (δ:Q→ Γ₀→ Q × Option Γ₁) (fin:Q→ Option Γ₁) :
    Q→ List Γ₀→ List Γ₁
  | q,[] =>(fin q).toList
  | q,a :: l =>(δ q a).2.toList ++ fstRun δ fin (δ q a).1 l
def fstRun2 {Γ₀ Γ₁ Q:Type} (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) :
    Q→ List Γ₀→ List Γ₁
  | q,[] =>(fin q).toList
  | q,a :: l =>(δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l
theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q:Type} (δ:Q→ Γ₀→ Q × Option Γ₁) (fin:Q→ Option Γ₁)
    (q:Q) (l:List Γ₀) :
    fstRun δ fin q l=fstRun2 (fun q a =>((δ q a).1,(δ q a).2,none)) fin q l:= by
  induction l generalizing q with
  | nil =>rfl
  | cons a l ih =>simp [fstRun,fstRun2,ih]
inductive TrK:Type
  | inp | tmp | out
  deriving DecidableEq
instance:Fintype TrK :=
  Fintype.ofList [.inp,.tmp,.out] (fun x => by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK→ Type
  | .inp =>Γ₀
  | .tmp =>Q × Option Γ₀
  | .out =>Γ₁
abbrev TrS (Γ₀ Q:Type):Type:= Q × Option Γ₀ × Bool
def trO1 (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) :
    Q × Option Γ₀→ Option Γ₁
  | (q,some a) =>(δ q a).2.1
  | (q,none) =>fin q
def trO2 (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁):Q × Option Γ₀→ Option Γ₁
  | (q,some a) =>(δ q a).2.2
  | (_,none) =>none
def trOut (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁)
    (e:Q × Option Γ₀):List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList
def trTrace (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁):Q→ List Γ₀→ List (Q × Option Γ₀)
  | q,[] =>[(q,none)]
  | q,a :: l =>(q,some a) :: trTrace δ (δ q a).1 l
theorem trTrace_length (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (q:Q) (l:List Γ₀) :
    (trTrace δ q l).length=l.length+1:= by
  induction l generalizing q with
  | nil =>rfl
  | cons a l ih =>simp [trTrace,ih]
theorem trTrace_out (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) (q:Q)
    (l:List Γ₀):(trTrace δ q l).flatMap (trOut δ fin)=fstRun2 δ fin q l:= by
  induction l generalizing q with
  | nil =>simp [trTrace,trOut,trO1,trO2,fstRun2]
  | cons a l ih =>simp [trTrace,trOut,trO1,trO2,fstRun2,ih]
def trWrite (o:TrS Γ₀ Q→ Option Γ₁) (d:Option Γ₁)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s =>(o s).isSome)
    (match d with
      | some dd =>.push .out (fun s =>(o s).getD dd) next
      | none =>next)
    next
def trProg (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) (q₀:Q)
    (d:Option Γ₁):Bool→ TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o =>(s.1,o,o.isSome))
      (.branch (fun s =>s.2.2)
        (.push .tmp (fun s =>(s.1,s.2.1))
          (.load (fun s =>(match s.2.1 with
              | some a =>(δ s.1 a).1
              | none =>s.1,none,false))
            (.goto fun _ =>false)))
        (.push .tmp (fun s =>(s.1,none))
          (.load (fun _ =>(q₀,none,false)) (.goto fun _ =>true))))
  | true =>
    .pop .tmp (fun _ o =>match o with
        | some e =>(e.1,e.2,true)
        | none =>(q₀,none,false))
      (.branch (fun s =>s.2.2)
        (trWrite (fun s =>trO2 δ (s.1,s.2.1)) d
          (trWrite (fun s =>trO1 δ fin (s.1,s.2.1)) d (.goto fun _ =>true)))
        .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁)
    (fin:Q→ Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
  K:= TrK
  k₀:= .inp
  k₁:= .out
  Γ:= TrΓ Γ₀ Γ₁ Q
  Λ:= Bool
  main:= false
  σ:= TrS Γ₀ Q
  initialState:= (q₀,none,false)
  Γk₀Fin:= inferInstanceAs (Fintype Γ₀)
  m:= trProg δ fin q₀ d
def trSt (l:List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
  | .inp =>l
  | .tmp =>t
  | .out =>u
theorem trSt_set_inp (l l':List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    upd (trSt l t u) .inp l'=trSt l' t u:= by
  funext k; cases k <;> simp [trSt]
theorem trSt_set_tmp (l:List Γ₀) (t t':List (Q × Option Γ₀)) (u:List Γ₁) :
    upd (trSt l t u) .tmp t'=trSt l t' u:= by
  funext k; cases k <;> simp [trSt]
theorem trSt_set_out (l:List Γ₀) (t:List (Q × Option Γ₀)) (u u':List Γ₁) :
    upd (trSt l t u) .out u'=trSt l t u':= by
  funext k; cases k <;> simp [trSt]
theorem trSt_start (l:List Γ₀) :
    (trSt l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      upd (fun _ =>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:= by
  funext k; cases k <;> simp [trSt]
theorem trSt_end (u:List Γ₁) :
    (trSt [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      upd (fun _ =>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:= by
  funext k; cases k <;> simp [trSt]
abbrev TrCfg (Γ₀ Γ₁ Q:Type):Type:= TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
theorem trWrite_stepAux (o:TrS Γ₀ Q→ Option Γ₁) (d:Option Γ₁) (hd:∀ _:Γ₁,d ≠ none)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    stepAuxT (trWrite o d next) s (trSt l t u) =
      stepAuxT next s (trSt l t ((o s).toList ++ u)):= by
  cases ho:o s with
  | none =>cases d <;> simp [trWrite,stepAuxT,ho]
  | some y =>
    cases d with
    | none =>exact absurd rfl (hd y)
    | some dd =>simp [trWrite,stepAuxT,ho,trSt,trSt_set_out]
variable (δ:Q→ Γ₀→ Q × Option Γ₁ × Option Γ₁) (fin:Q→ Option Γ₁) (q₀:Q)
  (d:Option Γ₁)
theorem trA_cons (s:TrS Γ₀ Q) (a:Γ₀) (l:List Γ₀) (t:List (Q × Option Γ₀))
    (u:List Γ₁) :
    tmStep (trProg δ fin q₀ d) (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩:= by
  simp [tmStep,trProg,stepAuxT,trSt,trSt_set_inp,trSt_set_tmp]
theorem trA_nil (s:TrS Γ₀ Q) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    tmStep (trProg δ fin q₀ d) (⟨some false,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true,(q₀,none,false),trSt [] ((s.1,none) :: t) u⟩:= by
  simp [tmStep,trProg,stepAuxT,trSt,trSt_set_inp,trSt_set_tmp]
theorem trB_cons (hd:∀ _:Γ₁,d ≠ none) (s:TrS Γ₀ Q) (e:Q × Option Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    tmStep (trProg δ fin q₀ d) (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e ++ u)⟩:= by
  simp only [tmStep,trProg,stepAuxT]
  have e1:(trSt [] (e :: t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e :: t:= rfl
  rw [e1]
  simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
  rw [trSt_set_tmp,trWrite_stepAux _ _ hd,trWrite_stepAux _ _ hd]
  simp [stepAuxT,trOut]
theorem trB_nil (s:TrS Γ₀ Q) (u:List Γ₁) :
    tmStep (trProg δ fin q₀ d) (⟨some true,s,trSt [] [] u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨none,(q₀,none,false),trSt [] [] u⟩:= by
  simp [tmStep,trProg,stepAuxT,trSt,trSt_set_tmp]
theorem trLoopA (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Q × Option Γ₀)) (s:TrS Γ₀ Q),
      (flip bind (tmStep (trProg δ fin q₀ d)))^[l.length+1]
          (some (⟨some false,s,trSt l t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true,(q₀,none,false),trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩:= by
  intro l
  induction l with
  | nil =>intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [len_cons,iter_succ]
    have e:flip bind (tmStep (trProg δ fin q₀ d))
        (some (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e,ih]
    simp [trTrace]
theorem trLoopB (hd:∀ _:Γ₁,d ≠ none) :
    ∀ (t:List (Q × Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
      (flip bind (tmStep (trProg δ fin q₀ d)))^[t.length+1]
          (some (⟨some true,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none,(q₀,none,false),trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩:= by
  intro t
  induction t with
  | nil =>intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [len_cons,iter_succ]
    have e':flip bind (tmStep (trProg δ fin q₀ d))
        (some (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e',ih]
    simp [List.flatMap_append]
theorem trM_run [Fintype Γ₀] [Fintype Q] (hd:∀ _:Γ₁,d ≠ none) (l:List Γ₀) :
    (flip bind (tmStep (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)):= by
  refine (congrArg (fun c =>(flip bind (tmStep (trProg δ fin q₀ d)))^[l.length+1+1 +
    (l.length+1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (tmStep (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
    (some (⟨some false,(q₀,none,false),upd (fun _ =>[]) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none,(q₀,none,false),upd (fun _ =>[]) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA:(flip bind (tmStep (trProg δ fin q₀ d)))^[l.length+1]
      (some (⟨some false,(q₀,none,false),trSt l [] []⟩:TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true,(q₀,none,false),trSt [] (trTrace δ q₀ l).reverse []⟩:= by
    have:= trLoopA δ fin q₀ d [] l [] (q₀,none,false)
    rw [List.append_nil] at this
    exact this
  have hB:(flip bind (tmStep (trProg δ fin q₀ d)))^[l.length+1+1]
      (some (⟨some true,(q₀,none,false),trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none,(q₀,none,false),trSt [] [] (fstRun2 δ fin q₀ l)⟩:= by
    have:= trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀,none,false)
    rw [List.length_reverse,trTrace_length,List.reverse_reverse,trTrace_out,
      List.append_nil] at this
    exact this
  rw [iter_add,← trSt_start,hA,hB,trSt_end]
theorem fst2_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (δ:Q→ αΓ→ Q × Option βΓ × Option βΓ)
    (fin:Q→ Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):= by
  classical
  let d:Option βΓ:= if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ _:βΓ,d ≠ none:= by
    intro y
    have hn:Nonempty βΓ:= ⟨y⟩
    simp [d,hn]
  exact ⟨{
    tm:= trM δ fin q₀ d
    inputAlphabet:= Equiv.refl _
    outputAlphabet:= Equiv.refl _
    time:= Polynomial.C 2 * Polynomial.X+Polynomial.C 3
    outputsFun:= fun a =>
      { steps:= (ea a).length+1+1+((ea a).length+1)
        evals_in_steps:= by
          have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l => by simp
          have:= trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l =>(flip bind (tmStep (trProg δ fin q₀ d)))^[(ea a).length +
            1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l =>some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:= by
          simp only [evalAddP,evalMulP,evalCP,
            evalXP]
          omega } }⟩
theorem fst_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→ List αΓ)
    (eb:β→ List βΓ) (f:α→ β) (δ:Q→ αΓ→ Q × Option βΓ) (fin:Q→ Option βΓ) (q₀:Q)
    (h:∀ a,eb (f a)=fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a =>((δ q a).1,(δ q a).2,none)) fin q₀
    (fun a =>(h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))
end Lib.Machines
end
section
namespace Lib.Machines
open PEqualNP.Library
private theorem cpt_mul {f g:TapeMap}
    (hf:PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) f)
    (hg:PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x)
      (fun x:BitTape =>x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun x:BitTape =>List.replicate ((f x).length * (g x).length) true) :=
  cpt_comp (cpt_pair hf hg) mul_polyTime
private theorem pow_polyTime
    (hconst:∀ l:BitTape,PEqualNP.Library.ComputableInPolyTime
      (fun x:BitTape =>x) (fun x:BitTape =>x) (fun _:BitTape =>l))
    (n:ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun x:BitTape =>List.replicate (x.length ^ n) true):= by
  induction n with
  | zero =>simpa using hconst [true]
  | succ n ih =>
    have h:= cpt_mul cpt_id ih
    have e:(fun x:BitTape =>
        List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true) =
        (fun x:BitTape =>List.replicate (x.length ^ (n+1)) true):= by
      funext x
      rw [len_rep,pow_succ,Nat.mul_comm]
    rw [← e]
    exact h
theorem clock_polyTime
    (hconst:∀ l:BitTape,PEqualNP.Library.ComputableInPolyTime
      (fun x:BitTape =>x) (fun x:BitTape =>x) (fun _:BitTape =>l))
    (p:Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun x:BitTape =>List.replicate (p.eval x.length) true):= by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h:= cpt_comp (cpt_pair hp hq) cpt_append
    have e:(fun x:BitTape =>List.replicate (p.eval x.length) true ++
        List.replicate (q.eval x.length) true) =
        (fun x:BitTape =>List.replicate ((p+q).eval x.length) true):= by
      funext x
      rw [evalAddP,List.replicate_add]
    rw [← e]
    exact h
  | monomial n a =>
    have h:= cpt_mul (hconst (List.replicate a true)) (pow_polyTime hconst n)
    have e:(fun x:BitTape =>List.replicate ((List.replicate a true).length *
        (List.replicate (x.length ^ n) true).length) true) =
        (fun x:BitTape =>
          List.replicate ((Polynomial.monomial n a).eval x.length) true):= by
      funext x
      rw [len_rep,len_rep,Polynomial.eval_monomial]
    rw [← e]
    exact h
end Lib.Machines
end
section
theorem Lib.L055:∀ p:Polynomial ℕ,
    PEqualNP.Library.ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun x:BitTape =>List.replicate (p.eval x.length) true) :=
  fun p =>Lib.Machines.clock_polyTime
    (fun l =>Lib.Machines.constList_polyTime l) p
end
section
namespace Lib.Universal
def un (n:ℕ):BitTape:= List.replicate n true
def pairB (a b:BitTape):BitTape:= un a.length ++ false :: (a ++ b)
def unpairB (s:BitTape):BitTape × BitTape :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)
theorem unpairB_pairB (a b:BitTape):unpairB (pairB a b)=(a,b):= by
  have h1:(pairB a b).takeWhile id=un a.length:= by
    simp [pairB,un]
  have h2:(pairB a b).dropWhile id=false :: (a ++ b):= by
    simp [pairB,un]
  simp [unpairB,h1,h2,un]
end Lib.Universal
end
section
namespace Lib.Universal
def bflag (b:Bool):BitTape:= if b then [true] else []
@[simp] theorem un_zero:un 0=[]:= rfl
@[simp] theorem un_length (n:ℕ):(un n).length=n:= len_rep
theorem un_succ (n:ℕ):un (n+1)=true :: un n:= rfl
def hd (s:BitTape):BitTape:= s.takeWhile id
def dropN (s:BitTape):BitTape:= (s.dropWhile id).tail
def sel (f a b:BitTape):BitTape:= if f=[] then a else b
def mulU (u v:BitTape):BitTape:= un (u.length * v.length)
def spread (s:BitTape):BitTape:= s.flatMap fun b =>if b then [true,false] else [false]
def blank (s:BitTape):BitTape:= s.map fun _ =>false
theorem unpairB_length (s:BitTape) :
    2 * (unpairB s).1.length+(unpairB s).2.length≤ s.length:= by
  have h:= congrArg List.length (List.takeWhile_append_dropWhile (p:= id) (l:= s))
  simp only [len_app] at h
  simp only [unpairB,List.length_take,List.length_drop,List.length_tail]
  omega
theorem pairB_length (a b:BitTape):(pairB a b).length=2 * a.length+b.length+1:= by
  simp [pairB]; omega
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cpt_congr {α β αΓ βΓ:Type} {ea:α→ List αΓ} {eb:β→ List βΓ}
    {f f':α→ β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':= by
  obtain rfl:f=f':= funext e
  exact h
private theorem fm_elim {A B C:Type} (φl:A→ Option C) (φr:B→ Option C) (x:List A)
    (w:List B) :
    (x.map injL ++ w.map injR).filterMap (Sum.elim φl φr) =
      x.filterMap φl ++ w.filterMap φr:= by
  have h1:∀ x:List A,(x.map injL).filterMap (Sum.elim φl φr)=x.filterMap φl:= by
    intro x; induction x with
    | nil =>rfl
    | cons a l ih =>simp [List.filterMap_cons,ih]
  have h2:∀ w:List B,(w.map injR).filterMap (Sum.elim φl φr)=w.filterMap φr:= by
    intro w; induction w with
    | nil =>rfl
    | cons a l ih =>simp [List.filterMap_cons,ih]
  rw [List.filterMap_append,h1,h2]
private theorem fm_some {A C:Type} (g:A→ C) (l:List A) :
    l.filterMap (fun a =>some (g a))=l.map g:= by
  induction l with
  | nil =>rfl
  | cons a l ih =>simp [ih]
private theorem fm_none {A C:Type} (l:List A) :
    l.filterMap (fun _:A =>(none:Option C))=[]:= by
  induction l with
  | nil =>rfl
  | cons a l ih =>simp
theorem cpt_pairB :
    ComputableInPolyTime encodePair (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>pairB p.1 p.2):= by
  have hA:ComputableInPolyTime encodePair encodePair
      (fun p:BitTape × BitTape =>(p.1,p.1 ++ p.2)):= by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun b:Bool =>some (injL b)) (fun _:Bool =>none))
      (Sum.elim (fun b:Bool =>some (injR b)) (fun b:Bool =>some (injR b))) ?_
    rintro ⟨x,w⟩
    simp only [encodePair]
    rw [fm_elim,fm_elim,fm_some,fm_some,fm_some,fm_none]
    simp
  have hU:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun a:BitTape =>a.map (fun _ =>true) ++ [false]):= by
    refine fst_polyTime _ _ _ (fun (_:Unit) (_:Bool) =>((),some true))
      (fun _ =>some false) () ?_
    intro a
    induction a with
    | nil =>rfl
    | cons b l ih =>
      simp only [fstRun,mapC,List.cons_append,Option.toList_some] at ih ⊢
      rw [← ih]; rfl
  refine cpt_congr (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
  rintro ⟨x,w⟩
  simp [pairB,un]
theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>if p.1=[] then p.2 else []):= by
  obtain ⟨c⟩:= constList_polyTime []
  have hI:= Iter.iter_polyTime (fun _:BitTape =>([]:BitTape)) c 0 (by simp)
  refine cpt_congr (cpt_comp cpt_swap hI) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil =>simp
  | cons b l =>simp [iter_succ']
theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>if p.1=[] then [] else p.2):= by
  have hneg:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun x:BitTape =>if x=[] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
  refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil =>simp
  | cons b l =>simp
private def encT (u:BitTape):BitTape:= u.flatMap (fun b =>[true,b])
private def encF (v:BitTape):BitTape:= v.flatMap (fun b =>[false,b])
private def twD:Bool→ Bool→ Bool × Option Bool
  | true,true =>(true,some true)
  | _,_ =>(false,none)
private theorem twD_run (l:BitTape) :
    fstRun twD (fun _ =>none) false l=[] ∧
      fstRun twD (fun _ =>none) true l=l.takeWhile id:= by
  induction l with
  | nil =>exact ⟨rfl,rfl⟩
  | cons b l ih =>cases b <;> simp [fstRun,twD,ih.1,ih.2]
private def e0D:Bool→ Bool→ Bool × Option Bool × Option Bool
  | false,true =>(false,none,none)
  | false,false =>(true,none,none)
  | true,b =>(true,some false,some b)
private theorem e0D_run_true (l:BitTape) :
    fstRun2 e0D (fun _ =>none) true l=encF l:= by
  induction l with
  | nil =>rfl
  | cons b l ih =>simp [fstRun2,e0D,encF,ih]
private theorem e0D_run_false (l:BitTape) :
    fstRun2 e0D (fun _ =>none) false l=encF (l.dropWhile id).tail:= by
  induction l with
  | nil =>rfl
  | cons b l ih =>cases b <;> simp [fstRun2,e0D,ih,e0D_run_true]
private def mkD:Bool × Bool→ Bool→ (Bool × Bool) × Option Bool
  | (d,false),t =>((d || !t,true),some (t || !d))
  | (d,true),b =>((d,false),some b)
private def mk (l:BitTape):BitTape:= fstRun mkD (fun _ =>none) (false,false) l
private theorem mkD_length (q:Bool × Bool) (l:BitTape) :
    (fstRun mkD (fun _ =>none) q l).length=l.length:= by
  induction l generalizing q with
  | nil =>rfl
  | cons b l ih =>obtain ⟨d,ph⟩:= q; cases ph <;> simp [fstRun,mkD,ih]
private theorem mkD_done (v:BitTape) :
    fstRun mkD (fun _ =>none) (true,false) (encF v)=encF v:= by
  induction v with
  | nil =>rfl
  | cons b v ih =>simp [fstRun,mkD,encF] at ih ⊢; exact ih
private theorem mkD_marked (u r:BitTape) :
    fstRun mkD (fun _ =>none) (false,false) (encT u ++ r) =
      encT u ++ fstRun mkD (fun _ =>none) (false,false) r:= by
  induction u with
  | nil =>rfl
  | cons b u ih =>simp [fstRun,mkD,encT] at ih ⊢; exact ih
private theorem mk_nil (u:BitTape):mk (encT u ++ encF [])=encT u ++ encF []:= by
  unfold mk; rw [mkD_marked]; rfl
private theorem mk_cons (u:BitTape) (b:Bool) (v:BitTape) :
    mk (encT u ++ encF (b :: v))=encT (u ++ [b]) ++ encF v:= by
  unfold mk
  rw [mkD_marked]
  have h:fstRun mkD (fun _ =>none) (false,false) (encF (b :: v)) =
      true :: b :: encF v:= by
    have h':= mkD_done v
    simp [fstRun,mkD,encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]
private theorem mk_iter (k:ℕ):∀ u t:BitTape,
    mk^[k] (encT u ++ encF t)=encT (u ++ t.take k) ++ encF (t.drop k):= by
  induction k with
  | zero =>intro u t; simp
  | succ k ih =>
    intro u t
    rw [iter_succ]
    cases t with
    | nil =>rw [mk_nil,ih]; simp
    | cons b t =>rw [mk_cons,ih]; simp
private def dcD:Option Bool→ Bool→ Option Bool × Option (Bool ⊕ Bool)
  | none,t =>(some t,none)
  | some t,b =>(none,some (if t then injL b else injR b))
private theorem dcD_F (v:BitTape) :
    fstRun dcD (fun _ =>none) none (encF v)=v.map injR:= by
  induction v with
  | nil =>rfl
  | cons b v ih =>simp [fstRun,dcD,encF] at ih ⊢; exact ih
private theorem dcD_T (u r:BitTape) :
    fstRun dcD (fun _ =>none) none (encT u ++ r) =
      u.map injL ++ fstRun dcD (fun _ =>none) none r:= by
  induction u with
  | nil =>rfl
  | cons b u ih =>simp [fstRun,dcD,encT] at ih ⊢; exact ih
private def rawDec (l:List (Bool ⊕ Bool)):BitTape × BitTape :=
  (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private theorem rawDec_tagged (u v:BitTape) :
    rawDec (u.map injL ++ v.map injR)=(u,v):= by
  have h1:∀ x:BitTape,(x.map (injL (β:= Bool))).filterMap Sum.getLeft?=x:= by
    intro x; induction x with
    | nil =>rfl
    | cons a l ih =>exact congrArg (a :: ·) ih
  have h2:∀ x:BitTape,(x.map (injR (α:= Bool))).filterMap Sum.getLeft?=[]:= by
    intro x; induction x with
    | nil =>rfl
    | cons a l ih =>exact ih
  have h3:∀ x:BitTape,(x.map (injL (β:= Bool))).filterMap Sum.getRight?=[]:= by
    intro x; induction x with
    | nil =>rfl
    | cons a l ih =>exact ih
  have h4:∀ x:BitTape,(x.map (injR (α:= Bool))).filterMap Sum.getRight?=x:= by
    intro x; induction x with
    | nil =>rfl
    | cons a l ih =>exact congrArg (a :: ·) ih
  simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
theorem cpt_unpairB :
    ComputableInPolyTime (fun x:BitTape =>x) encodePair unpairB:= by
  have hTw:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s:BitTape =>s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _ =>none) true (fun s =>(twD_run s).2.symm)
  have hE0:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s:BitTape =>encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _ =>none) false (fun s =>(e0D_run_false s).symm)
  have hMk:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) mk :=
    fst_polyTime _ _ _ mkD (fun _ =>none) (false,false) (fun _ =>rfl)
  obtain ⟨cMk⟩:= hMk
  have hIt:= Iter.iter_polyTime mk cMk 0 (fun y => by simp [mk,mkD_length])
  have hDc:ComputableInPolyTime (fun x:BitTape =>x) (fun l:List (Bool ⊕ Bool) =>l)
      (fun l:BitTape =>fstRun dcD (fun _ =>none) none l) :=
    fst_polyTime _ _ _ dcD (fun _ =>none) none (fun _ =>rfl)
  have hRaw:ComputableInPolyTime (fun l:List (Bool ⊕ Bool) =>l) encodePair rawDec:= by
    refine twoPass_polyTime _ _ _
      (fun s:Bool ⊕ Bool =>(Sum.getLeft? s).map injL)
      (fun s:Bool ⊕ Bool =>(Sum.getRight? s).map injR) ?_
    intro l
    simp only [rawDec,encodePair,List.map_filterMap]
  refine cpt_congr (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h:= mk_iter (s.takeWhile id).length [] (s.dropWhile id).tail
  have e:encT [] ++ encF (s.dropWhile id).tail=encF (s.dropWhile id).tail:= rfl
  rw [e] at h
  simp only [h,List.nil_append]
  rw [dcD_T,dcD_F,rawDec_tagged]
  rfl
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptc {α β αΓ βΓ:Type} {ea:α→ List αΓ} {eb:β→ List βΓ}
    {f f':α→ β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':= by
  obtain rfl:f=f':= funext e
  exact h
private def hdD:Bool→ Bool→ Bool × Option Bool
  | true,true =>(true,some true)
  | _,_ =>(false,none)
private theorem hdD_run (l:BitTape) :
    fstRun hdD (fun _ =>none) false l=[] ∧
      fstRun hdD (fun _ =>none) true l=l.takeWhile id:= by
  induction l with
  | nil =>exact ⟨rfl,rfl⟩
  | cons b l ih =>cases b <;> simp [fstRun,hdD,ih.1,ih.2]
theorem cpt_hd :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) hd :=
  fst_polyTime _ _ _ hdD (fun _ =>none) true (fun s =>(hdD_run s).2.symm)
private def dnD:Bool→ Bool→ Bool × Option Bool
  | false,true =>(false,none)
  | false,false =>(true,none)
  | true,b =>(true,some b)
private def tlD:Bool→ Bool→ Bool × Option Bool
  | false,_ =>(true,none)
  | true,b =>(true,some b)
private theorem tlD_true (l:BitTape):fstRun tlD (fun _ =>none) true l=l:= by
  induction l with
  | nil =>rfl
  | cons b l ih =>simp [fstRun,tlD,ih]
private theorem tlD_false (l:BitTape):fstRun tlD (fun _ =>none) false l=l.tail:= by
  cases l with
  | nil =>rfl
  | cons b l =>simp [fstRun,tlD,tlD_true]
theorem cpt_tail :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s:BitTape =>s.tail) :=
  fst_polyTime _ _ _ tlD (fun _ =>none) false (fun s =>(tlD_false s).symm)
private def spD:Unit→ Bool→ Unit × Option Bool × Option Bool
  | _,true =>((),some true,some false)
  | _,false =>((),some false,none)
theorem cpt_const (l:BitTape) :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun _:BitTape =>l) :=
  constList_polyTime l
theorem cpt_mulU :
    ComputableInPolyTime encodePair (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>mulU p.1 p.2) :=
  cptc mul_polyTime (fun _ =>rfl)
theorem cpt_unpairB1 :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s:BitTape =>(unpairB s).1) :=
  cptc (cpt_comp cpt_unpairB cpt_fst) (fun _ =>rfl)
theorem cpt_unpairB2 :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s:BitTape =>(unpairB s).2) :=
  cptc (cpt_comp cpt_unpairB cpt_snd) (fun _ =>rfl)
theorem cpt_app2 {u v:TapeMap}
    (hu:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) u)
    (hv:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) v) :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s =>u s ++ v s) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ =>rfl)
theorem cpt_pairB2 {u v:TapeMap}
    (hu:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) u)
    (hv:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) v) :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s =>pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ =>rfl)
theorem cpt_mulU2 {u v:TapeMap}
    (hu:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) u)
    (hv:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) v) :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s =>mulU (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) cpt_mulU) (fun _ =>rfl)
theorem cpt_sel {f a b:TapeMap}
    (hf:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) f)
    (ha:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) a)
    (hb:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) b) :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s =>sel (f s) (a s) (b s)):= by
  have h1:= cpt_comp (cpt_pair hf ha) cpt_ifEmpty
  have h2:= cpt_comp (cpt_pair hf hb) cpt_ifNonempty
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h:f s=[] <;> simp [sel,h]
theorem cpt_iterLen {g cnt arg:TapeMap}
    (hg:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) g)
    (hgl:∀ s,(g s).length≤ s.length)
    (hcnt:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) cnt)
    (harg:ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x) arg) :
    ComputableInPolyTime (fun x:BitTape =>x) (fun x:BitTape =>x)
      (fun s =>g^[(cnt s).length] (arg s)):= by
  obtain ⟨c⟩:= hg
  have hI:ComputableInPolyTime encodePair (fun x:BitTape =>x)
      (fun p:BitTape × BitTape =>g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y => by simpa using hgl y)
  exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _ =>rfl)
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptE_mini {f f':TapeMap} (h:Lib.CPTs f) (e:∀ a,f a=f' a):Lib.CPTs f':= by
  obtain rfl:f=f':= funext e; exact h
theorem cpt_hd1 {f:TapeMap} (hf:Lib.CPTs f):Lib.CPTs (fun y =>hd (f y)) :=
  cpt_comp hf cpt_hd
theorem cpt_tail1 {f:TapeMap} (hf:Lib.CPTs f):Lib.CPTs (fun y =>(f y).tail) :=
  cpt_comp hf cpt_tail
theorem cpt_unpairB1_1 {f:TapeMap} (hf:Lib.CPTs f) :
    Lib.CPTs (fun y =>(unpairB (f y)).1):= cpt_comp (g:= fun s =>(unpairB s).1) hf cpt_unpairB1
theorem cpt_unpairB2_1 {f:TapeMap} (hf:Lib.CPTs f) :
    Lib.CPTs (fun y =>(unpairB (f y)).2):= cpt_comp (g:= fun s =>(unpairB s).2) hf cpt_unpairB2
theorem cpt_cons1 (b:Bool) {f:TapeMap} (hf:Lib.CPTs f) :
    Lib.CPTs (fun y =>b :: f y) :=
  cptE_mini (cpt_app2 (cpt_const [b]) hf) (fun _ =>rfl)
end Lib.Universal
end
section
namespace Lib.Loop
open PEqualNP.Library Lib.Machines Lib.Universal
theorem cptE {f f':TapeMap} (h:Lib.CPTs f) (e:∀ a,f a=f' a) :
    Lib.CPTs f':= by
  obtain rfl:f=f':= funext e
  exact h
theorem cpt_iterMeasure {g cnt arg:TapeMap} (hg:Lib.CPTs g)
    (m:BitTape→ ℕ) (a:ℕ) (hm:∀ y,m (g y)≤ m y)
    (hgl:∀ y,(g y).length≤ y.length+m y) (ha:∀ y,m y≤ a * y.length+a)
    (hcnt:Lib.CPTs cnt) (harg:Lib.CPTs arg) :
    Lib.CPTs (fun s =>g^[(cnt s).length] (arg s)):= by
  obtain ⟨c⟩:= hg
  exact cptE (cpt_comp (cpt_pair harg hcnt) (Iter.iter_polyTime_measure g c m a hm hgl ha))
    (fun _ =>rfl)
def tk (p w:BitTape):BitTape:= (unpairB (mulU p [true] ++ false :: w)).1
theorem tk_eq (p w:BitTape):tk p w=w.take p.length:= by
  have h1:(mulU p [true] ++ false :: w).takeWhile id=un p.length:= by
    simp [mulU,un]
  have h2:(mulU p [true] ++ false :: w).dropWhile id=false :: w:= by
    simp [mulU,un]
  simp [tk,unpairB,h1,h2,un]
theorem tk_length (p w:BitTape):(tk p w).length≤ p.length:= by
  rw [tk_eq,List.length_take]
  exact Nat.min_le_left _ _
theorem cpt_tk {p w:TapeMap} (hp:Lib.CPTs p) (hw:Lib.CPTs w) :
    Lib.CPTs (fun s =>tk (p s) (w s)) :=
  cpt_unpairB1_1 (cpt_app2 (cpt_mulU2 hp (cpt_const [true])) (cpt_cons1 false hw))
def lstep (f:TapeMap) (y:BitTape):BitTape :=
  pairB (unpairB y).1 (pairB (unpairB (unpairB y).2).1.tail
    (pairB (unpairB (unpairB (unpairB y).2).2).1
      (tk (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
        (unpairB (unpairB (unpairB y).2).2).1)) ++ (unpairB (unpairB (unpairB y).2).2).2)))
theorem cpt_lstep {f:TapeMap} (hf:Lib.CPTs f):Lib.CPTs (lstep f):= by
  have h1:Lib.CPTs (fun y =>(unpairB y).1):= cpt_unpairB1
  have h2:Lib.CPTs (fun y =>(unpairB y).2):= cpt_unpairB2
  have hr:= cpt_tail1 (cpt_unpairB1_1 h2)
  have h3:= cpt_unpairB2_1 h2
  have harg:= cpt_unpairB1_1 h3
  have hacc:= cpt_unpairB2_1 h3
  exact cpt_pairB2 h1 (cpt_pairB2 hr (cpt_pairB2 harg
    (cpt_app2 (cpt_tk h1 (cpt_comp (cpt_pairB2 hr harg) hf)) hacc)))
theorem lstep_pairB (f:TapeMap) (pad r arg acc:BitTape) :
    lstep f (pairB pad (pairB r (pairB arg acc))) =
      pairB pad (pairB r.tail (pairB arg (tk pad (f (pairB r.tail arg)) ++ acc))):= by
  simp only [lstep,unpairB_pairB]
theorem lstep_measure (f:TapeMap) (y:BitTape) :
    (unpairB (lstep f y)).1.length+3≤ (unpairB y).1.length+3:= by
  simp only [lstep,unpairB_pairB]
  exact le_rfl
theorem lstep_length (f:TapeMap) (y:BitTape) :
    (lstep f y).length≤ y.length+((unpairB y).1.length+3):= by
  have h1:= unpairB_length y
  have h2:= unpairB_length (unpairB y).2
  have h3:= unpairB_length (unpairB (unpairB y).2).2
  have h4:= tk_length (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
        (unpairB (unpairB (unpairB y).2).2).1))
  have h5:(unpairB (unpairB y).2).1.tail.length≤ (unpairB (unpairB y).2).1.length:= by
    simp
  simp only [lstep,pairB_length,len_app]
  omega
theorem lstep_iter (f:TapeMap) (pad arg:BitTape) (n:ℕ)
    (hpad:∀ i< n,(f (pairB (un i) arg)).length≤ pad.length) (acc:BitTape) :
    (lstep f)^[n] (pairB pad (pairB (un n) (pairB arg acc))) =
      pairB pad (pairB [] (pairB arg
        ((List.range n).flatMap (fun i =>f (pairB (un i) arg)) ++ acc))):= by
  induction n generalizing acc with
  | zero =>simp
  | succ n ih =>
    rw [iter_succ,lstep_pairB,un_succ,List.tail_cons,tk_eq,
      List.take_of_length_le (hpad n (by omega)),ih (fun i hi =>hpad i (by omega)),
      List.range_succ,List.flatMap_append]
    simp
theorem cpt_flatMapRange {f cnt arg:TapeMap} (hf:Lib.CPTs f) (hcnt:Lib.CPTs cnt)
    (harg:Lib.CPTs arg) :
    Lib.CPTs (fun s =>(List.range (cnt s).length).flatMap fun i =>f (pairB (un i) (arg s))):= by
  obtain ⟨P,hP⟩:= output_length_poly f hf
  have hpad:Lib.CPTs (fun s =>List.replicate (P.eval (pairB (cnt s) (arg s)).length) true) :=
    cpt_comp (cpt_pairB2 hcnt harg) (Lib.L055 P)
  have hun:Lib.CPTs (fun s =>mulU (cnt s) [true]):= cpt_mulU2 hcnt (cpt_const [true])
  have hinit:= cpt_pairB2 hpad (cpt_pairB2 hun (cpt_pairB2 harg (cpt_const [])))
  have hit:= cpt_iterMeasure (cpt_lstep hf) (fun y =>(unpairB y).1.length+3) 3
    (lstep_measure f) (lstep_length f)
    (fun y => by have:= unpairB_length y; omega) hcnt hinit
  have hout:= cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hit))
  refine cptE hout (fun s =>?_)
  have e:mulU (cnt s) [true]=un (cnt s).length:= by simp [mulU]
  have hb:∀ i< (cnt s).length,(f (pairB (un i) (arg s))).length ≤
      (List.replicate (P.eval (pairB (cnt s) (arg s)).length) true).length:= by
    intro i hi
    rw [len_rep]
    refine (hP _).trans (eval_mono P ?_)
    rw [pairB_length,pairB_length,un_length]
    omega
  show (unpairB (unpairB (unpairB ((lstep f)^[(cnt s).length]
    (pairB _ (pairB (mulU (cnt s) [true]) (pairB (arg s) []))))).2).2).2=_
  rw [e,lstep_iter f _ (arg s) (cnt s).length hb,unpairB_pairB,unpairB_pairB,unpairB_pairB]
  simp
end Lib.Loop
end
end PT
namespace PT
namespace Lib.R
open PEqualNP.Library Lib.Machines Lib.Universal Lib.Loop
def encV (v:NVec):BitTape:= v.flatMap (fun a =>false :: un a)
def dbl (w:BitTape):BitTape:= w.flatMap (fun b =>[true,b])
def encLL (S:NMat):BitTape:= S.flatMap (fun v =>false :: dbl (encV v))
def dsl_dv:BitTape→ ℕ × NVec
  | [] =>(0,[])
  | true :: r =>((dsl_dv r).1+1,(dsl_dv r).2)
  | false :: r =>(0,(dsl_dv r).1 :: (dsl_dv r).2)
def decV (w:BitTape):NVec:= (dsl_dv w).2
def dr:BitTape→ BitTape × List (BitTape)
  | [] =>([],[])
  | false :: r =>(([]:BitTape),(dr r).1 :: (dr r).2)
  | true :: b :: r =>(b :: (dr r).1,(dr r).2)
  | [true] =>([],[])
def decLL (w:BitTape):NMat:= (dr w).2.map decV
@[local simp] theorem dsl_eV0:encV []=[]:= rfl
@[local simp] theorem dsl_eV1 (a:ℕ) (v:NVec):encV (a :: v)=false :: (un a ++ encV v):= rfl
@[local simp] theorem dsl_eVa (v w:NVec):encV (v ++ w)=encV v ++ encV w:= by simp [encV]
@[local simp] theorem dsl_db0:dbl []=[]:= rfl
@[local simp] theorem dsl_db1 (b:Bool) (w:BitTape):dbl (b :: w)=true :: b :: dbl w:= rfl
@[local simp] theorem dsl_eL0:encLL []=[]:= rfl
@[local simp] theorem dsl_eL1 (v:NVec) (S:NMat) :
    encLL (v :: S)=false :: (dbl (encV v) ++ encLL S):= rfl
@[local simp] theorem dsl_eLa (S T:NMat):encLL (S ++ T)=encLL S ++ encLL T:= by
  simp [encLL]
theorem dsl_dvu (a:ℕ) (w:BitTape):dsl_dv (un a ++ w)=((dsl_dv w).1+a,(dsl_dv w).2):= by
  induction a with
  | zero =>rfl
  | succ a ih =>simp only [un_succ,List.cons_append,dsl_dv,ih,Nat.add_assoc]
theorem decV_encV (v:NVec):decV (encV v)=v:= by
  have:∀ v,dsl_dv (encV v)=(0,v):= by
    intro v; induction v with
    | nil =>rfl
    | cons a v ih =>simp [dsl_dv,dsl_dvu,ih]
  simp [decV,this]
theorem dsl_dvi (w:BitTape):un (dsl_dv w).1 ++ encV (dsl_dv w).2=w:= by
  induction w with
  | nil =>rfl
  | cons b w ih =>cases b <;> simp [dsl_dv,un_succ,ih]
theorem dsl_ed (w:BitTape):encV (decV w)=w.dropWhile id:= by
  induction w with
  | nil =>rfl
  | cons b w ih =>
    cases b
    · simpa [decV,dsl_dv] using dsl_dvi w
    · simpa [decV,dsl_dv] using ih
theorem dsl_drd (x w:BitTape):dr (dbl x ++ w)=(x ++ (dr w).1,(dr w).2):= by
  induction x with
  | nil =>rfl
  | cons b x ih =>simp [dr,ih]
theorem decLL_encLL (S:NMat):decLL (encLL S)=S:= by
  have:∀ S,dr (encLL S)=([],S.map encV):= by
    intro S; induction S with
    | nil =>rfl
    | cons v S ih =>simp [dr,dsl_drd,ih]
  simp [decLL,this,Function.comp_def,decV_encV]
def NatR (f:BitTape→ ℕ):Prop:= Lib.CPTs (fun s =>un (f s))
def VecR (f:BitTape→ NVec):Prop:= Lib.CPTs (fun s =>encV (f s))
def LLR (f:BitTape→ NMat):Prop:= Lib.CPTs (fun s =>encLL (f s))
theorem dsl_T {Q:Type} [Fintype Q] (δ:Q→ Bool→ Q × Option Bool) (fin:Q→ Option Bool)
    (q:Q):Lib.CPTs (fstRun δ fin q):= fst_polyTime _ _ _ δ fin q (fun _ =>rfl)
theorem dsl_T2 {Q:Type} [Fintype Q] (δ:Q→ Bool→ Q × Option Bool × Option Bool)
    (fin:Q→ Option Bool) (q:Q):Lib.CPTs (fstRun2 δ fin q) :=
  fst2_polyTime _ _ _ δ fin q (fun _ =>rfl)
theorem dsl_fm (φ:Bool→ Option Bool):Lib.CPTs (fun w =>w.filterMap φ) :=
  cptE (dsl_T (fun (_:Unit) b =>((),φ b)) (fun _ =>none) ()) (fun w => by
    induction w with
    | nil =>rfl
    | cons b l ih =>simp only [fstRun]; rw [ih]; cases h:φ b <;> simp [h])
theorem dsl_fl {Q:Type} (δ:Q→ Bool→ Q × Option Bool) (q:Q) (l:BitTape) :
    (fstRun δ (fun _ =>none) q l).length≤ l.length:= by
  induction l generalizing q with
  | nil =>simp [fstRun]
  | cons a l ih =>
    simp only [fstRun,len_app,len_cons]
    have:= ih (δ q a).1
    cases (δ q a).2 <;> simp <;> omega
theorem dsl_skip {Q:Type} (δ:Q→ Bool→ Q × Option Bool) (fin:Q→ Option Bool) (q q':Q)
    (h1:δ q true=(q',none)) (h2:∀ b,δ q' b=(q,none)) (x y:BitTape) :
    fstRun δ fin q (dbl x ++ y)=fstRun δ fin q y:= by
  induction x with
  | nil =>rfl
  | cons b x ih =>simp only [dsl_db1,List.cons_append,fstRun,h1,h2]; simpa using ih
theorem dsl_cdbl:Lib.CPTs dbl :=
  cptE (dsl_T2 (fun (_:Unit) b =>((),some true,some b)) (fun _ =>none) ()) (fun w => by
    induction w with
    | nil =>rfl
    | cons b l ih =>simp only [fstRun2]; rw [ih]; rfl)
def dsl_dwD:Bool→ Bool→ Bool × Option Bool
  | false,true =>(false,none)
  | false,false =>(true,some false)
  | true,b =>(true,some b)
theorem dsl_cdw:Lib.CPTs (fun l =>l.dropWhile id):= by
  have ht:∀ l,fstRun dsl_dwD (fun _ =>none) true l=l:= by
    intro l; induction l with
    | nil =>rfl
    | cons b l ih =>simp [fstRun,dsl_dwD,ih]
  refine cptE (dsl_T dsl_dwD (fun _ =>none) false) (fun l =>?_)
  induction l with
  | nil =>rfl
  | cons b l ih =>cases b <;> simp [fstRun,dsl_dwD,ih,ht]
theorem dsl_up (x:ℕ) (w:BitTape):unpairB (un x ++ false :: w)=(w.take x,w.drop x):= by
  have h1:(un x ++ false :: w).takeWhile id=un x:= by simp [un]
  have h2:(un x ++ false :: w).dropWhile id=false :: w:= by simp [un]
  simp [unpairB,h1,h2]
theorem dsl_tw (l:BitTape):hd l=un (l.takeWhile id).length :=
  List.eq_replicate_iff.2 ⟨rfl,fun b hb => by simpa using List.mem_takeWhile_imp hb⟩
theorem dsl_hg {α:Type} (l:List α) (i:ℕ) (d:α):(l.drop i).headD d=l.getD i d:= by
  induction l generalizing i with
  | nil =>simp
  | cons a l ih =>cases i <;> simp
theorem dsl_itT {α:Type} (E:List α→ BitTape) (f:TapeMap)
    (hf:∀ S,f (E S)=E S.tail) (n:ℕ) (S:List α):f^[n] (E S)=E (S.drop n):= by
  induction n generalizing S with
  | zero =>rfl
  | succ n ih =>rw [iter_succ,hf,ih,List.drop_tail]
def dsl_G (g:TapeMap) (y:BitTape):BitTape :=
  pairB (unpairB y).1 (tk (unpairB y).1 (g (unpairB y).2))
theorem dsl_G1 (g:TapeMap) (y:BitTape) :
    (unpairB (dsl_G g y)).1.length+1≤ (unpairB y).1.length+1:= by
  simp [dsl_G,unpairB_pairB]
theorem dsl_G2 (g:TapeMap) (y:BitTape) :
    (dsl_G g y).length≤ y.length+((unpairB y).1.length+1):= by
  have h1:= unpairB_length y
  have h2:= tk_length (unpairB y).1 (g (unpairB y).2)
  simp only [dsl_G,pairB_length]; omega
theorem dsl_G3 (y:BitTape):(unpairB y).1.length+1≤ 1 * y.length+1:= by
  have:= unpairB_length y; omega
theorem dsl_Git (g:TapeMap) (pad y:BitTape) (n:ℕ)
    (h:∀ i≤ n,(g^[i] y).length≤ pad.length) :
    (dsl_G g)^[n] (pairB pad y)=pairB pad (g^[n] y):= by
  induction n with
  | zero =>rfl
  | succ n ih =>
    rw [iter_succ' (dsl_G g),ih (fun i hi =>h i (by omega)),
      iter_succ' g]
    simp only [dsl_G,unpairB_pairB,tk_eq]
    have:= h (n+1) le_rfl
    rw [iter_succ'] at this
    rw [List.take_of_length_le this]
theorem dsl_iterBound {g cnt arg:TapeMap} (hg:Lib.CPTs g) (hcnt:Lib.CPTs cnt)
    (harg:Lib.CPTs arg) (P:Polynomial ℕ)
    (hb:∀ s,∀ i≤ (cnt s).length,(g^[i] (arg s)).length≤ P.eval s.length) :
    Lib.CPTs (fun s =>g^[(cnt s).length] (arg s)):= by
  have hG:Lib.CPTs (dsl_G g) :=
    cpt_pairB2 cpt_unpairB1 (cpt_tk cpt_unpairB1 (cpt_comp cpt_unpairB2 hg))
  have hit:= cpt_iterMeasure hG (fun y =>(unpairB y).1.length+1) 1 (dsl_G1 g) (dsl_G2 g) dsl_G3
    hcnt (cpt_pairB2 (Lib.L055 P) harg)
  exact cptE (cpt_unpairB2_1 hit) (fun s => by
    rw [dsl_Git g _ _ _ (fun i hi => by simpa using hb s i hi),unpairB_pairB])
theorem dsl_iterR {F init cnt:TapeMap} (hF:Lib.CPTs F) (hi:Lib.CPTs init)
    (hc:Lib.CPTs cnt) (P:Polynomial ℕ)
    (hb:∀ s,∀ i≤ (cnt s).length,
      ((fun a =>F (pairB a s))^[i] (init s)).length≤ P.eval s.length) :
    Lib.CPTs (fun s =>(fun a =>F (pairB a s))^[(cnt s).length] (init s)):= by
  have e:∀ s i a,(fun y =>pairB (F y) (unpairB y).2)^[i] (pairB a s) =
      pairB ((fun a =>F (pairB a s))^[i] a) s:= by
    intro s i; induction i with
    | zero =>intro a; rfl
    | succ i ih =>intro a; simp only [iter_succ,unpairB_pairB,ih]
  have h:= dsl_iterBound (cpt_pairB2 hF cpt_unpairB2) hc (cpt_pairB2 hi cpt_id)
    (Polynomial.C 2 * P+Polynomial.X+Polynomial.C 1) (fun s i hi => by
      rw [e,pairB_length]; have:= hb s i hi
      simp only [evalAddP,evalMulP,evalCP,evalXP]
      omega)
  exact cptE (cpt_unpairB1_1 h) (fun s => by rw [e,unpairB_pairB])
theorem dsl_itU (F:TapeMap) (φ:ℕ→ ℕ) (s:BitTape)
    (hF:∀ x,F (pairB (un x) s)=un (φ x)) :
    ∀ i x,(fun a =>F (pairB a s))^[i] (un x)=un (φ^[i] x):= by
  intro i; induction i with
  | zero =>intro x; rfl
  | succ i ih =>intro x; simp only [iter_succ,hF,ih]
theorem dsl_loopN {φ:BitTape→ ℕ→ ℕ} {x0 n:BitTape→ ℕ}
    (hφ:NatR (fun t =>φ (unpairB t).2 (unpairB t).1.length)) (hx:NatR x0) (hn:NatR n)
    (P:Polynomial ℕ) (hb:∀ s,∀ i≤ n s,(φ s)^[i] (x0 s)≤ P.eval s.length) :
    NatR (fun s =>(φ s)^[n s] (x0 s)):= by
  have e:∀ s i x,(fun a =>un (φ (unpairB (pairB a s)).2 (unpairB (pairB a s)).1.length))^[i]
      (un x)=un ((φ s)^[i] x):= fun s =>
    dsl_itU (fun t =>un (φ (unpairB t).2 (unpairB t).1.length)) (φ s) s
      (fun x => by simp only [unpairB_pairB,un_length])
  have h:= dsl_iterR (F:= fun t =>un (φ (unpairB t).2 (unpairB t).1.length))
    (init:= fun s =>un (x0 s)) (cnt:= fun s =>un (n s)) hφ hx hn P
    (fun s i hi => by rw [e,un_length]; exact hb s i (by simpa using hi))
  exact cptE h (fun s => by rw [un_length,e])
theorem dsl_cle (C:ℕ→ Prop) [DecidablePred C] (i:ℕ) :
    (fun q =>if C q then q else q+1)^[i] 0≤ i:= by
  induction i with
  | zero =>exact le_rfl
  | succ i ih =>rw [iter_succ']; split_ifs <;> omega
theorem dsl_cnt (C:ℕ→ Prop) [DecidablePred C] (m:ℕ) (hC:∀ q,C q ↔ m< q+1) (i:ℕ) :
    (fun q =>if C q then q else q+1)^[i] 0=min i m:= by
  induction i with
  | zero =>simp
  | succ i ih =>
    rw [iter_succ',ih]
    split_ifs with h
    · have:= (hC _).1 h; omega
    · have:= mt (hC _).2 h; omega
theorem dsl_le {a:BitTape→ ℕ} (ha:NatR a):∃ P:Polynomial ℕ,∀ s,a s≤ P.eval s.length:= by
  obtain ⟨P,hP⟩:= output_length_poly _ ha
  exact ⟨P,fun s => by simpa using hP s⟩
theorem dsl_sel (n:ℕ) (x y:BitTape):sel (un n) x y=if n=0 then x else y:= by
  cases n <;> simp [sel,un]
theorem natR_const (k:ℕ):NatR (fun _ =>k):= cpt_const (un k)
theorem natR_len {p:TapeMap} (hp:Lib.CPTs p):NatR (fun s =>(p s).length) :=
  cptE (cpt_mulU2 hp (cpt_const [true])) (fun s => by simp [mulU])
theorem natR_add {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b):NatR (fun s =>a s+b s) :=
  cptE (cpt_app2 ha hb) (fun s => by simp only [un,List.replicate_add])
theorem natR_sub {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b):NatR (fun s =>a s - b s) :=
  cptE (cpt_unpairB2_1 (cpt_app2 hb (cpt_cons1 false ha))) (fun s => by
    rw [dsl_up]; simp [un])
theorem natR_mul {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b):NatR (fun s =>a s * b s) :=
  cptE (cpt_mulU2 ha hb) (fun s => by simp [mulU])
theorem dsl_cil {a b:BitTape→ ℕ} {x y:TapeMap} (ha:NatR a) (hb:NatR b)
    (hx:Lib.CPTs x) (hy:Lib.CPTs y):Lib.CPTs (fun s =>if a s< b s then x s else y s) :=
  cptE (cpt_sel (natR_sub hb ha) hy hx) (fun s => by
    dsimp only; rw [dsl_sel]; by_cases h:a s< b s
    · simp only [h,↓reduceIte,show ¬ b s - a s=0 by omega,↓reduceIte]
    · simp only [h,↓reduceIte,show b s - a s=0 by omega,↓reduceIte])
theorem dsl_cie {a b:BitTape→ ℕ} {x y:TapeMap} (ha:NatR a) (hb:NatR b)
    (hx:Lib.CPTs x) (hy:Lib.CPTs y):Lib.CPTs (fun s =>if a s=b s then x s else y s) :=
  cptE (cpt_sel (natR_add (natR_sub ha hb) (natR_sub hb ha)) hx hy) (fun s => by
    dsimp only; rw [dsl_sel]; by_cases h:a s=b s
    · simp only [h,↓reduceIte,show b s - b s+(b s - b s)=0 by omega]
    · simp only [h,↓reduceIte,show ¬ a s - b s+(b s - a s)=0 by omega])
theorem dsl_nlt {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if a s< b s then x s else y s) :=
  cptE (dsl_cil ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
theorem dsl_neq {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if a s=b s then x s else y s) :=
  cptE (dsl_cie ha hb hx hy) (fun s => by dsimp only; split_ifs <;> rfl)
theorem dsl_L1:NatR (fun t =>(unpairB t).1.length):= natR_len cpt_unpairB1
theorem dsl_nc2 {a:BitTape→ ℕ} (ha:NatR a):NatR (fun t =>a (unpairB t).2):= by
  unfold NatR at *
  exact cpt_comp (f:= fun t =>(unpairB t).2) (g:= fun s =>un (a s)) cpt_unpairB2 ha
theorem natR_div {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b):NatR (fun s =>a s / b s):= by
  obtain ⟨P,hP⟩:= dsl_le ha
  have hφ:= dsl_nlt (dsl_nc2 ha) (natR_mul (natR_add dsl_L1 (natR_const 1)) (dsl_nc2 hb)) dsl_L1
    (natR_add dsl_L1 (natR_const 1))
  have h:= dsl_loopN (φ:= fun s q =>if a s< (q+1) * b s then q else q+1) hφ
    (natR_const 0) ha P (fun s i hi =>(dsl_cle _ i).trans (hi.trans (hP s)))
  refine cptE (dsl_neq hb (natR_const 0) (natR_const 0) h) (fun s =>?_)
  dsimp only
  by_cases h0:b s=0
  · simp [h0]
  · simp only [h0,↓reduceIte]
    rw [dsl_cnt (fun q =>a s< (q+1) * b s) (a s / b s)
      (fun q =>(Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero h0)).symm) (a s),
      min_eq_right (Nat.div_le_self _ _)]
theorem natR_mod {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b):NatR (fun s =>a s % b s) :=
  cptE (natR_sub ha (natR_mul hb (natR_div ha hb))) (fun s => by dsimp only; rw [Nat.mod_eq_sub_mul_div])
theorem dsl_half (i x:ℕ):(fun x =>x / 2)^[i] x=x / 2 ^ i:= by
  induction i generalizing x with
  | zero =>simp
  | succ i ih =>rw [iter_succ,ih,Nat.div_div_eq_div_mul,pow_succ']
theorem dsl_halfN {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) :
    NatR (fun s =>a s / 2 ^ b s):= by
  obtain ⟨P,hP⟩:= dsl_le ha
  have h:= dsl_loopN (φ:= fun _ x =>x / 2) (natR_div dsl_L1 (natR_const 2)) ha hb P
    (fun s i _ => by rw [dsl_half]; exact (Nat.div_le_self _ _).trans (hP s))
  exact cptE h (fun s => by dsimp only; rw [dsl_half])
theorem natR_log2 {a:BitTape→ ℕ} (ha:NatR a):NatR (fun s =>(a s).log2):= by
  obtain ⟨P,hP⟩:= dsl_le ha
  have hφ:= dsl_nlt (dsl_halfN (dsl_nc2 ha) (natR_add dsl_L1 (natR_const 1))) (natR_const 1)
    dsl_L1 (natR_add dsl_L1 (natR_const 1))
  have h:= dsl_loopN (φ:= fun s q =>if a s / 2 ^ (q+1)< 1 then q else q+1) hφ
    (natR_const 0) ha P (fun s i hi =>(dsl_cle _ i).trans (hi.trans (hP s)))
  refine cptE h (fun s =>?_)
  dsimp only
  rw [dsl_cnt (fun q =>a s / 2 ^ (q+1)< 1) (a s).log2 (fun q =>?_) (a s),
    min_eq_right (Nat.log2_le_self _)]
  rcases Nat.eq_zero_or_pos (a s) with h0 | h0
  · simp [h0]
  · rw [Nat.div_lt_iff_lt_mul (by positivity),one_mul,Nat.log2_lt h0.ne']
theorem natR_testBit {a b:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) :
    NatR (fun s =>if (a s).testBit (b s) then 1 else 0) :=
  cptE (natR_mod (dsl_halfN ha hb) (natR_const 2)) (fun s => by
    dsimp only; rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (a s / 2 ^ b s) with h | h <;> simp [h])
theorem dsl_pm (A C i:ℕ):(fun x =>x * A % C)^[i] (1 % C)=A ^ i % C:= by
  induction i with
  | zero =>simp
  | succ i ih =>rw [iter_succ',ih,pow_succ,Nat.mod_mul_mod]
theorem natR_powmod {a b c:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hc:NatR c)
    (hc0:∀ s,0< c s):NatR (fun s =>a s ^ b s % c s):= by
  obtain ⟨P,hP⟩:= dsl_le hc
  have h:= dsl_loopN (φ:= fun s x =>x * a s % c s)
    (natR_mod (natR_mul dsl_L1 (dsl_nc2 ha)) (dsl_nc2 hc)) (natR_mod (natR_const 1) hc) hb P
    (fun s i _ => by rw [dsl_pm]; exact (Nat.mod_lt _ (hc0 s)).le.trans (hP s))
  exact cptE h (fun s => by dsimp only; rw [dsl_pm])
theorem dsl_powmodS {a b c:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hc:NatR c) :
    NatR (fun s =>a s ^ b s % (c s+1)) :=
  natR_powmod ha hb (natR_add hc (natR_const 1)) (fun _ =>Nat.succ_pos _)
theorem dsl_p2 (i:ℕ):(fun x =>x+x)^[i] 1=2 ^ i:= by
  induction i with
  | zero =>rfl
  | succ i ih =>rw [iter_succ',ih,pow_succ]; omega
theorem natR_pow2 {b:BitTape→ ℕ} (hb:NatR b) (P:Polynomial ℕ)
    (hP:∀ s,2 ^ b s≤ P.eval s.length):NatR (fun s =>2 ^ b s):= by
  have h:= dsl_loopN (φ:= fun _ x =>x+x) (natR_add dsl_L1 dsl_L1) (natR_const 1) hb P
    (fun s i hi => by rw [dsl_p2]; exact (Nat.pow_le_pow_right (by norm_num) hi).trans (hP s))
  exact cptE h (fun s => by dsimp only; rw [dsl_p2])
theorem cpt_ite_lt {a b:BitTape→ ℕ} {x y:TapeMap} (ha:NatR a) (hb:NatR b)
    (hx:Lib.CPTs x) (hy:Lib.CPTs y):Lib.CPTs (fun s =>if a s< b s then x s else y s) :=
  dsl_cil ha hb hx hy
theorem cpt_ite_eq {a b:BitTape→ ℕ} {x y:TapeMap} (ha:NatR a) (hb:NatR b)
    (hx:Lib.CPTs x) (hy:Lib.CPTs y):Lib.CPTs (fun s =>if a s=b s then x s else y s) :=
  dsl_cie ha hb hx hy
theorem natR_bit {p:TapeMap} {k:BitTape→ ℕ} (hp:Lib.CPTs p) (hk:NatR k) :
    NatR (fun s =>if (p s).getD (k s) false then 1 else 0):= by
  have h:= cpt_comp (cpt_tk (cpt_const [true]) (cpt_unpairB2_1 (cpt_app2 hk (cpt_cons1 false hp))))
    (dsl_fm (fun b =>if b then some true else none))
  refine cptE h (fun s =>?_)
  simp only [tk_eq,dsl_up,len_one]
  rw [getDOpt,← List.head?_drop]
  rcases (p s).drop (k s) with _ | ⟨_ | _,l⟩ <;> simp [un]
theorem natR_runAt {p:TapeMap} {k:BitTape→ ℕ} (hp:Lib.CPTs p) (hk:NatR k) :
    NatR (fun s =>(((p s).drop (k s)).takeWhile id).length) :=
  cptE (cpt_hd1 (cpt_unpairB2_1 (cpt_app2 hk (cpt_cons1 false hp)))) (fun s => by
    rw [dsl_up]; exact dsl_tw _)
theorem vecR_dec {p:TapeMap} (hp:Lib.CPTs p):VecR (fun s =>decV (p s)) :=
  cptE (cpt_comp hp dsl_cdw) (fun _ =>(dsl_ed _).symm)
theorem vecR_nil:VecR (fun _ =>[]):= cpt_const []
theorem vecR_single {a:BitTape→ ℕ} (ha:NatR a):VecR (fun s =>[a s]) :=
  cptE (cpt_cons1 false ha) (fun s => by simp)
theorem vecR_append {v w:BitTape→ NVec} (hv:VecR v) (hw:VecR w) :
    VecR (fun s =>v s ++ w s) :=
  cptE (cpt_app2 hv hw) (fun s => by simp)
theorem dsl_dwu (a:ℕ) (w:BitTape):(un a ++ w).dropWhile id=w.dropWhile id:= by
  induction a with
  | zero =>rfl
  | succ a ih =>simpa [un_succ] using ih
theorem dsl_twV (v:NVec):(encV v).takeWhile id=[]:= by cases v <;> rfl
theorem dsl_stV (v:NVec):((encV v).tail).dropWhile id=encV v.tail:= by
  cases v with
  | nil =>rfl
  | cons a v =>simp only [dsl_eV1,List.tail_cons,dsl_dwu]; cases v <;> rfl
theorem dsl_hdV (w:NVec):hd (encV w).tail=un (w.headD 0):= by
  cases w with
  | nil =>rfl
  | cons a w =>
    simp only [dsl_eV1,List.tail_cons,hd,List.headD_cons]
    rw [List.takeWhile_append_of_pos (by simp [un]),dsl_twV,List.append_nil]
theorem natR_get {v:BitTape→ NVec} {i:BitTape→ ℕ} (hv:VecR v) (hi:NatR i) :
    NatR (fun s =>(v s).getD (i s) 0):= by
  have h:= cpt_iterLen (g:= fun y =>(y.tail).dropWhile id) (cpt_comp cpt_tail dsl_cdw)
    (fun y =>(List.IsSuffix.length_le (List.dropWhile_suffix (l:= y.tail) id)).trans (by simp))
    hi hv
  exact cptE (cpt_hd1 (cpt_tail1 h)) (fun s => by
    rw [un_length,dsl_itT encV (fun y =>(y.tail).dropWhile id) dsl_stV,dsl_hdV,dsl_hg])
theorem natR_vlen {v:BitTape→ NVec} (hv:VecR v):NatR (fun s =>(v s).length):= by
  have e:∀ v:NVec,(encV v).filterMap (fun b =>if b then none else some true)=un v.length:= by
    intro v; induction v with
    | nil =>rfl
    | cons a v ih =>
      simp only [dsl_eV1,List.filterMap_cons,List.filterMap_append,ih]
      simp [un,List.filterMap_replicate_of_none,List.replicate_succ]
  exact cptE (cpt_comp hv (dsl_fm _)) (fun s =>e _)
theorem natR_sum {v:BitTape→ NVec} (hv:VecR v):NatR (fun s =>(v s).sum):= by
  have e:∀ v:NVec,(encV v).filterMap (fun b =>if b then some true else none)=un v.sum:= by
    intro v; induction v with
    | nil =>rfl
    | cons a v ih =>
      simp only [dsl_eV1,List.filterMap_cons,List.filterMap_append,ih]
      simp [un]
  exact cptE (cpt_comp hv (dsl_fm _)) (fun s =>e _)
theorem vecR_gen {A:TapeMap} {n:BitTape→ ℕ} {G:ℕ→ BitTape→ ℕ}
    (hA:Lib.CPTs A) (hn:NatR n) (hG:NatR (fun t =>G (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s =>(List.range (n s)).map (fun i =>G i (A s))) :=
  cptE (cpt_flatMapRange (cpt_cons1 false hG) hn hA) (fun s => by
    simp [encV,List.flatMap_map,unpairB_pairB])
theorem vecR_flat {A:TapeMap} {n:BitTape→ ℕ} {H:ℕ→ BitTape→ NVec}
    (hA:Lib.CPTs A) (hn:NatR n) (hH:VecR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s =>(List.range (n s)).flatMap (fun i =>H i (A s))) :=
  cptE (cpt_flatMapRange hH hn hA) (fun s => by simp [encV,List.flatMap_assoc,unpairB_pairB])
def dsl_bD:Bool→ Bool→ Bool × Option Bool
  | false,true =>(false,none)
  | false,false =>(true,none)
  | true,true =>(false,some true)
  | true,false =>(true,some false)
def dsl_bF (q:Bool):Option Bool:= if q then some false else none
theorem cpt_bitsOf {v:BitTape→ NVec} (hv:VecR v) :
    Lib.CPTs (fun s =>(v s).map (fun a =>decide (a ≠ 0))):= by
  have hu:∀ (a:ℕ) w,fstRun dsl_bD dsl_bF false (un a ++ w)=fstRun dsl_bD dsl_bF false w:= by
    intro a w; induction a with
    | zero =>rfl
    | succ a ih =>simpa [un_succ,fstRun,dsl_bD] using ih
  have e:∀ v:NVec,fstRun dsl_bD dsl_bF false (encV v)=v.map (fun a =>decide (a ≠ 0)) ∧
      fstRun dsl_bD dsl_bF true (encV v)=false :: v.map (fun a =>decide (a ≠ 0)):= by
    intro v; induction v with
    | nil =>exact ⟨rfl,rfl⟩
    | cons a v ih =>
      have key:fstRun dsl_bD dsl_bF true (un a ++ encV v) =
          decide (a ≠ 0) :: v.map (fun a =>decide (a ≠ 0)):= by
        cases a with
        | zero =>exact ih.2
        | succ a =>simp [un_succ,fstRun,dsl_bD,hu,ih.1]
      simp [fstRun,dsl_bD,key]
  exact cptE (cpt_comp hv (dsl_T dsl_bD dsl_bF false)) (fun s =>(e _).1)
def dsl_lD:Bool × Bool × Bool→ Bool→ (Bool × Bool × Bool) × Option Bool × Option Bool
  | (_,false,_),false =>((true,false,true),some false,none)
  | (r,false,d),true =>((r,true,d),none,none)
  | (false,true,_),_ =>((false,false,false),none,none)
  | (true,true,d),b =>
    if d && b then ((true,false,true),none,none) else ((true,false,false),some true,some b)
def dsl_rT (d:Bool) (x:BitTape):BitTape:= if d then x.dropWhile id else x
theorem dsl_lB (w:BitTape):∀ d,fstRun2 dsl_lD (fun _ =>none) (true,false,d) w =
    dbl (dsl_rT d (dr w).1) ++ encLL ((dr w).2.map decV):= by
  induction w using dr.induct with
  | case1 =>intro d; cases d <;> rfl
  | case2 r ih =>intro d; simp [fstRun2,dsl_lD,dr,ih,dsl_rT,dsl_ed]
  | case3 b r ih =>intro d; cases d <;> cases b <;> simp [fstRun2,dsl_lD,dr,ih,dsl_rT]
  | case4 =>intro d; cases d <;> rfl
theorem dsl_lA (w:BitTape):fstRun2 dsl_lD (fun _ =>none) (false,false,false) w =
    encLL (decLL w):= by
  induction w using dr.induct with
  | case1 =>rfl
  | case2 r ih =>simp [fstRun2,dsl_lD,dr,decLL,dsl_lB,dsl_rT,dsl_ed]
  | case3 b r ih =>simpa [fstRun2,dsl_lD,dr,decLL] using ih
  | case4 =>rfl
theorem llR_dec {p:TapeMap} (hp:Lib.CPTs p):LLR (fun s =>decLL (p s)) :=
  cptE (cpt_comp hp (dsl_T2 dsl_lD (fun _ =>none) (false,false,false))) (fun _ =>dsl_lA _)
theorem llR_nil:LLR (fun _ =>[]):= cpt_const []
theorem llR_single {v:BitTape→ NVec} (hv:VecR v):LLR (fun s =>[v s]) :=
  cptE (cpt_cons1 false (cpt_comp hv dsl_cdbl)) (fun s => by simp)
theorem llR_append {S T:BitTape→ NMat} (hS:LLR S) (hT:LLR T) :
    LLR (fun s =>S s ++ T s) :=
  cptE (cpt_app2 hS hT) (fun s => by simp)
def dsl_sD:Bool × Bool→ Bool→ (Bool × Bool) × Option Bool
  | (false,false),false =>((true,false),some false)
  | (false,false),true =>((false,true),none)
  | (false,true),_ =>((false,false),none)
  | (true,_),b =>((true,false),some b)
def dsl_xD:Bool × Bool→ Bool→ (Bool × Bool) × Option Bool
  | (false,false),false =>((true,false),none)
  | (false,false),true =>((false,true),none)
  | (false,true),b =>((false,false),some b)
  | (true,_),_ =>((true,false),none)
theorem dsl_rs (S:NMat) :
    fstRun dsl_sD (fun _ =>none) (false,false) (encLL S).tail=encLL S.tail:= by
  have hc:∀ x l,fstRun dsl_sD (fun _ =>none) (true,x) l=l:= by
    intro x l; induction l generalizing x with
    | nil =>rfl
    | cons b l ih =>simp [fstRun,dsl_sD,ih]
  cases S with
  | nil =>rfl
  | cons v S =>
    simp only [dsl_eL1,List.tail_cons]
    rw [dsl_skip dsl_sD _ (false,false) (false,true) rfl (fun _ =>rfl)]
    cases S with
    | nil =>rfl
    | cons w S =>simp [fstRun,dsl_sD,hc]
theorem dsl_xL (S:NMat) :
    fstRun dsl_xD (fun _ =>none) (false,false) (encLL S).tail=encV (S.headD []):= by
  have hd0:∀ x l,fstRun dsl_xD (fun _ =>none) (true,x) l=[]:= by
    intro x l; induction l generalizing x with
    | nil =>rfl
    | cons b l ih =>simp [fstRun,dsl_xD,ih]
  have hb:∀ x y,fstRun dsl_xD (fun _ =>none) (false,false) (dbl x ++ y) =
      x ++ fstRun dsl_xD (fun _ =>none) (false,false) y:= by
    intro x y; induction x with
    | nil =>rfl
    | cons b x ih =>simp [fstRun,dsl_xD,ih]
  cases S with
  | nil =>rfl
  | cons v S =>
    simp only [dsl_eL1,List.tail_cons,List.headD_cons]
    rw [hb]
    cases S with
    | nil =>simp [fstRun]
    | cons w S =>simp [fstRun,dsl_xD,hd0]
theorem vecR_row {S:BitTape→ NMat} {j:BitTape→ ℕ} (hS:LLR S) (hj:NatR j) :
    VecR (fun s =>(S s).getD (j s) []):= by
  have h:= cpt_iterLen (g:= fun y =>fstRun dsl_sD (fun _ =>none) (false,false) y.tail)
    (cpt_comp cpt_tail (dsl_T dsl_sD _ (false,false)))
    (fun y =>(dsl_fl _ _ _).trans (by simp)) hj hS
  exact cptE (cpt_comp (cpt_tail1 h) (dsl_T dsl_xD (fun _ =>none) (false,false))) (fun s => by
    rw [un_length,dsl_itT encLL (fun y =>fstRun dsl_sD (fun _ =>none) (false,false) y.tail)
      dsl_rs,dsl_xL,dsl_hg])
def dsl_cD:Bool→ Bool→ Bool × Option Bool
  | false,false =>(false,some true)
  | false,true =>(true,none)
  | true,_ =>(false,none)
theorem natR_llen {S:BitTape→ NMat} (hS:LLR S):NatR (fun s =>(S s).length):= by
  have e:∀ S:NMat,fstRun dsl_cD (fun _ =>none) false (encLL S)=un S.length:= by
    intro S; induction S with
    | nil =>rfl
    | cons v S ih =>
      simp only [dsl_eL1,fstRun,dsl_cD,Option.toList_some]
      rw [dsl_skip dsl_cD _ false true rfl (fun _ =>rfl),ih]; rfl
  exact cptE (cpt_comp hS (dsl_T dsl_cD _ false)) (fun s =>e _)
theorem llR_gen {A:TapeMap} {n:BitTape→ ℕ} {H:ℕ→ BitTape→ NVec}
    (hA:Lib.CPTs A) (hn:NatR n) (hH:VecR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s =>(List.range (n s)).map (fun i =>H i (A s))) :=
  cptE (cpt_flatMapRange (cpt_cons1 false (cpt_comp hH dsl_cdbl)) hn hA) (fun s => by
    simp [encLL,List.flatMap_map,unpairB_pairB])
theorem llR_flat {A:TapeMap} {n:BitTape→ ℕ} {H:ℕ→ BitTape→ NMat}
    (hA:Lib.CPTs A) (hn:NatR n) (hH:LLR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s =>(List.range (n s)).flatMap (fun i =>H i (A s))) :=
  cptE (cpt_flatMapRange hH hn hA) (fun s => by simp [encLL,List.flatMap_assoc,unpairB_pairB])
theorem cpt_iterBound {g cnt arg:TapeMap} (hg:Lib.CPTs g) (hcnt:Lib.CPTs cnt)
    (harg:Lib.CPTs arg) (P:Polynomial ℕ)
    (hb:∀ s,∀ i≤ (cnt s).length,(g^[i] (arg s)).length≤ P.eval s.length) :
    Lib.CPTs (fun s =>g^[(cnt s).length] (arg s)):= dsl_iterBound hg hcnt harg P hb
theorem encV_length (v:NVec):(encV v).length=v.length+v.sum:= by
  induction v with
  | nil =>rfl
  | cons a v ih =>simp [ih]; omega
theorem natR_le_poly {a:BitTape→ ℕ} (ha:NatR a):∃ P:Polynomial ℕ,∀ s,a s≤ P.eval s.length :=
  dsl_le ha
end Lib.R
end PT
namespace PT
namespace Lib.Fast
open PEqualNP.Library
def q22 {K:Type} {Γ:K→ Type} {Λ σ:Type}:Turing.TM2.Stmt Γ Λ σ→ Set (Σ k,Γ k)
  | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,Γ k)) ∪ q22 q
  | .peek _ _ q=>q22 q
  | .pop _ _ q=>q22 q
  | .load _ q=>q22 q
  | .branch _ q₁ q₂=>q22 q₁ ∪ q22 q₂
  | .goto _ =>∅
  | .halt =>∅
lemma q110 {K:Type} {Γ:K→ Type} {Λ σ:Type} [Finite σ]
    (q:Turing.TM2.Stmt Γ Λ σ):(q22 q).Finite:=by
  induction q with
  | push _ _ _ ih=>exact (Set.finite_range _).union ih
  | peek _ _ _ ih=>exact ih
  | pop _ _ _ ih=>exact ih
  | load _ _ ih=>exact ih
  | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
  | goto _=>exact Set.finite_empty
  | halt=>exact Set.finite_empty
def q29 {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
    (T:∀ k,Set (Γ k)) :
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩:Σ j,Γ j)∈q22 q→ s∈T k) →
    Turing.TM2.Stmt (fun k=>{s:Γ k // s∈T k}) Λ σ
  | .push k g q,h =>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
      (q29 T q (fun j s hs=>h j s (Or.inr hs)))
  | .peek k f q,h =>.peek k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
  | .pop k f q,h =>.pop k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
  | .load a q,h =>.load a (q29 T q h)
  | .branch f q₁ q₂,h =>.branch f
      (q29 T q₁ (fun j s hs=>h j s (Or.inl hs)))
      (q29 T q₂ (fun j s hs=>h j s (Or.inr hs)))
  | .goto f,_ =>.goto f
  | .halt,_ =>.halt
def q67 {K:Type} {Γ:K→ Type} {Λ σ:Type} (T:∀ k,Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s:Γ k // s∈T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
  ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma q181 {K:Type} {Γ:K→ Type} {Λ σ:Type} (T:∀ k,Set (Γ k)) :
    Function.Injective (q67 (Λ:= Λ) (σ:= σ) T):=by
  rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
  simp only [q67,Turing.TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl,rfl,hS⟩:=h
  congr 1
  funext k
  exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma q84 {K:Type} [DecidableEq K] {Γ:K→ Type} (T:∀ k,Set (Γ k))
    (S:∀ k,List {s:Γ k // s∈T k}) (k:K) (l:List {s:Γ k // s∈T k}) :
    (fun j=>(upd S k l j).map Subtype.val) =
      upd (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
  funext j
  by_cases h:j=k
  · subst h;simp
  · simp [h]
lemma q125 {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
    (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
    (hq:∀ k s,(⟨k,s⟩:Σ j,Γ j)∈q22 q→ s∈T k)
    (v:σ) (S:∀ k,List {s:Γ k // s∈T k}) :
    q67 T (stepAuxT (q29 T q hq) v S) =
      stepAuxT q v (fun k=>(S k).map Subtype.val):=by
  induction q generalizing v S with
  | push k g q ih =>
    simp only [q29,stepAuxT]
    rw [ih,q84];rfl
  | peek k f q ih =>
    simp only [q29,stepAuxT]
    exact (ih hq _ _).trans (by rw [List.head?_map])
  | pop k f q ih =>
    simp only [q29,stepAuxT]
    exact (ih hq _ _).trans (by rw [q84,List.head?_map,List.map_tail])
  | load a q ih =>
    simp only [q29,stepAuxT]
    exact ih hq (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [q29,stepAuxT]
    cases f v
    · exact ih₂ _ v S
    · exact ih₁ _ v S
  | goto f=>rfl
  | halt=>rfl
lemma cpt_to_fast {f:TapeMap} (hf:Lib.CPTs f) :
    ∃ M:Turing.TM2ComputableInPolyTime (fun x:BitTape=>x) (fun x:BitTape=>x) f,
      ∀ i,Finite (M.tm.Γ i):=by
  classical
  obtain ⟨c⟩:=hf
  let _:DecidableEq c.tm.K:=c.tm.kDecidableEq
  let _:Fintype c.tm.K:=c.tm.kFin
  let _:Fintype c.tm.Λ:= c.tm.ΛFin
  let _:Fintype c.tm.σ:= c.tm.σFin
  let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
  let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k =>
    {s | k=c.tm.k₀∨k=c.tm.k₁∨(⟨k,s⟩:Σ j,c.tm.Γ j)∈⋃ l:c.tm.Λ,q22 (c.tm.m l)}
  let e₀:{s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀ :=
    { toFun:=Subtype.val
      invFun:=fun s=>⟨s,Or.inl rfl⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let e₁:{s:c.tm.Γ c.tm.k₁ // s∈T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁ :=
    { toFun:=Subtype.val
      invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
  let tm':Turing.FinTM2 :=
    { K:=c.tm.K
      kDecidableEq:=c.tm.kDecidableEq
      kFin:=c.tm.kFin
      k₀:=c.tm.k₀
      k₁:=c.tm.k₁
      Γ:= fun k=>{s:c.tm.Γ k // s∈T k}
      Λ:= c.tm.Λ
      main:=c.tm.main
      ΛFin:=c.tm.ΛFin
      σ:= c.tm.σ
      initialState:=c.tm.initialState
      σFin:=c.tm.σFin
      Γk₀Fin:=hΓ0Fin
      m:=fun l=>q29 T (c.tm.m l) (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
  have hFin:∀ j:tm'.K,Finite (tm'.Γ j):=by
    intro j
    by_cases h0:j=c.tm.k₀
    · subst h0;exact Finite.of_fintype _
    · by_cases h1:j=c.tm.k₁
      · subst h1
        have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin:(⋃ l:c.tm.Λ,q22 (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l=>q110 (c.tm.m l)
        have:Finite ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)):=hUfin.to_subtype
        refine Finite.of_injective (f:=fun x:tm'.Γ j =>
            (⟨⟨j,x.1⟩,by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩:↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)))) ?_
        intro x y hxy
        have h1':=congrArg (fun z=>z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep:∀ cfg:tm'.Cfg,Option.map (q67 T) (tm'.step cfg)=c.tm.step (q67 T cfg):=by
    rintro ⟨l,v,S⟩
    cases l with
    | none=>rfl
    | some l =>
      change some (q67 T (stepAuxT (q29 T (c.tm.m l) _) v S)) =
        some (stepAuxT (c.tm.m l) v (fun k=>(S k).map Subtype.val))
      exact congrArg some (q125 T (c.tm.m l) _ v S)
  have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
      Option.map (q67 T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (q67 T cfg)):=by
    intro steps
    induction steps with
    | zero=>intro cfg;rfl
    | succ steps ih =>
      intro cfg
      rw [iter_succ',iter_succ']
      cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
      | none =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih];rfl
      | some cfg' =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]
        exact hstep cfg'
  let M:Turing.TM2ComputableInPolyTime (fun x:BitTape=>x) (fun x:BitTape=>x) f :=
    { tm:=tm'
      inputAlphabet:=e₀.trans c.inputAlphabet
      outputAlphabet:=e₁.trans c.outputAlphabet
      time:=c.time
      outputsFun:=fun a =>
        { steps:=(c.outputsFun a).steps
          evals_in_steps:=by
            have horig:=(c.outputsFun a).evals_in_steps
            have hinit:q67 T (Turing.initList tm' (a.map (e₀.trans c.inputAlphabet).invFun)) =
                Turing.initList c.tm (a.map c.inputAlphabet.invFun):=by
              simp only [q67,Turing.initList]
              congr 1;funext k
              by_cases hk:k=c.tm.k₀
              · subst hk;dsimp only [tm']
                simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,mapMap];rfl
              · dsimp only [tm']
                simp only [hk,↓reduceDIte,mapN]
            have hhalt:q67 T (Turing.haltList tm' ((f a).map (e₁.trans c.outputAlphabet).invFun)) =
                Turing.haltList c.tm ((f a).map c.outputAlphabet.invFun):=by
              simp only [q67,Turing.haltList]
              congr 1;funext k
              by_cases hk:k=c.tm.k₁
              · subst hk;dsimp only [tm']
                simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,mapMap];rfl
              · dsimp only [tm']
                simp only [hk,↓reduceDIte,mapN]
            apply Option.map_injective (q181 T)
            rw [hiter,hinit,horig]
            exact (congrArg some hhalt).symm
          steps_le_m:=(c.outputsFun a).steps_le_m } }
  exact ⟨M,hFin⟩
end Lib.Fast
end PT
namespace PT
namespace Alg
abbrev g (l:NVec) (i:ℕ):ℕ:= l.getD i 0
abbrev gg (S:NMat) (j:ℕ):NVec:= S.getD j []
def bit (x:BitTape) (k:ℕ):ℕ:= if x.getD k false then 1 else 0
def runAt (x:BitTape) (k:ℕ):ℕ:= ((x.drop k).takeWhile id).length
def pI (n:ℕ):NVec:= (List.range n).flatMap (fun i =>
  (List.range n).flatMap (fun j =>if i< j then [i] else []))
def pJ (n:ℕ):NVec:= (List.range n).flatMap (fun i =>
  (List.range n).flatMap (fun j =>if i< j then [j] else []))
def nV (x:BitTape):ℕ:= runAt x 0
def pN (x:BitTape):ℕ:= (pI (nV x)).length
def Em (x:BitTape):NVec:= (List.range (pN x)).map (fun k =>bit x (nV x+1+k))
def Pm (x:BitTape):NVec:= (List.range (pN x)).map (fun k =>bit x (nV x+1+pN x+k))
def oL (x:BitTape):ℕ:= nV x+1+2 * pN x
def lenV (x:BitTape):ℕ:= runAt x (oL x)
def oR (x:BitTape):ℕ:= oL x+lenV x+1
def rowM (x:BitTape):NMat:= (List.range (lenV x)).map (fun r =>
  (List.range (pN x)).map (fun k =>bit x (oR x+r * (pN x+1)+1+k)))
def rowS (x:BitTape):NVec:= (List.range (lenV x)).map (fun r =>bit x (oR x+r * (pN x+1)))
def missP (Pm row:NVec):ℕ:= ((List.range Pm.length).map (fun k =>g Pm k * (1 - g row k))).sum
def Frows (Pm:NVec) (rows:NMat):NMat :=
  (List.range rows.length).flatMap (fun r =>if missP Pm (gg rows r)=0 then [gg rows r] else [])
def Fsig (Pm:NVec) (rows:NMat) (sg:NVec):NVec :=
  (List.range rows.length).flatMap (fun r =>if missP Pm (gg rows r)=0 then [g sg r] else [])
def inVP (pi pj Pm:NVec) (v:ℕ):ℕ :=
  ((List.range Pm.length).map (fun k =>g Pm k * (if g pi k=v then 1 else if g pj k=v then 1 else 0))).sum
def Uset (pi pj Em Pm:NVec):NVec:= (List.range Em.length).flatMap (fun k =>
  if g Em k=0 then [] else if inVP pi pj Pm (g pi k)+inVP pi pj Pm (g pj k)=0 then [k] else [])
def firstNZ (v:NVec):ℕ :=
  ((List.range v.length).map (fun i =>if ((List.range (i+1)).map (fun j =>g v j)).sum=0 then 1 else 0)).sum
def isPr (c:ℕ):ℕ:= if c< 2 then 0 else
  if ((List.range c).map (fun d =>if d< 2 then 0 else if c % d=0 then 1 else 0)).sum=0 then 1 else 0
def primeAbove (B:ℕ):ℕ:= B+1+firstNZ ((List.range (B+2)).map (fun i =>isPr (B+1+i)))
def wedgeV (q N:ℕ) (x v:NVec):NVec:= (List.range (2 ^ N)).map (fun J =>
  ((List.range N).map (fun b =>if J.testBit b then
      (if ((List.range N).map (fun c =>if b< c then (if J.testBit c then 1 else 0) else 0)).sum % 2=0
        then g v b * g x (J - 2 ^ b) % q else q - g v b * g x (J - 2 ^ b) % q)
    else 0)).sum % q)
def vv (q N a:ℕ):NVec:= (List.range N).map (fun b =>a ^ b % q)
def e0 (q N:ℕ):NVec:= (List.range (2 ^ N)).map (fun J =>if J=0 then 1 % q else 0)
def wedgeLab (q N:ℕ) (pi pj τ:NVec):NVec :=
  ((fun p:ℕ × NVec =>(p.1+1,
      wedgeV q N (wedgeV q N p.2 (vv q N (g pi (g τ p.1)))) (vv q N (g pj (g τ p.1)))))^[τ.length]
    (0,e0 q N)).2
def chi (F:NMat) (τ:NVec) (r:ℕ):ℕ :=
  if ((List.range τ.length).map (fun i =>1 - g (gg F r) (g τ i))).sum=0 then 1 else 0
def vecL (q N:ℕ) (pi pj:NVec) (F:NMat) (τ:NVec):NVec :=
  (List.range (2 ^ N * F.length)).map (fun k =>
    g (wedgeLab q N pi pj τ) (k / F.length) * chi F τ (k % F.length) % q)
def posC (F:NMat) (fs:NVec) (τ:NVec):ℕ :=
  ((List.range F.length).map (fun r =>g fs r * chi F τ r)).sum
def negC (F:NMat) (fs:NVec) (τ:NVec):ℕ :=
  ((List.range F.length).map (fun r =>(1 - g fs r) * chi F τ r)).sum
def ends (pi pj τ:NVec):NVec:= (List.range (2 * τ.length)).map (fun i =>
  if i % 2=0 then g pi (g τ (i / 2)) else g pj (g τ (i / 2)))
def clash (pi pj τ:NVec):ℕ :=
  ((List.range (ends pi pj τ).length).map (fun i =>
    ((List.range (ends pi pj τ).length).map (fun j =>
      if i< j then (if g (ends pi pj τ) i=g (ends pi pj τ) j then 1 else 0) else 0)).sum)).sum
def hit (pi pj:NVec) (F:NMat) (fs τ:NVec):ℕ :=
  if clash pi pj τ=0 then (if posC F fs τ=negC F fs τ then 0 else 1) else 0
def red1 (q:ℕ) (v b:NVec) (p:ℕ):NVec :=
  (List.range v.length).map (fun i =>(g b p * g v i+(q - g v p) * g b i) % q)
def redAll (q:ℕ) (B:NMat) (pv:NVec) (v:NVec):NVec :=
  ((fun p:ℕ × NVec =>(p.1+1,red1 q p.2 (gg B p.1) (g pv p.1)))^[B.length] (0,v)).2
structure ESt where
  B:NMat
  pv:NVec
  sl:NMat
def insertG (q:ℕ) (vec:NVec→ NVec) (st:ESt) (τ:NVec):ESt :=
  let r:= redAll q st.B st.pv (vec τ)
  if r.sum=0 then st else ⟨st.B ++ [r],st.pv ++ [firstNZ r],st.sl ++ [τ]⟩
def selectG (q:ℕ) (vec:NVec→ NVec) (C:NMat):NMat :=
  ((fun p:ℕ × ESt =>(p.1+1,insertG q vec p.2 (gg C p.1)))^[C.length] (0,⟨[],[],[]⟩)).2.sl
def selectE (q N:ℕ) (pi pj:NVec) (F:NMat) (C:NMat):NMat :=
  selectG q (vecL q N pi pj F) C
def cand (U:NVec) (S:NMat):NMat :=
  (List.range S.length).flatMap (fun j =>(List.range U.length).map (fun u =>gg S j ++ [g U u]))
def hits (pi pj:NVec) (F:NMat) (fs:NVec) (C:NMat):NMat :=
  (List.range C.length).flatMap (fun j =>if hit pi pj F fs (gg C j)=0 then [] else [gg C j])
def lvl (q N:ℕ) (pi pj U:NVec) (F:NMat) (fs:NVec)
    (st:NMat × NMat):NMat × NMat :=
  if st.2.length=0 then
    (if (hits pi pj F fs st.1).length=0 then (cand U (selectE q N pi pj F st.1),[])
      else (st.1,[gg (hits pi pj F fs st.1) 0]))
  else st
def found (x:BitTape):NMat :=
  let n:= nV x
  let pi:= pI n
  let pj:= pJ n
  let F:= Frows (Pm x) (rowM x)
  let fs:= Fsig (Pm x) (rowM x) (rowS x)
  let K:= Nat.log2 F.length
  let q:= primeAbove (n+F.length)
  ((lvl q (2 * K) pi pj (Uset pi pj (Em x) (Pm x)) F fs)^[K+1] ([[]],[])).2
def outBits (x:BitTape) (τ:NVec):BitTape :=
  let F:= Frows (Pm x) (rowM x)
  let fs:= Fsig (Pm x) (rowM x) (rowS x)
  let a:= posC F fs τ
  let b:= negC F fs τ
  [true] ++ (List.range (pN x)).map (fun k =>
      decide (g (Pm x) k+((List.range τ.length).map (fun i =>if g τ i=k then 1 else 0)).sum ≠ 0)) ++
    [decide (a< b)] ++ (List.range ((lenV x).log2+1)).map (fun i =>((a - b)+(b - a)).testBit i)
def solveV (x:BitTape):BitTape :=
  if (found x).length=0 then [false] else outBits x (gg (found x) 0)
def zv (q:ℕ) (v:NVec):ℕ→ ZMod q:= fun i =>((v.getD i 0:ℕ):ZMod q)
end Alg
end PT
namespace PT
namespace Alg
def pairsF (n:ℕ):List (Fin n × Fin n):= (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j =>decide (i< j))).map (fun j =>(i,j)))
def maskF {n:ℕ} (A:Finset (Fin n × Fin n)):BitTape:= (pairsF n).map (fun e =>decide (e∈A))
def inputF (n:ℕ) (E P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool)) :
    BitTape :=
  (List.replicate n true ++ [false]) ++ maskF E ++ maskF P ++
    (List.replicate rows.length true ++ [false]) ++ rows.flatMap (fun t =>t.2 :: maskF t.1)
def ind {n:ℕ} (A:Finset (Fin n × Fin n)):NVec:= (pairsF n).map (fun e =>if e∈A then 1 else 0)
theorem dec_fm {α β:Type} (l:List α) (p:α→ Prop) [DecidablePred p] (f:α→ β) :
    l.flatMap (fun j =>if p j then [f j] else [])=(l.filter (fun j =>decide (p j))).map f:= by
  induction l with
  | nil =>simp
  | cons a l ih => by_cases h:p a <;> simp [h,ih]
theorem dec_rng (n:ℕ):List.range n=List.map Fin.val (List.finRange n) :=
  List.ext_getElem (by simp) (by simp)
theorem dec_pI (n:ℕ):pI n=(pairsF n).map (fun e =>(e.1:ℕ)):= by
  rw [pI,pairsF,dec_rng,List.flatMap_map,List.map_flatMap]
  congr 1; funext i
  rw [List.flatMap_map,mapMap]
  exact dec_fm (List.finRange n) (fun j:Fin n =>(i:ℕ)< j) (fun _ =>(i:ℕ))
theorem dec_pJ (n:ℕ):pJ n=(pairsF n).map (fun e =>(e.2:ℕ)):= by
  rw [pJ,pairsF,dec_rng,List.flatMap_map,List.map_flatMap]
  congr 1; funext i
  rw [List.flatMap_map,mapMap]
  exact dec_fm (List.finRange n) (fun j:Fin n =>(i:ℕ)< j) (fun j:Fin n =>(j:ℕ))
theorem pI_length (n:ℕ):(pI n).length=(pairsF n).length:= by simp [dec_pI]
theorem pairsF_get (n k:ℕ) (hk:k< (pairsF n).length) :
    (((pairsF n)[k]'hk).1:ℕ)=g (pI n) k∧(((pairsF n)[k]'hk).2:ℕ)=g (pJ n) k:= by
  simp [dec_pI,dec_pJ,hk]
theorem pairsF_nodup (n:ℕ):(pairsF n).Nodup:= by
  rw [pairsF,List.nodup_flatMap]
  refine ⟨fun i _ =>((List.nodup_finRange n).filter _).map (fun a b h =>(Prod.mk.inj h).2),?_⟩
  exact (List.nodup_finRange n).imp (fun hab =>List.disjoint_left.2 (by
    intro e h1 h2; simp at h1 h2; obtain ⟨_,_,rfl⟩:= h1; obtain ⟨_,_,h⟩:= h2
    exact hab (congrArg Prod.fst h).symm))
theorem mem_pairsF (n:ℕ) (e:Fin n × Fin n):e∈pairsF n ↔ e.1< e.2:= by
  obtain ⟨a,b⟩:= e; simp [pairsF]
theorem dec_bitA (a b:BitTape) (k:ℕ):bit (a ++ b) (a.length+k)=bit b k:= by
  simp [bit,List.getElem?_append_right]
theorem dec_bitB (a b:BitTape) (k:ℕ) (h:k< a.length):bit (a ++ b) k=bit a k:= by
  simp [bit,getLeftOpt h]
theorem dec_runA (a b:BitTape) (k:ℕ):runAt (a ++ b) (a.length+k)=runAt b k:= by
  simp [runAt,List.drop_append,List.drop_eq_nil_of_le (Nat.le_add_right a.length k)]
theorem dec_run0 (m:ℕ) (l:BitTape):runAt (List.replicate m true ++ false :: l) 0=m:= by
  induction m with
  | zero =>simp [runAt]
  | succ m ih =>simp_all [runAt,List.replicate_succ]
theorem dec_fmb {α:Type} (l:List α) (f:α→ BitTape) (m:ℕ) (hf:∀ a,(f a).length=m)
    (r j:ℕ) (hr:r< l.length) (hj:j< m):bit (l.flatMap f) (r * m+j)=bit (f l[r]) j:= by
  induction l generalizing r with
  | nil =>simp at hr
  | cons a l ih =>
    rw [List.flatMap_cons]
    rcases r with _ | r
    · simpa using dec_bitB _ _ j (by rw [hf]; exact hj)
    · have:(r+1) * m+j=(f a).length+(r * m+j):= by rw [hf]; ring
      rw [this,dec_bitA]; exact ih r (by simpa using hr)
theorem dec_maskF {n:ℕ} (A:Finset (Fin n × Fin n)) (k:ℕ) (h:k< (pairsF n).length) :
    bit (maskF A) k=if (pairsF n)[k]∈A then 1 else 0:= by
  simp [bit,maskF,h]
@[simp] theorem dec_maskL {n:ℕ} (A:Finset (Fin n × Fin n)):(maskF A).length=(pairsF n).length:= by
  simp [maskF]
section dec
variable (n:ℕ) (E P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool))
theorem dec_eq:inputF n E P rows=(List.replicate n true ++ [false]) ++ (maskF E ++ (maskF P ++
    ((List.replicate rows.length true ++ [false]) ++ rows.flatMap (fun t =>t.2 :: maskF t.1)))):= by
  simp [inputF]
theorem nV_inputF:nV (inputF n E P rows)=n:= by
  rw [dec_eq,nV]; simpa using dec_run0 n _
theorem pN_inputF:pN (inputF n E P rows)=(pairsF n).length:= by
  rw [pN,nV_inputF,pI_length]
theorem Em_inputF:Em (inputF n E P rows)=ind E:= by
  apply List.ext_getElem (by simp [Em,ind,pN_inputF])
  intro k h1 h2
  simp only [Em,ind,at_map,at_range,nV_inputF]
  simp [Em,pN_inputF] at h1
  rw [dec_eq,show n+1+k=(List.replicate n true ++ [false]).length+k by simp,dec_bitA,
    dec_bitB _ _ _ (by simpa using h1),dec_maskF _ _ h1]
theorem Pm_inputF:Pm (inputF n E P rows)=ind P:= by
  apply List.ext_getElem (by simp [Pm,ind,pN_inputF])
  intro k h1 h2
  simp only [Pm,ind,at_map,at_range,nV_inputF,pN_inputF]
  simp [Pm,pN_inputF] at h1
  rw [dec_eq,show n+1+(pairsF n).length+k=(List.replicate n true ++ [false]).length +
    ((maskF E).length+k) by simp; omega,dec_bitA,dec_bitA,
    dec_bitB _ _ _ (by simpa using h1),dec_maskF _ _ h1]
theorem dec_oL:oL (inputF n E P rows)=n+1+2 * (pairsF n).length:= by
  rw [oL,nV_inputF,pN_inputF]
theorem lenV_inputF:lenV (inputF n E P rows)=rows.length:= by
  rw [lenV,dec_oL,dec_eq,show n+1+2 * (pairsF n).length=(List.replicate n true ++ [false]).length +
    ((maskF E).length+((maskF P).length+0)) by simp; omega,dec_runA,dec_runA,dec_runA]
  simpa using dec_run0 _ _
theorem dec_pos (r j:ℕ):oR (inputF n E P rows)+r * ((pairsF n).length+1)+j =
    (List.replicate n true ++ [false]).length+((maskF E).length+((maskF P).length +
    ((List.replicate rows.length true ++ [false]).length+(r * ((pairsF n).length+1)+j)))):= by
  simp [oR,dec_oL,lenV_inputF]; ring
theorem dec_row (r j:ℕ) (hr:r< rows.length) (hj:j< (pairsF n).length+1) :
    bit (inputF n E P rows) (oR (inputF n E P rows)+r * ((pairsF n).length+1)+j) =
      bit (rows[r].2 :: maskF rows[r].1) j:= by
  rw [dec_pos,dec_eq,dec_bitA,dec_bitA,dec_bitA,dec_bitA,
    dec_fmb _ _ _ (fun t => by simp) _ _ hr hj]
theorem rowM_inputF:rowM (inputF n E P rows)=rows.map (fun t =>ind t.1):= by
  apply List.ext_getElem (by simp [rowM,lenV_inputF])
  intro r h1 h2
  simp [rowM,lenV_inputF] at h1
  apply List.ext_getElem (by simp [rowM,ind,pN_inputF])
  intro k h3 h4
  simp [rowM,pN_inputF] at h3
  simp only [rowM,ind,at_map,at_range,pN_inputF]
  rw [add_assoc,dec_row _ _ _ _ _ _ h1 (by omega),show 1+k=[rows[r].2].length+k by simp,
    ← List.singleton_append,dec_bitA,dec_maskF _ _ h3]
theorem rowS_inputF:rowS (inputF n E P rows)=rows.map (fun t =>if t.2 then 1 else 0):= by
  apply List.ext_getElem (by simp [rowS,lenV_inputF])
  intro r h1 h2
  simp [rowS,lenV_inputF] at h1
  simp only [rowS,at_map,at_range,pN_inputF]
  have:= dec_row n E P rows r 0 h1 (by omega)
  rw [add_zero] at this
  rw [this]; simp [bit]
end dec
end Alg
end PT
namespace PT
namespace Alg
def LwZ (q N:ℕ) (v:ℕ→ ZMod q):(ℕ→ ZMod q) →ₗ[ZMod q] (ℕ→ ZMod q) where
  toFun x J:= if J< 2 ^ N then
    ∑ b∈Finset.range N,(if J.testBit b then
      ((-1:ZMod q) ^ ((Finset.range N).filter (fun c =>b< c∧J.testBit c)).card) * v b * x (J - 2 ^ b)
      else 0) else 0
  map_add' x y:= by
    funext J; dsimp only [Pi.add_apply]; split_ifs
    · rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    · simp
  map_smul' c x:= by
    funext J; dsimp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; split_ifs
    · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    · simp
theorem ext_L (q N:ℕ) (v x:ℕ→ ZMod q) (J:ℕ):LwZ q N v x J=if J< 2 ^ N then
    ∑ b∈Finset.range N,(if J.testBit b then
      ((-1:ZMod q) ^ ((Finset.range N).filter (fun c =>b< c∧J.testBit c)).card) * v b * x (J - 2 ^ b)
      else 0) else 0:= rfl
theorem ext_ls {M:Type*} [AddCommMonoid M] (n:ℕ) (f:ℕ→ M) :
    ((List.range n).map f).sum=∑ i∈Finset.range n,f i:= by
  induction n with
  | zero =>simp
  | succ n ih =>simp [List.range_succ,Finset.sum_range_succ,ih]
theorem ext_gd {α:Type*} (n i:ℕ) (f:ℕ→ α) (d:α) :
    ((List.range n).map f).getD i d=if i< n then f i else d:= by
  rw [getDOpt]; by_cases h:i< n <;> simp [h]
theorem ext_cnt (N b J:ℕ) :
    ((List.range N).map (fun c =>if b< c then (if J.testBit c then 1 else 0) else 0)).sum =
      ((Finset.range N).filter (fun c =>b< c∧J.testBit c)).card:= by
  rw [ext_ls,Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ =>?_
  by_cases h1:b< c <;> by_cases h2:J.testBit c <;> simp [h1,h2]
theorem ext_sgn (q:ℕ) (hq:0< q) (k A:ℕ) :
    (((if k % 2=0 then A % q else q - A % q:ℕ)):ZMod q)=(-1) ^ k * A:= by
  rcases Nat.even_or_odd k with h | h
  · rw [ite_eq_left (Nat.even_iff.mp h),h.neg_one_pow,ZMod.natCast_mod,one_mul]
  · rw [ite_eq_right (by rw [Nat.odd_iff.mp h]; omega),h.neg_one_pow,Nat.cast_sub (Nat.mod_lt _ hq).le,
      ZMod.natCast_self,ZMod.natCast_mod]; ring
theorem zv_wedgeV (q N:ℕ) (hq:0< q) (x v:NVec) :
    zv q (wedgeV q N x v)=LwZ q N (zv q v) (zv q x):= by
  funext J
  simp only [zv,wedgeV,ext_gd,ext_cnt,ext_L]
  split_ifs with hJ
  · rw [ZMod.natCast_mod,ext_ls,Nat.cast_sum]
    refine Finset.sum_congr rfl fun b _ =>?_
    by_cases hb:J.testBit b
    · rw [ite_eq_left hb,ite_eq_left hb,ext_sgn q hq,Nat.cast_mul]; ring
    · rw [ite_eq_right hb,ite_eq_right hb,Nat.cast_zero]
  · simp
def ext_W (q N:ℕ) (pi pj τ:NVec):ℕ→ NVec
  | 0 =>e0 q N
  | k+1 =>wedgeV q N (wedgeV q N (ext_W q N pi pj τ k) (vv q N (g pi (g τ k)))) (vv q N (g pj (g τ k)))
theorem ext_it (q N:ℕ) (pi pj τ:NVec) (k:ℕ) :
    ((fun p:ℕ × NVec =>(p.1+1,
      wedgeV q N (wedgeV q N p.2 (vv q N (g pi (g τ p.1)))) (vv q N (g pj (g τ p.1)))))^[k]
      (0,e0 q N))=(k,ext_W q N pi pj τ k):= by
  induction k with
  | zero =>rfl
  | succ k ih =>rw [iter_succ',ih]; rfl
theorem ext_wl (q N:ℕ) (pi pj τ:NVec):wedgeLab q N pi pj τ=ext_W q N pi pj τ τ.length :=
  congrArg Prod.snd (ext_it q N pi pj τ τ.length)
theorem ext_Wa (q N:ℕ) (pi pj τ:NVec) (e:ℕ) :
    ∀ k≤ τ.length,ext_W q N pi pj (τ ++ [e]) k=ext_W q N pi pj τ k
  | 0,_ =>rfl
  | k+1,h => by
    have h2:g (τ ++ [e]) k=g τ k:= by
      simp only [g,getDOpt]; rw [getLeftOpt (by omega)]
    simp only [ext_W]; rw [ext_Wa q N pi pj τ e k (by omega),h2]
theorem wedgeLab_snoc (q N:ℕ) (pi pj τ:NVec) (e:ℕ) :
    wedgeLab q N pi pj (τ ++ [e]) =
      wedgeV q N (wedgeV q N (wedgeLab q N pi pj τ) (vv q N (g pi e))) (vv q N (g pj e)):= by
  have h2:g (τ ++ [e]) τ.length=e:= by simp only [g,getDOpt]; simp
  rw [ext_wl,ext_wl,len_app,len_one,ext_W,
    ext_Wa q N pi pj τ e _ le_rfl,h2]
theorem ext_Wl (q N:ℕ) (pi pj τ:NVec):∀ k,(ext_W q N pi pj τ k).length=2 ^ N
  | 0 => by simp [ext_W,e0]
  | k+1 => by simp [ext_W,wedgeV]
theorem wedgeLab_length (q N:ℕ) (pi pj τ:NVec):(wedgeLab q N pi pj τ).length=2 ^ N:= by
  rw [ext_wl]; exact ext_Wl _ _ _ _ _ _
def ext_G (q N:ℕ) (u:ℕ→ ℕ→ ZMod q):ℕ→ ℕ→ ZMod q
  | 0 =>zv q (e0 q N)
  | r+1 =>LwZ q N (u r) (ext_G q N u r)
theorem ext_e0 (q N J:ℕ):zv q (e0 q N) J=if J=0 then 1 else 0:= by
  simp only [zv,e0,ext_gd]
  by_cases h:J=0
  · subst h; simp [ZMod.natCast_mod]
  · simp [h]
theorem ext_bm {J c:ℕ}:J.testBit c=true ↔ ∃ j< J.bitIndices.length,J.bitIndices.getD j 0=c:= by
  rw [← Nat.mem_bitIndices,List.mem_iff_getElem]
  constructor
  · rintro ⟨j,hj,rfl⟩; exact ⟨j,hj,List.getD_eq_getElem _ _ hj⟩
  · rintro ⟨j,hj,rfl⟩; exact ⟨j,hj,(List.getD_eq_getElem _ _ hj).symm⟩
theorem ext_bN {N J c:ℕ} (hJ:J< 2 ^ N) (hc:J.testBit c=true):c< N:= by
  by_contra h
  have:= Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hJ (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)))
  simp_all
theorem ext_lt {l:NVec} (hl:l.SortedLT) {i j:ℕ} (hi:i< l.length) (hj:j< l.length) :
    l.getD i 0< l.getD j 0 ↔ i< j:= by
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
  exact hl.lt_iff_lt (a:= ⟨i,hi⟩) (b:= ⟨j,hj⟩)
theorem ext_inj {l:NVec} (hl:l.SortedLT) {i j:ℕ} (hi:i< l.length) (hj:j< l.length)
    (h:l.getD i 0=l.getD j 0):i=j:= by
  rcases lt_trichotomy i j with h' | h' | h'
  · have:= (ext_lt hl hi hj).mpr h'; omega
  · exact h'
  · have:= (ext_lt hl hj hi).mpr h'; omega
theorem ext_er (J i:ℕ) (hi:i< J.bitIndices.length) :
    (J - 2 ^ J.bitIndices.getD i 0).bitIndices=J.bitIndices.eraseIdx i:= by
  have hs:(J.bitIndices.eraseIdx i).SortedLT :=
    (Nat.bitIndices_sorted.pairwise.sublist (List.eraseIdx_sublist _ _)).sortedLT
  have hJ:= Nat.sum_map_two_pow_bitIndices J
  set l:= J.bitIndices
  have hl:l=l.take i ++ l[i] :: l.drop (i+1):= by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have h3:(l.map (fun i =>2 ^ i)).sum =
      ((l.take i).map (fun i =>2 ^ i)).sum+2 ^ l[i]+((l.drop (i+1)).map (fun i =>2 ^ i)).sum:= by
    conv_lhs =>rw [hl]
    simp only [List.map_append,mapC,List.sum_append,List.sum_cons]; ring
  have h4:J - 2 ^ l.getD i 0=((l.eraseIdx i).map (fun i =>2 ^ i)).sum:= by
    rw [List.eraseIdx_eq_take_drop_succ,List.getD_eq_getElem _ _ hi,List.map_append,List.sum_append]
    omega
  rw [h4,Nat.bitIndices_sum_map_two_pow hs]
theorem ext_ge (l:NVec) (i k:ℕ) :
    (l.eraseIdx i).getD k 0=l.getD (if k< i then k else k+1) 0:= by
  rw [getDOpt,getDOpt]
  split_ifs with h
  · rw [List.getElem?_eraseIdx_of_lt h]
  · rw [List.getElem?_eraseIdx_of_ge (not_lt.mp h)]
theorem ext_sa {r:ℕ} (i:Fin (r+1)) (k:Fin r) :
    (i.succAbove k:ℕ)=if (k:ℕ)< i then (k:ℕ) else (k:ℕ)+1:= by
  rcases lt_or_ge (k:ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h),ite_eq_left h]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h),ite_eq_right (by omega)]; rfl
theorem ext_key {M:Type*} [AddCommMonoid M] (N J:ℕ) (hJ:J< 2 ^ N) (F:ℕ→ M) :
    (∑ b∈Finset.range N,if J.testBit b then F b else 0) =
      ∑ i∈Finset.range J.bitIndices.length,F (J.bitIndices.getD i 0):= by
  rw [← Finset.sum_filter]
  have:(Finset.range N).filter (fun b =>J.testBit b=true) =
      (Finset.range J.bitIndices.length).image (fun i =>J.bitIndices.getD i 0):= by
    ext c
    simp only [mem_filt,Finset.mem_range,Finset.mem_image]
    exact ⟨fun h =>ext_bm.mp h.2,fun h =>⟨ext_bN hJ (ext_bm.mpr h),ext_bm.mpr h⟩⟩
  rw [this,Finset.sum_image fun a ha b hb hab =>
    ext_inj Nat.bitIndices_sorted (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab]
theorem ext_card (N J r:ℕ) (hJ:J< 2 ^ N) (hr:J.bitIndices.length=r+1) (i:ℕ) (hi:i< r+1) :
    ((Finset.range N).filter (fun c =>J.bitIndices.getD i 0< c∧J.testBit c)).card=r - i:= by
  have hs:= @Nat.bitIndices_sorted J
  have hi':i< J.bitIndices.length:= by omega
  have:(Finset.range N).filter (fun c =>J.bitIndices.getD i 0< c∧J.testBit c) =
      (Finset.Ioc i r).image (fun j =>J.bitIndices.getD j 0):= by
    ext c
    simp only [mem_filt,Finset.mem_range,Finset.mem_image,Finset.mem_Ioc]
    constructor
    · rintro ⟨-,hlt,hb⟩
      obtain ⟨j,hj,rfl⟩:= ext_bm.mp hb
      exact ⟨j,⟨(ext_lt hs hi' hj).mp hlt,by omega⟩,rfl⟩
    · rintro ⟨j,⟨h1,h2⟩,rfl⟩
      have hj:j< J.bitIndices.length:= by omega
      exact ⟨ext_bN hJ (ext_bm.mpr ⟨j,hj,rfl⟩),(ext_lt hs hi' hj).mpr h1,ext_bm.mpr ⟨j,hj,rfl⟩⟩
  rw [this,Finset.card_image_of_injOn fun a ha b hb hab =>ext_inj hs
    (by simp only [Finset.coe_Ioc,Set.mem_Ioc] at ha; omega)
    (by simp only [Finset.coe_Ioc,Set.mem_Ioc] at hb; omega) hab,Nat.card_Ioc]
theorem ext_det (q N:ℕ) (u:ℕ→ ℕ→ ZMod q) (r J:ℕ) :
    ext_G q N u r J=if J< 2 ^ N∧J.bitIndices.length=r then
      (Matrix.of fun i k:Fin r =>u k (J.bitIndices.getD i 0)).det else 0:= by
  induction r generalizing J with
  | zero =>
    rw [ext_G,ext_e0,Matrix.det_fin_zero]
    by_cases h:J=0
    · subst h; simp
    · rw [ite_eq_right h,ite_eq_right]; rintro ⟨-,h2⟩; apply h
      rw [← Nat.sum_map_two_pow_bitIndices J,List.length_eq_zero_iff.mp h2]; rfl
  | succ r ih =>
    rw [ext_G,ext_L]
    by_cases hJ:J< 2 ^ N
    swap
    · simp [hJ]
    rw [ite_eq_left hJ,ext_key N J hJ]
    by_cases hr:J.bitIndices.length=r+1
    · rw [ite_eq_left ⟨hJ,hr⟩,Matrix.det_succ_column _ (Fin.last r),hr,Finset.sum_range]
      refine Fintype.sum_congr _ _ fun i =>?_
      have hi:= i.isLt
      have hi':(i:ℕ)< J.bitIndices.length:= by omega
      rw [ih,ext_er J i hi',ite_eq_left ⟨lt_of_le_of_lt (Nat.sub_le _ _) hJ,by rw [List.length_eraseIdx_of_lt hi']; omega⟩,
        ext_card N J r hJ hr i hi]
      simp only [Matrix.of_apply,Fin.val_last,Fin.succAbove_last]
      congr 1
      · congr 1
        rw [show (i:ℕ)+r=(r - i)+2 * i by omega,pow_add,pow_mul]; simp
      · congr 1; ext a b
        simp only [Matrix.of_apply,Matrix.submatrix_apply,ext_ge,ext_sa,Fin.val_castSucc]
    · rw [ite_eq_right (fun h =>hr h.2)]
      refine Finset.sum_eq_zero fun i hi =>?_
      rw [Finset.mem_range] at hi
      rw [ih,ext_er J i hi,ite_eq_right,mul_zero]
      rintro ⟨-,h⟩; rw [List.length_eraseIdx_of_lt hi] at h; omega
def ext_u (q N:ℕ) (pi pj τ:NVec) (i:ℕ):ℕ→ ZMod q :=
  zv q (vv q N (if i % 2=0 then g pi (g τ (i / 2)) else g pj (g τ (i / 2))))
theorem ext_wz (q N:ℕ) (hq:0< q) (pi pj τ:NVec) (k:ℕ) :
    zv q (ext_W q N pi pj τ k)=ext_G q N (ext_u q N pi pj τ) (2 * k):= by
  induction k with
  | zero =>rfl
  | succ k ih =>
    have ha:ext_u q N pi pj τ (2 * k)=zv q (vv q N (g pi (g τ k))):= by
      simp only [ext_u]; rw [ite_eq_left (by omega),show 2 * k / 2=k by omega]
    have hb:ext_u q N pi pj τ (2 * k+1)=zv q (vv q N (g pj (g τ k))):= by
      simp only [ext_u]; rw [ite_eq_right (by omega),show (2 * k+1) / 2=k by omega]
    rw [show 2 * (k+1)=2 * k+1+1 by ring,ext_W,ext_G,ext_G,zv_wedgeV q N hq,
      zv_wedgeV q N hq,ih,ha,hb]
theorem ext_wz2 (q N:ℕ) (hq:0< q) (pi pj τ:NVec) :
    zv q (wedgeLab q N pi pj τ)=ext_G q N (ext_u q N pi pj τ) (2 * τ.length):= by
  rw [ext_wl,ext_wz q N hq]
theorem ext_ue (q N:ℕ) (pi pj τ:NVec) (i:ℕ) (h:i< 2 * τ.length) :
    ext_u q N pi pj τ i=zv q (vv q N ((ends pi pj τ).getD i 0)):= by
  rw [ext_u,ends,ext_gd,ite_eq_left h]
theorem ext_cl (pi pj τ:NVec):clash pi pj τ=0 ↔
    ∀ i j,i< j→ j< 2 * τ.length→ (ends pi pj τ).getD i 0 ≠ (ends pi pj τ).getD j 0:= by
  have hL:(ends pi pj τ).length=2 * τ.length:= by simp [ends]
  simp only [clash,g,ext_ls,hL,Finset.sum_eq_zero_iff,Finset.mem_range]
  constructor
  · intro h i j hij hj he
    have:= h i (by omega) j hj
    rw [ite_eq_left hij,ite_eq_left he] at this; exact one_ne_zero this
  · intro h i _ j hj
    split_ifs with h1 h2
    · exact absurd h2 (h i j h1 hj)
    · rfl
    · rfl
theorem ext_gs (r:ℕ):((List.range r).map (fun i =>2 ^ i)).sum+1=2 ^ r:= by
  induction r with
  | zero =>simp
  | succ r ih =>
    rw [List.range_succ,List.map_append,List.sum_append,pow_succ]; simp; omega
theorem wedgeLab_zero (q N:ℕ) [Fact q.Prime] (pi pj τ:NVec) (h:clash pi pj τ ≠ 0) :
    zv q (wedgeLab q N pi pj τ)=0:= by
  have hq0:= (Fact.out:q.Prime).pos
  obtain ⟨i,j,hij,hj,he⟩:∃ i j,i< j∧j< 2 * τ.length ∧
      (ends pi pj τ).getD i 0=(ends pi pj τ).getD j 0:= by
    by_contra hc; exact h ((ext_cl pi pj τ).mpr fun i j hij hj he =>hc ⟨i,j,hij,hj,he⟩)
  funext J
  rw [ext_wz2 q N hq0,ext_det,Pi.zero_apply]
  split_ifs
  · refine Matrix.det_zero_of_column_eq (i:= (⟨i,by omega⟩:Fin (2 * τ.length))) (j:= ⟨j,hj⟩)
      (fun h => by simp [fin_eq] at h; omega) fun k =>?_
    simp only [Matrix.of_apply]
    rw [ext_ue _ _ _ _ _ _ (by omega:i< 2 * τ.length),ext_ue _ _ _ _ _ _ hj,he]
  · rfl
theorem wedgeLab_ne_zero (q N:ℕ) [Fact q.Prime] (pi pj τ:NVec) (h:clash pi pj τ=0)
    (hN:2 * τ.length≤ N) (hq:∀ a∈ends pi pj τ,a< q) :
    zv q (wedgeLab q N pi pj τ) ≠ 0:= by
  have hq0:= (Fact.out:q.Prime).pos
  have hd:= (ext_cl pi pj τ).mp h
  have hL:(ends pi pj τ).length=2 * τ.length:= by simp [ends]
  have hm:∀ k< 2 * τ.length,(ends pi pj τ).getD k 0< q:= fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hq _ (at_mem _)
  intro h0
  have hJ:= ext_gs (2 * τ.length)
  have h1:= congrFun h0 ((List.range (2 * τ.length)).map (fun i =>2 ^ i)).sum
  rw [Pi.zero_apply,ext_wz2 q N hq0,ext_det,Nat.bitIndices_sum_map_two_pow (List.sortedLT_range _),
    ite_eq_left ⟨lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by norm_num) hN),by simp⟩] at h1
  have hM:Matrix.transpose (Matrix.vandermonde fun k:Fin (2 * τ.length) =>
      (((ends pi pj τ).getD k 0:ℕ):ZMod q))=Matrix.of fun i k:Fin (2 * τ.length) =>
        ext_u q N pi pj τ k ((List.range (2 * τ.length)).getD i 0):= by
    ext i k
    have hi:= i.isLt
    rw [Matrix.transpose_apply,Matrix.vandermonde_apply,Matrix.of_apply,
      List.getD_eq_getElem (List.range _) _ (by simp),at_range,ext_ue _ _ _ _ _ _ k.isLt,zv,vv,
      ext_gd,ite_eq_left (by omega),ZMod.natCast_mod,Nat.cast_pow]
  refine (Matrix.det_vandermonde_ne_zero_iff (v:= fun k:Fin (2 * τ.length) =>
    (((ends pi pj τ).getD k 0:ℕ):ZMod q))).mpr ?_ (by rw [← Matrix.det_transpose,hM]; exact h1)
  intro a b hab
  simp only at hab
  rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt (hm _ a.isLt),Nat.mod_eq_of_lt (hm _ b.isLt)] at hab
  rcases lt_trichotomy (a:ℕ) b with h' | h' | h'
  · exact absurd hab (hd _ _ h' b.isLt)
  · exact Fin.ext h'
  · exact absurd hab.symm (hd _ _ h' a.isLt)
end Alg
end PT
namespace PT
namespace Alg
def selStep (q:ℕ) (vec:NVec→ NVec) (C:NMat) (p:ℕ × ESt):ℕ × ESt :=
  (p.1+1,insertG q vec p.2 (gg C p.1))
theorem selectG_eq (q:ℕ) (vec:NVec→ NVec) (C:NMat) :
    selectG q vec C=((selStep q vec C)^[C.length] (0,⟨[],[],[]⟩)).2.sl:= rfl
theorem el_fst {α:Type} (f:ℕ × α→ ℕ × α) (h:∀ p,(f p).1=p.1+1) (x:α) :
    ∀ k,(f^[k] (0,x)).1=k
  | 0 =>rfl
  | k+1 => by rw [iter_succ',h,el_fst f h x k]
theorem el_gP {α:Type} (P:α→ Prop) (l:List α) (d:α) (i:ℕ) (h0:P d)
    (h:∀ a∈l,P a):P (l.getD i d):= by
  rw [getDOpt]
  cases e:l[i]? with
  | none =>simpa using h0
  | some a =>simpa using h a (List.mem_of_getElem? e)
theorem el_mem {α:Type} (l:List α) (d:α) (k:ℕ) (h:k< l.length):l.getD k d∈l:= by
  rw [List.getD_eq_getElem _ _ h]; exact at_mem h
theorem el_gapp {α:Type} (l:List α) (a d:α) (j:ℕ) :
    (l ++ [a]).getD j d=if j< l.length then l.getD j d else if j=l.length then a else d:= by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega
theorem el_cnt (a:ℕ):∀ n,((List.range n).map fun i =>if i< a then 1 else 0).sum=min n a
  | 0 => by simp
  | n+1 => by
    rw [List.range_succ,List.map_append,List.sum_append,el_cnt a n]; simp; split_ifs <;> omega
theorem el_fnz (v:NVec) (h:∃ i,i< v.length∧g v i ≠ 0) :
    firstNZ v< v.length∧g v (firstNZ v) ≠ 0:= by
  classical
  have e:firstNZ v=Nat.find h:= by
    unfold firstNZ
    rw [List.map_congr_left (g:= fun i =>if i< Nat.find h then 1 else 0),el_cnt]
    · exact min_eq_right (Nat.find_spec h).1.le
    intro i _
    have:((List.range (i+1)).map fun j =>g v j).sum=0 ↔ i< Nat.find h:= by
      rw [List.sum_eq_zero_iff]
      simp only [mem_mapL,List.mem_range,forall_exists_index,and_imp,
        forall_apply_eq_imp_iff₂]
      constructor
      · intro H; by_contra H'; push Not at H'; exact (Nat.find_spec h).2 (H _ (by omega))
      · intro H j hj
        have:= Nat.find_min h (show j< Nat.find h by omega)
        by_cases hj2:j< v.length
        · by_contra H2; exact this ⟨hj2,H2⟩
        · exact List.getD_eq_default _ _ (by omega)
    simp only [this]
  rw [e]; exact Nat.find_spec h
theorem el_g1 (q:ℕ) (w b:NVec) (p i:ℕ) :
    g (red1 q w b p) i=if i< w.length then (g b p * g w i+(q - g w p) * g b i) % q else 0:= by
  simp only [g]; split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp [red1,h])]; simp [red1]
  · rw [List.getD_eq_default]; simp [red1]; omega
theorem el_m0 (q a b:ℕ) (h:a≤ q):(b * a+(q - a) * b) % q=0:= by
  rw [show b * a+(q - a) * b=q * b by zify [h]; ring]; exact Nat.mul_mod_right q b
def el_I (q D:ℕ) (st:ESt):Prop :=
  st.pv.length=st.B.length∧st.sl.length=st.B.length ∧
  (∀ b∈st.B,b.length=D∧∀ a∈b,a< q) ∧
  ∀ j< st.B.length,g st.pv j< D∧g (gg st.B j) (g st.pv j) ≠ 0 ∧
    ∀ l,j< l→ l< st.B.length→ g (gg st.B l) (g st.pv j)=0
def el_it (q:ℕ) (B:NMat) (pv v:NVec) (k:ℕ):ℕ × NVec :=
  (fun p:ℕ × NVec =>(p.1+1,red1 q p.2 (gg B p.1) (g pv p.1)))^[k] (0,v)
theorem el_its (q:ℕ) (B:NMat) (pv v:NVec) (k:ℕ) :
    el_it q B pv v (k+1)=(k+1,red1 q (el_it q B pv v k).2 (gg B k) (g pv k)):= by
  have:= el_fst (fun p:ℕ × NVec =>(p.1+1,red1 q p.2 (gg B p.1) (g pv p.1))) (fun _ =>rfl) v k
  simp only [el_it,iter_succ',this]
theorem el_redA (q D:ℕ) (hq:0< q) (st:ESt) (hI:el_I q D st) (v:NVec)
    (hv:v.length=D) (hv2:∀ a∈v,a< q):∀ k≤ st.B.length,
    (el_it q st.B st.pv v k).2.length=D∧(∀ a∈(el_it q st.B st.pv v k).2,a< q) ∧
      ∀ j< k,g (el_it q st.B st.pv v k).2 (g st.pv j)=0
  | 0 =>fun _ =>⟨hv,hv2,by simp⟩
  | k+1 =>fun hk => by
    obtain ⟨h1,h2,h3⟩:= el_redA q D hq st hI v hv hv2 k (by omega)
    rw [el_its]
    refine ⟨by simp [red1,h1],?_,?_⟩
    · intro a ha; simp only [red1,mem_mapL] at ha; obtain ⟨i,_,rfl⟩:= ha; exact Nat.mod_lt _ hq
    · intro j hj; rw [el_g1]; split_ifs
      · rcases (show j< k∨j=k by omega) with hj | rfl
        · rw [h3 j hj,(hI.2.2.2 j (by omega)).2.2 k hj (by omega)]; simp
        · exact el_m0 _ _ _ (el_gP (·< q) _ _ _ hq h2).le
      · rfl
theorem el_insI (q D:ℕ) (hq:0< q) (vec:NVec→ NVec) (st:ESt) (hI:el_I q D st)
    (τ:NVec) (hv:(vec τ).length=D) (hv2:∀ a∈vec τ,a< q) :
    el_I q D (insertG q vec st τ):= by
  obtain ⟨hr1,hr2,hr3⟩:= el_redA q D hq st hI _ hv hv2 _ le_rfl
  have hr1':(redAll q st.B st.pv (vec τ)).length=D:= hr1
  unfold insertG; dsimp only; split_ifs with hs
  · exact hI
  have hne:∃ i,i< (redAll q st.B st.pv (vec τ)).length∧g (redAll q st.B st.pv (vec τ)) i ≠ 0:= by
    obtain ⟨a,ha,ha0⟩:∃ a∈redAll q st.B st.pv (vec τ),a ≠ 0:= by
      by_contra H; push Not at H; exact hs (List.sum_eq_zero_iff.mpr H)
    obtain ⟨i,hi,rfl⟩:= List.getElem_of_mem ha
    exact ⟨i,hi,by simp only [g]; rwa [List.getD_eq_getElem _ _ hi]⟩
  have hp:= el_fnz _ hne
  obtain ⟨hI1,hI2,hI3,hI4⟩:= hI
  refine ⟨by simp [hI1],by simp [hI2],?_,?_⟩
  · intro b hb; rw [mem_app,mem_one] at hb
    rcases hb with hb | rfl
    · exact hI3 b hb
    · exact ⟨hr1,hr2⟩
  · intro j hj; simp only [len_app,len_one] at hj
    simp only [g,gg,el_gapp,hI1]
    rcases (show j< st.B.length∨j=st.B.length by omega) with hj | rfl
    · simp only [hj,ite_true]; obtain ⟨a1,a2,a3⟩:= hI4 j hj; refine ⟨a1,a2,fun l hl1 hl2 =>?_⟩
      simp only [len_app,len_one] at hl2
      rcases (show l< st.B.length∨l=st.B.length by omega) with hl | rfl
      · simp only [hl,ite_true]; exact a3 l hl1 hl
      · simp only [lt_irrefl,ite_false,ite_true]; exact hr3 j hj
    · simp only [lt_irrefl,ite_false,ite_true]
      exact ⟨by omega,hp.2,fun l h1 h2 => by simp at h2; omega⟩
def el_st (q:ℕ) (vec:NVec→ NVec) (C:NMat) (i:ℕ):ℕ × ESt :=
  (selStep q vec C)^[i] (0,⟨[],[],[]⟩)
theorem el_sts (q:ℕ) (vec:NVec→ NVec) (C:NMat) (i:ℕ) :
    el_st q vec C (i+1)=(i+1,insertG q vec (el_st q vec C i).2 (gg C i)):= by
  have:= el_fst (selStep q vec C) (fun _ =>rfl) ⟨[],[],[]⟩ i
  simp only [el_st,iter_succ',selStep,this]
theorem el_sub (q:ℕ) (vec:NVec→ NVec) (C:NMat) :
    ∀ i≤ C.length,∀ τ∈(el_st q vec C i).2.sl,τ∈C
  | 0 =>fun _ τ h => by simp [el_st] at h
  | i+1 =>fun hi τ hτ => by
    rw [el_sts] at hτ; unfold insertG at hτ; dsimp only at hτ; split_ifs at hτ
    · exact el_sub q vec C i (by omega) τ hτ
    · rw [mem_app,mem_one] at hτ
      rcases hτ with h | rfl
      · exact el_sub q vec C i (by omega) τ h
      · exact el_mem C [] i (by omega)
theorem el_invI (q:ℕ) (hq:0< q) (vec:NVec→ NVec) (D:ℕ)
    (hlen:∀ τ,(vec τ).length=D) (hlt:∀ τ,∀ a∈vec τ,a< q) (C:NMat) :
    ∀ i,el_I q D (el_st q vec C i).2
  | 0 => by show el_I q D ⟨[],[],[]⟩; exact ⟨rfl,rfl,by simp,by simp⟩
  | i+1 => by rw [el_sts]; exact el_insI q D hq vec _ (el_invI q hq vec D hlen hlt C i) _ (hlen _) (hlt _)
theorem el_Blen (q D:ℕ) (st:ESt) (hI:el_I q D st):st.B.length≤ D:= by
  have:= Finset.card_le_card_of_injOn (fun j =>g st.pv j) (s:= Finset.range st.B.length)
    (t:= Finset.range D) ?_ ?_
  · simpa using this
  · intro j hj; simp at hj ⊢; exact (hI.2.2.2 j hj).1
  · intro j1 hj1 j2 hj2 e; simp at hj1 hj2; by_contra hne; dsimp only at e
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have:= (hI.2.2.2 j1 hj1).2.2 j2 h hj2; rw [e] at this; exact (hI.2.2.2 j2 hj2).2.1 this
    · have:= (hI.2.2.2 j2 hj2).2.2 j1 h hj1; rw [← e] at this; exact (hI.2.2.2 j1 hj1).2.1 this
theorem el_pvlt (q D:ℕ) (st:ESt) (hI:el_I q D st):∀ p∈st.pv,p< D:= by
  intro p hp; obtain ⟨j,hj,rfl⟩:= List.getElem_of_mem hp
  have:= (hI.2.2.2 j (hI.1 ▸ hj)).1; simp only [g] at this; rwa [List.getD_eq_getElem _ _ hj] at this
theorem selStep_inv (q:ℕ) (hq:0< q) (vec:NVec→ NVec) (D:ℕ)
    (hlen:∀ τ,(vec τ).length=D) (hlt:∀ τ,∀ a∈vec τ,a< q) (C:NMat)
    (i:ℕ) (hi:i≤ C.length) :
    ((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).1=i ∧
    (((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.B.length≤ D) ∧
    (((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.pv.length=((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.B.length) ∧
    (((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.sl.length=((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.B.length) ∧
    (∀ b∈((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.B,b.length=D∧∀ a∈b,a< q) ∧
    (∀ p∈((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.pv,p< D) ∧
    (∀ τ∈((selStep q vec C)^[i] (0,⟨[],[],[]⟩)).2.sl,τ∈C):= by
  have hI:= el_invI q hq vec D hlen hlt C i
  exact ⟨el_fst _ (fun _ =>rfl) _ i,el_Blen q D _ hI,hI.1,hI.2.1,hI.2.2.1,el_pvlt q D _ hI,
    el_sub q vec C i hi⟩
theorem selectG_sub (q:ℕ) (vec:NVec→ NVec) (C:NMat) :
    ∀ τ∈selectG q vec C,τ∈C:= fun τ h =>el_sub q vec C _ le_rfl τ h
theorem selectG_length (q:ℕ) (hq:0< q) (vec:NVec→ NVec) (D:ℕ)
    (hlen:∀ τ,(vec τ).length=D) (hlt:∀ τ,∀ a∈vec τ,a< q) (C:NMat) :
    (selectG q vec C).length≤ D:= by
  obtain ⟨-,h1,-,h2,-⟩:= selStep_inv q hq vec D hlen hlt C _ le_rfl
  rw [selectG_eq,h2]; exact h1
def el_sp (q:ℕ) (f:NVec→ ℕ→ ZMod q) (L:NMat):Submodule (ZMod q) (ℕ→ ZMod q) :=
  Submodule.span (ZMod q) {z | ∃ τ∈L,z=f τ}
theorem el_sps (q:ℕ) (f:NVec→ ℕ→ ZMod q) (L:NMat) (a:NVec) :
    el_sp q f (L ++ [a])=el_sp q f L ⊔ Submodule.span (ZMod q) {f a}:= by
  unfold el_sp; rw [← Submodule.span_union]; congr 1; ext z
  simp only [Set.mem_union,Set.mem_setOf_eq,Set.mem_singleton_iff,mem_app,mem_one]
  constructor
  · rintro ⟨τ,h | rfl,rfl⟩; exacts [Or.inl ⟨τ,h,rfl⟩,Or.inr rfl]
  · rintro (⟨τ,h,rfl⟩ | rfl); exacts [⟨τ,Or.inl h,rfl⟩,⟨_,Or.inr rfl,rfl⟩]
theorem el_sp0 (q:ℕ) (f:NVec→ ℕ→ ZMod q):el_sp q f []=⊥:= by simp [el_sp]
theorem el_swap {K V:Type} [Field K] [AddCommGroup V] [Module K V] (W:Submodule K V) (x y:V)
    (c:K) (hc:c ≠ 0) (h:x - c • y∈W):W ⊔ Submodule.span K {x}=W ⊔ Submodule.span K {y}:= by
  apply le_antisymm <;> apply sup_le le_sup_left <;> rw [Submodule.span_singleton_le_iff_mem]
  · have:x=(x - c • y)+c • y:= by abel
    rw [this]; exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)))
  · have:y=c⁻¹ • (x - (x - c • y)):= by simp [smul_smul,inv_mul_cancel₀ hc]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)) (Submodule.mem_sup_left h))
theorem el_zv1 (q:ℕ) (w b:NVec) (p:ℕ) (hb:b.length≤ w.length) (hw:g w p≤ q) :
    zv q (red1 q w b p)=(g b p:ZMod q) • zv q w - (g w p:ZMod q) • zv q b:= by
  funext i
  simp only [zv,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  have:= el_g1 q w b p i
  simp only [g] at this hw ⊢
  split_ifs at this with hi
  · rw [this,ZMod.natCast_mod]; push_cast [Nat.cast_sub hw,ZMod.natCast_self]; ring
  · have e1:w.getD i 0=0:= List.getD_eq_default _ _ (by omega)
    have e2:b.getD i 0=0:= List.getD_eq_default _ _ (by omega)
    rw [this,e1,e2]; simp
theorem el_redB (q D:ℕ) [Fact q.Prime] (st:ESt) (hI:el_I q D st) (v:NVec)
    (hv:v.length=D) (hv2:∀ a∈v,a< q):∀ k≤ st.B.length,
    ∃ c:ZMod q,c ≠ 0∧zv q (el_it q st.B st.pv v k).2 - c • zv q v∈el_sp q (zv q) st.B
  | 0 =>fun _ =>⟨1,one_ne_zero,by
    show zv q v - _ • _∈_; rw [one_smul,sub_self]; exact zero_mem _⟩
  | k+1 =>fun hk => by
    have hq:0< q:= (Fact.out:q.Prime).pos
    obtain ⟨c,hc,h⟩:= el_redB q D st hI v hv hv2 k (by omega)
    obtain ⟨h1,h2,-⟩:= el_redA q D hq st hI v hv hv2 k (by omega)
    have hb:(gg st.B k).length=D∧∀ a∈gg st.B k,a< q:= hI.2.2.1 _ (el_mem st.B [] k hk)
    have hp:= (hI.2.2.2 k hk).2.1
    refine ⟨(g (gg st.B k) (g st.pv k):ZMod q) * c,mul_ne_zero ?_ hc,?_⟩
    · intro h0; have h3:= congrArg ZMod.val h0
      rw [ZMod.val_natCast,ZMod.val_zero,Nat.mod_eq_of_lt (el_gP (·< q) _ _ _ hq hb.2)] at h3
      exact hp h3
    · rw [el_its]; dsimp only
      rw [el_zv1 _ _ _ _ (by omega) (el_gP (·< q) _ _ _ hq h2).le]
      have hbm:zv q (gg st.B k)∈el_sp q (zv q) st.B :=
        Submodule.subset_span ⟨_,el_mem st.B [] k hk,rfl⟩
      convert Submodule.sub_mem _ (Submodule.smul_mem _ (g (gg st.B k) (g st.pv k):ZMod q) h)
        (Submodule.smul_mem _ (g (el_it q st.B st.pv v k).2 (g st.pv k):ZMod q) hbm) using 1
      rw [smul_sub,smul_smul]; abel
theorem el_insS (q D:ℕ) [Fact q.Prime] (vec:NVec→ NVec) (st:ESt) (hI:el_I q D st)
    (hS:el_sp q (zv q) st.B=el_sp q (fun τ =>zv q (vec τ)) st.sl)
    (τ:NVec) (hv:(vec τ).length=D) (hv2:∀ a∈vec τ,a< q) :
    el_sp q (zv q) (insertG q vec st τ).B=el_sp q (fun τ =>zv q (vec τ)) (insertG q vec st τ).sl ∧
    el_sp q (fun τ =>zv q (vec τ)) (insertG q vec st τ).sl =
      el_sp q (fun τ =>zv q (vec τ)) st.sl ⊔ Submodule.span (ZMod q) {zv q (vec τ)}:= by
  obtain ⟨c,hc,h⟩:= el_redB q D st hI _ hv hv2 _ le_rfl
  rw [hS] at h
  unfold insertG; dsimp only; split_ifs with hs
  · refine ⟨hS,?_⟩; symm; apply sup_eq_left.mpr; rw [Submodule.span_singleton_le_iff_mem]
    have hz:zv q (redAll q st.B st.pv (vec τ))=0:= funext fun i => by
      simp only [zv,Pi.zero_apply]
      rw [(el_gP (·=0) _ 0 i rfl (List.sum_eq_zero_iff.mp hs):(redAll q st.B st.pv (vec τ)).getD i 0=0)]
      simp
    change zv q _ - _∈_ at h
    rw [show (el_it q st.B st.pv (vec τ) st.B.length).2=redAll q st.B st.pv (vec τ) from rfl,hz,
      zero_sub,neg_mem_iff] at h
    have:= Submodule.smul_mem _ c⁻¹ h; rwa [smul_smul,inv_mul_cancel₀ hc,one_smul] at this
  · simp only [el_sps,hS,and_true]
    exact el_swap _ _ _ c hc h
theorem el_spAll (q:ℕ) [Fact q.Prime] (vec:NVec→ NVec) (D:ℕ)
    (hlen:∀ τ,(vec τ).length=D) (hlt:∀ τ,∀ a∈vec τ,a< q) (C:NMat) :
    ∀ i≤ C.length,el_sp q (zv q) (el_st q vec C i).2.B=el_sp q (fun τ =>zv q (vec τ)) (el_st q vec C i).2.sl ∧
      el_sp q (fun τ =>zv q (vec τ)) (el_st q vec C i).2.sl=el_sp q (fun τ =>zv q (vec τ)) (C.take i)
  | 0 =>fun _ =>⟨by simp only [el_st,Function.iterate_zero,id,el_sp0],
      by simp only [el_st,Function.iterate_zero,id,el_sp0,List.take_zero]⟩
  | i+1 =>fun hi => by
    obtain ⟨h1,h2⟩:= el_spAll q vec D hlen hlt C i (by omega)
    rw [el_sts]
    obtain ⟨e1,e2⟩:= el_insS q D vec _ (el_invI q (Fact.out:q.Prime).pos vec D hlen hlt C i) h1
      (gg C i) (hlen _) (hlt _)
    refine ⟨e1,?_⟩
    have:C.take (i+1)=C.take i ++ [gg C i]:= by
      have e:gg C i=C[i]:= List.getD_eq_getElem _ _ (by omega)
      rw [e]; exact List.take_succ_eq_append_getElem (by omega)
    rw [e2,h2,this,el_sps]
theorem selectG_span (q:ℕ) [Fact q.Prime] (vec:NVec→ NVec) (D:ℕ)
    (hlen:∀ τ,(vec τ).length=D) (hlt:∀ τ,∀ a∈vec τ,a< q) (C:NMat) :
    Submodule.span (ZMod q) {z | ∃ τ∈selectG q vec C,z=zv q (vec τ)} =
      Submodule.span (ZMod q) {z | ∃ τ∈C,z=zv q (vec τ)}:= by
  have:= (el_spAll q vec D hlen hlt C _ le_rfl).2
  rw [List.take_length] at this; exact this
end Alg
end PT
namespace PT
namespace Alg
def sgn {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (Q:Finset (Fin n × Fin n)):ℤ :=
  ((rows.filter (fun t =>t.2 && decide (Q ⊆ t.1))).length:ℤ) -
    ((rows.filter (fun t =>!t.2 && decide (Q ⊆ t.1))).length:ℤ)
section mob
variable {n:ℕ}
theorem mob_split (rows:List (Finset (Fin n × Fin n) × Bool)) (a:Fin n × Fin n) (Q) :
    sgn rows Q=sgn (rows.filter (fun t =>decide (a∈t.1))) Q +
      sgn (rows.filter (fun t =>!decide (a∈t.1))) Q:= by
  induction rows with
  | nil =>simp [sgn]
  | cons t l ih =>
    obtain ⟨s,b⟩:= t
    by_cases h1:a∈s <;> by_cases h2:Q ⊆ s <;> cases b <;>
      simp [sgn,h1,h2] at ih ⊢ <;> omega
theorem mob_ins (rows:List (Finset (Fin n × Fin n) × Bool)) (a:Fin n × Fin n) (Q) :
    sgn (rows.filter (fun t =>decide (a∈t.1))) Q=sgn rows (insert a Q):= by
  induction rows with
  | nil =>simp [sgn]
  | cons t l ih =>
    obtain ⟨s,b⟩:= t
    by_cases h1:a∈s <;> by_cases h2:Q ⊆ s <;> cases b <;>
      simp [sgn,h1,h2,Finset.insert_subset_iff] at ih ⊢ <;> omega
theorem mob_len (rows:List (Finset (Fin n × Fin n) × Bool)) (a:Fin n × Fin n) (P) :
    (rows.filter (fun t =>decide (P ⊆ t.1))).length =
      ((rows.filter (fun t =>decide (a∈t.1))).filter (fun t =>decide (P ⊆ t.1))).length +
      ((rows.filter (fun t =>!decide (a∈t.1))).filter (fun t =>decide (P ⊆ t.1))).length:= by
  induction rows with
  | nil =>simp
  | cons t l ih =>
    by_cases h1:a∈t.1 <;> by_cases h2:P ⊆ t.1 <;> simp [h1,h2] at ih ⊢ <;> omega
theorem mob_abs (rows:List (Finset (Fin n × Fin n) × Bool)) (P) :
    (sgn rows P).natAbs≤ (rows.filter (fun t =>decide (P ⊆ t.1))).length:= by
  induction rows with
  | nil =>simp [sgn]
  | cons t l ih =>
    obtain ⟨s,b⟩:= t
    by_cases h2:P ⊆ s <;> cases b <;> simp [sgn,h2] at ih ⊢ <;> omega
end mob
theorem mobius_bound {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool))
    (P R:Finset (Fin n × Fin n)) (hzero:∀ S,S ⊂ R→ sgn rows (P ∪ S)=0) :
    2 ^ R.card * (sgn rows (P ∪ R)).natAbs≤ (rows.filter (fun t =>decide (P ⊆ t.1))).length:= by
  induction R using Finset.induction_on generalizing rows with
  | empty =>simpa using mob_abs rows P
  | insert a R ha ih =>
    have hs:∀ S,S ⊂ R→ insert a S ⊂ insert a R:= fun S hS =>
      ⟨Finset.insert_subset_insert a hS.1,fun h =>hS.2 (fun x hx => by
        have:= h (mem_ins_of hx)
        rcases mem_ins.1 this with rfl | h' <;> [exact absurd hx ha; exact h'])⟩
    have e1:∀ S,sgn (rows.filter (fun t =>decide (a∈t.1))) (P ∪ S)=sgn rows (P ∪ insert a S) :=
      fun S => by rw [mob_ins,Finset.union_insert]
    have h1:= ih (rows.filter (fun t =>decide (a∈t.1))) (fun S hS => by
      rw [e1]; exact hzero _ (hs S hS))
    have h2:= ih (rows.filter (fun t =>!decide (a∈t.1))) (fun S hS => by
      have:= mob_split rows a (P ∪ S)
      rw [e1,hzero _ (hs S hS),hzero _ (hS.trans (Finset.ssubset_insert ha))] at this
      omega)
    have e2:= mob_split rows a (P ∪ R)
    rw [e1,hzero _ (Finset.ssubset_insert ha)] at e2
    rw [e1] at h1
    have e3:(sgn (rows.filter (fun t =>!decide (a∈t.1))) (P ∪ R)).natAbs =
      (sgn rows (P ∪ insert a R)).natAbs:= by omega
    rw [e3] at h2
    rw [mob_len rows a P,Finset.card_insert_of_notMem ha,pow_succ]
    nlinarith
end Alg
end PT
namespace PT
namespace Alg
theorem lv_gm {α:Type} (d:α) (S:List α) {j:ℕ} (hj:j< S.length):S.getD j d∈S:= by
  rw [List.getD_eq_getElem _ _ hj]; exact at_mem hj
theorem lv_mg {α:Type} (d:α) {S:List α} {τ:α} (h:τ∈S):∃ j< S.length,S.getD j d=τ:= by
  obtain ⟨j,hj,rfl⟩:= List.getElem_of_mem h
  exact ⟨j,hj,List.getD_eq_getElem _ _ hj⟩
theorem lv_cand (U:NVec) (S:NMat) (τ:NVec) :
    τ∈cand U S ↔ ∃ ρ∈S,∃ e∈U,τ=ρ ++ [e]:= by
  simp only [cand,List.mem_flatMap,mem_mapL,List.mem_range]
  constructor
  · rintro ⟨j,hj,u,hu,rfl⟩; exact ⟨_,lv_gm _ _ hj,_,lv_gm _ _ hu,rfl⟩
  · rintro ⟨ρ,hρ,e,he,rfl⟩
    obtain ⟨j,hj,rfl⟩:= lv_mg [] hρ
    obtain ⟨u,hu,rfl⟩:= lv_mg 0 he
    exact ⟨j,hj,u,hu,rfl⟩
theorem lv_hits (pi pj:NVec) (F:NMat) (fs:NVec) (C:NMat) (τ:NVec) :
    τ∈hits pi pj F fs C ↔ τ∈C∧hit pi pj F fs τ ≠ 0:= by
  simp only [hits,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨j,hj,h⟩
    split_ifs at h with h0
    · simp at h
    · rw [mem_one] at h; subst h; exact ⟨lv_gm _ _ hj,h0⟩
  · rintro ⟨hτ,h0⟩
    obtain ⟨j,hj,rfl⟩:= lv_mg [] hτ
    exact ⟨j,hj,by simp only [h0,↓reduceIte,mem_one]⟩
theorem lv_ls (q m:ℕ) (f:ℕ→ ℕ) :
    ((((List.range m).map f).sum:ℕ):ZMod q)=∑ r∈Finset.range m,(f r:ZMod q):= by
  induction m with
  | zero =>simp
  | succ m ih =>simp [List.range_succ,Finset.sum_range_succ,ih]
theorem lv_zv (q N:ℕ) (pi pj:NVec) (F:NMat) (τ:NVec) (k:ℕ) :
    zv q (vecL q N pi pj F τ) k=if k< 2 ^ N * F.length then
      zv q (wedgeLab q N pi pj τ) (k / F.length) * (chi F τ (k % F.length):ZMod q) else 0:= by
  unfold zv vecL
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [ZMod.natCast_mod]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp
theorem lv_fun (q N:ℕ) (pi pj:NVec) (F:NMat) (τ:NVec) {r:ℕ} (hr:r< F.length) :
    LinearMap.funLeft (ZMod q) (ZMod q) (fun J =>J * F.length+r) (zv q (vecL q N pi pj F τ)) =
      (chi F τ r:ZMod q) • zv q (wedgeLab q N pi pj τ):= by
  funext J
  simp only [LinearMap.funLeft_apply,Pi.smul_apply,smul_eq_mul,lv_zv]
  have h1:(J * F.length+r) / F.length=J:= by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hr,Nat.zero_add]
  have h2:(J * F.length+r) % F.length=r:= by
    rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr]
  rw [h1,h2]
  split_ifs with h
  · ring
  · have:2 ^ N≤ J:= by
      by_contra h'; apply h
      calc J * F.length+r< (J+1) * F.length:= by rw [Nat.succ_mul]; omega
        _≤ 2 ^ N * F.length:= Nat.mul_le_mul_right _ (by omega)
    have h3:(wedgeLab q N pi pj τ)[J]?=none:= by
      rw [List.getElem?_eq_none_iff,wedgeLab_length]; exact this
    simp [zv,h3]
theorem lv_chi (F:NMat) (σ:NVec) (e r:ℕ) :
    chi F (σ ++ [e]) r=chi F σ r * (if 1 - g (gg F r) e=0 then 1 else 0):= by
  have h1:(List.range σ.length).map (fun i =>1 - g (gg F r) (g (σ ++ [e]) i)) =
      (List.range σ.length).map (fun i =>1 - g (gg F r) (g σ i)) :=
    List.map_congr_left (fun i hi => by rw [List.mem_range] at hi; simp [getLeftOpt hi])
  have h2:g (σ ++ [e]) σ.length=e:= by simp
  simp only [chi,len_app,len_one,List.range_succ,List.map_append,List.sum_append,
    h1,mapC,mapN,List.sum_cons,List.sum_nil,h2]
  split_ifs <;> omega
def lv_L (q N:ℕ) (pi pj:NVec) (F:NMat) (e:ℕ):(ℕ→ ZMod q) →ₗ[ZMod q] (ℕ→ ZMod q) :=
  LinearMap.pi (fun k =>if k< 2 ^ N * F.length then
    ((if 1 - g (gg F (k % F.length)) e=0 then 1 else 0:ℕ):ZMod q) •
      (LinearMap.proj (k / F.length) ∘ₗ LwZ q N (zv q (vv q N (g pj e))) ∘ₗ LwZ q N (zv q (vv q N (g pi e))) ∘ₗ
        LinearMap.funLeft (ZMod q) (ZMod q) (fun J =>J * F.length+k % F.length)) else 0)
theorem lv_L_ap (q N:ℕ) (hq:0< q) (pi pj:NVec) (F:NMat) (σ:NVec) (e:ℕ) :
    lv_L q N pi pj F e (zv q (vecL q N pi pj F σ))=zv q (vecL q N pi pj F (σ ++ [e])):= by
  funext k
  rw [lv_zv]
  simp only [lv_L,LinearMap.pi_apply]
  by_cases hk:k< 2 ^ N * F.length
  · simp only [hk,↓reduceIte]
    have hr:k % F.length< F.length:= Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos F.length with h | h
      · rw [h,Nat.mul_zero] at hk; omega
      · exact h)
    simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply,lv_fun q N pi pj F σ hr,
      map_smul,wedgeLab_snoc,zv_wedgeV q N hq,lv_chi,smul_eq_mul]
    simp [mul_comm]
  · simp [hk]
def lv_c (q:ℕ) (F:NMat) (fs:NVec):(ℕ→ ZMod q) →ₗ[ZMod q] (ℕ→ ZMod q) :=
  ∑ r∈Finset.range F.length,(((g fs r:ℕ):ZMod q) - ((1 - g fs r:ℕ):ZMod q)) •
    LinearMap.funLeft (ZMod q) (ZMod q) (fun J =>J * F.length+r)
theorem lv_c_ap (q N:ℕ) (pi pj:NVec) (F:NMat) (fs τ:NVec) :
    lv_c q F fs (zv q (vecL q N pi pj F τ)) =
      ((posC F fs τ:ZMod q) - (negC F fs τ:ZMod q)) • zv q (wedgeLab q N pi pj τ):= by
  rw [lv_c,LinearMap.sum_apply,posC,negC,lv_ls,lv_ls,← Finset.sum_sub_distrib,Finset.sum_smul]
  refine Finset.sum_congr rfl (fun r hr =>?_)
  rw [LinearMap.smul_apply,lv_fun q N pi pj F τ (Finset.mem_range.mp hr),smul_smul]
  congr 1; push_cast; ring
theorem lv_snd (q N:ℕ) [Fact q.Prime] (pi pj:NVec) (F:NMat) (fs τ:NVec)
    (h:lv_c q F fs (zv q (vecL q N pi pj F τ)) ≠ 0):hit pi pj F fs τ ≠ 0:= by
  rw [lv_c_ap] at h
  have hc:clash pi pj τ=0:= by
    by_contra hc; exact h (by rw [wedgeLab_zero q N pi pj τ hc,smul_zero])
  have hp:posC F fs τ ≠ negC F fs τ:= by
    intro he; exact h (by rw [he,sub_self,zero_smul])
  simp [hit,hc,hp]
theorem lv_le (F:NMat) (f:ℕ→ ℕ) (h:∀ r,f r≤ 1) :
    ((List.range F.length).map f).sum≤ F.length:= by
  have:= List.sum_le_length_nsmul ((List.range F.length).map f) 1 (by simpa using fun r _ =>h r)
  simpa using this
theorem lv_cmp (q N K:ℕ) [Fact q.Prime] (hN:N=2 * K) (pi pj:NVec) (F:NMat) (fs τ:NVec)
    (hq:∀ a∈ends pi pj τ,a< q) (hm:F.length< q) (hfs:∀ a∈fs,a≤ 1) (hl:τ.length≤ K)
    (h:hit pi pj F fs τ ≠ 0):lv_c q F fs (zv q (vecL q N pi pj F τ)) ≠ 0:= by
  have hc:clash pi pj τ=0:= by by_contra hc; simp [hit,hc] at h
  have hp:posC F fs τ ≠ negC F fs τ:= by intro he; simp [hit,he] at h
  have hch:∀ r,chi F τ r≤ 1:= fun r => by unfold chi; split_ifs <;> omega
  have hg:∀ r,g fs r≤ 1:= fun r => by
    rw [g,getDOpt]
    cases h':fs[r]? with
    | none =>simp
    | some a =>simpa using hfs a (List.mem_of_getElem? h')
  have h1:posC F fs τ< q:= lt_of_le_of_lt (lv_le F _ (fun r =>
    le_trans (Nat.mul_le_mul (hg r) (hch r)) (by norm_num))) hm
  have h2:negC F fs τ< q:= lt_of_le_of_lt (lv_le F _ (fun r =>
    le_trans (Nat.mul_le_mul (Nat.sub_le 1 _) (hch r)) (by norm_num))) hm
  rw [lv_c_ap]
  refine smul_ne_zero ?_ (wedgeLab_ne_zero q N pi pj τ hc (by omega) hq)
  intro he; apply hp
  have:= congrArg ZMod.val (sub_eq_zero.mp he)
  rwa [ZMod.val_cast_of_lt h1,ZMod.val_cast_of_lt h2] at this
def lv_I (q N:ℕ) (pi pj U:NVec) (F:NMat) (fs:NVec) (i:ℕ)
    (st:NMat × NMat):Prop :=
  (st.2=[]∧(∀ τ∈st.1,τ.length=i∧∀ e∈τ,e∈U) ∧
    (∀ σ:NVec,σ.length=i→ (∀ e∈σ,e∈U)→ zv q (vecL q N pi pj F σ) ∈
      Submodule.span (ZMod q) {z | ∃ τ∈st.1,z=zv q (vecL q N pi pj F τ)}) ∧
    ∀ σ:NVec,(∀ e∈σ,e∈U)→ σ.length< i→ hit pi pj F fs σ=0) ∨
  (∃ τ:NVec,st.2=[τ]∧(∀ e∈τ,e∈U)∧τ.length< i∧hit pi pj F fs τ ≠ 0 ∧
    ∀ σ:NVec,(∀ e∈σ,e∈U)→ σ.length< τ.length→ hit pi pj F fs σ=0)
theorem lv_step (q N K:ℕ) [Fact q.Prime] (hN:N=2 * K) (pi pj U:NVec)
    (F:NMat) (fs:NVec)
    (hq:∀ τ:NVec,(∀ e∈τ,e∈U)→ ∀ a∈ends pi pj τ,a< q)
    (hm:F.length< q) (hfs:∀ a∈fs,a≤ 1) (i:ℕ) (hi:i≤ K) (st:NMat × NMat)
    (h:lv_I q N pi pj U F fs i st):lv_I q N pi pj U F fs (i+1) (lvl q N pi pj U F fs st):= by
  have q0:0< q:= (Fact.out:q.Prime).pos
  have hvl:∀ τ,(vecL q N pi pj F τ).length=2 ^ N * F.length:= fun τ => by simp [vecL]
  have hvq:∀ τ,∀ a∈vecL q N pi pj F τ,a< q:= fun τ a ha => by
    simp only [vecL,mem_mapL] at ha; obtain ⟨k,_,rfl⟩:= ha; exact Nat.mod_lt _ q0
  rcases h with ⟨h2,hC,hsp,hno⟩ | ⟨τ,h2,hU,hl,hh,hmin⟩
  · unfold lvl; simp only [h2,len_nil,↓reduceIte]
    split_ifs with hH
    · left
      refine ⟨rfl,fun τ hτ =>?_,fun σ hσ hU =>?_,fun σ hU hl =>?_⟩
      · obtain ⟨ρ,hρ,e,he,rfl⟩:= (lv_cand _ _ _).mp hτ
        obtain ⟨h1,h3⟩:= hC ρ (selectG_sub _ _ _ ρ hρ)
        refine ⟨by simp [h1],fun x hx =>?_⟩
        rcases mem_app.mp hx with hx | hx
        · exact h3 x hx
        · rw [mem_one.mp hx]; exact he
      · obtain ⟨ρ,e,rfl⟩:∃ ρ e,σ=ρ ++ [e]:= by
          rcases List.eq_nil_or_concat σ with h0 | ⟨ρ,e,h0⟩
          · subst h0; simp at hσ
          · exact ⟨ρ,e,by rw [h0,List.concat_eq_append]⟩
        have hρ:= hsp ρ (by simpa using hσ) (fun x hx =>hU x (List.mem_append_left _ hx))
        rw [← selectG_span q _ _ hvl hvq] at hρ
        have:= Submodule.apply_mem_span_image_of_mem_span (lv_L q N pi pj F e) hρ
        rw [lv_L_ap q N q0] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_,⟨τ,hτ,rfl⟩,rfl⟩
        exact ⟨τ ++ [e],(lv_cand _ _ _).mpr ⟨τ,hτ,e,hU e (by simp),rfl⟩,lv_L_ap q N q0 _ _ _ _ _⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
        · exact hno σ hU hl
        by_contra hσ
        have hc:= lv_cmp q N K hN pi pj F fs σ (hq σ hU) hm hfs (by omega) hσ
        apply hc
        have hk:Submodule.span (ZMod q) {z | ∃ τ∈st.1,z=zv q (vecL q N pi pj F τ)} ≤
            LinearMap.ker (lv_c q F fs):= by
          rw [Submodule.span_le]
          rintro _ ⟨τ,hτ,rfl⟩
          by_contra h0
          have:= (lv_hits pi pj F fs st.1 τ).mpr ⟨hτ,lv_snd q N pi pj F fs τ h0⟩
          rw [List.length_eq_zero_iff] at hH; rw [hH] at this; simp at this
        exact hk (hsp σ hl hU)
    · right
      have h0:0< (hits pi pj F fs st.1).length:= Nat.pos_of_ne_zero hH
      obtain ⟨hτ,hh⟩:= (lv_hits pi pj F fs st.1 (gg (hits pi pj F fs st.1) 0)).mp (lv_gm [] _ h0)
      obtain ⟨h1,h3⟩:= hC _ hτ
      exact ⟨_,rfl,h3,by omega,hh,fun σ hU hl =>hno σ hU (by omega)⟩
  · unfold lvl; simp only [h2,len_one,one_ne_zero,↓reduceIte]
    exact Or.inr ⟨τ,h2,hU,by omega,hh,hmin⟩
theorem found_spec (q N K:ℕ) [Fact q.Prime] (hN:N=2 * K) (pi pj U:NVec)
    (F:NMat) (fs:NVec)
    (hq:∀ τ:NVec,(∀ e∈τ,e∈U)→ ∀ a∈ends pi pj τ,a< q)
    (hm:F.length< q) (hfs:∀ a∈fs,a≤ 1) (_hfsl:fs.length=F.length) :
    (((lvl q N pi pj U F fs)^[K+1] ([[]],[])).2=[] ∧
      ∀ τ:NVec,(∀ e∈τ,e∈U)→ τ.length≤ K→ hit pi pj F fs τ=0) ∨
    (∃ τ:NVec,((lvl q N pi pj U F fs)^[K+1] ([[]],[])).2=[τ]∧(∀ e∈τ,e∈U) ∧
      τ.length≤ K∧hit pi pj F fs τ ≠ 0 ∧
      ∀ σ:NVec,(∀ e∈σ,e∈U)→ σ.length< τ.length→ hit pi pj F fs σ=0):= by
  have hall:∀ i≤ K+1,lv_I q N pi pj U F fs i ((lvl q N pi pj U F fs)^[i] ([[]],[])):= by
    intro i hi
    induction i with
    | zero =>
      left
      refine ⟨rfl,fun τ hτ => by simp at hτ; simp [hτ],fun σ hσ _ =>?_,fun σ _ hl => by simp at hl⟩
      rw [List.length_eq_zero_iff] at hσ; subst hσ
      exact Submodule.subset_span ⟨[],by simp,rfl⟩
    | succ i ih =>
      rw [iter_succ']
      exact lv_step q N K hN pi pj U F fs hq hm hfs i (by omega) _ (ih (by omega))
  rcases hall (K+1) le_rfl with ⟨h2,-,-,hno⟩ | ⟨τ,h2,hU,hl,hh,hmin⟩
  · exact Or.inl ⟨h2,fun τ hU hl =>hno τ hU (by omega)⟩
  · exact Or.inr ⟨τ,h2,hU,by omega,hh,hmin⟩
end Alg
end PT
namespace PT
namespace Alg
open Lib.R Lib.Universal Lib.Loop
theorem tqzN {f:BitTape→ ℕ} (h:NatR f) :
    ∀ ⦃p:BitTape→ BitTape⦄,Lib.CPTs p→ NatR (fun t =>f (p t)) :=
  fun _ hp =>Lib.Machines.cpt_comp (g:= fun s =>un (f s)) hp h
theorem tqzV {f:BitTape→ NVec} (h:VecR f) :
    ∀ ⦃p:BitTape→ BitTape⦄,Lib.CPTs p→ VecR (fun t =>f (p t)) :=
  fun _ hp =>Lib.Machines.cpt_comp (g:= fun s =>encV (f s)) hp h
theorem tqzL {f:BitTape→ NMat} (h:LLR f) :
    ∀ ⦃p:BitTape→ BitTape⦄,Lib.CPTs p→ LLR (fun t =>f (p t)) :=
  fun _ hp =>Lib.Machines.cpt_comp (g:= fun s =>encLL (f s)) hp h
theorem tqzI:∀ ⦃p:BitTape→ BitTape⦄,Lib.CPTs p→ NatR (fun t =>(unpairB (p t)).1.length) :=
  fun _ hp =>natR_len (cpt_unpairB1_1 hp)
theorem tqgN {n:BitTape→ ℕ} {H:ℕ→ BitTape→ ℕ} (hn:NatR n)
    (hH:NatR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s =>(List.range (n s)).map (fun i =>H i s)):= vecR_gen Lib.Machines.cpt_id hn hH
theorem tqgF {n:BitTape→ ℕ} {H:ℕ→ BitTape→ NVec} (hn:NatR n)
    (hH:VecR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    VecR (fun s =>(List.range (n s)).flatMap (fun i =>H i s)):= vecR_flat Lib.Machines.cpt_id hn hH
theorem tqgL {n:BitTape→ ℕ} {H:ℕ→ BitTape→ NVec} (hn:NatR n)
    (hH:VecR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s =>(List.range (n s)).map (fun i =>H i s)):= llR_gen Lib.Machines.cpt_id hn hH
theorem tqgLF {n:BitTape→ ℕ} {H:ℕ→ BitTape→ NMat} (hn:NatR n)
    (hH:LLR (fun t =>H (unpairB t).1.length (unpairB t).2)) :
    LLR (fun s =>(List.range (n s)).flatMap (fun i =>H i s)):= llR_flat Lib.Machines.cpt_id hn hH
theorem tqnE {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if a s=b s then x s else y s) :=
  cptE (cpt_ite_eq ha hb hx hy) (fun _ =>(apply_ite un _ _ _).symm)
theorem tqnL {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if a s< b s then x s else y s) :=
  cptE (cpt_ite_lt ha hb hx hy) (fun _ =>(apply_ite un _ _ _).symm)
theorem tqnT {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if (a s).testBit (b s) then x s else y s) :=
  cptE (cpt_ite_eq (natR_testBit ha hb) (natR_const 1) hx hy)
    (fun s => by dsimp only; cases (a s).testBit (b s) <;> rfl)
theorem tqvE {a b:BitTape→ ℕ} {x y:BitTape→ NVec} (ha:NatR a) (hb:NatR b)
    (hx:VecR x) (hy:VecR y):VecR (fun s =>if a s=b s then x s else y s) :=
  cptE (cpt_ite_eq ha hb hx hy) (fun _ =>(apply_ite encV _ _ _).symm)
theorem tqvL {a b:BitTape→ ℕ} {x y:BitTape→ NVec} (ha:NatR a) (hb:NatR b)
    (hx:VecR x) (hy:VecR y):VecR (fun s =>if a s< b s then x s else y s) :=
  cptE (cpt_ite_lt ha hb hx hy) (fun _ =>(apply_ite encV _ _ _).symm)
theorem tqlE {a b:BitTape→ ℕ} {x y:BitTape→ NMat} (ha:NatR a) (hb:NatR b)
    (hx:LLR x) (hy:LLR y):LLR (fun s =>if a s=b s then x s else y s) :=
  cptE (cpt_ite_eq ha hb hx hy) (fun _ =>(apply_ite encLL _ _ _).symm)
theorem tqI {n:BitTape→ ℕ} (hn:NatR n):VecR (fun s =>pI (n s)):= by
  have:= tqzN hn; unfold pI
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgF,tqvL,vecR_single,vecR_nil,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem tqJ {n:BitTape→ ℕ} (hn:NatR n):VecR (fun s =>pJ (n s)):= by
  have:= tqzN hn; unfold pJ
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgF,tqvL,vecR_single,vecR_nil,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_nV:NatR (fun s =>nV s):= natR_runAt Lib.Machines.cpt_id (natR_const 0)
theorem tqcN {f:BitTape→ ℕ} (h:NatR f):Lib.CPTs (fun s =>un (f s)):= h
theorem tqcV {f:BitTape→ NVec} (h:VecR f):Lib.CPTs (fun s =>encV (f s)):= h
theorem natR_pN:NatR (fun s =>pN s):= natR_vlen (tqI natR_nV)
theorem vecR_pI {n:BitTape→ ℕ} (hn:NatR n):VecR (fun s =>pI (n s)):= tqI hn
theorem vecR_pJ {n:BitTape→ ℕ} (hn:NatR n):VecR (fun s =>pJ (n s)):= tqJ hn
theorem vecR_Em:VecR (fun s =>Em s):= by
  unfold Em bit
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,natR_bit,natR_add,natR_const,tqzN natR_nV,tqzN natR_pN,tqzI,
    Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_Pm:VecR (fun s =>Pm s):= by
  unfold Pm bit
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,natR_bit,natR_add,natR_const,tqzN natR_nV,tqzN natR_pN,tqzI,
    Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_lenV:NatR (fun s =>lenV s):= by
  unfold lenV runAt oL
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [natR_runAt,natR_add,natR_mul,natR_const,natR_nV,natR_pN,Lib.Machines.cpt_id]
theorem llR_rowM:LLR (fun s =>rowM s):= by
  unfold rowM oR oL bit
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgL,tqgN,natR_bit,natR_add,
    natR_mul,natR_const,tqzN natR_nV,tqzN natR_pN,tqzN natR_lenV,tqzI,Lib.Machines.cpt_id,
    cpt_unpairB2_1]
theorem vecR_rowS:VecR (fun s =>rowS s):= by
  unfold rowS oR oL bit
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,natR_bit,natR_add,natR_mul,
    natR_const,tqzN natR_nV,tqzN natR_pN,tqzN natR_lenV,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem llR_Frows {pm:BitTape→ NVec} {rows:BitTape→ NMat} (hp:VecR pm)
    (hr:LLR rows):LLR (fun s =>Frows (pm s) (rows s)):= by
  have:= tqzV hp; have:= tqzL hr; unfold Frows missP
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgLF,tqlE,llR_single,llR_nil,
    vecR_row,natR_sum,tqgN,natR_mul,natR_sub,natR_get,natR_vlen,natR_llen,natR_const,tqzI,
    Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_Fsig {pm sg:BitTape→ NVec} {rows:BitTape→ NMat} (hp:VecR pm)
    (hr:LLR rows) (hs:VecR sg):VecR (fun s =>Fsig (pm s) (rows s) (sg s)):= by
  have:= tqzV hp; have:= tqzL hr; have:= tqzV hs; unfold Fsig missP
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgF,tqvE,vecR_single,vecR_nil,
    vecR_row,natR_sum,tqgN,natR_mul,natR_sub,natR_get,natR_vlen,natR_llen,natR_const,tqzI,
    Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_Uset {pi pj em pm:BitTape→ NVec} (hi:VecR pi) (hj:VecR pj) (he:VecR em)
    (hp:VecR pm):VecR (fun s =>Uset (pi s) (pj s) (em s) (pm s)):= by
  have:= tqzV hi; have:= tqzV hj; have:= tqzV he; have:= tqzV hp; unfold Uset inVP
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgF,tqvE,vecR_single,vecR_nil,
    natR_sum,tqgN,natR_mul,tqnE,natR_add,natR_get,natR_vlen,natR_const,tqzI,
    Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_firstNZ {v:BitTape→ NVec} (hv:VecR v):NatR (fun s =>firstNZ (v s)):= by
  have:= tqzV hv; unfold firstNZ
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [natR_sum,tqgN,tqnE,natR_add,
    natR_get,natR_vlen,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_primeAbove {B:BitTape→ ℕ} (hB:NatR B):NatR (fun s =>primeAbove (B s)):= by
  have:= tqzN hB; unfold primeAbove isPr
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [natR_firstNZ,natR_sum,tqgN,tqnE,
    tqnL,natR_add,natR_mod,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
end Alg
end PT
namespace PT
namespace Alg
open Lib.R Lib.Universal Lib.Loop
theorem tqW (q N:ℕ) (x v:NVec):wedgeV q N x v=(List.range (2 ^ N)).map (fun J =>
  ((List.range N).map (fun b =>if J.testBit b then
      (if ((List.range N).map (fun c =>if b< c then (if J.testBit c then 1 else 0) else 0)).sum % 2=0
        then g v b * g x (J - 2 ^ b % (J+1)) % q else q - g v b * g x (J - 2 ^ b % (J+1)) % q)
    else 0)).sum % q):= by
  unfold wedgeV; congr 1; funext J; congr 3; funext b
  by_cases h:J.testBit b
  · rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (Nat.ge_two_pow_of_testBit h))]
  · simp [h]
theorem vecR_wedgeV {q N:BitTape→ ℕ} {x v:BitTape→ NVec} (hq:NatR q) (hN:NatR N)
    (hP:NatR (fun s =>2 ^ N s)) (hx:VecR x) (hv:VecR v) :
    VecR (fun s =>wedgeV (q s) (N s) (x s) (v s)):= by
  have:= tqzN hq; have:= tqzN hN; have:= tqzN hP; have:= tqzV hx; have:= tqzV hv
  simp only [tqW]
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,dsl_powmodS,natR_mod,natR_sum,tqnT,tqnE,tqnL,
    natR_mul,natR_sub,natR_get,natR_add,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_vv {q N a:BitTape→ ℕ} (hq:NatR q) (hq0:∀ s,0< q s) (hN:NatR N) (ha:NatR a) :
    VecR (fun s =>vv (q s) (N s) (a s)):= by
  have e:(fun s =>vv (q s) (N s) (a s)) =
      fun s =>(List.range (N s)).map (fun b =>a s ^ b % (q s - 1+1)):= by
    funext s; simp only [vv,Nat.sub_add_cancel (hq0 s)]
  rw [e]; have hq1:= natR_sub hq (natR_const 1)
  have:= tqzN hq1; have:= tqzN ha
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,dsl_powmodS,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_e0 {q N:BitTape→ ℕ} (hq:NatR q) (hP:NatR (fun s =>2 ^ N s)) :
    VecR (fun s =>e0 (q s) (N s)):= by
  have:= tqzN hq; unfold e0
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,tqnE,natR_mod,natR_const,tqzI,Lib.Machines.cpt_id,
    cpt_unpairB2_1]
def tqS (q N:ℕ) (pi pj τ:NVec) (p:ℕ × NVec):ℕ × NVec :=
  (p.1+1,wedgeV q N (wedgeV q N p.2 (vv q N (g pi (g τ p.1)))) (vv q N (g pj (g τ p.1))))
def tqE (s:BitTape) (p:ℕ × NVec):BitTape:= pairB (un p.1) (pairB (encV p.2) s)
def tqT (q N:BitTape→ ℕ) (pi pj τ:BitTape→ NVec) (t:BitTape):BitTape :=
  tqE (unpairB (unpairB t).2).2 (tqS (q (unpairB (unpairB t).2).2) (N (unpairB (unpairB t).2).2)
    (pi (unpairB (unpairB t).2).2) (pj (unpairB (unpairB t).2).2) (τ (unpairB (unpairB t).2).2)
    ((unpairB t).1.length,decV (unpairB (unpairB t).2).1))
theorem tqit (q N:BitTape→ ℕ) (pi pj τ:BitTape→ NVec) (s:BitTape) (k:ℕ) :
    ∀ p,(tqT q N pi pj τ)^[k] (tqE s p)=tqE s ((tqS (q s) (N s) (pi s) (pj s) (τ s))^[k] p):= by
  induction k with
  | zero =>intro p; rfl
  | succ k ih =>
    intro p
    have:tqT q N pi pj τ (tqE s p)=tqE s (tqS (q s) (N s) (pi s) (pj s) (τ s) p):= by
      simp [tqT,tqE,unpairB_pairB,decV_encV]
    rw [iter_succ,iter_succ,this,ih]
theorem tqinv (q N:ℕ) (pi pj τ:NVec) (hq:0< q) (k:ℕ) :
    ((tqS q N pi pj τ)^[k] (0,e0 q N)).1=k∧((tqS q N pi pj τ)^[k] (0,e0 q N)).2.length=2 ^ N
     ∧∀ a∈((tqS q N pi pj τ)^[k] (0,e0 q N)).2,a< q:= by
  induction k with
  | zero =>
    refine ⟨rfl,by simp [e0],fun a ha =>?_⟩
    simp only [Function.iterate_zero,id,e0,mem_mapL,List.mem_range] at ha
    obtain ⟨J,-,rfl⟩:= ha
    split_ifs <;> simp [Nat.mod_lt _ hq,hq]
  | succ k ih =>
    rw [iter_succ']
    refine ⟨by simp [tqS,ih.1],by simp [tqS,wedgeV],fun a ha =>?_⟩
    simp only [tqS,wedgeV,mem_mapL,List.mem_range] at ha
    obtain ⟨J,-,rfl⟩:= ha
    exact Nat.mod_lt _ hq
theorem vecR_wedgeLab {q N:BitTape→ ℕ} {pi pj τ:BitTape→ NVec} (hq:NatR q)
    (hq0:∀ s,0< q s) (hN:NatR N) (hP:NatR (fun s =>2 ^ N s)) (hi:VecR pi)
    (hj:VecR pj) (ht:VecR τ):VecR (fun s =>wedgeLab (q s) (N s) (pi s) (pj s) (τ s)):= by
  have hT:Lib.CPTs (tqT q N pi pj τ):= by
    have:= tqzN hq; have:= tqzN hN; have:= tqzN hP; have:= tqzV hi; have:= tqzV hj; have:= tqzV ht
    unfold tqT tqE tqS; dsimp only
    apply_rules (maxDepth:= 500) (transparency:= .reducible) [cpt_pairB2,tqcN,tqcV,vecR_wedgeV,vecR_vv,vecR_dec,
      natR_get,natR_add,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1,cpt_unpairB1_1]
    all_goals exact fun _ =>hq0 _
  have hA:Lib.CPTs (fun s =>tqE s (0,e0 (q s) (N s))):= by
    unfold tqE; dsimp only
    apply_rules (maxDepth:= 500) (transparency:= .reducible) [cpt_pairB2,tqcN,tqcV,vecR_e0,natR_const,
      Lib.Machines.cpt_id]
  obtain ⟨Pt,ht'⟩:= natR_le_poly (natR_vlen ht)
  obtain ⟨PP,hP'⟩:= natR_le_poly hP
  obtain ⟨Pq,hq'⟩:= natR_le_poly hq
  have:= cpt_iterBound hT (natR_vlen ht) hA
    (Polynomial.C 2 * Pt+Polynomial.C 2 * (PP+PP * Pq)+Polynomial.X+Polynomial.C 2) (by
      intro s i hi'
      obtain ⟨h1,h4,h2⟩:= tqinv (q s) (N s) (pi s) (pj s) (τ s) (hq0 s) i
      have h3:= List.sum_le_length_nsmul _ (q s) (fun a ha =>(h2 a ha).le)
      have h5:= Nat.mul_le_mul (hP' s) (hq' s)
      have h6:= ht' s; have h7:= hP' s
      simp only [un_length] at hi'
      rw [h4] at h3; rw [tqit]
      simp only [tqE,pairB_length,un_length,encV_length,smul_eq_mul,evalAddP,
        evalMulP,evalCP,evalXP] at *
      linarith)
  refine cptE (vecR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 this))) (fun s =>?_)
  have e:wedgeLab (q s) (N s) (pi s) (pj s) (τ s) =
    ((tqS (q s) (N s) (pi s) (pj s) (τ s))^[(τ s).length] (0,e0 (q s) (N s))).2:= rfl
  dsimp only; rw [e,tqit]; simp only [un_length,tqE,unpairB_pairB,decV_encV]
theorem natR_chi {F:BitTape→ NMat} {τ:BitTape→ NVec} {r:BitTape→ ℕ}
    (hF:LLR F) (ht:VecR τ) (hr:NatR r):NatR (fun s =>chi (F s) (τ s) (r s)):= by
  have:= tqzL hF; have:= tqzV ht; have:= tqzN hr; unfold chi
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqnE,natR_sum,tqgN,natR_sub,natR_get,vecR_row,
    natR_vlen,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_vecL {q N:BitTape→ ℕ} {pi pj τ:BitTape→ NVec}
    {F:BitTape→ NMat} (hq:NatR q) (hq0:∀ s,0< q s) (hN:NatR N)
    (hP:NatR (fun s =>2 ^ N s)) (hi:VecR pi) (hj:VecR pj) (hF:LLR F) (ht:VecR τ) :
    VecR (fun s =>vecL (q s) (N s) (pi s) (pj s) (F s) (τ s)):= by
  have:= tqzN hq; have:= tqzN hN; have:= tqzN hP; have:= tqzV hi; have:= tqzV hj; have:= tqzL hF
  have:= tqzV ht
  have:∀ ⦃p:BitTape→ BitTape⦄,∀ s,0< q (p s):= fun _ s =>hq0 _
  unfold vecL
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,natR_mod,natR_mul,natR_get,natR_div,natR_llen,
    vecR_wedgeLab,natR_chi,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_posC {F:BitTape→ NMat} {fs τ:BitTape→ NVec} (hF:LLR F)
    (hf:VecR fs) (ht:VecR τ):NatR (fun s =>posC (F s) (fs s) (τ s)):= by
  have:= tqzL hF; have:= tqzV hf; have:= tqzV ht; unfold posC
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [natR_sum,tqgN,natR_mul,natR_get,natR_llen,natR_chi,
    tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_negC {F:BitTape→ NMat} {fs τ:BitTape→ NVec} (hF:LLR F)
    (hf:VecR fs) (ht:VecR τ):NatR (fun s =>negC (F s) (fs s) (τ s)):= by
  have:= tqzL hF; have:= tqzV hf; have:= tqzV ht; unfold negC
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [natR_sum,tqgN,natR_mul,natR_sub,natR_const,natR_get,
    natR_llen,natR_chi,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem vecR_ends {pi pj τ:BitTape→ NVec} (hi:VecR pi) (hj:VecR pj) (ht:VecR τ) :
    VecR (fun s =>ends (pi s) (pj s) (τ s)):= by
  have:= tqzV hi; have:= tqzV hj; have:= tqzV ht; unfold ends
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqgN,natR_mul,natR_vlen,tqnE,natR_mod,natR_div,
    natR_get,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
theorem natR_hit {pi pj fs τ:BitTape→ NVec} {F:BitTape→ NMat} (hi:VecR pi)
    (hj:VecR pj) (hF:LLR F) (hf:VecR fs) (ht:VecR τ) :
    NatR (fun s =>hit (pi s) (pj s) (F s) (fs s) (τ s)):= by
  have:= tqzV hi; have:= tqzV hj; have:= tqzL hF; have:= tqzV hf; have:= tqzV ht; unfold hit clash
  apply_rules (maxDepth:= 500) (transparency:= .reducible) [tqnE,tqnL,natR_posC,natR_negC,natR_sum,tqgN,natR_get,
    natR_vlen,vecR_ends,natR_const,tqzI,Lib.Machines.cpt_id,cpt_unpairB2_1]
end Alg
end PT
namespace PT
namespace Alg
open Lib.R Lib.Universal
theorem tcC {f h:TapeMap} (hf:Lib.CPTs f) (hh:Lib.CPTs h) :
    Lib.CPTs (fun s =>f (h s)):= Lib.Machines.cpt_comp hh hf
theorem tcn1 {a:BitTape→ ℕ} (h:NatR a):NatR (fun t =>a (unpairB t).1):= tcC h cpt_unpairB1
theorem tcn2 {a:BitTape→ ℕ} (h:NatR a):NatR (fun t =>a (unpairB t).2):= tcC h cpt_unpairB2
theorem tcv1 {a:BitTape→ NVec} (h:VecR a):VecR (fun t =>a (unpairB t).1):= tcC h cpt_unpairB1
theorem tcv2 {a:BitTape→ NVec} (h:VecR a):VecR (fun t =>a (unpairB t).2):= tcC h cpt_unpairB2
theorem tcl1 {a:BitTape→ NMat} (h:LLR a):LLR (fun t =>a (unpairB t).1) :=
  tcC h cpt_unpairB1
theorem tcl2 {a:BitTape→ NMat} (h:LLR a):LLR (fun t =>a (unpairB t).2) :=
  tcC h cpt_unpairB2
theorem tci:NatR (fun t =>(unpairB t).1.length):= natR_len cpt_unpairB1
theorem tci2:NatR (fun t =>(unpairB (unpairB t).2).1.length):= natR_len (cpt_unpairB1_1 cpt_unpairB2)
theorem tcNI {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if a s=b s then x s else y s) :=
  Lib.Loop.cptE (cpt_ite_eq ha hb hx hy) (fun s =>(apply_ite un _ _ _).symm)
theorem tcNL {a b x y:BitTape→ ℕ} (ha:NatR a) (hb:NatR b) (hx:NatR x) (hy:NatR y) :
    NatR (fun s =>if a s< b s then x s else y s) :=
  Lib.Loop.cptE (cpt_ite_lt ha hb hx hy) (fun s =>(apply_ite un _ _ _).symm)
theorem tcLI {a b:BitTape→ ℕ} {x y:BitTape→ NMat} (ha:NatR a) (hb:NatR b)
    (hx:LLR x) (hy:LLR y):LLR (fun s =>if a s=b s then x s else y s) :=
  Lib.Loop.cptE (cpt_ite_eq ha hb hx hy) (fun s =>(apply_ite encLL _ _ _).symm)
theorem tc_unl (n:ℕ):(un n).length=n:= by simp [un]
theorem tc_dbl (w:BitTape):(dbl w).length=2 * w.length:= by
  induction w with
  | nil =>rfl
  | cons b w ih =>
    simp only [dbl,List.flatMap_cons,len_app,len_cons,len_nil] at *
    omega
theorem tc_ell (S:NMat) :
    (encLL S).length=(S.map (fun v =>2 * (encV v).length+1)).sum:= by
  induction S with
  | nil =>rfl
  | cons v S ih =>
    simp only [encLL,List.flatMap_cons,len_app,len_cons,tc_dbl,mapC,
      List.sum_cons] at *
    omega
theorem tc_ellm {S:NMat} {v:NVec} (h:v∈S) :
    (encV v).length≤ (encLL S).length:= by
  rw [tc_ell]
  have:= List.le_sum_of_mem (List.mem_map_of_mem (f:= fun v =>2 * (encV v).length+1) h)
  omega
theorem tc_elle {S:NMat} {M:ℕ} (h:∀ v∈S,(encV v).length≤ M) :
    (encLL S).length≤ S.length * (2 * M+1):= by
  rw [tc_ell]
  have:= List.sum_le_length_nsmul (S.map (fun v =>2 * (encV v).length+1)) (2 * M+1)
    (by simp only [mem_mapL]; rintro _ ⟨v,hv,rfl⟩; have:= h v hv; omega)
  simpa using this
theorem tc_sumle {l:NVec} {q:ℕ} (h:∀ a∈l,a≤ q):l.sum≤ l.length * q:= by
  have:= List.sum_le_length_nsmul l q h; simpa using this
theorem tc_evle {v:NVec} {M:ℕ} (h:∀ a∈v,a≤ M):(encV v).length≤ v.length * (M+1):= by
  rw [encV_length,Nat.mul_succ]; have:= tc_sumle h; omega
theorem tc_itinv {α:Type} (F:ℕ × α→ ℕ × α) (P:α→ Prop) (x:ℕ × α) (h0:P x.2)
    (hs:∀ y,P y.2→ P (F y).2) (i:ℕ):P (F^[i] x).2:= by
  induction i with
  | zero =>exact h0
  | succ i ih =>rw [iter_succ']; exact hs _ ih
theorem tc_isnd {α:Type} (h:α→ α) (k n:ℕ) (a:α) :
    ((fun p:ℕ × α =>(p.1+1,h p.2))^[k] (n,a)).2=h^[k] a:= by
  induction k generalizing n a with
  | zero =>rfl
  | succ k ih =>rw [iter_succ,iter_succ,ih]
def tcG {α:Type} (E:α→ BitTape) (D:BitTape→ α) (f:BitTape→ ℕ→ α→ α)
    (t:BitTape):BitTape :=
  pairB (unpairB t).1 (pairB (true :: (unpairB (unpairB t).2).1)
    (E (f (unpairB t).1 (unpairB (unpairB t).2).1.length (D (unpairB (unpairB t).2).2))))
theorem tc_lp {α:Type} (E:α→ BitTape) (D:BitTape→ α) (hD:∀ a,D (E a)=a)
    (f:BitTape→ ℕ→ α→ α) (k:BitTape→ ℕ) (a0:BitTape→ α)
    (hf:Lib.CPTs (fun t =>E (f (unpairB t).1 (unpairB (unpairB t).2).1.length
      (D (unpairB (unpairB t).2).2))))
    (hk:NatR k) (ha:Lib.CPTs (fun u =>E (a0 u))) (B:BitTape→ ℕ) (hB:NatR B)
    (hb:∀ u i,i≤ k u →
      (E ((fun p:ℕ × α =>(p.1+1,f u p.1 p.2))^[i] (0,a0 u)).2).length≤ B u) :
    Lib.CPTs (fun u =>E ((fun p:ℕ × α =>(p.1+1,f u p.1 p.2))^[k u] (0,a0 u)).2):= by
  have hg:Lib.CPTs (tcG E D f) :=
    cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_cons1 true (cpt_unpairB1_1 cpt_unpairB2)) hf)
  have h1:∀ u i,((fun p:ℕ × α =>(p.1+1,f u p.1 p.2))^[i] (0,a0 u)).1=i:= by
    intro u i
    induction i with
    | zero =>rfl
    | succ i ih =>rw [iter_succ',ih]
  have h2:∀ u i,(tcG E D f)^[i] (pairB u (pairB [] (E (a0 u)))) =
      pairB u (pairB (un i) (E ((fun p:ℕ × α =>(p.1+1,f u p.1 p.2))^[i] (0,a0 u)).2)):= by
    intro u i
    induction i with
    | zero =>rfl
    | succ i ih =>
      rw [iter_succ',ih,iter_succ']
      simp only [tcG,unpairB_pairB,hD,tc_unl,h1]
      rfl
  obtain ⟨P,hP⟩:= natR_le_poly (natR_add (natR_add (natR_mul (natR_const 2)
    (natR_len Lib.Machines.cpt_id)) (natR_mul (natR_const 2) hk)) (natR_add hB (natR_const 2)))
  have hI:= cpt_iterBound hg hk (cpt_pairB2 Lib.Machines.cpt_id (cpt_pairB2 (cpt_const []) ha)) P
    (by
      intro u i hi
      rw [tc_unl] at hi
      rw [h2]
      simp only [pairB_length,tc_unl]
      have:= hb u i hi
      have:= hP u
      beta_reduce at this
      omega)
  refine Lib.Loop.cptE (cpt_unpairB2_1 (cpt_unpairB2_1 hI)) (fun u =>?_)
  rw [tc_unl,h2]
  simp only [unpairB_pairB]
theorem tc_red1 {q p:BitTape→ ℕ} {v b:BitTape→ NVec} (hq:NatR q) (hv:VecR v)
    (hb:VecR b) (hp:NatR p):VecR (fun s =>red1 (q s) (v s) (b s) (p s)) :=
  vecR_gen (A:= fun s =>s) (n:= fun s =>(v s).length)
    (G:= fun i s =>(g (b s) (p s) * g (v s) i+(q s - g (v s) (p s)) * g (b s) i) % q s)
    Lib.Machines.cpt_id (natR_vlen hv)
    (natR_mod (natR_add (natR_mul (natR_get (tcv2 hb) (tcn2 hp)) (natR_get (tcv2 hv) tci))
      (natR_mul (natR_sub (tcn2 hq) (natR_get (tcv2 hv) (tcn2 hp))) (natR_get (tcv2 hb) tci)))
      (tcn2 hq))
theorem tc_red1l (q:ℕ) (v b:NVec) (p:ℕ):(red1 q v b p).length=v.length:= by
  simp [red1]
theorem tc_red1lt {q:ℕ} (hq:0< q) (v b:NVec) (p:ℕ):∀ a∈red1 q v b p,a< q:= by
  simp only [red1,mem_mapL]; rintro _ ⟨i,-,rfl⟩; exact Nat.mod_lt _ hq
theorem tc_redAll {q:BitTape→ ℕ} {B:BitTape→ NMat} {pv v:BitTape→ NVec}
    (hq:NatR q) (hq0:∀ s,0< q s) (hB:LLR B) (hpv:VecR pv) (hv:VecR v) :
    VecR (fun s =>redAll (q s) (B s) (pv s) (v s)) :=
  tc_lp encV decV decV_encV (fun u i w =>red1 (q u) w (gg (B u) i) (g (pv u) i))
    (fun u =>(B u).length) v
    (tc_red1 (tcn1 hq) (vecR_dec (cpt_unpairB2_1 cpt_unpairB2)) (vecR_row (tcl1 hB) tci2)
      (natR_get (tcv1 hpv) tci2))
    (natR_llen hB) hv (fun u =>(v u).length+(v u).sum+(v u).length * q u)
    (natR_add (natR_add (natR_vlen hv) (natR_sum hv)) (natR_mul (natR_vlen hv) hq))
    (fun u i _ => by
      obtain ⟨h1,h2 | h2⟩:= tc_itinv (fun p:ℕ × NVec =>(p.1+1,red1 (q u) p.2 (gg (B u) p.1) (g (pv u) p.1)))
        (fun w =>w.length=(v u).length∧(w=v u∨∀ a∈w,a< q u)) (0,v u) ⟨rfl,Or.inl rfl⟩ (fun y hy =>⟨(tc_red1l _ _ _ _).trans hy.1,Or.inr (tc_red1lt (hq0 u) _ _ _)⟩) i
      · rw [h2,encV_length]; omega
      · have:= tc_sumle (fun a ha =>(h2 a ha).le); rw [h1] at this; rw [encV_length,h1]; omega)
def tcE (st:ESt):BitTape:= pairB (encLL st.B) (pairB (encV st.pv) (encLL st.sl))
def tcD (t:BitTape):ESt :=
  ⟨decLL (unpairB t).1,decV (unpairB (unpairB t).2).1,decLL (unpairB (unpairB t).2).2⟩
theorem tcDE (st:ESt):tcD (tcE st)=st:= by
  cases st; simp only [tcD,tcE,unpairB_pairB,decV_encV,decLL_encLL]
theorem tc_ins {q:BitTape→ ℕ} {st:BitTape→ ESt} {vec:BitTape→ NVec→ NVec}
    {τ:BitTape→ NVec} (hq:NatR q) (hq0:∀ s,0< q s) (hB:LLR (fun s =>(st s).B))
    (hp:VecR (fun s =>(st s).pv)) (hl:LLR (fun s =>(st s).sl)) (ht:VecR τ)
    (hw:VecR (fun s =>vec s (τ s))) :
    Lib.CPTs (fun s =>tcE (insertG (q s) (vec s) (st s) (τ s))):= by
  have hr:= tc_redAll hq hq0 hB hp hw
  refine Lib.Loop.cptE (cpt_ite_eq (natR_sum hr) (natR_const 0) (cpt_pairB2 hB (cpt_pairB2 hp hl))
    (cpt_pairB2 (llR_append hB (llR_single hr)) (cpt_pairB2 (vecR_append hp
      (vecR_single (natR_firstNZ hr))) (llR_append hl (llR_single ht))))) (fun s =>?_)
  simp only [insertG]; split_ifs <;> rfl
theorem tc_vecLl (q N:ℕ) (pi pj:NVec) (F:NMat) (τ:NVec) :
    (vecL q N pi pj F τ).length=2 ^ N * F.length:= by simp [vecL]
theorem tc_vecLlt {q:ℕ} (hq:0< q) (N:ℕ) (pi pj:NVec) (F:NMat) (τ:NVec) :
    ∀ a∈vecL q N pi pj F τ,a< q:= by
  simp only [vecL,mem_mapL]; rintro _ ⟨k,-,rfl⟩; exact Nat.mod_lt _ hq
theorem tc_sel {q N:BitTape→ ℕ} {pi pj:BitTape→ NVec} {F C:BitTape→ NMat}
    (hq:NatR q) (hq0:∀ s,0< q s) (hN:NatR N) (hP:NatR (fun s =>2 ^ N s))
    (hi:VecR pi) (hj:VecR pj) (hF:LLR F) (hC:LLR C) :
    LLR (fun s =>selectE (q s) (N s) (pi s) (pj s) (F s) (C s)):= by
  have hL:= tc_lp tcE tcD tcDE
    (fun u i st =>insertG (q u) (vecL (q u) (N u) (pi u) (pj u) (F u)) st (gg (C u) i))
    (fun u =>(C u).length) (fun _ =>⟨[],[],[]⟩)
    (tc_ins (st:= fun t =>tcD (unpairB (unpairB t).2).2)
      (vec:= fun t w =>vecL (q (unpairB t).1) (N (unpairB t).1) (pi (unpairB t).1) (pj (unpairB t).1)
        (F (unpairB t).1) w) (τ:= fun t =>gg (C (unpairB t).1) (unpairB (unpairB t).2).1.length)
      (tcn1 hq) (fun _ =>hq0 _)
      (llR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)))
      (vecR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))))
      (llR_dec (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))))
      (vecR_row (tcl1 hC) tci2)
      (vecR_vecL (tcn1 hq) (fun _ =>hq0 _) (tcn1 hN) (tcn1 hP) (tcv1 hi) (tcv1 hj) (tcl1 hF)
        (vecR_row (tcl1 hC) tci2)))
    (natR_llen hC) (cpt_const (tcE ⟨[],[],[]⟩))
    (fun u =>2 * (2 ^ N u * (F u).length * (2 * (2 ^ N u * (F u).length +
        2 ^ N u * (F u).length * q u)+1))+(2 * (2 ^ N u * (F u).length +
        2 ^ N u * (F u).length * (2 ^ N u * (F u).length)) +
        2 ^ N u * (F u).length * (2 * (encLL (C u)).length+1)+1)+1)
    (natR_add (natR_add (natR_mul (natR_const 2) (natR_mul (natR_mul hP (natR_llen hF))
      (natR_add (natR_mul (natR_const 2) (natR_add (natR_mul hP (natR_llen hF))
        (natR_mul (natR_mul hP (natR_llen hF)) hq))) (natR_const 1))))
      (natR_add (natR_add (natR_mul (natR_const 2) (natR_add (natR_mul hP (natR_llen hF))
        (natR_mul (natR_mul hP (natR_llen hF)) (natR_mul hP (natR_llen hF)))))
        (natR_mul (natR_mul hP (natR_llen hF)) (natR_add (natR_mul (natR_const 2)
          (natR_len hC)) (natR_const 1)))) (natR_const 1))) (natR_const 1))
    (fun u i hi => by
      obtain ⟨-,h1,h2,h3,h4,h5,h6⟩:= selStep_inv (q u) (hq0 u)
        (vecL (q u) (N u) (pi u) (pj u) (F u)) _ (tc_vecLl _ _ _ _ _) (tc_vecLlt (hq0 u) _ _ _ _)
        (C u) i hi
      show (tcE ((selStep (q u) (vecL (q u) (N u) (pi u) (pj u) (F u)) (C u))^[i]
        (0,⟨[],[],[]⟩)).2).length≤ _
      generalize ((selStep (q u) (vecL (q u) (N u) (pi u) (pj u) (F u)) (C u))^[i]
        (0,⟨[],[],[]⟩)).2=st at h1 h2 h3 h4 h5 h6 ⊢
      generalize 2 ^ N u * (F u).length=D at *
      have x1:(encLL st.B).length≤ D * (2 * (D+D * q u)+1) :=
        (tc_elle (M:= D+D * q u) (fun b hb => by
          rw [encV_length,(h4 b hb).1]
          have:= tc_sumle (fun a ha =>((h4 b hb).2 a ha).le); rw [(h4 b hb).1] at this; omega)).trans
          (Nat.mul_le_mul_right _ h1)
      have x2:(encV st.pv).length≤ D+D * D:= by
        rw [encV_length]
        have:= tc_sumle (fun a ha =>(h5 a ha).le)
        have:= Nat.mul_le_mul_right D (h2.trans_le h1)
        omega
      have x3:(encLL st.sl).length≤ D * (2 * (encLL (C u)).length+1) :=
        (tc_elle (fun v hv =>tc_ellm (h6 v hv))).trans (Nat.mul_le_mul_right _ (h3.trans_le h1))
      simp only [tcE,pairB_length]
      omega)
  exact Lib.Loop.cptE (cpt_unpairB2_1 (cpt_unpairB2_1 hL)) (fun u => by
    simp only [tcE,unpairB_pairB]; rfl)
theorem tc_cand {U:BitTape→ NVec} {S:BitTape→ NMat} (hU:VecR U) (hS:LLR S) :
    LLR (fun s =>cand (U s) (S s)) :=
  llR_flat (A:= fun s =>s) (n:= fun s =>(S s).length)
    (H:= fun j s =>(List.range (U s).length).map (fun k =>gg (S s) j ++ [g (U s) k]))
    Lib.Machines.cpt_id (natR_llen hS)
    (llR_gen (A:= fun t =>t) (n:= fun t =>(U (unpairB t).2).length)
      (H:= fun k t =>gg (S (unpairB t).2) (unpairB t).1.length ++ [g (U (unpairB t).2) k])
      Lib.Machines.cpt_id (natR_vlen (tcv2 hU))
      (vecR_append (vecR_row (tcl2 (tcl2 hS)) tci2) (vecR_single (natR_get (tcv2 (tcv2 hU)) tci))))
theorem tc_hits {pi pj fs:BitTape→ NVec} {F C:BitTape→ NMat} (hi:VecR pi)
    (hj:VecR pj) (hF:LLR F) (hf:VecR fs) (hC:LLR C) :
    LLR (fun s =>hits (pi s) (pj s) (F s) (fs s) (C s)) :=
  llR_flat (A:= fun s =>s) (n:= fun s =>(C s).length)
    (H:= fun j s =>if hit (pi s) (pj s) (F s) (fs s) (gg (C s) j)=0 then [] else [gg (C s) j])
    Lib.Machines.cpt_id (natR_llen hC)
    (tcLI (natR_hit (tcv2 hi) (tcv2 hj) (tcl2 hF) (tcv2 hf) (vecR_row (tcl2 hC) tci))
      (natR_const 0) llR_nil (llR_single (vecR_row (tcl2 hC) tci)))
def tcE2 (p:NMat × NMat):BitTape:= pairB (encLL p.1) (encLL p.2)
def tcD2 (t:BitTape):NMat × NMat:= (decLL (unpairB t).1,decLL (unpairB t).2)
theorem tcDE2 (p:NMat × NMat):tcD2 (tcE2 p)=p:= by
  simp [tcD2,tcE2,unpairB_pairB,decLL_encLL]
theorem tc_lvl {q N:BitTape→ ℕ} {pi pj U fs:BitTape→ NVec} {F:BitTape→ NMat}
    {st:BitTape→ NMat × NMat} (hq:NatR q) (hq0:∀ s,0< q s) (hN:NatR N)
    (hP:NatR (fun s =>2 ^ N s)) (hi:VecR pi) (hj:VecR pj) (hU:VecR U) (hF:LLR F)
    (hf:VecR fs) (h1:LLR (fun s =>(st s).1)) (h2:LLR (fun s =>(st s).2)) :
    Lib.CPTs (fun s =>tcE2 (lvl (q s) (N s) (pi s) (pj s) (U s) (F s) (fs s) (st s))):= by
  have hH:= tc_hits hi hj hF hf h1
  refine Lib.Loop.cptE (cpt_ite_eq (natR_llen h2) (natR_const 0) (cpt_ite_eq (natR_llen hH)
    (natR_const 0) (cpt_pairB2 (tc_cand hU (tc_sel hq hq0 hN hP hi hj hF h1)) llR_nil)
    (cpt_pairB2 h1 (llR_single (vecR_row hH (natR_const 0))))) (cpt_pairB2 h1 h2)) (fun s =>?_)
  simp only [lvl]; split_ifs <;> rfl
theorem tc_ggm {C:NMat} {j:ℕ} (h:j< C.length):gg C j∈C:= by
  simp [gg,getOptEq h,at_mem]
theorem tc_gm {U:NVec} {j:ℕ} (h:j< U.length):g U j∈U:= by
  simp [g,getOptEq h,at_mem]
theorem tc_hm {pi pj fs:NVec} {F C:NMat} {x:NVec} (h:x∈hits pi pj F fs C) :
    x∈C:= by
  simp only [hits,List.mem_flatMap,List.mem_range] at h
  obtain ⟨j,hj,hx⟩:= h
  split_ifs at hx
  · simp at hx
  · rw [mem_one] at hx; rw [hx]; exact tc_ggm hj
theorem tc_candl (U:NVec) (S:NMat):(cand U S).length=S.length * U.length:= by
  simp [cand,List.length_flatMap]
theorem tc_candm {U:NVec} {S:NMat} {τ:NVec} (h:τ∈cand U S) :
    ∃ j< S.length,∃ k< U.length,τ=gg S j ++ [g U k]:= by
  simp only [cand,List.mem_flatMap,mem_mapL,List.mem_range] at h
  obtain ⟨j,hj,k,hk,rfl⟩:= h
  exact ⟨j,hj,k,hk,rfl⟩
theorem tc_lvlinv (q N:ℕ) (hq:0< q) (pi pj U:NVec) (F:NMat) (fs:NVec)
    (i:ℕ) :
    ((lvl q N pi pj U F fs)^[i] ([[]],[])).1.length≤ 1+2 ^ N * F.length * U.length ∧
    (∀ τ∈((lvl q N pi pj U F fs)^[i] ([[]],[])).1,τ.length≤ i∧∀ e∈τ,e∈U) ∧
    (∀ τ∈((lvl q N pi pj U F fs)^[i] ([[]],[])).2,τ∈((lvl q N pi pj U F fs)^[i] ([[]],[])).1) ∧
    ((lvl q N pi pj U F fs)^[i] ([[]],[])).2.length≤ 1:= by
  induction i with
  | zero =>simp
  | succ i ih =>
    rw [iter_succ']
    generalize (lvl q N pi pj U F fs)^[i] ([[]],[])=st at ih
    obtain ⟨C,d⟩:= st
    obtain ⟨h1,h2,h3,h4⟩:= ih
    simp only [lvl,selectE]
    split_ifs with a b
    · refine ⟨?_,?_,by simp,by simp⟩
      · rw [tc_candl]
        have:= Nat.mul_le_mul_right U.length
          (selectG_length q hq (vecL q N pi pj F) _ (tc_vecLl q N pi pj F) (tc_vecLlt hq N pi pj F) C)
        omega
      · intro τ hτ
        obtain ⟨j,hj,k,hk,rfl⟩:= tc_candm hτ
        obtain ⟨l1,l2⟩:= h2 _ (selectG_sub q (vecL q N pi pj F) C _ (tc_ggm hj))
        refine ⟨by simp only [len_app,len_one]; omega,fun e he =>?_⟩
        rcases mem_app.1 he with he | he
        · exact l2 e he
        · rw [mem_one] at he; rw [he]; exact tc_gm hk
    · refine ⟨h1,fun τ hτ =>⟨(h2 τ hτ).1.trans (Nat.le_succ _),(h2 τ hτ).2⟩,?_,by simp⟩
      intro τ hτ; rw [mem_one] at hτ; rw [hτ]; exact tc_hm (tc_ggm (Nat.pos_of_ne_zero b))
    · exact ⟨h1,fun τ hτ =>⟨(h2 τ hτ).1.trans (Nat.le_succ _),(h2 τ hτ).2⟩,h3,h4⟩
def tcF (s:BitTape):NMat:= Frows (Pm s) (rowM s)
def tcS (s:BitTape):NVec:= Fsig (Pm s) (rowM s) (rowS s)
def tcK (s:BitTape):ℕ:= Nat.log2 (tcF s).length
def tcQ (s:BitTape):ℕ:= primeAbove (nV s+(tcF s).length)
def tcU (s:BitTape):NVec:= Uset (pI (nV s)) (pJ (nV s)) (Em s) (Pm s)
def tcL (s:BitTape):NMat × NMat→ NMat × NMat :=
  lvl (tcQ s) (2 * tcK s) (pI (nV s)) (pJ (nV s)) (tcU s) (tcF s) (tcS s)
theorem tc_fe (s:BitTape):found s=((tcL s)^[tcK s+1] ([[]],[])).2:= rfl
theorem tc_hF:LLR tcF:= llR_Frows vecR_Pm llR_rowM
theorem tc_hS:VecR tcS:= vecR_Fsig vecR_Pm llR_rowM vecR_rowS
theorem tc_hK:NatR tcK:= natR_log2 (natR_llen tc_hF)
theorem tc_hQ:NatR tcQ:= natR_primeAbove (natR_add natR_nV (natR_llen tc_hF))
theorem tc_hQ0 (s:BitTape):0< tcQ s:= by unfold tcQ primeAbove; omega
theorem tc_hN:NatR (fun s =>2 * tcK s):= natR_mul (natR_const 2) tc_hK
theorem tc_hU:VecR tcU:= vecR_Uset (vecR_pI natR_nV) (vecR_pJ natR_nV) vecR_Em vecR_Pm
theorem tc_hP:NatR (fun s =>2 ^ (2 * tcK s)):= by
  obtain ⟨Pf,hPf⟩:= natR_le_poly (natR_llen tc_hF)
  refine natR_pow2 tc_hN (Pf ^ 2+1) (fun s =>?_)
  have h1:= hPf s
  beta_reduce at h1 ⊢
  rw [evalAddP,Polynomial.eval_pow,Polynomial.eval_one,pow_mul']
  rcases Nat.eq_zero_or_pos (tcF s).length with h | h
  · simp [tcK,h]
  · have h2:= Nat.pow_le_pow_left ((Nat.log2_self_le h.ne').trans h1) 2
    unfold tcK; omega
theorem tc_hL:Lib.CPTs (fun t =>tcE2 (tcL (unpairB t).1 (tcD2 (unpairB (unpairB t).2).2))) :=
  tc_lvl (st:= fun t =>tcD2 (unpairB (unpairB t).2).2) (tcn1 tc_hQ) (fun _ =>tc_hQ0 _)
    (tcn1 (a:= fun s =>2 * tcK s) tc_hN) (tcn1 (a:= fun s =>2 ^ (2 * tcK s)) tc_hP)
    (tcv1 (a:= fun s =>pI (nV s)) (vecR_pI natR_nV)) (tcv1 (a:= fun s =>pJ (nV s)) (vecR_pJ natR_nV))
    (tcv1 tc_hU)
    (tcl1 tc_hF) (tcv1 tc_hS)
    (llR_dec (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)))
    (llR_dec (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)))
def tcBd (u:BitTape):ℕ:= 3 * ((1+2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length) *
  (2 * ((tcK u+1) * ((tcU u).sum+1))+1))+1
theorem tc_hBd:NatR tcBd:= natR_add (
  natR_mul (natR_const 3) (natR_mul (natR_add (natR_const 1) (natR_mul (natR_mul tc_hP
    (natR_llen tc_hF)) (natR_vlen tc_hU))) (natR_add (natR_mul (natR_const 2) (natR_mul
    (natR_add tc_hK (natR_const 1)) (natR_add (natR_sum tc_hU) (natR_const 1)))) (natR_const 1)))) (natR_const 1)
theorem tc_fb (u:BitTape) (i:ℕ) (hi:i≤ tcK u+1) :
    (tcE2 ((tcL u)^[i] ([[]],[]))).length≤ tcBd u:= by
  obtain ⟨h1,h2,h3,h4⟩:= tc_lvlinv (tcQ u) (2 * tcK u) (tc_hQ0 u) (pI (nV u)) (pJ (nV u))
    (tcU u) (tcF u) (tcS u) i
  change _≤ 3 * ((1+2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length) *
    (2 * ((tcK u+1) * ((tcU u).sum+1))+1))+1
  have hX:= Nat.le_add_right 1 (2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length)
  unfold tcL
  generalize (lvl (tcQ u) (2 * tcK u) (pI (nV u)) (pJ (nV u)) (tcU u) (tcF u) (tcS u))^[i]
    ([[]],[])=st at h1 h2 h3 h4 ⊢
  have hM:∀ τ∈st.1,(encV τ).length≤ (tcK u+1) * ((tcU u).sum+1):= fun τ hτ =>
    (tc_evle (fun a ha =>List.le_sum_of_mem ((h2 τ hτ).2 a ha))).trans
      (Nat.mul_le_mul_right _ (((h2 τ hτ).1).trans hi))
  have x1:= (tc_elle hM).trans (Nat.mul_le_mul_right _ h1)
  have x2:= (tc_elle (fun τ hτ =>hM τ (h3 τ hτ))).trans (Nat.mul_le_mul_right _ h4)
  simp only [tcE2,pairB_length]
  generalize (1+2 ^ (2 * tcK u) * (tcF u).length * (tcU u).length)=X at *
  generalize (2 * ((tcK u+1) * ((tcU u).sum+1))+1)=Y at *
  nlinarith
theorem tc_found:LLR (fun s =>found s):= by
  have hL:= tc_lp tcE2 tcD2 tcDE2 (fun u _ st =>tcL u st) (fun u =>tcK u+1) (fun _ =>([[]],[]))
    tc_hL (natR_add tc_hK (natR_const 1)) (cpt_const (tcE2 ([[]],[]))) tcBd tc_hBd
    (fun u i hi => by rw [tc_isnd]; exact tc_fb u i hi)
  exact Lib.Loop.cptE (cpt_unpairB2_1 hL) (fun u => by
    beta_reduce; rw [tc_fe,tcE2,unpairB_pairB,tc_isnd])
theorem tc_oA {τ:BitTape→ NVec} (ht:VecR τ):VecR (fun s =>(List.range (pN s)).map
    (fun k =>g (Pm s) k+((List.range (τ s).length).map (fun i =>if g (τ s) i=k then 1 else 0)).sum)) :=
  vecR_gen (A:= fun s =>s) (n:= pN) (G:= fun k s =>g (Pm s) k +
    ((List.range (τ s).length).map (fun i =>if g (τ s) i=k then 1 else 0)).sum)
    Lib.Machines.cpt_id natR_pN
    (natR_add (natR_get (tcv2 vecR_Pm) tci) (natR_sum (vecR_gen (A:= fun t =>t)
      (n:= fun t =>(τ (unpairB t).2).length)
      (G:= fun i t =>if g (τ (unpairB t).2) i=(unpairB t).1.length then 1 else 0)
      Lib.Machines.cpt_id (natR_vlen (tcv2 ht))
      (tcNI (natR_get (tcv2 (tcv2 ht)) tci) tci2 (natR_const 1) (natR_const 0)))))
def tcA (s:BitTape) (τ:NVec):ℕ:= posC (tcF s) (tcS s) τ
def tcB (s:BitTape) (τ:NVec):ℕ:= negC (tcF s) (tcS s) τ
theorem tc_oc {τ:BitTape→ NVec} (ht:VecR τ) :
    NatR (fun s =>(tcA s (τ s) - tcB s (τ s))+(tcB s (τ s) - tcA s (τ s))) :=
  natR_add (natR_sub (natR_posC tc_hF tc_hS ht) (natR_negC tc_hF tc_hS ht))
    (natR_sub (natR_negC tc_hF tc_hS ht) (natR_posC tc_hF tc_hS ht))
theorem tc_oB {τ:BitTape→ NVec} (ht:VecR τ):VecR (fun s =>(List.range ((lenV s).log2+1)).map
    (fun i =>if ((tcA s (τ s) - tcB s (τ s))+(tcB s (τ s) - tcA s (τ s))).testBit i then 1 else 0)) :=
  vecR_gen (A:= fun s =>s) (n:= fun s =>(lenV s).log2+1) (G:= fun i s =>
    if ((tcA s (τ s) - tcB s (τ s))+(tcB s (τ s) - tcA s (τ s))).testBit i then 1 else 0)
    Lib.Machines.cpt_id (natR_add (natR_log2 natR_lenV) (natR_const 1))
    (natR_testBit (tcn2 (a:= fun s =>(tcA s (τ s) - tcB s (τ s))+(tcB s (τ s) - tcA s (τ s)))
      (tc_oc ht)) tci)
theorem tc_e2 (c:Prop) [Decidable c]:decide ((if c then 1 else 0) ≠ 0)=decide c:= by
  by_cases h:c <;> simp [h]
theorem tc_oe (s:BitTape) (τ:NVec):outBits s τ=[true] ++
    ((List.range (pN s)).map (fun k =>g (Pm s) k +
      ((List.range τ.length).map (fun i =>if g τ i=k then 1 else 0)).sum)).map (fun a =>decide (a ≠ 0)) ++
    [if tcA s τ< tcB s τ then 1 else 0].map (fun a =>decide (a ≠ 0)) ++
    ((List.range ((lenV s).log2+1)).map (fun i =>if ((tcA s τ - tcB s τ)+(tcB s τ - tcA s τ)).testBit i
      then 1 else 0)).map (fun a =>decide (a ≠ 0)):= by
  simp only [mapMap,mapC,mapN,Function.comp_def,tc_e2]
  rfl
theorem tc_out {τ:BitTape→ NVec} (ht:VecR τ):Lib.CPTs (fun s =>outBits s (τ s)) :=
  Lib.Loop.cptE (cpt_app2 (cpt_app2 (cpt_app2 (cpt_const [true]) (cpt_bitsOf (tc_oA ht)))
    (cpt_bitsOf (vecR_single (tcNL (natR_posC tc_hF tc_hS ht) (natR_negC tc_hF tc_hS ht)
      (natR_const 1) (natR_const 0))))) (cpt_bitsOf (tc_oB ht))) (fun s =>(tc_oe s (τ s)).symm)
end Alg
theorem cpt_solveV:Lib.CPTs Alg.solveV :=
  Lib.Loop.cptE (Lib.R.cpt_ite_eq (Lib.R.natR_llen Alg.tc_found) (Lib.R.natR_const 0)
    (Lib.Universal.cpt_const [false]) (Alg.tc_out (Lib.R.vecR_row Alg.tc_found (Lib.R.natR_const 0))))
    (fun _ =>rfl)
end PT
namespace PT
namespace Alg
theorem mn_rm {α β:Type*} (l:List α) (f:ℕ→ β) (h:α→ β)
    (H:∀ r (hr:r< l.length),f r=h l[r]):(List.range l.length).map f=l.map h:= by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [at_map,at_range]
  exact H i (by simpa using h1)
theorem mn_rfm {α β:Type*} (l:List α) (f:ℕ→ List β) (h:α→ List β)
    (H:∀ r (hr:r< l.length),f r=h l[r]):(List.range l.length).flatMap f=l.flatMap h:= by
  simp only [List.flatMap_def,mn_rm l f h H]
theorem mn_cnt {α:Type*} (l:List α) (p:α→ Bool) :
    (l.map (fun t =>if p t then 1 else 0)).sum=(l.filter p).length:= by
  induction l with
  | nil =>rfl
  | cons a l ih =>cases h:p a <;> simp [List.filter_cons,h,ih] <;> omega
theorem mn_flt {α β:Type*} (l:List α) (c:α→ Prop) [DecidablePred c] (f:α→ β) :
    l.flatMap (fun t =>if c t then [f t] else [])=(l.filter (fun t =>decide (c t))).map f:= by
  induction l with
  | nil =>rfl
  | cons a l ih => by_cases h:c a <;> simp [List.filter_cons,h,ih]
theorem mn_cntlt (c N:ℕ):((List.range N).map (fun i =>if i< c then 1 else 0)).sum=min c N:= by
  induction N with
  | zero =>simp
  | succ N ih =>rw [List.range_succ,List.map_append,List.sum_append,ih]; simp; split_ifs <;> omega
theorem mn_isPr (c:ℕ):isPr c ≠ 0 ↔ c.Prime:= by
  unfold isPr
  rw [Nat.prime_def_lt']
  split_ifs with h1 h2
  · simp; omega
  · rw [sumZeroList,List.forall_mem_map] at h2
    simp only [ne_eq,one_ne_zero,not_false_eq_true,true_iff]
    refine ⟨by omega,fun d hd hdc hdvd =>?_⟩
    have:= h2 d (List.mem_range.2 hdc)
    rw [if_neg (by omega),if_pos (Nat.mod_eq_zero_of_dvd hdvd)] at this
    exact one_ne_zero this
  · simp only [ne_eq,not_true_eq_false,false_iff,not_and,not_forall]
    intro _
    rw [sumZeroList,List.forall_mem_map] at h2
    push_neg at h2
    obtain ⟨d,hd,hne⟩:= h2
    refine ⟨d,?_,List.mem_range.1 hd,?_⟩ <;> split_ifs at hne with h3 h4 <;> simp_all
    · omega
    · exact Nat.dvd_of_mod_eq_zero h4
theorem mn_fnz (v:NVec) (h:∃ j,g v j ≠ 0):firstNZ v< v.length∧g v (firstNZ v) ≠ 0:= by
  have hi0:g v (Nat.find h) ≠ 0:= Nat.find_spec h
  have hlt:Nat.find h< v.length:= by
    by_contra hc
    apply hi0
    simp only [g]
    rw [getDOpt,List.getElem?_eq_none (show v.length≤ Nat.find h by omega)]
    rfl
  have:firstNZ v=Nat.find h:= by
    unfold firstNZ
    rw [List.map_congr_left (g:= fun i =>if i< Nat.find h then 1 else 0),mn_cntlt]
    · omega
    · intro i _
      refine if_congr ?_ rfl rfl
      rw [sumZeroList,List.forall_mem_map,Nat.lt_find_iff]
      simp [Nat.lt_succ_iff]
  rw [this]; exact ⟨hlt,hi0⟩
theorem mn_q (B:ℕ):(primeAbove B).Prime∧B< primeAbove B:= by
  unfold primeAbove
  have hv:∀ j,j< B+2→ g ((List.range (B+2)).map (fun i =>isPr (B+1+i))) j=isPr (B+1+j) :=
    fun j hj => by simp [g,getDOpt,List.getElem?_range hj]
  obtain ⟨p,hp,h1,h2⟩:= Nat.exists_prime_lt_and_le_two_mul (B+1) (by omega)
  obtain ⟨hl,hne⟩:= mn_fnz ((List.range (B+2)).map (fun i =>isPr (B+1+i)))
    ⟨p - (B+1),by rw [hv _ (by omega),show B+1+(p - (B+1))=p by omega]; exact (mn_isPr p).2 hp⟩
  simp only [len_map,List.length_range] at hl
  rw [hv _ hl] at hne
  exact ⟨(mn_isPr _).1 hne,by omega⟩
def mn_ix {n:ℕ} (e:Fin n × Fin n):ℕ:= (pairsF n).idxOf e
theorem mn_il {n:ℕ} (A:Finset (Fin n × Fin n)):(ind A).length=(pairsF n).length:= by
  simp [ind]
theorem mn_ixl {n:ℕ} {e:Fin n × Fin n} (h:e.1< e.2):mn_ix e< (pairsF n).length :=
  List.idxOf_lt_length_of_mem ((mem_pairsF n e).2 h)
theorem mn_gix {n:ℕ} {e:Fin n × Fin n} (h:e.1< e.2):(pairsF n)[mn_ix e]'(mn_ixl h)=e :=
  List.getElem_idxOf _
theorem mn_ixg {n k:ℕ} (hk:k< (pairsF n).length):mn_ix ((pairsF n)[k])=k :=
  (pairsF_nodup n).idxOf_getElem k hk
theorem mn_gpi {n:ℕ} {e:Fin n × Fin n} (h:e.1< e.2) :
    g (pI n) (mn_ix e)=e.1∧g (pJ n) (mn_ix e)=e.2:= by
  have:= pairsF_get n _ (mn_ixl h)
  rw [mn_gix h] at this
  exact ⟨this.1.symm,this.2.symm⟩
theorem mn_gind {n:ℕ} (A:Finset (Fin n × Fin n)) (k:ℕ) (hk:k< (pairsF n).length) :
    g (ind A) k=if (pairsF n)[k]∈A then 1 else 0:= by
  simp [g,ind,getDOpt,hk]
theorem mn_gi {n:ℕ} (A:Finset (Fin n × Fin n)) {e:Fin n × Fin n} (h:e.1< e.2) :
    g (ind A) (mn_ix e)=if e∈A then 1 else 0:= by
  rw [mn_gind A _ (mn_ixl h),mn_gix h]
def mn_val {n:ℕ} (E Q:Finset (Fin n × Fin n)):Prop :=
  Q ⊆ E∧∀ e∈Q,∀ f∈Q,e ≠ f→ Disjoint ({e.1,e.2}:Finset (Fin n)) {f.1,f.2}
def mn_good {n:ℕ} (E P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool))
    (Q:Finset (Fin n × Fin n)):Prop:= P ⊆ Q∧mn_val E Q∧sgn rows Q ≠ 0
def mn_ok {n:ℕ} (E P:Finset (Fin n × Fin n)) (e:Fin n × Fin n):Prop :=
  e∈E∧∀ f∈P,Disjoint ({e.1,e.2}:Finset (Fin n)) {f.1,f.2}
theorem mn_nd {n:ℕ} (a:Fin n × Fin n):¬ Disjoint ({a.1,a.2}:Finset (Fin n)) {a.1,a.2} :=
  fun h =>Finset.insert_ne_empty _ _ (disjoint_self.1 h)
theorem mn_ldsj {n:ℕ} (a b:Fin n × Fin n) :
    List.Disjoint [(a.1:ℕ),a.2] [(b.1:ℕ),b.2] ↔ Disjoint ({a.1,a.2}:Finset (Fin n)) {b.1,b.2}:= by
  simp only [List.Disjoint,disj_leftF,List.mem_cons,List.not_mem_nil,mem_ins,
    mem_oneF,or_false]
  constructor
  · intro h x hx hy
    exact h (a:= (x:ℕ)) (by rcases hx with rfl | rfl <;> simp) (by rcases hy with rfl | rfl <;> simp)
  · intro h x hx hy
    rcases hx with rfl | rfl <;> rcases hy with h' | h'
    all_goals first
      | exact h (Or.inl rfl) (Or.inl (Fin.ext h')) | exact h (Or.inl rfl) (Or.inr (Fin.ext h'))
      | exact h (Or.inr rfl) (Or.inl (Fin.ext h')) | exact h (Or.inr rfl) (Or.inr (Fin.ext h'))
theorem mn_miss {n:ℕ} {P:Finset (Fin n × Fin n)} (hPe:∀ e∈P,e.1< e.2) (T:Finset (Fin n × Fin n)) :
    missP (ind P) (ind T)=0 ↔ P ⊆ T:= by
  unfold missP
  rw [mn_il,sumZeroList,List.forall_mem_map]
  simp only [List.mem_range]
  constructor
  · intro H e he
    have:= H _ (mn_ixl (hPe e he))
    rw [mn_gi P (hPe e he),mn_gi T (hPe e he),if_pos he] at this
    by_contra hT
    rw [if_neg hT] at this
    exact one_ne_zero this
  · intro H k hk
    rw [mn_gind P k hk,mn_gind T k hk]
    by_cases h:(pairsF n)[k]∈P
    · simp [h,H h]
    · simp [h]
def mn_rP {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (P:Finset (Fin n × Fin n)) :=
  rows.filter (fun t =>decide (P ⊆ t.1))
def mn_F0 {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (P:Finset (Fin n × Fin n)):NMat :=
  (mn_rP rows P).map (fun t =>ind t.1)
def mn_f0 {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (P:Finset (Fin n × Fin n)):NVec :=
  (mn_rP rows P).map (fun t =>if t.2 then 1 else 0)
theorem mn_F {n:ℕ} (P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool))
    (hPe:∀ e∈P,e.1< e.2):Frows (ind P) (rows.map (fun t =>ind t.1))=mn_F0 rows P:= by
  unfold Frows mn_F0 mn_rP
  rw [len_map,mn_rfm rows _ (fun t =>if P ⊆ t.1 then [ind t.1] else []) (fun r hr =>?_)]
  · exact mn_flt _ _ _
  · simp [gg,getDOpt,hr,mn_miss hPe]
theorem mn_Fs {n:ℕ} (P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool))
    (hPe:∀ e∈P,e.1< e.2) :
    Fsig (ind P) (rows.map (fun t =>ind t.1)) (rows.map (fun t =>if t.2 then 1 else 0))=mn_f0 rows P:= by
  unfold Fsig mn_f0 mn_rP
  rw [len_map,mn_rfm rows _ (fun t =>if P ⊆ t.1 then [if t.2 then 1 else 0] else []) (fun r hr =>?_)]
  · exact mn_flt _ _ _
  · simp [gg,g,getDOpt,hr,mn_miss hPe]
theorem mn_inv {n:ℕ} {P:Finset (Fin n × Fin n)} (hPe:∀ e∈P,e.1< e.2) (w:Fin n) :
    inVP (pI n) (pJ n) (ind P) (w:ℕ)=0 ↔ ∀ f∈P,w ∉ ({f.1,f.2}:Finset (Fin n)):= by
  unfold inVP
  rw [mn_il,sumZeroList,List.forall_mem_map]
  simp only [List.mem_range]
  constructor
  · intro H f hf
    have:= H _ (mn_ixl (hPe f hf))
    rw [mn_gi P (hPe f hf),(mn_gpi (hPe f hf)).1,(mn_gpi (hPe f hf)).2,if_pos hf] at this
    simp only [mem_ins,mem_oneF,not_or]
    constructor <;> rintro rfl <;> simp at this
  · intro H k hk
    rw [mn_gind P k hk,← (pairsF_get n k hk).1,← (pairsF_get n k hk).2]
    by_cases h1:(pairsF n)[k]∈P
    · have:= H _ h1
      rw [if_pos h1,one_mul]
      simp only [mem_ins,mem_oneF,not_or] at this
      rw [if_neg (fun h =>this.1 (Fin.ext h).symm),if_neg (fun h =>this.2 (Fin.ext h).symm)]
    · rw [if_neg h1,zero_mul]
theorem mn_okk {n:ℕ} {E P:Finset (Fin n × Fin n)} (hPe:∀ e∈P,e.1< e.2) {k:ℕ}
    (hk:k< (pairsF n).length):mn_ok E P ((pairsF n)[k]) ↔ (pairsF n)[k]∈E ∧
      inVP (pI n) (pJ n) (ind P) (g (pI n) k)+inVP (pI n) (pJ n) (ind P) (g (pJ n) k)=0:= by
  rw [Nat.add_eq_zero_iff,← (pairsF_get n k hk).1,← (pairsF_get n k hk).2,mn_inv hPe,mn_inv hPe]
  unfold mn_ok
  simp only [Finset.disjoint_insert_left,Finset.disjoint_singleton_left]
  exact ⟨fun ⟨a,b⟩ =>⟨a,fun f hf =>(b f hf).1,fun f hf =>(b f hf).2⟩,
    fun ⟨a,b,c⟩ =>⟨a,fun f hf =>⟨b f hf,c f hf⟩⟩⟩
theorem mn_U {n:ℕ} {E P:Finset (Fin n × Fin n)} (hPe:∀ e∈P,e.1< e.2) (k:ℕ) :
    k∈Uset (pI n) (pJ n) (ind E) (ind P) ↔ ∃ hk:k< (pairsF n).length,mn_ok E P ((pairsF n)[k]):= by
  unfold Uset
  rw [mn_il]
  simp only [List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨a,ha,hk⟩
    rw [mn_gind E a ha] at hk
    by_cases h1:(pairsF n)[a]∈E
    · rw [if_neg (by simp [h1])] at hk
      split_ifs at hk with h2
      · obtain rfl:= mem_one.1 hk
        exact ⟨ha,(mn_okk hPe ha).2 ⟨h1,h2⟩⟩
      · simp at hk
    · rw [if_pos (by simp [h1])] at hk; simp at hk
  · rintro ⟨hk,hok⟩
    obtain ⟨h1,h2⟩:= (mn_okk hPe hk).1 hok
    exact ⟨k,hk,by rw [mn_gind E k hk,if_neg (by simp [h1]),if_pos h2]; simp⟩
theorem mn_lab {n:ℕ} {E P:Finset (Fin n × Fin n)} (hPe:∀ e∈P,e.1< e.2) (τ:NVec)
    (hτ:∀ k∈τ,k∈Uset (pI n) (pJ n) (ind E) (ind P)) :
    ∃ es:List (Fin n × Fin n),τ=es.map mn_ix∧∀ e∈es,mn_ok E P e:= by
  induction τ with
  | nil =>exact ⟨[],rfl,by simp⟩
  | cons k τ ih =>
    obtain ⟨hk,hok⟩:= (mn_U hPe k).1 (hτ k (by simp))
    obtain ⟨es,rfl,hes⟩:= ih (fun j hj =>hτ j (by simp [hj]))
    exact ⟨(pairsF n)[k] :: es,by rw [mapC,mn_ixg hk],List.forall_mem_cons.2 ⟨hok,hes⟩⟩
theorem mn_ixU {n:ℕ} {E P:Finset (Fin n × Fin n)} (hPe:∀ e∈P,e.1< e.2) {e:Fin n × Fin n}
    (h:e.1< e.2) (he:mn_ok E P e):mn_ix e∈Uset (pI n) (pJ n) (ind E) (ind P) :=
  (mn_U hPe _).2 ⟨mn_ixl h,by rw [mn_gix h]; exact he⟩
theorem mn_ends (pi pj τ:NVec):ends pi pj τ=τ.flatMap (fun k =>[g pi k,g pj k]):= by
  induction τ with
  | nil =>rfl
  | cons k τ ih =>
    rw [List.flatMap_cons,← ih]
    simp only [ends,len_cons]
    rw [show 2 * (τ.length+1)=2 * τ.length+1+1 by ring,List.range_succ_eq_map,
      List.range_succ_eq_map]
    simp only [mapC,mapMap,Function.comp_def,Nat.succ_eq_add_one,List.cons_append,
      List.nil_append]
    rw [List.cons.injEq,List.cons.injEq]
    refine ⟨by simp [g],by simp [g],List.map_congr_left (fun i _ =>?_)⟩
    rw [show i+1+1=i+2 by ring,Nat.add_mod_right,Nat.add_div_right _ (by norm_num)]
    simp [g]
theorem mn_endsE {n:ℕ} (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) :
    ends (pI n) (pJ n) (es.map mn_ix)=es.flatMap (fun e =>[(e.1:ℕ),(e.2:ℕ)]):= by
  rw [mn_ends,List.flatMap_map]
  simp only [List.flatMap_def]
  congr 1
  exact List.map_congr_left (fun e he => by rw [(mn_gpi (hes e he)).1,(mn_gpi (hes e he)).2])
theorem mn_clash (pi pj τ:NVec):clash pi pj τ=0 ↔ (ends pi pj τ).Nodup:= by
  unfold clash
  generalize ends pi pj τ=l
  rw [sumZeroList,List.forall_mem_map,List.nodup_iff_pairwise_ne,
    List.pairwise_iff_getElem]
  simp only [List.mem_range,sumZeroList,List.forall_mem_map]
  constructor
  · intro H i j hi hj hij heq
    have:= H i hi j hj
    simp [hij,g,getDOpt,hi,hj,heq] at this
  · intro H i hi j hj
    split_ifs with h1 h2
    · exact absurd (by simpa [g,getDOpt,hi,hj] using h2) (H i j hi hj h1)
    · rfl
    · rfl
theorem mn_chi {n:ℕ} (F:NMat) (r:ℕ) (T:Finset (Fin n × Fin n)) (hT:gg F r=ind T)
    (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) :
    chi F (es.map mn_ix) r=if es.toFinset ⊆ T then 1 else 0:= by
  unfold chi
  rw [hT,mn_rm (es.map mn_ix) _ (fun k =>1 - g (ind T) k) (fun i hi => by
    simp only [len_map] at hi; simp [g,getDOpt,hi]),mapMap]
  refine if_congr ?_ rfl rfl
  rw [sumZeroList,List.forall_mem_map]
  simp only [Function.comp_apply,Finset.subset_iff,List.mem_toFinset]
  refine forall₂_congr (fun e he =>?_)
  rw [mn_gi T (hes e he)]
  split_ifs with h <;> simp [h]
theorem mn_pos {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (P:Finset (Fin n × Fin n))
    (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) :
    posC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) =
      (rows.filter (fun t =>t.2 && decide (P ∪ es.toFinset ⊆ t.1))).length:= by
  unfold posC
  rw [show (mn_F0 rows P).length=(mn_rP rows P).length by simp [mn_F0],
    mn_rm (mn_rP rows P) _ (fun t =>if (t.2 && decide (es.toFinset ⊆ t.1))=true then 1 else 0)
      (fun r hr =>?_),mn_cnt]
  · unfold mn_rP
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    rintro ⟨T,_ | _⟩ _ <;> simp [Finset.union_subset_iff] <;> exact Bool.and_comm _ _
  · rw [mn_chi (mn_F0 rows P) r (mn_rP rows P)[r].1 (by simp [mn_F0,gg,getDOpt,hr]) es hes]
    simp only [mn_f0,g,getDOpt,List.getElem?_map,getOptEq hr,
      Option.map_some,Option.getD_some]
    cases (mn_rP rows P)[r].2 <;> simp
theorem mn_neg {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (P:Finset (Fin n × Fin n))
    (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) :
    negC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) =
      (rows.filter (fun t =>!t.2 && decide (P ∪ es.toFinset ⊆ t.1))).length:= by
  unfold negC
  rw [show (mn_F0 rows P).length=(mn_rP rows P).length by simp [mn_F0],
    mn_rm (mn_rP rows P) _ (fun t =>if (!t.2 && decide (es.toFinset ⊆ t.1))=true then 1 else 0)
      (fun r hr =>?_),mn_cnt]
  · unfold mn_rP
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    rintro ⟨T,_ | _⟩ _ <;> simp [Finset.union_subset_iff] <;> exact Bool.and_comm _ _
  · rw [mn_chi (mn_F0 rows P) r (mn_rP rows P)[r].1 (by simp [mn_F0,gg,getDOpt,hr]) es hes]
    simp only [mn_f0,g,getDOpt,List.getElem?_map,getOptEq hr,
      Option.map_some,Option.getD_some]
    cases (mn_rP rows P)[r].2 <;> simp
theorem mn_hitE {n:ℕ} (rows:List (Finset (Fin n × Fin n) × Bool)) (P:Finset (Fin n × Fin n))
    (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) :
    hit (pI n) (pJ n) (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) ≠ 0 ↔
      (es.flatMap (fun e =>[(e.1:ℕ),(e.2:ℕ)])).Nodup∧sgn rows (P ∪ es.toFinset) ≠ 0:= by
  have:hit (pI n) (pJ n) (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) ≠ 0 ↔
      clash (pI n) (pJ n) (es.map mn_ix)=0 ∧
        posC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix) ≠ negC (mn_F0 rows P) (mn_f0 rows P) (es.map mn_ix):= by
    unfold hit; split_ifs <;> simp [*]
  rw [this,mn_clash,mn_endsE es hes,mn_pos rows P es hes,mn_neg rows P es hes]
  unfold sgn
  constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1,by omega⟩
theorem mn_mb {n:ℕ} (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) (k:ℕ)
    (hk:k< (pairsF n).length) (A:Finset (Fin n × Fin n)) :
    decide (g (ind A) k+((List.range (es.map mn_ix).length).map
      (fun i =>if g (es.map mn_ix) i=k then 1 else 0)).sum ≠ 0)=decide ((pairsF n)[k]∈A ∪ es.toFinset):= by
  rw [mn_gind A k hk,mn_rm (es.map mn_ix) _ (fun j =>if j=k then 1 else 0) (fun i hi => by
    simp only [len_map] at hi; simp [g,getDOpt,hi]),mapMap]
  have hB:(pairsF n)[k]∈es ↔ (es.map ((fun j =>if j=k then 1 else 0) ∘ mn_ix)).sum ≠ 0:= by
    rw [ne_eq,sumZeroList,List.forall_mem_map]
    simp only [Function.comp_apply,ite_eq_right_iff,one_ne_zero,imp_false,not_forall,not_not]
    constructor
    · intro h; exact ⟨_,h,mn_ixg hk⟩
    · rintro ⟨e,he,hek⟩; subst hek; rw [mn_gix (hes e he)]; exact he
  apply decide_eq_decide.2
  rw [mem_un,List.mem_toFinset,hB]
  generalize (es.map ((fun j =>if j=k then 1 else 0) ∘ mn_ix)).sum=S
  split_ifs with h1 <;> simp [h1] <;> omega
theorem mn_out {n:ℕ} (E P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool))
    (hPe:∀ e∈P,e.1< e.2) (es:List (Fin n × Fin n)) (hes:∀ e∈es,e.1< e.2) :
    outBits (inputF n E P rows) (es.map mn_ix)=[true] ++ maskF (P ∪ es.toFinset) ++
      [decide (sgn rows (P ∪ es.toFinset)< 0)] ++
        (List.range (rows.length.log2+1)).map (fun i =>(sgn rows (P ∪ es.toFinset)).natAbs.testBit i):= by
  simp only [outBits,Pm_inputF,rowM_inputF,rowS_inputF,pN_inputF,lenV_inputF,mn_F P rows hPe,
    mn_Fs P rows hPe,mn_pos rows P es hes,mn_neg rows P es hes,sgn]
  rw [mn_rm (pairsF n) _ (fun e =>decide (e∈P ∪ es.toFinset)) (fun k hk =>mn_mb es hes k hk P)]
  have key:∀ a b:ℕ,decide (a< b)=decide ((a:ℤ) - b< 0)∧(a - b)+(b - a)=((a:ℤ) - b).natAbs :=
    fun a b =>⟨decide_eq_decide.2 (by omega),by omega⟩
  rw [(key _ _).1,(key _ _).2]; rfl
theorem mn_gd {n:ℕ} {E P:Finset (Fin n × Fin n)} {rows:List (Finset (Fin n × Fin n) × Bool)}
    (hP:mn_val E P) (es:List (Fin n × Fin n)) (hes:∀ e∈es,mn_ok E P e)
    (hnd:(es.flatMap (fun e =>[(e.1:ℕ),(e.2:ℕ)])).Nodup) (hs:sgn rows (P ∪ es.toFinset) ≠ 0) :
    mn_good E P rows (P ∪ es.toFinset)∧(P ∪ es.toFinset) \ P=es.toFinset ∧
      es.toFinset.card=es.length:= by
  rw [List.nodup_flatMap] at hnd
  have hpw:∀ a∈es,∀ b∈es,a ≠ b→ Disjoint ({a.1,a.2}:Finset (Fin n)) {b.1,b.2} :=
    fun a ha b hb =>List.Pairwise.forall_of_forall_of_flip
      (R:= fun a b =>a ≠ b→ Disjoint ({a.1,a.2}:Finset (Fin n)) {b.1,b.2}) (fun x _ h =>absurd rfl h)
      (hnd.2.imp (fun {a b} h (_:a ≠ b) =>(mn_ldsj a b).1 h)) (hnd.2.imp (fun {a b} h (_:b ≠ a) =>((mn_ldsj a b).1 h).symm)) ha hb
  have hnd':es.Nodup:= hnd.2.imp (fun {a b} h hab => by subst hab; exact mn_nd a ((mn_ldsj a a).1 h))
  have hPR:Disjoint P es.toFinset:= disj_leftF.2 (fun e heP heR =>
    mn_nd e ((hes e (List.mem_toFinset.1 heR)).2 e heP))
  refine ⟨⟨Finset.subset_union_left,⟨Finset.union_subset hP.1
    (fun e he =>(hes e (List.mem_toFinset.1 he)).1),?_⟩,hs⟩,
    Finset.union_sdiff_cancel_left hPR,List.toFinset_card_of_nodup hnd'⟩
  intro e he f hf hef
  simp only [mem_un,List.mem_toFinset] at he hf
  rcases he with he | he <;> rcases hf with hf | hf
  · exact hP.2 e he f hf hef
  · exact ((hes f hf).2 e he).symm
  · exact (hes e he).2 f hf
  · exact hpw e he f hf hef
theorem mn_fg {n:ℕ} {E P:Finset (Fin n × Fin n)} {rows:List (Finset (Fin n × Fin n) × Bool)}
    (hE:∀ e∈E,e.1< e.2) (Q:Finset (Fin n × Fin n)) (hQ:mn_good E P rows Q) :
    (∀ e∈(Q \ P).toList,mn_ok E P e) ∧
      ((Q \ P).toList.flatMap (fun e =>[(e.1:ℕ),(e.2:ℕ)])).Nodup ∧
      P ∪ (Q \ P).toList.toFinset=Q∧(Q \ P).toList.length=(Q \ P).card:= by
  obtain ⟨hPQ,⟨hQE,hQm⟩,-⟩:= hQ
  refine ⟨fun e he =>?_,List.nodup_flatMap.2 ⟨fun e he =>?_,
    (Finset.nodup_toList _).pairwise_of_forall_ne (fun a ha b hb hab =>?_)⟩,
    by rw [Finset.toList_toFinset,Finset.union_sdiff_of_subset hPQ],Finset.length_toList _⟩
  · rw [Finset.mem_toList,Finset.mem_sdiff] at he
    exact ⟨hQE he.1,fun f hf =>hQm e he.1 f (hPQ hf) (fun h =>he.2 (h ▸ hf))⟩
  · rw [Finset.mem_toList,Finset.mem_sdiff] at he
    have:= Fin.lt_def.1 (hE e (hQE he.1))
    simp only [List.nodup_cons,mem_one,List.not_mem_nil,not_false_eq_true,List.nodup_nil,
      and_true]
    omega
  · rw [Finset.mem_toList,Finset.mem_sdiff] at ha hb
    exact (mn_ldsj a b).2 (hQm a ha.1 b hb.1 hab)
theorem mn_exmin {α:Type*} (p:Finset α→ Prop) (h:∃ Q,p Q) :
    ∃ Q,p Q∧∀ S,p S→ Q.card≤ S.card:= by
  classical
  have h':∃ k,∃ Q,p Q∧Q.card=k:= ⟨_,h.choose,h.choose_spec,rfl⟩
  obtain ⟨Q,hQ,hc⟩:= Nat.find_spec h'
  exact ⟨Q,hQ,fun S hS =>hc ▸ Nat.find_min' h' ⟨S,hS,rfl⟩⟩
theorem mn_min {n:ℕ} {E P:Finset (Fin n × Fin n)} {rows:List (Finset (Fin n × Fin n) × Bool)}
    (Q:Finset (Fin n × Fin n)) (hQ:mn_good E P rows Q)
    (hmin:∀ S,mn_good E P rows S→ Q.card≤ S.card) :
    2 ^ (Q \ P).card * (sgn rows Q).natAbs≤ (mn_rP rows P).length:= by
  have:= mobius_bound rows P (Q \ P) (fun S hS => by
    by_contra hne
    have hSQ:P ∪ S ⊆ Q:= Finset.union_subset hQ.1 (hS.subset.trans Finset.sdiff_subset)
    have:= hmin (P ∪ S) ⟨Finset.subset_union_left,⟨hSQ.trans hQ.2.1.1,
      fun e he f hf hef =>hQ.2.1.2 e (hSQ he) f (hSQ hf) hef⟩,hne⟩
    have h1:= Finset.card_union_le P S
    have h2:= Finset.card_lt_card hS
    have h3:= Finset.card_sdiff_add_card_eq_card hQ.1
    omega)
  rwa [Finset.union_sdiff_of_subset hQ.1] at this
theorem mn_main (n:ℕ) (E P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool))
    (hE:∀ e∈E,e.1< e.2) (hP:mn_val E P) :
    ((mn_rP rows P).length=0→ solveV (inputF n E P rows)=[false]) ∧
    (solveV (inputF n E P rows)=[false] ↔ ¬ ∃ Q,mn_good E P rows Q) ∧
    ((∃ Q,mn_good E P rows Q)→ ∃ Q,mn_good E P rows Q∧(∀ S,mn_good E P rows S→ Q.card≤ S.card) ∧
      2 ^ ((Q \ P).card) * (sgn rows Q).natAbs≤ (mn_rP rows P).length∧solveV (inputF n E P rows) =
        [true] ++ maskF Q ++ [decide (sgn rows Q< 0)] ++
          (List.range (rows.length.log2+1)).map (fun i =>(sgn rows Q).natAbs.testBit i)):= by
  have hPe:∀ e∈P,e.1< e.2:= fun e he =>hE e (hP.1 he)
  have hq:= mn_q (n+(mn_rP rows P).length)
  haveI:Fact (primeAbove (n+(mn_rP rows P).length)).Prime:= ⟨hq.1⟩
  have hfd:found (inputF n E P rows)=((lvl (primeAbove (n+(mn_rP rows P).length))
      (2 * Nat.log2 (mn_rP rows P).length) (pI n) (pJ n) (Uset (pI n) (pJ n) (ind E) (ind P))
      (mn_F0 rows P) (mn_f0 rows P))^[Nat.log2 (mn_rP rows P).length+1] ([[]],[])).2:= by
    simp only [found,nV_inputF,Pm_inputF,Em_inputF,rowM_inputF,rowS_inputF,mn_F P rows hPe,
      mn_Fs P rows hPe]
    simp only [mn_F0,len_map]
  have hsv:solveV (inputF n E P rows)=if (found (inputF n E P rows)).length=0 then [false]
      else outBits (inputF n E P rows) (gg (found (inputF n E P rows)) 0):= rfl
  have hgh:∀ S,mn_good E P rows S →
      (∀ k∈(S \ P).toList.map mn_ix,k∈Uset (pI n) (pJ n) (ind E) (ind P)) ∧
      ((S \ P).toList.map mn_ix).length=(S \ P).card ∧
      hit (pI n) (pJ n) (mn_F0 rows P) (mn_f0 rows P) ((S \ P).toList.map mn_ix) ≠ 0:= by
    intro S hS
    obtain ⟨h1,h2,h3,h4⟩:= mn_fg hE S hS
    refine ⟨fun k hk =>?_,by rw [len_map,h4],(mn_hitE rows P _ (fun e he =>hE e (h1 e he).1)).2
      ⟨h2,by rw [h3]; exact hS.2.2⟩⟩
    obtain ⟨e,he,rfl⟩:= mem_mapL.1 hk
    exact mn_ixU hPe (hE e (h1 e he).1) (h1 e he)
  rcases found_spec (primeAbove (n+(mn_rP rows P).length)) (2 * Nat.log2 (mn_rP rows P).length)
      (Nat.log2 (mn_rP rows P).length) rfl (pI n) (pJ n) (Uset (pI n) (pJ n) (ind E) (ind P))
      (mn_F0 rows P) (mn_f0 rows P)
      (fun τ hτ a ha => by
        obtain ⟨es,rfl,hes⟩:= mn_lab hPe τ hτ
        rw [mn_endsE es (fun e he =>hE e (hes e he).1),List.mem_flatMap] at ha
        obtain ⟨e,-,he⟩:= ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl <;> omega)
      (by simp only [mn_F0,len_map]; omega)
      (by simp only [mn_f0,mem_mapL]; rintro a ⟨t,-,rfl⟩; split_ifs <;> omega)
      (by simp [mn_F0,mn_f0]) with ⟨h0,hno⟩ | ⟨τ,h1,hU,hK,hhit,hmin⟩
  · have hs:solveV (inputF n E P rows)=[false]:= by rw [hsv,hfd,h0]; rfl
    have hnone:¬ ∃ Q,mn_good E P rows Q:= by
      intro hex
      obtain ⟨Q,hQ,hQm⟩:= mn_exmin _ hex
      have hb:= mn_min Q hQ hQm
      have hs0:(sgn rows Q).natAbs ≠ 0:= Int.natAbs_ne_zero.2 hQ.2.2
      have hm0:(mn_rP rows P).length ≠ 0:= by
        intro h; rw [h] at hb; exact hs0 (by simpa using hb)
      have hK:(Q \ P).card≤ Nat.log2 (mn_rP rows P).length :=
        (Nat.le_log2 hm0).2 (le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hs0)) hb)
      obtain ⟨g1,g2,g3⟩:= hgh Q hQ
      exact g3 (hno _ g1 (by rw [g2]; exact hK))
    exact ⟨fun _ =>hs,iff_of_true hs hnone,fun h =>absurd h hnone⟩
  · obtain ⟨es,rfl,hes⟩:= mn_lab hPe τ hU
    have hes':∀ e∈es,e.1< e.2:= fun e he =>hE e (hes e he).1
    obtain ⟨hnd,hsg⟩:= (mn_hitE rows P es hes').1 hhit
    obtain ⟨hgood,hdiff,hcard⟩:= mn_gd hP es hes hnd hsg
    have hQm:∀ S,mn_good E P rows S→ (P ∪ es.toFinset).card≤ S.card:= by
      intro S hS
      obtain ⟨g1,g2,g3⟩:= hgh S hS
      have:= not_lt.1 (fun h =>g3 (hmin _ g1 h))
      rw [g2,len_map] at this
      have c1:= Finset.card_sdiff_add_card_eq_card hS.1
      have c2:= Finset.card_sdiff_add_card_eq_card hgood.1
      rw [hdiff,hcard] at c2
      omega
    have hb:= mn_min _ hgood hQm
    have hs:solveV (inputF n E P rows)=[true] ++ maskF (P ∪ es.toFinset) ++
        [decide (sgn rows (P ∪ es.toFinset)< 0)] ++ (List.range (rows.length.log2+1)).map
          (fun i =>(sgn rows (P ∪ es.toFinset)).natAbs.testBit i):= by
      rw [hsv,hfd,h1]; exact mn_out E P rows hPe es hes'
    refine ⟨fun h =>?_,⟨fun h =>?_,fun h =>absurd ⟨_,hgood⟩ h⟩,fun _ =>⟨_,hgood,hQm,hb,hs⟩⟩
    · rw [h] at hb
      exact absurd (Int.natAbs_eq_zero.1 (by simpa using hb)) hgood.2.2
    · rw [hs] at h; simp at h
theorem solveV_spec:∀ (n:Nat) (E P:Finset (Fin n × Fin n)) (rows:List (Finset (Fin n × Fin n) × Bool)),
  (∀ e∈E,e.1< e.2) →
  let ends:= fun e:Fin n × Fin n =>({e.1,e.2}:Finset (Fin n))
  let valid:= fun Q:Finset (Fin n × Fin n) =>Q ⊆ E ∧
    ∀ e∈Q,∀ f∈Q,e ≠ f→ Disjoint (ends e) (ends f)
  valid P →
  let signed:= fun Q:Finset (Fin n × Fin n) =>
    ((rows.filter (fun t =>t.2 && decide (Q ⊆ t.1))).length:Int) -
      ((rows.filter (fun t =>!t.2 && decide (Q ⊆ t.1))).length:Int)
  let mask:= fun A:Finset (Fin n × Fin n) =>((fun n:Nat =>(List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j =>decide (i< j))).map (fun j =>(i,j)))) n).map (fun e =>decide (e∈A))
  let good:= fun Q =>P ⊆ Q∧valid Q∧signed Q ≠ 0
  let m:= (rows.filter (fun t =>decide (P ⊆ t.1))).length
  let x:= (fun z:Nat =>List.replicate z true ++ [false]) n ++ mask E ++ mask P ++
    (fun z:Nat =>List.replicate z true ++ [false]) rows.length ++ rows.flatMap (fun t =>t.2 :: mask t.1)
  (m=0→ solveV x=[false])∧(solveV x=[false] ↔ ¬ ∃ Q,good Q) ∧
  ((∃ Q,good Q)→ ∃ Q,good Q∧(∀ S,good S→ Q.card≤ S.card) ∧
    2^((Q \ P).card)*(signed Q).natAbs≤ m∧solveV x =
      [true] ++ mask Q ++ [decide (signed Q< 0)] ++
        (List.range (rows.length.log2+1)).map (fun i =>(signed Q).natAbs.testBit i)):= by
  intro n E P rows hE
  exact mn_main n E P rows hE
end Alg
end PT
namespace Circ
variable {α:Type} [Fintype α] [DecidableEq α]
def IsM (M:Finset (Finset α)):Prop :=
  (∀ e∈M,e.card=2)∧(∀ e∈M,∀ g∈M,e ≠ g→ Disjoint e g)
theorem IsM.mono {M N:Finset (Finset α)} (valid:IsM M) (sub:N ⊆ M):IsM N :=
  ⟨fun edge member =>valid.1 edge (sub member),fun edge member other included =>valid.2 edge (sub member) other (sub included)⟩
theorem isM_empty:IsM (∅:Finset (Finset α)):= ⟨by simp,by simp⟩
open PEqualNP.CircuitLowerBounds
def step (w:BitTape) (g:Gate):BitTape :=
  w ++ [g.op.eval (g.inputs.map fun i =>w.getD i false)]
def run (gs:List Gate) (w:BitTape):BitTape:= gs.foldl step w
theorem run_append (a b:List Gate) (w:BitTape):run (a ++ b) w=run b (run a w) :=
  List.foldl_append
theorem run_cons (g:Gate) (gs:List Gate) (w:BitTape):run (g :: gs) w=run gs (step w g):= rfl
theorem run_nil (w:BitTape):run [] w=w:= rfl
theorem run_length (gs:List Gate) (w:BitTape):(run gs w).length=w.length+gs.length:= by
  induction gs generalizing w with
  | nil =>rfl
  | cons g gs ih =>rw [run_cons,ih]; simp [step]; omega
theorem getD_keep (w t:BitTape) {i:ℕ} (hi:i< w.length) :
    (w ++ t).getD i false=w.getD i false:= by
  simp [getDOpt,getLeftOpt hi]
theorem getD_new (w:BitTape) (v:Bool) {i:ℕ} (hi:i=w.length) :
    (w ++ [v]).getD i false=v:= by
  subst hi
  simp [getDOpt]
theorem prefix_keep (gs:List Gate) (w:BitTape) {i:ℕ} (hi:i< w.length) :
    (run gs w).getD i false=w.getD i false:= by
  induction gs generalizing w with
  | nil =>rfl
  | cons g gs ih =>
    rw [run_cons,ih _ (by simp [step]; omega)]
    exact getD_keep _ _ hi
def value (C:Circuit) (x:BitTape) (i:ℕ):= (C.wires x).getD i false
theorem value_gate (C:Circuit) (x:BitTape) (j:ℕ) (hj:j< C.gates.length) :
    value C x (x.length+j) =
      (C.gates[j]).op.eval
        ((C.gates[j]).inputs.map fun i =>if i< x.length+j then value C x i else false):= by
  let gs:= C.gates
  let w:= run (gs.take j) x
  have hlen:w.length=x.length+j:= by
    simp only [w,run_length,gs,List.length_take,Nat.min_eq_left hj.le]
  have hs:gs=gs.take j ++ gs[j] :: gs.drop (j+1):= by
    simp [gs,List.take_append_drop]
  have hrun:C.wires x=run (gs.drop (j+1)) (step w gs[j]):= by
    change run gs x=_
    conv_lhs =>rw [hs,run_append,run_cons]
  have hread (i:ℕ) (hi:i< w.length):value C x i=w.getD i false:= by
    change (run gs x).getD i false=_
    conv_lhs =>rw [← List.take_append_drop j gs,run_append]
    exact prefix_keep _ _ hi
  unfold value
  conv_lhs =>rw [hrun]
  rw [prefix_keep _ _ (by simp [step,hlen])]
  rw [← hlen]
  simp only [step]
  rw [getD_new _ _ rfl]
  apply congrArg _
  apply List.map_congr_left
  intro i _
  split
  · rename_i hi
    exact (hread i hi).symm
  · rename_i hi
    simp [getDOpt,List.getElem?_eq_none_iff.2 (by omega:w.length≤ i)]
section tree
variable (C:Circuit) (n:ℕ)
def gateAt (w:ℕ):Gate:= C.gates.getD (w - n) ⟨GateOp.and,[]⟩
def isNot (w:ℕ):Prop:= n≤ w∧(gateAt C n w).op=GateOp.not
open Classical in
noncomputable def reads (w:ℕ):NVec :=
  if (gateAt C n w).op=GateOp.not then (gateAt C n w).inputs.take 1 else (gateAt C n w).inputs
noncomputable def ch (w:ℕ):NVec :=
  if n≤ w∧w - n< C.gates.length then (reads C n w).filter (fun c =>decide (c< w)) else []
theorem ch_lt {w c:ℕ} (h:c∈ch C n w):c< w:= by
  unfold ch at h
  split at h
  · simpa using (List.mem_filter.1 h).2
  · simp at h
theorem ch_ge {w c:ℕ} (h:c∈ch C n w):n≤ w:= by
  unfold ch at h
  split at h
  · rename_i h'
    exact h'.1
  · simp at h
noncomputable def desc (w:ℕ):Finset ℕ :=
  insert w ((ch C n w).toFinset.attach.biUnion fun c =>desc c.1)
termination_by w
decreasing_by exact ch_lt C n (List.mem_toFinset.mp c.2)
theorem mem_desc (w v:ℕ):v∈desc C n w ↔ v=w∨∃ c∈ch C n w,v∈desc C n c:= by
  conv_lhs =>rw [desc]
  simp only [mem_ins,Finset.mem_biUnion,Finset.mem_attach,true_and,Subtype.exists,
    List.mem_toFinset,exists_prop]
theorem self_desc (w:ℕ):w∈desc C n w:= (mem_desc C n w w).2 (Or.inl rfl)
theorem desc_le:∀ w v,v∈desc C n w→ v≤ w:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c,hc,h⟩
    · exact le_rfl
    · exact (ih c (ch_lt C n hc) v h).trans (ch_lt C n hc).le
theorem desc_trans:∀ w v,v∈desc C n w→ desc C n v ⊆ desc C n w:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c,hc,h⟩
    · exact Finset.Subset.refl _
    · intro u hu
      exact (mem_desc C n w u).2 (Or.inr ⟨c,hc,ih c (ch_lt C n hc) v h hu⟩)
theorem desc_parent:∀ w v,v∈desc C n w→ v ≠ w→ ∃ p∈desc C n w,v∈ch C n p:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv hne
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c,hc,h⟩
    · exact absurd rfl hne
    · by_cases hvc:v=c
      · exact ⟨w,self_desc C n w,hvc ▸ hc⟩
      · obtain ⟨p,hp,hvp⟩:= ih c (ch_lt C n hc) v h hvc
        exact ⟨p,(mem_desc C n w p).2 (Or.inr ⟨c,hc,hp⟩),hvp⟩
theorem child_desc {o p c:ℕ} (hp:p∈desc C n o) (hc:c∈ch C n p):c∈desc C n o :=
  desc_trans C n o p hp ((mem_desc C n p c).2 (Or.inr ⟨c,hc,self_desc C n c⟩))
def GoodC:Prop:= ∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or∨g.op=GateOp.not)∧g.inputs.length≤ 2
theorem gateAt_eq {w:ℕ} (h:w - n< C.gates.length):gateAt C n w=C.gates[w - n]:= by
  unfold gateAt
  rw [getDOpt,getOptEq h]
  rfl
open Classical in
noncomputable def bnd (w:ℕ):ℕ:= if isNot C n w then 1 else 2
theorem ch_len (hg:GoodC C) {w:ℕ} (hw:n≤ w):(ch C n w).length≤ bnd C n w:= by
  classical
  unfold ch bnd
  split
  · rename_i h
    refine (List.length_filter_le _ _).trans ?_
    unfold reads
    have hg':(gateAt C n w).inputs.length≤ 2:= by
      rw [gateAt_eq C n h.2]
      exact (hg _ (at_mem h.2)).2
    by_cases hn:(gateAt C n w).op=GateOp.not
    · rw [if_pos hn,if_pos (show isNot C n w from ⟨hw,hn⟩),List.length_take]
      omega
    · rw [if_neg hn,if_neg (show ¬ isNot C n w from fun c =>hn c.2)]
      exact hg'
  · simp
noncomputable def gatesIn (o:ℕ):Finset ℕ:= (desc C n o).filter (fun w =>n≤ w)
noncomputable def leaves (o:ℕ):Finset ℕ:= (desc C n o).filter (fun w =>w< n)
open Classical in
noncomputable def nots (o:ℕ):Finset ℕ:= (desc C n o).filter (fun w =>isNot C n w)
open Classical in
theorem sum_bnd (o:ℕ):∑ p∈gatesIn C n o,bnd C n p+(nots C n o).card=2 * (gatesIn C n o).card:= by
  have h1:nots C n o=(gatesIn C n o).filter (fun w =>isNot C n w):= by
    unfold nots gatesIn
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro w _
    exact ⟨fun h =>⟨h.1,h⟩,fun h =>h.2⟩
  rw [h1,Finset.card_filter,← Finset.sum_add_distrib,mul_comm,← smul_eq_mul,← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro p _
  unfold bnd
  split <;> rfl
theorem leaves_gates (o:ℕ):(leaves C n o).card+(gatesIn C n o).card=(desc C n o).card:= by
  unfold leaves gatesIn
  have:= Finset.card_filter_add_card_filter_not (s:= desc C n o) (fun w =>w< n)
  simpa only [not_lt] using this
theorem parent_cover (o:ℕ):(desc C n o).erase o ⊆ (gatesIn C n o).biUnion (fun p =>(ch C n p).toFinset):= by
  intro v hv
  rw [Finset.mem_erase] at hv
  obtain ⟨p,hp,hvp⟩:= desc_parent C n o v hv.2 hv.1
  rw [Finset.mem_biUnion]
  exact ⟨p,mem_filt.2 ⟨hp,ch_ge C n hvp⟩,List.mem_toFinset.2 hvp⟩
theorem card_ch_le (hg:GoodC C) (o p:ℕ) (hp:p∈gatesIn C n o):(ch C n p).toFinset.card≤ bnd C n p :=
  (List.toFinset_card_le _).trans (ch_len C n hg (mem_filt.1 hp).2)
theorem count (hg:GoodC C) (o:ℕ):(leaves C n o).card+(nots C n o).card≤ (gatesIn C n o).card+1:= by
  have h1:= card_monoF (parent_cover C n o)
  rw [Finset.card_erase_of_mem (self_desc C n o)] at h1
  have h2:((gatesIn C n o).biUnion (fun p =>(ch C n p).toFinset)).card ≤
      ∑ p∈gatesIn C n o,(ch C n p).toFinset.card:= Finset.card_biUnion_le
  have h3:= Finset.sum_le_sum (card_ch_le C n hg o)
  have h4:= sum_bnd C n o
  have h5:= leaves_gates C n o
  omega
theorem exact_count (hg:GoodC C) (o:ℕ)
    (hex:(gatesIn C n o).card+1≤ (leaves C n o).card+(nots C n o).card) :
    (∀ p∈gatesIn C n o,(ch C n p).toFinset.card=bnd C n p) ∧
    (∀ p∈desc C n o,∀ r∈desc C n o,∀ c,c∈ch C n p→ c∈ch C n r→ p=r):= by
  have h1:= card_monoF (parent_cover C n o)
  rw [Finset.card_erase_of_mem (self_desc C n o)] at h1
  have h2:((gatesIn C n o).biUnion (fun p =>(ch C n p).toFinset)).card ≤
      ∑ p∈gatesIn C n o,(ch C n p).toFinset.card:= Finset.card_biUnion_le
  have h3:= Finset.sum_le_sum (card_ch_le C n hg o)
  have h4:= sum_bnd C n o
  have h5:= leaves_gates C n o
  have h6:∑ p∈gatesIn C n o,(ch C n p).toFinset.card=∑ p∈gatesIn C n o,bnd C n p:= by omega
  have h7:∑ p∈gatesIn C n o,(ch C n p).toFinset.card ≤
      ((gatesIn C n o).biUnion (fun p =>(ch C n p).toFinset)).card:= by omega
  refine ⟨(Finset.sum_eq_sum_iff_of_le (card_ch_le C n hg o)).1 h6,?_⟩
  intro p hp r hr c hcp hcr
  by_contra hpr
  have hpG:p∈gatesIn C n o:= mem_filt.2 ⟨hp,ch_ge C n hcp⟩
  have hrG:r∈gatesIn C n o:= mem_filt.2 ⟨hr,ch_ge C n hcr⟩
  let F:ℕ→ Finset ℕ:= fun s =>if s=r then (ch C n s).toFinset.erase c else (ch C n s).toFinset
  have hsub:(gatesIn C n o).biUnion (fun p =>(ch C n p).toFinset) ⊆ (gatesIn C n o).biUnion F:= by
    intro v hv
    rw [Finset.mem_biUnion] at hv ⊢
    obtain ⟨s,hs,hvs⟩:= hv
    by_cases hvc:v=c
    · refine ⟨p,hpG,?_⟩
      simp only [F,if_neg hpr,hvc]
      exact List.mem_toFinset.2 hcp
    · refine ⟨s,hs,?_⟩
      simp only [F]
      split
      · exact Finset.mem_erase.2 ⟨hvc,hvs⟩
      · exact hvs
  have h8:∑ s∈gatesIn C n o,(F s).card< ∑ s∈gatesIn C n o,(ch C n s).toFinset.card:= by
    apply Finset.sum_lt_sum
    · intro s _
      simp only [F]
      split
      · exact Finset.card_erase_le
      · exact le_rfl
    · refine ⟨r,hrG,?_⟩
      simp only [F,if_true]
      exact Finset.card_erase_lt_of_mem (List.mem_toFinset.2 hcr)
  have h9:= (card_monoF hsub).trans Finset.card_biUnion_le
  omega
theorem sib_disj (o:ℕ)
    (huniq:∀ p∈desc C n o,∀ r∈desc C n o,∀ c,c∈ch C n p→ c∈ch C n r→ p=r)
    (p a b:ℕ) (hp:p∈desc C n o) (ha:a∈ch C n p) (hb:b∈ch C n p) (hab:a ≠ b) :
    Disjoint (desc C n a) (desc C n b):= by
  have haT:= child_desc C n hp ha
  have hbT:= child_desc C n hp hb
  have top:∀ a b:ℕ,a∈ch C n p→ b∈ch C n p→ a ≠ b→ a∈desc C n o→ b∈desc C n o →
      a∈desc C n b→ False:= by
    intro a b ha hb hab haT hbT h
    obtain ⟨r,hr,har⟩:= desc_parent C n b a h hab
    have hrT:= desc_trans C n o b hbT hr
    have:p=r:= huniq p hp r hrT a ha har
    have:= desc_le C n b r hr
    have:= ch_lt C n hb
    omega
  have main:∀ d v,p - v=d→ v∈desc C n a→ v∈desc C n b→ False:= by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro v hd hva hvb
      by_cases h1:v=a
      · exact top a b ha hb hab haT hbT (h1 ▸ hvb)
      by_cases h2:v=b
      · exact top b a hb ha hab.symm hbT haT (h2 ▸ hva)
      obtain ⟨s,hs,hvs⟩:= desc_parent C n a v hva h1
      obtain ⟨r,hr,hvr⟩:= desc_parent C n b v hvb h2
      have hsr:s=r:= huniq s (desc_trans C n o a haT hs) r (desc_trans C n o b hbT hr) v hvs hvr
      subst hsr
      have h3:= desc_le C n a s hs
      have h4:= ch_lt C n ha
      have h5:= ch_lt C n hvs
      exact ih (p - s) (by omega) s rfl hs hr
  rw [disj_leftF]
  intro v hva hvb
  exact main _ v rfl hva hvb
end tree
def Node (n:ℕ) (T:Finset ℕ) (V:ℕ→ (ℕ→ Bool)→ Bool) (S:ℕ→ Finset ℕ) (N:ℕ→ Prop) (w:ℕ):Prop :=
  (w< n∧S w={w}∧∀ f,V w f=f w) ∨
  (n≤ w∧¬ N w∧∃ a∈T,∃ b∈T,a< w∧b< w∧Disjoint (S a) (S b)∧S w=insert w (S a ∪ S b) ∧
    ((∀ f,V w f=(V a f && V b f))∨∀ f,V w f=(V a f || V b f))) ∨
  (n≤ w∧N w∧∃ a∈T,a< w∧S w=insert w (S a)∧∀ f,V w f=!V a f)
def inp (n:ℕ) (f:ℕ→ Bool):BitTape:= (List.range n).map f
theorem tree_nodes (C:Circuit) (n:ℕ) (hg:GoodC C) (o:ℕ) (ho:o< n+C.gates.length)
    (hex:(gatesIn C n o).card+1≤ (leaves C n o).card+(nots C n o).card) :
    ∀ w∈desc C n o,Node n (desc C n o) (fun w f =>value C (inp n f) w) (desc C n) (isNot C n) w:= by
  classical
  intro w hw
  obtain ⟨hcard,huniq⟩:= exact_count C n hg o hex
  have hlen:∀ f,(inp n f).length=n:= fun f => by simp [inp]
  by_cases hwn:w< n
  · refine Or.inl ⟨hwn,?_,?_⟩
    · ext v
      rw [mem_desc]
      have:ch C n w=[]:= by
        unfold ch
        rw [if_neg (by omega)]
      simp [this]
    · intro f
      change (run C.gates (inp n f)).getD w false=f w
      rw [prefix_keep _ _ (by rw [hlen]; exact hwn)]
      simp [inp,getDOpt,hwn]
  have hwn':n≤ w:= by omega
  right
  have hwo:= desc_le C n o w hw
  have hj:w - n< C.gates.length:= by omega
  have hnw:n+(w - n)=w:= by omega
  have hval:∀ f,value C (inp n f) w=(gateAt C n w).op.eval
      ((gateAt C n w).inputs.map fun i =>if i< w then value C (inp n f) i else false):= by
    intro f
    have:= value_gate C (inp n f) (w - n) hj
    rw [hlen,hnw] at this
    rw [gateAt_eq C n hj]
    exact this
  have hG:w∈gatesIn C n o:= mem_filt.2 ⟨hw,hwn'⟩
  have hc:= hcard w hG
  have hch:ch C n w=(reads C n w).filter (fun c =>decide (c< w)):= by
    unfold ch
    rw [if_pos ⟨hwn',hj⟩]
  have hop:= hg _ (at_mem hj)
  rw [← gateAt_eq C n hj] at hop
  have hdesc:∀ v,v∈desc C n w ↔ v=w∨∃ c∈ch C n w,v∈desc C n c:= mem_desc C n w
  have hlenle:(ch C n w).toFinset.card≤ (ch C n w).length:= List.toFinset_card_le _
  by_cases hN:isNot C n w
  · right
    refine ⟨hwn',hN,?_⟩
    have hop':(gateAt C n w).op=GateOp.not:= hN.2
    have hreads:reads C n w=(gateAt C n w).inputs.take 1:= by
      unfold reads
      rw [if_pos hop']
    rw [show bnd C n w=1 from if_pos hN] at hc
    cases hin:(gateAt C n w).inputs with
    | nil =>
      rw [hin] at hreads
      rw [hch,hreads] at hc
      simp at hc
    | cons a l =>
      rw [hin] at hreads
      simp only [List.take_succ_cons,List.take_zero] at hreads
      have haw:a< w:= by
        by_contra h
        rw [hch,hreads] at hc
        simp [h] at hc
      have hcha:ch C n w=[a]:= by
        rw [hch,hreads]
        simp [haw]
      have haT:a∈desc C n o:= child_desc C n hw (hcha ▸ List.mem_singleton_self a)
      refine ⟨a,haT,haw,?_,?_⟩
      · ext v
        rw [hdesc,hcha]
        simp
      · intro f
        change value C (inp n f) w=!value C (inp n f) a
        rw [hval,hop',hin]
        simp [GateOp.eval,haw]
  · left
    refine ⟨hwn',hN,?_⟩
    have hop':(gateAt C n w).op ≠ GateOp.not:= fun c =>hN ⟨hwn',c⟩
    have hreads:reads C n w=(gateAt C n w).inputs:= by
      unfold reads
      rw [if_neg hop']
    rw [show bnd C n w=2 from if_neg hN] at hc
    have h2:= hop.2
    have hfl:= List.length_filter_le (fun c =>decide (c< w)) (gateAt C n w).inputs
    rw [hch,hreads] at hlenle hc
    have hlen2:(gateAt C n w).inputs.length=2:= by omega
    obtain ⟨a,b,hab⟩:= List.length_eq_two.1 hlen2
    rw [hab] at hlenle hc hfl
    have haw:a< w:= by
      by_contra h
      by_cases h':b< w <;> simp [h,h'] at hc
    have hbw:b< w:= by
      by_contra h
      simp [haw,h] at hc
    have hne:a ≠ b:= by
      intro h
      subst h
      simp [haw] at hc
    have hchab:ch C n w=[a,b]:= by
      rw [hch,hreads,hab]
      simp [haw,hbw]
    have haT:a∈desc C n o:= child_desc C n hw (by rw [hchab]; simp)
    have hbT:b∈desc C n o:= child_desc C n hw (by rw [hchab]; simp)
    refine ⟨a,haT,b,hbT,haw,hbw,?_,?_,?_⟩
    · exact sib_disj C n o huniq w a b hw (by rw [hchab]; simp) (by rw [hchab]; simp) hne
    · ext v
      rw [hdesc,hchab]
      simp
    · rcases hop.1 with h | h | h
      · left
        intro f
        change value C (inp n f) w=(value C (inp n f) a && value C (inp n f) b)
        rw [hval,h,hab]
        simp [GateOp.eval,haw,hbw]
      · right
        intro f
        change value C (inp n f) w=(value C (inp n f) a || value C (inp n f) b)
        rw [hval,h,hab]
        simp [GateOp.eval,haw,hbw]
      · exact absurd h hop'
def only (z:ℕ):ℕ→ Bool:= fun i =>decide (i=z)
def two (a b:ℕ):ℕ→ Bool:= fun i =>decide (i=a∨i=b)
def zero:ℕ→ Bool:= fun _ =>false
section nodes
variable {n:ℕ} {T:Finset ℕ} {V:ℕ→ (ℕ→ Bool)→ Bool} {S:ℕ→ Finset ℕ} {N:ℕ→ Prop}
  (H:∀ w∈T,Node n T V S N w)
def sup (n:ℕ) (S:ℕ→ Finset ℕ) (w:ℕ):Finset ℕ:= (S w).filter (fun i =>i< n)
theorem sup_bin {a b w:ℕ} (h:S w=insert w (S a ∪ S b)) (hw:n≤ w) (i:ℕ) :
    i∈sup n S w ↔ i∈sup n S a∨i∈sup n S b:= by
  unfold sup
  rw [h,Finset.filter_insert,if_neg (by omega),Finset.filter_union,mem_un]
theorem sup_un {a w:ℕ} (h:S w=insert w (S a)) (hw:n≤ w):sup n S w=sup n S a:= by
  unfold sup
  rw [h,Finset.filter_insert,if_neg (by omega)]
theorem sup_leaf {w:ℕ} (h:S w={w}) (hw:w< n):sup n S w={w}:= by
  unfold sup
  rw [h,Finset.filter_singleton,if_pos hw]
theorem sup_disj {a b:ℕ} (h:Disjoint (S a) (S b)) {i:ℕ} (ha:i∈sup n S a) (hb:i∈sup n S b):False :=
  disj_leftF.1 h (mem_filt.1 ha).1 (mem_filt.1 hb).1
include H
theorem self_mem:∀ w∈T,w∈S w:= by
  intro w hw
  rcases H w hw with ⟨_,h,_⟩ | ⟨_,_,a,_,b,_,_,_,_,h,_⟩ | ⟨_,_,a,_,_,h,_⟩
  · rw [h]
    exact Finset.mem_singleton_self _
  · rw [h]
    exact Finset.mem_insert_self _ _
  · rw [h]
    exact Finset.mem_insert_self _ _
theorem sup_ne:∀ w∈T,(sup n S w).Nonempty:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases H w hw with ⟨h1,h2,_⟩ | ⟨h0,_,a,ha,b,_,haw,_,_,h,_⟩ | ⟨h0,_,a,ha,haw,h,_⟩
    · rw [sup_leaf h2 h1]
      exact Finset.singleton_nonempty _
    · obtain ⟨i,hi⟩:= ih a haw ha
      exact ⟨i,(sup_bin h h0 i).2 (Or.inl hi)⟩
    · rw [sup_un h h0]
      exact ih a haw ha
theorem dep:∀ w∈T,∀ f g:ℕ→ Bool,(∀ i∈sup n S w,f i=g i)→ V w f=V w g:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw f g hfg
    rcases H w hw with ⟨h1,h2,h3⟩ | ⟨h0,_,a,ha,b,hb,haw,hbw,_,h,hv⟩ | ⟨h0,_,a,ha,haw,h,hv⟩
    · rw [h3,h3]
      exact hfg w (by rw [sup_leaf h2 h1]; simp)
    · have e1:= ih a haw ha f g (fun i hi =>hfg i ((sup_bin h h0 i).2 (Or.inl hi)))
      have e2:= ih b hbw hb f g (fun i hi =>hfg i ((sup_bin h h0 i).2 (Or.inr hi)))
      rcases hv with hv | hv <;> rw [hv,hv,e1,e2]
    · rw [hv,hv,ih a haw ha f g (fun i hi =>hfg i (by rw [sup_un h h0]; exact hi))]
theorem mono:∀ w∈T,(∀ v∈S w,¬ N v)→ ∀ f g:ℕ→ Bool,(∀ i,f i=true→ g i=true) →
    V w f=true→ V w g=true:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm f g hfg
    rcases H w hw with ⟨_,_,h3⟩ | ⟨_,_,a,ha,b,hb,haw,hbw,_,h,hv⟩ | ⟨_,hN,_⟩
    · rw [h3,h3]
      exact hfg w
    · have ma:= ih a haw ha (fun v hv =>hm v (by rw [h]; simp [hv])) f g hfg
      have mb:= ih b hbw hb (fun v hv =>hm v (by rw [h]; simp [hv])) f g hfg
      rcases hv with hv | hv <;> rw [hv,hv]
      · simp only [Bool.and_eq_true]
        exact fun p =>⟨ma p.1,mb p.2⟩
      · simp only [Bool.or_eq_true]
        exact fun p =>p.imp ma mb
    · exact absurd hN (hm w (self_mem H w hw))
theorem mono_zero:∀ w∈T,(∀ v∈S w,¬ N v)→ V w zero=false:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm
    rcases H w hw with ⟨_,_,h3⟩ | ⟨_,_,a,ha,b,hb,haw,hbw,_,h,hv⟩ | ⟨_,hN,_⟩
    · rw [h3]
      rfl
    · have ma:= ih a haw ha (fun v hv =>hm v (by rw [h]; simp [hv]))
      have mb:= ih b hbw hb (fun v hv =>hm v (by rw [h]; simp [hv]))
      rcases hv with hv | hv <;> rw [hv,ma,mb] <;> rfl
    · exact absurd hN (hm w (self_mem H w hw))
theorem off {w:ℕ} (hw:w∈T) (hm:∀ v∈S w,¬ N v) (f:ℕ→ Bool)
    (hf:∀ i∈sup n S w,f i=false):V w f=false :=
  (dep H w hw f zero hf).trans (mono_zero H w hw hm)
end nodes
def Pr {k:ℕ} (xi yi:Fin k→ ℕ) (s:Finset (Fin k)) (M:Finset (Finset (Fin k))) (f:ℕ→ Bool):Prop :=
  (∃ u∈s,f (xi u)=true∧f (yi u)=true) ∨
  ∃ e∈M,(∀ u∈e,f (xi u)=true)∨(∀ u∈e,f (yi u)=true)
theorem Pr_union {k:ℕ} (xi yi:Fin k→ ℕ) (s t:Finset (Fin k)) (M L:Finset (Finset (Fin k)))
    (f:ℕ→ Bool):Pr xi yi (s ∪ t) (M ∪ L) f ↔ Pr xi yi s M f∨Pr xi yi t L f:= by
  simp only [Pr,mem_un,or_and_right,exists_or]
  exact or_or_or_comm
theorem isM_union {k:ℕ} (s t:Finset (Fin k)) (M L:Finset (Finset (Fin k))) (hM:IsM M) (hL:IsM L)
    (hs:∀ e∈M,e ⊆ s) (ht:∀ e∈L,e ⊆ t) (hd:Disjoint s t) :
    IsM (M ∪ L)∧∀ e∈M ∪ L,e ⊆ s ∪ t:= by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro e he
    rcases mem_un.1 he with h | h
    · exact hM.1 e h
    · exact hL.1 e h
  · intro e he g hg hne
    rcases mem_un.1 he with h | h <;> rcases mem_un.1 hg with h' | h'
    · exact hM.2 e h g h' hne
    · exact hd.mono (hs e h) (ht g h')
    · exact (hd.mono (hs g h') (ht e h)).symm
    · exact hL.2 e h g h' hne
  · intro e he
    rcases mem_un.1 he with h | h
    · exact (hs e h).trans Finset.subset_union_left
    · exact (ht e h).trans Finset.subset_union_right
section classify
variable {n:ℕ} {T:Finset ℕ} {V:ℕ→ (ℕ→ Bool)→ Bool} {S:ℕ→ Finset ℕ} {N:ℕ→ Prop}
  (H:∀ w∈T,Node n T V S N w) {k:ℕ} (xi yi:Fin k→ ℕ)
  (hx:∀ u v,xi u=xi v→ u=v) (hy:∀ u v,yi u=yi v→ u=v) (hxy:∀ u v,xi u ≠ yi v)
include H
theorem and_child {a:ℕ} (ha:a∈T) (ma:∀ v∈S a,¬ N v) (f:ℕ→ Bool)
    (h1:∀ z∈sup n S a,V a (only z)=true):V a f=true ↔ ∃ z∈sup n S a,f z=true:= by
  constructor
  · intro h
    by_contra c
    have:V a f=false:= off H ha ma f (fun i hi => by
      cases hfi:f i
      · rfl
      · exact absurd ⟨i,hi,hfi⟩ c)
    rw [this] at h
    exact Bool.false_ne_true h
  · rintro ⟨z,hz,hfz⟩
    apply mono H a ha ma (only z) f _ (h1 z hz)
    intro i hi
    simp only [only,decide_eq_true_eq] at hi
    rw [hi]
    exact hfz
include hx hy hxy
theorem cls_id:∀ w∈T,(∀ v∈S w,¬ N v)→ ∀ s:Finset (Fin k),
    (∀ i,i∈sup n S w ↔ ∃ u∈s,i=xi u∨i=yi u) →
    (∀ u∈s,∀ v∈s,V w (two (xi u) (yi v))=decide (u=v)) →
    (∀ z,V w (only z)=false) →
    ∃ M:Finset (Finset (Fin k)),IsM M∧(∀ e∈M,e ⊆ s)∧∀ f,(V w f=true ↔ Pr xi yi s M f):= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm s hs hval hsing
    rcases H w hw with ⟨h1,h2,_⟩ | ⟨h0,_,a,ha,b,hb,haw,hbw,hd,h,hv⟩ | ⟨_,hN,_⟩
    · exfalso
      obtain ⟨i,hi⟩:= sup_ne H w hw
      obtain ⟨u,hu,_⟩:= (hs i).1 hi
      have e1:xi u∈sup n S w:= (hs _).2 ⟨u,hu,Or.inl rfl⟩
      have e2:yi u∈sup n S w:= (hs _).2 ⟨u,hu,Or.inr rfl⟩
      rw [sup_leaf h2 h1,mem_oneF] at e1 e2
      exact hxy u u (e1.trans e2.symm)
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma:∀ v∈S a,¬ N v:= fun v hv =>hm v (by rw [h]; simp [hv])
    have mb:∀ v∈S b,¬ N v:= fun v hv =>hm v (by rw [h]; simp [hv])
    have hsup:= sup_bin (n:= n) h h0
    have disj:∀ i,i∈sup n S a→ i∈sup n S b→ False:= fun i =>sup_disj hd
    have inab:∀ u∈s,(xi u∈sup n S a∨xi u∈sup n S b)∧(yi u∈sup n S a∨yi u∈sup n S b) :=
      fun u hu =>⟨(hsup _).1 ((hs _).2 ⟨u,hu,Or.inl rfl⟩),(hsup _).1 ((hs _).2 ⟨u,hu,Or.inr rfl⟩)⟩
    have offt:∀ c∈T,(∀ v∈S c,¬ N v)→ ∀ p q:ℕ,p ∉ sup n S c→ q ∉ sup n S c →
        V c (two p q)=false:= by
      intro c hc mc p q hp hq
      apply off H hc mc
      intro i hi
      have e1:i ≠ p:= fun e =>hp (e ▸ hi)
      have e2:i ≠ q:= fun e =>hq (e ▸ hi)
      simp [two,e1,e2]
    have onel:∀ c∈T,∀ p q:ℕ,q ∉ sup n S c→ V c (two p q)=V c (only p):= by
      intro c hc p q hq
      apply dep H c hc
      intro i hi
      have e:i ≠ q:= fun e =>hq (e ▸ hi)
      simp [two,only,e]
    have oner:∀ c∈T,∀ p q:ℕ,p ∉ sup n S c→ V c (two p q)=V c (only q):= by
      intro c hc p q hp
      apply dep H c hc
      intro i hi
      have e:i ≠ p:= fun e =>hp (e ▸ hi)
      simp [two,only,e]
    rcases hv with hv | hv
    · have h1:∀ u∈s,V a (two (xi u) (yi u))=true∧V b (two (xi u) (yi u))=true:= by
        intro u hu
        have:= hval u hu u hu
        rw [hv] at this
        simpa using this
      have h2:∀ u∈s,(xi u∈sup n S a∨yi u∈sup n S a)∧(xi u∈sup n S b∨yi u∈sup n S b):= by
        intro u hu
        constructor
        · by_contra c
          rw [not_or] at c
          have:= offt a ha ma _ _ c.1 c.2
          rw [(h1 u hu).1] at this
          exact Bool.noConfusion this
        · by_contra c
          rw [not_or] at c
          have:= offt b hb mb _ _ c.1 c.2
          rw [(h1 u hu).2] at this
          exact Bool.noConfusion this
      have h3a:∀ z∈sup n S a,V a (only z)=true:= by
        intro z hz
        obtain ⟨u,hu,rfl | rfl⟩:= (hs z).1 ((hsup z).2 (Or.inl hz))
        · have:yi u ∉ sup n S a:= by
            intro c
            rcases (h2 u hu).2 with d | d
            · exact disj _ hz d
            · exact disj _ c d
          rw [← onel a ha (xi u) (yi u) this]
          exact (h1 u hu).1
        · have:xi u ∉ sup n S a:= by
            intro c
            rcases (h2 u hu).2 with d | d
            · exact disj _ c d
            · exact disj _ hz d
          rw [← oner a ha (xi u) (yi u) this]
          exact (h1 u hu).1
      have h3b:∀ z∈sup n S b,V b (only z)=true:= by
        intro z hz
        obtain ⟨u,hu,rfl | rfl⟩:= (hs z).1 ((hsup z).2 (Or.inr hz))
        · have:yi u ∉ sup n S b:= by
            intro c
            rcases (h2 u hu).1 with d | d
            · exact disj _ d hz
            · exact disj _ d c
          rw [← onel b hb (xi u) (yi u) this]
          exact (h1 u hu).2
        · have:xi u ∉ sup n S b:= by
            intro c
            rcases (h2 u hu).1 with d | d
            · exact disj _ d c
            · exact disj _ d hz
          rw [← oner b hb (xi u) (yi u) this]
          exact (h1 u hu).2
      have core:∀ a∈T,∀ b∈T,(∀ v∈S a,¬ N v)→ (∀ v∈S b,¬ N v) →
          (∀ i,i∈sup n S w ↔ i∈sup n S a∨i∈sup n S b) →
          (∀ i,i∈sup n S a→ i∈sup n S b→ False) →
          (∀ z∈sup n S a,V a (only z)=true)→ (∀ z∈sup n S b,V b (only z)=true) →
          (∀ f,V w f=(V a f && V b f)) →
          ∀ p∈s,∀ q∈s,q ≠ p→ xi p∈sup n S a →
          ∃ M:Finset (Finset (Fin k)),IsM M∧(∀ e∈M,e ⊆ s)∧∀ f,(V w f=true ↔ Pr xi yi s M f):= by
        intro a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp hpa
        have cross:∀ u∈s,∀ v∈s,u ≠ v→ xi u∈sup n S a→ yi v∈sup n S b→ False:= by
          intro u hu v hv' huv h1 h2
          have e1:V a (two (xi u) (yi v))=true :=
            (and_child H ha ma _ h3a).2 ⟨_,h1,by simp [two]⟩
          have e2:V b (two (xi u) (yi v))=true :=
            (and_child H hb mb _ h3b).2 ⟨_,h2,by simp [two]⟩
          have:= hval u hu v hv'
          rw [hv,e1,e2] at this
          simp [huv] at this
        have cross':∀ u∈s,∀ v∈s,u ≠ v→ xi u∈sup n S b→ yi v∈sup n S a→ False:= by
          intro u hu v hv' huv h1 h2
          have e1:V a (two (xi u) (yi v))=true :=
            (and_child H ha ma _ h3a).2 ⟨_,h2,by simp [two]⟩
          have e2:V b (two (xi u) (yi v))=true :=
            (and_child H hb mb _ h3b).2 ⟨_,h1,by simp [two]⟩
          have:= hval u hu v hv'
          rw [hv,e1,e2] at this
          simp [huv] at this
        have mem:∀ u∈s,∀ z,(z=xi u∨z=yi u)→ z∈sup n S a∨z∈sup n S b:= by
          intro u hu z hz
          exact (hsup z).1 ((hs z).2 ⟨u,hu,hz⟩)
        have yqa:yi q∈sup n S a :=
          (mem q hq _ (Or.inr rfl)).resolve_right (fun c =>cross p hp q hq hqp.symm hpa c)
        have xqb:xi q∈sup n S b:= by
          refine (mem q hq _ (Or.inl rfl)).resolve_left (fun c =>?_)
          have:V b (two (xi q) (yi q))=false:= by
            apply off H hb mb
            intro i hi
            have e1:i ≠ xi q:= fun e =>disj _ c (e ▸ hi)
            have e2:i ≠ yi q:= fun e =>disj _ yqa (e ▸ hi)
            simp [two,e1,e2]
          have h:= hval q hq q hq
          rw [hv,this] at h
          simp at h
        have ypb:yi p∈sup n S b :=
          (mem p hp _ (Or.inr rfl)).resolve_left (fun c =>cross' q hq p hp hqp xqb c)
        have only2:∀ r∈s,r=p∨r=q:= by
          intro r hr
          by_contra c
          rw [not_or] at c
          rcases mem r hr (yi r) (Or.inr rfl) with d | d
          · exact cross' q hq r hr (Ne.symm c.2) xqb d
          · exact cross p hp r hr (Ne.symm c.1) hpa d
        have hs2:s={p,q}:= by
          ext r
          simp only [mem_ins,mem_oneF]
          constructor
          · exact only2 r
          · rintro (rfl | rfl) <;> assumption
        have ma':∀ z,z∈sup n S a ↔ z=xi p∨z=yi q:= by
          intro z
          constructor
          · intro hz
            obtain ⟨u,hu,e⟩:= (hs z).1 ((hsup z).2 (Or.inl hz))
            rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
            · exact Or.inl rfl
            · exact (disj _ hz ypb).elim
            · exact (disj _ hz xqb).elim
            · exact Or.inr rfl
          · rintro (rfl | rfl) <;> assumption
        have mb':∀ z,z∈sup n S b ↔ z=xi q∨z=yi p:= by
          intro z
          constructor
          · intro hz
            obtain ⟨u,hu,e⟩:= (hs z).1 ((hsup z).2 (Or.inr hz))
            rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
            · exact (disj _ hpa hz).elim
            · exact Or.inr rfl
            · exact Or.inl rfl
            · exact (disj _ yqa hz).elim
          · rintro (rfl | rfl) <;> assumption
        refine ⟨{{p,q}},⟨?_,?_⟩,?_,?_⟩
        · intro e he
          rw [mem_oneF] at he
          rw [he,Finset.card_pair hqp.symm]
        · intro e he g hg hne
          rw [mem_oneF] at he hg
          exact absurd (he.trans hg.symm) hne
        · intro e he
          rw [mem_oneF] at he
          rw [he,hs2]
        · intro f
          rw [hv,Bool.and_eq_true,and_child H ha ma f h3a,and_child H hb mb f h3b]
          simp only [ma',mb',or_and_right,exists_or,exists_eq_left]
          rw [hs2]
          simp only [Pr,mem_ins,mem_oneF,or_and_right,exists_or,exists_eq_left,
            forall_eq_or_imp,forall_eq]
          tauto
      obtain ⟨i,hi⟩:= sup_ne H w hw
      obtain ⟨p,hp,_⟩:= (hs i).1 hi
      by_cases hq:∃ q∈s,q ≠ p
      · obtain ⟨q,hq,hqp⟩:= hq
        rcases (inab p hp).1 with c | c
        · exact core a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp c
        · exact core b hb a ha mb ma (fun i =>(hsup i).trans or_comm) (fun i x y =>disj i y x) h3b h3a
            (fun f => by rw [hv,Bool.and_comm]) p hp q hq hqp c
      · have only1:∀ r∈s,r=p:= fun r hr => by
          by_contra c
          exact hq ⟨r,hr,c⟩
        have hs1:s={p}:= by
          ext r
          rw [mem_oneF]
          exact ⟨only1 r,fun e =>e ▸ hp⟩
        have vars:∀ z,z∈sup n S w→ z=xi p∨z=yi p:= by
          intro z hz
          obtain ⟨u,hu,e⟩:= (hs z).1 hz
          rwa [only1 u hu] at e
        refine ⟨∅,isM_empty,by simp,?_⟩
        intro f
        rw [hv,Bool.and_eq_true,and_child H ha ma f h3a,and_child H hb mb f h3b]
        have goal:Pr xi yi s ∅ f ↔ f (xi p)=true∧f (yi p)=true:= by
          simp [Pr,hs1]
        rw [goal]
        have key:(xi p∈sup n S a∧yi p∈sup n S b)∨(yi p∈sup n S a∧xi p∈sup n S b):= by
          rcases (inab p hp).1 with c | c
          · rcases (h2 p hp).2 with d | d
            · exact (disj _ c d).elim
            · exact Or.inl ⟨c,d⟩
          · rcases (h2 p hp).1 with d | d
            · exact (disj _ d c).elim
            · exact Or.inr ⟨d,c⟩
        have uni:∀ c:ℕ,∀ z0,z0∈sup n S c→ (∀ z∈sup n S c,z=z0) →
            ((∃ z∈sup n S c,f z=true) ↔ f z0=true):= by
          intro c z0 h0' hu
          constructor
          · rintro ⟨z,hz,hf⟩
            rwa [hu z hz] at hf
          · intro hf
            exact ⟨z0,h0',hf⟩
        rcases key with ⟨k1,k2⟩ | ⟨k1,k2⟩
        · rw [uni a (xi p) k1,uni b (yi p) k2]
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
            · exact (disj _ k1 (e ▸ hz)).elim
            · exact e
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
            · exact e
            · exact (disj _ (e ▸ hz) k2).elim
        · rw [uni a (yi p) k1,uni b (xi p) k2,and_comm]
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
            · exact e
            · exact (disj _ k1 (e ▸ hz)).elim
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
            · exact (disj _ (e ▸ hz) k2).elim
            · exact e
    · have sa0:∀ z,V a (only z)=false∧V b (only z)=false:= by
        intro z
        have:= hsing z
        rw [hv] at this
        simpa using this
      have tog:∀ u∈s,(xi u∈sup n S a∧yi u∈sup n S a)∨(xi u∈sup n S b∧yi u∈sup n S b):= by
        intro u hu
        have tr:V w (two (xi u) (yi u))=true:= by
          rw [hval u hu u hu]
          simp
        rw [hv] at tr
        rcases (inab u hu).1 with c1 | c1 <;> rcases (inab u hu).2 with c2 | c2
        · exact Or.inl ⟨c1,c2⟩
        · rw [onel a ha _ _ (fun c =>disj _ c c2),oner b hb _ _ (fun c =>disj _ c1 c),
            (sa0 _).1,(sa0 _).2] at tr
          exact Bool.noConfusion tr
        · rw [oner a ha _ _ (fun c =>disj _ c c1),onel b hb _ _ (fun c =>disj _ c2 c),
            (sa0 _).1,(sa0 _).2] at tr
          exact Bool.noConfusion tr
        · exact Or.inr ⟨c1,c2⟩
      have part:∀ a∈T,∀ b∈T,a< w→ (∀ v∈S a,¬ N v)→ (∀ v∈S b,¬ N v) →
          (∀ i,i∈sup n S w ↔ i∈sup n S a∨i∈sup n S b) →
          (∀ i,i∈sup n S a→ i∈sup n S b→ False) →
          (∀ f,V w f=(V a f || V b f)) →
          (∀ u∈s,(xi u∈sup n S a∧yi u∈sup n S a)∨(xi u∈sup n S b∧yi u∈sup n S b)) →
          ∃ M:Finset (Finset (Fin k)),IsM M∧(∀ e∈M,e ⊆ s.filter (fun u =>xi u∈sup n S a)) ∧
            ∀ f,(V a f=true ↔ Pr xi yi (s.filter (fun u =>xi u∈sup n S a)) M f):= by
        intro a ha b hb haw ma mb hsup disj hv tog
        apply ih a haw ha ma
        · intro i
          constructor
          · intro hi
            obtain ⟨u,hu,e⟩:= (hs i).1 ((hsup i).2 (Or.inl hi))
            refine ⟨u,mem_filt.2 ⟨hu,?_⟩,e⟩
            rcases tog u hu with c | c
            · exact c.1
            · rcases e with e | e
              · exact (disj _ (e ▸ hi) c.1).elim
              · exact (disj _ (e ▸ hi) c.2).elim
          · rintro ⟨u,hu,e⟩
            rw [mem_filt] at hu
            rcases tog u hu.1 with c | c
            · rcases e with rfl | rfl
              · exact c.1
              · exact c.2
            · exact (disj _ hu.2 c.1).elim
        · intro u hu v hv'
          rw [mem_filt] at hu hv'
          have t:= hval u hu.1 v hv'.1
          rw [hv] at t
          have ub:xi u ∉ sup n S b:= fun c =>disj _ hu.2 c
          have vb:yi v ∉ sup n S b:= by
            intro c
            rcases tog v hv'.1 with d | d
            · exact disj _ d.2 c
            · exact disj _ hv'.2 d.1
          rw [offt b hb mb _ _ ub vb,Bool.or_false] at t
          exact t
        · intro z
          have:= hsing z
          rw [hv] at this
          exact (Bool.or_eq_false_iff.1 this).1
      obtain ⟨Ma,hMa,sMa,va⟩:= part a ha b hb haw ma mb hsup disj hv tog
      obtain ⟨Mb,hMb,sMb,vb⟩:= part b hb a ha hbw mb ma (fun i =>(hsup i).trans or_comm)
        (fun i x y =>disj i y x) (fun f => by rw [hv,Bool.or_comm]) (fun u hu =>(tog u hu).symm)
      have hsplit:s.filter (fun u =>xi u∈sup n S a) ∪ s.filter (fun u =>xi u∈sup n S b)=s:= by
        rw [← Finset.filter_or]
        apply Finset.filter_true_of_mem
        intro u hu
        exact (inab u hu).1
      have hdj:Disjoint (s.filter (fun u =>xi u∈sup n S a)) (s.filter (fun u =>xi u∈sup n S b)):= by
        rw [disj_leftF]
        intro u h1 h2
        exact disj _ (mem_filt.1 h1).2 (mem_filt.1 h2).2
      obtain ⟨hM,hMs⟩:= isM_union _ _ Ma Mb hMa hMb sMa sMb hdj
      rw [hsplit] at hMs
      refine ⟨Ma ∪ Mb,hM,hMs,?_⟩
      intro f
      rw [hv,Bool.or_eq_true,va,vb,← Pr_union,hsplit]
theorem cls_z (z:ℕ) (hzx:∀ u,z ≠ xi u) (hzy:∀ u,z ≠ yi u):∀ w∈T,(∀ v∈S w,¬ N v) →
    ∀ s:Finset (Fin k),
    (∀ i,i∈sup n S w ↔ i=z∨∃ u∈s,i=xi u∨i=yi u) →
    (∀ u∈s,∀ v∈s,V w (two (xi u) (yi v))=decide (u=v)) →
    (∀ i,i ≠ z→ V w (only i)=false)→ V w (only z)=true →
    ∃ M:Finset (Finset (Fin k)),IsM M∧(∀ e∈M,e ⊆ s) ∧
      ∀ f,(V w f=true ↔ f z=true∨Pr xi yi s M f):= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm s hs hval hsing hz
    rcases H w hw with ⟨h1,h2,h3⟩ | ⟨h0,_,a,ha,b,hb,haw,hbw,hd,h,hv⟩ | ⟨_,hN,_⟩
    · have ez:z=w:= by
        have:= (hs z).2 (Or.inl rfl)
        rwa [sup_leaf h2 h1,mem_oneF] at this
      have es:s=∅:= by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        have:= (hs (xi u)).2 (Or.inr ⟨u,hu,Or.inl rfl⟩)
        rw [sup_leaf h2 h1,mem_oneF] at this
        exact hzx u (ez.trans this.symm)
      refine ⟨∅,isM_empty,by simp,fun f =>?_⟩
      rw [h3,es,ez]
      simp [Pr]
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma:∀ v∈S a,¬ N v:= fun v hv =>hm v (by rw [h]; simp [hv])
    have mb:∀ v∈S b,¬ N v:= fun v hv =>hm v (by rw [h]; simp [hv])
    have hsup:= sup_bin (n:= n) h h0
    have disj:∀ i,i∈sup n S a→ i∈sup n S b→ False:= fun i =>sup_disj hd
    have core:∀ a∈T,∀ b∈T,a< w→ b< w→ (∀ v∈S a,¬ N v)→ (∀ v∈S b,¬ N v) →
        (∀ i,i∈sup n S w ↔ i∈sup n S a∨i∈sup n S b) →
        (∀ i,i∈sup n S a→ i∈sup n S b→ False) →
        (∀ f,V w f=(V a f || V b f))→ z∈sup n S a →
        ∃ M:Finset (Finset (Fin k)),IsM M∧(∀ e∈M,e ⊆ s) ∧
          ∀ f,(V w f=true ↔ f z=true∨Pr xi yi s M f):= by
      intro a ha b hb haw hbw ma mb hsup disj hv hza
      have zb:z ∉ sup n S b:= disj z hza
      have bz:V b (only z)=false:= by
        apply off H hb mb
        intro i hi
        have:i ≠ z:= fun e =>zb (e ▸ hi)
        simp [only,this]
      have asing:∀ i,i ≠ z→ V a (only i)=false:= by
        intro i hi
        have:= hsing i hi
        rw [hv] at this
        exact (Bool.or_eq_false_iff.1 this).1
      have bsing:∀ i,V b (only i)=false:= by
        intro i
        by_cases e:i=z
        · rw [e,bz]
        · have:= hsing i e
          rw [hv] at this
          exact (Bool.or_eq_false_iff.1 this).2
      have az:V a (only z)=true:= by
        have:= hz
        rw [hv,bz,Bool.or_false] at this
        exact this
      have inab:∀ u∈s,∀ i,(i=xi u∨i=yi u)→ i∈sup n S a∨i∈sup n S b :=
        fun u hu i e =>(hsup i).1 ((hs i).2 (Or.inr ⟨u,hu,e⟩))
      have onel:∀ c∈T,∀ p q:ℕ,q ∉ sup n S c→ V c (two p q)=V c (only p):= by
        intro c hc p q hq
        apply dep H c hc
        intro i hi
        have e:i ≠ q:= fun e =>hq (e ▸ hi)
        simp [two,only,e]
      have oner:∀ c∈T,∀ p q:ℕ,p ∉ sup n S c→ V c (two p q)=V c (only q):= by
        intro c hc p q hp
        apply dep H c hc
        intro i hi
        have e:i ≠ p:= fun e =>hp (e ▸ hi)
        simp [two,only,e]
      have tog:∀ u∈s,(xi u∈sup n S a∧yi u∈sup n S a)∨(xi u∈sup n S b∧yi u∈sup n S b):= by
        intro u hu
        have tr:V w (two (xi u) (yi u))=true:= by
          rw [hval u hu u hu]
          simp
        rw [hv] at tr
        rcases inab u hu _ (Or.inl rfl) with c1 | c1 <;> rcases inab u hu _ (Or.inr rfl) with c2 | c2
        · exact Or.inl ⟨c1,c2⟩
        · rw [onel a ha _ _ (fun c =>disj _ c c2),oner b hb _ _ (fun c =>disj _ c1 c),
            asing _ (hzx u).symm,bsing] at tr
          exact Bool.noConfusion tr
        · rw [oner a ha _ _ (fun c =>disj _ c c1),onel b hb _ _ (fun c =>disj _ c2 c),
            asing _ (hzy u).symm,bsing] at tr
          exact Bool.noConfusion tr
        · exact Or.inr ⟨c1,c2⟩
      let sa:= s.filter (fun u =>xi u∈sup n S a)
      let sb:= s.filter (fun u =>xi u∈sup n S b)
      have mema:∀ u∈sa,xi u∈sup n S a∧yi u∈sup n S a:= by
        intro u hu
        have hu':= mem_filt.1 hu
        rcases tog u hu'.1 with c | c
        · exact c
        · exact (disj _ hu'.2 c.1).elim
      have memb:∀ u∈sb,xi u∈sup n S b∧yi u∈sup n S b:= by
        intro u hu
        have hu':= mem_filt.1 hu
        rcases tog u hu'.1 with c | c
        · exact (disj _ c.1 hu'.2).elim
        · exact c
      have tos:∀ u∈s,∀ i,(i=xi u∨i=yi u)→ (i∈sup n S a→ u∈sa)∧(i∈sup n S b→ u∈sb):= by
        intro u hu i e
        constructor
        · intro hi
          refine mem_filt.2 ⟨hu,?_⟩
          rcases tog u hu with c | c
          · exact c.1
          · rcases e with e | e
            · exact (disj _ (e ▸ hi) c.1).elim
            · exact (disj _ (e ▸ hi) c.2).elim
        · intro hi
          refine mem_filt.2 ⟨hu,?_⟩
          rcases tog u hu with c | c
          · rcases e with e | e
            · exact (disj _ c.1 (e ▸ hi)).elim
            · exact (disj _ c.2 (e ▸ hi)).elim
          · exact c.1
      obtain ⟨Ma,hMa,sMa,va⟩:= ih a haw ha ma sa (by
          intro i
          constructor
          · intro hi
            rcases (hs i).1 ((hsup i).2 (Or.inl hi)) with e | ⟨u,hu,e⟩
            · exact Or.inl e
            · exact Or.inr ⟨u,(tos u hu i e).1 hi,e⟩
          · rintro (rfl | ⟨u,hu,rfl | rfl⟩)
            · exact hza
            · exact (mema u hu).1
            · exact (mema u hu).2) (by
          intro u hu v hv'
          have t:= hval u (mem_filt.1 hu).1 v (mem_filt.1 hv').1
          rw [hv] at t
          have:V b (two (xi u) (yi v))=false:= by
            apply off H hb mb
            intro i hi
            have e1:i ≠ xi u:= fun e =>disj _ (mema u hu).1 (e ▸ hi)
            have e2:i ≠ yi v:= fun e =>disj _ (mema v hv').2 (e ▸ hi)
            simp [two,e1,e2]
          rw [this,Bool.or_false] at t
          exact t) asing az
      obtain ⟨Mb,hMb,sMb,vb⟩:= cls_id H xi yi hx hy hxy b hb mb sb (by
          intro i
          constructor
          · intro hi
            rcases (hs i).1 ((hsup i).2 (Or.inr hi)) with e | ⟨u,hu,e⟩
            · exact (zb (e ▸ hi)).elim
            · exact ⟨u,(tos u hu i e).2 hi,e⟩
          · rintro ⟨u,hu,rfl | rfl⟩
            · exact (memb u hu).1
            · exact (memb u hu).2) (by
          intro u hu v hv'
          have t:= hval u (mem_filt.1 hu).1 v (mem_filt.1 hv').1
          rw [hv] at t
          have:V a (two (xi u) (yi v))=false:= by
            have e1:xi u ∉ sup n S a:= fun c =>disj _ c (memb u hu).1
            have e2:yi v ∉ sup n S a:= fun c =>disj _ c (memb v hv').2
            have:V a (two (xi u) (yi v))=V a zero:= by
              apply dep H a ha
              intro i hi
              have f1:i ≠ xi u:= fun e =>e1 (e ▸ hi)
              have f2:i ≠ yi v:= fun e =>e2 (e ▸ hi)
              simp [two,zero,f1,f2]
            rw [this,mono_zero H a ha ma]
          rw [this,Bool.false_or] at t
          exact t) bsing
      have hsplit:sa ∪ sb=s:= by
        simp only [sa,sb]
        rw [← Finset.filter_or]
        apply Finset.filter_true_of_mem
        intro u hu
        exact inab u hu _ (Or.inl rfl)
      have hdj:Disjoint sa sb:= by
        rw [disj_leftF]
        intro u h1 h2
        exact disj _ (mem_filt.1 h1).2 (mem_filt.1 h2).2
      obtain ⟨hM,hMs⟩:= isM_union _ _ Ma Mb hMa hMb sMa sMb hdj
      rw [hsplit] at hMs
      refine ⟨Ma ∪ Mb,hM,hMs,?_⟩
      intro f
      rw [hv,Bool.or_eq_true,va,vb,or_assoc,← Pr_union,hsplit]
    rcases hv with hv | hv
    · exfalso
      rw [hv,Bool.and_eq_true] at hz
      have off1:∀ c∈T,(∀ v∈S c,¬ N v)→ z ∉ sup n S c→ V c (only z)=false:= by
        intro c hc mc hzc
        apply off H hc mc
        intro i hi
        have:i ≠ z:= fun e =>hzc (e ▸ hi)
        simp [only,this]
      by_cases c:z∈sup n S a
      · have:= off1 b hb mb (disj z c)
        rw [hz.2] at this
        exact Bool.noConfusion this
      · have:= off1 a ha ma c
        rw [hz.1] at this
        exact Bool.noConfusion this
    · rcases (hsup z).1 ((hs z).2 (Or.inl rfl)) with c | c
      · exact core a ha b hb haw hbw ma mb hsup disj hv c
      · exact core b hb a ha hbw haw mb ma (fun i =>(hsup i).trans or_comm) (fun i x y =>disj i y x)
          (fun f => by rw [hv,Bool.or_comm]) c
end classify
theorem no_crown {n:ℕ} {T:Finset ℕ} {V:ℕ→ (ℕ→ Bool)→ Bool} {S:ℕ→ Finset ℕ} {N:ℕ→ Prop}
    (H:∀ w∈T,Node n T V S N w) {k:ℕ} (hk:3≤ k) (xi yi:Fin k→ ℕ)
    (hx:∀ u v,xi u=xi v→ u=v) (hy:∀ u v,yi u=yi v→ u=v) (hxy:∀ u v,xi u ≠ yi v)
    (z:ℕ) (hzx:∀ u,z ≠ xi u) (hzy:∀ u,z ≠ yi u) :
    ∀ w∈T,(∀ v∈S w,¬ N v) →
      (∀ u v,V w (two (xi u) (yi v))=decide (u ≠ v)) →
      (∀ u,V w (two (xi u) z)=true)→ V w (only z)=false→ False:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm hval hcol hz
    have p0:0< k:= by omega
    have p1:1< k:= by omega
    have p2:2< k:= by omega
    let i0:Fin k:= ⟨0,p0⟩
    let i1:Fin k:= ⟨1,p1⟩
    let i2:Fin k:= ⟨2,p2⟩
    have n01:i0 ≠ i1:= by simp [i0,i1,fin_eq]
    have n02:i0 ≠ i2:= by simp [i0,i2,fin_eq]
    have n12:i1 ≠ i2:= by simp [i1,i2,fin_eq]
    have sing:∀ u,V w (only (xi u))=false∧V w (only (yi u))=false:= by
      intro u
      have h0:V w (two (xi u) (yi u))=false:= by
        rw [hval]
        simp
      constructor
      · by_contra c
        rw [Bool.not_eq_false] at c
        have:= mono H w hw hm (only (xi u)) (two (xi u) (yi u)) (fun i hi => by
          simp only [only,two,decide_eq_true_eq] at hi ⊢
          exact Or.inl hi) c
        rw [h0] at this
        exact Bool.noConfusion this
      · by_contra c
        rw [Bool.not_eq_false] at c
        have:= mono H w hw hm (only (yi u)) (two (xi u) (yi u)) (fun i hi => by
          simp only [only,two,decide_eq_true_eq] at hi ⊢
          exact Or.inr hi) c
        rw [h0] at this
        exact Bool.noConfusion this
    rcases H w hw with ⟨_,_,h3⟩ | ⟨h0,_,a,ha,b,hb,haw,hbw,hd,h,hv⟩ | ⟨_,hN,_⟩
    · have e1:= hval i0 i1
      have e2:= hval i1 i0
      rw [h3] at e1 e2
      simp only [two,n01,n01.symm,ne_eq,not_false_eq_true,decide_true,decide_eq_true_eq] at e1 e2
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact n01 (hx _ _ (e1.symm.trans e2))
      · exact hxy _ _ (e1.symm.trans e2)
      · exact hxy _ _ (e2.symm.trans e1)
      · exact n01 (hy _ _ (e2.symm.trans e1))
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma:∀ v∈S a,¬ N v:= fun v hv =>hm v (by rw [h]; simp [hv])
    have mb:∀ v∈S b,¬ N v:= fun v hv =>hm v (by rw [h]; simp [hv])
    have hsup:= sup_bin (n:= n) h h0
    have disj:∀ i,i∈sup n S a→ i∈sup n S b→ False:= fun i =>sup_disj hd
    have onel:∀ c∈T,∀ p q:ℕ,q ∉ sup n S c→ V c (two p q)=V c (only p):= by
      intro c hc p q hq
      apply dep H c hc
      intro i hi
      have e:i ≠ q:= fun e =>hq (e ▸ hi)
      simp [two,only,e]
    have oner:∀ c∈T,∀ p q:ℕ,p ∉ sup n S c→ V c (two p q)=V c (only q):= by
      intro c hc p q hp
      apply dep H c hc
      intro i hi
      have e:i ≠ p:= fun e =>hp (e ▸ hi)
      simp [two,only,e]
    rcases hv with hv | hv
    · have nab:V a zero=false∧V b zero=false:= ⟨mono_zero H a ha ma,mono_zero H b hb mb⟩
      have both:∀ u v:Fin k,u ≠ v→ V a (two (xi u) (yi v))=true∧V b (two (xi u) (yi v))=true:= by
        intro u v huv
        have:= hval u v
        rw [hv] at this
        simpa [huv] using this
      have one:∀ c∈T,(∀ v∈S c,¬ N v)→ ∀ p q:ℕ,V c (two p q)=true →
          p∈sup n S c∨q∈sup n S c:= by
        intro c hc mc p q ht
        by_contra c'
        rw [not_or] at c'
        have:V c (two p q)=false:= by
          apply off H hc mc
          intro i hi
          have e1:i ≠ p:= fun e =>c'.1 (e ▸ hi)
          have e2:i ≠ q:= fun e =>c'.2 (e ▸ hi)
          simp [two,e1,e2]
        rw [this] at ht
        exact Bool.noConfusion ht
      have core:∀ a∈T,∀ b∈T,(∀ v∈S a,¬ N v)→ (∀ v∈S b,¬ N v) →
          (∀ i,i∈sup n S a→ i∈sup n S b→ False) →
          (∀ u v:Fin k,u ≠ v→ V a (two (xi u) (yi v))=true∧V b (two (xi u) (yi v))=true) →
          (∀ f,V w f=(V a f && V b f))→ xi i0∈sup n S a→ False:= by
        intro a ha b hb ma mb disj both hv h0a
        have split:∀ u v:Fin k,u ≠ v →
            (xi u∈sup n S a→ yi v∈sup n S b)∧(yi v∈sup n S b→ xi u∈sup n S a):= by
          intro u v huv
          have c1:= one a ha ma _ _ (both u v huv).1
          have c2:= one b hb mb _ _ (both u v huv).2
          constructor
          · intro h1
            rcases c2 with c2 | c2
            · exact (disj _ h1 c2).elim
            · exact c2
          · intro h2
            rcases c1 with c1 | c1
            · exact c1
            · exact (disj _ c1 h2).elim
        have y1:= (split i0 i1 n01).1 h0a
        have x2:= (split i2 i1 n12.symm).2 y1
        have y0:= (split i2 i0 n02.symm).1 x2
        have y2:= (split i0 i2 n02).1 h0a
        have x1:= (split i1 i2 n12).2 y2
        have e1:V a (two (xi i0) (yi i0))=true:= by
          rw [onel a ha _ _ (fun c =>disj _ c y0),← onel a ha _ (yi i1) (fun c =>disj _ c y1)]
          exact (both i0 i1 n01).1
        have e2:V b (two (xi i0) (yi i0))=true:= by
          rw [oner b hb _ _ (fun c =>disj _ h0a c),← oner b hb (xi i1) _ (fun c =>disj _ x1 c)]
          exact (both i1 i0 n01.symm).2
        have:= hval i0 i0
        rw [hv,e1,e2] at this
        simp at this
      rcases one a ha ma _ _ (both i0 i1 n01).1 with c | c
      · exact core a ha b hb ma mb disj both hv c
      · have xb:xi i0∈sup n S b:= by
          rcases one b hb mb _ _ (both i0 i1 n01).2 with d | d
          · exact d
          · exact (disj _ c d).elim
        exact core b hb a ha mb ma (fun i x y =>disj i y x) (fun u v huv =>(both u v huv).symm)
          (fun f => by rw [hv,Bool.and_comm]) xb
    · have sa:∀ i,V w (only i)=false→ V a (only i)=false∧V b (only i)=false:= by
        intro i hi
        rw [hv] at hi
        exact Bool.or_eq_false_iff.1 hi
      have same:∀ c∈T,∀ u v:Fin k,V c (two (xi u) (yi v))=true→ V c (only (xi u))=false →
          V c (only (yi v))=false→ xi u∈sup n S c∧yi v∈sup n S c:= by
        intro c hc u v ht h1 h2
        constructor
        · by_contra d
          rw [oner c hc _ _ d,h2] at ht
          exact Bool.noConfusion ht
        · by_contra d
          rw [onel c hc _ _ d,h1] at ht
          exact Bool.noConfusion ht
      have core:∀ a∈T,∀ b∈T,a< w→ (∀ v∈S a,¬ N v)→ (∀ v∈S b,¬ N v) →
          (∀ i,i∈sup n S a→ i∈sup n S b→ False) →
          (∀ f,V w f=(V a f || V b f))→ xi i0∈sup n S a→ False:= by
        intro a ha b hb haw ma mb disj hv h0a
        have sa:∀ i,V w (only i)=false→ V a (only i)=false∧V b (only i)=false:= by
          intro i hi
          rw [hv] at hi
          exact Bool.or_eq_false_iff.1 hi
        have link:∀ u v:Fin k,u ≠ v→ (xi u∈sup n S a ↔ yi v∈sup n S a):= by
          intro u v huv
          have t:= hval u v
          rw [hv] at t
          simp only [huv,ne_eq,not_false_eq_true,decide_true,Bool.or_eq_true] at t
          rcases t with t | t
          · have:= same a ha u v t (sa _ (sing u).1).1 (sa _ (sing v).2).1
            exact ⟨fun _ =>this.2,fun _ =>this.1⟩
          · have:= same b hb u v t (sa _ (sing u).1).2 (sa _ (sing v).2).2
            exact ⟨fun c =>(disj _ c this.1).elim,fun c =>(disj _ c this.2).elim⟩
        have y1:= (link i0 i1 n01).1 h0a
        have x2:= (link i2 i1 n12.symm).2 y1
        have y0:= (link i2 i0 n02.symm).1 x2
        have y2:= (link i0 i2 n02).1 h0a
        have x1:= (link i1 i2 n12).2 y2
        have ally:∀ v:Fin k,yi v∈sup n S a:= by
          intro v
          by_cases c:v=i0
          · exact c ▸ y0
          · exact (link i0 v (Ne.symm c)).1 h0a
        have allx:∀ u:Fin k,xi u∈sup n S a:= by
          intro u
          by_cases c:u=i1
          · exact c ▸ x1
          · exact (link u i1 c).2 y1
        have xnb:∀ u,xi u ∉ sup n S b:= fun u c =>disj _ (allx u) c
        have ynb:∀ u,yi u ∉ sup n S b:= fun u c =>disj _ (ally u) c
        have znb:z ∉ sup n S b:= by
          intro zb
          have t:= hcol i0
          rw [hv,oner b hb _ _ (xnb i0),(sa z hz).2,Bool.or_false,
            onel a ha _ _ (fun c =>disj _ c zb),(sa _ (sing i0).1).1] at t
          exact Bool.noConfusion t
        have bz:∀ p q:ℕ,(p=z∨p ∉ sup n S b)→ (q=z∨q ∉ sup n S b)→ V b (two p q)=false:= by
          intro p q hp hq
          apply off H hb mb
          intro i hi
          have e1:i ≠ p:= by
            intro e
            rcases hp with d | d
            · exact znb (d ▸ e ▸ hi)
            · exact d (e ▸ hi)
          have e2:i ≠ q:= by
            intro e
            rcases hq with d | d
            · exact znb (d ▸ e ▸ hi)
            · exact d (e ▸ hi)
          simp [two,e1,e2]
        apply ih a haw ha ma
        · intro u v
          have t:= hval u v
          rw [hv,bz _ _ (Or.inr (xnb u)) (Or.inr (ynb v)),Bool.or_false] at t
          exact t
        · intro u
          have t:= hcol u
          rw [hv,bz _ _ (Or.inr (xnb u)) (Or.inl rfl),Bool.or_false] at t
          exact t
        · exact (sa z hz).1
      have t:= hval i0 i1
      rw [hv] at t
      simp only [n01,ne_eq,not_false_eq_true,decide_true,Bool.or_eq_true] at t
      rcases t with t | t
      · exact core a ha b hb haw ma mb disj hv
          (same a ha _ _ t (sa _ (sing i0).1).1 (sa _ (sing i1).2).1).1
      · exact core b hb a ha hbw mb ma (fun i x y =>disj i y x) (fun f => by rw [hv,Bool.or_comm])
          (same b hb _ _ t (sa _ (sing i0).1).2 (sa _ (sing i1).2).2).1
section circ
variable (C:Circuit) (n:ℕ)
def val (o:ℕ) (f:ℕ→ Bool):Bool:= value C (inp n f) o
theorem inp_len (f:ℕ→ Bool):(inp n f).length=n:= by simp [inp]
theorem val_input (o:ℕ) (ho:o< n) (f:ℕ→ Bool):val C n o f=f o:= by
  change (run C.gates (inp n f)).getD o false=f o
  rw [prefix_keep _ _ (by rw [inp_len]; exact ho)]
  simp [inp,getDOpt,ho]
theorem val_gate (o:ℕ) (ho:n≤ o) (hj:o - n< C.gates.length) (f:ℕ→ Bool) :
    val C n o f=(gateAt C n o).op.eval
      ((gateAt C n o).inputs.map fun i =>if i< o then val C n i f else false):= by
  have hnw:n+(o - n)=o:= by omega
  have:= value_gate C (inp n f) (o - n) (by exact hj)
  rw [inp_len,hnw] at this
  rw [gateAt_eq C n hj]
  exact this
theorem val_out (o:ℕ) (ho:n+C.gates.length≤ o) (f:ℕ→ Bool):val C n o f=false:= by
  change (run C.gates (inp n f)).getD o false=false
  have:(run C.gates (inp n f)).length≤ o:= by
    rw [run_length,inp_len]
    exact ho
  simp [getDOpt,List.getElem?_eq_none_iff.2 this]
theorem mem_ch {w i:ℕ} (hn:n≤ w) (hj:w - n< C.gates.length) (hi:i∈reads C n w) (hiw:i< w) :
    i∈ch C n w:= by
  unfold ch
  rw [if_pos ⟨hn,hj⟩,List.mem_filter]
  exact ⟨hi,by simpa using hiw⟩
theorem dep0:∀ w,∀ f g:ℕ→ Bool,(∀ i∈desc C n w,i< n→ f i=g i)→ val C n w f=val C n w g:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro f g h
    by_cases h1:w< n
    · rw [val_input C n w h1,val_input C n w h1]
      exact h w (self_desc C n w) h1
    by_cases h2:n+C.gates.length≤ w
    · rw [val_out C n w h2,val_out C n w h2]
    have hn:n≤ w:= by omega
    have hj:w - n< C.gates.length:= by omega
    rw [val_gate C n w hn hj,val_gate C n w hn hj]
    have key:∀ i∈reads C n w,(if i< w then val C n i f else false) =
        (if i< w then val C n i g else false):= by
      intro i hi
      split
      · rename_i hiw
        have hc:= mem_ch C n hn hj hi hiw
        apply ih i hiw
        intro v hv
        exact h v ((mem_desc C n w v).2 (Or.inr ⟨i,hc,hv⟩))
      · rfl
    unfold reads at key
    by_cases hop:(gateAt C n w).op=GateOp.not
    · rw [if_pos hop] at key
      rw [hop]
      cases hin:(gateAt C n w).inputs with
      | nil =>rfl
      | cons a l =>
        rw [hin] at key
        have:= key a (by simp)
        simp only [GateOp.eval,mapC,List.headD_cons,this]
    · rw [if_neg hop] at key
      congr 1
      exact List.map_congr_left key
theorem mono0 (hg:GoodC C):∀ w,(∀ v∈desc C n w,¬ isNot C n v)→ ∀ f g:ℕ→ Bool,
    (∀ i,f i=true→ g i=true)→ val C n w f=true→ val C n w g=true:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hm f g hfg
    by_cases h1:w< n
    · rw [val_input C n w h1,val_input C n w h1]
      exact hfg w
    by_cases h2:n+C.gates.length≤ w
    · rw [val_out C n w h2]
      exact fun h =>(Bool.noConfusion h)
    have hn:n≤ w:= by omega
    have hj:w - n< C.gates.length:= by omega
    rw [val_gate C n w hn hj,val_gate C n w hn hj]
    have hop:(gateAt C n w).op ≠ GateOp.not:= fun c =>hm w (self_desc C n w) ⟨hn,c⟩
    have hg':(gateAt C n w).op=GateOp.and∨(gateAt C n w).op=GateOp.or:= by
      rw [gateAt_eq C n hj] at hop ⊢
      rcases (hg _ (at_mem hj)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hop
    have key:∀ i∈(gateAt C n w).inputs,(if i< w then val C n i f else false)=true →
        (if i< w then val C n i g else false)=true:= by
      intro i hi
      split
      · rename_i hiw
        have hc:i∈ch C n w:= mem_ch C n hn hj (by unfold reads; rw [if_neg hop]; exact hi) hiw
        apply ih i hiw _ f g hfg
        intro v hv
        exact hm v ((mem_desc C n w v).2 (Or.inr ⟨i,hc,hv⟩))
      · exact id
    rcases hg' with h | h <;> rw [h] <;>
      simp only [GateOp.eval,List.all_eq_true,List.any_eq_true,mem_mapL,id]
    · rintro p b ⟨i,hi,rfl⟩
      exact key i hi (p _ ⟨i,hi,rfl⟩)
    · rintro ⟨b,⟨i,hi,rfl⟩,p⟩
      exact ⟨_,⟨i,hi,rfl⟩,key i hi p⟩
theorem gates_le (o:ℕ) (ho:o< n+C.gates.length):(gatesIn C n o).card≤ C.gates.length:= by
  have:gatesIn C n o ⊆ Finset.Ico n (n+C.gates.length):= by
    intro v hv
    have hv':= mem_filt.1 hv
    have:= desc_le C n o v hv'.1
    rw [Finset.mem_Ico]
    exact ⟨hv'.2,by omega⟩
  have:= card_monoF this
  rw [Nat.card_Ico] at this
  omega
end circ
theorem class_id (k:ℕ) (hk:2≤ k) (C:Circuit) (hg:GoodC C)
    (hmon:∀ g∈C.gates,g.op ≠ GateOp.not) (hsize:C.gates.length+1≤ 2 * k)
    (hrep:∀ u v:Fin k,val C (k+k) C.output (two u.val (k+v.val))=decide (u=v)) :
    ∃ M:Finset (Finset (Fin k)),IsM M∧∀ f,
      (val C (k+k) C.output f=true ↔ Pr (fun u =>u.val) (fun u =>k+u.val) Finset.univ M f):= by
  have hnot:∀ v,¬ isNot C (k+k) v:= by
    intro v h
    have h2:= h.2
    unfold gateAt at h2
    by_cases c:v - (k+k)< C.gates.length
    · rw [getDOpt,getOptEq c] at h2
      exact hmon _ (at_mem c) h2
    · rw [getDOpt,List.getElem?_eq_none_iff.2 (by omega)] at h2
      exact GateOp.noConfusion h2
  have ho:C.output< k+k+C.gates.length:= by
    by_contra c
    have:= hrep ⟨0,by omega⟩ ⟨0,by omega⟩
    rw [val_out C _ _ (by omega)] at this
    simp at this
  have other:∀ u:Fin k,∃ w:Fin k,w ≠ u:= by
    intro u
    by_cases c:u.val=0
    · exact ⟨⟨1,by omega⟩,by simp [fin_eq,c]⟩
    · exact ⟨⟨0,by omega⟩,by simp [fin_eq,eq_comm,c]⟩
  have mo:= mono0 C (k+k) hg C.output (fun v _ =>hnot v)
  have fx:∀ u:Fin k,val C (k+k) C.output (only u.val)=false ∧
      val C (k+k) C.output (only (k+u.val))=false:= by
    intro u
    obtain ⟨w,hw⟩:= other u
    constructor
    · by_contra c
      rw [Bool.not_eq_false] at c
      have:= mo (only u.val) (two u.val (k+w.val)) (fun i hi => by
        simp only [only,two,decide_eq_true_eq] at hi ⊢
        exact Or.inl hi) c
      rw [hrep] at this
      simp [Ne.symm hw] at this
    · by_contra c
      rw [Bool.not_eq_false] at c
      have:= mo (only (k+u.val)) (two w.val (k+u.val)) (fun i hi => by
        simp only [only,two,decide_eq_true_eq] at hi ⊢
        exact Or.inr hi) c
      rw [hrep] at this
      simp [hw] at this
  have hleaf:∀ i< k+k,i∈desc C (k+k) C.output:= by
    intro i hi
    by_contra c
    have key:∀ u:Fin k,(i=u.val∨i=k+u.val)→ False:= by
      intro u e
      have h1:= hrep u u
      simp only [decide_true] at h1
      rcases e with e | e
      · have:val C (k+k) C.output (two u.val (k+u.val)) =
            val C (k+k) C.output (only (k+u.val)):= by
          apply dep0
          intro v hv _
          have:v ≠ u.val:= fun d =>c (e ▸ d ▸ hv)
          simp [two,only,this]
        rw [this,(fx u).2] at h1
        exact Bool.noConfusion h1
      · have:val C (k+k) C.output (two u.val (k+u.val))=val C (k+k) C.output (only u.val):= by
          apply dep0
          intro v hv _
          have:v ≠ k+u.val:= fun d =>c (e ▸ d ▸ hv)
          simp [two,only,this]
        rw [this,(fx u).1] at h1
        exact Bool.noConfusion h1
    by_cases d:i< k
    · exact key ⟨i,d⟩ (Or.inl rfl)
    · exact key ⟨i - k,by omega⟩ (Or.inr (show i=k+(i - k) by omega))
  have hL:leaves C (k+k) C.output=Finset.range (k+k):= by
    ext i
    unfold leaves
    rw [mem_filt,Finset.mem_range]
    exact ⟨fun h =>h.2,fun h =>⟨hleaf i h,h⟩⟩
  have hex:(gatesIn C (k+k) C.output).card+1 ≤
      (leaves C (k+k) C.output).card+(nots C (k+k) C.output).card:= by
    have:= gates_le C (k+k) C.output ho
    rw [hL,Finset.card_range]
    omega
  have H:= tree_nodes C (k+k) hg C.output ho hex
  have hs:sup (k+k) (desc C (k+k)) C.output=Finset.range (k+k):= hL
  have hself:= self_desc C (k+k) C.output
  obtain ⟨M,hM,_,hv⟩:= cls_id H (fun u:Fin k =>u.val) (fun u:Fin k =>k+u.val)
    (fun u v h =>Fin.ext h) (fun u v h =>Fin.ext (by omega)) (fun u v h => by have:= u.isLt; omega)
    C.output hself (fun v _ =>hnot v) Finset.univ (by
      intro i
      rw [hs,Finset.mem_range]
      constructor
      · intro hi
        by_cases d:i< k
        · exact ⟨⟨i,d⟩,mem_all _,Or.inl rfl⟩
        · exact ⟨⟨i - k,by omega⟩,mem_all _,Or.inr (show i=k+(i - k) by omega)⟩
      · rintro ⟨u,_,rfl | rfl⟩ <;> have:= u.isLt <;> omega)
    (fun u _ v _ =>hrep u v)
    (by
      intro z
      change val C (k+k) C.output (only z)=false
      by_cases d:z< k
      · exact (fx ⟨z,d⟩).1
      by_cases e:z< k+k
      · have:= (fx ⟨z - k,by omega⟩).2
        have ez:k+(z - k)=z:= by omega
        simpa [ez] using this
      refine off H hself (fun v _ =>hnot v) _ ?_
      intro i hi
      rw [hs,Finset.mem_range] at hi
      have:i ≠ z:= by omega
      simp [only,this])
  exact ⟨M,hM,hv⟩
def Qc (k u v:ℕ):Prop:= u ≠ k+1∧¬ (u< k∧u=v)
theorem rows_distinct (k:ℕ) (hk:2≤ k) (u u':ℕ) (hu:u< k+2) (hu':u'< k+2)
    (h:∀ v< k+1,(Qc k u v ↔ Qc k u' v)):u=u':= by
  unfold Qc at h
  by_contra c
  have hk0:= h k (by omega)
  by_cases a:u< k
  · have h1:= h u (by omega)
    omega
  by_cases b:u'< k
  · have h1:= h u' (by omega)
    omega
  omega
theorem cols_distinct (k:ℕ) (v v':ℕ) (hv:v< k+1) (hv':v'< k+1)
    (h:∀ u< k+2,(Qc k u v ↔ Qc k u v')):v=v':= by
  unfold Qc at h
  by_contra c
  by_cases a:v< k
  · have h1:= h v (by omega)
    omega
  · have h1:= h v' (by omega)
    omega
theorem avoid (k:ℕ) (hk:5≤ k) (a b c d:ℕ):∃ u,u< k∧u ≠ a∧u ≠ b∧u ≠ c∧u ≠ d:= by
  have:¬ Finset.range 5 ⊆ {a,b,c,d}:= by
    intro h
    have h1:= card_monoF h
    have h2:({a,b,c,d}:Finset ℕ).card≤ 4:= Finset.card_le_four
    rw [Finset.card_range] at h1
    omega
  rw [Finset.not_subset] at this
  obtain ⟨u,hu,hn⟩:= this
  rw [Finset.mem_range] at hu
  simp only [mem_ins,mem_oneF,not_or] at hn
  exact ⟨u,by omega,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2⟩
theorem almost_all (m:ℕ) (p:ℕ→ Prop) [DecidablePred p]
    (h:∀ a b,a< m→ b< m→ ¬ p a→ ¬ p b→ a=b):m≤ ((Finset.range m).filter p).card+1:= by
  have h1:((Finset.range m).filter (fun a =>¬ p a)).card≤ 1:= by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [mem_filt,Finset.mem_range] at ha hb
    exact h a b ha.1 hb.1 ha.2 hb.2
  have h2:= Finset.card_filter_add_card_filter_not (s:= Finset.range m) p
  rw [Finset.card_range] at h2
  omega
section single
variable (C:Circuit) (n o ν c:ℕ)
  (H:∀ w∈desc C n o,Node n (desc C n o) (fun w f =>value C (inp n f) w) (desc C n) (isNot C n) w)
  (huni:∀ v∈desc C n o,isNot C n v→ v=ν)
  (hν:isNot C n ν) (hc:c< ν) (hcT:c∈desc C n o)
  (hS:desc C n ν=insert ν (desc C n c))
  (hV:∀ f,val C n ν f=!val C n c f)
include huni hc
theorem below_c:∀ v∈desc C n c,v∈desc C n o→ ¬ isNot C n v:= by
  intro v hv hvo h
  have:= huni v hvo h
  have:= desc_le C n c v hv
  omega
theorem nonu {w:ℕ} (hw:w∈desc C n o) (h:ν ∉ desc C n w):∀ v∈desc C n w,¬ isNot C n v:= by
  intro v hv hn
  have:= huni v (desc_trans C n o w hw hv) hn
  exact h (this ▸ hv)
include H hcT hS
theorem sup_c_sub {a:ℕ} (h:ν∈desc C n a):∀ i∈sup n (desc C n) c,i∈sup n (desc C n) a:= by
  intro i hi
  have hi':= mem_filt.1 hi
  refine mem_filt.2 ⟨desc_trans C n a ν h ?_,hi'.2⟩
  rw [hS]
  exact mem_ins_of hi'.1
theorem step_nu:∀ w∈desc C n o,ν∈desc C n w→ w ≠ ν →
    ∃ a∈desc C n o,∃ b∈desc C n o,a< w∧ν∈desc C n a∧ν ∉ desc C n b ∧
      (∀ i∈sup n (desc C n) b,i ∉ sup n (desc C n) c) ∧
      (∀ i,i∈sup n (desc C n) w ↔ i∈sup n (desc C n) a∨i∈sup n (desc C n) b) ∧
      ((∀ f,val C n w f=(val C n a f && val C n b f))∨∀ f,val C n w f=(val C n a f || val C n b f)):= by
  intro w hw hνw hne
  have hlev:= desc_le C n w ν hνw
  rcases H w hw with ⟨h1,h2,_⟩ | ⟨h0,_,a,ha,b,hb,haw,_,hd,h,hv⟩ | ⟨_,hN,_⟩
  · rw [h2,mem_oneF] at hνw
    exact absurd hνw.symm hne
  · have key:∀ a∈desc C n o,∀ b∈desc C n o,a< w→ Disjoint (desc C n a) (desc C n b) →
        desc C n w=insert w (desc C n a ∪ desc C n b)→ ν∈desc C n a →
        ((∀ f,val C n w f=(val C n a f && val C n b f))∨∀ f,val C n w f=(val C n a f || val C n b f)) →
        ∃ a∈desc C n o,∃ b∈desc C n o,a< w∧ν∈desc C n a∧ν ∉ desc C n b ∧
          (∀ i∈sup n (desc C n) b,i ∉ sup n (desc C n) c) ∧
          (∀ i,i∈sup n (desc C n) w ↔ i∈sup n (desc C n) a∨i∈sup n (desc C n) b) ∧
          ((∀ f,val C n w f=(val C n a f && val C n b f)) ∨
            ∀ f,val C n w f=(val C n a f || val C n b f)):= by
      intro a ha b hb haw hd h hνa hv
      refine ⟨a,ha,b,hb,haw,hνa,disj_leftF.1 hd hνa,?_,sup_bin h h0,hv⟩
      intro i hib hic
      exact sup_disj hd (sup_c_sub C n o ν c H huni hc hcT hS hνa i hic) hib
    rw [h,mem_ins,mem_un] at hνw
    rcases hνw with e | e | e
    · exact absurd e.symm hne
    · exact key a ha b hb haw hd h e hv
    · refine key b hb a ha (by assumption) hd.symm (by rw [h,Finset.union_comm]) e ?_
      rcases hv with hv | hv
      · exact Or.inl fun f =>(hv f).trans (Bool.and_comm _ _)
      · exact Or.inr fun f =>(hv f).trans (Bool.or_comm _ _)
  · have:= huni w hw hN
    exact absurd this hne
include hV
theorem polar:∀ w∈desc C n o,ν∈desc C n w→ ∀ f g:ℕ→ Bool,
    (∀ i,i ∉ sup n (desc C n) c→ f i=true→ g i=true) →
    (∀ i∈sup n (desc C n) c,g i=true→ f i=true) →
    val C n w f=true→ val C n w g=true:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hνw f g h1 h2
    by_cases e:w=ν
    · subst e
      rw [hV,hV]
      have mc:val C n c g=true→ val C n c f=true:= by
        intro hg
        let g':ℕ→ Bool:= fun i =>if i∈sup n (desc C n) c then g i else false
        have e1:val C n c g=val C n c g':= by
          apply dep H c hcT
          intro i hi
          simp only [g',if_pos hi]
        apply mono H c hcT (fun v hv =>below_c C n o _ c huni hc v hv (desc_trans C n o c hcT hv)) g' f _
          (e1.symm.trans hg)
        intro i hi
        simp only [g'] at hi
        split at hi
        · rename_i d
          exact h2 i d hi
        · exact Bool.noConfusion hi
      intro h
      cases hg:val C n c g
      · rfl
      · rw [mc hg] at h
        exact Bool.noConfusion h
    · obtain ⟨a,ha,b,hb,haw,hνa,hνb,hbc,_,hv⟩ :=
        step_nu C n o ν c H huni hc hcT hS w hw hνw e
      have ia:= ih a haw ha hνa f g h1 h2
      have ib:val C n b f=true→ val C n b g=true:= by
        intro hf
        let f':ℕ→ Bool:= fun i =>if i∈sup n (desc C n) b then f i else false
        have e1:val C n b f=val C n b f':= by
          apply dep H b hb
          intro i hi
          simp only [f',if_pos hi]
        apply mono H b hb (nonu C n o ν c huni hc hb hνb) f' g _ (e1.symm.trans hf)
        intro i hi
        simp only [f'] at hi
        split at hi
        · rename_i d
          exact h1 i (hbc i d) hi
        · exact Bool.noConfusion hi
      rcases hv with hv | hv <;> rw [hv,hv]
      · simp only [Bool.and_eq_true]
        exact fun p =>⟨ia p.1,ib p.2⟩
      · simp only [Bool.or_eq_true]
        exact fun p =>p.imp ia ib
theorem bit:∀ w∈desc C n o,ν∈desc C n w→ ∀ f g:ℕ→ Bool,
    (∀ i,i ∉ sup n (desc C n) c→ f i=g i)→ val C n c f=val C n c g →
    val C n w f=val C n w g:= by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hνw f g h1 h2
    by_cases e:w=ν
    · subst e
      rw [hV,hV,h2]
    · obtain ⟨a,ha,b,hb,haw,hνa,_,hbc,_,hv⟩ :=
        step_nu C n o ν c H huni hc hcT hS w hw hνw e
      have ia:= ih a haw ha hνa f g h1 h2
      have ib:val C n b f=val C n b g:= dep H b hb f g (fun i hi =>h1 i (hbc i hi))
      rcases hv with hv | hv <;> rw [hv,hv,ia,ib]
omit hV in
theorem outside (hνo:ν∈desc C n o) (hne:o ≠ ν) :
    ∃ i∈sup n (desc C n) o,i ∉ sup n (desc C n) c:= by
  obtain ⟨a,_,b,hb,_,_,_,hbc,hsup,_⟩ :=
    step_nu C n o ν c H huni hc hcT hS o (self_desc C n o) hνo hne
  obtain ⟨i,hi⟩:= sup_ne H b hb
  exact ⟨i,(hsup i).2 (Or.inr hi),hbc i hi⟩
end single
theorem class_crown (k:ℕ) (hk:7≤ k) (C:Circuit) (hg:GoodC C) (hsize:C.gates.length≤ 2 * k+1)
    (hrep:∀ u< k+2,∀ v< k+1,
      (val C (k+2+(k+1)) C.output (two u (k+2+v))=true ↔ Qc k u v)) :
    ∃ M:Finset (Finset (Fin k)),IsM M∧∀ f,
      (val C (k+2+(k+1)) C.output f=true ↔
        ¬ (f (k+1)=true∨Pr (fun u =>u.val) (fun u =>k+2+u.val) Finset.univ M f)):= by
  classical
  generalize hn:k+2+(k+1)=n at hrep ⊢
  generalize ho':C.output=o at hrep ⊢
  have ho:o< n+C.gates.length:= by
    by_contra c
    have:= (hrep 0 (by omega) 1 (by omega)).2 (by unfold Qc; omega)
    rw [val_out C _ _ (by omega)] at this
    exact Bool.noConfusion this
  have unx:∀ u u',u< k+2→ u'< k+2→ u ∉ desc C n o→ u' ∉ desc C n o→ u=u':= by
    intro u u' hu hu' h1 h2
    apply rows_distinct k (by omega) u u' hu hu'
    intro v hv
    have drop:∀ r,r ∉ desc C n o→ val C n o (two r (k+2+v))=val C n o (only (k+2+v)):= by
      intro r hr
      apply dep0
      intro i hi _
      have:i ≠ r:= fun e =>hr (e ▸ hi)
      simp [two,only,this]
    rw [← hrep u hu v hv,← hrep u' hu' v hv,drop u h1,drop u' h2]
  have uny:∀ v v',v< k+1→ v'< k+1→ k+2+v ∉ desc C n o→ k+2+v' ∉ desc C n o→ v=v':= by
    intro v v' hv hv' h1 h2
    apply cols_distinct k v v' hv hv'
    intro u hu
    have drop:∀ r,r ∉ desc C n o→ val C n o (two u r)=val C n o (only u):= by
      intro r hr
      apply dep0
      intro i hi _
      have:i ≠ r:= fun e =>hr (e ▸ hi)
      simp [two,only,this]
    rw [← hrep u hu v hv,← hrep u hu v' hv',drop _ h1,drop _ h2]
  have xread:= almost_all (k+2) (fun u =>u∈desc C n o) unx
  have yread:= almost_all (k+1) (fun v =>k+2+v∈desc C n o) (fun a b ha hb =>uny a b ha hb)
  have leafge:∀ (X Y:Finset ℕ),(∀ u∈X,u< k+2∧u∈desc C n o) →
      (∀ v∈Y,v< k+1∧k+2+v∈desc C n o)→ X.card+Y.card≤ (leaves C n o).card:= by
    intro X Y hX hY
    have e:(Y.image (fun v =>k+2+v)).card=Y.card :=
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)
    rw [← e,← Finset.card_union_of_disjoint]
    · apply card_monoF
      intro i hi
      unfold leaves
      rw [mem_filt]
      rcases mem_un.1 hi with h | h
      · exact ⟨(hX i h).2,by have:= (hX i h).1; omega⟩
      · obtain ⟨v,hv,rfl⟩:= Finset.mem_image.1 h
        exact ⟨(hY v hv).2,by have:= (hY v hv).1; omega⟩
    · rw [disj_leftF]
      intro i hi hi'
      obtain ⟨v,_,rfl⟩:= Finset.mem_image.1 hi'
      have:= (hX _ hi).1
      omega
  have lge:2 * k+1≤ (leaves C n o).card:= by
    have:= leafge ((Finset.range (k+2)).filter (fun u =>u∈desc C n o))
      ((Finset.range (k+1)).filter (fun v =>k+2+v∈desc C n o))
      (fun u hu => by simpa using hu) (fun v hv => by simpa using hv)
    omega
  have hgl:= gates_le C n o ho
  have hcnt:= count C n hg o
  have hself:= self_desc C n o
  have z1:∀ u,u< k→ (k+1 ≠ u):= fun u hu => by omega
  by_cases hnots:nots C n o=∅
  · exfalso
    have hnn:∀ v∈desc C n o,¬ isNot C n v:= by
      intro v hv h
      have:v∈nots C n o:= mem_filt.2 ⟨hv,h⟩
      rw [hnots] at this
      exact Finset.notMem_empty _ this
    have mo:= mono0 C n hg o hnn
    have xr:∀ u< k+1,u∈desc C n o:= by
      intro u hu
      by_contra hu0
      have h1:∀ u'< k+2,∀ v< k+1,Qc k u v→ Qc k u' v:= by
        intro u' hu' v hv hq
        have h2:= (hrep u (by omega) v hv).2 hq
        have e:val C n o (two u (k+2+v))=val C n o (only (k+2+v)):= by
          apply dep0
          intro i hi _
          have:i ≠ u:= fun e =>hu0 (e ▸ hi)
          simp [two,only,this]
        rw [e] at h2
        apply (hrep u' hu' v hv).1
        exact mo _ _ (fun i hi => by
          simp only [only,two,decide_eq_true_eq] at hi ⊢
          exact Or.inr hi) h2
      by_cases d:u< k
      · obtain ⟨w,hw,hwu,_⟩:= avoid k (by omega) u u u u
        have:= h1 w (by omega) w (by omega) (by unfold Qc; omega)
        unfold Qc at this
        omega
      · have:= h1 0 (by omega) 0 (by omega) (by unfold Qc; omega)
        unfold Qc at this
        omega
    have yr:∀ v< k+1,k+2+v∈desc C n o:= by
      intro v hv
      by_contra hv0
      have h1:∀ v'< k+1,∀ u< k+2,Qc k u v→ Qc k u v':= by
        intro v' hv' u hu hq
        have h2:= (hrep u hu v hv).2 hq
        have e:val C n o (two u (k+2+v))=val C n o (only u):= by
          apply dep0
          intro i hi _
          have:i ≠ k+2+v:= fun e =>hv0 (e ▸ hi)
          simp [two,only,this]
        rw [e] at h2
        apply (hrep u hu v' hv').1
        exact mo _ _ (fun i hi => by
          simp only [only,two,decide_eq_true_eq] at hi ⊢
          exact Or.inl hi) h2
      obtain ⟨w,hw,hwv,_⟩:= avoid k (by omega) v v v v
      have:= h1 w (by omega) w (by omega) (by unfold Qc; omega)
      unfold Qc at this
      omega
    have:= leafge (Finset.range (k+1)) (Finset.range (k+1))
      (fun u hu => by
        rw [Finset.mem_range] at hu
        exact ⟨by omega,xr u hu⟩)
      (fun v hv => by
        rw [Finset.mem_range] at hv
        exact ⟨hv,yr v hv⟩)
    rw [Finset.card_range] at this
    have hex:(gatesIn C n o).card+1≤ (leaves C n o).card+(nots C n o).card:= by omega
    have H:= tree_nodes C n hg o ho hex
    refine no_crown H (k:= k) (by omega) (fun u =>u.val) (fun u =>k+2+u.val)
      (fun u v h =>Fin.ext h) (fun u v h =>Fin.ext (by omega)) (fun u v h => by have:= u.isLt; omega)
      (k+2+k) (fun u => by have:= u.isLt; omega) (fun u => by have:= u.isLt; omega)
      o hself hnn ?_ ?_ ?_
    · intro u v
      change val C n o (two u.val (k+2+v.val))=_
      have hu:= u.isLt
      have hv:= v.isLt
      rw [Bool.eq_iff_iff,hrep _ (by omega) _ (by omega),decide_eq_true_eq]
      unfold Qc
      simp only [ne_eq,fin_eq]
      omega
    · intro u
      change val C n o (two u.val (k+2+k))=true
      have hu:= u.isLt
      rw [hrep _ (by omega) _ (by omega)]
      unfold Qc
      omega
    · change val C n o (only (k+2+k))=false
      by_contra d
      rw [Bool.not_eq_false] at d
      have:= (hrep (k+1) (by omega) k (by omega)).1 (mo _ _ (fun i hi => by
        simp only [only,two,decide_eq_true_eq] at hi ⊢
        exact Or.inr hi) d)
      unfold Qc at this
      omega
  have hpos:0< (nots C n o).card:= Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hnots)
  have hex:(gatesIn C n o).card+1≤ (leaves C n o).card+(nots C n o).card:= by omega
  have hone:(nots C n o).card=1:= by omega
  have H:= tree_nodes C n hg o ho hex
  obtain ⟨ν,hν⟩:= Finset.card_eq_one.1 hone
  have hνm:ν∈nots C n o:= by
    rw [hν]
    exact Finset.mem_singleton_self _
  obtain ⟨hνo,hνn⟩:= mem_filt.1 hνm
  have huni:∀ v∈desc C n o,isNot C n v→ v=ν:= by
    intro v hv h
    have:v∈nots C n o:= mem_filt.2 ⟨hv,h⟩
    rwa [hν,mem_oneF] at this
  have hnode:∃ c∈desc C n o,c< ν∧desc C n ν=insert ν (desc C n c) ∧
      ∀ f,val C n ν f=!val C n c f:= by
    rcases H ν hνo with ⟨h1,_⟩ | ⟨_,h,_⟩ | ⟨_,_,c,hcT,hcν,hS,hV⟩
    · have:= hνn.1
      omega
    · exact absurd hνn h
    · exact ⟨c,hcT,hcν,hS,hV⟩
  obtain ⟨c,hcT,hcν,hS,hV⟩:= hnode
  have csub:∀ i∈sup n (desc C n) c,i∈sup n (desc C n) o :=
    sup_c_sub C n o ν c H huni hcν hcT hS hνo
  have memsup:∀ i,i∈sup n (desc C n) o ↔ i∈desc C n o∧i< n:= fun i =>mem_filt
  have pol:= polar C n o ν c H huni hcν hcT hS hV o hself hνo
  have bt:= bit C n o ν c H huni hcν hcT hS hV o hself hνo
  have hroot:o=ν:= by
    by_contra hne
    obtain ⟨z,hzo,hzc⟩:= outside C n o ν c H huni hcν hcT hS hνo hne
    obtain ⟨i,hi⟩:= sup_ne H c hcT
    have xpos:∀ u v:ℕ,u ∉ sup n (desc C n) c→ val C n o (only (k+2+v))=true →
        val C n o (two u (k+2+v))=true:= by
      intro u v hu h
      refine pol _ _ (fun j _ hj =>?_) (fun j hj h2 =>?_) h
      · simp only [only,two,decide_eq_true_eq] at hj ⊢
        exact Or.inr hj
      · simp only [only,two,decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact absurd (e ▸ hj) hu
        · exact e
    have xneg:∀ u v:ℕ,u∈sup n (desc C n) c→ val C n o (two u (k+2+v))=true →
        val C n o (only (k+2+v))=true:= by
      intro u v hu h
      refine pol _ _ (fun j hj h2 =>?_) (fun j _ h2 =>?_) h
      · simp only [only,two,decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact absurd (e ▸ hu) hj
        · exact e
      · simp only [only,two,decide_eq_true_eq] at h2 ⊢
        exact Or.inr h2
    have ypos:∀ u v:ℕ,k+2+v ∉ sup n (desc C n) c→ val C n o (only u)=true →
        val C n o (two u (k+2+v))=true:= by
      intro u v hv h
      refine pol _ _ (fun j _ hj =>?_) (fun j hj h2 =>?_) h
      · simp only [only,two,decide_eq_true_eq] at hj ⊢
        exact Or.inl hj
      · simp only [only,two,decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact e
        · exact absurd (e ▸ hj) hv
    have yneg:∀ u v:ℕ,k+2+v∈sup n (desc C n) c→ val C n o (two u (k+2+v))=true →
        val C n o (only u)=true:= by
      intro u v hv h
      refine pol _ _ (fun j hj h2 =>?_) (fun j _ h2 =>?_) h
      · simp only [only,two,decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact e
        · exact absurd (e ▸ hv) hj
      · simp only [only,two,decide_eq_true_eq] at h2 ⊢
        exact Or.inl h2
    have r1:∀ u v:ℕ,u< k+2→ v< k+1→ Qc k u v→ val C n o (two u (k+2+v))=true :=
      fun u v hu hv h =>(hrep u hu v hv).2 h
    have r0:∀ u:ℕ,u< k→ val C n o (two u (k+2+u))=false:= by
      intro u hu
      rw [Bool.eq_false_iff]
      intro h
      have:= (hrep u (by omega) u (by omega)).1 h
      unfold Qc at this
      omega
    have rz:∀ v:ℕ,v< k+1→ val C n o (two (k+1) (k+2+v))=false:= by
      intro v hv
      rw [Bool.eq_false_iff]
      intro h
      have:= (hrep (k+1) (by omega) v hv).1 h
      unfold Qc at this
      omega
    have missx:∃ m,∀ u< k+2,u ≠ m→ u∈desc C n o:= by
      by_cases h:∃ m< k+2,m ∉ desc C n o
      · obtain ⟨m,hm,hm'⟩:= h
        refine ⟨m,fun u hu hne =>?_⟩
        by_contra d
        exact hne (unx u m hu hm d hm')
      · refine ⟨0,fun u hu _ =>?_⟩
        by_contra d
        exact h ⟨u,hu,d⟩
    have missy:∃ m,∀ v< k+1,v ≠ m→ k+2+v∈desc C n o:= by
      by_cases h:∃ m< k+1,k+2+m ∉ desc C n o
      · obtain ⟨m,hm,hm'⟩:= h
        refine ⟨m,fun v hv hne =>?_⟩
        by_contra d
        exact hne (uny v m hv hm d hm')
      · refine ⟨0,fun v hv _ =>?_⟩
        by_contra d
        exact h ⟨v,hv,d⟩
    obtain ⟨mx,hmx⟩:= missx
    obtain ⟨my,hmy⟩:= missy
    have xin:∀ u< k,u ≠ mx→ u∈sup n (desc C n) o:= fun u hu h =>
      (memsup u).2 ⟨hmx u (by omega) h,by omega⟩
    have yin:∀ v< k,v ≠ my→ k+2+v∈sup n (desc C n) o:= fun v hv h =>
      (memsup _).2 ⟨hmy v (by omega) h,by omega⟩
    have samex:∀ u w,u< k→ w< k→ u ≠ w→ u ∉ sup n (desc C n) c→ w∈sup n (desc C n) c→ False:= by
      intro u w hu hw huw h1 h2
      have a:= r1 w u (by omega) (by omega) (by unfold Qc; omega)
      have b:= xpos u u h1 (xneg w u h2 a)
      rw [r0 u hu] at b
      exact Bool.noConfusion b
    have samey:∀ v w,v< k→ w< k→ v ≠ w→ k+2+v ∉ sup n (desc C n) c →
        k+2+w∈sup n (desc C n) c→ False:= by
      intro v w hv hw hvw h1 h2
      have a:= r1 v w (by omega) (by omega) (by unfold Qc; omega)
      have b:= ypos v v h1 (yneg v w h2 a)
      rw [r0 v hv] at b
      exact Bool.noConfusion b
    let px:Prop:= ∃ u< k,u ≠ mx∧u∈sup n (desc C n) c
    let py:Prop:= ∃ v< k,v ≠ my∧k+2+v∈sup n (desc C n) c
    have allx:px→ ∀ u< k,u ≠ mx→ u∈sup n (desc C n) c:= by
      rintro ⟨w,hw,_,hwc⟩ u hu _
      by_contra d
      exact samex u w hu hw (fun e =>d (e ▸ hwc)) d hwc
    have ally:py→ ∀ v< k,v ≠ my→ k+2+v∈sup n (desc C n) c:= by
      rintro ⟨w,hw,_,hwc⟩ v hv _
      by_contra d
      exact samey v w hv hw (fun e =>d (e ▸ hwc)) d hwc
    have nox:¬ px→ ∀ u< k,u ∉ sup n (desc C n) c:= by
      intro h u hu d
      have:u ≠ mx:= by
        intro e
        have h1:= (memsup u).1 (csub u d)
        have h2:∃ w< k,w ≠ mx:= by
          obtain ⟨w,hw,hwm,_⟩:= avoid k (by omega) mx mx mx mx
          exact ⟨w,hw,hwm⟩
        obtain ⟨w,hw,hwm⟩:= h2
        have hwc:w ∉ sup n (desc C n) c:= fun e' =>h ⟨w,hw,hwm,e'⟩
        exact samex w u hw hu (by omega) hwc d
      exact h ⟨u,hu,this,d⟩
    have noy:¬ py→ ∀ v< k,k+2+v ∉ sup n (desc C n) c:= by
      intro h v hv d
      have:v ≠ my:= by
        intro e
        obtain ⟨w,hw,hwm,_⟩:= avoid k (by omega) my my my my
        have hwc:k+2+w ∉ sup n (desc C n) c:= fun e' =>h ⟨w,hw,hwm,e'⟩
        exact samey w v hw hv (by omega) hwc d
      exact h ⟨v,hv,this,d⟩
    have zform:∀ j,j∈sup n (desc C n) o→ j< k+2∨∃ v< k+1,j=k+2+v:= by
      intro j hj
      have:= ((memsup j).1 hj).2
      by_cases d:j< k+2
      · exact Or.inl d
      · exact Or.inr ⟨j - (k+2),by omega,by omega⟩
    have cread:∀ j,j∈sup n (desc C n) o→ j∈desc C n o:= fun j hj =>((memsup j).1 hj).1
    by_cases hpx:px <;> by_cases hpy:py
    · have z0:∀ j< k+1,val C n o (only (k+2+j))=true:= by
        intro j hj
        obtain ⟨w,hw,hwm,hwj,_⟩:= avoid k (by omega) mx j j j
        exact xneg w j (allx hpx w hw hwm) (r1 w j (by omega) hj (by unfold Qc; omega))
      have c0:∀ i< k+2,i ≠ k+1→ val C n o (only i)=true:= by
        intro i hi hik
        obtain ⟨w,hw,hwm,hwi,_⟩:= avoid k (by omega) my i i i
        exact yneg i w (ally hpy w hw hwm) (r1 i w hi (by omega) (by unfold Qc; omega))
      rcases zform z hzo with hz | ⟨t,ht,rfl⟩
      · by_cases d:z< k
        · by_cases e:z=mx
          · obtain ⟨w,hw,hwm,_⟩:= avoid k (by omega) mx mx mx mx
            exact samex z w d hw (by omega) hzc (allx hpx w hw hwm)
          · exact hzc (allx hpx z d e)
        by_cases e:z=k
        · subst e
          have row:mx=z:= by
            have hmxlt:mx< z+2:= by
              by_contra g
              have h1:∀ u< z+2,u∈desc C n o:= fun u hu =>hmx u hu (by omega)
              have:= leafge (Finset.range (z+2))
                ((Finset.range (z+1)).filter (fun v =>z+2+v∈desc C n o))
                (fun u hu => by
                  rw [Finset.mem_range] at hu
                  exact ⟨hu,h1 u hu⟩)
                (fun v hv => by simpa using hv)
              rw [Finset.card_range] at this
              omega
            by_cases g:mx∈desc C n o
            · have h1:∀ u< z+2,u∈desc C n o:= fun u hu => by
                by_cases e:u=mx
                · exact e ▸ g
                · exact hmx u hu e
              have:= leafge (Finset.range (z+2))
                ((Finset.range (z+1)).filter (fun v =>z+2+v∈desc C n o))
                (fun u hu => by
                  rw [Finset.mem_range] at hu
                  exact ⟨hu,h1 u hu⟩)
                (fun v hv => by simpa using hv)
              rw [Finset.card_range] at this
              omega
            apply rows_distinct z (by omega) mx z hmxlt (by omega)
            intro v hv
            have e1:val C n o (two mx (z+2+v))=val C n o (only (z+2+v)):= by
              apply dep0
              intro i hi _
              have:i ≠ mx:= fun e =>g (e ▸ hi)
              simp [two,only,this]
            rw [← hrep mx hmxlt v hv,← hrep z (by omega) v hv,e1,z0 v hv,
              r1 z v (by omega) hv (by unfold Qc; omega)]
          obtain ⟨g1,_⟩:= (memsup z).1 hzo
          have:∀ u< z+2,u∈desc C n o:= fun u hu => by
            by_cases e:u=z
            · exact e ▸ g1
            · exact hmx u hu (by omega)
          have:= leafge (Finset.range (z+2))
            ((Finset.range (z+1)).filter (fun v =>z+2+v∈desc C n o))
            (fun u hu => by
              rw [Finset.mem_range] at hu
              exact ⟨hu,this u hu⟩)
            (fun v hv => by simpa using hv)
          rw [Finset.card_range] at this
          omega
        have ez:z=k+1:= by omega
        have a:= xpos z 0 hzc (z0 0 (by omega))
        rw [ez,rz 0 (by omega)] at a
        exact Bool.noConfusion a
      · by_cases d:t< k
        · by_cases e:t=my
          · obtain ⟨w,hw,hwm,_⟩:= avoid k (by omega) my my my my
            exact samey t w d hw (by omega) hzc (ally hpy w hw hwm)
          · exact hzc (ally hpy t d e)
        have et:t=k:= by omega
        subst et
        have col:∀ i< t+2,(val C n o (only i)=true ↔ Qc t i t):= by
          intro i hi
          by_cases e:i=t+1
          · have hf:val C n o (only i)=false:= by
              rw [Bool.eq_false_iff]
              intro h
              have a:= ypos i t hzc h
              rw [e,rz t (by omega)] at a
              exact Bool.noConfusion a
            rw [hf]
            unfold Qc
            simp [e]
          · rw [c0 i hi e]
            unfold Qc
            exact ⟨fun _ => by omega,fun _ =>rfl⟩
        have g1:= cread _ hzo
        have miss:∃ v< t+1,t+2+v ∉ desc C n o:= by
          by_contra g
          have h1:∀ v< t+1,t+2+v∈desc C n o:= fun v hv => by
            by_contra d'
            exact g ⟨v,hv,d'⟩
          have:= leafge ((Finset.range (t+2)).filter (fun u =>u∈desc C n o)) (Finset.range (t+1))
            (fun u hu => by simpa using hu)
            (fun v hv => by
              rw [Finset.mem_range] at hv
              exact ⟨hv,h1 v hv⟩)
          rw [Finset.card_range] at this
          omega
        obtain ⟨m,hm,hm'⟩:= miss
        have:m=t:= by
          apply cols_distinct t m t hm (by omega)
          intro u hu
          have e1:val C n o (two u (t+2+m))=val C n o (only u):= by
            apply dep0
            intro i hi _
            have:i ≠ t+2+m:= fun e =>hm' (e ▸ hi)
            simp [two,only,this]
          rw [← hrep u hu m hm,e1,col u hu]
        exact hm' (this ▸ g1)
    · obtain ⟨a,ha,ham,_⟩:= avoid k (by omega) mx mx mx mx
      obtain ⟨b,hb,hbm,hba,_⟩:= avoid k (by omega) mx a a a
      obtain ⟨d,hd,hdm,hda,hdb,_⟩:= avoid k (by omega) mx a b b
      have ync:∀ j< k,k+2+j ∉ sup n (desc C n) c:= noy hpy
      have eqc:∀ u j,j< k→ val C n c (two u (k+2+j))=val C n c (only u):= by
        intro u j hj
        apply dep H c hcT
        intro i hi
        have:i ≠ k+2+j:= fun e =>ync j hj (e ▸ hi)
        simp [two,only,this]
      have pig:∀ u w,u< k→ w< k→ u ≠ w→ u ≠ mx→ w ≠ mx →
          val C n c (only u)=val C n c (only w)→ False:= by
        intro u w hu hw huw hum hwm h
        have uc:= allx hpx u hu hum
        have wc:= allx hpx w hw hwm
        have key:val C n o (two u (k+2+u))=val C n o (two w (k+2+u)):= by
          apply bt
          · intro i hi
            have e1:i ≠ u:= fun e =>hi (e ▸ uc)
            have e2:i ≠ w:= fun e =>hi (e ▸ wc)
            simp [two,e1,e2]
          · rw [eqc u u hu,eqc w u hu,h]
        rw [r0 u hu,r1 w u (by omega) (by omega) (by unfold Qc; omega)] at key
        exact Bool.noConfusion key
      have three:∀ p q r:Bool,p=q∨p=r∨q=r:= by decide +kernel
      rcases three (val C n c (only a)) (val C n c (only b)) (val C n c (only d)) with h | h | h
      · exact pig a b ha hb hba.symm ham hbm h
      · exact pig a d ha hd hda.symm ham hdm h
      · exact pig b d hb hd hdb.symm hbm hdm h
    · obtain ⟨a,ha,ham,_⟩:= avoid k (by omega) my my my my
      obtain ⟨b,hb,hbm,hba,_⟩:= avoid k (by omega) my a a a
      obtain ⟨d,hd,hdm,hda,hdb,_⟩:= avoid k (by omega) my a b b
      have xnc:∀ j< k,j ∉ sup n (desc C n) c:= nox hpx
      have eqc:∀ v j,j< k→ val C n c (two j (k+2+v))=val C n c (only (k+2+v)):= by
        intro v j hj
        apply dep H c hcT
        intro i hi
        have:i ≠ j:= fun e =>xnc j hj (e ▸ hi)
        simp [two,only,this]
      have pig:∀ u w,u< k→ w< k→ u ≠ w→ u ≠ my→ w ≠ my →
          val C n c (only (k+2+u))=val C n c (only (k+2+w))→ False:= by
        intro u w hu hw huw hum hwm h
        have uc:= ally hpy u hu hum
        have wc:= ally hpy w hw hwm
        have key:val C n o (two u (k+2+u))=val C n o (two u (k+2+w)):= by
          apply bt
          · intro i hi
            have e1:i ≠ k+2+u:= fun e =>hi (e ▸ uc)
            have e2:i ≠ k+2+w:= fun e =>hi (e ▸ wc)
            simp [two,e1,e2]
          · rw [eqc u u hu,eqc w u hu,h]
        rw [r0 u hu,r1 u w (by omega) (by omega) (by unfold Qc; omega)] at key
        exact Bool.noConfusion key
      have three:∀ p q r:Bool,p=q∨p=r∨q=r:= by decide +kernel
      rcases three (val C n c (only (k+2+a))) (val C n c (only (k+2+b)))
          (val C n c (only (k+2+d))) with h | h | h
      · exact pig a b ha hb hba.symm ham hbm h
      · exact pig a d ha hd hda.symm ham hdm h
      · exact pig b d hb hd hdb.symm hbm hdm h
    · have xnc:∀ j< k,j ∉ sup n (desc C n) c:= nox hpx
      have ync:∀ j< k,k+2+j ∉ sup n (desc C n) c:= noy hpy
      have nk:k ∉ sup n (desc C n) c:= by
        intro h
        obtain ⟨j,hj,hjm,_⟩:= avoid k (by omega) mx mx mx mx
        have a:= xneg k j h (r1 k j (by omega) (by omega) (by unfold Qc; omega))
        have b:= xpos j j (xnc j hj) a
        rw [r0 j hj] at b
        exact Bool.noConfusion b
      have nyk:k+2+k ∉ sup n (desc C n) c:= by
        intro h
        obtain ⟨j,hj,hjm,_⟩:= avoid k (by omega) my my my my
        have a:= yneg j k h (r1 j k (by omega) (by omega) (by unfold Qc; omega))
        have b:= ypos j j (ync j hj) a
        rw [r0 j hj] at b
        exact Bool.noConfusion b
      have hik:i=k+1:= by
        rcases zform i (csub i hi) with h | ⟨t,ht,rfl⟩
        · by_cases d:i< k
          · exact absurd hi (xnc i d)
          by_cases e:i=k
          · exact absurd (e ▸ hi) nk
          omega
        · by_cases d:t< k
          · exact absurd hi (ync t d)
          have:t=k:= by omega
          exact absurd (this ▸ hi) nyk
      have g1:= cread _ (csub i hi)
      rw [hik] at g1
      have z0:∀ j< k,j ≠ mx→ val C n o (only (k+2+j))=false:= by
        intro j hj hjm
        rw [Bool.eq_false_iff]
        intro h
        have a:= xpos j j (xnc j hj) h
        rw [r0 j hj] at a
        exact Bool.noConfusion a
      have miss:∃ m< k+2,m ∉ desc C n o:= by
        by_contra g
        have h1:∀ u< k+2,u∈desc C n o:= fun u hu => by
          by_contra d'
          exact g ⟨u,hu,d'⟩
        have:= leafge (Finset.range (k+2))
          ((Finset.range (k+1)).filter (fun v =>k+2+v∈desc C n o))
          (fun u hu => by
            rw [Finset.mem_range] at hu
            exact ⟨hu,h1 u hu⟩)
          (fun v hv => by simpa using hv)
        rw [Finset.card_range] at this
        omega
      obtain ⟨m,hm,hm'⟩:= miss
      have mrow:∀ v< k+1,(val C n o (only (k+2+v))=true ↔ Qc k m v):= by
        intro v hv
        have e1:val C n o (two m (k+2+v))=val C n o (only (k+2+v)):= by
          apply dep0
          intro i hi _
          have:i ≠ m:= fun e =>hm' (e ▸ hi)
          simp [two,only,this]
        rw [← e1,hrep m hm v hv]
      have mne:m ≠ k+1:= fun e =>hm' (e ▸ g1)
      by_cases d:m< k
      · obtain ⟨j,hj,hjm,hjm',_⟩:= avoid k (by omega) mx m m m
        have a:= (mrow j (by omega)).2 (by unfold Qc; omega)
        rw [z0 j hj hjm] at a
        exact Bool.noConfusion a
      · obtain ⟨j,hj,hjm,_⟩:= avoid k (by omega) mx mx mx mx
        have a:= (mrow j (by omega)).2 (by unfold Qc; omega)
        rw [z0 j hj hjm] at a
        exact Bool.noConfusion a
  subst hroot
  have hFG:∀ f,val C n o f=!val C n c f:= hV
  have cmon:∀ v∈desc C n c,¬ isNot C n v:= fun v hv =>
    below_c C n o o c huni hcν v hv (desc_trans C n o c hcT hv)
  have supc:sup n (desc C n) c=sup n (desc C n) o:= (sup_un hS hνn.1).symm
  have mc:= mono H c hcT cmon
  have G:∀ u< k+2,∀ v< k+1,(val C n c (two u (k+2+v))=true ↔ ¬ Qc k u v):= by
    intro u hu v hv
    rw [← hrep u hu v hv,hFG]
    cases val C n c (two u (k+2+v)) <;> simp
  have notin:∀ i,i< n→ i ∉ desc C n o→ i ∉ sup n (desc C n) c:= by
    intro i _ h d
    rw [supc] at d
    exact h ((memsup i).1 d).1
  have gdrop:∀ r s,r ∉ sup n (desc C n) c→ val C n c (two r s)=val C n c (only s):= by
    intro r s hr
    apply dep H c hcT
    intro i hi
    have:i ≠ r:= fun e =>hr (e ▸ hi)
    simp [two,only,this]
  have gdrop':∀ r s,s ∉ sup n (desc C n) c→ val C n c (two r s)=val C n c (only r):= by
    intro r s hs
    apply dep H c hcT
    intro i hi
    have:i ≠ s:= fun e =>hs (e ▸ hi)
    simp [two,only,this]
  have up1:∀ a b,val C n c (only a)=true→ val C n c (two a b)=true:= fun a b h =>
    mc _ _ (fun i hi => by
      simp only [only,two,decide_eq_true_eq] at hi ⊢
      exact Or.inl hi) h
  have up2:∀ a b,val C n c (only b)=true→ val C n c (two a b)=true:= fun a b h =>
    mc _ _ (fun i hi => by
      simp only [only,two,decide_eq_true_eq] at hi ⊢
      exact Or.inr hi) h
  have xk:∃ m< k+2,m ∉ desc C n o:= by
    by_contra g
    have h1:∀ u< k+2,u∈desc C n o:= fun u hu => by
      by_contra d'
      exact g ⟨u,hu,d'⟩
    have:= leafge (Finset.range (k+2))
      ((Finset.range (k+1)).filter (fun v =>k+2+v∈desc C n o))
      (fun u hu => by
        rw [Finset.mem_range] at hu
        exact ⟨hu,h1 u hu⟩)
      (fun v hv => by simpa using hv)
    rw [Finset.card_range] at this
    omega
  have yk:∃ m< k+1,k+2+m ∉ desc C n o:= by
    by_contra g
    have h1:∀ v< k+1,k+2+v∈desc C n o:= fun v hv => by
      by_contra d'
      exact g ⟨v,hv,d'⟩
    have:= leafge ((Finset.range (k+2)).filter (fun u =>u∈desc C n o)) (Finset.range (k+1))
      (fun u hu => by simpa using hu)
      (fun v hv => by
        rw [Finset.mem_range] at hv
        exact ⟨hv,h1 v hv⟩)
    rw [Finset.card_range] at this
    omega
  obtain ⟨mx,hmx,hmx'⟩:= xk
  obtain ⟨my,hmy,hmy'⟩:= yk
  have emx:mx=k:= by
    have hz:∀ v< k+1,¬ Qc k mx v→ ¬ Qc k k v:= by
      intro v hv h
      have a:= (G mx hmx v hv).2 h
      rw [gdrop _ _ (notin mx (by omega) hmx')] at a
      exact (G k (by omega) v hv).1 (up2 k _ a)
    have allq:∀ v< k+1,Qc k mx v:= by
      intro v hv
      by_contra d
      apply hz v hv d
      unfold Qc
      omega
    by_contra d
    by_cases e:mx< k
    · have:= allq mx (by omega)
      unfold Qc at this
      omega
    · have:= allq 0 (by omega)
      unfold Qc at this
      omega
  have emy:my=k:= by
    by_contra d
    have hmyk:my< k:= by omega
    have a:= (G my (by omega) my hmy).2 (by unfold Qc; omega)
    rw [gdrop' _ _ (notin _ (by omega) hmy')] at a
    obtain ⟨w,hw,hwm,_⟩:= avoid k (by omega) my my my my
    have b:= (G my (by omega) w (by omega)).1 (up1 my _ a)
    apply b
    unfold Qc
    omega
  subst mx
  subst my
  have xin:∀ u< k+2,u ≠ k→ u∈desc C n o:= fun u hu h => by
    by_contra d
    exact h (unx u k hu (by omega) d hmx')
  have yin:∀ v< k,k+2+v∈desc C n o:= fun v hv => by
    by_contra d
    have:= uny v k (by omega) (by omega) d hmy'
    omega
  have hsupc:∀ i,i∈sup n (desc C n) c ↔
      i=k+1∨∃ u∈(Finset.univ:Finset (Fin k)),i=u.val∨i=k+2+u.val:= by
    intro i
    rw [supc,memsup]
    constructor
    · rintro ⟨h1,h2⟩
      by_cases d:i< k
      · exact Or.inr ⟨⟨i,d⟩,mem_all _,Or.inl rfl⟩
      by_cases e:i=k
      · exact absurd (e ▸ h1) hmx'
      by_cases f:i=k+1
      · exact Or.inl f
      by_cases g:i=k+2+k
      · exact absurd (g ▸ h1) hmy'
      exact Or.inr ⟨⟨i - (k+2),by omega⟩,mem_all _,
        Or.inr (show i=k+2+(i - (k+2)) by omega)⟩
    · rintro (rfl | ⟨u,_,rfl | rfl⟩)
      · exact ⟨xin _ (by omega) (by omega),by omega⟩
      · have:= u.isLt
        exact ⟨xin _ (by omega) (by omega),by omega⟩
      · have:= u.isLt
        exact ⟨yin _ this,by omega⟩
  have notk:k+2+k ∉ sup n (desc C n) c:= notin _ (by omega) hmy'
  have zk:val C n c (only (k+1))=true:= by
    have a:= (G (k+1) (by omega) k (by omega)).2 (by unfold Qc; omega)
    rwa [gdrop' _ _ notk] at a
  have core0:∀ i,i ≠ k+1→ val C n c (only i)=false:= by
    intro i hi
    by_cases d:i∈sup n (desc C n) c
    swap
    · apply off H hcT cmon
      intro j hj
      have:j ≠ i:= fun e =>d (e ▸ hj)
      simp [only,this]
    rcases (hsupc i).1 d with e | ⟨u,_,e | e⟩
    · exact absurd e hi
    · have hu:= u.isLt
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨w,hw,hwu,_⟩:= avoid k (by omega) u.val u.val u.val u.val
      have:= (G u.val (by omega) w (by omega)).1 (up1 _ _ (e ▸ h))
      apply this
      unfold Qc
      omega
    · have hu:= u.isLt
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨w,hw,hwu,_⟩:= avoid k (by omega) u.val u.val u.val u.val
      have:= (G w (by omega) u.val (by omega)).1 (up2 _ _ (e ▸ h))
      apply this
      unfold Qc
      omega
  obtain ⟨M,hM,_,hv⟩:= cls_z H (fun u:Fin k =>u.val) (fun u:Fin k =>k+2+u.val)
    (fun u v h =>Fin.ext h) (fun u v h =>Fin.ext (by omega)) (fun u v h => by have:= u.isLt; omega)
    (k+1) (fun u => by have:= u.isLt; omega) (fun u => by have:= u.isLt; omega)
    c hcT cmon Finset.univ hsupc (by
      intro u _ v _
      change val C n c (two u.val (k+2+v.val))=_
      have hu:= u.isLt
      have hv:= v.isLt
      rw [Bool.eq_iff_iff,G _ (by omega) _ (by omega),decide_eq_true_eq,fin_eq]
      unfold Qc
      omega) core0 zk
  refine ⟨M,hM,fun f =>?_⟩
  rw [hFG,← hv]
  change (!val C n c f)=true ↔ ¬ val C n c f=true
  cases val C n c f <;> simp
section build
variable (nr:ℕ) {k:ℕ}
def term (b:Fin k × Fin k) (f:ℕ→ Bool):Bool :=
  if b.1=b.2 then f b.1.val && f (nr+b.1.val)
  else (f b.1.val || f (nr+b.2.val)) && (f b.2.val || f (nr+b.1.val))
def blk (m:ℕ) (b:Fin k × Fin k):List Gate × ℕ :=
  if b.1=b.2 then ([⟨GateOp.and,[b.1.val,nr+b.1.val]⟩],m)
  else ([⟨GateOp.or,[b.1.val,nr+b.2.val]⟩,⟨GateOp.or,[b.2.val,nr+b.1.val]⟩,
    ⟨GateOp.and,[m,m+1]⟩],m+2)
def bcost (b:Fin k × Fin k):ℕ:= if b.1=b.2 then 2 else 4
def build (n:ℕ):List (Fin k × Fin k)→ List Gate × ℕ
  | [] =>([],0)
  | [b] =>blk nr n b
  | b :: b' :: l =>
    let r:= build n (b' :: l)
    let s:= blk nr (n+r.1.length) b
    (r.1 ++ s.1 ++ [⟨GateOp.or,[r.2,s.2]⟩],n+r.1.length+s.1.length)
def Mon (gs:List Gate):Prop:= ∀ g∈gs,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤ 2
theorem run_one (g:Gate) (w:BitTape):run [g] w=step w g:= rfl
theorem blk_ok (n:ℕ) (hn:∀ u:Fin k,u.val< n∧nr+u.val< n) (f:ℕ→ Bool) (w:BitTape)
    (hlen:n≤ w.length) (hf:∀ i< n,w.getD i false=f i) (b:Fin k × Fin k) :
    (run (blk nr w.length b).1 w).getD (blk nr w.length b).2 false=term nr b f ∧
    (blk nr w.length b).2< w.length+(blk nr w.length b).1.length ∧
    (blk nr w.length b).1.length+1=bcost b∧Mon (blk nr w.length b).1:= by
  have a1:= hn b.1
  have a2:= hn b.2
  have keep:∀ (t:BitTape) (i:ℕ),i< n→ (w ++ t).getD i false=f i:= by
    intro t i hi
    rw [getD_keep _ _ (by omega)]
    exact hf i hi
  by_cases h:b.1=b.2
  · simp only [blk,term,bcost,if_pos h]
    refine ⟨?_,by simp,by simp,?_⟩
    · rw [run_one]
      simp only [step]
      rw [getD_new _ _ rfl]
      simp [GateOp.eval,← getDOpt,hf _ a1.1,hf _ a1.2]
    · intro g hg
      rw [mem_one] at hg
      subst hg
      simp
  · simp only [blk,term,bcost,if_neg h]
    refine ⟨?_,by simp,by simp,?_⟩
    · have s1:step w ⟨GateOp.or,[b.1.val,nr+b.2.val]⟩=w ++ [f b.1.val || f (nr+b.2.val)]:= by
        simp only [step,mapC,mapN,hf _ a1.1,hf _ a2.2]
        simp [GateOp.eval]
      have s2:∀ x:Bool,step (w ++ [x]) ⟨GateOp.or,[b.2.val,nr+b.1.val]⟩ =
          w ++ [x] ++ [f b.2.val || f (nr+b.1.val)]:= by
        intro x
        simp only [step,mapC,mapN,keep _ _ a2.1,keep _ _ a1.2]
        simp [GateOp.eval]
      have s3:∀ x y:Bool,step (w ++ [x] ++ [y]) ⟨GateOp.and,[w.length,w.length+1]⟩ =
          w ++ [x] ++ [y] ++ [x && y]:= by
        intro x y
        have e1:(w ++ [x] ++ [y]).getD w.length false=x:= by
          rw [getD_keep _ _ (by simp),getD_new _ _ rfl]
        have e2:(w ++ [x] ++ [y]).getD (w.length+1) false=y:= getD_new _ _ (by simp)
        simp only [step,mapC,mapN,e1,e2]
        simp [GateOp.eval]
      rw [run_cons,s1,run_cons,s2,run_cons,s3,run_nil]
      exact getD_new _ _ (by simp)
    · intro g hg
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp
theorem build_ok (n:ℕ) (hn:∀ u:Fin k,u.val< n∧nr+u.val< n) (f:ℕ→ Bool) (w:BitTape)
    (hlen:w.length=n) (hf:∀ i< n,w.getD i false=f i) :
    ∀ l:List (Fin k × Fin k),l ≠ [] →
      (run (build nr n l).1 w).getD (build nr n l).2 false=l.any (fun b =>term nr b f) ∧
      (build nr n l).2< n+(build nr n l).1.length ∧
      (build nr n l).1.length+1=(l.map bcost).sum∧Mon (build nr n l).1:= by
  intro l
  induction l with
  | nil =>exact fun h =>absurd rfl h
  | cons b l ih =>
    intro _
    cases l with
    | nil =>
      have:= blk_ok nr n hn f w (by omega) hf b
      rw [hlen] at this
      simpa [build] using this
    | cons b' l =>
      obtain ⟨h1,h2,h3,h4⟩:= ih (by simp)
      simp only [build]
      generalize hr:build nr n (b' :: l)=r at h1 h2 h3 h4
      let w1:= run r.1 w
      have l1:w1.length=n+r.1.length:= by
        simp only [w1,run_length,hlen]
      have hf1:∀ i< n,w1.getD i false=f i:= by
        intro i hi
        simp only [w1]
        rw [prefix_keep _ _ (by omega)]
        exact hf i hi
      obtain ⟨k1,k2,k3,k4⟩:= blk_ok nr n hn f w1 (by omega) hf1 b
      rw [l1] at k1 k2 k3 k4
      generalize hs:blk nr (n+r.1.length) b=s at k1 k2 k3 k4
      let w2:= run s.1 w1
      have l2:w2.length=n+r.1.length+s.1.length:= by
        simp only [w2,run_length,l1]
      have keep:w2.getD r.2 false=w1.getD r.2 false:= by
        simp only [w2]
        exact prefix_keep _ _ (by omega)
      refine ⟨?_,?_,?_,?_⟩
      · rw [run_append,run_append,run_one]
        change (step w2 ⟨GateOp.or,[r.2,s.2]⟩).getD (n+r.1.length+s.1.length) false=_
        simp only [step]
        rw [getD_new _ _ l2.symm]
        simp only [mapC,mapN]
        rw [keep]
        change GateOp.or.eval [w1.getD r.2 false,(run s.1 w1).getD s.2 false]=_
        rw [show w1.getD r.2 false=_ from h1,k1,List.any_cons (a:= b)]
        simp [GateOp.eval,Bool.or_comm]
      · simp only [len_app,len_one]
        omega
      · rw [mapC,List.sum_cons]
        simp only [len_app,len_one]
        omega
      · intro g hg
        simp only [mem_app,mem_one] at hg
        rcases hg with (hg | hg) | hg
        · exact h4 g hg
        · exact k4 g hg
        · subst hg
          simp
theorem blocks (nr:ℕ) (M:Finset (Finset (Fin k))) (hM:IsM M) :
    ∃ l:List (Fin k × Fin k),(l.map bcost).sum=2 * k ∧
      ∀ f,(l.any (fun b =>term nr b f)=true ↔
        Pr (fun u =>u.val) (fun u =>nr+u.val) Finset.univ M f):= by
  have pairs:∀ M:Finset (Finset (Fin k)),IsM M→ ∃ l:List (Fin k × Fin k),
      (l.map bcost).sum=2 * (M.biUnion id).card ∧
      ∀ f,(l.any (fun b =>term nr b f)=true ↔
        Pr (fun u =>u.val) (fun u =>nr+u.val) (M.biUnion id) M f):= by
    intro M
    induction M using Finset.induction_on with
    | empty =>exact fun _ =>⟨[],by simp,fun f => by simp [Pr]⟩
    | @insert e M he ih =>
      intro hM
      obtain ⟨l,h1,h2⟩:= ih (hM.mono (Finset.subset_insert _ _))
      obtain ⟨a,b,hab,rfl⟩:= Finset.card_eq_two.1 (hM.1 e (Finset.mem_insert_self _ _))
      have hdj:Disjoint ({a,b}:Finset (Fin k)) (M.biUnion id):= by
        rw [Finset.disjoint_biUnion_right]
        intro g hg
        exact hM.2 _ (Finset.mem_insert_self _ _) g (mem_ins_of hg) (fun c =>he (c ▸ hg))
      refine ⟨(a,b) :: l,?_,fun f =>?_⟩
      · rw [mapC,List.sum_cons,h1,Finset.biUnion_insert,id,
          Finset.card_union_of_disjoint hdj,Finset.card_pair hab]
        simp only [bcost,if_neg hab]
        omega
      · rw [List.any_cons,Bool.or_eq_true,h2,Finset.biUnion_insert,id]
        have e1:insert ({a,b}:Finset (Fin k)) M={{a,b}} ∪ M:= Finset.insert_eq _ _
        rw [e1,Pr_union]
        apply or_congr _ Iff.rfl
        simp only [term,if_neg hab,Pr,mem_ins,mem_oneF,or_and_right,
          exists_or,exists_eq_left,forall_eq_or_imp,forall_eq,Bool.and_eq_true,Bool.or_eq_true]
        tauto
  obtain ⟨l,h1,h2⟩:= pairs M hM
  let R:= Finset.univ \ M.biUnion id
  refine ⟨l ++ R.toList.map (fun u =>(u,u)),?_,fun f =>?_⟩
  · have:(R.toList.map (fun u =>(u,u))).map bcost=List.replicate R.card 2:= by
      rw [mapMap,← Finset.length_toList,← List.map_const']
      apply List.map_congr_left
      intro u _
      simp [bcost]
    rw [List.map_append,List.sum_append,h1,this,List.sum_replicate,smul_eq_mul]
    have h3:= Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (M.biUnion id))
    rw [Finset.card_univ,Fintype.card_fin] at h3
    simp only [R]
    omega
  · rw [List.any_append,Bool.or_eq_true,h2]
    have hu:M.biUnion id ∪ R=Finset.univ:= by
      simp [R]
    have e:Pr (fun u =>u.val) (fun u =>nr+u.val) Finset.univ M f ↔
        Pr (fun u =>u.val) (fun u =>nr+u.val) (M.biUnion id) M f ∨
        Pr (fun u =>u.val) (fun u =>nr+u.val) R ∅ f:= by
      rw [← Pr_union,hu,Finset.union_empty]
    rw [e]
    apply or_congr Iff.rfl
    simp [Pr,term,List.any_map,List.any_eq_true]
end build
theorem list_inp (l:BitTape) (n:ℕ) (h:l.length=n):l=inp n (fun i =>l.getD i false):= by
  apply List.ext_getElem
  · simp [inp,h]
  · intro i h1 h2
    simp [inp,getDOpt,getOptEq h1]
theorem getD_app_left {a b:ℕ} (x:Fin a→ Bool) (y:Fin b→ Bool) (i:ℕ) (hi:i< a) :
    (List.ofFn x ++ List.ofFn y).getD i false=x ⟨i,hi⟩:= by
  rw [getD_keep _ _ (by simpa using hi)]
  simp [getDOpt,hi]
theorem getD_app_right {a b:ℕ} (x:Fin a→ Bool) (y:Fin b→ Bool) (i:ℕ) (hi:i< b) :
    (List.ofFn x ++ List.ofFn y).getD (a+i) false=y ⟨i,hi⟩:= by
  rw [getDOpt,List.getElem?_append_right (by simp)]
  simp [hi]
theorem oneEach_inp {a b:ℕ} (u:Fin a) (v:Fin b) :
    PEqualNP.Represents.oneEach u v=inp (a+b) (two u.val (a+v.val)):= by
  apply List.ext_getElem
  · simp [PEqualNP.Represents.oneEach,inp]
  · intro i h1 h2
    have hi:i< a+b:= by simpa [inp] using h2
    have key:(PEqualNP.Represents.oneEach u v).getD i false=two u.val (a+v.val) i:= by
      unfold PEqualNP.Represents.oneEach two
      have hu:= u.isLt
      have hv:= v.isLt
      by_cases d:i< a
      · rw [getD_app_left _ _ i d]
        rw [decide_eq_decide,fin_eq]
        simp only
        omega
      · have e:i=a+(i - a):= by omega
        conv_lhs =>rw [e]
        rw [getD_app_right _ _ (i - a) (by omega)]
        rw [decide_eq_decide,fin_eq]
        simp only
        omega
    rw [getDOpt,getOptEq h1,Option.getD_some] at key
    rw [key]
    simp [inp]
open PEqualNP.MetaComplexity PEqualNP.Represents
theorem pr_point (k d u v:ℕ) (hkd:k≤ d) (hu:u< d) (M:Finset (Finset (Fin k))) (hM:IsM M) :
    Pr (fun w =>w.val) (fun w =>d+w.val) Finset.univ M (two u (d+v)) ↔ u=v∧u< k:= by
  constructor
  · rintro (⟨w,_,h1,h2⟩ | ⟨e,he,h⟩)
    · simp only [two,decide_eq_true_eq] at h1 h2
      have:= w.isLt
      omega
    · obtain ⟨a,b,hab,rfl⟩:= Finset.card_eq_two.1 (hM.1 e he)
      have hne:a.val ≠ b.val:= fun c =>hab (Fin.ext c)
      have ha:= a.isLt
      have hb:= b.isLt
      simp only [two,decide_eq_true_eq,mem_ins,mem_oneF,forall_eq_or_imp,
        forall_eq] at h
      omega
  · rintro ⟨h,hk⟩
    left
    refine ⟨⟨u,hk⟩,mem_all _,by simp [two],by simp [two,h]⟩
theorem goodC_of_fan (C:Circuit) (h:FanInTwo C):GoodC C:= by
  intro g hg
  have:= h g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at this
  exact this
theorem eval_val (C:Circuit) (n:ℕ) (l:BitTape) (h:l.length=n) :
    C.eval l=val C n C.output (fun i =>l.getD i false):= by
  change C.eval l=C.eval (inp n (fun i =>l.getD i false))
  rw [← list_inp l n h]
theorem classify_false (k:ℕ) (hk:2≤ k) (C:Circuit) (hm:Monotone2 C) (hs:C.size+1≤ 2 * k)
    (hR:∀ u v:Fin k,C.eval (oneEach u v)=decide (u.val=v.val)) :
    ∃ M:Finset (Finset (Fin k)),IsM M∧∀ x y:Fin k→ Bool,
      C.eval (List.ofFn x ++ List.ofFn y)=true ↔
        Pr (fun w =>w.val) (fun w =>k+w.val) Finset.univ M (fun i =>(List.ofFn x ++ List.ofFn y).getD i false):= by
  have hg:GoodC C:= by
    intro g hg
    have:= hm g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at this
    exact ⟨this.1.imp id Or.inl,this.2⟩
  have hmon:∀ g∈C.gates,g.op ≠ GateOp.not:= by
    intro g hg c
    have:= (hm g hg).1
    rw [c] at this
    simp at this
  obtain ⟨M,hM,h⟩:= class_id k hk C hg hmon hs (by
    intro u v
    have:= hR u v
    rw [oneEach_inp] at this
    rw [show decide (u=v)=decide (u.val=v.val) from decide_eq_decide.2 fin_eq]
    exact this)
  refine ⟨M,hM,fun x y =>?_⟩
  rw [eval_val C (k+k) _ (by simp)]
  exact h _
theorem classify_true (k:ℕ) (hk:7≤ k) (C:Circuit) (hf:FanInTwo C) (hs:C.size≤ 2 * k+1)
    (hR:∀ (u:Fin (k+2)) (v:Fin (k+1)),C.eval (oneEach u v) =
      decide (u.val ≠ k+1∧¬ (u.val< k∧u.val=v.val))) :
    ∃ M:Finset (Finset (Fin k)),IsM M∧∀ (x:Fin (k+2)→ Bool) (y:Fin (k+1)→ Bool),
      C.eval (List.ofFn x ++ List.ofFn y)=true ↔
        ¬ ((List.ofFn x ++ List.ofFn y).getD (k+1) false=true ∨
          Pr (fun w =>w.val) (fun w =>k+2+w.val) Finset.univ M (fun i =>(List.ofFn x ++ List.ofFn y).getD i false)):= by
  obtain ⟨M,hM,h⟩:= class_crown k hk C (goodC_of_fan C hf) hs (by
    intro u hu v hv
    have:= hR ⟨u,hu⟩ ⟨v,hv⟩
    rw [oneEach_inp] at this
    change val C (k+2+(k+1)) C.output (two u (k+2+v))=_ at this
    rw [this,decide_eq_true_eq]
    rfl)
  refine ⟨M,hM,fun x y =>?_⟩
  rw [eval_val C (k+2+(k+1)) _ (by rw [len_app,List.length_ofFn,List.length_ofFn])]
  exact h _
theorem construct (k nr n:ℕ) (hk:2≤ k) (hn:∀ u:Fin k,u.val< n∧nr+u.val< n)
    (M:Finset (Finset (Fin k))) (hM:IsM M) :
    ∃ (gs:List Gate) (o:ℕ),Mon gs∧gs.length+1=2 * k∧o< n+gs.length ∧
      ∀ f,(run gs (inp n f)).getD o false=true ↔ Pr (fun w =>w.val) (fun w =>nr+w.val) Finset.univ M f:= by
  obtain ⟨l,h1,h2⟩:= blocks nr M hM
  have hl:l ≠ []:= by
    intro c
    rw [c] at h1
    simp at h1
    omega
  have key:∀ f,_:= fun f =>build_ok nr n hn f (inp n f) (inp_len n f)
    (fun i hi => by simp [inp,getDOpt,hi]) l hl
  refine ⟨(build nr n l).1,(build nr n l).2,(key (fun _ =>false)).2.2.2,
    (key (fun _ =>false)).2.2.1.trans h1,(key (fun _ =>false)).2.1,fun f =>?_⟩
  rw [(key f).1]
  exact h2 f
theorem circuit_false (k:ℕ) (hk:2≤ k) (M:Finset (Finset (Fin k))) (hM:IsM M) :
    ∃ C:Circuit,Monotone2 C∧C.size+1≤ 2 * k ∧
      (∀ u v:Fin k,C.eval (oneEach u v)=decide (u.val=v.val)) ∧
      ∀ x y:Fin k→ Bool,C.eval (List.ofFn x ++ List.ofFn y)=true ↔
        Pr (fun w =>w.val) (fun w =>k+w.val) Finset.univ M (fun i =>(List.ofFn x ++ List.ofFn y).getD i false):= by
  obtain ⟨gs,o,h1,h2,_,h4⟩:= construct k k (k+k) hk (fun u => by have:= u.isLt; omega) M hM
  have ev:∀ f,(⟨gs,o⟩:Circuit).eval (inp (k+k) f)=true ↔
      Pr (fun w =>w.val) (fun w =>k+w.val) Finset.univ M f:= h4
  refine ⟨⟨gs,o⟩,?_,?_,?_,?_⟩
  · intro g hg
    have:= h1 g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    exact this
  · change gs.length+1≤ 2 * k
    omega
  · intro u v
    have hu:= u.isLt
    rw [oneEach_inp,Bool.eq_iff_iff,ev,pr_point k k u.val v.val le_rfl hu M hM,decide_eq_true_eq]
    omega
  · intro x y
    have e:= list_inp (List.ofFn x ++ List.ofFn y) (k+k) (by simp)
    conv_lhs =>rw [e]
    exact ev _
theorem circuit_true (k:ℕ) (hk:2≤ k) (M:Finset (Finset (Fin k))) (hM:IsM M) :
    ∃ C:Circuit,FanInTwo C∧C.size≤ 2 * k+1 ∧
      (∀ (u:Fin (k+2)) (v:Fin (k+1)),C.eval (oneEach u v) =
        decide (u.val ≠ k+1∧¬ (u.val< k∧u.val=v.val))) ∧
      ∀ (x:Fin (k+2)→ Bool) (y:Fin (k+1)→ Bool),C.eval (List.ofFn x ++ List.ofFn y)=true ↔
        ¬ ((List.ofFn x ++ List.ofFn y).getD (k+1) false=true ∨
          Pr (fun w =>w.val) (fun w =>k+2+w.val) Finset.univ M (fun i =>(List.ofFn x ++ List.ofFn y).getD i false)):= by
  obtain ⟨gs,o,h1,h2,h3,h4⟩:= construct k (k+2) (k+2+(k+1)) hk
    (fun u => by have:= u.isLt; omega) M hM
  let n:= k+2+(k+1)
  let m:= n+gs.length
  let C:Circuit:= ⟨gs ++ [⟨GateOp.or,[o,k+1]⟩,⟨GateOp.not,[m]⟩],m+1⟩
  have ev:∀ f,C.eval (inp n f)=true ↔
      ¬ (f (k+1)=true∨Pr (fun w =>w.val) (fun w =>k+2+w.val) Finset.univ M f):= by
    intro f
    let w:= run gs (inp n f)
    have lw:w.length=m:= by simp only [w,run_length,inp_len,m]
    have a1:w.getD (k+1) false=f (k+1):= by
      simp only [w]
      rw [prefix_keep _ _ (by rw [inp_len]; omega)]
      have:k+1< n:= by omega
      simp [inp,getDOpt,this]
    have s1:step w ⟨GateOp.or,[o,k+1]⟩=w ++ [w.getD o false || f (k+1)]:= by
      simp only [step,mapC,mapN,a1]
      simp [GateOp.eval]
    have s2:∀ b:Bool,step (w ++ [b]) ⟨GateOp.not,[m]⟩=w ++ [b] ++ [!b]:= by
      intro b
      simp only [step,mapC,mapN]
      rw [getD_new _ _ lw.symm]
      simp [GateOp.eval]
    have e:C.eval (inp n f)=!(w.getD o false || f (k+1)):= by
      change (run (gs ++ [⟨GateOp.or,[o,k+1]⟩,⟨GateOp.not,[m]⟩]) (inp n f)).getD (m+1) false=_
      rw [run_append]
      change (run [⟨GateOp.or,[o,k+1]⟩,⟨GateOp.not,[m]⟩] w).getD (m+1) false=_
      rw [run_cons,s1,run_cons,s2,run_nil]
      exact getD_new _ _ (by simp [lw])
    rw [e,← h4 f]
    change (!(w.getD o false || f (k+1)))=true ↔ ¬ (f (k+1)=true∨w.getD o false=true)
    cases w.getD o false <;> cases f (k+1) <;> simp
  refine ⟨C,?_,?_,?_,?_⟩
  · intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    simp only [C,mem_app,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with hg | rfl | rfl
    · have:= h1 g hg
      exact ⟨this.1.imp id Or.inl,this.2⟩
    · simp
    · simp
  · change (gs ++ [_,_]).length≤ 2 * k+1
    simp only [len_app,len_cons,len_nil]
    omega
  · intro u v
    have hu:= u.isLt
    have hv:= v.isLt
    rw [oneEach_inp,Bool.eq_iff_iff,ev,pr_point k (k+2) u.val v.val (by omega) hu M hM,
      decide_eq_true_eq]
    simp only [two,decide_eq_true_eq]
    omega
  · intro x y
    have e:= list_inp (List.ofFn x ++ List.ofFn y) n
      (by rw [len_app,List.length_ofFn,List.length_ofFn])
    conv_lhs =>rw [e]
    exact ev _
def ends {k:Nat} (edge:Fin k × Fin k):Finset (Fin k):= {edge.1,edge.2}
theorem ends_injective {k:Nat} (edge other:Fin k × Fin k)
    (ord:edge.1< edge.2) (ord':other.1< other.2) (eq:ends edge=ends other):edge=other:= by
  have left:edge.1∈ends other:= eq ▸ Finset.mem_insert_self _ _
  have right:edge.2∈ends other:= eq ▸ mem_ins_of (Finset.mem_singleton_self _)
  simp only [ends,mem_ins,mem_oneF] at left right
  rcases left with left | left <;> rcases right with right | right
  · exact (ord.ne (left.trans right.symm)).elim
  · exact Prod.ext left right
  · rw [left,right] at ord
    exact (lt_asymm ord ord').elim
  · exact (ord.ne (left.trans right.symm)).elim
theorem probe_Pr {k nr nc:Nat} (h1:k≤ nr) (h2:k≤ nc)
    (edge:Fin k × Fin k) (ord:edge.1< edge.2) (matching:Finset (Finset (Fin k))) (hm:IsM matching) :
    let x:= fun i:Fin nr =>decide (i.val=edge.1.val∨i.val=edge.2.val)
    let y:= fun _:Fin nc =>false
    Pr (fun w =>w.val) (fun w =>nr+w.val) Finset.univ matching
      (fun i =>(List.ofFn x ++ List.ofFn y).getD i false) ↔ ends edge∈matching:= by
  intro x y
  have hv (w:Fin k):w.val< nr:= w.isLt.trans_le h1
  have hw (w:Fin k):w.val< nc:= w.isLt.trans_le h2
  simp only [Pr,getD_app_left x y _ (hv _),getD_app_right x y _ (hw _),x,y,
    Bool.false_eq_true,and_false,exists_const,mem_all,true_and,false_or,decide_eq_true_eq,
    Fin.val_eq_val,exists_false]
  constructor
  · rintro ⟨key,hk,left | empty⟩
    · have sub:key ⊆ ends edge:= by
        intro v hv
        simpa only [ends,mem_ins,mem_oneF] using left v hv
      have eq:key=ends edge:= Finset.eq_of_subset_of_card_le sub (by simp [ends,ord.ne,hm.1 key hk])
      exact eq ▸ hk
    · obtain ⟨v,hv'⟩:= Finset.card_pos.mp (show 0< key.card by rw [hm.1 key hk]; decide +kernel)
      exact False.elim (empty v hv')
  · intro member
    exact ⟨_,member,Or.inl (by simp [ends])⟩
def active {k nr nc:Nat} (matching:Finset (Finset (Fin k)))
    (x:Fin nr→ Bool) (y:Fin nc→ Bool):Prop :=
  Pr (fun w =>w.val) (fun w =>nr+w.val) Finset.univ matching
    (fun i =>(List.ofFn x ++ List.ofFn y).getD i false)
theorem classify_observations (k:Nat) (crown:Bool) (small:2≤ k) (big:crown=true→ 7≤ k) :
    let nr:= if crown then k+2 else k
    let nc:= if crown then k+1 else k
    let A:= fun (i:Fin nr) (j:Fin nc) =>if crown then
      decide (i.val ≠ k+1∧¬ (i.val< k∧i.val=j.val)) else decide (i.val=j.val)
    ∀ C:Circuit,(if crown then FanInTwo C∧C.size≤ 2 * k+1 else Monotone2 C∧C.size+1≤ 2 * k) →
      Represents A C→ ∃ matching:Finset (Finset (Fin k)),IsM matching ∧
      ∀ (x:Fin nr→ Bool) (y:Fin nc→ Bool),
        C.eval (List.ofFn x ++ List.ofFn y)=!crown ↔
          (crown=true∧(List.ofFn x ++ List.ofFn y).getD (k+1) false=true)∨active matching x y:= by
  cases crown
  · intro nr nc A circ good repr
    obtain ⟨matching,hm,law⟩:= classify_false k (by omega) circ good.1 good.2 repr
    refine ⟨matching,hm,fun x y =>?_⟩
    simp only [Bool.not_false,Bool.false_eq_true,false_and,false_or]
    exact law x y
  · intro nr nc A circ good repr
    obtain ⟨matching,hm,law⟩:= classify_true k (big rfl) circ good.1 good.2 repr
    refine ⟨matching,hm,fun x y =>?_⟩
    have spec:= law x y
    change (circ.eval (List.ofFn x ++ List.ofFn y)=false ↔ _)
    simp only [true_and]
    have res:= not_congr spec
    simp only [Bool.not_eq_true,not_not] at res
    exact res
theorem min_key_sorted {k:Nat} (key:Finset (Fin k)) (sz:key.card=2) :
    ∃ edge:Fin k × Fin k,edge.1< edge.2∧ends edge=key:= by
  obtain ⟨a,b,ne,rfl⟩:= Finset.card_eq_two.mp sz
  rcases lt_or_gt_of_ne ne with ord | ord
  · exact ⟨(a,b),ord,rfl⟩
  · exact ⟨(b,a),ord,Finset.pair_comm _ _⟩
theorem exists_observations (k:Nat) (crown:Bool) (small:2≤ k) (big:crown=true→ 7≤ k) (matching:Finset (Finset (Fin k)))
    (hm:IsM matching) :
    let nr:= if crown then k+2 else k
    let nc:= if crown then k+1 else k
    let A:= fun (i:Fin nr) (j:Fin nc) =>if crown then
      decide (i.val ≠ k+1∧¬ (i.val< k∧i.val=j.val)) else decide (i.val=j.val)
    ∃ C:Circuit,(if crown then FanInTwo C∧C.size≤ 2 * k+1 else Monotone2 C∧C.size+1≤ 2 * k) ∧
      Represents A C∧∀ (x:Fin nr→ Bool) (y:Fin nc→ Bool),
        C.eval (List.ofFn x ++ List.ofFn y)=!crown ↔
          (crown=true∧(List.ofFn x ++ List.ofFn y).getD (k+1) false=true)∨active matching x y:= by
  cases crown
  · obtain ⟨c,mon,size,rep,ev⟩:= circuit_false k (by omega) matching hm
    refine ⟨c,⟨mon,size⟩,rep,fun x y =>?_⟩
    simp only [Bool.not_false,Bool.false_eq_true,false_and,false_or]
    exact ev x y
  · obtain ⟨c,fan,size,rep,ev⟩:= circuit_true k (by omega) matching hm
    refine ⟨c,⟨fan,size⟩,rep,fun x y =>?_⟩
    have spec:= not_congr (ev x y)
    simp only [Bool.not_eq_true,not_not] at spec
    simp only [Bool.not_true,true_and]
    exact spec
theorem probe_as_matching {k nr nc:Nat} (h1:k≤ nr) (h2:k≤ nc) (crown:Bool)
    (h3:crown=true→ k+1< nr) (matching:Finset (Finset (Fin k))) (hm:IsM matching)
    (f:(Fin nr→ Bool)→ (Fin nc→ Bool)→ Bool)
    (law:∀ x y,f x y=!crown ↔ (crown=true∧(List.ofFn x ++ List.ofFn y).getD (k+1) false=true)∨active matching x y)
    (edge:Fin k × Fin k) (ord:edge.1< edge.2) :
      f (fun i =>decide (i.val=edge.1.val∨i.val=edge.2.val)) (fun _ =>false)=!crown ↔ ends edge∈matching:= by
  let x:= fun i:Fin nr =>decide (i.val=edge.1.val∨i.val=edge.2.val)
  let y:= fun _:Fin nc =>false
  change f x y=!crown ↔ _
  rw [law]
  have noextra:¬ (crown=true∧(List.ofFn x ++ List.ofFn y).getD (k+1) false=true):= by
    rintro ⟨hc,hit⟩
    rw [getD_app_left x y _ (h3 hc)] at hit
    have hl:= edge.1.isLt
    have hr:= edge.2.isLt
    simp [x,show k+1 ≠ edge.1.val by omega,show k+1 ≠ edge.2.val by omega] at hit
  rw [or_iff_right noextra]
  exact probe_Pr h1 h2 edge ord matching hm
end Circ

end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641

variable {E : Type*} [DecidableEq E]

def coeff (g : Finset E → ℤ) (s : Finset E) : ℤ :=
  ∑ t ∈ s.powerset, (-1 : ℤ) ^ (s.card - t.card) * g t

def diff (g : Finset E → ℤ) (e : E) (t : Finset E) := g (insert e t) - g t

lemma coeff_insert (g : Finset E → ℤ) {e : E} {s : Finset E} (he : e ∉ s) :
    coeff g (insert e s) = coeff (diff g e) s := by
  unfold coeff
  rw [Finset.sum_powerset_insert he, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have sub := Finset.mem_powerset.mp ht
  have et : e ∉ t := fun h => he (sub h)
  have le := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem et]
  have r : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
  rw [r, pow_succ]
  simp only [Nat.add_sub_add_right, diff]
  ring

lemma coeff_congr {f g : Finset E → ℤ} {s : Finset E} (h : ∀ t ⊆ s, f t = g t) :
    coeff f s = coeff g s :=
  Finset.sum_congr rfl fun t ht => congrArg _ (h t (Finset.mem_powerset.mp ht))

lemma coeff_zero_on {f : Finset E → ℤ} {s : Finset E} (h : ∀ t ⊆ s, f t = 0) :
    coeff f s = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  rw [h t (Finset.mem_powerset.mp ht), mul_zero]

lemma inversion (g : Finset E → ℤ) (s : Finset E) : (∑ t ∈ s.powerset, coeff g t) = g s := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp [coeff]
  | @insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h : ∀ t ∈ s.powerset, coeff g (insert a t) = coeff (diff g a) t :=
      fun t ht => coeff_insert _ (fun h => ha (Finset.mem_powerset.mp ht h))
    rw [Finset.sum_congr rfl h, ih, ih]
    simp [diff]

lemma diff_pair (g : Finset E → ℤ) {e f : E} {t : Finset E}
    (ef : e ≠ f) (et : e ∉ t) (ft : f ∉ t) :
    coeff g (insert e (insert f t)) = coeff (diff (diff g e) f) t := by
  rw [coeff_insert g (by simpa using And.intro ef et), coeff_insert _ ft]

def Down (D : Finset E → Prop) := ∀ {s t : Finset E}, t ⊆ s → D s → D t

def AffineAt (D : Finset E → Prop) (g : Finset E → ℤ) (I : Finset E) :=
  ∀ K ⊆ I, ∃ (c : ℤ) (w : E → ℤ), ∀ s, D s → s ∩ I = K → g s = c + (s \ I).sum w

def Edge (D : Finset E → Prop) (g : Finset E → ℤ) (e f : E) :=
  e ≠ f ∧ ∃ s, e ∈ s ∧ f ∈ s ∧ D s ∧ coeff g s ≠ 0

def PairZero (D : Finset E → Prop) (g : Finset E → ℤ) (I : Finset E) :=
  ∀ e f, e ≠ f → e ∉ I → f ∉ I → ∀ t, e ∉ t → f ∉ t → D (insert e (insert f t)) →
    diff (diff g e) f t = 0

lemma affine_pairZero {D : Finset E → Prop} (hd : Down D) {g : Finset E → ℤ} {I : Finset E}
    (ha : AffineAt D g I) : PairZero D g I := by
  intro e f hef he hf t het hft hD
  let K := t ∩ I
  obtain ⟨c, w, hw⟩ := ha K Finset.inter_subset_right
  have dft := hd (Finset.subset_insert e _) hD
  have dt := hd (Finset.subset_insert f _) dft
  have det := hd (Finset.insert_subset_insert e (Finset.subset_insert f _)) hD
  have h0 := hw t dt rfl
  have h1 := hw (insert e t) det (Finset.insert_inter_of_notMem he)
  have h2 := hw (insert f t) dft (Finset.insert_inter_of_notMem hf)
  have h12 := hw _ hD (by simp only [Finset.insert_inter_of_notMem he, Finset.insert_inter_of_notMem hf, K])
  have a : e ∉ insert f (t \ I) := by simp [hef, het]
  have b : f ∉ t \ I := by simp [hft]
  have j : e ∉ t \ I := by simp [het]
  simp only [diff, h0, h1, h2, h12, Finset.insert_sdiff_of_notMem _ he,
    Finset.insert_sdiff_of_notMem _ hf, Finset.sum_insert a, Finset.sum_insert b, Finset.sum_insert j]
  ring

lemma diff_stable {D : Finset E → Prop} (hd : Down D) {g : Finset E → ℤ} {I : Finset E}
    (hz : PairZero D g I) {K U : Finset E} (hK : K ⊆ I) (dis : Disjoint U I) {e : E}
    (he : e ∉ I) (hU : e ∉ U) (hD : D (insert e (U ∪ K))) :
    diff g e (U ∪ K) = diff g e K := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
    rw [Finset.insert_union] at hD ⊢
    have ea : e ≠ a := fun h => hU (Finset.mem_insert.mpr (Or.inl h))
    have eu : e ∉ U := fun h => hU (Finset.mem_insert_of_mem h)
    obtain ⟨ai, dis'⟩ := Finset.disjoint_insert_left.mp dis
    have ek : e ∉ K := fun h => he (hK h)
    have ak : a ∉ K := fun h => ai (hK h)
    have hb := hz e a ea he ai (U ∪ K) (by simp [eu, ek]) (by simp [ha, ak]) hD
    have d := hd (Finset.insert_subset_insert e (Finset.subset_insert a _)) hD
    have q := ih dis' eu d
    unfold diff at hb
    unfold diff at q ⊢
    omega

lemma pairZero_affine {D : Finset E → Prop} (hd : Down D) {g : Finset E → ℤ} {I : Finset E}
    (hz : PairZero D g I) : AffineAt D g I := by
  intro K hK
  refine ⟨g K, fun e => diff g e K, ?_⟩
  have aux (U : Finset E) (dis : Disjoint U I) (hD : D (U ∪ K)) :
      g (U ∪ K) = g K + U.sum (fun e => diff g e K) := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert a U ha ih =>
      obtain ⟨ai, dis'⟩ := Finset.disjoint_insert_left.mp dis
      rw [Finset.insert_union] at hD ⊢
      have step := diff_stable hd hz hK dis' ai ha hD
      have old := ih dis' (hd (Finset.subset_insert a _) hD)
      rw [Finset.sum_insert ha]
      unfold diff at step old ⊢
      omega
  intro s hs hi
  have h : (s \ I) ∪ K = s := by rw [← hi, Finset.sdiff_union_inter]
  have z := aux (s \ I) Finset.sdiff_disjoint (h.symm ▸ hs)
  simpa only [h] using z

lemma pairZero_covers {D : Finset E → Prop} (hd : Down D) {g : Finset E → ℤ} {I : Finset E}
    (hz : PairZero D g I) : ∀ e f, Edge D g e f → e ∈ I ∨ f ∈ I := by
  rintro e f ⟨ne,s,es,fs,ds,nz⟩
  by_contra! h
  let t := (s.erase e).erase f
  have fe : f ∈ s.erase e := Finset.mem_erase.mpr ⟨ne.symm,fs⟩
  have et : e ∉ t := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)
  have ft : f ∉ t := Finset.notMem_erase _ _
  have rep : insert e (insert f t) = s := by simp only [t,Finset.insert_erase fe,Finset.insert_erase es]
  apply nz
  rw [← rep, diff_pair g ne et ft]
  apply coeff_zero_on
  intro u hu
  apply hz e f ne h.1 h.2 u (fun b => et (hu b)) (fun b => ft (hu b))
  apply hd (Finset.insert_subset_insert e (Finset.insert_subset_insert f hu))
  exact rep.symm ▸ ds

lemma covers_pairZero {D : Finset E → Prop} (hd : Down D) {g : Finset E → ℤ} {I : Finset E}
    (hc : ∀ e f, Edge D g e f → e ∈ I ∨ f ∈ I) : PairZero D g I := by
  intro e f ne he hf t et ft ds
  rw [← inversion (diff (diff g e) f) t]
  apply Finset.sum_eq_zero
  intro u hu
  have sub := Finset.mem_powerset.mp hu
  rw [← diff_pair g ne (fun h => et (sub h)) (fun h => ft (sub h))]
  by_contra hn
  have h := hc e f ⟨ne, insert e (insert f u), by simp, by simp,
    hd (Finset.insert_subset_insert e (Finset.insert_subset_insert f sub)) ds, hn⟩
  exact h.elim he hf

lemma affine_iff_covers {D : Finset E → Prop} (hd : Down D) (g : Finset E → ℤ) (I : Finset E) :
    AffineAt D g I ↔ ∀ e f, Edge D g e f → e ∈ I ∨ f ∈ I :=
  ⟨fun h => pairZero_covers hd (affine_pairZero hd h), fun h => pairZero_affine hd (covers_pairZero hd h)⟩

def Realized {F : Type*} (fits : F → Prop) (probe : F → Finset E) (s : Finset E) :=
  ∃ f, fits f ∧ probe f = s

def CubeActive {F : Type*} (fits : F → Prop) (probe : F → Finset E) (score : F → ℤ)
    (s : Finset E) := ∃ cube : Finset E → F,
  (∀ t ⊆ s, fits (cube t) ∧ probe (cube t) = t) ∧ coeff (score ∘ cube) s ≠ 0

def Strong {F : Type*} (fits : F → Prop) (probe : F → Finset E) (score : F → ℤ)
    (I : Finset E) := ∀ K ⊆ I, ∃ (offset : ℤ) (w : E → ℤ),
    ∀ f, fits f → probe f ∩ I = K → score f = offset + ((probe f) \ I).sum w

lemma active_iff {F : Type*} (fits : F → Prop) (probe : F → Finset E) (score : F → ℤ)
    (hd : Down (Realized fits probe)) (g : Finset E → ℤ) (tracks : ∀ f, fits f → score f = g (probe f))
    (s : Finset E) : CubeActive fits probe score s ↔ Realized fits probe s ∧ coeff g s ≠ 0 := by
  classical
  constructor
  · rintro ⟨cube,h,hz⟩
    obtain ⟨hf,hp⟩ := h s Finset.Subset.rfl
    refine ⟨⟨cube s,hf,hp⟩,?_⟩
    rwa [coeff_congr (f := score ∘ cube) (g := g) (fun t ht =>
      (tracks _ (h t ht).1).trans (congrArg g (h t ht).2))] at hz
  · rintro ⟨hs,hz⟩
    obtain ⟨base,hbase⟩ := hs
    let cube := fun t => if h : Realized fits probe t then Classical.choose h else base
    have H (t : Finset E) (ht : t ⊆ s) : fits (cube t) ∧ probe (cube t) = t := by
      have h := hd ht (show Realized fits probe s from ⟨base,hbase⟩)
      simpa only [cube, dif_pos h] using Classical.choose_spec h
    refine ⟨cube,H,?_⟩
    rwa [coeff_congr (f := score ∘ cube) (g := g) (fun t ht =>
      (tracks _ (H t ht).1).trans (congrArg g (H t ht).2))]

lemma strong_iff_affine {F : Type*} (fits : F → Prop) (probe : F → Finset E) (score : F → ℤ)
    (g : Finset E → ℤ) (tracks : ∀ f, fits f → score f = g (probe f)) (I : Finset E) :
    Strong fits probe score I ↔ AffineAt (Realized fits probe) g I := by
  constructor
  · intro H K hK
    obtain ⟨b,w,H⟩ := H K hK
    refine ⟨b,w,?_⟩
    rintro _ ⟨f,hf,rfl⟩ hi
    rw [← tracks f hf]
    exact H f hf hi
  · intro H K hK
    obtain ⟨b,w,H⟩ := H K hK
    refine ⟨b,w,fun f hf hi => (tracks f hf).trans (H _ ⟨f,hf,rfl⟩ hi)⟩

def reward (z : E × E) (s : Finset E) : ℤ := if z.1 ∈ s ∨ z.2 ∈ s then 1 else 0

def rewardSum (A : Finset (E × E)) (s : Finset E) : ℤ := ∑ z ∈ A, reward z s

def zeta (h : Finset E → ℤ) (s : Finset E) := ∑ t ∈ s.powerset, h t

def mass {α : Type*} (A : Finset α) (U : α → Finset E) (w : α → ℤ) (s : Finset E) :=
  ∑ a ∈ A, if s ⊆ U a then w a else 0

end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace S

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev E (k : Nat) := Fin k × Fin k
def Vlist (k : Nat) := (List.finRange k).flatMap (fun i => ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
def V (k : Nat) := (Vlist k).toFinset
lemma ord {k : Nat} {e : E k} : e ∈ V k ↔ e.1 < e.2 := by
  obtain ⟨i,j⟩ := e
  simp [V,Vlist,List.mem_flatMap,List.mem_map,List.mem_filter]

def nr (k : Nat) (c : Bool) := if c then k+2 else k
def nc (k : Nat) (c : Bool) := if c then k+1 else k
abbrev X (k : Nat) (c : Bool) := Fin (nr k c) → Bool
abbrev Y (k : Nat) (c : Bool) := Fin (nc k c) → Bool
abbrev Fn (k : Nat) (c : Bool) := X k c → Y k c → Bool
abbrev Obs (k : Nat) (c : Bool) := X k c × Y k c
lemma hnr (k c) : k ≤ nr k c := by cases c <;> simp [nr]
lemma hnc (k c) : k ≤ nc k c := by cases c <;> simp [nc]
lemma dead_lt (k c) : c=true → k+1 < nr k c := by rintro rfl; simp [nr]

def eligible (k : Nat) (c : Bool) (f : Fn k c) := ∃ C : Circuit,
    (if c then FanInTwo C ∧ C.size ≤ 2*k+1 else Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    Represents (fun (i : Fin (nr k c)) (j : Fin (nc k c)) => if c then decide (i.val ≠ k+1 ∧ ¬(i.val < k ∧ i.val=j.val)) else decide (i.val=j.val)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)

def probe (k : Nat) (c : Bool) (f : Fn k c) := (V k).filter (fun e =>
  f (fun i => decide (i.val=e.1.val ∨ i.val=e.2.val)) (fun _ => false) = !c)

def fixed {k c} (z : Obs k c) : Prop :=
  (c=true ∧ (List.ofFn z.1 ++ List.ofFn z.2).getD (k+1) false = true) ∨
  ∃ i : Fin k, z.1 (i.castLE (hnr k c)) = true ∧ z.2 (i.castLE (hnc k c)) = true

def touches {k c} (z : Obs k c) (e : E k) : Prop :=
  (z.1 (e.1.castLE (hnr k c)) = true ∧ z.1 (e.2.castLE (hnr k c)) = true) ∨
  (z.2 (e.1.castLE (hnc k c)) = true ∧ z.2 (e.2.castLE (hnc k c)) = true)

def trig {k c} (s : Finset (E k)) (z : Obs k c) := fixed z ∨ ∃ e ∈ s, touches z e

def decode {k : Nat} (M : Finset (Finset (Fin k))) := (V k).filter (fun e => Circ.ends e ∈ M)

def Valid {k : Nat} (s : Finset (E k)) := s ⊆ V k ∧ Circ.IsM (s.image Circ.ends)

lemma decode_image {k} (M : Finset (Finset (Fin k))) (h : Circ.IsM M) :
    (decode M).image Circ.ends = M := by
  ext key
  constructor
  · intro hm
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp he).2
  · intro hm
    obtain ⟨e,he,eq⟩ := Circ.min_key_sorted key (h.1 key hm)
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨ord.mpr he,eq ▸ hm⟩,eq⟩

lemma image_decode {k} {s : Finset (E k)} (h : s ⊆ V k) : decode (s.image Circ.ends) = s := by
  ext e
  constructor
  · intro he
    obtain ⟨hv,hm⟩ := Finset.mem_filter.mp he
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hm
    exact Circ.ends_injective d e (ord.mp (h hd)) (ord.mp hv) eq ▸ hd
  · intro he
    exact Finset.mem_filter.mpr ⟨h he,Finset.mem_image_of_mem _ he⟩

lemma match_active {k c} (s : Finset (E k)) (z : Obs k c) :
    Circ.active (s.image Circ.ends) z.1 z.2 ↔
    (∃ i : Fin k, z.1 (i.castLE (hnr k c)) = true ∧ z.2 (i.castLE (hnc k c)) = true) ∨ ∃ e ∈ s, touches z e := by
  have hl (i : Fin k) : (List.ofFn z.1 ++ List.ofFn z.2).getD i.val false = z.1 (i.castLE (hnr k c)) :=
    Circ.getD_app_left z.1 z.2 _ (i.isLt.trans_le (hnr k c))
  have hr (i : Fin k) : (List.ofFn z.1 ++ List.ofFn z.2).getD (nr k c+i.val) false = z.2 (i.castLE (hnc k c)) :=
    Circ.getD_app_right z.1 z.2 _ (i.isLt.trans_le (hnc k c))
  simp only [Circ.active,Circ.Pr,Finset.mem_univ,true_and,hl,hr]
  simp [Circ.ends,touches]

lemma rep_law {k c} {f : Fn k c} {M : Finset (Finset (Fin k))} (hm : Circ.IsM M)
    (law : ∀ x y, f x y = !c ↔ (c=true ∧ (List.ofFn x ++ List.ofFn y).getD (k+1) false = true) ∨ Circ.active M x y) :
    probe k c f = decode M ∧ ∀ z : Obs k c, f z.1 z.2 = !c ↔ trig (decode M) z := by
  constructor
  · ext e
    simp only [probe,decode,Finset.mem_filter]
    apply and_congr_right
    intro hv
    exact Circ.probe_as_matching (hnr k c) (hnc k c) c (dead_lt k c) M hm f law e (ord.mp hv)
  · intro z
    rw [law,←decode_image M hm, match_active]
    simp only [decode_image M hm, trig, fixed, or_assoc]

lemma classifies {k c} (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) {f : Fn k c} (hf : eligible k c f) :
    Valid (probe k c f) ∧ ∀ z : Obs k c, f z.1 z.2 = !c ↔ trig (probe k c f) z := by
  obtain ⟨C,good,rep,ev⟩ := hf
  obtain ⟨M,hm,hM⟩ := Circ.classify_observations k c hk hc C good rep
  obtain ⟨p,hp⟩ := rep_law (f := f) hm (by intro x y; rw [ev]; exact hM x y)
  rw [p,Valid,decode_image _ hm]
  exact ⟨⟨Finset.filter_subset _ _,hm⟩,hp⟩

lemma realizes {k c} (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) {s : Finset (E k)} (hs : Valid s) :
    ∃ f : Fn k c, eligible k c f ∧ probe k c f = s ∧ ∀ z : Obs k c, f z.1 z.2 = !c ↔ trig s z := by
  obtain ⟨C,good,rep,ev⟩ := Circ.exists_observations k c hk hc (s.image Circ.ends) hs.2
  let f : Fn k c := fun x y => C.eval (List.ofFn x ++ List.ofFn y)
  obtain ⟨p,hp⟩ := rep_law (f := f) hs.2 ev
  rw [image_decode hs.1] at p hp
  exact ⟨f,⟨C,good,rep,fun _ _ => rfl⟩,p,hp⟩

end S
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Sig
variable {E : Type*} [DecidableEq E]

def unhit (A s : Finset E) : ℤ := if Disjoint A s then 1 else 0
lemma coeff_neg (g : Finset E → ℤ) (s : Finset E) : coeff (fun t => -g t) s = - coeff g s := by
  simp [coeff,Finset.sum_neg_distrib]
lemma coeff_add (f g : Finset E → ℤ) (s : Finset E) : coeff (fun t => f t + g t) s = coeff f s + coeff g s := by
  simp [coeff,mul_add,Finset.sum_add_distrib]
lemma coeff_const (b : ℤ) {s : Finset E} (hn : s.Nonempty) : coeff (fun _ => b) s = 0 := by
  rcases hn with ⟨e,he⟩
  rw [← Finset.insert_erase he, coeff_insert _ (Finset.notMem_erase _ _)]
  exact coeff_zero_on (by simp [diff])
lemma unhit_coeff (A s : Finset E) : coeff (unhit A) s = if s ⊆ A then (-1 : ℤ)^s.card else 0 := by
  induction s using Finset.induction_on with
  | empty => rw [show coeff (unhit A) ∅ = unhit A ∅ by simp [coeff]]; simp [unhit]
  | @insert e s he ih =>
    rw [coeff_insert _ he,Finset.card_insert_of_notMem he]
    by_cases h : e ∈ A
    · have eq : diff (unhit A) e = fun t => -unhit A t := by
        funext t
        simp [diff,unhit,Finset.disjoint_insert_right,h]
      rw [eq,coeff_neg,ih]; simp [Finset.insert_subset_iff,h,pow_succ]; split <;> simp
    · have eq : diff (unhit A) e = fun _ => 0 := by funext t; simp [diff,unhit,Finset.disjoint_insert_right,h]
      rw [eq,coeff_zero_on (fun _ _ => rfl)]; simp [Finset.insert_subset_iff,h]

abbrev hit (A s : Finset E) := (s ∩ A).Nonempty

def one (row : Finset E × Bool) (s : Finset E) : ℤ :=
  if decide (hit row.1 s) = row.2 then 1 else 0

def sign (b : Bool) : ℤ := if b then 1 else -1

def score (rows : List (Finset E × Bool)) (s : Finset E) : ℤ := (rows.map (fun row => one row s)).sum

def signed (rows : List (Finset E × Bool)) (s : Finset E) : ℤ :=
  ((rows.filter (fun t => t.2 && decide (s ⊆ t.1))).length : ℤ) -
  ((rows.filter (fun t => !t.2 && decide (s ⊆ t.1))).length : ℤ)

lemma one_coeff (r : Finset E × Bool) (s : Finset E) (hn : s.Nonempty) :
    coeff (one r) s = (-1 : ℤ)^(s.card+1) * (if s ⊆ r.1 then sign r.2 else 0) := by
  have hh (t A : Finset E) : hit A t ↔ ¬Disjoint A t := by
    simp only [hit,Finset.not_disjoint_iff,Finset.Nonempty,Finset.mem_inter]; grind
  obtain ⟨A,b⟩ := r
  cases b
  · have eq : one (A,false) = unhit A := by funext t; simp [one,unhit,hh]
    rw [eq,unhit_coeff]; simp only [sign, Bool.false_eq_true, ite_false,pow_succ]; split <;> ring
  · have eq : one (A,true) = fun t => 1 + -(unhit A t) := by
      funext t; by_cases h : Disjoint A t <;> simp [one,unhit,hh,h]
    rw [eq,coeff_add,coeff_const _ hn,coeff_neg,unhit_coeff]
    simp only [sign,ite_true,pow_succ,zero_add]; split <;> ring

lemma score_coeff (rows : List (Finset E × Bool)) (s : Finset E) (hn : s.Nonempty) :
    coeff (score rows) s = (-1 : ℤ)^(s.card+1) * signed rows s := by
  induction rows with
  | nil => simp [score,coeff,signed]
  | cons r rs ih =>
    have eq : score (r::rs) = fun t => one r t + score rs t := by funext t; simp [score]
    rw [eq,coeff_add,one_coeff _ _ hn,ih]
    have nextSigned : signed (r::rs) s = (if s ⊆ r.1 then sign r.2 else 0) + signed rs s := by
      obtain ⟨A,b⟩ := r
      cases b <;> by_cases h : s ⊆ A <;> simp [signed,sign,h,List.filter_cons] <;> ring
    rw [nextSigned,mul_add]

end Sig
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace S

variable {k : Nat} {c : Bool}

def fits (hard : List (Obs k c)) (f : Fn k c) := eligible k c f ∧ ∀ z ∈ hard, f z.1 z.2 = c

def scoreP (soft : List (Obs k c × Bool)) (f : Fn k c) : ℤ :=
  ((soft.filter (fun t => decide (f t.1.1 t.1.2 = t.2))).length : ℤ)

def possible (hard : List (Obs k c)) := ∀ z ∈ hard, ¬fixed z

noncomputable def allowed (hard : List (Obs k c)) : Finset (E k) := by
  classical
  exact (V k).filter (fun e => possible hard ∧ ∀ z ∈ hard, ¬ touches z e)

noncomputable def mask (z : Obs k c) : Finset (E k) := by
  classical
  exact (V k).filter (fun e => ¬fixed z ∧ touches z e)

noncomputable def label (t : Obs k c × Bool) : Bool := by
  classical
  exact if fixed t.1 then decide (t.2=c) else decide (t.2≠c)

noncomputable def normRows (soft : List (Obs k c × Bool)) :=
  soft.map (fun t => (mask t.1,label t))

lemma not_flip (a c : Bool) : a = c ↔ a ≠ !c := by cases a <;> cases c <;> decide +kernel

lemma realized_fits (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) (hard : List (Obs k c)) (s : Finset (E k)) :
  Realized (fits hard) (probe k c) s ↔ possible hard ∧ Valid s ∧ s ⊆ allowed hard := by
  classical
  constructor
  · rintro ⟨f,⟨he,hf⟩,rfl⟩
    obtain ⟨valid,ev⟩ := classifies hk hc he
    have no (z) (hz : z ∈ hard) : ¬trig (probe k c f) z := fun ht =>
      (not_flip _ _).mp (hf z hz) ((ev z).mpr ht)
    have hp : possible hard := fun z hz hu => no z hz (Or.inl hu)
    refine ⟨hp,valid,fun e hm => Finset.mem_filter.mpr ⟨valid.1 hm,hp,?_⟩⟩
    exact fun z hz t => no z hz (Or.inr ⟨e,hm,t⟩)
  · rintro ⟨hp,vs,sub⟩
    obtain ⟨f,he,eq,ev⟩ := realizes hk hc vs
    refine ⟨f,⟨he,?_⟩,eq⟩
    intro z hz
    apply (not_flip _ _).mpr
    intro h
    rcases (ev z).mp h with fixedZ | ⟨e,hm,hit⟩
    · exact hp z hz fixedZ
    · exact (Finset.mem_filter.mp (sub hm)).2.2 z hz hit

lemma fits_down (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) (hard : List (Obs k c)) :
    Down (Realized (fits hard) (probe k c)) := by
  intro s t sub hs
  rw [realized_fits hk hc] at hs ⊢
  exact ⟨hs.1,⟨sub.trans hs.2.1.1, Circ.IsM.mono hs.2.1.2 (Finset.image_subset_image sub)⟩, sub.trans hs.2.2⟩

lemma norm_one (s : Finset (E k)) (hs : s ⊆ V k) (f : Fn k c) (t : Obs k c × Bool)
    (ev : f t.1.1 t.1.2 = !c ↔ trig s t.1) :
    Sig.one (mask t.1,label t) s = if f t.1.1 t.1.2 = t.2 then 1 else 0 := by
  classical
  have h : Sig.hit (mask t.1) s ↔ ¬fixed t.1 ∧ ∃ e ∈ s, touches t.1 e := by
    change (∃ e, e ∈ s ∩ mask t.1) ↔ _
    simp only [Finset.mem_inter,mask,Finset.mem_filter]; grind
  dsimp only [Sig.one, label]
  by_cases h0 : fixed t.1
  · have a := ev.mpr (Or.inl h0)
    rw [a]; simp only [h,h0,ite_true,not_true_eq_false,false_and,decide_false]; cases c <;> cases t.2 <;> rfl
  · have law : Sig.hit (mask t.1) s ↔ f t.1.1 t.1.2 = !c := by simpa [h,h0,trig] using ev.symm
    simp only [if_neg h0,law]; cases c <;> cases f t.1.1 t.1.2 <;> cases t.2 <;> rfl

lemma tracks_score (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) (soft : List (Obs k c × Bool))
    {f : Fn k c} (he : eligible k c f) : scoreP soft f = Sig.score (normRows soft) (probe k c f) := by
  obtain ⟨val,ev⟩ := classifies hk hc he
  induction soft with
  | nil => simp [scoreP,normRows,Sig.score]
  | cons a r ih =>
    have next := norm_one (probe k c f) val.1 f a (ev a.1)
    simp only [normRows,List.map_cons,Sig.score,List.sum_cons] at ih ⊢
    rw [next,←ih]
    by_cases h : f a.1.1 a.1.2 = a.2 <;> simp [scoreP,h] <;> omega

abbrev PF (hard : List (Obs k c)) := Realized (fits hard) (probe k c)

def rel (D : Finset (E k)) (rows : List (Finset (E k) × Bool)) (e f : E k) : Prop :=
  e ≠ f ∧ ∃ Q, e ∈ Q ∧ f ∈ Q ∧ Q ⊆ D ∧ Valid Q ∧ Sig.signed rows Q ≠ 0

lemma rel_edge (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) (hard : List (Obs k c))
    (rows : List (Finset (E k) × Bool)) (e f : E k) :
    rel (allowed hard) rows e f ↔ Edge (PF hard) (Sig.score rows) e f := by
  classical
  constructor
  · rintro ⟨ne,Q,he,hf,sub,valid,nz⟩
    have possibleH := (Finset.mem_filter.mp (sub he)).2.1
    exact ⟨ne,Q,he,hf,(realized_fits hk hc _ _).mpr ⟨possibleH,valid,sub⟩,by
      rw [Sig.score_coeff _ _ ⟨_,he⟩]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) nz⟩
  · rintro ⟨ne,Q,he,hf,yes,nz⟩
    obtain ⟨_,valid,sub⟩ := (realized_fits hk hc _ _).mp yes
    exact ⟨ne,Q,he,hf,sub,valid,fun h => nz (by rw [Sig.score_coeff _ _ ⟨_,he⟩,h,mul_zero])⟩

end S
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Enc
open PT PT.Lib PT.Lib.Machines PT.Lib.Universal PT.Lib.R PT.Lib.Loop PT.Alg
abbrev W := List Bool

theorem flatC {n : W → Nat} {h : Nat → W → W} (hn : NatR n)
    (hh : CPTs (fun t => h (unpairB t).1.length (unpairB t).2)) :
    CPTs (fun s => (List.range (n s)).flatMap (fun i => h i s)) := by
  have p := cpt_flatMapRange (f := fun t => h (unpairB t).1.length (unpairB t).2)
    (cnt := fun t => un (n t)) (arg := id) hh hn cpt_id
  exact cptE p (fun s => by simp only [un_length,unpairB_pairB,id_eq])

def emit (n : Nat) : W := [decide (n ≠ 0)]
theorem emitC {n : W → Nat} (h : NatR n) : CPTs (fun s => emit (n s)) :=
  cptE (cpt_bitsOf (vecR_single h)) (fun _ => rfl)

def headr (n : Nat) : W := List.replicate n true ++ [false]
theorem headerC {n : W → Nat} (h : NatR n) : CPTs (fun s => headr (n s)) :=
  cpt_app2 (tqcN h) (cpt_const [false])

def names (x : W) : Nat := (runAt x 1)
theorem namesC {x : W → W} (hx : CPTs x) : NatR (fun s => names (x s)) :=
  (natR_runAt hx (natR_const 1))

def flag (x : W) : Nat := (bit x 0)
theorem flagC {x : W → W} (hx : CPTs x) : NatR (fun s => flag (x s)) :=
  (natR_bit hx (natR_const 0))

def nrows (x : W) : Nat := ((names x) + (2 * (flag x)))
theorem nrowsC {x : W → W} (hx : CPTs x) : NatR (fun s => nrows (x s)) :=
  (natR_add (namesC hx) (natR_mul (natR_const 2) (flagC hx)))

def spanW (x : W) : Nat := (((nrows x) + (names x)) + (flag x))
theorem spanWC {x : W → W} (hx : CPTs x) : NatR (fun s => spanW (x s)) :=
  (natR_add (natR_add (nrowsC hx) (namesC hx)) (flagC hx))

def hardN (x : W) : Nat := (runAt x ((names x) + 2))
theorem hardNC {x : W → W} (hx : CPTs x) : NatR (fun s => hardN (x s)) :=
  (natR_runAt hx (natR_add (namesC hx) (natR_const 2)))

def hardAt (x : W) : Nat := ((((names x) + 2) + (hardN x)) + 1)
theorem hardAtC {x : W → W} (hx : CPTs x) : NatR (fun s => hardAt (x s)) :=
  (natR_add (natR_add (natR_add (namesC hx) (natR_const 2)) (hardNC hx)) (natR_const 1))

def softMark (x : W) : Nat := ((hardAt x) + ((spanW x) * (hardN x)))
theorem softMarkC {x : W → W} (hx : CPTs x) : NatR (fun s => softMark (x s)) :=
  (natR_add (hardAtC hx) (natR_mul (spanWC hx) (hardNC hx)))

def softN (x : W) : Nat := (runAt x (softMark x))
theorem softNC {x : W → W} (hx : CPTs x) : NatR (fun s => softN (x s)) :=
  (natR_runAt hx (softMarkC hx))

def softAt (x : W) : Nat := (((softMark x) + (softN x)) + 1)
theorem softAtC {x : W → W} (hx : CPTs x) : NatR (fun s => softAt (x s)) :=
  (natR_add (natR_add (softMarkC hx) (softNC hx)) (natR_const 1))

def forced (x : W) (a : Nat) : Nat := (((flag x) * (bit x ((a + (names x)) + 1))) + ((List.range (names x)).map (fun i => ((bit x (a + i)) * (bit x ((a + (nrows x)) + i))))).sum)
theorem forcedC {x : W → W} {a : W → Nat} (hx : CPTs x) (ha : NatR a) : NatR (fun s => forced (x s) (a s)) :=
  (natR_add (natR_mul (flagC hx) (natR_bit hx (natR_add (natR_add ha (namesC hx)) (natR_const 1)))) (natR_sum (tqgN (namesC hx) (natR_mul (natR_bit (cpt_comp cpt_unpairB2 hx) (natR_add (tqzN ha cpt_unpairB2) (tqzI cpt_id))) (natR_bit (cpt_comp cpt_unpairB2 hx) (natR_add (natR_add (tqzN ha cpt_unpairB2) (nrowsC (cpt_comp cpt_unpairB2 hx))) (tqzI cpt_id)))))))

def touch (x : W) (a : Nat) (b : Nat) : Nat := (((bit x (a + (g (pI (names x)) b))) * (bit x (a + (g (pJ (names x)) b)))) + ((bit x ((a + (nrows x)) + (g (pI (names x)) b))) * (bit x ((a + (nrows x)) + (g (pJ (names x)) b)))))
theorem touchC {x : W → W} {a : W → Nat} {b : W → Nat} (hx : CPTs x) (ha : NatR a) (hb : NatR b) : NatR (fun s => touch (x s) (a s) (b s)) :=
  (natR_add (natR_mul (natR_bit hx (natR_add ha (natR_get (vecR_pI (namesC hx)) hb))) (natR_bit hx (natR_add ha (natR_get (vecR_pJ (namesC hx)) hb)))) (natR_mul (natR_bit hx (natR_add (natR_add ha (nrowsC hx)) (natR_get (vecR_pI (namesC hx)) hb))) (natR_bit hx (natR_add (natR_add ha (nrowsC hx)) (natR_get (vecR_pJ (namesC hx)) hb)))))

def allow (x : W) (a : Nat) : Nat := (if ((List.range (hardN x)).map (fun i => ((forced x ((hardAt x) + (i * (spanW x)))) + (touch x ((hardAt x) + (i * (spanW x))) a)))).sum = 0 then 1 else 0)
theorem allowC {x : W → W} {a : W → Nat} (hx : CPTs x) (ha : NatR a) : NatR (fun s => allow (x s) (a s)) :=
  (tqnE (natR_sum (tqgN (hardNC hx) (natR_add (forcedC (cpt_comp cpt_unpairB2 hx) (natR_add (hardAtC (cpt_comp cpt_unpairB2 hx)) (natR_mul (tqzI cpt_id) (spanWC (cpt_comp cpt_unpairB2 hx))))) (touchC (cpt_comp cpt_unpairB2 hx) (natR_add (hardAtC (cpt_comp cpt_unpairB2 hx)) (natR_mul (tqzI cpt_id) (spanWC (cpt_comp cpt_unpairB2 hx)))) (tqzN ha cpt_unpairB2))))) (natR_const 0) (natR_const 1) (natR_const 0))

def softWord (x : W) (a : Nat) : W := ((emit (if (forced x a) = 0 then (if (bit x (a + (spanW x))) = (flag x) then 0 else 1) else (if (bit x (a + (spanW x))) = (flag x) then 1 else 0))) ++ ((List.range (List.length (pI (names x)))).flatMap (fun i => (emit (if (forced x a) = 0 then (touch x a i) else 0)))))
theorem softWordC {x : W → W} {a : W → Nat} (hx : CPTs x) (ha : NatR a) : CPTs (fun s => softWord (x s) (a s)) :=
  (cpt_app2 (emitC (tqnE (forcedC hx ha) (natR_const 0) (tqnE (natR_bit hx (natR_add ha (spanWC hx))) (flagC hx) (natR_const 0) (natR_const 1)) (tqnE (natR_bit hx (natR_add ha (spanWC hx))) (flagC hx) (natR_const 1) (natR_const 0)))) (flatC (natR_vlen (vecR_pI (namesC hx))) (emitC (tqnE (forcedC (cpt_comp cpt_unpairB2 hx) (tqzN ha cpt_unpairB2)) (natR_const 0) (touchC (cpt_comp cpt_unpairB2 hx) (tqzN ha cpt_unpairB2) (tqzI cpt_id)) (natR_const 0)))))

def query (x : W) (a : Nat) (b : Nat) : W := (((((headr (names x)) ++ ((List.range (List.length (pI (names x)))).flatMap (fun i => (emit (allow x i))))) ++ ((List.range (List.length (pI (names x)))).flatMap (fun i => (emit (if i = a then 1 else (if i = b then 1 else 0)))))) ++ (headr (softN x))) ++ ((List.range (softN x)).flatMap (fun r => (softWord x ((softAt x) + (r * ((spanW x) + 1)))))))
theorem queryC {x : W → W} {a : W → Nat} {b : W → Nat} (hx : CPTs x) (ha : NatR a) (hb : NatR b) : CPTs (fun s => query (x s) (a s) (b s)) :=
  (cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 (headerC (namesC hx)) (flatC (natR_vlen (vecR_pI (namesC hx))) (emitC (allowC (cpt_comp cpt_unpairB2 hx) (tqzI cpt_id))))) (flatC (natR_vlen (vecR_pI (namesC hx))) (emitC (tqnE (tqzI cpt_id) (tqzN ha cpt_unpairB2) (natR_const 1) (tqnE (tqzI cpt_id) (tqzN hb cpt_unpairB2) (natR_const 1) (natR_const 0)))))) (headerC (softNC hx))) (flatC (softNC hx) (softWordC (cpt_comp cpt_unpairB2 hx) (natR_add (softAtC (cpt_comp cpt_unpairB2 hx)) (natR_mul (tqzI cpt_id) (natR_add (spanWC (cpt_comp cpt_unpairB2 hx)) (natR_const 1)))))))

def overlap (x : Nat) (a : Nat) (b : Nat) : Nat := (if (g (pI x) a) = (g (pI x) b) then 1 else (if (g (pI x) a) = (g (pJ x) b) then 1 else (if (g (pJ x) a) = (g (pI x) b) then 1 else (if (g (pJ x) a) = (g (pJ x) b) then 1 else 0))))
theorem overlapC {x : W → Nat} {a : W → Nat} {b : W → Nat} (hx : NatR x) (ha : NatR a) (hb : NatR b) : NatR (fun s => overlap (x s) (a s) (b s)) :=
  (tqnE (natR_get (vecR_pI hx) ha) (natR_get (vecR_pI hx) hb) (natR_const 1) (tqnE (natR_get (vecR_pI hx) ha) (natR_get (vecR_pJ hx) hb) (natR_const 1) (tqnE (natR_get (vecR_pJ hx) ha) (natR_get (vecR_pI hx) hb) (natR_const 1) (tqnE (natR_get (vecR_pJ hx) ha) (natR_get (vecR_pJ hx) hb) (natR_const 1) (natR_const 0)))))

def adjbit (x : W) (a : Nat) (b : Nat) : Nat := (if ((allow x a) * (allow x b)) = 0 then 0 else (if (overlap (names x) a b) = 0 then (bit (solveV (query x a b)) 0) else 0))
theorem adjbitC {x : W → W} {a : W → Nat} {b : W → Nat} (hx : CPTs x) (ha : NatR a) (hb : NatR b) : NatR (fun s => adjbit (x s) (a s) (b s)) :=
  (tqnE (natR_mul (allowC hx ha) (allowC hx hb)) (natR_const 0) (natR_const 0) (tqnE (overlapC (namesC hx) ha hb) (natR_const 0) (natR_bit (cpt_comp (queryC hx ha hb) cpt_solveV) (natR_const 0)) (natR_const 0)))

def rowbits (x : W) (a : Nat) : W := ((List.range (List.length (pI (names x)))).flatMap (fun j => (emit (adjbit x a j))))
theorem rowbitsC {x : W → W} {a : W → Nat} (hx : CPTs x) (ha : NatR a) : CPTs (fun s => rowbits (x s) (a s)) :=
  (flatC (natR_vlen (vecR_pI (namesC hx))) (emitC (adjbitC (cpt_comp cpt_unpairB2 hx) (tqzN ha cpt_unpairB2) (tqzI cpt_id))))

def write (x : W) : W := ((List.range (List.length (pI (names x)))).flatMap (fun i => (rowbits x i)))
theorem writeC {x : W → W} (hx : CPTs x) : CPTs (fun s => write (x s)) :=
  (flatC (natR_vlen (vecR_pI (namesC hx))) (rowbitsC (cpt_comp cpt_unpairB2 hx) (tqzI cpt_id)))

def vtx (x : W) : Nat := (runAt x 0)
theorem vtxC {x : W → W} (hx : CPTs x) : NatR (fun s => vtx (x s)) :=
  (natR_runAt hx (natR_const 0))

def expanded (x : W) : Nat := ((2 * (vtx x)) + 2)
theorem expandedC {x : W → W} (hx : CPTs x) : NatR (fun s => expanded (x s)) :=
  (natR_add (natR_mul (natR_const 2) (vtxC hx)) (natR_const 2))

def banned (x : Nat) (a : Nat) : Nat := (if (g (pI ((2 * x) + 2)) a) < (2 * x) then (if ((g (pI ((2 * x) + 2)) a) % 2) = 0 then (if (g (pJ ((2 * x) + 2)) a) = ((g (pI ((2 * x) + 2)) a) + 1) then 0 else 1) else 1) else 1)
theorem bannedC {x : W → Nat} {a : W → Nat} (hx : NatR x) (ha : NatR a) : NatR (fun s => banned (x s) (a s)) :=
  (tqnL (natR_get (vecR_pI (natR_add (natR_mul (natR_const 2) hx) (natR_const 2))) ha) (natR_mul (natR_const 2) hx) (tqnE (natR_mod (natR_get (vecR_pI (natR_add (natR_mul (natR_const 2) hx) (natR_const 2))) ha) (natR_const 2)) (natR_const 0) (tqnE (natR_get (vecR_pJ (natR_add (natR_mul (natR_const 2) hx) (natR_const 2))) ha) (natR_add (natR_get (vecR_pI (natR_add (natR_mul (natR_const 2) hx) (natR_const 2))) ha) (natR_const 1)) (natR_const 0) (natR_const 1)) (natR_const 1)) (natR_const 1))

def hardWord (x : Nat) (a : Nat) : W := (((List.range ((2 * x) + 2)).flatMap (fun j => (emit (if j = (g (pI ((2 * x) + 2)) a) then 1 else (if j = (g (pJ ((2 * x) + 2)) a) then 1 else 0))))) ++ ((List.range ((2 * x) + 2)).flatMap (fun j => [false])))
theorem hardWordC {x : W → Nat} {a : W → Nat} (hx : NatR x) (ha : NatR a) : CPTs (fun s => hardWord (x s) (a s)) :=
  (cpt_app2 (flatC (natR_add (natR_mul (natR_const 2) hx) (natR_const 2)) (emitC (tqnE (tqzI cpt_id) (natR_get (vecR_pI (natR_add (natR_mul (natR_const 2) (tqzN hx cpt_unpairB2)) (natR_const 2))) (tqzN ha cpt_unpairB2)) (natR_const 1) (tqnE (tqzI cpt_id) (natR_get (vecR_pJ (natR_add (natR_mul (natR_const 2) (tqzN hx cpt_unpairB2)) (natR_const 2))) (tqzN ha cpt_unpairB2)) (natR_const 1) (natR_const 0))))) (flatC (natR_add (natR_mul (natR_const 2) hx) (natR_const 2)) (cpt_const [false])))

def edgeBit (x : W) (a : Nat) : Nat := (bit x (((vtx x) + 1) + a))
theorem edgeBitC {x : W → W} {a : W → Nat} (hx : CPTs x) (ha : NatR a) : NatR (fun s => edgeBit (x s) (a s)) :=
  (natR_bit hx (natR_add (natR_add (vtxC hx) (natR_const 1)) ha))

def rewardWord (x : Nat) (a : Nat) : W := ((((List.range ((2 * x) + 2)).flatMap (fun j => (emit (if (j / 2) = (g (pI x) a) then 1 else (if (j / 2) = (g (pJ x) a) then 1 else 0))))) ++ ((List.range ((2 * x) + 2)).flatMap (fun j => [false]))) ++ [true])
theorem rewardWordC {x : W → Nat} {a : W → Nat} (hx : NatR x) (ha : NatR a) : CPTs (fun s => rewardWord (x s) (a s)) :=
  (cpt_app2 (cpt_app2 (flatC (natR_add (natR_mul (natR_const 2) hx) (natR_const 2)) (emitC (tqnE (natR_div (tqzI cpt_id) (natR_const 2)) (natR_get (vecR_pI (tqzN hx cpt_unpairB2)) (tqzN ha cpt_unpairB2)) (natR_const 1) (tqnE (natR_div (tqzI cpt_id) (natR_const 2)) (natR_get (vecR_pJ (tqzN hx cpt_unpairB2)) (tqzN ha cpt_unpairB2)) (natR_const 1) (natR_const 0))))) (flatC (natR_add (natR_mul (natR_const 2) hx) (natR_const 2)) (cpt_const [false]))) (cpt_const [true]))

def back (x : W) : W := ((((([false] ++ (headr (expanded x))) ++ (headr ((List.range (List.length (pI (expanded x)))).map (fun i => (banned (vtx x) i))).sum)) ++ ((List.range (List.length (pI (expanded x)))).flatMap (fun i => (if (banned (vtx x) i) = 0 then [] else (hardWord (vtx x) i))))) ++ (headr ((List.range (List.length (pI (vtx x)))).map (fun i => (edgeBit x i))).sum)) ++ ((List.range (List.length (pI (vtx x)))).flatMap (fun i => (if (edgeBit x i) = 0 then [] else (rewardWord (vtx x) i)))))
theorem backC {x : W → W} (hx : CPTs x) : CPTs (fun s => back (x s)) :=
  (cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 (cpt_const [false]) (headerC (expandedC hx))) (headerC (natR_sum (tqgN (natR_vlen (vecR_pI (expandedC hx))) (bannedC (vtxC (cpt_comp cpt_unpairB2 hx)) (tqzI cpt_id)))))) (flatC (natR_vlen (vecR_pI (expandedC hx))) (cpt_ite_eq (bannedC (vtxC (cpt_comp cpt_unpairB2 hx)) (tqzI cpt_id)) (natR_const 0) (cpt_const []) (hardWordC (vtxC (cpt_comp cpt_unpairB2 hx)) (tqzI cpt_id))))) (headerC (natR_sum (tqgN (natR_vlen (vecR_pI (vtxC hx))) (edgeBitC (cpt_comp cpt_unpairB2 hx) (tqzI cpt_id)))))) (flatC (natR_vlen (vecR_pI (vtxC hx))) (cpt_ite_eq (edgeBitC (cpt_comp cpt_unpairB2 hx) (tqzI cpt_id)) (natR_const 0) (cpt_const []) (rewardWordC (vtxC (cpt_comp cpt_unpairB2 hx)) (tqzI cpt_id)))))

end Enc
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Dec
open S Enc PT.Alg

def At (x : List Bool) (p : Nat) (w : List Bool) := ∃ t, x.drop p = w ++ t

lemma all_at (w : List Bool) : At w 0 w := ⟨[],by simp⟩
lemma split_at {x p u w} (h : At x p (u ++ w)) : At x p u ∧ At x (p+u.length) w := by
  obtain ⟨t,ht⟩ := h
  refine ⟨⟨w++t,by rw [ht,List.append_assoc]⟩,⟨t,?_⟩⟩
  rw [← List.drop_drop,ht,List.append_assoc,List.drop_left]

lemma at_prefix {x p u w} (h : At x p (u ++ w)) : At x p u := (split_at h).1
lemma at_suffix {x p u w} (h : At x p (u ++ w)) : At x (p+u.length) w := (split_at h).2
lemma at_header {x p n} (h : At x p (headr n)) : runAt x p = n := by
  obtain ⟨t,ht⟩ := h
  change ((x.drop p).takeWhile id).length = n
  rw [ht]
  simpa only [runAt,List.drop_zero,headr,List.append_assoc,List.singleton_append] using dec_run0 n t
lemma at_bit {x p w} (h : At x p w) (i : Nat) (hi : i < w.length) : bit x (p+i) = bit w i := by
  obtain ⟨t,ht⟩ := h
  have t0 : bit (x.drop p) i = bit x (p+i) := by simp [bit,List.getElem?_drop]
  rw [← t0, ht,dec_bitB _ _ _ hi]

lemma flat_len {A B : Type} (l : List A) (f : A → List B) (m : Nat) (hm : ∀ a, (f a).length = m) :
    (l.flatMap f).length = l.length*m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [hm,ih,Nat.succ_mul,Nat.add_comm]

lemma flat_at {A : Type} (l : List A) (f : A → List Bool) (m : Nat) (hm : ∀ a, (f a).length=m)
    {x p} (h : At x p (l.flatMap f)) (r : Nat) (hr : r < l.length) : At x (p+r*m) (f l[r]) := by
  induction l generalizing p r with
  | nil => simp at hr
  | cons a l ih =>
    obtain ⟨ha,hb⟩ := split_at (show At x p (f a ++ l.flatMap f) from by simpa using h)
    cases r with
    | zero => simpa using ha
    | succ r =>
      rw [hm] at hb
      simpa only [Nat.succ_mul,List.getElem_cons_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih hb r (by simpa using hr)

def banks {k c} (z : Obs k c) := List.ofFn z.1 ++ List.ofFn z.2
def sb {k c} (z : Obs k c × Bool) := banks z.1 ++ [z.2]
def pack {k c} (h : List (Obs k c)) (s : List (Obs k c × Bool)) :=
  [c] ++ (headr k ++ (headr h.length ++ (h.flatMap banks ++ (headr s.length ++ s.flatMap sb))))

lemma bank_len {k c} (z : Obs k c) : (banks z).length = nr k c + nc k c := by simp [banks]
lemma sb_len {k c} (z : Obs k c × Bool) : (sb z).length = nr k c + nc k c+1 := by simp [sb,bank_len]
lemma header_len (n : Nat) : (headr n).length = n+1 := by simp [headr]

lemma parsed {k c} (h : List (Obs k c)) (s : List (Obs k c × Bool)) :
    let x := pack h s
    names x = k ∧ flag x = c.toNat ∧ nrows x = nr k c ∧ spanW x = nr k c + nc k c ∧
    hardN x = h.length ∧ softN x = s.length ∧ At x (hardAt x) (h.flatMap banks) ∧ At x (softAt x) (s.flatMap sb) := by
  intro x
  have hall := all_at x
  change At x 0 ([c] ++ (headr k ++ (headr h.length ++ (h.flatMap banks ++ (headr s.length ++ s.flatMap sb))))) at hall
  obtain ⟨hc,rest⟩ := split_at hall
  change At x 1 _ at rest
  obtain ⟨hk,rest⟩ := split_at rest
  have kn : names x = k := at_header hk
  have fl : flag x = c.toNat := by
    change bit x (0+0) = c.toNat
    rw [at_bit hc 0 (by simp)]; cases c <;> rfl
  have rn : nrows x = nr k c := by rw [nrows,kn,fl]; cases c <;> simp [nr]
  have sp : spanW x = nr k c + nc k c := by rw [spanW,kn,fl,rn]; cases c <;> simp [nc,Nat.add_assoc]
  rw [header_len] at rest
  obtain ⟨hh,rest⟩ := split_at rest
  have hn : hardN x = h.length := by rw [hardN,kn,show k+2=1+(k+1) by omega]; exact at_header hh
  rw [header_len] at rest
  have atH : hardAt x = 1+(k+1)+(h.length+1) := by rw [hardAt,kn,hn]; omega
  rw [← atH] at rest
  obtain ⟨hd,rest⟩ := split_at rest
  have mark : softMark x = hardAt x + (h.flatMap banks).length := by
    rw [softMark,hn,sp,flat_len h banks _ bank_len,Nat.mul_comm]
  rw [← mark] at rest
  obtain ⟨hs,sd⟩ := split_at rest
  have sn : softN x = s.length := at_header hs
  rw [header_len] at sd
  exact ⟨kn,fl,rn,sp,hn,sn,hd,by simpa only [softAt,sn,Nat.add_assoc] using sd⟩

lemma bit_ofFn {n : Nat} (x : Fin n → Bool) (i : Fin n) : bit (List.ofFn x) i.val = (x i).toNat := by
  simp [bit,List.getD_eq_getElem?_getD,i.isLt,Bool.toNat]

lemma extract {k c} {x p} {z : Obs k c} (hz : At x p (banks z)) :
    (∀ i : Fin (nr k c), bit x (p+i.val) = (z.1 i).toNat) ∧
    (∀ i : Fin (nc k c), bit x (p+nr k c+i.val) = (z.2 i).toNat) := by
  obtain ⟨l,r⟩ := split_at (show At x p (List.ofFn z.1 ++ List.ofFn z.2) from hz)
  rw [List.length_ofFn] at r
  exact ⟨fun i => (at_bit l _ (by simpa using i.isLt)).trans (bit_ofFn _ i),
    fun i => (at_bit r _ (by simpa using i.isLt)).trans (bit_ofFn _ i)⟩

end Dec
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Dec
open S Enc PT.Alg
variable {k : Nat} {c : Bool}

lemma sumZero (n : Nat) (f : Nat → Nat) : ((List.range n).map f).sum = 0 ↔ ∀ i<n, f i = 0 := by
  simp [List.sum_eq_zero_iff_forall_eq_nat,List.forall_mem_map]
lemma zbit (b : Bool) : b.toNat = 0 ↔ ¬ b=true := by cases b <;> decide +kernel
lemma eb {a b : Nat} : a * b = 0 ↔ a = 0 ∨ b = 0 := Nat.mul_eq_zero

lemma readL {x p z} (hz : At x p (banks (k:=k) (c:=c) z)) (i : Fin k) :
    bit x (p+i.val) = (z.1 (i.castLE (hnr k c))).toNat := (extract hz).1 (i.castLE (hnr k c))
lemma readR {x p z} (hz : At x p (banks (k:=k) (c:=c) z)) (i : Fin k) :
    bit x (p+nr k c+i.val) = (z.2 (i.castLE (hnc k c))).toNat := (extract hz).2 (i.castLE (hnc k c))
lemma forced_zero {x p z} (hz : At x p (banks (k:=k) (c:=c) z)) (kn : names x = k) (rn : nrows x = nr k c)
    (fl : flag x = c.toNat) : forced x p = 0 ↔ ¬fixed z := by
  have d : flag x * bit x (p+k+1) = 0 ↔ ¬(c=true ∧ (banks z).getD (k+1) false = true) := by
    rw [fl]
    cases c with
    | false => simp
    | true =>
      have lt : k+1 < (banks z).length := by simp [bank_len,nr,nc]
      rw [Nat.add_assoc,at_bit hz _ lt]
      simp [bit]
  rw [forced,kn,rn,Nat.add_eq_zero_iff,d,sumZero]
  unfold fixed
  rw [not_or]
  apply and_congr_right
  intro _
  constructor
  · intro h ⟨i,h1,h2⟩
    have a := h i.val i.isLt
    rw [readL hz i,readR hz i,h1,h2] at a
    contradiction
  · intro h i hi
    let j : Fin k := ⟨i,hi⟩
    change bit x (p+j.val) * bit x (p+nr k c+j.val) = 0
    rw [readL hz j,readR hz j,eb,zbit,zbit]
    exact not_and_or.mp (fun ex => h ⟨j,ex⟩)

lemma touch_zero {x p z} (hz : At x p (banks (k:=k) (c:=c) z)) (kn : names x = k) (rn : nrows x = nr k c)
    {i : Nat} (hi : i < (pairsF k).length) : touch x p i = 0 ↔ ¬ touches z (pairsF k)[i] := by
  have ei := pairsF_get k i hi
  rw [touch,kn,rn,← ei.1,← ei.2]
  simp only [readL hz,readR hz,Nat.add_eq_zero_iff,eb,zbit,touches,not_or,not_and_or]

lemma good_bit (h : List (Obs k c)) (s : List (Obs k c × Bool)) {i : Nat} (hi : i < (pairsF k).length) :
    allow (pack h s) i ≠ 0 ↔ (pairsF k)[i] ∈ allowed h := by
  classical
  let x := pack h s
  obtain ⟨kn,fl,rn,sp,hn,sn,ah,as⟩ := parsed h s
  change allow x i ≠ 0 ↔ _
  rw [allow,(by decide +kernel : (1:Nat) ≠ 0).ite_ne_right_iff,hn,sumZero]
  have ve : (pairsF k)[i] ∈ V k := List.mem_toFinset.mpr (List.getElem_mem hi)
  simp only [allowed,Finset.mem_filter,ve,true_and]
  have prop (j : Nat) (hj : j < h.length) : forced x (hardAt x+j*spanW x) + touch x (hardAt x+j*spanW x) i = 0 ↔
      ¬fixed h[j] ∧ ¬touches h[j] (pairsF k)[i] := by
    have atz := flat_at h banks _ bank_len ah j hj
    rw [sp,Nat.add_eq_zero_iff,forced_zero atz kn rn fl,touch_zero atz kn rn hi]
  constructor
  · intro q
    have both : ∀ z ∈ h, ¬fixed z ∧ ¬touches z (pairsF k)[i] := by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hz
      exact (prop j hj).mp (q j hj)
    exact ⟨fun z hz => (both z hz).1,fun z hz => (both z hz).2⟩
  · rintro ⟨u,v⟩ j hj
    exact (prop j hj).mpr ⟨u _ (List.getElem_mem hj),v _ (List.getElem_mem hj)⟩

lemma flatmask {α : Type*} (L : List α) (f : Nat → Nat) (q : α → Bool)
    (spec : ∀ i (hi : i < L.length), decide (f i ≠ 0) = q L[i]) :
    (List.range L.length).flatMap (fun i => emit (f i)) = L.map q := by
  unfold emit
  exact (mn_rfm L _ (fun a => [q a]) (fun i hi => congrArg (fun b => [b]) (spec i hi))).trans List.map_eq_flatMap.symm

lemma softword_ok (h : List (Obs k c)) (s : List (Obs k c × Bool)) (r : Nat) (hr : r < s.length) :
    let x := pack h s
    softWord x (softAt x + r*(spanW x+1)) = label s[r] :: maskF (mask s[r].1) := by
  classical
  intro x
  obtain ⟨kn,fl,rn,sp,hn,sn,ah,as⟩ := parsed h s
  change spanW x = nr k c + nc k c at sp
  let t := s[r]
  let p := softAt x + r*(spanW x+1)
  have hs : At x p (sb t) := by simpa only [p,sp,t] using flat_at s sb _ sb_len as r hr
  obtain ⟨hz,ht⟩ := split_at (show At x p (banks t.1 ++ [t.2]) from hs)
  have fv := forced_zero hz kn rn fl
  have bt : bit x (p + spanW x) = t.2.toNat := by
    rw [bank_len,←sp] at ht
    have w := at_bit ht 0 (by simp)
    rw [Nat.add_zero] at w
    rw [w]; cases t.2 <;> rfl
  change softWord x p = label t :: maskF (mask t.1)
  rw [softWord,bt,fl,kn,pI_length]
  have head : (if forced x p = 0 then (if t.2.toNat = c.toNat then 0 else 1) else (if t.2.toNat = c.toNat then 1 else 0)) ≠ 0 ↔ label t = true := by
    have x0 : ∀ a b : Bool, (if a.toNat=b.toNat then 0 else 1) ≠ (0:Nat) ↔ decide (a≠b)=true := by decide +kernel
    have x1 : ∀ a b : Bool, (if a.toNat=b.toNat then 1 else 0) ≠ (0:Nat) ↔ decide (a=b)=true := by decide +kernel
    by_cases fr : fixed t.1
    · have hnot : forced x p ≠ 0 := fun q => fv.mp q fr
      simpa only [ite_eq_right hnot,label,ite_eq_left fr] using x1 t.2 c
    · simpa only [ite_eq_left (fv.mpr fr),label,ite_eq_right fr] using x0 t.2 c
  change decide _ :: _ = _ :: _
  congr 1
  · exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans head)
  · apply flatmask
    intro i hi
    have v : (pairsF k)[i] ∈ V k := List.mem_toFinset.mpr (List.getElem_mem hi)
    apply decide_eq_decide.mpr
    simp only [mask,Finset.mem_filter,v,true_and, fv]
    by_cases fr : fixed t.1 <;> simp [fr,touch_zero hz kn rn hi]

lemma query_ok (h : List (Obs k c)) (s : List (Obs k c × Bool)) (a b : Nat)
    (ha : a < (pairsF k).length) (hb : b < (pairsF k).length) :
    query (pack h s) a b = inputF k (allowed h) {(pairsF k)[a],(pairsF k)[b]} (normRows s) := by
  classical
  obtain ⟨kn,fl,rn,sp,hn,sn,ah,as⟩ := parsed h s
  unfold query inputF
  rw [kn,pI_length,sn]
  simp only [headr,normRows,List.length_map,List.flatMap_map]
  congr 1
  · congr 1
    congr 1
    · congr 1
      exact flatmask (pairsF k) _ _ (fun i hi => decide_eq_decide.mpr (good_bit h s hi))
    · apply flatmask
      intro i hi
      have neq (j : Nat) (hj : j < (pairsF k).length) : (pairsF k)[i] = (pairsF k)[j] ↔ i=j := by
        constructor
        · intro e; simpa only [mn_ixg hi,mn_ixg hj] using congrArg mn_ix e
        · rintro rfl; rfl
      by_cases ia : i=a <;> by_cases ib : i=b <;> simp [ia,ib,neq _ ha,neq _ hb]
  · apply mn_rfm
    exact softword_ok h s

end Dec
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Dec
open S Enc PT.Alg
variable {k : Nat}

lemma val_iff {D Q : Finset (E k)} (hd : D ⊆ V k) : mn_val D Q ↔ Q ⊆ D ∧ Valid Q := by
  constructor
  · rintro ⟨sub,dis⟩
    have v := sub.trans hd
    refine ⟨sub,v,?_,?_⟩
    · rintro key hm
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hm
      simp [Circ.ends,(ord.mp (v he)).ne]
    · rintro A hA B hB ne
      obtain ⟨a,ma,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨b,mb,rfl⟩ := Finset.mem_image.mp hB
      exact dis a ma b mb (fun h => ne (congrArg Circ.ends h))
  · rintro ⟨sub,v,valid⟩
    refine ⟨sub,fun a ma b mb ne => valid.2 _ (Finset.mem_image_of_mem _ ma) _ (Finset.mem_image_of_mem _ mb) ?_⟩
    exact fun eq => ne (Circ.ends_injective a b (ord.mp (v ma)) (ord.mp (v mb)) eq)

lemma overlap_iff (a b : Nat) (ha : a < (pairsF k).length) (hb : b < (pairsF k).length) :
    overlap k a b = 0 ↔ Disjoint (Circ.ends (pairsF k)[a]) (Circ.ends (pairsF k)[b]) := by
  rw [overlap,←(pairsF_get k a ha).1,←(pairsF_get k b hb).1,←(pairsF_get k a ha).2,←(pairsF_get k b hb).2]
  simp [Circ.ends,Finset.disjoint_left,Fin.val_eq_val] <;> grind

lemma pair_val {D : Finset (E k)} {a b : E k} (ha : a ∈ D) (hb : b ∈ D) (dis : Disjoint (Circ.ends a) (Circ.ends b)) :
    mn_val D {a,b} := by
  refine ⟨?_,?_⟩
  · exact Finset.insert_subset_iff.mpr ⟨ha,Finset.singleton_subset_iff.mpr hb⟩
  · intro i hi j hj ne
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> first | exact dis | exact dis.symm | contradiction

lemma rel_witness {D : Finset (E k)} (hd : D ⊆ V k) (rows : List (Finset (E k) × Bool)) {e f : E k}
    (ef : e ≠ f) : rel D rows e f ↔ ∃ Q, mn_good D {e,f} rows Q := by
  constructor
  · rintro ⟨_,Q,he,hf,sub,valid,nz⟩
    exact ⟨Q,Finset.insert_subset_iff.mpr ⟨he,Finset.singleton_subset_iff.mpr hf⟩,(val_iff hd).mpr ⟨sub,valid⟩,nz⟩
  · rintro ⟨Q,sub,val,nz⟩
    obtain ⟨hQ,v⟩ := (val_iff hd).mp val
    exact ⟨ef,Q,sub (by simp),sub (by simp),hQ,v,nz⟩

lemma rel_necessary {D : Finset (E k)} (hd : D ⊆ V k) {rows : List (Finset (E k) × Bool)} {e f : E k}
    (h : rel D rows e f) : e ∈ D ∧ f ∈ D ∧ Disjoint (Circ.ends e) (Circ.ends f) := by
  obtain ⟨ef,Q,he,hf,sub,valid,_⟩ := h
  exact ⟨sub he,sub hf,((val_iff hd).mpr ⟨sub,valid⟩).2 e he f hf ef⟩

lemma solver_bit {D : Finset (E k)} (hd : D ⊆ V k) {P : Finset (E k)} (hp : mn_val D P) (rows : List (Finset (E k) × Bool)) :
    bit (solveV (inputF k D P rows)) 0 ≠ 0 ↔ ∃ Q, mn_good D P rows Q := by
  obtain ⟨_,neg,pos⟩ := solveV_spec k D P rows (fun e he => ord.mp (hd he)) hp
  by_cases hx : ∃ Q, mn_good D P rows Q
  · obtain ⟨Q,_,_,_,out⟩ := pos hx
    change solveV (inputF k D P rows) = _ at out
    rw [out]
    exact ⟨fun _ => hx,fun _ => by simp [bit]⟩
  · have key := neg.mpr hx
    change solveV (inputF k D P rows) = [false] at key
    rw [key]; simp [bit,hx]

end Dec
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Dec
open S Enc PT.Alg
variable {k : Nat} {c : Bool}

lemma adj_correct (h : List (Obs k c)) (s : List (Obs k c × Bool)) (a b : Nat)
    (ha : a < (pairsF k).length) (hb : b < (pairsF k).length) : adjbit (pack h s) a b ≠ 0 ↔
    rel (allowed h) (normRows s) (pairsF k)[a] (pairsF k)[b] := by
  classical
  let x := pack h s
  let e := (pairsF k)[a]
  let f := (pairsF k)[b]
  let D := allowed h
  have hd : D ⊆ V k := Finset.filter_subset _ _
  have necessary := @rel_necessary k D hd (normRows s) e f
  have kn := (parsed h s).1
  change adjbit x a b ≠ 0 ↔ rel D (normRows s) e f
  rw [adjbit,kn]
  by_cases ea : e ∈ D
  · by_cases fb : f ∈ D
    · have h1 := (good_bit h s ha).mpr ea
      have h2 := (good_bit h s hb).mpr fb
      rw [ite_eq_right (Nat.mul_ne_zero h1 h2)]
      by_cases ds : Disjoint (Circ.ends e) (Circ.ends f)
      · rw [ite_eq_left ((overlap_iff a b ha hb).mpr ds),query_ok h s a b ha hb,solver_bit hd (pair_val ea fb ds)]
        have ne : e ≠ f := by
          intro eq
          have both : e.1 ∈ Circ.ends e := Finset.mem_insert_self _ _
          exact (Finset.disjoint_left.mp ds) both (eq ▸ both)
        exact (rel_witness hd _ ne).symm
      · have nz := mt (overlap_iff a b ha hb).mp ds
        rw [ite_eq_right nz]
        exact iff_of_false (by simp) (fun w => ds (necessary w).2.2)
    · have zero := not_not.mp (mt (good_bit h s hb).mp fb)
      rw [zero,Nat.mul_zero,ite_eq_left rfl]
      exact iff_of_false (by simp) (fun w => fb (necessary w).2.1)
  · have zero := not_not.mp (mt (good_bit h s ha).mp ea)
    rw [zero,Nat.zero_mul,ite_eq_left rfl]
    exact iff_of_false (by simp) (fun w => ea (necessary w).1)

noncomputable def graph (h : List (Obs k c)) (s : List (Obs k c × Bool)) (e f : E k) : Bool := by
  classical
  exact decide (rel (allowed h) (normRows s) e f)

lemma write_pack (h : List (Obs k c)) (s : List (Obs k c × Bool)) :
    Enc.write (pack h s) = (Vlist k).flatMap (fun e => (Vlist k).map (graph h s e)) := by
  classical
  have kn := (parsed h s).1
  rw [Enc.write,kn,pI_length]
  apply mn_rfm (pairsF k)
  intro i hi
  rw [rowbits,kn,pI_length]
  apply flatmask (pairsF k)
  intro j hj
  exact decide_eq_decide.mpr (adj_correct h s i j hi hj)

lemma graph_props (hk : 2 ≤ k) (hc : c = true → 7 ≤ k) (h : List (Obs k c)) (s : List (Obs k c × Bool)) :
    (∀ e ∈ V k, ∀ f ∈ V k, graph h s e f = true ↔ e≠f ∧ ∃ T, e ∈ T ∧ f ∈ T ∧ CubeActive (fits h) (probe k c) (scoreP s) T) ∧
    ∀ I ⊆ V k, Strong (fits h) (probe k c) (scoreP s) I ↔ ∀ e ∈ V k, ∀ f ∈ V k, graph h s e f = true → e ∈ I ∨ f ∈ I := by
  classical
  let g := Sig.score (normRows s)
  have hd : Down (PF h) := fits_down hk hc h
  have tracks (f : Fn k c) (hf : fits h f) : scoreP s f = g (probe k c f) := tracks_score hk hc s hf.1
  have ge (e f : E k) : graph h s e f = true ↔ Edge (PF h) g e f :=
    decide_eq_true_iff.trans (rel_edge hk hc h _ e f)
  constructor
  · intro e _ f _
    simp only [ge,Edge,active_iff _ _ _ hd g tracks,PF]
  · intro I _
    rw [strong_iff_affine _ _ _ g tracks,affine_iff_covers hd]
    simp only [ge]
    constructor
    · intro H e _ f _; exact H e f
    · intro H e f hef
      have ef' := hef
      obtain ⟨_,Q,he,hf,⟨F,_,p⟩,_⟩ := ef'
      have sub : Q ⊆ V k := p ▸ (Finset.filter_subset _ _ : probe k c F ⊆ V k)
      exact H e (sub he) f (sub hf) hef

end Dec
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Rev
open S Enc Dec PT.Alg

abbrev D (v : Nat) := 2*v+2
abbrev blk {v : Nat} (e : E (D v)) (i : Fin v) := e.1.val = 2*i.val ∧ e.2.val=2*i.val+1
def ban (v : Nat) := (pairsF (D v)).filter (fun e => decide (¬∃ i : Fin v, blk e i))
def edges {v : Nat} (H : Fin v → Fin v → Bool) := (pairsF v).filter (fun z => H z.1 z.2)
def banObs {v : Nat} (e : E (D v)) : Obs (D v) false :=
  (fun i => decide (i.val=e.1.val ∨ i.val=e.2.val),fun _ => false)
def edgeObs {v : Nat} (z : E v) : Obs (D v) false × Bool :=
  ((fun i => decide (i.val/2=z.1.val ∨ i.val/2=z.2.val),fun _ => false),true)
def hard (v : Nat) := (ban v).map banObs
def soft {v : Nat} (H : Fin v → Fin v → Bool) := (edges H).map edgeObs
def source {v : Nat} (H : Fin v → Fin v → Bool) := headr v ++ (pairsF v).map (fun e => H e.1 e.2)

lemma vtx_src {v} (H : Fin v → Fin v → Bool) : vtx (source H) = v := by
  simpa only [vtx,source,headr,List.append_assoc,List.singleton_append] using dec_run0 v ((pairsF v).map fun e => H e.1 e.2)
lemma edge_src {v} (H : Fin v → Fin v → Bool) (a : Nat) (ha : a < (pairsF v).length) :
    edgeBit (source H) a = (H (pairsF v)[a].1 (pairsF v)[a].2).toNat := by
  rw [edgeBit,vtx_src,source,← header_len v,dec_bitA]
  simp [bit,ha,Bool.toNat]
lemma block_arith (x y v : Nat) :
    (if x < 2*v then (if x%2=0 then (if y=x+1 then 0 else 1) else 1) else 1) =
    (if ∃ i : Fin v, x=2*i.val ∧ y=2*i.val+1 then (0 : Nat) else 1) := by
  have p : (∃ i : Fin v, x=2*i.val ∧ y=2*i.val+1) ↔ x<2*v ∧ x%2=0 ∧ y=x+1 := by
    constructor
    · rintro ⟨i,a,b⟩; have bound := i.isLt; omega
    · rintro ⟨a,b,c⟩; exact ⟨⟨x/2,by omega⟩,by dsimp;omega,by dsimp;omega⟩
  simp only [p]; split_ifs <;> omega
lemma ban_value (v a : Nat) (ha : a < (pairsF (D v)).length) :
    banned v a = if ∃ i : Fin v, blk (pairsF (D v))[a] i then 0 else 1 := by
  rw [banned,←(pairsF_get _ _ ha).1,←(pairsF_get _ _ ha).2]
  exact block_arith _ _ _
lemma flat_const (k : Nat) : (List.range k).flatMap (fun _ => [false]) = List.replicate k false := by
  rw [←List.map_eq_flatMap]; simp
lemma flat_fn (k : Nat) (n : Nat → Nat) (f : Fin k → Bool) (h : ∀ i : Fin k, decide (n i.val ≠ 0) = f i) :
    (List.range k).flatMap (fun j => emit (n j)) = List.ofFn f := by
  rw [List.ofFn_eq_map]
  have law (i : Nat) (hi : i < (List.finRange k).length) : decide (n i ≠ 0) = f (List.finRange k)[i] := by
    have bound : i < k := by simpa using hi
    calc
      _ = f ⟨i,bound⟩ := h ⟨i,bound⟩
      _ = _ := congrArg f (Fin.ext (by simp [List.getElem_finRange]))
  simpa only [List.length_finRange] using flatmask (List.finRange k) n f law
lemma hw (v a : Nat) (ha : a < (pairsF (D v)).length) :
    hardWord v a = banks (banObs (pairsF (D v))[a]) := by
  rw [hardWord,flat_const,←(pairsF_get _ _ ha).1,←(pairsF_get _ _ ha).2]
  unfold banks banObs
  simp only [List.ofFn_const]
  congr 1
  apply flat_fn (D v)
  intro j
  split_ifs <;> simp_all
lemma ew {v} (a : Nat) (ha : a < (pairsF v).length) :
    rewardWord v a = sb (edgeObs (pairsF v)[a]) := by
  rw [rewardWord,flat_const,←(pairsF_get _ _ ha).1,←(pairsF_get _ _ ha).2]
  unfold sb banks edgeObs
  simp only [List.ofFn_const]
  congr 2
  apply flat_fn (D v)
  intro j
  split_ifs <;> simp_all

lemma select_flat {α β : Type*} (L : List α) (p : α → Bool) (f : α → List β) :
    L.flatMap (fun a => if p a then f a else []) = (L.filter p).flatMap f := by
  induction L with
  | nil => simp
  | cons a l ih => cases ha : p a <;> simp [ha,ih]

lemma back_pack {v} (H : Fin v → Fin v → Bool) : back (source H) = pack (hard v) (soft H) := by
  have kg := vtx_src H
  have tab (i : Nat) (hi : i < (pairsF (D v)).length) : banned v i = if decide (¬ ∃ j : Fin v, blk (pairsF (D v))[i] j) then 1 else 0 := by
    rw [ban_value v i hi]
    by_cases ex : ∃ j : Fin v, blk (pairsF (D v))[i] j <;> simp [ex]
  have nb : ((List.range (pairsF (D v)).length).map (banned v)).sum = (ban v).length := by
    rw [mn_rm (pairsF (D v)) _ (fun e => if decide (¬∃ i : Fin v, blk e i) then 1 else 0) tab,mn_cnt]; rfl
  have ns : ((List.range (pairsF v).length).map (edgeBit (source H))).sum = (edges H).length := by
    rw [mn_rm (pairsF v) _ (fun e => if H e.1 e.2 then 1 else 0) (by intro i hi; rw [edge_src _ _ hi]; cases H _ _ <;> rfl),mn_cnt]; rfl
  have bh : (List.range (pairsF (D v)).length).flatMap (fun i => if banned v i = 0 then [] else hardWord v i) = (ban v).flatMap (fun e => banks (banObs e)) := by
    rw [mn_rfm (pairsF (D v)) _ (fun e => if decide (¬∃ j : Fin v, blk e j) then banks (banObs e) else []) (by
      intro i hi; rw [tab i hi,hw v i hi]; cases decide (¬∃ j : Fin v, blk (pairsF (D v))[i] j) <;> rfl),select_flat]; rfl
  have bs : (List.range (pairsF v).length).flatMap (fun i => if edgeBit (source H) i = 0 then [] else rewardWord v i) = (edges H).flatMap (fun e => sb (edgeObs e)) := by
    rw [mn_rfm (pairsF v) _ (fun e => if H e.1 e.2 then sb (edgeObs e) else []) (by intro i hi; rw [edge_src _ _ hi,ew _ hi]; cases H _ _ <;> rfl),select_flat]; rfl
  simp only [back,expanded,kg,pI_length,nb,ns,bh,bs,pack,hard,soft,List.length_map,List.flatMap_map,List.append_assoc,Function.comp_def,D] at *

end Rev
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Rev
open S Dec PT.Alg

variable {v : Nat}
lemma ban_fresh (a : E (D v)) : ¬fixed (banObs a) := by simp [fixed,banObs]
lemma edge_fresh (z : E v) : ¬fixed (edgeObs z).1 := by simp [fixed,edgeObs]
lemma touch_ban {a e : E (D v)} (ha : a ∈ V (D v)) (he : e ∈ V (D v)) :
    touches (banObs a) e ↔ e=a := by
  have la := Fin.lt_def.mp (ord.mp ha)
  have le := Fin.lt_def.mp (ord.mp he)
  simp only [touches,banObs,Fin.coe_castLE,decide_eq_true_eq,Bool.false_eq_true,false_and,or_false]
  constructor
  · rintro ⟨hl,hr⟩; apply Prod.ext <;> apply Fin.ext <;> omega
  · rintro rfl; simp
lemma allowed_block {e : E (D v)} (he : e ∈ V (D v)) : e ∈ allowed (hard v) ↔ ∃ i : Fin v, blk e i := by
  classical
  have ready : possible (hard v) := by
    rintro z hz; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz; exact ban_fresh a
  simp only [allowed,Finset.mem_filter,he,true_and]
  rw [and_iff_right ready]
  simp only [hard,List.forall_mem_map]
  constructor
  · intro hn; by_contra hb
    have hb' : e ∈ ban v := List.mem_filter.mpr ⟨List.mem_toFinset.mp he,decide_eq_true hb⟩
    exact hn e hb' ((touch_ban he he).mpr rfl)
  · rintro ex a ha t
    obtain ⟨ha',n⟩ := List.mem_filter.mp ha
    obtain rfl := (touch_ban (List.mem_toFinset.mpr ha') he).mp t
    exact (of_decide_eq_true n) ex
lemma touch_edge {e : E (D v)} {i : Fin v} (hi : blk e i) (z : E v) :
    touches (edgeObs z).1 e ↔ i=z.1 ∨ i=z.2 := by
  obtain ⟨h0,h1⟩ := hi
  have a : e.1.val / 2 = i.val := by omega
  have b : e.2.val / 2 = i.val := by omega
  simp [touches,edgeObs,a,b,Fin.val_eq_val]
lemma block_ne {e f : E (D v)} {i j : Fin v} (he : blk e i) (hf : blk f j) (ne : e≠f) : i≠j := by
  rintro rfl; exact ne (Prod.ext (Fin.ext (he.1.trans hf.1.symm)) (Fin.ext (he.2.trans hf.2.symm)))
lemma block_disj {e f : E (D v)} {i j : Fin v} (he : blk e i) (hf : blk f j) (ne : i≠j) :
    Disjoint (Circ.ends e) (Circ.ends f) := by
  obtain ⟨a,b⟩ := he; obtain ⟨c,d⟩ := hf
  have z : i.val ≠ j.val := fun q => ne (Fin.ext q)
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Circ.ends,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with eq|eq <;> have := congrArg Fin.val eq <;> omega
lemma signed_positive {E : Type*} [DecidableEq E] (rows : List (Finset E × Bool)) (Q : Finset E)
    (pos : ∀ t ∈ rows, t.2=true) : Sig.signed rows Q ≠ 0 ↔ ∃ t ∈ rows, Q ⊆ t.1 := by
  classical
  have nilneg : rows.filter (fun t => !t.2 && decide (Q ⊆ t.1)) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro t ht; simp [pos t ht]
  simp only [Sig.signed,nilneg,List.length_nil,Nat.cast_zero,sub_zero,ne_eq,Nat.cast_eq_zero,List.length_eq_zero_iff]
  constructor
  · intro hn
    obtain ⟨t,ht⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨ht,hh⟩ := List.mem_filter.mp ht
    exact ⟨t,ht,of_decide_eq_true (Bool.and_eq_true_iff.mp hh).2⟩
  · rintro ⟨t,ht,hq⟩ empty
    have hm : t ∈ rows.filter (fun t => t.2 && decide (Q ⊆ t.1)) := List.mem_filter.mpr ⟨ht,by simp [pos t ht,hq]⟩
    simp [empty] at hm

lemma reverse_graph (H : Fin v → Fin v → Bool) {e f : E (D v)} (he : e ∈ V (D v)) (hf : f ∈ V (D v)) :
    graph (hard v) (soft H) e f = decide (∃ i j : Fin v, blk e i ∧ blk f j ∧ i≠j ∧ H (min i j) (max i j) = true) := by
  classical
  have lookup {Q : Finset (E (D v))} : Sig.signed (normRows (soft H)) Q ≠ 0 ↔
      ∃ z ∈ edges H, Q ⊆ mask (edgeObs z).1 := by
    have on (z : E v) : label (edgeObs z) = true := by
      classical
      rw [label,ite_eq_right (edge_fresh z)]; rfl
    have ls : normRows (soft H) = (edges H).map (fun z => (mask (edgeObs z).1,true)) := by
      simp only [normRows,soft,List.map_map,Function.comp_def,on]
    rw [ls,signed_positive _ _ (by simp)]
    simp
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨ne,Q,eq,fq,sub,_,nz⟩
    obtain ⟨i,bi⟩ := (allowed_block he).mp (sub eq)
    obtain ⟨j,bj⟩ := (allowed_block hf).mp (sub fq)
    have ij := block_ne bi bj ne
    obtain ⟨z,hz,qs⟩ := lookup.mp nz
    obtain ⟨zm,hH⟩ := List.mem_filter.mp hz
    have zo := (mem_pairsF v z).mp zm
    have t1 := (touch_edge bi z).mp (Finset.mem_filter.mp (qs eq)).2.2
    have t2 := (touch_edge bj z).mp (Finset.mem_filter.mp (qs fq)).2.2
    refine ⟨i,j,bi,bj,ij,?_⟩
    rcases t1 with rfl|rfl <;> rcases t2 with rfl|rfl <;>
      first | contradiction | simpa only [min_eq_left zo.le,max_eq_right zo.le,min_eq_right zo.le,max_eq_left zo.le] using hH
  · rintro ⟨i,j,bi,bj,ij,hH⟩
    let z := (min i j,max i j)
    have zij : z.1 < z.2 := by
      rcases lt_or_gt_of_ne ij with hi|hi
      · simpa only [z,min_eq_left hi.le,max_eq_right hi.le] using hi
      · simpa only [z,min_eq_right hi.le,max_eq_left hi.le] using hi
    have hm : z ∈ edges H := List.mem_filter.mpr ⟨(mem_pairsF _ _).mpr zij,hH⟩
    have di := block_disj bi bj ij
    have ne : e≠f := by intro eq; have a := bi.1; rw [eq] at a; exact ij (Fin.ext (by have d := bj.1; omega))
    have a1 := (allowed_block he).mpr ⟨i,bi⟩
    have a2 := (allowed_block hf).mpr ⟨j,bj⟩
    obtain ⟨sub,valid⟩ := (val_iff (Finset.filter_subset _ _ : allowed (hard v) ⊆ V (D v))).mp (pair_val a1 a2 di)
    refine ⟨ne,{e,f},by simp,by simp,sub,valid,lookup.mpr ⟨z,hm,?_⟩⟩
    have both : (i=z.1 ∨ i=z.2) ∧ (j=z.1 ∨ j=z.2) := by
      rcases le_total i j with hi|hi
      · simp [z,min_eq_left hi,max_eq_right hi]
      · simp [z,min_eq_right hi,max_eq_left hi]
    exact Finset.insert_subset_iff.mpr ⟨Finset.mem_filter.mpr ⟨he,edge_fresh z,(touch_edge bi z).mpr both.1⟩,
      Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hf,edge_fresh z,(touch_edge bj z).mpr both.2⟩)⟩

end Rev
end PEqualNP.Outside.L_meta_33641

namespace PEqualNP.Outside.L_meta_33641
namespace Rev
open S Enc Dec PT.Alg

lemma banTape {v : Nat} (e : E (D v)) : banks (banObs e) =
    (List.finRange (D v)).map (fun i => decide (i=e.1 ∨ i=e.2)) ++ List.replicate (D v) false := by
  change List.ofFn (fun i : Fin (D v) => decide (i.val=e.1.val ∨ i.val=e.2.val)) ++ List.ofFn (fun _ : Fin (D v) => false) = _
  rw [List.ofFn_const]
  simp only [List.ofFn_eq_map,Fin.val_eq_val]
lemma edgeTape {v : Nat} (z : E v) : sb (edgeObs z) =
    (List.finRange (D v)).map (fun i => decide (i.val/2=z.1.val ∨ i.val/2=z.2.val)) ++ List.replicate (D v) false ++ [true] := by
  change (List.ofFn (fun i : Fin (D v) => decide (i.val/2=z.1.val ∨ i.val/2=z.2.val)) ++ List.ofFn (fun _ : Fin (D v) => false)) ++ [true] = _
  rw [List.ofFn_const]
  simp only [List.ofFn_eq_map]

lemma back_raw {v} (H : Fin v → Fin v → Bool) : Enc.back (source H) = [false] ++ headr (D v) ++ headr (ban v).length ++
    (ban v).flatMap (fun e => (List.finRange (D v)).map (fun i => decide (i=e.1 ∨ i=e.2)) ++ List.replicate (D v) false) ++ headr (edges H).length ++
    (edges H).flatMap (fun z => (List.finRange (D v)).map (fun i => decide (i.val/2=z.1.val ∨ i.val/2=z.2.val)) ++ List.replicate (D v) false ++ [true]) := by
  rw [back_pack]; simp only [pack,hard,soft,List.length_map,List.flatMap_map,Function.comp_def,banTape,edgeTape,List.append_assoc]

lemma write_back {v} (H : Fin v → Fin v → Bool) : Enc.write (Enc.back (source H)) = (pairsF (D v)).flatMap (fun e => (pairsF (D v)).map (fun f =>
    decide (∃ i j : Fin v, blk e i ∧ blk f j ∧ i≠j ∧ H (min i j) (max i j) = true))) := by
  rw [back_pack, write_pack]
  change (pairsF (D v)).flatMap _ = (pairsF (D v)).flatMap _
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro e he
  apply List.map_congr_left
  intro f hf
  exact reverse_graph H (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)

end Rev
end PEqualNP.Outside.L_meta_33641

theorem PEqualNP.Outside.L_meta_33641 :
let header := fun z : Nat => List.replicate z true ++ [false]
let pairs := fun n : Nat => (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)
∃ write back : List Bool → List Bool, fast write ∧ fast back ∧
  (∀ (k : Nat) (crown : Bool), 2 ≤ k → (crown = true → 7 ≤ k) →
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1 else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents A C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  ∀ (hard : List ((Fin nr → Bool) × (Fin nc → Bool)))
    (soft : List (((Fin nr → Bool) × (Fin nc → Bool)) × Bool)),
  let fits := fun f : Fn => eligible f ∧ ∀ h ∈ hard, f h.1 h.2 = crown
  let score := fun f : Fn => (soft.filter (fun t => decide (f t.1.1 t.1.2 = t.2))).length
  let probe := fun f : Fn => (pairs k).toFinset.filter (fun e =>
    f (fun i => decide (i.val = e.1.val ∨ i.val = e.2.val)) (fun _ => false) = !crown)
  let vs := (pairs k).toFinset
  let strong := fun I : Finset (Fin k × Fin k) => ∀ K ⊆ I,
    ∃ (offset : Int) (w : Fin k × Fin k → Int), ∀ f : Fn, fits f → probe f ∩ I = K →
      (score f : Int) = offset + ((probe f) \ I).sum w
  let active := fun S : Finset (Fin k × Fin k) =>
    ∃ cube : Finset (Fin k × Fin k) → Fn,
      (∀ T ⊆ S, fits (cube T) ∧ probe (cube T) = T) ∧
      S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*(score (cube T) : Int)) ≠ 0
  let banks := fun z : (Fin nr → Bool) × (Fin nc → Bool) => List.ofFn z.1 ++ List.ofFn z.2
  let x := [crown] ++ header k ++ header hard.length ++ hard.flatMap banks ++
    header soft.length ++ soft.flatMap (fun t => banks t.1 ++ [t.2])
  ∃ G : (Fin k × Fin k) → (Fin k × Fin k) → Bool,
    write x = (pairs k).flatMap (fun e => (pairs k).map (G e)) ∧
    (∀ e ∈ vs, ∀ f ∈ vs, G e f = true ↔ e ≠ f ∧ ∃ S, e ∈ S ∧ f ∈ S ∧ active S) ∧
    ∀ I ⊆ vs, strong I ↔ ∀ e ∈ vs, ∀ f ∈ vs, G e f = true → e ∈ I ∨ f ∈ I) ∧
  ∀ (v : Nat) (H : Fin v → Fin v → Bool),
    let source := header v ++ (pairs v).map (fun e => H e.1 e.2)
    let k := 2*v+2
    let block := fun (e : Fin k × Fin k) (i : Fin v) => e.1.val = 2*i.val ∧ e.2.val = 2*i.val+1
    let bans := (pairs k).filter (fun e => decide (¬∃ i : Fin v, block e i))
    let edges := (pairs v).filter (fun z => H z.1 z.2)
    let zero := List.replicate k false
    let bword := fun (e : Fin k × Fin k) => (List.finRange k).map (fun i => decide (i=e.1 ∨ i=e.2))
    let row := fun (z : Fin v × Fin v) => (List.finRange k).map
      (fun i => decide (i.val/2=z.1.val ∨ i.val/2=z.2.val))
    back source = [false] ++ header k ++ header bans.length ++
      bans.flatMap (fun e => bword e ++ zero) ++ header edges.length ++
      edges.flatMap (fun z => row z ++ zero ++ [true]) ∧
    write (back source) = (pairs k).flatMap (fun e => (pairs k).map (fun f =>
      decide (∃ i j : Fin v, block e i ∧ block f j ∧ i ≠ j ∧ H (min i j) (max i j) = true))) := by
  intro header pairs fast
  refine ⟨PEqualNP.Outside.L_meta_33641.Enc.write,PEqualNP.Outside.L_meta_33641.Enc.back,PEqualNP.Outside.L_meta_33641.PT.Lib.Fast.cpt_to_fast (PEqualNP.Outside.L_meta_33641.Enc.writeC PEqualNP.Outside.L_meta_33641.PT.Lib.Machines.cpt_id),
    PEqualNP.Outside.L_meta_33641.PT.Lib.Fast.cpt_to_fast (PEqualNP.Outside.L_meta_33641.Enc.backC PEqualNP.Outside.L_meta_33641.PT.Lib.Machines.cpt_id),?_,?_⟩
  · intro k c hk hc nr nc A Fn elig hard soft fits score probe vs strong active banks x
    refine ⟨PEqualNP.Outside.L_meta_33641.Dec.graph (k:=k) (c:=c) hard soft,?_,?_⟩
    · have cat6 (a b d e f g : List Bool) : a++b++d++e++f++g = a++(b++(d++(e++(f++g)))) := by simp only [List.append_assoc]
      have hx : x = PEqualNP.Outside.L_meta_33641.Dec.pack (k:=k) (c:=c) hard soft :=
        cat6 [c] (header k) (header hard.length) (hard.flatMap banks) (header soft.length) (soft.flatMap (fun t => banks t.1 ++ [t.2]))
      exact (congrArg PEqualNP.Outside.L_meta_33641.Enc.write hx).trans (PEqualNP.Outside.L_meta_33641.Dec.write_pack (k:=k) (c:=c) hard soft)
    · exact PEqualNP.Outside.L_meta_33641.Dec.graph_props (k:=k) (c:=c) hk hc hard soft
  · intro v H source k block bans edges zero bword row
    exact ⟨PEqualNP.Outside.L_meta_33641.Rev.back_raw H,PEqualNP.Outside.L_meta_33641.Rev.write_back H⟩
