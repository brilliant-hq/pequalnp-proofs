import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32836_aux.Core
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2,hp.2] at heq; contradiction
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&4294967295
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&(roots.map (·&&&d)).Nodup &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs⟩,hpairs⟩:=hinit
  have hnd_xs' : (roots.map (·&&&d)).Nodup:=by simpa using hnd_xs
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
def gvN (w:List Nat) (g : Gate):Nat :=
  match g.op with
  | .and=>g.inputs.foldr (fun i acc=>andD mask256 (w.getD i 0) acc) mask256
  | .or =>g.inputs.foldr (fun i acc=>orD mask256 (w.getD i 0) acc) 0
  | .not=>match g.inputs with | []=>mask256 | i :: _=>negD mask256 (w.getD i 0)
  | _=>0
def execN (gs:List Gate) (w:List Nat):List Nat :=
  gs.foldl (fun l g=>l ++ [gvN l g]) w
theorem gvN_bit (w:List Nat) (g : Gate) (r:Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i=>(w.map (·.testBit r)).getD i false):=by
  have hm : mask256.testBit r = true:=by simp [mask256_bit,hr]
  have hgd : ∀ i,(w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r:=by
    intro i; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? with | none=>simp | some v=>rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.all_cons,id_eq,andD,Nat.testBit_and,Nat.testBit_and,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.any_cons,id_eq,orD,Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    cases g.inputs with
    | nil=>simp [hm]
    | cons i l=>simp only [List.map_cons,List.headD_cons,negD,Nat.testBit_and,Nat.testBit_xor,hm,Bool.and_true,Bool.xor_true,hgd]
theorem execN_bit (gs:List Gate) (w:List Nat) (r:Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g=>l ++ [g.op.eval (g.inputs.map fun i=>l.getD i false)]) (w.map (·.testBit r)):=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [execN,List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]
def isNotGate (g : Gate):Bool:=match g.op with | .not=>true | _=>false
theorem execN_reach (u:Bool) (gs:List Gate) (roots:List Nat)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs,isNotGate g = false) :
    ∀ (p:Nat) (w bank:List Nat),NatReach u mask256 roots p bank →
      (∀ v ∈ w,Avail u mask256 bank v) →
      ∃ p' bank',p' ≤ p + gs.countP (fun g=>!isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w,Avail u mask256 bank' v:=by
  have hm256 : mask256&&&mask256 = mask256:=Nat.and_self _
  induction gs with
  | nil=>intro p w bank hr hsup; exact ⟨p,bank,by simp,hr,hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i,Avail u mask256 bank (w.getD i 0):=by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1,p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g],Avail u mask256 bank1 v):=by
      have hg:=hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      obtain ⟨hop,hlen⟩:=hg
      have hand_m : ∀ a,andD mask256 a mask256&&&mask256 = a&&&mask256:=fun a=>by
        simp [andD,Nat.and_assoc,Nat.and_self]
      have hor_0 : ∀ a,orD mask256 a 0&&&mask256 = a&&&mask256:=fun a=>by
        simp [orD,Nat.and_assoc,Nat.and_self]
      have lift_w : ∀ z,(∀ v ∈ w,Avail u mask256 (z :: bank) v):=fun z v hv=>avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,0,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by simp [opD,andD,Nat.and_assoc,Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,1,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by apply Nat.eq_of_testBit_eq; intro r; simp [opD,orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad:=hmono rfl g List.mem_cons_self
          simp [isNotGate,h] at hbad
        | true =>
          have hn : (!isNotGate g) = false:=by simp [isNotGate,h]
          rw [hn]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i,l⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1,bank1,hp1,hr1,hsup1⟩:=hstep
    obtain ⟨p2,bank2,hp2,hr2,hsup2⟩:=ih (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg'=>hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at hp1 ⊢ <;>
      exact ⟨p2,bank2,by omega,hr2,hsup2⟩
def xs256:List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def pt8 (r:Nat) : Fin 8 → Bool:=fun i=>r.testBit i.val
theorem xs256_bits : ∀ r : Fin 256,xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val):=by
  decide +kernel
theorem countP_not_lt {gs:List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x=>!isNotGate x) + 1 ≤ gs.length:=by
  induction gs with
  | nil=>simp at hg
  | cons x xs ih =>
    rw [List.countP_cons,List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn,Bool.not_true,Bool.false_eq_true,ite_false]
      have:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=xs); omega
    · have:=ih hxs; cases hb : !isNotGate x <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] <;> omega

end PEqualNP.Outside.L_meta_32836_aux.Core

namespace PEqualNP.Outside.L_meta_32836_aux
open PEqualNP.Outside.L_meta_32836_aux.Core

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
def determined68 (y : Nat) : List Nat → Nat → Bool
  | [], ds => isConstB ds y
  | w :: ws, ds =>
    isConstB ds y || (determined68 y ws (ds &&& w) && determined68 y ws (ds ^^^ (ds &&& w)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem determined68_of_separates (y : Nat) (ws : List Nat) (ds : Nat)
    (h : ∀ i j, ds.testBit i = true → ds.testBit j = true →
      (∀ w ∈ ws, w.testBit i = w.testBit j) → y.testBit i = y.testBit j) :
    determined68 y ws ds = true := by
  induction ws generalizing ds with
  | nil =>
    apply (isConstB_iff _ _).2
    by_cases z : y &&& ds = 0
    · exact Or.inl z
    · right
      have hex : ∃ i, (y &&& ds).testBit i = true := by
        by_contra! hn
        apply z
        apply Nat.eq_of_testBit_eq
        simpa using hn
      obtain ⟨i,hi⟩ := hex
      simp only [Nat.testBit_and,Bool.and_eq_true] at hi
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and]
      cases hj : ds.testBit j with
      | false => simp
      | true =>
        have hy := h i j hi.2 hj (by simp)
        simp [← hy,hi.1]
  | cons w ws ih =>
    simp only [determined68,Bool.or_eq_true,Bool.and_eq_true]
    right
    constructor
    · apply ih
      intro i j hi hj hws
      simp only [Nat.testBit_and,Bool.and_eq_true] at hi hj
      apply h i j hi.1 hj.1
      simpa only [List.forall_mem_cons] using And.intro (hi.2.trans hj.2.symm) hws
    · apply ih
      intro i j hi hj hws
      have aux (k : Nat) (u : (ds ^^^ (ds &&& w)).testBit k = true) :
          ds.testBit k = true ∧ w.testBit k = false := by
        cases h1 : ds.testBit k <;> cases h2 : w.testBit k <;>
          simp_all [Nat.testBit_and,Nat.testBit_xor]
      have ai := aux i hi
      have aj := aux j hj
      apply h i j ai.1 aj.1
      simpa only [List.forall_mem_cons] using And.intro (ai.2.trans aj.2.symm) hws

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem determined68_run {u : Bool} {d y s : Nat} {ws : List Nat}
    (hd : d &&& mask256 = d) (h : RunD u d y s ws) : determined68 y ws d = true :=
  determined68_of_separates _ _ _ (runD_bits hd h)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem nextD_mono68 (u : Bool) (d : Nat) {a b : Nat} (hab : a ≤ b)
    (ws : List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool) :
    nextD u d a ws f = true → nextD u d b ws f = true := by
  simp only [nextD,List.any_eq_true,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  intro ⟨x,hx,z,hz,hxz,op,hop, hw, H⟩
  refine ⟨x,hx,z,hz,hxz,op,hop,hw,?_⟩
  rcases H with ((h | ⟨ha,h⟩) | ⟨ha,h⟩)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨le_trans ha hab,h⟩)
  · exact Or.inr ⟨le_trans ha hab,h⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem nextD_of_run_le68 {u : Bool} {d y t s : Nat} {ws : List Nat}
    (hr : RunD u d y (t+1) ws) (hle : t ≤ s) (f : (Nat × Nat × Nat) → List Nat → Bool)
    (hf : ∀ g zs, RunD u d y t zs → f g zs = true) :
    nextD u d (s+2-ws.length) ws f = true :=
  nextD_mono68 _ _ (by omega) ws f (nextD_complete hr t rfl ws (.refl _) f hf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
def tinySearch (d y : Nat) : Nat → List Nat → Bool
  | 0, ws => ws == [y]
  | s+1, ws => ws == [y] || (decide (ws.length ≤ s+2) && determined68 y ws d &&
      nextD true d (s+2-ws.length) ws (fun _ zs=>tinySearch d y s zs))

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinySearch_ok {d y : Nat} (hd : d &&& mask256 = d) (s : Nat) :
    ∀ {ws t}, t ≤ s → RunD true d y t ws → tinySearch d y s ws = true := by
  induction s with
  | zero =>
    intro ws t ht hr
    exact beq_iff_eq.mpr (zero_done hr (by omega))
  | succ s ih =>
    intro ws t ht hr
    simp only [tinySearch, Bool.or_eq_true, Bool.and_eq_true]
    cases t with
    | zero => exact Or.inl (beq_iff_eq.mpr (zero_done hr rfl))
    | succ t =>
      right
      exact ⟨⟨decide_eq_true (by have := run_len hr; omega), determined68_run hd hr⟩,
        nextD_of_run_le68 hr (by omega) _ (fun _ _ h=>ih (by omega) h)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPartialLower {d y L : Nat} {ws : List Nat}
    (init : ((d&&&mask256 == d) && d.testBit 0 && !(y.testBit 0) &&
      ws.all (fun w=>!w.testBit 0) && !(isConstB d y)) = true)
    (pruned : (ws.map (·&&&d)).dedup.sublists.all (fun zs=> !tinySearch d (y&&&d) (L-1) zs) = true) :
    Lower true d ws y L := by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at init
  obtain ⟨⟨⟨⟨hd,hd0⟩,hy0⟩,hw0⟩,hc⟩ := init
  have hnc : ¬ IsConst d y := fun h=>by rw [(isConstB_iff _ _).2 h] at hc; contradiction
  intro p bank hreach hav
  by_contra! hp
  obtain ⟨s,vs,hs,hndv,hsub,hrun⟩ := reach_to_run hd hd0 hy0 hw0 hnc hreach hav
  let xs := (ws.map (·&&&d)).dedup.filter (fun w=>decide (w ∈ vs))
  have pe : vs.Perm xs := by
    apply (List.perm_ext_iff_of_nodup hndv (List.Nodup.filter _ (List.nodup_dedup _))).2
    intro w
    simp only [List.mem_filter,decide_eq_true_eq,List.mem_dedup]
    exact ⟨fun hw=>⟨hsub _ hw,hw⟩,fun h=>h.2⟩
  have curr := List.all_eq_true.mp pruned xs (List.mem_sublists.mpr (List.filter_sublist ..))
  have yes := tinySearch_ok hd (L-1) (by omega) (Run.perm pe hrun)
  simp [yes] at curr

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_0 : Lower true 15 [10, 12] 6 3 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_1 : Lower true 61 [170, 204, 240] 24 3 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_2 : Lower true 247 [170, 204, 240] 134 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_3 : Lower true 50277 [43690, 52428, 61680, 65280] 16484 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_4 : Lower true 39193 [43690, 52428, 61680, 65280] 32792 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_5 : Lower true 52377 [43690, 52428, 61680, 65280] 32920 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_6 : Lower true 8823 [43690, 52428, 61680, 65280] 550 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_7 : Lower true 51609 [43690, 52428, 61680, 65280] 32920 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_8 : Lower true 13127 [43690, 52428, 61680, 65280] 8258 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_9 : Lower true 52283 [43690, 52428, 61680, 65280] 16440 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_10 : Lower true 50299 [43690, 52428, 61680, 65280] 1098 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_11 : Lower true 59881 [43690, 52428, 61680, 65280] 33000 5 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_12 : Lower true 13167 [43690, 52428, 61680, 65280] 4200 4 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_13 : Lower true 30581 [43690, 52428, 61680, 65280] 548 5 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_14 : Lower true 61947 [43690, 52428, 61680, 65280] 4338 5 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_15 : Lower true 36863 [43690, 52428, 61680, 65280] 2190 6 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_16 : Lower true 65359 [43690, 52428, 61680, 65280] 8258 5 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_17 : Lower true 65527 [43690, 52428, 61680, 65280] 2182 6 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem tinyPrior_18 : Lower true 65535 [43690, 52428, 61680, 65280] 33022 6 :=
  tinyPartialLower (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux
open PEqualNP.Outside.L_meta_32836_aux.Core
theorem checkPool_le68 (u : Bool) (d l t s : Nat) (h : t ≤ s) (st : Nat × List Nat) (zs : List Nat)
    (hb : checkPool u d l s st zs = true) : checkPool u d l t st zs = true := by
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hb ⊢
  exact ⟨by omega,hb.2⟩

end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core

def sampleBit (row w : Nat) : Bool := row != 0 && w.testBit row.log2

def sample (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => Nat.bit (sampleBit r w) acc) 0

theorem sample_bit (rs : List Nat) (w i : Nat) :
    (sample rs w).testBit i = sampleBit (rs.getD i 0) w := by
  induction rs generalizing i with
  | nil => simp [sample,sampleBit,List.getD]
  | cons a rs ih =>
    cases i with
    | zero => simp [sample,Nat.testBit_bit_zero,List.getD]
    | succ i =>
      change (Nat.bit (sampleBit a w) (sample rs w)).testBit (i+1) = _
      rw [Nat.testBit_bit_succ,ih]
      rfl

theorem sample_and (rs : List Nat) (a b : Nat) : sample rs (a &&& b) = sample rs a &&& sample rs b := by
  apply Nat.eq_of_testBit_eq;intro i
  simp only [Nat.testBit_and,sample_bit,sampleBit]
  cases h : rs.getD i 0 != 0 <;> simp [h]
theorem sample_or (rs : List Nat) (a b : Nat) : sample rs (a ||| b) = sample rs a ||| sample rs b := by
  apply Nat.eq_of_testBit_eq;intro i
  simp only [Nat.testBit_or,sample_bit,sampleBit]
  cases h : rs.getD i 0 != 0 <;> simp [h]
theorem sample_xor (rs : List Nat) (a b : Nat) : sample rs (a ^^^ b) = sample rs a ^^^ sample rs b := by
  apply Nat.eq_of_testBit_eq;intro i
  simp only [Nat.testBit_xor,sample_bit,sampleBit]
  cases h : rs.getD i 0 != 0 <;> simp [h]
theorem sample_zero (rs : List Nat) : sample rs 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; simp [sample_bit,sampleBit]

theorem sample_neg {rs : List Nat} {d sub : Nat} (hd : d &&& mask256 = d) (hmask : sample rs mask256=d) (hsub : sample rs sub=d)
    (w : Nat) : sample rs (negD sub w) = negD d (sample rs w) := by
  simp only [negD,sample_and,sample_xor,hmask,hsub]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [mask256_bit,Nat.testBit_and,Nat.testBit_xor]
  have hi:=congrArg (fun x : Nat => x.testBit i) hd
  simp only [Nat.testBit_and,mask256_bit] at hi
  cases hd' : d.testBit i <;> cases h : decide (i<256) <;> cases (sample rs w).testBit i <;> simp_all

theorem sample_lower {rs : List Nat} {d sub : Nat} (hmask : sample rs mask256=d)
    (hd : d &&& mask256 = d) (hsub : sample rs sub=d)
    {u : Bool} {root root' : List Nat} {goal shape L : Nat}
    (ht : sample rs goal = shape)
    (hroots : ∀ r ∈ root',Avail u d root (sample rs r))
    (prior : Lower u d root shape L) : Lower u sub root' goal L := by
  have ng := sample_neg hd hmask hsub
  have opF (op a b : Nat) : sample rs (opD sub op a b) = opD d op (sample rs a) (sample rs b) := by
    cases op <;> simp_all [opD,andD,orD,sample_and,sample_or]
    rename_i n; cases n <;> simp_all [opD,andD,orD,sample_and,sample_or]
    rename_i n; cases n <;> simp_all [opD,andD,orD,sample_and,sample_or]
  have liftAvail : ∀ {b b' : List Nat} {v},(∀ w ∈ b,Avail u d b' (sample rs w)) →
      Avail u sub b v → Avail u d b' (sample rs v) := by
    intro b b' w hb hv
    rcases hv with (z|o)|⟨v,hv,eq⟩|⟨rfl,v,hv,eq⟩
    · exact Or.inl (Or.inl (by rw [←hsub,←sample_and,z,sample_zero]))
    · exact Or.inl (Or.inr (by rw [←hsub,←sample_and,o]))
    · exact avail_of_eq (by rw [←hsub,←sample_and,←sample_and,eq]) (hb v hv)
    · have e : sample rs v &&& d = negD d (sample rs w) &&& d := by
        rw [←hsub,←sample_and,eq,ng];rw [hsub,negD,Nat.and_assoc,Nat.and_self]
      have hn:=avail_neg hd (avail_of_eq e (hb v hv))
      exact avail_of_eq (by rw [negD_invol hd,Nat.and_assoc,Nat.and_self]) hn
  intro p bank hr ha
  have reassoc : ∃ b,NatReach u d root p b ∧ ∀ w ∈ bank,Avail u d b (sample rs w) := by
    clear ha
    induction p generalizing bank with
    | zero => subst hr;exact ⟨_,rfl,hroots⟩
    | succ p ih =>
      obtain ⟨b,a,c,op,ok,rfl,prev,sa,sc⟩:=hr
      obtain ⟨b',rb,hb⟩:=ih b prev
      refine ⟨_,⟨_,sample rs a,sample rs c,op,ok,rfl,rb,liftAvail hb sa,liftAvail hb sc⟩,?_⟩
      intro w hw;rcases List.mem_cons.mp hw with rfl|hit
      · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by rw [opF]⟩)
      · exact avail_cons _ _ (hb _ hit)
  obtain ⟨b,rb,hb⟩:=reassoc
  exact prior p b rb (ht ▸ liftAvail hb ha)

end PEqualNP.Outside.L_meta_32836_aux.Cubes

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core

structure Tiny where
  d : Nat
  y : Nat
  roots : List Nat
  L : Nat
  deriving Inhabited

def Tiny.valid (t : Tiny) : Prop := Lower true t.d t.roots t.y t.L

def cubeOK (d goal s : Nat) (ws : List Nat) (t : Tiny) (sub : Nat) (rs : List Nat) : Bool :=
  subValidB d sub goal goal && (t.d &&& mask256 == t.d) &&
  (sample rs mask256 == t.d) && (sample rs sub == t.d) &&
  ((sample rs goal == t.y) || (sample rs goal == negD t.d t.y)) &&
  ws.all (fun w => availB true t.d t.roots (sample rs w)) &&
  (s < t.L + ws.countP (isConstB sub))

theorem cubeOK_sound {d goal s : Nat} {ws : List Nat} {t : Tiny} {sub : Nat} {rs : List Nat}
    (hp : t.valid) (h : cubeOK d goal s ws t sub rs = true) : ¬ RunD true d goal s ws := by
  simp only [cubeOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hv,hd⟩,hd1⟩,hd2⟩,ht⟩,hw⟩,hs⟩ := h
  simp only [subValidB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hv
  change Lower true t.d t.roots t.y t.L at hp
  have hsmall : Lower true t.d t.roots (sample rs goal) t.L := by
    rcases ht with ht|ht
    · simpa only [ht] using hp
    · intro p bank hr ha
      rw [ht] at ha
      apply hp p bank hr
      apply avail_of_eq _ (avail_neg hd ha)
      rw [negD_invol hd,Nat.and_assoc,Nat.and_self]
  have hbig : Lower true sub ws goal t.L := sample_lower hd1 hd hd2 rfl
    (fun w hmem => (availB_iff _ _ _ _).mp (hw w hmem)) hsmall
  have hnc : ¬ IsConst sub goal := by
    intro hc
    have he := hv.2
    rw [(isConstB_iff _ _).2 hc] at he
    contradiction
  intro run
  have hp0 : NatReach true sub ws 0 ws := rfl
  obtain ⟨q,next,hq,ht,hcost⟩ := contraction hv.1.1.1 hv.1.1.2 hnc run hp0
    (fun w hmem => Or.inr (Or.inl ⟨w,hmem,rfl⟩))
  have := hbig q next hq ht
  omega

def signedColumn (d col : Nat) (b : Bool) := if b then col else d ^^^ col
def fixOff (d : Nat) (ws : List Nat) (axes base : Nat) : Nat :=
  (ws.zipIdx).foldl (fun z v =>
    if axes.testBit v.2 then z else z &&& signedColumn d v.1 (v.1.testBit base)) d
def selectRows (t : Tiny) (sub d : Nat) (cols : List Nat) (flip : Nat) : List Nat :=
  (List.range (2^cols.length)).map (fun r =>
    if t.d.testBit r then (cols.zipIdx).foldl
      (fun m c => m &&& signedColumn d c.1 ((r ^^^ flip).testBit c.2)) sub else 0)

def tiny : Nat → Tiny
  | 0 => ⟨15,6,[10, 12],3⟩
  | 1 => ⟨61,24,[170, 204, 240],3⟩
  | 2 => ⟨247,134,[170, 204, 240],4⟩
  | 3 => ⟨50277,16484,[43690, 52428, 61680, 65280],4⟩
  | 4 => ⟨39193,32792,[43690, 52428, 61680, 65280],4⟩
  | 5 => ⟨52377,32920,[43690, 52428, 61680, 65280],4⟩
  | 6 => ⟨8823,550,[43690, 52428, 61680, 65280],4⟩
  | 7 => ⟨51609,32920,[43690, 52428, 61680, 65280],4⟩
  | 8 => ⟨13127,8258,[43690, 52428, 61680, 65280],4⟩
  | 9 => ⟨52283,16440,[43690, 52428, 61680, 65280],4⟩
  | 10 => ⟨50299,1098,[43690, 52428, 61680, 65280],4⟩
  | 11 => ⟨59881,33000,[43690, 52428, 61680, 65280],5⟩
  | 12 => ⟨13167,4200,[43690, 52428, 61680, 65280],4⟩
  | 13 => ⟨30581,548,[43690, 52428, 61680, 65280],5⟩
  | 14 => ⟨61947,4338,[43690, 52428, 61680, 65280],5⟩
  | 15 => ⟨36863,2190,[43690, 52428, 61680, 65280],6⟩
  | 16 => ⟨65359,8258,[43690, 52428, 61680, 65280],5⟩
  | 17 => ⟨65527,2182,[43690, 52428, 61680, 65280],6⟩
  | 18 => ⟨65535,33022,[43690, 52428, 61680, 65280],6⟩
  | _ => ⟨0,0,[],0⟩

theorem tiny_valid (i : Nat) : (tiny i).valid := by
  match i with
  | 0 => exact tinyPrior_0
  | 1 => exact tinyPrior_1
  | 2 => exact tinyPrior_2
  | 3 => exact tinyPrior_3
  | 4 => exact tinyPrior_4
  | 5 => exact tinyPrior_5
  | 6 => exact tinyPrior_6
  | 7 => exact tinyPrior_7
  | 8 => exact tinyPrior_8
  | 9 => exact tinyPrior_9
  | 10 => exact tinyPrior_10
  | 11 => exact tinyPrior_11
  | 12 => exact tinyPrior_12
  | 13 => exact tinyPrior_13
  | 14 => exact tinyPrior_14
  | 15 => exact tinyPrior_15
  | 16 => exact tinyPrior_16
  | 17 => exact tinyPrior_17
  | 18 => exact tinyPrior_18
  | _+19 => intro p _ _ _; exact Nat.zero_le _

end PEqualNP.Outside.L_meta_32836_aux.Cubes

namespace PEqualNP.Outside.L_meta_32836_aux
open PEqualNP.Outside.L_meta_32836_aux.Core
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target328 : Nat := 0xfffffffffffefffefffeffeefefaeca0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def root328 (m : Nat) : Nat := (0xffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa >>> (128*m)) &&& 0xffffffffffffffffffffffffffffffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots328 (m : Nat) : List Nat :=
  let r7 : List Nat := []
  let r6 := if m.testBit 6 then 0xffffffffffffffff0000000000000000::r7 else r7
  let r5 := if m.testBit 5 then 0xffffffff00000000ffffffff00000000::r6 else r6
  let r4 := if m.testBit 4 then 0xffff0000ffff0000ffff0000ffff0000::r5 else r5
  let r3 := if m.testBit 3 then 0xff00ff00ff00ff00ff00ff00ff00ff00::r4 else r4
  let r2 := if m.testBit 2 then 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0::r3 else r3
  let r1 := if m.testBit 1 then 0xcccccccccccccccccccccccccccccccc::r2 else r2
  let r0 := if m.testBit 0 then 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa::r1 else r1
  r0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dom328 (m : Nat) : Nat :=
  let j:=m/16 % 8
  ((if j < 4 then (if j < 2 then (if j < 1 then 0xffff00000000000000000000000000005555000000000000000000000000000033330000000000000000000000000000111100000000000000000000000000000f0f000000000000000000000000000005050000000000000000000000000000030300000000000000000000000000000101000000000000000000000000000000ff0000000000000000000000000000005500000000000000000000000000000033000000000000000000000000000000110000000000000000000000000000000f000000000000000000000000000000050000000000000000000000000000000300000000000000000000000000000001 else 0xffffffff0000000000000000000000005555555500000000000000000000000033333333000000000000000000000000111111110000000000000000000000000f0f0f0f00000000000000000000000005050505000000000000000000000000030303030000000000000000000000000101010100000000000000000000000000ff00ff000000000000000000000000005500550000000000000000000000000033003300000000000000000000000000110011000000000000000000000000000f000f000000000000000000000000000500050000000000000000000000000003000300000000000000000000000000010001) else (if j < 3 then 0xffff0000ffff000000000000000000005555000055550000000000000000000033330000333300000000000000000000111100001111000000000000000000000f0f00000f0f0000000000000000000005050000050500000000000000000000030300000303000000000000000000000101000001010000000000000000000000ff000000ff00000000000000000000005500000055000000000000000000000033000000330000000000000000000000110000001100000000000000000000000f0000000f000000000000000000000005000000050000000000000000000000030000000300000000000000000000000100000001 else 0xffffffffffffffff00000000000000005555555555555555000000000000000033333333333333330000000000000000111111111111111100000000000000000f0f0f0f0f0f0f0f000000000000000005050505050505050000000000000000030303030303030300000000000000000101010101010101000000000000000000ff00ff00ff00ff0000000000000000005500550055005500000000000000000033003300330033000000000000000000110011001100110000000000000000000f000f000f000f000000000000000000050005000500050000000000000000000300030003000300000000000000000001000100010001)) else (if j < 6 then (if j < 5 then 0xffff000000000000ffff0000000000005555000000000000555500000000000033330000000000003333000000000000111100000000000011110000000000000f0f0000000000000f0f00000000000005050000000000000505000000000000030300000000000003030000000000000101000000000000010100000000000000ff00000000000000ff000000000000005500000000000000550000000000000033000000000000003300000000000000110000000000000011000000000000000f000000000000000f000000000000000500000000000000050000000000000003000000000000000300000000000000010000000000000001 else 0xffffffff00000000ffffffff000000005555555500000000555555550000000033333333000000003333333300000000111111110000000011111111000000000f0f0f0f000000000f0f0f0f0000000005050505000000000505050500000000030303030000000003030303000000000101010100000000010101010000000000ff00ff0000000000ff00ff00000000005500550000000000550055000000000033003300000000003300330000000000110011000000000011001100000000000f000f00000000000f000f000000000005000500000000000500050000000000030003000000000003000300000000000100010000000000010001) else (if j < 7 then 0xffff0000ffff0000ffff0000ffff00005555000055550000555500005555000033330000333300003333000033330000111100001111000011110000111100000f0f00000f0f00000f0f00000f0f000005050000050500000505000005050000030300000303000003030000030300000101000001010000010100000101000000ff000000ff000000ff000000ff0000005500000055000000550000005500000033000000330000003300000033000000110000001100000011000000110000000f0000000f0000000f0000000f000000050000000500000005000000050000000300000003000000030000000300000001000000010000000100000001 else 0xffffffffffffffffffffffffffffffff5555555555555555555555555555555533333333333333333333333333333333111111111111111111111111111111110f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050505050505050505030303030303030303030303030303030101010101010101010101010101010100ff00ff00ff00ff00ff00ff00ff00ff005500550055005500550055005500550033003300330033003300330033003300110011001100110011001100110011000f000f000f000f000f000f000f000f000500050005000500050005000500050003000300030003000300030003000300010001000100010001000100010001))) >>> (128*(m % 16))) &&& 0xffffffffffffffffffffffffffffffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def lb328 (m : Nat) : Nat := (0xdaa7a774a7747451a875875475525441a7747441745241208552542152412110a673744173514120744154214120211063413110414110103110110010100000 >>> (4*m)) &&& 15
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def mode328 (m : Nat) : Nat := (0xffeeffe9eebbe9bdffedf9d4e9b59d54ededd9d4edb5d45499549d4454504400 >>> (2*m)) &&& 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def source328 (m : Nat) : Nat := (0xfdbbe6cd7ab8e8ed9b8e4e38b0e0ddab668d5a3460cd8b0e0c5830009f3aad4972a8c8ab522c4a30a0809d2a2c895224008b1220084000007aa9aa856a98a86a88a94628908056a94a854a14004a8908044000002a50a9422288802a50a002200000142828014000000a000000000000 >>> (7*m)) &&& 127
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def vars328 (m : Nat) : Nat := (0xfffbefcf603c80efdbaf4e600860de1368403a80e8ce10264038b0e0bf7aedcb602cc8af58854a70a8809e1044c032a4c8051a2c4870a0807e51ebc7601ca86ed901466898805e016a802a94a84e892804689080147801436288800050a9422008801e2828014280000a002800000000 >>> (7*m)) &&& 127
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def neighbor328 (m : Nat) : Nat := (0xbe585c547474 >>> (7*m)) &&& 127
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def singles328 (m : Nat) : List (Nat × Nat × Nat) := ((List.range 7).filter (vars328 m).testBit).map fun i=>
  let j := Nat.log2 (neighbor328 i &&& m)
  (root328 i &&& dom328 m, 2^j, 2^j+2^i)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev prior328 (m : Nat) := Lower true (dom328 m) (roots328 m) target328 (lb328 m)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev deps328 (m : Nat) := ∀ k, k&&&m=k → k<m → prior328 k
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev runWindow328 (m : Nat) := ∀ t ≤ lb328 m - 1,
  ¬RunD true (dom328 m) (target328&&&dom328 m) t ((roots328 m).map (·&&&dom328 m))
end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux
open PEqualNP.Outside.L_meta_32836_aux.Core

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private abbrev masked328 (m : Nat) := (roots328 m).map (·&&&dom328 m)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private abbrev pairs328 (m : Nat) := (singles328 m).map Prod.snd

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem common328 : ∀ i : Fin 128, mode328 i ≠ 0 →
    (dom328 i &&& mask256 = dom328 i) ∧ (dom328 i).testBit 0 = true ∧
    target328.testBit 0 = false ∧ (roots328 i).all (fun r=> !r.testBit 0) = true ∧
    isConstB (dom328 i) target328 = false ∧ ((singles328 i).map Prod.fst).Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem ess328 : ∀ i : Fin 128, mode328 i = 1 →
    (singles328 i).all (fun e=>essOK (dom328 i) (target328&&&dom328 i) (masked328 i) e.1 e.2) = true ∧
    lb328 i ≤ (singles328 i).length - 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem slice328 : ∀ i : Fin 128, mode328 i = 2 →
    let k := source328 i
    k < i.val ∧ k &&& i.val = k ∧ dom328 k &&& mask256 = dom328 k ∧
    dom328 k &&& dom328 i = dom328 k ∧ isConstB (dom328 k) target328 = false ∧
    (roots328 i).all (availB true (dom328 k) (roots328 k)) = true ∧
    (singles328 i).all (fun e=>isConstB (dom328 k) e.1 &&
      essOK (dom328 i) (target328&&&dom328 i) (masked328 i) e.1 e.2) = true ∧
    lb328 i ≤ lb328 k + (singles328 i).length := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem search328 : ∀ i : Fin 128, mode328 i = 3 →
    (masked328 i).Nodup ∧
    (pairs328 i).all (fun p=>(dom328 i).testBit p.1 && (dom328 i).testBit p.2 &&
        !(target328&&&dom328 i).testBit p.1 && (target328&&&dom328 i).testBit p.2) = true ∧
    (masked328 i).sublists.all (fun zs => zs == masked328 i || !(unorientedCov (pairs328 i) zs)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem cases328 : ∀ i : Fin 128,
    lb328 i = 0 ∨ mode328 i = 1 ∨ mode328 i = 2 ∨ mode328 i = 3 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allSlices328
    (certified : ∀ m, m < 128 → mode328 m = 3 → deps328 m → runWindow328 m) :
    ∀ m, m < 128 → prior328 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    let i : Fin 128 := ⟨m,hm⟩
    have priorSmall : deps328 m := fun k _ h => ih k h (by omega)
    rcases cases328 i with h | h | h | h
    · change lb328 m = 0 at h
      intro p _ _ _
      rw [h]
      exact Nat.zero_le _
    · obtain ⟨hd,hd0,ht0,hr0,hnc,hnd⟩ := common328 i (by omega)
      obtain ⟨hOK,hle⟩ := ess328 i h
      have base := lower_ess_count (u:=true) hd hd0 ht0 hr0 hnc (singles328 i) hnd hOK
      exact fun p b hr ha => hle.trans (base p b hr ha)
    · obtain ⟨hd,hd0,ht0,hr0,hnc,hnd⟩ := common328 i (by omega)
      obtain ⟨hk,hs,hd',hh',hc',hc,hOK,hle⟩ := slice328 i h
      have low := lower_slice hd hd0 ht0 hr0 hd' hh' rfl hnc hc' hc (singles328 i) hnd hOK (priorSmall _ hs hk)
      exact fun p b hr ha => hle.trans (low p b hr ha)
    · obtain ⟨hd,hd0,ht0,hr0,hnc,_⟩ := common328 i (by omega)
      obtain ⟨hnd,hpair,hsub⟩ := search328 i h
      apply lower_of_search (pairs:=pairs328 i)
      · simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq]
        exact ⟨⟨⟨⟨⟨⟨hd,hd0⟩,ht0⟩,hr0⟩,hnc⟩,hnd⟩,hpair⟩
      · intro zs hz hne
        have hx := List.all_eq_true.mp hsub zs hz
        change zs ≠ masked328 i at hne
        simpa [hne] using hx
      · exact certified m hm h priorSmall

end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem finish328
    (c21 : deps328 21 → runWindow328 21)
    (c39 : deps328 39 → runWindow328 39)
    (c42 : deps328 42 → runWindow328 42)
    (c45 : deps328 45 → runWindow328 45)
    (c47 : deps328 47 → runWindow328 47)
    (c51 : deps328 51 → runWindow328 51)
    (c55 : deps328 55 → runWindow328 55)
    (c57 : deps328 57 → runWindow328 57)
    (c59 : deps328 59 → runWindow328 59)
    (c61 : deps328 61 → runWindow328 61)
    (c63 : deps328 63 → runWindow328 63)
    (c69 : deps328 69 → runWindow328 69)
    (c74 : deps328 74 → runWindow328 74)
    (c79 : deps328 79 → runWindow328 79)
    (c83 : deps328 83 → runWindow328 83)
    (c86 : deps328 86 → runWindow328 86)
    (c87 : deps328 87 → runWindow328 87)
    (c89 : deps328 89 → runWindow328 89)
    (c91 : deps328 91 → runWindow328 91)
    (c92 : deps328 92 → runWindow328 92)
    (c93 : deps328 93 → runWindow328 93)
    (c94 : deps328 94 → runWindow328 94)
    (c95 : deps328 95 → runWindow328 95)
    (c97 : deps328 97 → runWindow328 97)
    (c98 : deps328 98 → runWindow328 98)
    (c103 : deps328 103 → runWindow328 103)
    (c104 : deps328 104 → runWindow328 104)
    (c106 : deps328 106 → runWindow328 106)
    (c109 : deps328 109 → runWindow328 109)
    (c111 : deps328 111 → runWindow328 111)
    (c115 : deps328 115 → runWindow328 115)
    (c116 : deps328 116 → runWindow328 116)
    (c117 : deps328 117 → runWindow328 117)
    (c118 : deps328 118 → runWindow328 118)
    (c119 : deps328 119 → runWindow328 119)
    (c121 : deps328 121 → runWindow328 121)
    (c123 : deps328 123 → runWindow328 123)
    (c124 : deps328 124 → runWindow328 124)
    (c125 : deps328 125 → runWindow328 125)
    (c126 : deps328 126 → runWindow328 126)
    (c127 : deps328 127 → runWindow328 127) :
    prior328 127 := by
  apply allSlices328 _ 127 (by decide)
  intro m hm active
  have lookup : ∀ i : Fin 128, mode328 i = 3 → i.val ∈ [21, 39, 42, 45, 47, 51, 55, 57, 59, 61, 63, 69, 74, 79, 83, 86, 87, 89, 91, 92, 93, 94, 95, 97, 98, 103, 104, 106, 109, 111, 115, 116, 117, 118, 119, 121, 123, 124, 125, 126, 127] := by decide +kernel
  have entry := lookup ⟨m,hm⟩ active
  change m ∈ [21, 39, 42, 45, 47, 51, 55, 57, 59, 61, 63, 69, 74, 79, 83, 86, 87, 89, 91, 92, 93, 94, 95, 97, 98, 103, 104, 106, 109, 111, 115, 116, 117, 118, 119, 121, 123, 124, 125, 126, 127] at entry
  have evidence : ∀ j ∈ [21, 39, 42, 45, 47, 51, 55, 57, 59, 61, 63, 69, 74, 79, 83, 86, 87, 89, 91, 92, 93, 94, 95, 97, 98, 103, 104, 106, 109, 111, 115, 116, 117, 118, 119, 121, 123, 124, 125, 126, 127], deps328 j → runWindow328 j := by
    simp only [List.forall_mem_cons]
    exact ⟨c21, c39, c42, c45, c47, c51, c55, c57, c59, c61, c63, c69, c74, c79, c83, c86, c87, c89, c91, c92, c93, c94, c95, c97, c98, c103, c104, c106, c109, c111, c115, c116, c117, c118, c119, c121, c123, c124, c125, c126, c127, by simp⟩
  exact evidence m entry
end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux
set_option maxRecDepth 100000 in
private def metaBook328Slab0 (j : Nat) : Nat :=
(if j < 8 then
(if j < 4 then
(if j < 2 then
(if j < 1 then
0x0
else
0x0)
else
(if j < 3 then
0x1200100000000000000012001000001200100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
else
0x1200100000000000000012001000000000000000120010000000000000001200100000000000000012001000000000000000120010000000000000001200100000000000000012001))
else
(if j < 6 then
(if j < 5 then
0x12001000001200100000000000000012001000000000000000120010000000000000001200100000000000000012001000000000000000120010000000000000001200100000000000000012001
else
0x2001e002000004800400000000000000048004000001200100000360030000000000000003600300000000000000036003000001200100000240020000000000000002400200000000000000024002)
else
(if j < 7 then
0x2001e002002007800700000000000020078007000000000000200780070000000000002007800700000120010020066006000000000000200660060000000000002006600600000000000020066006
else
0x3c02f405500800e400e000000000000800e400e002001e00200600c600c000000000000600c600c002001e00200400a800a000000000000400a800a0000012001004009600900000000000040096009)))
else
(if j < 12 then
(if j < 10 then
(if j < 9 then
0x4403ea064000000000004403ea064000001200104403d8063000000000004403d8063000000000004403d8063000000000004403d8063000000000004403d8063000000000004403d8063
else
0x9007a00d04403fc065000000000004403fc065000000000004403fc065000000000004403fc065000000000004403fc065000001200104403ea064000000000004403ea064000000000004403ea064)
else
(if j < 11 then
0x2001c00204d049a074000001200104d0488073000000000004d0488073000000000004d0488073000001200104d0476072000000000004d0476072000000000004d0476072000000000004d0476072
else
0x2e0240041055053207e002001e002053051407c002001c00205104f807a000001200105104e6079002001e00204f04c8077000000000004f04c8077000001200104f04b6076000000000004f04b6076))
else
(if j < 14 then
(if j < 13 then
0x1001200108307960c1000000000008307960c1000000000008307960c1000000000008307960c1000000000008307960c1000001200108307840c0000001200108307720bf000000000008307720bf
else
0x4002a00309808300ce000000000009808300ce0010012001097081e0cd0000000000097081e0cd0000000000097081e0cd013006400a08407ba0c3000000000008407ba0c3000001200108407a80c2)
else
(if j < 15 then
0x4d03f20720a108b80d7002001e00209f089a0d5001001200109e08880d4000001200109e08760d3002001c00209c085a0d1000000000009c085a0d1000000000009c085a0d1000000000009c085a0d1
else
0xaf2e13f9d31c8151e23a05602ac04d17212721ed04d03f20721250e8017b002001e0021230e62179033019c02e0f00cc614b00000000000f00cc614b002001c0020ee0caa14900000000000ee0caa149))))

set_option maxRecDepth 100000 in
private def metaBook328 (i : Nat) : Nat :=
  let j := i/8
  let w := metaBook328Slab0 j
  (w >>> (80*(i % 8))) &&& 0xffffffffffffffffffff

set_option maxRecDepth 100000 in
private def offBook328Slab0 (j : Nat) : Nat :=
(if j < 14 then
(if j < 7 then
(if j < 3 then
(if j < 1 then
0x160180180804401c158250020240200003201c0602300601c05801032158030090020000089a00a014030000020142c07e000098010090000000080000000400009000020000040020040000800200801000004000000000000540881108a1f402810048024da8750340540c8410140080803f00211801009016004000100000700180400e068018250a2000000110160e00500007800c480000a80040982901e0640082100000800015014000210150020180100000000400003002000010000000000007900e0080000c0620300800500200c038000004e80181000407c1d803042034060010263500b8010881701b01600001c1200700a0000e00e000024330000a00481602a0ac0382381500010c068000120382c8060000300181b13004c188270020880d8050040f40000b00c008008010220601281300613c0580000e0fc060080200200080000606002002000008000000060000000400000000000
else
(if j < 2 then
0x2000030200260000380201402800003002010280030740040202301e1102201710608c000010100340487b00004c1a80502c14000022120000189fa11a0c83788f00c04c0080d02a0702c00200801c100070ba000018090100141501a0020c4100010b40b00186e022018478040500900300406604004004020028000030d60004180e02203800859000000000110020780001102a040028330980382480a05a0140881f014028018010980001081001c0b8118000020200086200801c000000160b01880505a004140000901480000307a1580e03f0140940381109e0100002200800c150000340040280302e050020110000040200001800401014000030000b501e078260000180041a8180001a0070980040440b83701c0517481204e2581000001c008018b5022014170160500582c8150660481005601800c368270101342500034c0840003e0424680b00201c0140000000001c2f00900608824800
else
0x4a00407809008000110100400000a82502600c0181005a26c020010360340480e02e0040a8010000380180d0000b00000300e0580000e06c0040480b0000380d0020880280981e000004150020000240e82405e020088000500140386003006c070000000441d802006098030090000f80280c0020040901000e0c8010040a804c048260040040280e00000002005082000060041320140101f070000088070000000000105e000110030001400001700a03c0080707400001000000074068320040043b81a004000028130300000000405200c008000100082b80c0280280080d0420180681000c03c0902900200c0480802202030000000004100c100a00c0001d00000415800096018070040240d0938090001e0950000000140000100c004088d9030020022370000280185306e0340a80a170150140b705c0c40003b0080b45384500a1840280404a008008260000b41d00101012c1801202210c04887))
else
(if j < 5 then
(if j < 4 then
0x100100800f0220000800f01c0b8720060202740801a000014000110080180100d004024020200180c81e80201e02c000100000400681d014010028020080240d00501401c1182c0080600080005c0101101302e0180301305001c008000040080304b016004018050400000300b0020500580d0160f40d80c09a0b00102201c0080180b02e020088020140f46483d000048018150020f00d8040420080000000000c078020040000300105409c0000707a0100000200000c0c0160020b0020000180d8008030440280500a06e0042e00200e0244901e0700080003900409c008140080080100601a02c0004700208816018010010000030b00480000000001c0e85100007c0201600c0480f0160100441980907c0780180400600000005008040070020020cc0700a02a0040080204c0442000803e0701081d00802c0680a036000018380000082781400000001018002054088130080780080202000011005
else
0x720680000d00a0180d8070000101c0150000000000f00c084070000320001100c0000040e0040060040d00108203c0580503c0480082d00401c1080000c078008090aa0342b80801608c0002302800806000006000100230f000c3780000201c0800100a0280f8000560000d01e0460181204409206000002008058168510140a41480a06e000348010500440201e01201c060330020000000101e0040204c04a078058110040200481000a0901b802002098150010120d81a00e002010000180680680a01000a0280080602e0080b01f0120f800804066220010000460081480000a00c0103c056160128000b80880d000084018118020d415c1101803205400022006088010220100380d01c00200402013038038020330600b01686500a0c40004d01c008040050000000080900e0040002702c0ac01001004000088040040040100701202401806050020008020080200082203c0340b00c00a00430052)
else
(if j < 6 then
0x180000100300605c00000068014008000000180d80c0ca0b80980008a0103280802001c008000020080100100203c000220420c82e80007e024070120180a00580a0660600100002e014140430000000100600601c1602b02807c0980000c00c1b8010100e40280400e038138060020000280302e00023001000004328cc0060240580108e068120020140702d82305410c0000a0140181680002a110000010000002081001201800801016004170000340000880a0040400080004006c0100b0220080d0080be1f80300900602c0603e0000041800002200c0003800000c008070200a41402c0340001300b01002c00001000018070050020980280f0000240d01e01a00011801016064190000100140b806002044018090060b4000660300b80381a02a0000f00502000c0e00200a0440800600001c0d001004074070070060100002b01800c0481b0600801180b00c008028050000400003400204800009
else
0x100600884000e01c12038000078258150000180403501e064050000000fc02001010134000001000002a80000800c000670040380c8010000000c80700004c03005016004018000380041101b0280080d80007c0781401c0360004d04402e1103a0010320440101200a0080b016008020000010040100080b0140040880000a000068160080100106a012010008030160700583d02401c008021260000280c00003c038080160180088900004c1704e0020101507f014010018130b4024038050020044c0050360380386402a0ec0d80802e0081f0000041840500000800c0381808a0480002d0302d00501201e13c0200403e000000050f60740181e02e1840000101c20c0a01c000020020030140300280c010034010010020f00b00d0161b0000420500c40080003e0340200200000c00007004008080000260040a8420100880000404e03808801000078018000360440c01a0000040081200a00019806)))
else
(if j < 10 then
(if j < 8 then
0xfe16c05800002004068100460040283805606c060100160a00780208c0200800606c0dc36803008030010070420bc0600202401c0100e02803c0b81702403c0004e0020581282c00009800027002004138000160000980e0000180804c0440200602001600015800006010008d70000000f00502601402046000194130010021140180f0000081781d0020000000200000c008020020103782a00c0080500f02c01401815006054020000100000002f0360600280200a00800007040008060000280600080e05200c0101600c1343885314007c0f8310000680680401412c02000008008098050d21a0098230520082b8080220040d8530700000780200a00807801054000008060161b80f00600c0180080d008070000010100180c0030481b82e8000300040180a00a0a00003707a02c0500008e0203300a07c00c1a00a01210c0182e04c0040b848000004170410180140c8090ac2140200d02200002029
else
(if j < 9 then
0x3e02c0180b00e588038060382b8028120180ac0a800024068148010120d0000000440080002e00400c18000026028028020240280080800600000804012000018890001840100100205c1d8000ea010000550000000281101205035019066000458000740480280300601804832014000050070040181580005800c060011940e4030360ee028378000060000602c01601c1e803020008150160080480d00000214c330050380a40101a02a1e40a0070000d40d00100c0001400e000000040000062f4030000020140300803403c000000be000050120880d80002d02c0100d0040020181482b03c0040080002223c020000100000604a01a0140680107e00003012002014028b200e0d40500c0640080a8000001000201e0981040080500c000050140120c40a86311a000038070020a011015016004028010100801788801c000000000040c0000230c801c0500208c0e00713e0501100182200401c17000
else
0x7e008008010000600001600e0000600b01e0141102900001c0000b07a0040300d0140280208f0340ec0a0080020840200101c04c0100e13600015016004000040000061b40080c0200101080400e03c0000d02603004035002028028120980b00b02b04a0c43081500c0102180e01a014008010001400201601600c0300005c004008570000682601c012034000110600900000501407c158070000981b80200002c1b80000001019836010000000b70640880f8240700701d001056000008220000200700001e008130000021000d8160080000084207605c058070000fc170630000340a8050340041400303200c0a8120020340d80000c0580000302e0000780500409c0283c00c0800d0020b80f00280000001c0680001409c06812052000088710620780000004e0800f811008050040a904e0440b0080861080900002e0580a00203615c2901601a15400012060058128100320080000c04003808801))
else
(if j < 12 then
(if j < 11 then
0xa0081c0a203c0380001a0020200082f00a18401036000020000020080141d00c0081140f82b0120a80000b02c0c80a00f03a0f8218480000281f80b0000dc0482e0982a820013002000028340001700284f0321181c01100c0140600c1500040880100c0580480a00c0ac0200005c00c0a8270ce0b8148000360040a80301a0880180c0100380f80203c28c0e86501e0100b87a0780148300b01000000019002014020050000a400000002000000060021bc1a81700828c460010000100305001e034198030220380a84a03c0001d04a03c0a400803012090010040d20080481a0240740984f0000040604c05c0540480002e000070120400001600e0020340000300408c0000704a018180210120005905e000008070010200000f00002e0042901c0240640100d060000018420020700501900214c0981f050024000070280040381008e01c0087002a000018100060100000005a0780181100600c10820
else
0xf81d43b816182000000000060000000900a1740281c01e004000000140080085100e090048050160a00080003a0981800c01c0081201801607c0d80000a1440d0020600040006700201c1383400402c02001076060268040743780100500e00c0d8050400d80500303a0081f80f0040200000602e0800100106c0f80a02b0200080784d0001641085c000000030070100082f004010014280540320d02f8140020b41500200c018400760740040b00e000030008010a00100180001c020048010f80300a01d00e0340c02300800000000170000020170c001c318040180000580600200c020030f000002017016020000010121800700100c09c078160240680883101600c090000260043980401a0001980602601c0280300c0041e0050160200482609601c050170040e0050050200001704701a0540708c05a01c260180080041300f0000640000003a00410807026000110010000240002e01800003801)
else
(if j < 13 then
0x1c128058080240003b8090000400100105e00c0f02900800c0702a0020100780d000050048060080000800f02c0283c17600c0040708e0120640882605e1902c803068000058040263702280402a0b80004b02001001863014078008100b608c0100026a0ec0600d000020168100000680080e0020680001205205c2f80c00c0380800001a0080382d082038000020f20100b0000020000080000a1782305e00a0540583d0000000080100a0104a0140140000104b00c1880f03b00002c0004301c08c0e8000400784609b0062880681209a3c8038000020781e81a0000140380005200012000002180030040040000700b0460701f82f0260080500202a19426824000024010130020a03d00600a0140101808e010208180ac2e40c80701c0280101201c014058120500140280110a1ec138ea01e0240302200427c01012000078078330100482a0023540a8008080044640201f01e018008200120180981b
else
0x2400008871008010170110120280601a0160040280b0040600f000002014150000002080080c01c0001482801e0a80d0170020243e00405c1dc0182306a00088827002060128030440000083a00a06c2c8060ba00c02001074198010330040100080b004014070050320300c05600c0041000c020010410050020881e00402801453840052008040090000140088807a008128a100a0100307b0c44301301000a008038a0000040198210120f00483800400008800012004010040440940600006a0041c8370000381a0050000701300400000001013024238010321040fc1f80508a010098150000000100103409c308000283100c8190340c0000200140004a80d0040343c01f0000ac26805006000008000480180080703200c0280100a04000007058000030210000540280303e04412833014030118110040002782a01c348108d80580040680a0080e000809006008130000200100b8010080ac21032))))
else
(if j < 21 then
(if j < 17 then
(if j < 15 then
0x100083a8b303a00c018010000f00582200023c010c70800ac0081a0441641080e0100dc070060020000002100a0000b80201a0000400001c02807800000058000130060582b000024018108750080002407100400c000110000400380a10a00c1584d0062f01801400007408005010004140150020b01a00910e0301180506605c0480b01e014020950480001715400a00c140890780040282f0000740501000e00c418000181580401503200c0c0cb172000000000540040a81500e004130000160a0008360000000080001e0c40300800008c0700c0000040000f008004028470442902400a0180100780100011c279cb0080140200800c0041d8010000140080a0a0030208120000640f8000320181081a00005427848002000000b80020dc3f8100260082e803006030010010081940d00f0560001c0070303a00000101c0041c006008008010db008014000020ca18808800084000068000700080184a
else
(if j < 16 then
0x9a2141503a0040280d0000000040001200a00c0d00a0081680380d0680004400600c00c0a81400401409011014010000cc0240000800e0e601c0080209605800015126018060180000881b81b02c224018030160500200003a038110010040981500205a138010110040000a80901828c0185c0340300000101005c5680b08a004000420101d06d82300a1e00980404200004828000000050430081306a80907c0100d80e0da1580680f02a0201b8000000000f00d0bc0000f8060120643c04a050000060350b41d81e0040a40100000e04a098000110200380c00200c0141801f196008070050020701700002c0703a8340060680981204c0782400800c050140050060640488100202c0f80f0004881381600a0100282600e014008130c60000d82a00e1e46884e0060000580601c01c1c01916a0140000e0ae0740001c034078340340080082503100011c00029000228000450360000a80000804419807
else
0x80000f83522615c0080204e0380b0a7080000000130a80280102d0a41880d0370ce0141a8230000184383e0120240e0030040340084006a0000d00001e03c1201402c0302184e0da11400008014068089d60ba01858034014038100020121381c82501a2e40185009a0000801b0061d409045092030250080640301295612a02c0c00504e03c000150100140180203008c0d80b004074158000002780084001c004298000760140094e0340e40081b0e2130410020101040981300007803000078010020540040000001d00e0701a8180000440005d01e0f40e80a06a0644801101408014800030008000000580f41b81100a0981600d0c842c0381a0b6010218bf0940a4050000062d0060bc016014000020000182b8cc0040a4238030600300000500855044039046004008010800000201d0220142b0010800a00180700e188010a601800c0100f020014008520b61200000b002008008020182f812036))
else
(if j < 19 then
(if j < 18 then
0x186030120060040b41707e02e1500900501e0200200d0c01bc1e00013c000088000040d0000050100bc0486f0480f40900703e004000020060487105600013c0483d028014090040880740105808e2581d80d000000128090001a80908505e0a01100c00600401053006000000430220101d0010001700000d00803420822008088080160000c80400b0001240008d084010178e90ee160000060500580005c0dc0cc0481600000c2602107a00c0902d00a024118070600002f00003e0000780c05a010410be00041011015014018180090140c44d8fc0e808c100020e20687d0cb01e080a304500c01c2800104c0a02000209202416810056004018070260640002309a0801180d0040000d01e02c02c070860960002501901a0805d0020060543001200e0bc0000e0b01c83f0421a44d40781608e01401807078008001730000100280101602c01001000050088171840240500300a2480006101a1609a000
else
0x261ac1a88f0081500000f0ea1584481d0002640280201210c0b83d00000841812006400038260000240017929c0080481a01803c108010140080605e0ac0800203915c03c010080b604c0186d0101401100802609c2c0c100800c0e8060580c8168e5062034000010000001b8170a618c0c8230a80201f0250280000183d00e1d8070420421640a8120460540e8010181582c02401e010160030020601683d0000e04780300a0002c8230280180300107a2a0020020000040100c01211c08801022004000161920ec5f80e00e01c0007d0040100380000419c1c80a00c00c0182303e0081a00d08621c040d10040080900000c0ac008180001040083e02a0600300107a01414800004100038010024540280001e064218490ee0006201e0000340c004004044078090100000d01f01606c000120022180500a0d40440002f0280281680b00e014000350c00040501c00a1f4008720ee0080187d00c19c1b819)
else
(if j < 20 then
0x2c3a8880700580108b0020041208206c0300b85200c00807893000070498030003d0038430260042780107a034078130022601f91106e0d8110060740180a85e006000078331320080301b03e0080082613c28c110020f207024015004038380020320b06000d02a32c0600502a0500101c01a0000481b01c3d80b098000014018321120d8040fa02e010260ed00c1083281802204c328120220504500b002008d080401e05c6980200e000000a1000010010080060281b80000e1c8068210281440406a0540941a00000a0200999001e0401c00703e0003e00101c0d40600213c01c1e00a04011c0702700c0840002306c02c0201b0a00b0040072d2018e60270200401f004018000000181160000380b0703502681d0061080280201825c0e04f0040042b81601800401068014004008110b6070030110040b4038030280002289c1aa02025000064104028000020600d8040120140384d00601c19827
else
0x41582b8010020584b8180a8390300310720a4018021a6294000050160b81b0670780280d0251ca088009011700480a8420b4004050180001440e8000020641f816034030010040020000e00b0060041e10702c2c400017014350020060060c02102a06c07c0182d02004c048020180640201605a3e40880a01e05c0085d04a3d8008010782a0018060000680005d00e0f4050960040800a88601c0042b94213a3104e8320140000300c02c0040280504c000068120460441103506a0240b80015c0000a00d01a09c0100d0320080a80202e0080007c04c0740881f008034038a001402c2600307a0040c028006018150040040000a8140ee0280000d0060080e05a0001780100c01e000068510020e80100105022424015000018080000a20040100501a0003981300806c0200d026000068d60000901b8040020443a837082020010190360100000000002c030010382241a03800e00c0101103e2385b821)))
else
(if j < 25 then
(if j < 23 then
(if j < 22 then
0x16a300010563520c80100801603c0419708606c0011101c09c1d81201c0840080b02c010000630244041783400007c040380061481582b01a118000000800e809005048024000900041a8058110040940201b0840000000018e0900000112e1f00500505a0001b858008074018030400240d82d12800c0380825c0001588e0cc014029c80200100302e0220711c05e0060700a805018070000550000041187600002c0115903200013000000000628000f21700a8a100c1b42d04408203c0002803e01c6b02a04c14004039014124c900b0440001f00601a0109d06601813c0f028018024a58280680000d009008000330080e45b4068f30a20041108200e0002c0000741fc0100d0520040e80706e0242980001c0000c8180e00000007f05a00c180510360040000000631c6c84304810c0a8000543180281807612025019044144080460300281880b0021e81c0c00260b40000a0e60e8548350521cc31803
else
0x561400c82b0923040004802a0081482d1600d40001000628c4b93508000c3a0230e80041900503611838027150058380000085f4048011860b806048014080018af00000c4081f000070208eb0000080088d00000c000100dc088070ea0000bc0684b07017c431180201480105100e0200200600002c3708000416c0581b0061787580109c00c020411343e8010db0020049c81407e0281280401a03c240cf00209c0e0080060246e80c03405407a6200c0004900c0040680202c01806c3400e0360183e80300e0684b043026010068020442100400a0260040b83701e03c0780025c02c00000020188060221b0008010090ce02c0081c04a0380a80000e0041a01f006014008000e002c1287002c12c1495400e0e4089331300000a00609a0080981e0280080280518a17c108372962b4008050100d80b0260041080482604a00010063000038120020800241780f020000d280b0023000881108400c0084b)
else
(if j < 24 then
0x6000058040361c40181200e0b05d85003a0340b8110580001201401002c0880908e014120381640000083b0480e40525a01e0240007300e048120092082947c0080661400780e0240240801400c1b8128a30160080082a01c004000a91de0002880000200c0301a2720280182301c0440296e05e0640607002601c050371d20100180e10e23c398550240040084001600c4080c15e0b42f8000360485300a054074000340040005d8041c4670058080061851c80311c0001e005040000060030040040c0030902bc000430620000080100a0846e0060020b43b82f01c0e0308ac1822143201202a0a40a0970060000081401806804a380a203c050400220000d00f1123c0010b2026008000012de018788bd0080480181516a0482680400a2100184b04400c0080b0de0200b02d11c0300181600c008050300d031400815024038018680860000006a04e0ec988eb18a018098350300d40982c05802439005
else
0x5414002155002004520890004900602a18e0004700d13a00413040000074280120b215c4381d00a0046001108a00c1d83f0021305705e00210c100000023fc1280e0bc0c0a104f02e0483c05b00e350348010f82fc470063480d0130d303c0204580104a02c0383e06600c288fe014010030cf0640001081100c0ec008020060187e01b00c11c158130a02c00800218e0001f813036118010100aa134018200000340283014269cdb00d002018220110022500080b0c60004c0f200a0c46986d0d0040020000640200006d04a120010080480200093a16009401000000020108420400240600e00e1680b8020d407c078010ce0d40901800204c0083d0480080180f0600552e0bb006014038500220003480700600401a940fa0ac2906b1920000001800a064198020040040003b3e80003381301015400013002398030020020a80080b0080004400c00a130090bf00e0800100005a5300a80108817c26004))
else
(if j < 27 then
(if j < 26 then
0xb60d078a3f0284005f801018044000323102800080f1700444e8072501ac0183510a04d5e08e1260180483e00039400a130fa0482a86600205c6200806e0a4091640300400f00a0ca1840e00e0060440a93c0b4008148182861500281801631c050101282a80483a018030000001760c40982e0080201b8041420e40204300a054068e80c02500180305c0040005f0a40380231e0600140b812072290df80030603c290f61081183000632c008010010600a8250010020007101802201000834000000100bc17c3a40180e0180002c0141900102106100042c058300020083e8a60a2044760302ea5406d8000120180300f002004228812ce0909e0020505bc33808016000108080960ec640080be028488310080808181109600c2b0000000bc4704000a014118290761687e011056204058b51620184684b0240300b8e402a00001005008004068970620041a80426600c020411000080c00a09e1400080c
else
0x1e0000001e02c2184401b172060318be00c07ca501712801c2280101861c2682803c1b80d0030062580300f0662001781b102668068170060e0cb88910c0943180000800c0301b014000070ea00201c7083418202c09813006010009b411811c0881500c0300e8a70de06c2d00f0060603285c00c1ec0089c11a0dc1805005e42c9389000200415005338018030001960000001c03214c0600301225c2580500600c848850ac1bcd88141fe404170133a02f84d80407800c0001c0f81d00081c0940580a804012310031021265140b00e00601c170182b60309500000c060240000000206880302002c1a0010f03e40283364a00c34a4005c000060110f81d08180001e0201900401c03063873002000188f50960d400000002474008050141780301202002c830010020880000001e2440700f2340102f0000501342c00302c0002980400860c008e808c0ac1c1030100b45b01f00216c1a8040260000186d)
else
(if j < 28 then
0x20a45e989058168261590141f43286f0080b02b12913c000003960080140881c0040b80005b0020040209c00402002000006088af802004058159c80526f0008040680482e00413206c0580000406c4280b03a2488b93c1404380b8063b001463806018110008cd0cc0680000000877c2d89e0261141e03501201c4000103605c000000361a80000010803c1d87000e03c4e80f0b005c2301700602001a0904600022000002098030f82240d41800608e0f00a089000000018054ee0100080202c0080603d008138090000cc018028173b200c6c0001e42709287504e0300081218e29c5d8000040bc061d70cc09c0588308848c0588d00c0041f88b00a380018370040f00a96200e12c6e4bc02809c2c0150001184385c15a038098270461282f0a90101a00809c13c390070000562e064840062070000100146b0028090280300181503e0380918e1160901a95510a01c028140140040f9ef0360f40a001
else
0x3105a00800805000018310480004b006015)))))

set_option maxRecDepth 100000 in
private def offBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := offBook328Slab0 j
  (w >>> (11*(i % 256))) &&& 2047

set_option maxRecDepth 100000 in
private def slotBook328Slab0 (j : Nat) : Nat :=
(if j < 16 then
(if j < 8 then
(if j < 4 then
(if j < 2 then
(if j < 1 then
0x1d46e07562012154220c90634780000002ade00d5e00ca58326f0056f80c7fc001a58ceb384453809c8b000000074b583b820261c1c4e38e97f843dae318e4748ca08a2a405aec220e30c4c73abac5a5be884dda483748e97f4361923b1860654a0e22c818bfe0c6834e76b08878818f2a000000657008df8e1b79cc09ad06560831a883558c3b3be5b35341d6d418d680c7f601438880b3045584ce6dc063e3830f99d5da29259d0d5e3009a8c371e29ce9211be28e9738361c0862831a1e400803139deb076df977f38be26846d0e388c00000000000004d7e000005804182d244789c00074a11466ce1ab233b70f29fb0118780dd4036bda03249174d980d4ac1953e2f3fb000000327cc379ae000000d7e70887153abf2d559d0de560e9f685d34c03413110ebc36b6800000cdad706578888e98195dd1c5e71106a8cb21c26f86210f40000006c2ca11794202d50183888ab3878d20237ec748e48336c8687eabaef010f528024b04479b1e2cb00334c787acf1f680000000000348b90002a6b52ef0010c0000000000000000018450000000000026ce30000005d6442b9a000000000000008f400000000000000000042000000e1b9c00000000001d8bee072cc000001fb6a800000000000000000000000000000000000000098000000c57ed0f45580000000000000004da5b8937180000000000000000000000ad5a00151000000000000000000000000001fb6a40000000000000003da3240e50c000000012880000000224e28e700000045a6c0000000000000000000014b9d6000003f94e00000000000000000000000000000000000000000000326c000000000000000000000000000000000000000000000007edbf0000000000000000000000000000000000000000000065f0000000000000000000000000000000000000
else
0x21aa297e00000000000000000000000193400000000000000000000000000000000000000000000000000000000000000000cd81d26e456f0a2b7ee000001a1df8c8ed401cfc3a8e10d7ca000000072a202e6700d253ce2f0000000013a191c686eaf800001178ad17aef06c38800a5a000004317e86e380689342029f0000008875071106862fe115708e938435fce3a79d0000018ebfc1211c228dc066e30a836046d1a0cebc111dc0be344445eae57b90d84b00912e34d720cdf71d040b52e113c1542f8fd747f38e9f5863b963a0d21d47b03328000000ccddd000004bbefc195452f5b2069f406c2f13f5ea0046d8e35c8e9248713b633aa0016240e96f0004680c3fb75776888f38000000c98f115760333240000021ec805a4508835e187ea924bd000002f42e4399ea202cc01d1100000045588027588ced986b72474928eb8db0110e831f6c1934a000000149ababba8749100000000a160029041857200f7c1144103164435b0a22adf5b3780085107672c220df0d85680ed28026ec02a76891620e97303d704f29fe01e320882a0066740c6ee828d7c7e6d109bb20c9c7000000058dc19d9e39cf490b77830b8874b8a0000079c4808872124b141d2b100c11888a8a6bfc40000058d6c4d7ee446f1d0babf01b3d8e938c405060c9b0780c688da060c98e025754e7483d23fc735340000009bef809a89ecb5800000060c50000005f11020ab6110ec80bce000000c09b511451088266029cd07696000000b5b9c018fa0c6e6467e303533dfffc00124a1105e307b785d3b61b0b20677a888a3802e6401b200000000787c0162803803065600045cdd7f0c388ce000002ebb40341de8cfb3467fa8000000100201f061d3cd00702519f162218a809558000004055632ed00080f88db887498a00000018b00e2280689463b18e)
else
(if j < 3 then
0x1796e0abff9d7104e1aa77d8f02d7f700289e137e000b1580000027f341ad9f111e0804de465d700c9ef7cb6c800000379360c5a7822cc00a4c9d85c000000110fe02d39044130223a9062ca0d0f20195300000001736827eac195e4e56a35c2758333b44ef1638a891c47d3e127827f76221db10f42bb83a8000000caf5470568bc2c400e2e026b6157e8c56fd919fe2e07ee604d2239b2427f4ed75a000789032a643a5180010519d7d1e4f580000000000061f1009a8026fd600000000002e464c05a6e9ceda4eac3848a1804a1a026ef17c440ba6e81935cdc085000000aa7f06516c8e6f404ce68d0e70687b00c3c16f3e40326c559f8eba8fe0d7ef032bddc9f6a1b2811016c8887a45177e002010000018231400000000006cbf1800000002aa0000075c6a000000c15960000002bf9800000061b0030fd00000000000061680020c00000002ad80026e00000000000000000000000000000001fb62c0000000000000000000000000000000000000000000000000000000000000002ebd80016703957bb172800000e1ba10013d0000000000015ce30000000000000000000003f6ef0000000000000000000000000000000000000000ba8009340ad48030c30000000000000000000000187300000004dd400000442fc80000000000000000000000000000000000000000000000000000000000000000000000000000003f6ea391aa000000000005b9ea001931a77fa74d9f75c48bbbe6400000c7c9900000001c714b1e4d0fe07124d00000000a22d13bd52c6000000000000eb89c757652e62dc012c2001070012ab64610000009f1a57b94b2296798e3e4f6788000001a8e88d1f70ae7c96c8ffb6bb240065e88ad04bfc3000001b2f42a39cb7cf76a8ca51d5d1e000005bf540021650ab527abe464852ae8f4db2f9400000
else
0x3a464003cb00085200000000000008c80269400574006bb1df3081074a0094b00000003834002c800b6c55673804130e97a095bc300000000c1c0e51cb52df00000001d281071e00de14b5e2213ef0be3d695ca80040a800000eff4c000000064a80000000000000000000000000000000000000000000000000000000000000000059c0000000000000000000000000000000000000032c00000000000000000000000000000000000000000000000000c9a00000000000000009badd5dee90d0e99119c0e568b8f77d0abf6c421be220fa00000009a08513462f5da09fdd80acc04ebba996be3fbd2800ca80125e343ec75c5180608c0203a38abc4e7688000005e7f6000000101d0266580000022295747dc9e3e3836118bbd850d6ff86c2c0048e21b0bc488e383ce1520d888e69a488c186c2cc03eea8e6e9101768cf32800ab40265109feea2330c04dc60cc9f0112c3d374117f9a00c224706d04ff5418b4800000825edb8a6b6339eebbdd44837b00000027fd2f4fcd064ef35efe5bcf1c015484c55084fe300049c2afb90000004fe65d6d62e4ff9016242157d0000003708400734b65e0403460e91e66cbde80a09ded39f386de177fead9b64379388cfe46e75c8000000224c0b4e709c50cbd76c00000c0cf21105c06c3fc443722f8de09bd38e8f511c13e222e74454ebfffbc01a7a0c29b473468029e1c537601c10411c7233f3db2b5201708000002ef6bc024de000001045f80759c0000009ff3004300882d00426201b0d196410d0f805dffcf8ddb0d7f73e364c0328a00000357dd030f8444f660062d000000be3f5e174e2f2de17c7dbae3fc195581afd801505000000000000236100f348593f53698a0045600000239ea9b2fd2f69b1000000000006f1c6375b54eaf684feb8016e80275d0000038276df09c41baf2))
else
(if j < 6 then
(if j < 5 then
0x899ea9bf34c000000589c6f1db0ca3c9f2d28e4fe94ad4d2b63d8000000000001e22236e0c02c7a279b112a6e80000219d6a058d5601e38fd2d4038a613fda6adde800000096bf14eb7090dfa0cac46b94ea4c94147ddcb66e00000077dc5642d6816fc98afb20413e732de016b34189bcf84e13fe652902c806e04ae2930000026d62201d3a22ad84116f816b3c27f54135ca65ecd049e9c00000745d2014270004d0e958e03b6f5266d9def661cb7013f91010b58bbe8471b74ae4c3001ad8000006bbd02af9b000000000002510c05dd07bb59000000000000293d13a7e806ce12fd76136b80198e31cf340402a03d7a0905b8050f5bcfb30f09c19dd431c652477646afb400f6f0a6a05f2dc4026c4736ec8a3ffc00000000005ca448a3fc40690a0321202c5a000001a33209bae56eac30000000225e009501fa7925e6100bb6c03a6572b6c20aba851f76affca09fd6800001965e0309cc02d620486f86b3fe29ab34da7100a83952152007471c6e6b8a66953776043760e7c080e1dc0bb8e35d817c25a0000015ffc02029f147deab92a2199ed0c3a66f3cf0009dc07c9ade7cd6426d88870c405be787be00096800000004b4057e4302e100000000000000006cedd8000015d30a00000000003d8f3800000000000000000000000000000000000000000000234000000000000000000000000003f95780000000000000000000017c3e00e58200000000000000000044400000000000005581e32a072cd0000000000000000692ec00000000da4000008b2a400000000000000006c8dc0000016a3a4d87c288df60000000045c000000026d352f9001190d4b3a00000000000000000024a0000000000000000000000000000000000000022d084e9d018cf80000000ca000c68000000049cc0141400000443480000012df9c057e9
else
0x4dd438a3ec034362f8bed0239e1e16c57d73201a753be6e3a7b312fbd600d5c46fff00fcd1685480131547355ab3b42265fe0187900f27001855d71c80084264e608fd27423b8a13f9184d7b2b3a7903982c71bd3f3c604d7c427f6604616585472b637d49940135ea6d6f200000026f7802b7e00ff6a90be53514ea58ad6f85f80d834365f8162e802ed79d1a08000000394702b73a297ca2651a0170c5cc67816e6c0eb6c124c67d8c1816b98c3938275901fad600550c7e94002e08157d226d2edc997aba6ac147fea00f782450609a868774084db4027f80de9e43674a37c29051fe6164a8038e484fe140000003138000000a6ba902b0e20286727c20e37542b94072fd8000000121adb477c000003be7336931c03aaaaffc6834f50049900b5bcccce00262d8a3f35367240340d4c1da9e1a3440b3897bb66f3d9015a2000000023014dd53a68770000000256101612809ab0d3d26e3ce900000266e0c77b6a5bda318cf900000027fd613f8209bce0e36e80000005dfc56770b1c7d4e73aa618b2634512293f849d940f0d50210f179b4c0000097dee09fe02b3a24675eede7ed09fe980658c000008e6ed13cd300b43c4d7be6b79202ed2bbe6a055d9e0224d01a88be5b3d04b8a136924bd428039e4109cc206b602b7800000000000ad2f152c760a3f9055fe6ce4910021904d67c26f027c28508bd3aba79c24be6a3fe33c5c5ab930c07170137bd062ee000000fdba80000000000048274000000105a357c20000003d99800c50178d71ce271685c2fb1bf145e33e369826b52049250000027ca9001ea4aff8d09b7c0aa680060f40c5dc4117c000000000000c4fa09afb8fd3ec617fcf96ba012373e5b740b7fc005286907684e385f2d5e254e60000009f36418bc109aee13a4584b220000006aaca4da40be36f826b2cdf089)
else
(if j < 7 then
0x140f8d6ad43a93e2c7ec13876187f90b57f21769b0022587ae6c0f54817584644c4a70fad9011a010560baf7800000c453862feb03c503ed7cc3d778006440b3c4875288c85065b2e00153c85728d3ebb8b5bd80b1e33183e026fc46088903c70822b1455d60072ab304f71906f80000002b2e0079f8dae3800000084ef3176c16ce30c0f582c785320e2c556dc0f5740232401101981f9c2edea032490013a00697c2bbda220cf7d8db05de3c04c340000000aad8000002bbbe001714dfe9057b1cb671e167b8010b68000000325c01233079fe96aec861bd6606d12d6620946dc1099a178c1000001823986d508027090000000b9a86b3d236a9d30fd78000000f516632ed00000021338036fa000001b5e0000000b6536642af0068684fef4000000000003d7285af1972774665b7303751dc2e003a66d5581004943873e83d7026ecc04f75c81d6c802cf8084d5005890050a42bba000c730161485dacc22b8600822866c901d7122abc80314207bda801c741155801865866f981d7f02c702609af185570000000f522084cb019888028ec1e3b60f1d6014b5000000000000728403943000000be1d00000000111000000000000010e0000003c6a80000000a59025149d16d81f1290c3875d27abda638071ed246d7090fb0576493418213fa97c24fa5f628189dae25b14d65fb1c67615f26bbd844e3cc00000051f5adf0b086059ab47880882c040203f3e78a3f6027fd297ae9157d92222ec0165ce56af3a17e8bc26809a0438d92157e5a9d7395c588ff8c40915a2ef6b004d76000000627b8c9f4008a84ab3e03dfee84e24827fe0762f01facf80000051139156f4013b22b2be003e81108820131d0ca2c855d08f8bfc19dc780bca5663fc6cee4000000fd2158e3a0e4fab4d24cb07395223c8803be3e2d7be5b645358200000
else
0x3c3f005af8003ddeae4f5204f18aca9df77e6163e801e3fb1c2984dbbcbcf9a01b8fb7c38960f4409abc2f9f90476519334600000426732dd654000003289e0914ea3f3040000074caa3c76e987351d7136df0ee00614be5a7c1356277c8109cc22f7b30042663abf6000b8811828565f4f8bf804d54ae53245658689cc8022a7979f45059cc0396000000413f19e3520b52d75727c8acb39f2d4a8dba800c2900000000000b82e73c9d881000c815c2a7db85637285920c074c22cef213cf8080af8016ac0000001b0816eb28d558e0491809a789706acbe5382b2920187b2f7ac405c86995813d8ce800000b41a4755dd015b98000002d7b40000000000000001a7f4218ae20000038978621de2a4a9c736cd80000112dba9019658b78ab92103295c1228900e34000000f3bc4038fd52e592fa76c449d2002070197300000007e0ef1e8b12d4ba8c741f2dfefa5c500f1600e21c034027fec044dc8003d202d70e793b42f97f8bbba02c7ece37bf13a4d826a30015ec005430b5d380e2642c90cff3b21596c24c3d859dda0124e0b5f3202a2170580075fe3f973b0d28c2d784000000000034779c01caa618b00b5fa800000050e22bc8d1594b0b86e9e4b2c2b2e92e0cf000002621b20000000db30cefec058a4a58f50076e2e0a786d52e7f391019ab81d60c07a06163e013ae68121e62757c034f00000000000000000a5cab00000000000002660000000000000001ed1a8116a40011301cb01c5164000003304f000000000005acb6000001d877405ac40135c0bb7501e22804a680303c00b89801460c5f3c02f380b1e5000001ba942770de00e2d800000006fc0115200f9a073a35d8de8020590ae5185dbd401cd062ec300f0f1bb2b44e1bc000000455081eb6c2bfde00000128f39983f4517a20243a0000048b6c058fe8f12f1)))
else
(if j < 12 then
(if j < 10 then
(if j < 9 then
0x574510000001e5f0e6ca31e1ff44f289cd936a94e47bd6300e331f49e4f18b52e8daa157e8d434b140d215e6ca157540eb988e88544b548000002d76e409a5678e580c1b1a25640f1d17366d010cbdbe1566a9f5012098058f41e30eae4b7000003236b4f1f5604b284d442ae0b0513912de9d0664fb80a8506512ac719400564800000000000206b13a4283c6b55c92236dcd894f804a258069ce0153b0b5d100d324028cc2b29301111026f08065c6163cf1d5db8593b22511e822dc178ef31c6cd13b9664af0411522ba34d4b194275bd805d890260d77be8047437aacdbeefe02d7340421204f7400d3202d7d503df844e7d8000015955e0114101699800001b659ac81ab0794421675112f56c71fb807ffae63c05796eed1d9204e90acbbd021a6202a6004bb0c22e4015fd13ce0433e2803fe8000000040237042902a04000000080c351540b3648f1f2e000003bf5d0887b405ea600000875508128edff7eee6cfd736468287b800000a3f927ddde3ddb084f9369959e357d503c79625194195d90000026fe2c006e80f2f007948008df5bab5e16bd301a943c6a29f2db8f93f147de49e02d5a47f6abde0110c7bdc20c000000277c1594732374403a169a9db078ed000000565d2793950000017a2c5869802f0d80268c00e3d459bdcdf0f48874328265835bc00000004d7e304a980712ceccfb16753800001f7733232d30222c265218000000000001a5ca5fffd1ebecbdef613b76bc523901754b94b3020b242534c00000f18ec5ad6c00c2c459b98d13af204ed37a78a09ba60297b3536c8000002d77c09adb59a751a8769f492e00d30009a84386a4f7fa60388800000009590061f8328ae13cf3222240d3f100071f5cbec848a84eff44ba49e0030a3c622400000979ba078e40b8771f49acc29f351e610040480000016384
else
0x35c7609e78c0ac7401c3a00f15989ac5cf7c6660b101fad987f26127160355e0fc41c8b7284d3d01b2ab00523c44730096167c69f02a96800001ddd047b1c502721002c7c043f8e6fd4060eb8021c4277745f4de3d9ee16ce483d71e6adb831764808b58f91500270e01161863b6c5dfdb01fe50169c1876adb2f4c7aee231365a3c780c8b06df3f66c96080f4ac0a62e6e8cf023a5988614d5b767bef8000000105a93eb7c01f53001bf187f3e4916509c8a00000015148000006b8ce6ae61188e840000000d163e3760000011e16ac8ae0010b481188c3550600000888d3804c700000064c813d9f60134ac2770e627896fadd004510f5df80027c46f630012c0000006ad97795e61e6621923a901fd60d9473cafcc31d74df7d791073000001cdf96f2bfd6fa428094dc02a5a64ec2020381ae300645e0646886f9d8c2460418b7c626a000eb3989bb818348c579b75c5b9ec61c0000061fb30183b89b74612724fb5fc0fce406abac43d4cad0ff02189800000401c4c5be50000037d294cc1ec0100f02bcb189f29bc5829d58b01518800000000007578b0665987af764918a00c380022b1f26a1f03f20016001b0800ec7da759909283017a185af4c0505c629bf0ffc680000005c480000001bd306cb6c0a2da02044824efaac275be98402c113134100cd54c3b78c67f00000000c5e9f6554d55db01e33402349be75c000006fad0800000000000f1b40b5ca0065742d7447fec6642f0805d7c068660389c01da590278c065d6afad70b14a880a0c0eba62e0811015b0eaf3c757263ab8c1716c0162680149e0383f7cb61830a490058e03175053c219862804c9678ffe364c5498fb0193f204c2f5ef47a1a33424108328c01675480000003ea87898f5727dc1a29457998ac6ec35bc100f848064542ce8d000000000000ada6fa5cd)
else
(if j < 11 then
0x19fc7035b8070b58addf8000004f92983618946bbd518470000003cd88200cd6c8d8800000441280000000b718e9365075c44d98200000083f52105220a0e01017d80000018f0c03c92076e48ce64c975e830ca61d876037e9a279d608350a17640000017c7cedd2ed0000021e28a81d600348e0d87306c3d8833bc03db917573b87fb8000000beb566dd5030ad4000000000000000088b147ef5e9fbb72aae64707e00000005ead43fde35472c76183270ac067db000000165a6d9786000001c7f80c9564023aa1c1cb235d364ed48fb4881f64ece7334000000c1b71d3edac22c1955f4221848bcd6888af043d04dcab6028da2cb741285ceba28f064c4cea2ba4730a02aa71a1e8a4e711beb682a6ff24a30bae32400000223fc5d958306ae0b25b822015000001eee28f5fc8d41930122c800001b230aab2ee35c4d0b57dc3493a000003e4c1018334bd5dc023063d8c48000000a08a0000000a0800000227ffc04a4530fe31e6a5609d7c640a2015b4008ab8c3f82000000132f000000183f50c39030eca01107cd9f11049d8014ba9ebf84030ea7aec130d68989e980000021ef76efc80058143d7170fa966f9e08025240329a03a32000000000021271461fb3310c6805dc6279aedf38287d5480151c00e3e04f38314ef99867644177220a2355e000495006e3c1ac8845d7328bfa40a41c01a1e01cad3ac3700c1ac61fb28ad7237de6455df7244fd3d74b07af2408ad521b8d3304d8683ac0680921bd800000228bb5f0352df3b66f17f1e66440c1540000000d949ec62406448de28a024ae84a2edf034e022a94dd7b0121c80440b037f1733c8c24e4443d9e9cec0330ee8108bc169d826acf3137100f94d3d74200e56737e980000000c260000003077babb180981000f060106584ee85ab9fe060f6030420316993699a03819
else
0x144d60a133675f0a9d5c10197f0e22a0461c61bb820b1da4066d4000000c7b21ece80e9e092d98e2aa93153751c1d001c12a02fe18377598d6ac555903a7ec000000a26f00dbec1fb8a7d7ce1466c01829e045dc4c3ee04d2d444162e31fa155e7086365209142aabc509d8096a98000009c2d007a588382cd0c9100c9cd10f7b928f64c751a33c9697e4e892ba418bb0000000dbd11ac71dfff7021ec64e77c8523367116a49af4176d2087ac9109a475682239e7177e8400000b7bab36ce30e83a8000001ff8c0d85e1322f42a182245d45f26f08a28e7c9cc3a2ba10f4e1a73bc1790e8f3b55c650800001f4f6c3a5ec1db308a3ffc4e77c25a9e1104b88462c00000741e406c7183078074fe6224a70e0f3023af08428c14292063c183279c35ba61ab9901e56ca6680659d03f92f20cef391f41af504cece9000000992e0445c8000000645f86f10445752f13d9110e38e933c18d76f4fc39a7d386c3b4939525beb67b44a859a2000000e5d978f472887be08c77801aa5909e28be28c05c88af0df22a39018a6848368d91d61186a88e770687e833fb7061d80728f44b160000008d4f996665c45104351b907dcc01f3707159407ad735ed3a67dbcf495e0cded158609becfa73ff2343899754d800001448f6f58b20d5ce88a2041bbbe0000053b4689634031a08d91c90aad98262a44058c0776a6facbc686bc4b5a82d41a1e3caba6a40707dec61b8266780d122de1d3a184ae037130e27e999d912e2d09f2cc888278509bef0d8d0085e8cb344687680e0b0064ea8e3e8c9345ca826a603ebb0371571dee0cfc705a4d1fffb176fb5359cd0dc74830e40555da0efe51d260830bd4221a40c283232fd208550b262822ffb88a4bbbf71541a78075df0737800000046db8220f0022d10e93a445fbb34df4110618cff6556506f33d3))
else
(if j < 14 then
(if j < 13 then
0x64dd352e6c28d02266ce06348be4e60021c49af4100000295a1c6833a870917716d47af0536978f4e8c07ad606b728639980000003b5a08c2348d3043e19225a4a02c3f1ec5400ab854ff0a08835e5bdb7104db12b65a6ebc400000228821d8ee9d5c20183a14548c2b9ddacb28e82be00e0950d6658000004454abace60f2cb06f680e018221ea21325406ae5474bf80000066468032f3222da8ffdd460a5b88be24445cc2f8dd04ff6800000029f212b974e0f2362fec5e7fb15bb015566816b10485ed1c7ff92d75bb175c445a8092d10a6cba0327d0c94d1459389ee29d425c1ada422fde11b5a01e8ec4416a351b50d54b013a5d44af6224bd067664943e4000003a7b63ecfb07074c1951c000002a94e051a34569d22d3f71a0ecc40a9c05f940c9a710f64a33ed9dc5100a53c319080b4aa67371040d8229ce889579c185209203376867c9bad0000001bbe243276a38e1c0ab3cdd0d0060f184d72612f7e33aab8e2d61bcba400000073ea2ee2408c7a93c14e2809148ef3035a9c3716834c957a6588883e072b27003a3605cc832b18e7bf41b095117ee0e5cf4215980df8109c7701bc484517628fde000001c8de03b14600ac10ec448a26f443d7607bfa6a4df0843fdd2dbe2c9220f36803be1c7af1c2b48d391ea31fe6040924b77ca0a0e00ecaac81bde000001dbfd203ad0455b62ae97000000e638c00000287fc3409d4237f843d271bffa00000037a6dc870a4579e885d7037f6cd25a2efefc49a3806c395631593e48e1d2620166d442bfaa37dd12156831a3c00000f0797047c9367b2141568eb88f3906b0fbe3c00000d77d81fd6e84d2458a95c03cd6067c9888b74371de226c488a710463dc4552c2a6d6693d50000017db82160940f6dc088f5a229d42cfac037daad077d6b3d03743613351044f411f4322f7fd
else
0x38c780887541a962224b05ff4d851ac663bfa0755606060be561a77f0a134cf9fa4308eeece80a80d6d0063fd041fbd266fa0b76719255b54f7d3e2142a7f21d3e88e9f4d7db0a2d6d81a05e800000485e2363b681945000002229f687382376c408823800000f00d13b49584d368a5769109c55b6532209e81938a0f8f309a4d837e905656666b8606f558a1274357d8f63bf053fa8414b446370000006aedb856e4c742b22b2fd3f998000001e5ba88efcd266c20647343613c0408d000001ed58436180289ad2aadb08c664000007e6ac4503d035e7c19b726f58e0e9798ad3a476d3809e8a77177a08ba5935b314ae81ef328fdfc407f805a6f00cf1221572493a270d5c31a951040b70d6cb0040a11105607fed09d9b24aec91106a8343244b9461ef62064f706f5641b1c80665540a120000000000060d0321f474f42a686d624656292ef2a87504757a4000005c3fa8a9b9499df69a636115713eb36c43d660c2b792d530883a4509baf04b312b3a04ef8530b9060c1535a69b0c698e6b4638c821d27c8157d9d9d0533dac1176c4773cc4754421ed0304b4090a2868f9e0c1e85f444a17ac443d180c995000000e93744e9af2248215847033b5c000000000007af6bb7395e9d2c0c68d1947b0000012eee63469c35f22adf798487b00c185060cf060cf417d50464e68adcc83fa9c069ea07cd735fc28625a549c460f5fa953d30a794008cf822fff17c7e24fed4771f44ce8f0000006be40c4d6912ae4101798892b44531219a4a54ef5000000473b8893b20dff1855ffc78158026af1c4e29aa2284493e454c082af30d75a5a7b4043132063dac6af9c1bcde3a79500000298ff06215a220990d6fb01eb1c193ce38ea20b7f03f9b5400000c20a369c49c6efd0441980caba1f06715c84872fa81ad9179e6a03077c0000001183)
else
(if j < 15 then
0x1a7ac01355c02794101570a9ba067f10228cd10f483aba784414625cf5155f1aeff89c51260000087fdd8ed5e8e748020288111c406aadd4257e0f273099b003123d0f7cb336c812b7e8c3a3d2f59230207747498e96b80f948120a97184e888211f59f222fd300000088324000000000085b5e15cf740f99ed39f112bdc9f22c9e15a03fa91110e1bda28a40b02000008c5709491a07cf2803f9502271087b603b71af01a76a46500000006b882899307bcb8b124c1ada0015f6000000c50fc687f214cbd1d26d0307792ed3221ee42547850d36890b7a2eb15066e6106744185123b0e32887b2d376c000000ef9203d72000001be73e260e41105744525048b9a1418b112778cebbc00000342ad1dc6c06be202d75610fd90707c2abca4195323b1c04fa6d837f5c22560026c14aeb83edaf439afc221dc067febeb32c35598035d97ded606b6b426b2a7aa0819f7e84dbdc55f441f6c0186640000011a3fa0c2dd114f108a3b07c5da04eef5d9dd02ca706875e0c7da469f180000070b7b08dfa43c5593d9dcd288a64ca41ecd7031b44711e83ade7657629d9cc06e67c1419a111432e7b3c86930388c676b6a0d0e6c1bd340e8cf0000017a95876ffa2a6e4935fcc2371e757ca41e8911054831315831900eff11f5e38382704857e160894e88e8ad314b6af8221a51117e8000003ff4ab0eeb067d2c1b6a019b670edbe2ec18087bb85736e000008d354a562c8047bc574730000041d2e4455cd137cb6a264831b35bdf4848a70000002db6f8355891c8ce1a27f013f0c35bc822ffc06be60edbd45f36452fba142570000010eb62134956f4f445c25951def0f1cd579e299cfd80815b06db70657a0e9f7c44336a6fda02f71882a5e0db322fa5d11dca87b66633980f57fe9d36e85c261df1706fcf711258a73adc00000de9f6
else
0x1557281c26a6ade21b0887d7d48363dcbb29a89f58157ca002ed128cc4dbcf797cfa1b3b6443d8ca25b711044010c2800000222d3000000e9eb045f68241a6493a88ce79444d7e134ac66d4c44e6b84639421ef9774580000007418e04db09ab6806b692637b8d65c7213c5844ece5b16a361c71214593284da0bf40cae8251c48883e1dd3a86c6c15d54200000027778035e901efc418a5d809143bec306a6cb9b3ac0c5fa1e8b811def471729bfda6036a909a5a030bc45b6fa86cd21ca4fa3bfc0513c00a8e50466f0116417d5b868ec20e994856b7239b3c22ae2595c6835a20441fa6d7f8000000720227c92609fdd04c65c146950e70b24baf159d700000007f4a94eb101ecd3383941312c0fefe153571a92b4455280c68c1557088a65dbe7305f51b133694b7a79106b221e976d5c78bcf4df0d6694a3d204d516f3e239144d4cd8a2c7107feb8000004f9d211077297b69b7bbe164578c1dfcf2ef82934400000157743ca6e4269cc0da8b8da4983f6b80b94c0c1fb0f56808c27402a7446992101728c3b0c357da8a9ae077c80b45dc00000346e67da6f0e5248defd1143b39d37e82161c0c9e211cc14fbfd800000830da40db44da7080000035b9144ea448ec29337a17c5460efe90d7f1cd6630285e209ace41ee184d214083ea052e2114c219d5ec2d7f1113e60000008a3ac43146627a199cfe06b65c269d4a5312266de08e7b822a3a343f4000000a9b71c67106803e00000000001a2b940000002ac812a7140000078cb275769a4a7f5c1ba6d7cfc117e8833b684056033e907caf44e3f8c74b120d6dd9325200f29410a3e045ba0de5f837af4f69db45bb94a4b981b6dcf8af0038b485a5c8313e5e597c0c6fd900e10796244511421eae052ef3b7a1c18d806ce8107ffc80000239be21b7c96765d9dd5b01cf667a6cc))))
else
(if j < 24 then
(if j < 20 then
(if j < 18 then
(if j < 17 then
0x23af6800000000003468f3b6c0805e25beb56ee5b87ea6fc8ab585a7543adcd0137206c2304f398343bb162638000002577b250ae0df8088c25400000000001586ea0d0a8441941e4eb31be81a97fc5f39eb168710af89a6e98377d21b0e1145bd0ceb741356010dd45c3418e9ef076588b87e61c7c2030f5807b6e19eb64751aaa2a48000000c2a2771700000002d73ca4bb21d3d199d01dabbc4255b620a8213fccc0000006ac90a4eb84ffdc25f6c202987a6de0e95f026f40b4ac8099dbb1639c1dfe8222d18917b8af218361c09ab1a000001680803bf023a3ef93b4309df259bba0fd5980e954923771bb32c0c1e75a3ea4de2741df280000010f70035b65c51201aacf1d6cc8e0f69d1f4a22ae012d5c8e0ec4183f4139b443860854d98277360db905ccf18507250e8b800000735d880000000001114de023f9090fe07635c375bf7cce702b9593d329448ba4a8ce087b1d9a9f2418ab5f8770487789cdfca89fb39343a8383e619700e1be08b6d27e1c41bfce00000828c383079c1af600c7fc178ea04e66c00000203f14b3bd02284493762900f319ce3bcf6d04418f1448127e2917d8a47b2c016bfe0475e08db7910952537e10d5fd218a2208fb802baa1154ed1e69cc41c65129a1389c037f9c0dffe0d7f80e0ca0a9b0e46bdc7342000000321ecc743e9271dd8514384d6cce9e7e1adcf69b7c08844547b6a106a209ad08000009b3d71cdd46cbf7837fa51eff8062be070698d356c35f7c00000251e031232c8d5cc7eed31b34404d7ac00000b50ec0000015388c1eb1e161af1a4de0d2c9824110be8d946a9ba0df5c445aa134d108ffa847f95a17cf3e28987073283bc405f96a21c709cd20e0f5c000003aeff00000031efa67de6dfff234568185f185373281c5e2d1c6b87ef05135221e89059dab046d49ada61adcf
else
0x1b0ac090a7d17afcbeae74fd041166141dfbe2f7bf48a0981bfa01dffa6d8db202cd250650da72244ffa5897ca2f39525314cf091451c62e2e88b3b3abc1c304e49043b487215e220866f9ef831ac0361ae0b2b434f790d17a4377649fd6f1d843080b70b35760b7c63fed68883702438621e89000003e42640000022081131dc031e5435bea810ff26743271b457bf288e8dc1d3ee99136c0000129ee70f2470b32a8888b80d0c7058e4800001775e67e6bc19cd803528817d72139eb000000279bc074ce1b0b302c4e8cea3e3630e00000063c2cc4e744059a0000063d74a0867c2694b484b120e5d00000036146dffb171c5a031be00f974933b80000001628505e543c87c155e51d9b5800001272e052e623ba6514b44a146a41104c880b68111061c1f809a45031b04085311bafe06fd60000025a3fe123695df72848284135ba00000118fe8aaad11c720f4f931db6f06b644195b21c1f2000000a124a7976915bfb62a75b21b082b6ee2229306346000002747522b4f966d518527ed877444b535065408bced5d4f442209b247cf8e929d82976343868c0419c6090000001e1e70000024edc4dd9301e6a50000030f77400000defa91116a0000022f38c9e4c6017da00da80000000000015a7e80000044776040ee2b771000000405b23449c063f61046285c4b8b57860b3729439cc1699e6dbd91336908a2dcb9f4c1b0ec07fd994242026d6d16495101dd0d0f543797ac47ec482f3949e55117c61b8a8368dd8acb88483c023098527bd055aac4574621b0190c7e83d70c1b96e0e0cb1d522cf92cc5617c000004eace890b894bd86449710a1f6238f8d251de1ddcf2314a1ef11888422000000d65844af7c18f6d33699060ec837f560fdf21eb831bb1b000000075ea0458962fff8c3050403b6a6884050c24af6dc1bb3097201)
else
(if j < 19 then
0xd571832ac41954c149cd48e9b00000006d98f77d4075c680000000000b8eb49677b00000035b8aa9b7000000026db800000241e111079b2cfb0c936a7b0479cdda8886541f4721b0f145bf20aaaf11af3a8e8ee063d3800000693fa0d69305f5010c8681af222a689110d600e7fc42da8202e100000143c9485d220d7ae646d9cfdb39e7f0f3cb91050d100000000000027b5112c1c3072a22b0279726117d9087b89b7378d16ba20b52afcee0055bcf93a938d36493a08856700000018369060620749e84c416000000b13dc40594363c1080efd006a90e128245c1050e92487b51bb721c4726faf0a4875ddfdae5beec1fdc74fe375e9b920000045e5acf1744a4d1c32d3e7cc760a12a04517e0cfb309a43843f110d2bf3e3ea60a7638ce4c1bf891de951534d08a3981898a95dc5058929a03804051ae908736a61cf37adef35a4dd82770e5800001d71e00c8930ba3e874e3476d4c0dfa908844350e100b75804cf882afc079bac405e800000323b68447e400000011879ab528807407cffc00000061fe0376c93f99664d1b3168d0cb3387d6340c798077fa075f84269ba2a6b60abf4800000405580caa0673d0000000261a240db01c1ee0ba7cc0a79a6d8930d8d638bbc400000259c02141708c7227b7a60c2b90a0eb80000074fc0c31fc73c430d1b2075ee23a48c14bf20d0e968bf1b26ed31144607e3881af361718c1104e8be3c88c7720c6ac000000d473c4512e236851217f88868c7cbc800000063ca035bb4000000000006a7308ef3c355fc3a0d52f293017b4c1a1eae5795a134f858278441c80c1b900000037fc466740023a6000000be2b9827aa1d1f620cda39dad8687a70b49b064c20cebd01893e140f819ff98503206332acbcdc8bcf08fae45f0520a12a3036e21aa2283ff360000088a7cb5aba88a55402ffc
else
0x605553f66147279e2f7c0075e240aa4c48568bddce840774f2e510e4c000000116442997b895185085b02af511db93d8ef7ca83c71fcf28fe2e9641944f2d509a640882c026b631148c0a6e12fabb8bd924ed8c808b5aa4ae606891332ebd66ad8835e9416d64c11b1070630a824015d3e0c694045c980f70c000002b2bc486ff2c1765963ee1df8e2c8b0b37f541e72b1ce8838860bf16c8273142e39f22ad280000035b82555af1d0c6a3435c2545c4ad4c06360c51af8183929cdf591a6d80000045198242844c2dd0afee4701de0effe4ff460f4a0decb6ede4842aafd087aac564bcc52a80d6df8a138894958000000000013ec2d1394400000155eb88bf28169b921b920eef7513ff013f1e228cb000002fa21418d3000000200140000027c984228bb159f80fb2d28e740e70df104c64207e688f5e28dfa01b52000000451c67f92c115e133b3e1ef9940000006b5c826a70561ec220e01c4449553a07f01091e9d7d4641202b0357bd2adea082e4000000890af094971104c0000000e10e0ca811a2cb8d0ff4d9e4e02f88132cc920c8da69f684af600000033aa9ddb9825d9e14b480efce846d240000088a77c076181911004fbc36cd5000001559120000034b6914a711eaf2b1f38300000301e9dea3e22b2d306c6402504027f183dfb73d436b2d660000010d5d11126f87ffca4a1d2fc682551678063bd3ab3a343c1000000b37e419b58220f36dccd21bfd1983b334c9b61dc49b1834405263a0f038489827175b773c0618b2935a37d67493d7c1aad61117833da8c225601c1b04123c4736805f1a711486889482dd2a8f7e11372f683fe09a4791c1fd03449e320ce2c5ee029dcc0c9c03ed4e0983cc44148202951e706835e1c9f9cc345c3938e10acf41c8b76ae0f7938d139ce2c43ddb2398d068458e83c4445780297d))
else
(if j < 22 then
(if j < 21 then
0x142760bfa4152d101b0caa3c4b8000002690624be21c1f38cfa78687d8043a70d7e4cdf274fbf987b9e16f84103835c327fc2f7cd08c60a1e73c46d940000010f4b8e23a000000ad5fa0f04c8000024ef52000000d85488bf18065400000011045b6efb4000001ebb297b70234ae043310f2eac46dc7aa15d019bb3124b4121440b5b11ed19a2a6935a5470000008c3fe2239647ef705262c713fe3b18c1d3ebb96bdcaef9e1ecc75f94e4196ba797c69fad21147e88ab31cd9be000000dafe0b01a4445d2220e4670c083837c825a2388a106b7212a14445f8e000000a2c60483dc70784cecb51a4c180000021706284a601d5c136fb45e73a00000000000000001f578000009285b0000010e31093fb6085eca37c313d21200000551c3c3537d046363b4ed01df58382b8441de353ff5b541133644000009d68a30b80a24ea51997c7eaac2c5e2520b69c1555356c4543d186eb85ae55c8ca9d5ea6f888b305554c3aee52f1742ffa34682bd3d1b16aaf2c9aaa872f4604fe62605c000000569ca7b48e07af9bd96387020c12a976faf1a50ac84159e138c9a1dc580000024398332260884944429c935ec3451404c181b66a4405265136e182c615f37c5657666542125e1809a0594fc6379940000006e20416b7022f88123693592f427302000001c45d0cee544e66ad9783904f44b0ae034c4849514813f8836b20d8504157b412d42b4b6fc000006d4851127e043225b3990bbaf0111d5bee7a8425e6095f2066118906bc70992289e0637ff8000001af8e9d5990aae386b60435b5674b67243028d4798ce20c0c3910000038e7c443966038d82c14508daaca8b393769507adb033795137a81c1d91c4e3072bc419db01bce67ffd1aee70843dd400000803e7111e7021ffc1c0d7035c1896a28441fa9d5e55596986d60927180900e9
else
0x24fe980bf142734e144b9000000e93950e1620c9b80a4ef847e6071f3eac9f8148d88e22190ddfaf3cd809cfb81e354db00a0ef9f757758bb66e36b641010a0614f8e924c54db2576e709bfecedf8122ba858ab50000023d23c000000e0f6838d20000007611f185d100000101a843d77a000004bd7d9b07923f388252850000006aa9800000000003842b2a4880d8e2416ceb436e8890bc58f3c04e3ef112709187814bda8346c02d8ee885e7419f9e341c45f8ee0ec48c9e92af19bf7abd5b647e65cbec23e8500000000000355bcf4cbe059eaca4e1c441d60b3ab8e745031ea4183d60de922e7ad031a943ffe80d7a201779000001ffd78a10d46767c1392380000129f82699ce0482f854dc71c1f31fc55c6aa343ab2a21efb571ac0000000c5711b5919f2539cdb763b1c822af700000030a0810e2a3abd0693e20e9f8269b0e3a4c9112df835a980462829fc00000046f63cc25f20dec910f7114a12c445a267cb81f6c8a7579000000c82fca00580d27d5425c2b929869462090ab4dad3e110dc0c1eb8a12962fd4e7e9d202a3439ff0444dec4a3ad000000788e8431e40c7ae6ca528b37f827f461b0f91c44500000005f882b2a216cc58000001adbe8b00d090e9a2f1e6287a803ff788a7d06c3bd3f75c0d5c41fcd103e2fc3613f485d52fad20283d217f140b3dc64acd84727cad73a91d8409ce0c3a7143d62f219b802e56aafa244411a8929c28a7d88daa01e9feeae9781ff8c356892a0840b1f8179f1831aec000013e59c00000267a4581bf20000088fdca8d2d476f6c1b0d00f8c50aca8cfd834226cb1b30d8cb33d48cf03a7ad0f35c851abc62d7633fd68e6e583216c4099c21ba16b2d8918710477748ef941d3f1800000441f421ef5110518b375912cf4b28ff38756888b19185f60c6d8060f63cf3d0361423a4de)
else
(if j < 23 then
0x6fae300000074bbc00000720fe25ab0dd5d080d3c9069ca0fb28043d3e138ff05a7f2a576a229f60000093747057d141c106343ac1fc6507ffda6b350226c117c7094b62d39d460c3f70684f8c57684456615aec0b7c61c5ade7976e2468d08b440356645e8c858b8203d6c0fae463b14c428e84e742226980443471cdc50f5cc8a276c361b62898f5bfd81607241838a0c1fe8386a08bedc1bf24bc88875e4b094c700000004d8511644835fdcead540c7af153610e9e149521403cee1c4670d0fac1954813f843e9cc939af2797880e09c0d7cc896bcc19f962ae04282dd11cc7419f5a044a600000035a94291b01a6e119644842c515537a000007c9fd800000f19ff2049610f7a0e22a02306002be0541a687067e0f9c2cec81120d405cbf07578e20bfa68a470000005f1be0fa9e9e5c608837c838801bcca115fc035f366b3ce0603869bfa8000001356618e7110f53c32719a89724fe06524f4275620083de0ca1684b5b88f3d00000021eb9060f08acb482b71ea5ed409a5288b6a1e9bc60e0810907b0e928c16350ee1d62b4b687e2d0183c4072e3477ce0e833ccff32220c109ad108aa1e7cb7ce7da9764f20116c41ad306842e0f343a94e612acee1aaa300000485fb02935481636281450446e9487842800106b7f0382c843d60ea5bb2f79a000000000000dc996e26586c34c7495cb64db09f742bbbbc0e71a0000000000000001e63bc00000060fb34dab82833d067b9254601537b6865ae220aa0d64e901ee01c1343b5b1067cf33eba89233e1add956efc00000121b3620486000003ffff618b18307b9497f48000003578ceaaee76e698c4adc361f40efc42aacb04df503ff50202a853bf1a001445891e8b173067f9087ae8355a8148f601b519f23ba8c7900a0d8077ffa6e1283235427b6e01acf0323946870824184
else
0xe22908f88e00000067d907627a229ccc1ee062649084715bc973270a258f5fb21f4819f9524ee0592440e9e10317062209f1db7b0072d4000002a681067703cd394e9394072364eaffa4f7085e1a04408a50b808cfbcc483c2c0dd811151445704000011c1ef0000012701c0000139fc52b8b0864ffc1954a306b2393320843dc47df000fb004d7b88a21635daa3996d4d5c6c1ba4026968df2f102d68cfff78a4ab20d59600000032efc0000011c64036de1df0089a11cf4da3334e499bbc008792222d766d6d2f569e63fc688da01056606c27c00000f66a255681069a4683bbc5fdb03074c840e4896ff60cfdc0000009bf8c283769ce9c02dd24a964217fbaa1de40a566090af6647f0c08be19cd386c3f04595a11b87523cc00000071f788d194417048bd68808b381b0ce24efe0e22d0361bc141891a16517c0440df801c5bf53446831ae131fea228869374d089260a6932c578e42452080a418df34000004063b831fa5e9d5ca814c11475831b88361aa16ba1117c8087a50449b2855dc1144706b6182932c4b0030f90401be140796656df00d54084d3b1a092c7017d077f08fe7e92478c9d58c603de4943588dbf46ea781297c30373c76f62c6bdf1d5db1ad0780000023bfd063eb49c72d37dae8c76f0d6ff86f338524423b8bc485c8836eb000000defc8017f612a20c1a15c2428b6254ec453787072f0dad3148208612a5a4fce558a46faf9085ed4205769399b015c5c45e50d5c3816cf94a9e48e222826b7e43a07418e60985f01b3aa113ff063408000011c74090aa3592e10000017437e8fe7a509602fded865d4204297212f60e96d64b7d0a1cab061cd8e9ec8147de098f71a0d5027f801f3f80388d7fa74bae2ec1c4f6046ad8e74b218f642275279ed6299c781020dd5dbabb99d28a69c48b347096f115d7)))
else
(if j < 28 then
(if j < 26 then
(if j < 25 then
0x4114d149d702af9e2266d1d83d881f5c56556e18f88c54ec1cfa55b7a647e4e539e3064e94203fd27aeb0d85d00f2901a184756f9436e139c3a98a17e3dbb211f5984d374c952e43195268c2458b801b9a48a1f01f0418de678b9764dc2e0060d4270a30555e20caa719ff71743cc00c460126500000242a69b2f1c1bcc50cfb08383fc913420a615000001a0e9c1c18400000473f88be27660bde1d4ef533c415ed810e1c45a4e317c732fb7c44e9c60dfc6060e628256c000001bcbd40852a90dc4451bb171ec159630583d070a8434a85077f58f7eb05f14800000000001af2501af607da3a0000004aa59a59cc000002c3198aaff825f580cdd1022c621243043d762ffaf390cf86c2c4131c0e5fbc67f7b056f4000000484c31070e854e90405f00000006ff30893648c458d2f9f05954887bb414dd6045bc3137e858f2019d9f31ebc037e928fb58685f038ad20d6d351f60a7451e1d5da102dba531c92bfbe000003158c91c0105efba144e311041224a3c54ea0558a9192e49c510e3a76c0c1d00884415d61c00001216f400000088a80984183163f5acdb8e2754c7f6e2d7ed0a47f888be413592397bb066cc858fe13e8852c9a8031571508481bf3ae7086118684542d0449ccf8fcc000000000002b78c41cb60d8661bbd40465fa47c9f0f27d47b2b80bd5691db9937548000004862c3e7ee0d84280000222b181b3bf213068a37cc55547364920d85782aef4d6df22f56b55d7200000204589222d2147be0ec268907811f2fa19d438000001bfc8662df0000017fb78477f2241fc060d6335b7824958222f75f76f0000020ddfa000005c5c288bf1975d544533f130658cf2894dbea134d5258d51272e0a393cf619f491cc0f9a3478f2e22fa61537580000007b828ed38110678b5a981b3380000002f69c6ef4d19b2e2bcc2
else
0x28ab092bc8178d90e5cff063ef4683e42a3e3114c0000003f0f003455c717861145db39acc38786240f748dc5313ec8019a8400922c07c89e88008d0e23efd0634c1032be4a37c0e9e40adf00342c505634134f9470c20be2c8441746d1991db6e888741b55980ceba078f937bee0087ced97d00d84b037fb048a94fb386063df3d3f281f76ebb29766ac293e6dcf7be812ca919d2680c2cd773741b3949e46d0a2665421f6e2cfd00000035bbd4d52914da119f42b15a0c44908ee8e109aec831a947dbce0c9ee1fc6e0ffef085c14236fa05cb6000000d7af9271c29e57d80bfe9d7190d22cd05f589c4f3474bb6409ac41aa03076adc0d80be3d293cdf10225818da60ce8b06f7e8e96645137c1baec348938000015627a221be097ef273aa0ea24849e9f000001ad79c1bb3e0effb4642e44539e4dd76de49809a7f0906ec7491489ca91534d152a901b9c40358f5d7d616867cf4e4f076d54e767c667980e71c132e21554da63a1c0000000000064dc02ea0c5a59216bbb00000139728000001cd9f110e7c103941cfb690a98a0bf68e92341c15419dda92a6a06667074f1e0bbae1d853835b0c1c1f600000117ce4e9ad54dbe02f8ee00000135f380000135694297fe03bf946898cdf5e911263b447f82435e203fd40cdaa00d528837862e1f09254123bc043d8a0000007accb29356723b6a6eb2169d10056fc04d8a392693fc7b020acd3d3526e4b420ce90e4a664d3c529bec00dc6218a2d7d3f400000160690d0ff800000490a11cbf38eb6144a9d62a6b90000020abb213dd4a9ef71d86b056e19adbb00fea20df69ce0ab52fb54dd7b83f466189a5dca78b19ea77577580000282180038cf3eb4e8000008fffe654a02baf5234261b97b00c9c10000004026c485ce02fde120c50000002833cc86f949866cfdfad523c53e4be)
else
(if j < 27 then
0x534700907ec1314298a3c075c68342d90fbaa0e0e20684610f3c21edd2be7950000006ff384a8a8202c60624b04d7364df09115cb93877c56ecc98aa638cec06fef2e17d050932a26a8757440acf3512f4e975c834c75339acd5057822acba04fe8b134408b8a447b61d4c300da1d3aba4fff9309a4a03377c0000038fd01bd83d156ec43d5a222ff1147088826120ea01c60a000003f3a881c166000000000036462c00000a000d22ae983e310269128bafd060c8421fb4000008bce455fe1888ed9d95c2220bb1bcfb80f65c18d061189e000003d430c4837422fa8061e40000000535c222e9928568f420e5272a2f89301e57034ecd86b640caff09546870681201ac2fa879d944ce8638b3534149f100000000002213a71ba844f850453e5523d8c1ab8c9cde1087a200d57a7f4791a2572c132c1bb590588e030efbca6a456576388e35c2ca0acbfda4fa422f900eab636fac8144fcde4aa09bed88831d9c32821ee90fcb808821c3612a23ccf1126b800f2c1830e513b243a4c9a94d1d7102ab95c1426b0be3d827f783a7829f2eacdab60dc5521bb8152f7a84e14c00000dafb891e539b5a60463f22ab8d1104b2557b419fee0000006fef10366874ff00d6f0144ffb1dbcc43dca1dcf91d3f333ca80ee5406b3b288a5084d28c6838a4b9ac10f4d1a18f80000021edb4e74dd19ab80000000000069d80382e450820e12f55c75d052c9c000005b0d306857cf2e54281a225ecb0dc4c3a8754000001239147a660cee5c4ee641b0f373264982cd29018287ad149a718d0eb8565a9072ca8d5f789303a33bd2328ca607790000004c58c14cc953e688be314451468cfa609bd18e92a8441a70429c1d2570a773539df2faffa150da838301883dc4e2c420ac8158604fb152fdce74cbce10232898e220000012c4508428c513d8c35df
else
0x1061088db7e2296c284e9148dbc5e629da992220960687e880abc43d5c971a0000000b38ad7bf940d78d000004406719fb5e000006c8e1b7664028362bb98406740bb8be891b54c119402675c30bd443d92191ce8b94280e78c9e3f60c2a215a4e0e2bb05f198a82eb584464ee6b54db22343c28a9702147490c61e096923d69397f9357d772000001980ab88ef05e9901d2ef12bd90dc9bc09f4a137e3448d1aa2ff850912054b8109bc0162983834a1d9c011e5305073c00000101b012079800000983b8110d2619ce808fa136f541212912fe204d39843da43ada30635d4f2fea4ed02220ce0eccf13977a0f5386cdfa0e2e488fac827356221d286453b36b90d4dd22f7a63c81b0fe2a65c794ee9d71325a800002229d8106f972770830bc47b9a531bbf114642f12f8749700efeb01367009bc0000001b0af4f6c802cb5445f0f278f009a5e809bc81e3260000027ef28cbad436bf60000054147b49e18000007ca819e5e39d088054acc0fbe152a5741f6643612849f9f0a8e997558a8476e141cf0c8d54a4e7c6ffa00000033e070b423c11c5e862e35f8510e83a5ccdd800000770d1800000000008e3b31f48e273a1027788137c4338e93d62fc235fe6d7c46c3d842d2cda59e61aa8b7efe902fa24403e0d27f70d8440000010d032c0d988c55a2365a5255ea2228c2814a258b2800000dfdef11d4d86d31c683b2d5c8737f4591cfe0357520d6f5063e004e7fc68d660823f0b5c8370ba0183e42127470fe5800001ad77e0d09f2ee969d39482ad282239f0dc4c08f3ea3b7c00c2ac530af087a50463f822fb05bb794f2eb4711a232cb00969e273acc1c182519a301c70030bb018d3f36fee6fae603f695801aa0bba4937d7000000e0534000009e5e343765caab205391718ecb919320183640e0c41f6be84e61867310241b8))
else
(if j < 30 then
(if j < 29 then
0x279670a9b34cb01514dae4d1d3b603815055eed88201c6f189e059d9220cac89f24494dda647d6c831df05e3d12c2164f5760c1fa067d68de7b037f21443f506f5f88aa340d5844126188a60282eac671b2634b411b5b88835e0eb26900cd0d87e8000007491c55218066e90000005949d22a971a1d0468ace4b7f4bedb310f778a140c47d3e2643f56baaae26b861234221cb09cf4887ba1fedb40c9e002c54bcd3753b4da02ccd079deca976069320cd8c500000087a7c6c7c40000006b4b0cb040509680f5cd54bb686b7302730421ec432b7e16aa1c9e5f403f2c97367b5eb0052f161286204af20acfcc000004cd5c02761a73b463cd2800000064e1088f3982dc8223fa6e243c7633a49d2aa90c506ee106e2a5253d8079e9069cb94526c1c1044feca8c74283073d5b84a50af0647fa00bbd0f641a02ff38f8752e0ed855f5ad9bde0dc6e07fe715cba0e72e96f74786c36db836ec62c1124d58e92b019de2036c93c72db6efe0069d8db6ce08b39af36304415c2e6f0000000327c948b1e8309e1087d8b65b429154000000317f0000016d520148b00f5ff8e0e7c1a1762bc5406ee2b87b1000000230db27bd6911214459da9d5b319988233f9c1bdc2465a708c6685583c000000aab83c7c72eaa14441a82fadc11ebb2b5f7844530aebcd08955b00abc000000e0a416bd3108c6563fcc000001e06b00000028d9c516c79f27e8000000c5b29cee937b76c7071e7c9e2220a60ab5e93cbbce552b0a6d14a2f90a9aea6a11e699ee16ba8000001dd1c43fda808723800000473b40d08572c43813e9467342345cd0dd688f961c99bab10bc9101fdafa31a545ec7cd6a14345087a684b5da2b2a0223bc3de61c0199926fbe2991a41ee18a1fe4339ab143f4b98bb04ef4ca43963faf3cbdbc58f3a0b0c911d3ef888634416ce67b47
else
0x1215e035bbc00000364850135d45e76c1a10a1e59d5eed73b670018f3a808f30000018eee60e1c80afa0162691067246879539bcc076740be2207b79471f0987fe414d14c4cbf823090144d537f795f5f04718e90000024ebfd6171e23ebb03add880a99b8d5a046fc8e46f0aae6827b7c7a6f5000001c946c5402222ab651abc8882d06a198b638a4609306b6b4eda921ff4c02acb2bc3a8269941cbd4062d911a7799216c32c8d01373d1f6a5c633622abc313688e96f4445ccbe8d742af9889be9d5d4247bb2740d60bce18000008c33d11ff780f67d75d9e9cce665e5ac2f2f277118191630000005462c4497a2028911167830a6c4095c8aa491c2f1cf2780000000c8ec17c630527709cc20220a65f86e844f0c00000aaddd7384e90cb14000000000004e661c3ee0bc038c26899934200cae1f5f483a5bf0b578cbe354000004c0f30765082b45821fe014081535bbaebbe9ad3fe0ba2c748e783064a647c47eacd7276da50b3d07676d9199075390756f430df60c99800e77837fa893d142aacc1a26a035b5808ef6d41d9673793ebe500000139b9b58168927e7843d120cd5c1106f29734caebd40bdbf1ef5d80000045f4d250bc0d87c000000b4bc233ee9067f18883241ad38477c2883e33053d881b3c58fba12d68312b7060d2a280ec9645a9e90598730aa6cf85c0caa4760c55fe60c9de0827908a21400000339987a7f384e6ea2bf5e9ff991144c0ad24e67506f3ce61c454a9ae2c2d202210e14a55903074d394f80d7e2227663b72f06223a38dab000002ce6e47cb023a098693cb888ea444d3e388f317c65268ad021f7e587fa5f47001c248000001af980d87528c3d876d8c48acd1d6d21063754d31a0c9c942821000001535e0efecd0e0439a4f1000000000008a5c30be2401dff60000055bbecd8710443966635a)
else
(if j < 31 then
0x19cf8ace6681e2e2312c111042032ab4849ba000004c130033f0c47798463b14cfc8830ee41a14c1f6e90edeacc73b15c762149f6000003b73f844168012fa8fd7f11a6701ff47352e0000000edeb4291ae137979cddc811405a4fa48c68e0cd5600000017914a3e5005ae2870e3443da6473d996ade0817ad5076a21e9a36d672d26d471da51d9c36e5c943064018d742288d0690500000000000000001d4eb08127cad95a93d23a2b742177cc55544000001554e8ad3c01af1875df0558778f9d2123ba4bb7c47fce443df74000005d13e71964065218745c1370ac7c4c09589fc1b5de000000abd001c3a0749e62d694014d6035abdd7186139932f9458eaef41bd1e09db1000000963cc000000d0fa8d3600963c57e37c141dd8f66f1a21d60cf7220acd5044d831aac711640708c00000038280687ae0000010f6b0000001b4ca0e3dd155d4103775f31ce28912486f33cea100000033b071b1fa0e93640c1800c1fb9f25b28ddf844158222fa000000e2f601bf946cafd04ee18d1aa03ab03146a43ab450fead8000001ad8f111432edff269f142e3b209df5b65fe1e998abca8742acf05a09c00000d27fd18c4ac9ea3017dbe345e900000000000e052c565dc8ec67a11f6443d0a44fdc144f03ba24da9bdc00000266e645e7602955edb9e9060e20526c8c178642eda103604c7ef53ab565d47a469cc335fc0485cc8124e58a7a0a5a48183a41bfb7176ff8ec3ec955206cee848bbc8897505654c02e911d75d8a13c4000004371c00000090a7c00000bdaf7069dc087b181a99a4a19c0d6c1088a8c00000e5e9e0d57c0306c15c0840e9fb24edba6d3d0da9b0409d106fc70273a400000269249f26a338b540000016bdd11173275788d122e139bf4926a830a4951ab44e5d91d26a0892aa495741e5da574b28ecbcc678260cbd9
else
0x1a967831ee1d7d24121a51fcc79469581231b402ab280f53d5f04405be3d7391a24488c7a049a144fa8c02efc8af7928ada6000001016bcdea91ae79a2208c492d4048fe85092e0f7f71297244534836728222a22a6728de46a615d0af5c58ecff0a9a8c74f70222a2a1d7c0e839a2dd10343fb01b7503121054d9e83969077fe80ff5c54da40c7fe5f96f000001e496e0d8bb0000000000287d2c3aba549565836e8426f742028d400478000003612d21d963c9cb2215d1b1f7e16b8110f42826b6c4059c67dfc1106d03778c461d823db21971a83defc5612898360110641a4b1c451240a3d033bf786f350935980dfee1d3fa47b290375c6bedf80e970064d9d4fb7e0c2dc11f752ee6dc183680d7d10d6c0c1424c1abee1139409ae507576a0a3fc000001e27a1557442afa8222c3037d61137401278a0000080169a51ee053132568241a1c2273cf8757d73a9ce2c2750e1208089785358237e794ee2800000022adc0d8669014fa17751179d224f43b3129021fde2b2961017a1362167c93e25afa25ebc8000001af40134e9014f89acab42c92a0c1db00000000000e7982e709261e75087b4a38b60000000707103afa41df84149b35f8e20e92a54bdf31819d19646038254cba0613fe11a1dcbf4b5675144241ad8326eb65f05dc3e8344be09a741aee3d6735a3e7a808e5e4452885671c215c50d6f608db4843d3e148c4963f3835a482379d043be09a7f45ef10711be05a9a0836f0000018fd209eb02008ea01c2ac47cb00a7b4000000fae6e479560dfd90f34286b7664dd86276e7100ca8e52607393a000001a7f780000000000feef307a530f6fb047780a5c4d1145221747844332241c206fc389079c361a29cec80000037d6f0b398a0c6f506be4888bb07e1760c7f3670f78000001a1c6cbef38dc511fc3703177c76608)))))

set_option maxRecDepth 100000 in
private def slotBook328Slab1 (j : Nat) : Nat :=
(if j < 48 then
(if j < 40 then
(if j < 36 then
(if j < 34 then
(if j < 33 then
0x7ca86d4be13baafaf96966d38a9b642ad58e9cf50ffe2000000513c8256a70c22394e33127e66931e48ddcb00000018d9400000063ed889ad4000000e096754cb080bb476d84baec51d24c360af8000000db9a25c7a800001586e60000047ccf8d0e5cc95d4a68b11115903a2e02695821086064ec0c7af01853233ce30a4deb23b85e5bf41add702268254a04c601e00000746c50172d074166343c606b47940c596951119ee73e3200307e9ce17e2428c04cec80000000000441320b5ef8e343076d74df3f00000002720800000000004f57c887aac635c43b0c29ef6506b758749544dac11325fb49f40dd90a705ac484fb83b3e0000001bba50674e87661067d8800000495ab211250000001adfc15352a73abc405f00f39d7ff433a8b0cae73a135c70000002d2e01f15e1b19e000004bba8c74f226b1f9218ce08e7b1ae77a045a2243f64ebb0467def3cbbb0d86bb2aba000000000000f2f38000021310c20ac46a0519a09008c3a22d9bf01c4814f5417b1948e74b000000ce6741873271a9439d9a8337d0000000ef94643f70563683ff26310b9120fba1fff1b4538c57ed42253800001a5fdab3afc000000307bc08bf60c1db110788f065211bacc10d2111ef86ab804631f2ec9e8e47fb96a807239a323661ee3426814d151ce763048c4e1afa2c843dbebe2bb016c8837fd054dcee1dbd016ba880a101c121371f8a03601ba544451e0511130b1e68d07404434a45e880585e3abb807498221eb0077f500be5437ffc0fec90ca40b9ee4115170141ff2a1c327b0d47411a2b4e61115c308ed8fa03a3b6db362ad889b8c185aafa194014e9835e089a72c8dac4206f408837447dbe697a57bf491b888446db20caae0705200000051f2a0df8131ca903d6a8479c2000007b2e2126d58d29f4048593eaa80000025ef5cf9fd0
else
0x2ae5955515b73c80ddeb0dc7700abccec9086c2370de7f125949d5dfc418d5118fbb25bbc7195a0c1cf373a3a0cee88e7f85a5d23eecf4d7fb8ce9fc3adbf0a46a1226cc1df482578b1e9a50edb106b7888e2e586ef8036d6931a643583b01fd09b9fc9a7b761aafa0000022d9a5e530e15bd7206cc0a3649aad7106d9b01f640c6e88075bc139bc0000030dbc83696e217cb01a799a26e8405d6123f8486ee0506c8c26587ee559ad62888a15dd37adb9eb465eb0e9fb41bb72015a95b67382afa85a66e0000018cf3022c1d9ad94393eb153eb0336e8beb2011ff606b50c583d844972d6c864d7ea880bb42910e0000029ae80ec6d0ca6c02be093a7eb8090e4451eeacc0409fe6833645bc50e036f21017e0883241830a34da906142346f941afa6239ac1f874297904000002559a5f54a86bf6523be6228d484b6906f28c8e9cc000000f2e64f8b0474b24922b00f36b19b758000000000024d5d3d8bcc67d441c54c7a6e50bcb04000006fa5d06ecc833e984079277cb6011d900000029384ab2d848ed50d0e75f69dc6c6c44a2d8bd33f44414c1348f1e22904d2f8193f4aaee9522f10383500a078134f79c1f7aaefa63d385390ed66f7a8aca0806b2a0fe2c09a4d08a329bfb2c2aabf4ea7480000046d1efbce61844f0882d40e18a3faa4273e980d2c8131b2f93960004492e4c49da4828c5a29062b0ef4419f7cd24e927966d166a47415e2aab96cbf1800001d71548ef540a05f0d3f3c74b2a3c9bb06ed7031a24331448e52d0e6c72ade05ca7ce048d51fe690a39264a1b4164dd09a5d1c106517ffa242a1393f58bce9800000000000a4f000000012bd4a4dc311dde03278c0618628dca8ddfe80344c00001446c911ed4088a4439c70466a62cc4ebe42bc8314e900be88afa08e66a34d5c0efc72bac78c734e2f320135da)
else
(if j < 35 then
0x118fac4be7c43d041b0b8524b08000001e3b88cffa647d38a9b4e7c526bdda0238f888ab5826fc40bbdc00000116d35215b857d4f00000152ee137c3c1b0ed00000090b355075823db419f4a29540ded176222e41364ac112445af2a453a069bcf892ef67972a0e0fb8c277030edc85fa4dfc920dafa00000043dac0d7ec7957183befdb9786a57d704fd2030f3897c123269c6c7d53d329915bc6a4dc8000002ad15c9b174134910ab79ab5bc975d162794151c4a02fb39d39da3a4b910f7b088f01ca3513e4a20000004d36c00000649ed5f5c9166b809088a899e6101d5035ea80730c000007eafc8aca44000002b4c36076ad0b3c005f227943b4914e000000da36e1188811d7a8e9eaca17941c1b40d84c000001571ee19bca06a580e8acc00000b8a930000006c23a771782b4e74e75308b3d4f27680000000000128e9000001144b9015da01821cecfc6224f73aa900cf270a6fb40c7bd07ff90677e000000b43da51fe39067780391a0000017c7a0571d22a12e557c31a1cc2fc7ec1c1b23fad88f46304134c135fc3b2fb4e748835f045176cfbbb91506a048ec400001250a582d6887fea84773ab18ee455da86e35202fe4c87e2120ef088b6024332218ca675610b9a4c4795813cd109a44926abc4834000000942f2800000a5c882f21706168826af4749820f8ee87645090ad41a3680ddb000000025fb49c630b8c8222dc20e9e700000117298000000706b93ab953b7ec873e6844a1a6e3160d6df007d2926b24405f400000077d500f7e21a75a9ced04e741837e64df51233ab310ff7031b404b524e3fed06be78502b800000409c6082ef8e92281c1e87d5f2468fe408fe5e1114139cf1984f339b85173c04eeda11543080afcd6186215c014b3e9022501bef41b49506ff8273b184054e5f5d40d8e53596f40000038cc0
else
0x99df1240f04283c40b8ae1624a0d0fa435b72000000a47100000017b4ccc18c2507a090bf800000113391105584ff111d07ebae849f24d8ad3084515c959020000005ae349bc9ec51aea40d8ab9a78483a6134f82cbe04c13f41afba027b8153699b12a581b992648206f4f8883ee00d0c9d5a55e5e480e77119b1a23acd0000033b3881c36000000000000cebd2263780cf912bad581eb866b3ee1df940a17486c34152b5e3644b10f730513e026960bbbad206cd8d1328269027a48e59966087a5081ba21aab311354bd97504631a289921db62888a803f58c2109513419887a103239107cd00d7d8302e7843d4490ac410f5846ef9cc48ce470b60635f80000045f721ac87746f6018ae8445da3a4c41a6c580bfc16cf8344c945593680000075dcd116ac89f59c1c3c84055c1a9cd232e7800000281b08ce830380416898c441e41578506354000000add860c3b35c5f0038298283a03a4f9159a6800000000000dfc7000000906318cb9621ec87227e0d17e8683751f3ad5fb5c8d122880242469c720e87083aa044180c31c1000003eb32843d1ee40e75bc6bbabb480b1b40c19a0635d8aa6880000021ec30d846035ac0ff32c9cedb00000153174d091a0000011b6a0796d8555eeab5a107ad08000000000049f9506bdc21c2281955c000000a31d8fa72c1932aaa21e61bd14c7e8c43d22e31e3799f0cf7f41497d20d98915346834fd068b3033afc1a2532a6b54e09240c2f516c4c087b75985d90b4b50386a82a3d4e3aa20abba09a778882201ef40149d200000072af139d84100f94a5629372847c8a642a568bcc2cce674065f6e919992f64103e4c000000b1cb02c620b7b8571de80c1d958d434f4ee4371da000000000028c0f874bfc22ff32760e1277b84838421efb117cc8706d0361802f6b33f1360aaa78aa94221ea5))
else
(if j < 38 then
(if j < 37 then
0x9a558df6562877912f9410f414a72b0183f033fc68184b800000687e1115e000218088a54768113e5af1fcf6803a1037960139dd4c9c883bf3c627da3436f579d935e6c204b66d27b34ef1ac847c400000f028241c6900000039b88046d63665a03827c1b18404587144c881f32c483fc58507125d6ce02b17bb9ccddfa5e849381318000000000009b6f8883ec75334e94f5477fac79ebc000000dfa0000000343a429bb05da010000000000050fd43b0a11a1fc9a6bec44114344d19d35118fb86229582e4f6000001e547a38bbec0da515e660e92a843d951cd97320cb8ee31a055cc000001fd4f37d65809f0930eec384ed401618193b033ef607df880000027fd2092ee111c8880a98b6c26bb694389739ad755cbffef9ad309bea1476d445562881a711179827b1a86b9e0b29201cdf19e39a0fb6a23546110c4480fb914e4600000846f603b3ddf598c343c90000038eb94421c8b46da11b6f0a728468da4a143d6357a890a511b792b139b14179887a10ebf6829efe0a4ea882e2d88f2a224d90d8493c7ff95810606f861d0410a26264ddaa236fb2ade8427b4e5fb500000009dd1b7f7a052f160bcdd1b3740906745f1a8489ab066ee8cfa08455fb293e311ccc409354757aa1ada80aa9488232150148fb4e791e7237f63dbffa200000000002036140bb226d35400000037f382835ca938f114df05232863bd288dcc0dbd185073284ff80d79b0000031a7342252e1c6c7348e7800000269681658409ac5a84a8c23faa0000009a47888ac4183903be3c0000008838c3c102241c10d87a03be61beb4a0d88b0000013caa40c1a26e40f1f1b20caaec683e2ab5ae9d9c68fe71054dcc160e20aae8291d21769fc1b0d51115ab863d9739123b2b306bde1ca82875d26dfd951ac5f83e62d4a3ec390eb0614c08cae90ed9c129fe
else
0x5346584d32800000dbbda07055834382555c8f7ce418afd889a1023e1cb30f103ad2018a5c2c74aa5cf73bb18033b44a9fbe09fe70d6ce39c2b27c9a26c4d3147deaec7b959eb219fcb11e673b63b4553723fa9523f9d84e7287df5b072e98ede8c676501dffa000008ec73c1c29d301e0917c5055fc21f9354e3bc705bd84a61831f80c1da22208e06714284fc881cce78a3d5b964880b9c325504fdf6511dc06be300000020d421d3d6b3af50441d2d33f802afd380ab0095de0000020ef44d621026fc33e0e206bec51fbce8a5382848b8f9f98422f418d1effdb6062482897dc1f9bb3edb4211c900d7cd0ef90911689795bbabba0463022419013e95b17759bebaa0c1bb0d844b3f26e36b121602b0a0da830b3809f28ae6f419d69087acc7f1b2120f74494d94b3804432e7fb0d120ccb54380293c51bab63af45000000723591cc9d70efa1b779c83b384dc9f17c53902764357a223ac9227198e27dce253c292c6674cd856abc1afee000000674b000000d233306eed7f4da4b7b4443f605a7f2000003953621b57ea032c5612293376026912140650e86284ee8942a180000011044b29709a014616bc40000015bfdc74be804fdc3ac1783beea6eb4e0329b0b270848e2dd67713e4a57cb6d8d0ea0ae724221a611044233e384452807ccd1fe39c77e8d80d0a8ade7090de37a7f06c527396b5454248d4a064e1b6231f6534d1800000361382aacd54d598c4e623b16a091cc000003e770211b8c814da4dd492e1e8a6a334e5bd606f4808b3ac293183a4ff9206f1d5a3c00000de4de064d1087ab436182a44eb00000052ebdb730931bd36707f06b744361bc2228620529b38a14441c29843708c512b9abc20056dfdd100000045e84eb1102881c000002de72495140293bc111da3647444454e223de1105f92a73c36104224c3)
else
(if j < 39 then
0x1c7686bf547f3602b298837f800bf7000000560666e3cf851b4142b283abc61f4cb0a9a0cafd6c8fdd9260659ada846331e2a6f50686babc345761729cedc04048000000135e2fb7c75791440833868932fc7d63fb5bcdb2141a7368983a18a510907090c5662368c120ec080b881938696b2c1d3ebae1e9a1abb4bbec3a20490b8edc0000139bfa9765596e4c015b0e339c112146041da88178a23b98197438907d1b27d94519811564887ac443da45754737df33b72dd70906d5aab036f587ba460c908229a0833ea087b00449c829e9e743c5800001db95070f0f3281f1cc66279d32343e445554311f62535a6140d8043d1273b04876d00f5db1104b84bed5124ca9cc4a802648882452c87c28aa75f5df832bf9d75962cd6310f481282e88ea223a4db237e01c53a83ab54099dd1104783be8c509ba0e0875fadb9b75ed39d22055fb07ed91487b443d2614095065e29a29980d5d8221fe1116b08aa607118d3179c11159c996be3d3c6fddc118eb224ff95661e4230e206a6d04fbd25afda981565c279800000441f8000002437c9632ec90b6039b5266efc992a441c50c2a6d37ebc4a1f57d1c75a136ba346dc87ba18799322b2a70b1c588de1529122f2f8a365980000004600a21ed806eef0000010adac148ac0000002775c44d7f479e0026af02111571d6c3d0511d0440291c818de60e0f3263c4831ee85d22e286b810f7a800001a3f1c0dfab1107084abca33b56652e8273c9cf5260b281ab8ef400000300ba0504d2587de237ffc7cefa0dbd33e5cd1104f8cbfd576fe23b0fa88a6a85079c741661adf806844ae7e1444520000006a4c8874a7c41d94f4e8a0000024daac00000031ea09ad280000074fa08253522459914a6c2890e000001534b8a9b5c19f460708d01e845193d40000000000110448d1ae681bfec72db
else
0x90fe37d62542de0d6f941554d800001f078e6616600000000000fc1de0000039f99bdba7d21b762b2ca0de6eb823581a1426b5830000004183828dde146f96266283078602388a70c50d84080000150daecd5e5120c904ab4018da83a7da0000029814437756000000e34c0a82ae299a61efde115d344529e339d02a8ae436b38000018b7c8147b8259e590b19c3eaec599b33439f0e5ff45136e0000056ad30ce78c711ea405c30d5479bc95c4b5700000088a771073a047d470b4c309a45815758aab9c2c5f845db680dae072f168f6983ab63855a4c445261b0e96f245831fe17714a22ff067d5586c75447728a64ad1d2ec826b3445574149e509fb38e222663be823efe7c36e0892a0509f49576f06ffa216e4493b1ea60f20000007fe95fe378b409d91d5e15b990d97b1146880ddf080000046322589be064ff83efb8a3f348afde1a1ec247191f5f140e0be7bef60ad2d4000001bf9070ff50000024cff0be9871fc4e9036045eff02aaa23c10f8e8258c6a790a9a3413c683ad91fefa730ffa477e31e785413ff63489b0dc6d890255e7918b528c93fd62402f044326000009f25db372f9a519423cae118cea4b37c047273cbe87a7630d1c2024330ceffe216f29c56be7752e133ab5eed328af70000000c1d32d61d04d3002c2084d9ef00000000000d803c144f5803601661c475fb6241c7725d03086808d33e3a797000000aa37ca6a54ee2991dcc8800000000003a0fc0e2fc0000007611e045c12959d8d273443dfa221d20ec94c826e819d1af6daa75767088360176283418b51602247764357f80000000000035f8119f3aca8ac4247d0653b85556e1e36d17aee89075c2b71ebabf4110ce04d39924a542f39b7bc438cb2785519c3a67223a7991872419df30fdca1250c3d33388c39838890157e4016e2894616222ab)))
else
(if j < 44 then
(if j < 42 then
(if j < 41 then
0x24771d004f21e5da00000029e4c14d3d45a98000000cfeb9f5b6d1449306b6184ef001df9e8dc0a1af86051a7a667d8455cc1d77c8b06d131c9641392238ee000002895ac9433512d4d8000009d97c0fdd2069fb0be3c08c35a3a5db10144088b21c3f70e30ad1c56896c8e817970102cd06df70d0e4d08b3609c9b319fcaf66581934658c98040bc2776499d9d24cdfb0b5f1a410981af461dac21ebc088f290b379e0e3da5d6d0c3f27019b960000053edbcf930dce11a4d33e1055406af0868f3935698000003b8ae56d128eb8da007de9b3b80171129d5d89ef59050c5437bc0289bf09a6c800002689f63abab142458a9a9872a9a224ad5cd618a0218248a65f7dd1d05c819e5426926461bf775e18a8c78917ea1b084105c2248ad0405fe21ea11fc71030f95075dc0c3f69e5ed13aeaa34d02113e132edd080a75ba12c5fad01d851881221dc3c00c3c5111601b4fac000000c9f911bd64b82dc935180e08a357ad0882bd3fdb8294cf01243000001e01080588e41243197d003d7827ea421dcf522985def35c6d8e391c65aee6942d644b87835737e01e3d58f3ae257c6992c60e9fece70aabd09d0d8d80e129843dc807cdd3e3d7033a9000000d0986153721acb526d3c873ea95da51031f7080d6e793c5484259c9f4c283d67a258060eaa40a94150071c8ff11143c1b3a81e78af4797178c0c273c55833e0000001c748a9aa43617a3b7a619cfc088385dd967114fd58b6e9a395521ba61ada48e0ec833a4467d9c384971427b38baf85eb403a0f065c5381b06c273c2202987ace78be2aa13dd400000110672536f0589987712c9e5fd00a2b800000bfafe8bce8800001beb673c1953dadc4d96753475aac4eb50bf8830e606e1cacda862d8150be39c55f5510ab302db300000019f97189df162511bf6fc3c85eababa
else
0x1bcda0aab9e313540f1da1c389c3ee840754687b8410f7fbdd72218ff2149ab060dd8910ea3a57821eca19d75031f541cf6129ed318b66906ebc00000e45ae02afba9224d4f024135e4386110e0f8035532b1dc31e5f314581c379bcdb7857544a831b5443d0a0e70e120cd0137143cb860d8d8065480ceb81773aa0c1dd2c40484c904445624b14815a6f08eb88293388f20b1a210b7734852326339481d2c7b76a1d5f35c1e4e916477000000483e416bae0000006f3c46d3cc3a5ac18d8f8000023b3722109e85f62b32ea02859022ad848ce78fbeec3612a0d0ae0e6fb92bfdc18dfe52ab987f68888af0bf9e08d6520000028e42df0f4a149fc748fc4746e8831b26f1bb8e0e229666418fd6223de1c46b0b52cc08b9ccbcbb11547000000183268bfac24154827bfc4415c1b0820d7cc02b2b991fd0388e40000006bf0cd8f62284ca6fee10000010697a2368f1c1c103f7c043de08b6b685f7e0be375811f8502af0d6ce0a56de797cd0d4eb477d4844f687e57a0c3ff1a1e78983c0429444b6b71fc6992cf983558e000007b2c30337c8a6336a22d8636d8abb9b63c7283f9f70675c9e878445f351deda34efa8b13141bdec063b3000001673cc00000c93db07dd1035fa8361a00e7d006857159b9cd256a0c19177c5e8eb7ac44590000001a566ba3621d71c80c99f066d483bfedb2354fcb843fa720cfab9bebb803de7117d010f9e885d160e0b96467f000000831e6202e10d62290bf3c54d92c26d476c6d038344485549d9e00dae80acbc1d919b24ed417dfd13323446dfa3d2e4159c60f8a59264b6935478fc79283d896d3602cd901cbf1add37e2292c0d693469f4a0da58449860f3b1118ed088364381a8573330076d985bcc9e3431d8f5647e28e72c837f4e1d2af1ed110797b883332220a10555388f2d04415e16551)
else
(if j < 43 then
0x8a34f22ab5c8b4e2291a18456a0883a917fbc00000254670487fc45fe836b08081789c5ec04191c289921f4cb887aaa6e9f88bddd324cb00f3e01551d0808711cf443a290fcc784709a48984c67ea60dbd0218991cd5d449625aebce3b68a870dac97f3c415801b0fd6f2579302a8749ccc0fc50743f17165073824667b60000010ebbc3ff3a0000025dfd13031c67bc2192c27a64b064712783d61e6e61fcfb80000287bd2000005c36ab6475dbdb20388994d55106c3604456a8fd05509a10ade9c422231148b0b5f48be25633d601d5c3312cfb7d6d018dce2a9d611df0aa0fd88d1b01d2db1104cba07a4376bf041db697f7000001299a0141931d272230750157c4438f611d4e1568cc4410c058a50d87a000001d832ab7dd71c1d0b65e94f27468d9a21c443ae3388cef20236905da5f4f93c444d4d250e35c3e4890e85ecbe883abf7d7e88bde6df2d62f47da46cda889b74000009cecb1c6528e93d0383611ddfb9fb56c452d8d9a0a82924774e194c31468320bd0ef179cd06b66844352043f71a1641d8f24000001d5d548756887b48d67413bb8d1154b830b805600c9950305c77038390273e21b09f54b0fc80f907d3320df9f1147e27348854d1873746434d006c32c4ab32a17bd0e04f3a1b380ec580d6bb067fc861f007d962f7c8e606da1d5bfc327ea0d9f40614d88c71c98ff4000001de3904d30c405d8220fc7a77303070e797f80ddd2000002242b406be400000281ee41e76058140864901fc590c4e304c1780e5e60000008a2785739423bd985d6480000047deed40e84cecea9dc5c0000010d431bcd586d260981be3b7b711df401f9c4000013c2d2120d13ddba400000b20ea06fc70b22f800001006a27d67c0546e4000010d5ee8e850800000e1fbe23dac064ca26a8dc21f92141d45dbc633772257b8edfde8
else
0x2ac20e9e2467d64cbba300000445b6e4b17b324ee1d259b23f744514c681851a0e592f74190ffe241d06557e8a27c4000000c19525a46c72634cb52c0c2d0088c98235b80000011a401c261035b784dfa80c1ed063fa888ab456580d279a35fcf196be24dfc0969266a9768be35472218fa09b06e52366eb01f6071469413af900f6b26331c220f80a16900f6a0f326a146ed1d1728a13ec4456632add6cbd81063884471cef5fe000000ad35c13172045b71ddb5019bf8193326e48b1cbf70e93b80ad42221eb34b13011b04441c1173ac0000037cf3843d18816c124f578a26a0183021b0f92ace1c6ea9e64b1ccc3e686afe37f6c6129c6f6ad120a2712777011e6e3a9b225bfa3c8f2a77b44163c4716d2b936bc1c16832ca0534d18cea28555b502de21554480000000000989901d260973f8476d6600000158710000025035c0000048351800001534c2a8aaf0d6e43d1b8418542a0b19984ff00000020fd92b3861efba126e24c8450000000fbc206b25035b96ae7e88acfd88a3984159622a9d06b58314f7000000000001d07a85c9719c3f0741210b6c10000006898651cd91d2f7c52b2c19d1421ebc0000021eaa0000003bea5060dc0cfa05425ca229da0dc6d39a2940eb3c202e909a6000cb54d9d0a2368408169bcdfb85accc00000144ef8aabd8405581b09c1147886e918155c40000093b508aab1c18f991e9ab061d286cf64083b4231c72326d294fd8763fb0658a091df145c5d1e76cdf59a111f3088a39013e61105b8026c4f8b1e3b3de23aeb1157803ca8835f1714d8e00293cb77ad7bba633eee0fc4cbebe8d9b9400d7980000006af9c5139c31c960fb9ec632a81398509eb09cec63d32c27c5bec79de660c6051aa6275aed758c11d7903f7e04512a0e52a174d614cb0c5dbff25d851c7ff959bf97078023f92))
else
(if j < 46 then
(if j < 45 then
0x7a6db887ace17f9ec6fd11a73704d2e96e3c33e4c001de2a73a517d9fe260e815cfcac23d485de20000003a42a842e4371560e0e44ead40a9b2c000002aaca0317980000015bc6228d8421838883e41c1a4a69536eddb2a4204269dcbb4f60ffc2ab9a7c367a2649226e97b0896c089b641029a41343117e9000000864a786d4c026270ddcba1b0b11c475c9fa0c40992c08e74e70b0812f06897821a0d1db678156f55ef1a3399f4eacc02658c7492620faf35347895a98197e42b2c31a6c939531de9b723d9b40f5fa37b65c293b08c4ff254d194f109979f255dd114fd5910f3c22728135f479deabcfa400000083c06352fa93ddb8299d0e5ce6612eb9d243c74106679c2000003002dcf13340c6bd00000352e3868742bd0b8531188000000df2aecff277461976aa4555c0000000e3cb3173610c9ae2b486148d700000278dba4089f669d5000000463cf1a68b022eb80000027348efda411477033f11de31242f8b838d300000043d8c2d0030000008a32c00000526313619c8d0049dcf2014195746fb837f5818d52587e7542cd0c36c4591a24db8d00000000000fae8a83fd408dc48b1378711f01aac70655e36bf904735e7f49635af8365e649452e89c259384180000009d97399d900000497f81b2f84160b115a5b88928000000d7fc69c6ce08e754000004e6f02e9b889f880000010ddac3fdc6031ee885de4220b1119683abaf83cdde87c7e0d84c80000250fdeae9e84eae9493af451374f83ec14275899b0cc99e6383d628c04c45274000005558c3675d3d336c0000021eec254cf0172805139a21e8410b5e8fb3c95ba84000001145e816334aeb980644c260f7948f0c749eb2caf51c44e2fcb04361e425af63729b09524c4872b115e8114490ce7290b448af9ee06ff78ad3e862b961a3d119cc7427b3ccfd6864cbf
else
0x9a7d87c76878aac865c31016e05aed59b5ab1d88904c7e0d0e90a582c48021101eb2589d50e078e4ee6111cf0592514a74adc58f0000008b39043df6034d100000051b4c445b4419d7364592b66ce1432403df817cf9130c1a67562000001537e833e5051b5b00c9e47ec4c1d6104413a9d25c22fb9213c6cb9be60000031ea129fd9018f7cf7ec616c6c00d224781c410fe6110ee9c6dc5d19361ac8d039dc009aba2b75819d7d19cfc31bbd49814605ae23e8d08232a0781b0a11f9035d58a2b18455ea564eb03ae204867a6d33a3b0f70d5d9888359ca32003fa7000003382a5bebc0852850000002efc1e9f16223a71156d9ac9bc293ccc4cc234589082b30283306639906343a9730c4271a129d111b6c8307fa0c90c1abb30adf888f7d000000de4ef72cde80000003408b8ef909f5d0b2f40a3d049f4f100000052a0c567782209610f5a06c76c0c538000004d9032c039481860221e64eaea84b2048470a0caa0000000fb77165fc2716c51d2513847c865f7e00000216ca00000047f560cf9711cc9085bb8665d22289e00000035bce7a5940c6971a245818b1e6cd0cd4c88144da8b13501d72c9a17c2aadc8f9fa01117078860099c511e4989d9564648688a42051322797f2366b376e59353ee9559d26f63d00000396aee4e17e4db977c57a8d2a481b79223ec028469887ad0c4a9012728118560307f0713862c572065770b36c0a5db0222ea1426400000018d44000004041fac268c19fc00c6d20507901364813bac65ba10e07e888bd07133202dd49e5e882fb18449384cd8f10f76853bc4a4750937ac44aa5b9c7d069b32649bc110518b170c48341151e90634b0307341fa9cc5b8207e4e4ac315d3be4000008e0e7831f550c5e8cec9b1057e800000aa386d278f087e9918fd90b5fca33ef77bfb1b7c6c3573e553c5)
else
(if j < 47 then
0x6b6b0883d970f260e0d72bd38887adcf76083939f100dd33ff6c183dae32f28e0f6871eada2158222b120c64a2e94042bf2239812c3c90c0ab889f360c9b0153658544d00798e409a005c6c834f7dc63c2ce1f70905eae0ff9146ee0000032a21caca1c675deeb8bc0d6ef499b510e14621ea37c54c843f0019feee4ef524f4d84d384000000c7e9110eb37d618c2be0519121c44b06b63202bde221c3000005092ec54dfe193cb7a4462ed658fb6028ceb659c628d0f30f79e0dab850d6db835a6475d7a1b7e25f456880a8067d6838af91d3f10e225d27fec21ec52accfa14a605eff836c8f947779b6a201936605bc00d8671f2a4a629ad347b1121620533dd28a32f4e9e111908000018214b3cbe3865e488a2c0183882228a87b7a167aea22936881bc2dc3bc76251b87be3a7dd0000012c6dc00000f39a71556b872a7c1c1b70deef099dd83137c5d370365825e975810f7ccb51d1a18e6e9639d50ad06c0687dee75c6f831a80935533c0f4067fda923b1d5d9c0257812f7846ea4d33214388b2000000406180000023ba700000088b0e22b1f0b0f30a3638326fc151d80c6947bf5d813225421f42788c000003b733881d9a2228a06b730ea6ce6adb43bae48326204e7f4445487e2a33f9299ad7800000013988000000033810ab0b3e4c00907781ccb055d8f0e2eb477fc9473680000044d520000013ca6e3d1be2b4ca000000e22d4555f25188a0d54fa9736800000c0ff80b04639e6d08a390fbd8770cc8094bf5467be6aa15403d12a4d14187322aaee1574dce36fc0d65848a9409a5f0133a278984228d015971880b0026d3712dc19374dcd37f8336d403cc63e3c33fcb242bd62b01d3007340e194d81d944258a12159be778ca8bfa1cbe605c6e835afc79b72241d75b64b08aba4451b000000060ed9caf68505ac5b888
else
0x705e07c7d14ddb8d44eb1d0602aad683a558409980d55a811fc8451c00fbec6ab458d94541839e940f94bf9d925d55549601109700000284e30d70983a7920a4f786b6641b73c575d9191dc5206827c5543fec91ca6903339c7f7ca3f9f81d98d91c6185097a0c4af101d3800000269b711aff58accc56e80e5704098e1492de880a540bb081ff9c000002cee483d0aebddea747c64cab145a7be544c206b4e0ee3202b0c6000001c46904d61400001055a448059031a94409b63a4a419f5c2a98c663f2e22fbb277e8a6e268685c6094c209a4ac4521c13ed21aadb1d25987d6b0a0178241ff2546b0e9304679083eecd18cf5035e3de99d4789af491e200000019b0e2a6ed052d4bffed01b17c0000088b4b889aba22d2c000007f8e922958db8f8a220e411d6f8b3fbd19fda4881f45a040e22a018db02a6c1064f30684804effc09cb663978800000439e32ccd9603f30a9a50981dc221c2255ab800001089f4cb0db09a5b85babda4f98217cc027e2a2b6c444194436cd0667684df4da838e9f4af1014403d6ece23d603dd8027f1896a047612c4f9682cada1944e53ab4a7ade10614524778800000242df271fa4e9e1c513b62aa960d8e0831b04bf82a3a0df15cf508e33435b76094c036d8622ef84749ea8bdd517cea0000005e54a776d20824daf16f0273b0b74f6000000000012e03e22081260f9033eb0939361d9ad5456dcfdb58183e0001121c460bfabd0ac1ec4bc2c1535082f2e8bf60220a1900000076f68000005478d645e2472bd8000004fa71154500218f81a1a26d5ac8f9ce088ba1153571f3a91a2e7189be8b0612236aca40e6880be818758e2acf66e5b887b300000047bf51d4540de3ad23b161da8111041840b142affb250b5538eb29eb004e53201cfc120c38906d8361e2f8aa082f433b2725d71e69bb93))))
else
(if j < 56 then
(if j < 52 then
(if j < 50 then
(if j < 49 then
0x89ea0de32c00000000001015e8d0f550128c49a9f0adca000000183de061b219763818b84069e84769d09a55000000749fe2ad9c0000006b6d8685bc000000ee87157f7c0629c00000a2ddfa6b6290fd6c2367f06270b077846cdd221ebe03e5d0deeade050e4ef2e1d4c203b62cf4cb612aa67c15b80beb8079be146f304d62a8c28e4795aaafec53c6592b0067c9929e0fe6e0f6afbb8ddd3d26c81c3b6330326a5207311e1911a9ed800000087b090f1a0d6db0000000712a1b893017ca96ec8d897de531760634d03835054dee60de515578177a248339310df407dcd0919445794a0c29711d69000000711a619b8d1116e83be494764e14ce87ac4743d3c0d799494b9f0e0ea0e9274d9d5c70e300000007271d142701570720cfe80000099bc2134bf06fd1191ff5e995726e8404ebcaf42e4acdb32a0810635783070000000efcee456b3918651821842418d1a1c688a820447521b0e3938f2800001983e6eb8b405f710907cd2711a95ec6064e549c65c0000037c4606bd80482d0687d13b1f61c7a680000000000000002fe8347b3b878df6ac1c43b135079a5c00000202a712f1ec6a30c43d1614c9b077e9835735a5d95224c888a7c86c2f426b792088605dd294da19c453c156a34747d89d6f87dd3221ed5060fd9c1ea18af56141a85414c0327dca4d989df95022cb0132a5be930a6f06036c4872d0ccb648129771d559ba8e1c45bbf1f3cc1a4e80000012421af16f6903cd8ce7b03810aa19120e0f7afa3983616a1499a1a1fb06abf9635a833e8b1145dc5a72407998149c53f08483832800000e28b7000000e971820834419f93fde4031bc269bb09ba2385d57c9c29418549146e510f669bd6dc47746edfae0555b147a1a22dac403d87a4c2277df0195dc9ce89159689f87a818dceca8fb00852371a1063bd09b4a2
else
0x7d0cf1e75a443d5c25fbc000003bdb35863ca0c1f141fac0000004c9ee00000063d4887b38741d40c6da11062081298749160c1be24846888654461ec0d7ef0adfc07ff5c361a60f5b8843500edad8b3df2f93e01f7c2ca0aa664fd8b80b975bed4466703334020290154da8000005f176220a5000000ad23c749cc0ebf417d69b2c6aa22960ca9d0528c20a8ba41952f3e4ec04e74087a0850e02be488a3066a4d714627f820399167da9f3cbd0a1b2225b01c366887aec1fbf4aeb30063e6087a80000001f1ec4a0d8030730cb1e2f36831fc7cb98aace5918231880e92403063e1077850d6a1d279a30e541e39806ffa1a26580000079a426685da17731c76e8673801c08d0d86c943fd47492c00000017dd04d6cc1a1e0d97bc09a4104820848394000008ec6b8e46f8053df203b00d8493492785445054bd21a1d5000000441f222186234de841fbd027e672f4f0687a4e676c443ca16ba809b4b8be33ddd1d40bcb479a6d04fe701ebfc000000bd5482b2447b92433e9006ff82275c56d572385a02b5d88d2aa4000000c18e68d534f579076b7a346cd5da4684c64c0000013d73095a41fe7b252f720debc4f343800001821c600c54465e7009b0c2833c21ed21b35f8000017c938223b410f72aecf7c8a28a0f3ee88a6c0873d824bd806f9d786c40d0f701bbc2343ae3733e835fd1b13d022a9d1665b0a9a18833aa467b25c3ea8eaae4000001359c6f7dc83e37075f2022f8f000000e26281b52c1b0f107e5d8506447f16b0d79584f76033f642734acaec088e683d22b119ce2ecdfa0616e887a4820970388b552ece88ba228fd9e24281840ddb342d0b9d140c1fc6ff4d4b87348174a0cdfb0000006c79447d2303bfb39ea706b7c035b200a7d838ccb2ba6b8405970bfb49cffd1ada0d546d216aec1d93449760a593e6228d8)
else
(if j < 51 then
0x1015e035e91d37c439ac981756037e303bf4633ad9316e30000015a886409a71114f8000023e1086aecd03ad400000045694062d66faf7be73246df282828f19ccb18d980000001969d118d503276021f5875cbe06bf108d6060598b2e19010f5e1b5b80383c82cdc10b87580000000000b82851d3a3887b4d4277af939e1b1c6c762a4b96b0383e20000037ffb26a71e8938f7745f2bcb748d9f81d8960626546967c0abc83a0c275cf6be7e207e15e53067576d75127f4829e2035cb0b9798883181b9ee8accf7b4750326d018f370bad861975a24a9d9c3680c98b012cc921e50a63a4134a447c2308ebf0000001de9883559ae0b5199ddd0c7880686c8000001e744343dc06f698736b411d64241e3432de8883dca5bda000001124bb9c3541830b1c0f70ae9821054c76dfa00000562f4023ba13eaf8220e414de0203b1ce7c5a060e42fc5000000198356df3d5000000eab59ca768134da06cda0cc62971b33050f26fdcf00f66a451fa2ede0878ef000000707720000058dc108c60d8d7993e4e87d7f71fb51c565be23eab1019d3ffe48fe02e1be3a1d3df0ec2dc771960c6e292765a73b3c1c122155b912e7a3d338c43dfa149f2153624552a921b931c5cb1c4c42cfaec443eb26fed9fd6104028437160d91ac01a4d0c4f16169121addd9f15e08ab41e8728224ee2ccf9087b8c7411c0000090d74000000e0fc2e4fa936fd88e22d8053773e7ee4efcf93685800000a66f206f658000001c15d019fb0000015d7381bd1aa10cc0c6e91fe9021f9973d4ad8144680000012926220b9260630d0e6c4436804df61427db6feea4a1024f57983759af9a3c4458a389d001eee0e9f1140d843a791000003e63d800000faff70637b90b3e81bf6679efd06cc4800000375667c73a7d75ba357f0361cc388a0987d908be6ca1ba2044f8
else
0x7ba78835efc8d3d6a2f7e9c543031bb4b17fd411f51a1ee1bb514223fcb83dd94ef30252186851abbffd11de69302880000000000885c10883d05f1a6016cd1157a888a100000000000111cdcbbe4445782289fc5c1d29aff1e575b93aafa000000b5ecdbfb840ddbe2ebfa030af1216e8000009fb5589ff7cc1c93111fd15572883e6c4471836a5b80ace833b8c1eb341bbfd527729b4f3428d2ab88f08a0fa02ce2400000507903c2fe9a64d01df62000007cb4488eab837fc41b0821db560d0e496cf4c1adbe10763845b941af9a5c3ef2cac8088ee000001315e810165810f40445ec194c36b9c7887a9e6f7be134a5155548d0eb443da83439e0f9e60d0fe419b8c0cfbb655654427dc5a3d40e786a4656c9bf554b3a6388d4246d482d47000000e03c47b478000000000000c8ac64170048350ea30480896000002d0220ae94a3a4ff0000001aec450d56811633cc5d84fe5596fa40729f10ad313aae47415c4d78988c5588833c00000000002cad349be9ca4d143f8df655e715cf8c26988343e006bcc33f220541acc339719d4781c2a400000502f646872855f30f1fea0d7b413248031b648c36c163b8236a981e524185889c8488cbfb9c88d476f3c00000000004cd2f56579881893060d31c72e1ce1462229812bce04febc869d4b35f81f6f602620c687e20d6fd965632600c55610a100f154aa3458eadecb96419cb518bc93aa54711be96e250d6f3831bf5b5340dd6d90add786a2cc131c491d821107c8187b4023142a3b511079135354d2de8669381c52daac01c205aa344ef1c36b28805800000149ff8be57427f40715103898909ada49de2d4fa48679b31bce523432c741804edca1bf480372a58fbbce4e9f021fb07fe14371fd31da7543fc80ea604059d2cba16fac80757550cc073bccf28026888ad062d8a1dbec))
else
(if j < 54 then
(if j < 53 then
0x419aea42629e5da1250c82a3d014da5c1833600000a2869094a38bf416108f26f7d404c7021ab52404de63acf0d0e25e2374000001fade06abac0000095a3076e4236f25de9fb424c81000004d03dcd4fc11dba807456800001a55922abaf0e5ec1403b1e53e82a6e010152a2725c585c24635254eaa1d913a7c9a4eb8de110460542ac43dd281d99007d381f3fa391f4055b00000014eeac187a80e0e9740ce031f453253432cc4089e088ab5c07b62f83e54259c3ff25844f0926abd077c10286e819d271c4847844d080a0e3b19d0a5a006ecf8e82092bf9c1abea53458b6be396edf40f5fd1d2fcc453b0569440c19f300d2be9e38da1511e9c7017ddafcb6c43de80000022ee18e936c4434447ea00e44c899f91446945014c05c72c8376c445613e4fb10f52a8412c4638c21eb17a1670e92dc1df1cdec81027c703e7ba7c7b80f3918addd06c3094832c03ffa23055cc7ec000000d97bb1b3cec50e4c00000455e9089f7c6eb71f21dcee4cf06c45a73b0c00000100ef5fcd400000266f4e230d58b6ee86eeac467350d3ce2b583c9439dffbd4554c410f593fae406738eff9c81d5ec29a27c00000f4de6153780d0e045f1551fffa20cd2b87e426258a258c4000000326cc0000000000064ee000000e783a867070000042fe8c0000033aca9cbc58d627d405e601cd211074b2aa1474fb4fc2de10159bcf394d6be433aac0000049bfa420d4b17fc611460887b10532ba3b89c1a876031f26495c6046ed1ed530b139127780759d906ac704d3ec5a76600000067fe9749c400000fc8914363806abb8441dc24bda10f45031a2844374343e8798513b2ec0eadc80cadb19cd4019e0934dde2f87b874578306097b5ceb4ad9000002491b5cd37c226bc10155879f3c729dc2a6b41ff4a49430c183523a5a51f8f20383b0183d42f5a4
else
0x72d69c5cbd939d54202fd1a4750bfc860a5743c6d1081430163c9f679a9e629090e08a9a94269deb83fb969ff333b5c000007eb1e8057a84d3584433c21e9a08a7e089bcc1df5a436ed75a4688868c0000039d6a0677d48bfc8085ac875af097f18e894622934135b05e767ccca44195a0231f472f4c848f5c187501b0e40dddf06c344fb5b6000000adc0837fa2361cd40bde0d8f41273dc441840c68d07c66080b60507da5169f06b5c860bf54686ea13ce20cd2085148831be51b5fa1b7f08834418340a452526df3052794693ad0d5d400000306fc000000fc8e010f5a1c1af87bffa0e0f69ab6800000064d6421e82245918372d46e53524ce7000000aafec45d0809de8066e9275aee4e7a06101a6767c035828c4fec3a0e700000033b1e48b9434dea0851080b6f80a3101d2f5660f338c7655b23221ece118d42a3c2c2735c21efa430778a9bc400001329e901ed78000002d7ca8dd0a270a20d0fdc26f60000001426c00000222994241ce251e805417845cea52f01213772e663db77260000000000010bc85f11858e260dd7747a6845269adba9b6c8dd0bced639de49a243189698a9a20000000e1e1067ee831f80a28281499c0a35eab158d5cd4e3a5ff03d66840b9c441200d8cd390ee8e977066a1e222ec077e14c97b23830a21ef5000000e9208833b68b8f70a0f43c26e4463382f7f20f5c5837eb8000000cae91c4d40e3a7c283c20d0b9000000cfbbc1f39a0d6c040d929c91f4be676df5a6144eaa11a3c455d222f9d929e80e93d63374c86bf41c4518000004b9ee3f9ea7145706e3c4000000000011363869abe3691c344ae0000013c729f5f7a0e0e70707abfa2b41bdbc7c96c4fff5832bac00000df3c89b4d448ce9c18726058c8070748000006879e0efcf2b181000000441bb1e4ef18ecfc456187bf4c220be)
else
(if j < 55 then
0x6f4e7322f5800000354a10d6dc18e2040000021edf1026180dbc681f8606cd510f44813354000001bd8919fc980000019fac2f29e0637604d258d24f8231b7110480263a019bdc46fca1a0f7030f48445ec339c606488bd6ec854d25345a79c65989bdf61d714419cb11b6e88eaf4179af114ba0de4982d74e6fbbe3a4db3f405145e4cad12690da66e365b6eff027354221874c6384736d0000002209a1156810e5641e362df58c5ed4c2c5a6400000388db04d4d436bec0000009ab01a1f7b6e61c26fc4f91db061f03dfba50f562098b8985d94f7f287db40e70e4080e0087a8875d82a6d6d0a46683273c1af491d8ab0d84e8ec73539795241c2110df8182d092bc8fc09f7577c80d689a9380221cd15cdbc537f84452e264de35107087bd0445dafdef10b5cba7624a4b354103ca1116900a2d906b4a1afc91d041aaa0941b7ac0c6a905dffc9ba583337419ee5197710cfb2d3ab5c2574f529cbc452862972e5225f07a61a5a7849158e3d9a56d0d8bb86b045fa0c8fe1120df81f3241afa43b7aa26abb0268183a5a4222fd0ecc4c9426d49938fe59d694df037730f75e6000000ff740000003ed0e055c40627cc38a51eedca239cc786cf235b903d71247bbd1d74b248ef8c95324c8417387b9713307df324dacf110ec88939c2279b100c24fb6611927245357350d101460ae331685fc30d5ae373da9d945876d6cf0dca1d5cda8ff1c0000022ab81a35cc987f800000139e211d920aca327b3e6343ca142498000021b97a3a5ac5e6c899be38451f400000000004f2fd454dc93b79d06ec50000000832c202c9596dbb7bee000000df5fc1544d000000a7e1f26eb14b8a9c2fa108ad6a4359f489da3ea744c4df4224d30a0538306e51657224bbe9f25780d21c43dc633ebc1a378c81224379c8d91fe7087b800000947b006e8e
else
0x345d41e93b40000010f9e000004893826d3ba12bbf2903da5e29c0000000000422dfb4ce2e407700c99d79045af93d46a1d0086aa026e98882f50fb591d8c4060d5ac235d82f4e2a6ed7995a86ee8a28d701f8f1000004453b400000461c85688daa2c1040b162b1680000020efb475d1c532fe11b53035b3c5e7acc6ff776d7e8ac2a07493a0d88e471f5800000069bc0000084f4691868881bbc12fdf5d4f506c2de7b1a2339b30000012fcc41351f1e6ca88b6b030f69e9970771ae772784edabc5ef24000000704d2286ae2291000000144cf052630a3ab859fba30a5f8d8eb08e3f2034fc674de887a0d4f1fa2afd49f262b0a306737dc000001b9cf84f978d9d0e3a5c41d27686ffb80000022ae6431cc2d02941df42910b876e460342c53754000000164d206c380eade8659900b7dc8547f0195020c28e19cc9046b182732032cde1fd76c62a6c025ca0000000000381a8db230342a9f6966011cf80193720a99d06b619d671c443381baf8063de06be34361e01b083077c0c2177c2d710436f9108444717cd71d6c149b40a4c2830a6cda7623a0f8000000d0ff81df94e7a9f196480a122085a4c9919d0f0830707911d9e6a665e3685c864328000013cb9c10f56c706801839002b200abd5c27a5826bcb47ee7546ed991910000002e70106573080bdc2d7989c0da93750247b6d1288e356b806f54b0f24c3979b144a1458f0033e5c48519109b700000030a68000007d6ed9fcd48907a444184062ef1d3cf9517c8269201b8ba1a9d8a563383ff24223c039fd83b4fa82432938ca1098dc831a4d2c12021ec444f3214a31043d0c2fa9d1ca5d818b6035f78000000627f80000055f9e1c00c0e79a02c25499dc691682020cc887a7c09b7ef9a8a596ed0996c520f48b729e067d6497e323d3dc000000ec7f1da620243fc070de)))
else
(if j < 60 then
(if j < 58 then
(if j < 57 then
0x1c4721704341411e203905586280000027fb4228f61f4fd0be31c509ac042d4376350eb03a5b9a004cde06b530aab50d69fa035eb03955aad4881837c6bc2206b6688824450f86202b9050f58f01d019fb2509c632f27bad699e19aa0c6ac5366b09a9fa479fe1af99924fca92ea818d1a236de033eb03d78c18d2a228211530545cbe1a5d8a32eeb48472a7f6ec257f547aad3b5ea800000000004a2dc5134c03ca94000001b88955f2c828bb400000220f9067f6887bc22297f3f6e04fd4c0907928ed8c452a410566480f6c00000148b820f1ac8f3d89dc7a70227189e18ed6ec7aa0cf4c919ef630906a44459a88ee41975300f73800001238a9534cfafb7740000111488000004fd70c09c8a00000509c10316fa4e1f41518b10c560f302d629c01afa64fa7f8ec27df5f9c575f362f6e820a88237423a4e60674e0652c8071fa4d46d1497e0e937062bc2b1a9256ac9035d481eb242028e19ce9c8a3bcb739e48515000003db6e8b168937bbf000000cf66c3719800000000003ba666175822948901a5b16571c483fc64fdf169c1888bf0361e4135837cc6388aa74483b202989155f08307c426b160000007fa780ccde4533c3b0c9075da8dd70876d041e5db08267085692271b00b4e50d6410000001ebcc59e5b416ab800002229106d7b53b9031b23cc54dbcbbbe9992ca000001219d6500a2432c7c59b19f1db6389aa02c57800001b852e224e4595548883ee4e9ca0000020c50864f20553441348718ac4ce520c00000f52c9111cd828bb90f2d6000001d2e1ccf3f46564cc1b8c673498e1b8cf0ce708d9a01a4f826a9444704f95ca1666a1815e8453fa0000073e46bb87667bf3cce0ee761c39292e4053ee38091000000aa2b83a53e000000d84c9eb3791a418013dd382f1d1f3f806138c0fef15352a910fd0c99a3898d
else
0x10f72880b941bf34231d112d4a0352a0483a4ac43022c4590374419575189a6000002f93e000000000001d2cf0000013ab349583b8ce7788aa68685bc0a0dca3741888268111de2dd58231f5851afdb753a000000000040935018fd80d0ee0e9500665e8000008642b0d6f8494250c90bc8cc471cd3b07b064529b7376d80656f189e941570aa4893000004e6a459c11e000000000013a285246188cda4780fb1c0f9d193222f013986cc19384c0858c1249400000033fcc43d6e18dcc6947312d9a964f353bdf9179c34daea81b712dbafd17c59b2a3cc43d88ed2fb4a7620000003817b145f22b2c0a16568675ee99448053d89d75082932c1b0cd4327e145781a8fa5168bf3d03c4aa7e818342cf2880384a811384405041af906e0fc8a12b8243202a6bc0d866a18aedb2fb60cea0159f2a35a9537ec8e8d8a19d5006f304555543a5812d8ac0000001c176035aa3ee271dbad84458d144e600000276b300000086a7d1215e11b6144ef320a6c8065551035791bca29f65c1fd75c9c70c4531a1fc92536580f777004d4e1d2d02466f06aaa1db9d0241e29f253423271667c31e0bf12e6886b74c7f1b8163ee0d84193cbc074fd2acbc40d5cec04b0019596000008adfd87c6d047de8dfde800000028b0453984134f200000445b3c1dfc6267d119cd5087bc143e492dbed983d221ec5843dda66703000000b1c0471306072a70000028739c1bdaa0578d005cea196a8707e40ac336b9e31bd1101bb723f8e46dd6b04e68429c6065ae614ddc3cdef84b59102c9624d772381b8347924069b217e93fde923db6600000065783b7fac1cb1406fa34884129d170000007e3703b7a88000004053e226ba2c44f444f4009945143b88e0c686f7186eb286ce7a238ff0406e5d5d0c21ee1099c888824e63ff324eae944489cea961cfea043f6)
else
(if j < 59 then
0xd84c883e0418366b1c9a47f7808c6953756a8f44f62bf8888b6c1831a339f7017d928b5ac0570e89ee9027f90edb0911b444e6df000000cfb7800000000004400380000019fc40000005a7013668844550c6cdb343cfb8e6dc1b136550890416eb2f2d8d51f670a0b5476b0000010f7132f1996cbe90a1fe04058e0db9c000004737a50632a000008dcd11eb82949f741aea81c585018a302c13b006cf928e5c0538d721d8c79f2111d00fb7d1efd0a2d39e00000087aa5151c539b967bff1000001dbb9240df40b8f30f945407b661ba92925d804d3144053ac19c0465c41803495ccf0e1bf1117dd8f1edc0f7720c9c81d2c326d238359642bd4a14266c1bbf8213acf2bcd893ce009be23b7160f4aa1e06c3e5e467c99e289a50da4583832c62d26c8fcd062268e9f313452833e93117d7c9cf2215dee753cd0d5edad56e4ce7b00dd965c0dc897e412c7d403cf226c3097bbbc21fe00f1e40eacbb112cc43c04768ef206f6139b5d532dc111883131288a27c2aff28af78138f7034f105fc9f355d706175800001bc5b0000002a6cfa4c10c4fd36102952935e8883f03bc244f58519a048000001adaabb7a46afd61e71ac8a404a597f4dd5ac2eb080000142ed717d4f8000001f5f0328e8117c717ae0c0000003dfc06b478882d00000090da81db44c2fa69c3f965671c06ad6831ac8273d21b088066ec898248455a6f82f12547d86efc40000013ff1144e480da04fcb6d1b6952cd792b323c73de822fd07a86b0d0ec9903ce59aad1105f0a5054189f8d74d05011e83f1487492632c9a4f196835b1454112d21a06bd4b199ba67eb441e0ea1116122feb49b263114ee0636bad47d843d2ac94810000047bf603ff4c23aab4c140bd33f040328419fd49bec0e931444144deb8301e428ca03cc7b6abf1c72cb5e000000189ce03c8d
else
0x152533b7310f4b60753ce439c81b8eca7c976b2de49edf804168000000a798f101413077f9136b00c24c0e4be476f29b1b740f195248d60fc6540000000000449a78d0e10000006fc9215a680812604a2100a03b793fd8307007ad960cfd9a28fdacff080687a3b0b59e5cd880b3c18dac241911557a0fba0470f9a0268806ef90965f4e2d027a3c41db700be2c60e108000001104e0f822c405b0f9fea6cbec88a2fdb23860000008963a4026c0000022fcc060e688dbd8749d20ea8a15578855b7819fba007e392ed104ea0c4159c6a8b6477701b9ad4475f6355ce9844424f89c3ffd80c1d170fc988a35404d7c30b3f4807141e7fe03d3620ea312d709c0dfe5692240eac05c57c397a975d40221a50add901fa08687203e3d46aff8c90a342d93e045a30ffdfc6762c483e84404e7cdda5077b5a69ea116a91b034890ad8000003a7f1456144e3e30445de85b5c0b0712efe5c13528232e0055fa4c83e8a01a0d71f560d71a7b8700000032ec010ad4195f787117cb96a7064fb0a2749305483b80536852856ec988f14cacc9000000e93a44514821ea117c648343f41a99a0c6dc6cbd2c766e440518fb4d309f5d29e9dd1ef74f269200000011b7a46f0c794ea2b1d4888298812eed33a01d25a2a2aa674bac00000251762a0008687e4134cb05f7e1dd6d119bb43c0e60000017660a7c7702229b2fcf3104b7443db62ad451dd2783cf60c959c2f8ad0815b8fb8ec447b86e81c15361033b6da4749029db0000011b218409e64355f5242f115650483ac1ffe36dcff880a9550b762e5b711e798f177c473d5260f87e0ec000000000007e56e7ffe682c6cc6fb34255a82a4be037a2026b840268e748ea15876855546220811d2ef2e32b0da9cc260c423395b12b18163820c1a611576054edc269b7405eaa32e440b76c76b1016bc3))
else
(if j < 62 then
(if j < 61 then
0x10bad088a3863dd80972120c5496c61400000d5eb1111430383b818536045f70d7cc08e614015bc0c6ea27f600ce64588d94220cb5b1d61d6d7d7e55222a8c061e905070893dbe000000d84b0b22a400000dc2ba1d74500bfec46d9600000871e31517e059ba0a83e81535711d872323aed76d3063660000004850234bad0a4d5a24094b66880d6ee0556d831a4919d55206b02aae58568c97efb25bfea19fd649b70440520000006e87e0ce680295d60cf9f6944902970c806f40d0f370643941ef03575238cc1a0661033ab199d88231d48a3481e470c36fe243cae99465c89208000010b2dd2b175835f7585578a6ceb836eeb607b05c05c163b8101c6088b55b2392231c10a4f2b95fc25ff3622fa6110c30e23d84cf788537f56f698977514250821e8311b4b087ba66590d33ad49d37f320b968eb0d41bda54ad885d3e08454e855c645cdbbe52200ab108aca460a4b88e36db8f1491881062fb087bd0445b49c9b40d77e15ce084511e21e9d01e59caa3381a7520de892aa6510f6fa3a7e85d5a78ebc5888a40441d2418ef125f104f744369decec8500000068bbc000006f48c84a42023ad8000002a6bf8c4c4c06b0c9b7ae180910517744dba88c344137da40e4d2013340c186192a71e069a756b00c56621e9400000031a04607be2a6cf3869d1670ec000000c3a642162888a5944d711d9cc1116b849a40314d2210ae9985980000018fb01bda403855843e7c2439cae9db1fb2506c3c0483d126cce0b5e384d2521db30c13a21534082fdb8b785e0c9c810541277399a4f90d4a9c0000003768805f6c0cfe47d3cf0d47f874110102b21e1bd0cb3083ad161d29b11143cc7fe83a29c0000035f60ceb7ccc247003d893b9cd8a2fb63e7092448d105680ce67000000988671117d11c7284052f07eb1064fbbcff889536a1b085
else
0x1db411d83e01d72cee9be5d0ff8000007e2ea21ef61938319ab1c1df6a63be50cef21faed0a7f8e2b3ea0a4d2c1c25df3119144fb4574e0000001bf5087ba42ad5004e710c2940241fa4e751b24f796d7a21d9cd6766c3a0250b0bb00b2e60050d8cc548483be220da1145608837c289ca000009ffdb2e0e6475790000001594488ea7043dda8e3d6111734a375c183b08c8ff06351189b2c293cc000005f44b99e7518ef884d9af5d65c800000445ad1a6a083e70162e70445e405cf3512c8030aba3abcc508ce15a64ca3edd3d530258fa673608e924826917420f6000000e23210ed8e98b660d6f69be320445a81f6ae06fce08ff014ec12149ce544d208c71e80710f2da806a76031fd400000066d71145d00d2980b9404192b09ac500a2b807bf6f4ae706bccc80309449d2426c96b4fe4f96381954400000086eb81f2742b77021ed73914a12763c143d41468506bca234f1de9f706f0c7786dac9c78c1b79a000000000004d3e9b835c0ebd915555cd1f7c40575488d836bde883b75e996a1bb9ca1f5a830a64eb5cc31fad1e3e88516d0569046daba0a3440d1f900f57c3f8c9000003e8ec46b4dceaed573b7080000018f46139e10d56a9b24180000000000231ecb79bf03cd848eb494cf5f81f254079291aafe748c6080bdc45f2002fbc000000000020039c202c47f67317357468725228ae13c6c832a7cb3a8e224ba0eff1c4537e22d28555e301c5e88bfd86c3e25102f7714790d3b9d7111142f931f6306f260ad5aaeb8d133795880b7ded9a270fa600000231a897c1ea0e0820d7df8000003b33049fd7155cb99b0e50c54a289f3234db832af81f9388c04a7de7f037eac43d8a894ac1021106aad501dceb69f1836e2843f04687f02529400000019b5c5f130fafee1017d88835127d483b08a48fa80be3e81fbe000000)
else
(if j < 63 then
0x104165b652ee07d500000035ee0a49d40c2f163cf23533700ddbc48d8c1144b8808ae4c3a204496000000e23440d1160a5fa2c5c98000000b1d20cad64592a469b6805fce026a0104cd000000000002f6623f88980000000000fb48f3dc791e86401f5fb1bbdb43dd1031f843b7c20e0ab06cde854b41ac5183837e26a6b9da82c3b3f0627c01a9ea8a52a5fb59f0738b1ae2b80bbc02af9021e95120d880000183d94408e66e36922caa8195f8378ba09cf3259f14505209ffa71a1e4000000a43db036ad06379a25a19e6bdc3f9cd8a84a956d0036eba0fc8d1157f0882403a546a36ed054558e0f84ce088222fe2c658ce6e707073a1d2c41a1e9000001e53525971a836d5a5b58c291d847fd59fac7831b90191c40c98811167880ab89ba1e000001a87b800000131f855c5d067e68cfb3a2697e2a6e64ad87b0d6185eff80a1b5887ed44a365ebf062a6d9064d9088ba59b3ae6c0d5000002aec84000002405c13277340bb2571af2a7ce078130aca1c673ca00000938454c8a60361caf15a01d5cd2d5a2d4d1180000003e7c4fdb7e6adc41cef113a7d94037000000ee2df1d25137e3601a198a879885deb10dbd9e9b651c5b1248f8887b08283e2343e51a1d7027e614db72c33820237f8366b1bdf06000008ec5b087b9c91bfa0000011cfc46aaa94598b1bbb600000034f5443d64e8ceb11452080b988bae622383064d68ec2eda7dde8136f7a6514b4a781b702057dd120c28342557e1300c6901a543837a4d787fa221e25c15e0d0a195663422ab3110588efa487df5e2b67d096c988cb1c749a2139e111e73258c4566f804e1cf1a36c23b3fe5bd48249e4534502ad9e843d0298ba35f8c7bf3ff021e261fe0d25e5914ef28771a4000007a64794a8bc4c14e1dc195085b203d481831e202d272acd8000021a1142239c
else
0x7d85b8a9ba491796926220000007529a8c5a60000000000501f34a0a6af7ebb03cc71bb69911a8a22bc507de58306284636e0000000000122ae8673290718e19fda0e82e96951a313bf110790f85685ee5ac10813a99ab18a3876d9000000740ffa20b18551ac0d3fd0a4df9647204576c23ecd07a11887b3842b8ca7f94065794c7e9a7c9361c2be404db0009d01a164eb8e710f69bae3dc7610f3cb8105a560e83d4405f43c0e7913c633b2447497a0cd906aafeaf771408b8c751d4926db880b4818d0aaf3cc1015b9875aa029688a8bd65e510c0da865d307cba785d7486bf2c673c4379bc61b41ae2ea4000008c995859c38cae19b855600000000004a36ddab5de806ff090e6000000185460712d878cf37fa38555ca1d2ec144fb037ede4bb85301d6917d90ddd601bd4891fe957cd1037a1c63e908606300000030ebe84f60df5e209ff10000000000005cdf19f5a09accc1c9a05ca8703a41835b00131d4224970000005afdcb89a87310f221754457fc291e233eeb063420000009cafe1499b0d87e8d93d5c879809eed29c7501d178000004784c10bc6c9c3c84c9a1239d620c5b471b3937ab8000008ce6c2e3788487300f9b51f4c8080a9e7c50c0fab088a5e129b50451c02f5d25096b0cd2a80bc943a08706368881c1a1b5fa8cf992d378238e45c9f5e0c2d633985846729dd3f2ee1d36397d31ca860fde61abfd19cf3d15f16235982899b00000045fc4513808185504c41a61720f825b37fbc565b0ad7a443837c80659000000ee2140711c222a243bd8bbf7de2b3e00c1d3206cfa193840d07c5a2d41106201563d368d40c9cb5d8750a025a7b37221eaa079b380000013556d258902647031f2c5fdb803c94063729e9304d59d4202b41d061217ea000000220f26d8e2c453b08c2553e4fa0c5afa73ac81a7c24b31c)))))

set_option maxRecDepth 100000 in
private def slotBook328Slab2 (j : Nat) : Nat :=
(if j < 80 then
(if j < 72 then
(if j < 68 then
(if j < 66 then
(if j < 65 then
0x98fd780000043d06e498c27fd60963a876dfa137a6411748000019f98cdfd9312e6b00000054d32000001155708c35440adf46881173461e4fae26bd21b0f61116b000000835ce139e21535c0000007d98322aa84aa52aa8498000011abc10615a088b60269400fde0116fe00000054d4087fbc077f4c376363fd722ec5311f77b732c006582000004c886841b5445576aa8a20dc5cafb27c18360ec5bb070ea3da3e04c9580cab079e6426e56c00000c97b411f7d93be3de693e0aa021ced4887a641a788000005eee2834fb464d8a000001536b0526904754c0cad0000000882c8443d20000007f4ebd968805b7ea5c9b88a6f3a1e1c00586d1eba101578406f076d04e7f860a045265d240c30222ca51c4c7132a4c075c806dcf71ad41c53b44639a3a9851edc5a20eee261e60000054f26bc8660089cc22ac41d8f4361b424ab20026a7061dca53a204731a25ccf10f488d1bd63b1a4ca0c586d578506f047dbc21ecc00000487e81b2f42f3fc513c3e24684c0616706dc300000161fddbfb4e1adff0000037069c000003aecf3c20986b7f580d640c9dc074790e8350477073e497022d404e7741c0b019387000000a466006b6f2ff8b11b70018aac35e133e29306249218a902e3c2853d683f5986660d691f800000a0a6e03de0800000616ad6fede87fe4d0ede0000003c9fb92ebe10fb16571c100000000000155ee22ac30236d05275255d74224ef120d106bedded114ffdcc554fe8aaa11be760075f174ae2a877840f9b2202f3738651c3f3c0571cb36c208182a86169b59443b9bd1d05c06c2ed1109c396737d7fa000000183793c4f893afa86b7a02d7e213aa91107c83f2324e1ee000000000045377c9a22804e8f000000a02ecd2be80d5b845a6c0983cc1c182436af09a7a008f4c48358a61f01d24e16d33c2a45d114e3
else
0x9a77d0e3fcd58338148e812bd680000009f8c313a615e410111c06f3f034f1e000001067680000033fbc85a758483406a16e2b2f92a0f30000001438a0000010f62800000673e6044910000038c791573d0344ce2ae60887bc85531a33e965f262283640710c625a98926e633cf7140bf85ebbf9384806b604f27325c5c230a8c0acae00cf8f1bb8d928662a2bf619518873f93c9231e349c00000034dc6fadd915d84000005b4a7696f9baaea167b6aee29a0c10503371d81d810d5e1125674cff3424aa8bb7cd3580e8376b0000001add44e74e8306a9a6fa822fd0729e208bfedd71680000006f52b3f248483bc000009cdec0052fe113fc21aa30000006bf2c54de009fa0000000cdd7c293f497b541d6f0a42fdd19a049e8208284e0d86c87cbf91fbd41cb7e08c75c749020fdcc000000206e4160aae50f00636d08b56043d069481b06f58454b64653d81df9d431500c178c1898131fe08c1538f477876d08b44f873ef80000006876c450bd4803f2a5ac4bee6400000497290fe280457840ebd376e430409bc8b250220e200000031afc269680ef821a8480f92b0f5efb2508d8a24106abd575fee298132b2f7c25aa00000022acd1534f8d7f5d3f1283a970110e5154f60455a44ccb52676f92ea32229163ab90394dd80000086d44231e60dd552f36d5c6530418af0975eba2ba032f671c18c3ee882c5b6c463c251222075eb887ac90b0c6d41d0061449e933800000a6cc109cca995f8d7c93f3dea78f17fc32370441246cdc1081678000004af749cee547d6f3c5654183f403cbf0ea158cba40000002d3991880ab3f3dd1d564572fe09a41ae6a710e18c141951d24616f9cc07b5f41f8c065528883288cb1254bd05f75398fcac1a9b0c05f6000000fc2f1255dc7e49012a72050e5cb50fc3a4e91117f0e8c104412434391)
else
(if j < 67 then
0x3e7068636b81c136289956737b031a1997d222b4bd420fdb036d007bb0217c810140833744405d0228ae6cbed00000121566113ca927731c429da8352271ff080e00e927c441f40c1b405a64a5a8c0411d0e00f18ecf193cb7e063c8b08980daf4424328687783ece90c9dc0cbb5e28f04aacf70f367b7ce301754e1b0ba11049016fa81138e046e951b68af5a654a78c0d7ce1d7538000016d53a00fef110e48e83a5b7f5e2b4d40de5f090498a8b1c1d2ec10f7b80bfb8536a649ec50000004e659088b63a5ac71ad584067c000002b2fe0000000ea9c445c6e8be87a7c186aeac7476a844904f27b0000024979c0ca8b635d48307dc04f2211415064f2a756653307a06fa20970d8c6f91eb19e0c7a101c5780be4c1956e43f6778dcabd379cc1d0cd59f4111efaf6adc43dead29ef37d6902725805f4e2c5dd154f50bdf3d4e1cc228c919f4834cb0cc225c4a5b80a4df82f350ab1560df9e000000000022296aee48a01a478486a588f522a6c206171b90ed274d5121e8b079f9203b9cfe3b0aa7ee15377abbcc11cbe8044fe721600113dc00000499f01536f3b7b1c19bfc000009295ea317d0687dc16cb228160087b144410c3ece417e3186d2809398049de00f04c38fa9d64d783a4c830f23a149141b90c00000114590d1214405163054c4460c0000004050f1baf00705900000249ba6242e704f65c736f84456b3cbd60dd4bc51b383ad803faec0904e1322761390c0000011cf50cfb440ab95172ce5280b9c44c03550c04cfd9816c0d8230f807a35e69114530eaff8269a2220b9668fe800000e2db3179b9284e2a5c29919f04e81c3312e72ed2ac1959e00000610651161ad4a3e0222c54f08481dedd2a5a80458b000000000013a3463fd45087dd0762c8000001adf73c7dba415c830ade9e8a810f701dd68d1217c00000
else
0x23a7217e32ed0eaa57de308bf8c281d102afe0306f03bef1a4f501c5d736c758787048b9c601e7f10f76088b8c1c1543f89763a5d2751347bfd6210c90d852058374e2e780000037e42212668749643a8909e5ef0883ec187f845be632bea8e5e7d8fba43a7f01ca6b9c237400000a89af1657706bf8419531114e539aba9648f008b14223a51a1ff45274859f1a0000066ecf42d32c44dbd41ac186978c37f645254c222de8c57b800001f75d72f0fe6ad59106add4bdc263b531a1c207d050f95deb74963d0bf08ef3c74f720e0d010f7b080aa179bee9be8885f509a437c74188388d892875835ab63651c9652410159887a5819f302b49d0ab7f2c0e48355a13e28c0000004ff48155d4a83c15b56283bec86a34a06da766edd8aaa54285e00c7ff1d5e88e278d0eb10812ef06b699a126400001203b50d8498a231c8133e04ce20b25e835f5473b863a7918e6ef1a60745017742dc75523982c298713fa2229f1534315276474f346063e10177089bb5d5d1c537ea01ede031ef5141a4ef0ad1de98a1f27845fc2bccb01114f3d378e4df7223efe1d3d7a54d7054d5a3428a0b52f000001dfb740c1a47a66d2452524ddbc02de8110d21cc8ba7b9de5fb968b6f18382ccbe28486d8e00000090b089ff360c1df2504445ce5026f6e241f02f635225a19dd95a1aafc121eb0e2311773862d6921d27b1e69e02a82c23983081780d4c0539d545c2a8000001325ed1c8cd19d8c0d878b3b3800998a138a70d114831be18dfa64a63010cf23b83418276421e869284688128cd7f2c3419e9cdef8336320dde622fd30d8738d0ee80000023cef3f1d99c06580000006df6991ff0fe6f8071de236f53c1e32df219d5d8a2a6ed6f9e98fe738951431728f973ed121f40269df0e7de015f6087ab41adf8221ce03d4217403c3a33c220b5))
else
(if j < 70 then
(if j < 69 then
0x10f4244d24c7c51f235f2a0cfe86b7dcf695c968500dc5c9cc618b8f4a18388000003d134054dd48acf22460b08c6d4441df187a82f928c3ffb07494402fff12c4100000205f41070992a6c787964846977006b74eae0457afc000005e2623d2680000020fdbc18df64a88d8fe3714a5d20c7fa5d8c84432686f34a0000016938bcf2e17df590b1da44c9800cad199fd6e87ba060cb80000018d8433ed4853cb088bc4817ea8b94703e73462f282df7ac83ef56823800001fff9e0094b06af30e930819b30c98b007fee470e2c43d64dd6bc937f1832cf4000005b75309a7e8c04a4693ca3f9d626566c277801876b1cf838f9d186eac46306040c925c878a80f5418fe04a1b811072af36b438f042aad07817f85270c289f6862d20000018a308d79162b6e90000003067e675da00000778f684e7711ff8825a7d000000286e8441441dde80dc4a21c2e4e986400000251c083d219dd1260d89811f49c9bf0c6fdee18cb41295e8000000000009df7110708000000771a3194737c38082afc187c0e54be11de4234a720c90e52cbe53199013f483bf6072c24203d89b560c000000e4a906ce503829d4d062beeba09cc52477e1dbd1135d9c24d6baa575c000012fea26e155a75768749f200000384e70be20469350dbbaf0087300f3d80000057c4b628cfc69e141c17290d1f4b02b144a8dcb58a6fcda1017d881bf4183f442ed2901d602a6f14bed02cdd709ee20887644f5bc0e6c586dc31c2670db3bab1bd7526cccf2fda45fb039037089d30e221851328c10cc000003023306af80220cb10f7c03379a355d642be4836f2824844000000000011951089a2a0e5b8241ca0c4ec0695081bfaa000004eec280000044382ee2996116188830c3cb7293cee0654d84a7fc74726e70ae0000006bb0a295849d5401426d927698185beae9a5
else
0x4e9441342c406b02339b36736b0acaa42f728b6587022e086ab6e16ffb127ed1d8ee1aff20dbc38b8ce1846d50a023086bc0000004a6fc2811893f9e82efe97d5ff0907403bdac1b0d586d6503074c1c1a46e15f7ed7b83830535574120b54dd7d93824df3b603a0d442b700ceadc81b9622498811d5087a68f3f411ba850a9ca80000076d200c1920ddef39f61401dfb3beee00000087a3c74fd60000011579080b9cdb3e11af8a118cd889b2d3e4a00438d111e60ec38491ba515cbe84c7fcf2f6de6f2a0e0e424d600acb0c54d82636c6696e40c685845da8155b98c6eda22db409f4473aeb0374c39d6301df461b083069e2043f4cb770e000003b42889070445fad059d209a4204d79d5df7a000001536bc73aaa797ca226f84d7330f36d8a75c4000000a4cb029ef805f2af00ab303d1b70be218d98139870000020d3c12792e2d85a0be6200000004c11320f119d7426eba14717c3a4ea928492cafbc18f84de4ca3ebda94376df25828c2a758f7c97b94d0cdf20d0e10de6b02e2a9ce14e3495957357c4eb9c7bfb80a3da5f0c78000000000021ef206dfb42ff5c18f8e000000000021967819f280de8798b6386b708000005a118142501f5f1c36f36343da1af4faa95603b1bc2b2d4063ea8882f83617e3a78904fff8e2a4000000fe4ad696e4000002229144ffb50d847832a21ecded105b6026ef2067a1b79e40d7eb88a64bd02f8445c60d7be060ea88b218c62d8000004d1760a1390687c83b6ee4b62321c3089ab680c6db29346800000e2ab23a4ca067ff84aba86755cdf5fd1b34a888bec000009d5ef6e25c080e3dacbc84619584f48983785be956c57970196d09eeacdd3783e5ba98fe0a30fe92d1e40c6ce0000006cf243ff20e36f21115088a3d84d81679f170a27908823c6755c8b8ce10160b02ba468770a26ee)
else
(if j < 71 then
0x60f7833a3c07bd21e08e19761418f29a5b533d0f5000000000001f7dc08eea35e550ad2e0000001418706376880b917c9020dfa3418d28000001b77515bc80825fb5ee0634fd48668e209eb00d345893960d081118e028a6087f1c63fa95120de1b3bf2213f41d5f105982311fd0565305e3420d874063fedf0dd6d4fb0060cc0a9b104d96600000060ca8db08c7bf646f06e7c4791b8064dfdd2339d75f44d321f70105ba3a7ad000000d0e40dc74038e8d10f4f01c2650bc80d0bed013da087b5828314d88c341d598702b86d13ca659965a49033f94df8361b5c71117402cea983f690dab6796da006b522efa677f1c0dc4993369c7491e58dd35c0e08376c80e1881cfd133bbb8000026df662b4c756db2019bad08a381b0a670a79bd224e171021358926bd5089a6451fca50d9b12960835bb08d0aace5ef5cad70357d85ebc87a6aa5131eaeaf752a8641aaaf038720000002f8f40000010781887b6db87781ffb613a669b5a4668332000000216dc5b32cb254c1dbff062f48d1608509a0248c7299d33c2b2c415c24c6899e47da3515e3d17c0c29d07b31887b3c8eb704afd90d57c8b9a503d7f62abd28ec542947d4435b00ef97000000000008173adf5ad4daa286abb8483b820924060d8079b20981360e088000000eaf9cdcd7adaace6fae8080a992a480000000197b1beb88daecc230d8044632cb23c0000000000830e5b49ea47493200000111618842446878e0eded1ed95833f1c3617ceb89d000001739dc6abb6011f740f6a8892f0483e91c5d487c4e051f08473d315baf90b6a035a80565422f0d61144a088a3181bfc704a47397d8e8b7c00000222fa51679841e5899b88103f56fec64427c0c0e081b7ef9384a800001b23c4520b55f26ba06a884510682ba21faf70357adefdec351860000000000222934cb9e6
else
0x10f53374e90eb385453bd7a44db05fdc371920dbee1554f810f9c05ff003d8c0b5f3a759641ad4c22a894854abc12245657ebaec76f0ddc3839a157220d9d8027ef8244483dc14b6ff2061ed03d2b476f544bad81d26cafbed1f0728149955db4088ae9035bf45779f000000ee2dd7d34442ead0000048f2280154c0000010f5cbafe44b88d6a9f958fcf28000005752c3e78f3eb4380000291338241e40e6e6009edc2a78a40d827836fd0929850f160d7cc11c808cfa644492c1418e7a64c8307009352622ad414d22016e1c2fb2899a01290e9a68e462038b452c538279384f962dfd479e961a959a9cd844854a163b74eadc02a569e99cc4818e07ec6121af843da14339009ccb4d8f46229c290a9d36ca4c1b7920dbf338ee5770f086c36839d52a5cca0bae2088a7c2852e0000006ef43792e57d1e2204bf07055baeffd80d140ce866e674000000000000000052b7d88c6404416a0e8c41d2c0805ae81e944fddba0477cc4eaed9b590247a81719d37f721707dc9b01f1c7d30d06c87132cb8ecf0000000a7483b31ce5f82076448d9aac4838a0000009cfab36bf41bfbca8fdd9e5ffc36aca3b36b0e38513f75882020eb23e2ccbc077e78cdb6422d1ea412f11b790172884d112170130000021d3095d58b1c1ca110d88463586730a0618f0eb750326c8357725aed106eec8307447f53535cb3166e799e85018766383d60d6cb8e620868b810bc8172be002245211bf20000000000000000cefca53795121568da1ba173e022c9f33ddfa4d67829354000006de584a337022d8821ef34b8ef81a54e0f95432ea89ab58cd53e88c7060f3b118bbf9e31641c9e00c73f07ee006e305282fe000000e04981c2a01ade405cf7104cea1da7539d0f3a6a12e615303a594bd3a015810e95b8306d9bebec1adae11f6f0000004638e225b0)))
else
(if j < 76 then
(if j < 74 then
(if j < 73 then
0x817d4763144837cd78d62c5c988ffe47136800000352fc8465e506bb80efe6532890b4f7060e1a4ddb751d714caa3d5b90f0c7dd66e5802cb0a7c95c9b1632045a10da54131d81cdaf694f5c9bfae4a184a3a5c0000022d689f9198d5fbc1de52303732387823abe28d36585cc881df42132b0313588b2acc00000241f53bcfc06c225ad1601418652107bd36e4185522768e15ffd031f0000001305d1000001fd979bc538120a41106794b6f875776aa8941557786ab10ac58e224b5061fc0afdcd95176bea9604fcc854fa400001116ef5ebd686f254000002aac1155c5179ca068912000001c3649585b048370046b7120df00000006df24bee872bdf238e3406ed2d46e974c4c954329231ec07c981ba91bab27043d0a0404b4f2c186f314445a20b3ec10cce8dfa703610822be602af51a8c69dcbc0000005ccc53386e540106409a6325538e92dc4659e3485104d4d0000000000001d5507ad808ab800b1de6bfe40000019e53cbe8244cb75217d2087b9435f5442ca14ead8887ba86cf24220b900000112bfcc4f52c8f9f3c3e50662781876664040437f10a4789cfbe218b8124c4ec50e881a9c8ffed3000002d9f6819f661fff47884d8be328491f222a932935106abdc187ee0000069af9b5ee681af64000005e15706afb2189400000008755838314af020221bd1127c11a3e0833ee202e21105f890768795f2576d20b743c1c6945f1e6df5ba0596a3582ec7f5360c9ce1d062b65bf844561146cd063ce142d30327503ad4709ceb830e14323f82028d278e280d2f81df6a3a5f509b3b0423fa851d6a6ab72af732e0fb819f9221eae110d908fb58000010dafb08453b90fc43cdce061d1239e8029f662293e6288d00000000000000000fcd65097a3b53fc771190d1a58235f421af443dc46cef0111e3c45b5121bbc0bb83
else
0x19ff8000000c287946fb41535b888a38273de21e87118e5261d3053dac149c20b7a19bfdf4565ca0c7f40d542233ed5eb3460c18d11040bb732807fe8d29d716fdf8d4b9d3aba4a4ee557cf90a5d3d37772127a67e85a895e31be79c80e7a068580000000000038cff7ae4da15b05fc1f82e6dc3c8b48446c095c8c194ef50b2f8b85da433321c1a304e5727eca418b2aa60ea234d79b46b1f5f88102ea1910915b07094d2a0c7d9961448aca4068994000000676d8c43a95bc6622fbf43c78a41e386fc70546fe04153c0db5e2770c000005ba7abfd7c9b2f98438b400000000001a033b114b71d3c50000001116af57df88a4d445258273ee4358e491e20bde8d23b6e141ea11059284e30453a0545d00d5498a9a35f31720dff1867d3882b8036f1c3029f0dac688db09063541b0b90000024ca2c2957c04de826b0d83379474fb6ac7cb000001bb790443320d6a923d7f03bef81838e265bb0686528cfd44632e221829c2c10a9bd81ad68473e807cd681566c7c330000006766f888f95dc3a2d91a500000494235f07d83a4bc7796c8cfbb41a92e0ce861d578016ed437b6a339b315a46a352960f7e0221b5550d2013a240c5d819ed10000005a63847d7e0cfe2058558000020fb1407d9110f65035ec47fc6a000001106f8f3ee8449e01ade852f618cfacda2f1a138e8117ca80000000000221b90a4c68263101897a01ce0a1841a0a861f3f02000006e5c6323f6a139b449a884cc4708a6fc1df553e9c516b5b0377b80000003bb110f60069c720eff33cbe20654386c37c1ff409d3cf111630137c09452a0fbbc01efc2c9bbca80e4f68be01e5bc2775c54dca1b8b100000468399cb91606a974a5e7c83ab94c3354838409ace0aaa84cd90c010d12a452888aa5d6376346da000000ec2503f7aa1b0890c416281cd8273ba236f1)
else
(if j < 75 then
0x28b43371f4018320d28c32037dcf92d806c9c1b09e1014f03ee3018354e8ed215369033ec08d3101aa9300000032a78ea76d2fade6cb700e83ec1afb216e0e1d261087bcc51340134ef8dc79035af0193c0221fe88add06bf88c0958134a60deff9d8e4017d0a22f84347940812c028b92d66f53ab39a4a8341c1ca22fd01534102f7ed8f9e8206e36f9f50d2bb81ad38000008c1db080af56e1c4f94c26e1e5030bce4ed24000002bc510d13347574c0c7fa1b8c488835016f5710887000002a27cc00000141e309a7734cec2563b4034c011b7f8fb71d71b35321bf10309a2cf5c1f13c0d687077e10908e444d66f83a919f46963acc0895c034e36d9e2004668175fe202c40adc0834234000000cffb0d870c45a581910a220d119ce98383b9efdba0d7b811b451187681ad1b14aa08c7eea47f14000000000011a7d3ba2e800000241b5017da859c40363da221ad0ce1ac52b7018f6c1f688738698cfb457056a27bf33e77c08aa604e94222aa61116b8d17e000000341cf4746e1db33c75bf50beff40fd6090654000000e0da1bcfa0d45e035b1603de1063fa80ffa247bd4cc5c60a49ca9ee81caf84478b86084e87fe157a3a6233814e7480307b843df89fef270ace105e08707320a6e20000005534d2db426296302e439a351005f3a4176601376bc8a9869be2405c70156bcea2588d4291c592115559b50647610f0538f118459e3ee4193e2134ae09cfccd0b207498c2369e49751ae3aac711fe489830000004d6fc0f92e1ab95144fb050be23278400000000001dbb8c1917813fb30000024a1b8b34b693989052d63ca3b66ade80ef874bbee015f2c729d4134ee0e0ce88bf5450990dfde06f07daec230513241afad468fc896a5cadd240000011054848f6e17f488edf31d07622db943614a4c0e712e659e4ce5cc32e46c47
else
0x1a14d41bbb6507d83fa83000000bc28418a8e49aff928cfb79be48433a39e50923d615aa7043d1021eaa000000080089a5ce4fbc6117d888be4ca3f370d3f1110593647a000000be49d0000024af1c46674229813febe09617de799a2ddfa4dd6fc0b6788c34e2df7a000001f502c6219a108f710f6684d74874f1c0513c0196e8157a2245200c7aa1114dc1cee5e397c326081c1c718dfec1afe80ced5120d03646f9378ea039935710c80000024d4d018e574458bcf21d4b14e2a6856f4d6896f20771c0000000a4c7280f3457d3d290a50dc5ba373f8121ea46ab11e31c3cf25c1adfc3a7e95df5681161800000344ef067f700000018d2e6dcf30def90eba8400000241f91c05c031ff238bdc49edd485c641336ca422a224ff000000336881bf461f5d99f2690157ae11d863296e03ff1887ac41a15e4e6b70a0d43ab60819f64000000dd790ad10d75d9c3f88f9f67a031bd435f101dff80000006c38c46370134ed000000e23bd4248a267a237ab9cf2240687a4c6fff0515545e6d0c4dfc3059b11d45831ffc36148beda945c3e8d0e2622d8f2ffe607cf249b3a587da80d0cd23dbe8eaf407354c0000013b7684d7557e7a9109b70000000000018f4aac5fe17c53a843f07119648cfe10f5582cb300000106ea924f76087be0465bc70abd08859000001f69cc00000781e0082a708e7540d7f3077f7830f716f5ec3a1ed19cffbc065e06b640e0b62100f8e12b233bc83a0a588a772112a1530e65f68e1d24c8000010fb76204c9000000de730193b23061307ac406be3c3550a11e6a670d0b65f7826056a5bb80f5da84315c87b16104811595f91cbb87019cdbcf106879050f481f722172f2114590be3d1bebf2fc0872e77308aa880000032ede7276b1b92ac15d5616ca20e0d6819e4a72b840c7ab512cf83062dc6759320dc))
else
(if j < 78 then
(if j < 77 then
0x6fcc183a0cf4f3d348bd8eded140260fa982a89a57fb420356b43d3ea000003c590848614749cc87ea18f5de3ae3e904028292c20000014e2b5ce1d210fa38cac539f7cc763e250ffb1d846a84aa9f25eb39bb2a2a7fc453a81fd60228e26f7c408da40449d00ec4d1c45e0306ec4051a0cda7656c92843e94e08f25dcf110550579f1c5170719700e2db0a9bc01af74094a85726f9f06a83833c1c1ae30fb58256cd01d6c1419009a68000001e1bb68a91d0a46f0be3e40000000000071578dc1f400000323fb0000006aabc27370000001d2f90aca2c43d881b1a03ec0780a97c46df20c1eb020450ae4c5f098c21f5067ad6088e6570774bb2b10000002d31040d7413b62000000047ac45566860e51534708db10298e00c68b1115709c172175d4149fe0ade3029feced1622edf51145f8a037c4970e3aec776e72133bd0000000cf9c4376f8653b20fbf8f068e0d6d680dbe8441783b6f824e7408ab0800000efea1361e395ce8e2d7682248810f581aa0e5382fe3a0be4e8778a9bec167fe20fcb9567f073aa84fd462419fa037aa9b6303cb680d7a6111d0aeb7689e3c41569e57e7eb037c000000489b006bf6831ac9acb6a062ff5e858c993904419e000002ca51ac96707235a0d6986f8d9a71825436c4000000c5c30faf2263fac6d8a91fd63bdef145b976a8cfb157d6035fce219560e0bf204cd8343acaa918000000c9ed34dbb0161bb46da286d4d3aff8062f7a2899f3c7ce3e9b04728231bbbf060c2a882ac1950600000471e60886b934ba6956a6118de2c5bccd25e610fc636833137358e8f04a348d0000008dba86f3c67d24b0e6ca9a1a19c81c60c3df1929304d3300c3a800000064c104da882d7fc035e78037b80000040956000000d55228692c2699214add006588e96906895ab8fb00a0e2033ff850bde22a9a
else
0x2c960a84b8c0000021dae63364c45360000000c4f0836e10e93191cb10224b2114d90cb274729b2df5c96f34f032792497b4cae83851d906aa590dd4e026cd1d3cc873718383a0e28d6776d1035a407490f007a70000000000079dfe0d49c8327e8d2e99c171856ebc92fec8ad2b4aa9a84f681937418337a5cedd422084063e4c19b725cb28c558d01cc61b5f6c4611c4e83f6a2c2037a49e21ba7b13700e070efbc85693a94d550707892ff3626db60cea807ae203e62cee318267f09fdf8030d08687d4500a1180ca8acbe8553d82b8201555e161cacf699c7a51e17c4d05e40d16142384b000000431e7c2b75b0dddc06fea07ae5c00000f58921204598ae141992e8b29933ead0cfa28bae0c339cc13276bcf295e79ea4abf63e9830a26211a6f4302e4145f687fe880000000000110f039e2384918e4f2fe069d089127d5d3a63ede2729e90ba3ac143429e06e02aacbdafe8687301abc8249b006c2d91a55a222b51105a05665c3619a236c4222bf8de8d84459b0d5cf0000009ba59e5bfa00000490eb845ff000000228f46a158136a084636213bbf3bfdf006a895943c81e22729cd92ae845152c614f47ffcd000001272cb306f91a4d891c7444cca0070f159371cd5a08000003fa899f84240e2c64c5d0199e710f5603fbbd43bb4725a04617083138977f1c23bbd938d00cff3c000008fdc711146ba06618bf6221e921fd4dc65b3819f64de9d624fdb8306ecba962e8fb81017041bbb2327f20c7eb00000000000555be0000046cddaac670183542eccf2f0a60383b41ad4e6269400000011ad4405ac1b0fe44733903a0c44574220e91a1e40be2881bf4411ca206f440cea4c000000ecf1144e3887aad21b2c149d07ab6500af4191b280c29b1146e2b1ca1b7722202e2000000a9ba563f120c9e68645a3372300698e50a88)
else
(if j < 79 then
0x10161ab0eb1a491a6002a1145b8496f0239a2f10d82ac820cfb9846dc8000008ec668d2758075126b5ed022c0b65e2c7f3680be9809ad11cd9885908416c0d1a93180000055d7a7a9ed10162090b64bb966496a03076111f3b8749de1ae2b5dc7b07c6bc00e1c7f56c00000139b02175e0a2af3883530f02256ed620ef6d049fd8acbf00000026ef8145e10000022290222ace9f25f83131c00000399a611076113cde0b55cd979b132848dc4f8ae30e2aaa10e965ba93801ad0c34ae90dfdd07a941b510e7b0ee8d5f80000019f51a9b4e84eaee8367e4000002f98380f75887a5c00000a4dda06f68033d09e6588000000000004dbe80000033f873312804dfb970dbe22af1054648f5f9c000003889f521f4800000003be0d08e31d57038321f5bec1d650060fa0891c622950143c010aef80000018fc2334fd9307a887b0c98bb8210c210f60832328143440268a485423067c93277c0dcc1060f984753c449bca4dc9677773b8acd47834202cd0b1ed083e6c51beb222aa1be7089062d2bd560d08c1127a19062810110ce1d60000030362a7978c0ced0125e9c45358693e600000111e9800000445a2641e9169d0887be043d3c257c806fe42e066c74316000001537a0a13082b5b03e599229de427351414a0148a547cd19f63ed361ea0c3aa1114f2c8be0525fa0000004e410d12243e3f40000008c481d7d75517b4075f005066986ebc9043a000000000006c2a0619763ffc6110e1c3cb2051356026c6833da8000009519a00000771ca00000000001215872a6ce905679557f60d6911cf93a642981af4a857411a11e080b8e1bbe0c8bfa0b30b80fa98357d602a968de688d265c707fe1aada06ffd8a125e58b14228a40000000000018378470b41d76a80bf217e5802a6d10a55015769c00000bb48f8ec584377888dbc01c1b0
else
0x1978835addc11481aaa911f6207ffe041594098bb000003ccfe57db7055f2400000066ef1f2705055e6152cd07c434e0df42d56800000350f9418d0217d9f9f2eb436a8dc87223edc88e0fccce3a26b18e4f82c2a467330e184418a9312a1e0583cae74de1d217e73000003306ec1abdf10dbe5555634b348273e4e69b888b6c86f3dc81bf603ce2061ec02afa819f49172e89e5d4088a6444531470af14f8db67ed23ab6004d9e0ffd144571c6eda66cea709bd80892d000001114ab07de6006f20626f93cbec000004d36a455572036d10a4c88aaa7c15ef4f548128c7a051bfc63932209d757510837b1ca81e6d9799606eb160e700db3a0000009a4e8000015a622144d011d6105ae24683d6f769702a5a86c3c1dd7921b7952b9f1a73bba11b0a1aab91ebd10edff505be0418eb5fe50074af01857c0c6a51106a0eda3cdedba03daf9bcd1887bf0463b420ad6059dc0116404555e28a1b4176d8a5f95d454e8d0db10f7d00000000000339eb4c0ebc4530c8c38737b9565e6e33a784415d0220875b670096320445dc222a412e2c887a2c1aa5800000069db2c96e5c4f20552930000008c344355dc0d0eb325ce067ab81b9de21eb206eef9884b00000000000a30ff2eeba41836ca53a811cde06de9d3842016edd12df40372d43cdf6d44b001a7f850e45d239a4a39c8ae7c381ab800000241814626301568df5fce626ab114788677d47419c000007f7fa8000004432625213132550307a01afc60000002de30247348f3e00d1f500000035bdc43d3e3a5c71c67e2187cc5237278540742dd0ddf0814e25384a6037e886137d8ffe60000000000292e10451e08c8d9066d603ded41472e1bbe2976d60000013da50147ba04018823bf8000000000095a4c984ea93bbd6d97f306bd3140a795d05e000001c459c446ec000007a3bc))))
else
(if j < 88 then
(if j < 84 then
(if j < 82 then
(if j < 81 then
0x11550aefeac3273a289f619f44a43f8843d2e0cacf1542325d06c0f10c2aab866e4fa436b844798c36d98d272031b4026704c1dab41a7f4393f01d9142219d00000000001addc603df906bdc8000021913e151c60a261a344f82d9180000011559080b40222440d6a12112c08be604551a0a19779e46116a6d19f50cecb6000000000000000000000115de1bda78000004cdad9cfddbdfa2a2b1fc149b213ac7bf8b44868a01d9d57575e8f3d5c000000d7ed0e0c90acbdc3f066887ea04e6337e2185a7a81c1b50ffdf5077a00000000000763f08eae6c1536c1399f1547b180f082695c000004fb6ac8929e501f4221bf000000e93144450a804d202dfa06c64c000003084a8965b80000026b4e4e6df3674b13cb3c68dee3b2bb50c55bac75c293d4223bb050aa0aa63a647181abfd7e5782c2e2d73b822ab7810f7bad779d0f328045f1110d600f2d981bb02b4e50000012760880f0a91dc54614508bfe843d1a8e3c1088de80000054d12bc8ca1f6d1273bcc19f0e21ec81d3de800000741f2228f656fdd3e670d6310a113ad06ff88e9f15bf3c0a128306be38bbbeded1320e0bd110cd0a9a541951811e9301ca324a4b0441b000000000001864382c1c6117e09abceafe22c54d6c3a0f7525d8031e506e9705aa71069fe05b3f0763d03b6ab9f24d800001148e2bbed31616200000233bc13e4ec1117f00000037f1a02eba0d764c7ca0c000003f9c1498cab76e8870762000000000003272894704221b101ae23bb70c43dc6e79fd471df88a3f939db2289ff685d91d5bb9a61b22398a683e28f9e29a617c257dda38e2cd5a0a6730e4a76364b6c9e229c6874013484000000283d40b556a2abc09cc608ab7e7970c220a10a4e88bf24971f740000024ffcb7f68a4d9a076b29209bb1e8706031e8157e5453d9087bc8000004cde9
else
0x685dc0d63b000000000003897c809a043285094fbb15ad91332e1b0b668b356000000000026f730000002bf89cc76d0000000000000000010638419c94018c64769a1f2f44053a3438c9815ab4df501933f39bd11d0628e929c749e0e7dbb0dc79833bf4000000c7b8060e50176c0523f33bed8017e60f9754b8ec51fdce060d094f73893dc0c88c60000005279844d1a5440810f4a04079117da4000005e2d209dee57d3c8289cb88a5d1d691c7e7801bbae06be6bb8a8200da6f29c40ce419ee12c00000e5e9e060f30342252edb4d7bfc45aaa8195181adf5455fa1a53b879d34efc4cfe5e106956c977205f1f6191a692d45895e24d3684b7ab75955a8d0e1c51be8d2384000002e320c8cc2cd99b806bc28000015cdc8100fb06371230ef8741a525da1118e00ccf65c017e148d7368f1a786e80c9ce00000788682d83ae0abaa2208563de880338a4e164230d811173011289a4ff20508c961c945d2c0fdda65bb9627ad90a12d0283e60cfba28260864651ff5ae2768215568888650291841affe0000008829d8233c224ac10f700883f5be97621ed3525cd94534c193263af969aada21213a38bbe149b406de50372327dd78098df1155d2cf2fc85e3c8cfe10000015561c35f4605cbd154e825927c4855c00000197ef8526108ab78d90c031e3a15526c0b5c82a2d5000000d0ef939d9a000001e8fb37f6f404ded13cc968a4e02970c1b9e238897000003902503cba319d831eafb8486dc00000bbfd109a5a1b5e1028e4ec499b112590000016958f1c5a73dd16809a7c0000130df000000416be0ebca0730b46cec106aeb53f53400000061e94177688d1f209dc36c8e3962e88833a21bc93000000c4f71703a0289b4117c70e13c043d56533c51d7793ca66400000176301425f019e91ce1da12bfb1d243242a743ffeafd2d5)
else
(if j < 83 then
0x7b0da01b7a42478412fcd721d25087f44ea72221e0588fc031abe13316231dd51476000000000001ffdb1d3d7079ad8e6646af9d443766000001c81f9114d6000000ca3d87ada63aea88e071017bd1b41ae202df00000089b94183c90c9bd5096f8b3774d4e6e2f9360c5de2edfd9cff7848f3c44dd32ea79dd4b262a6d7085d50d0e5141f0632edf50953310e10755322f58121ef684e6a4509960ce99048d43b72990cb7a0c18323264088ad4565021b09a1156c3d5f5c5095ebeed906df23ccea8687ccd5fe11fd79000000ca154a9f5b910e285076d531da13bf422f01cd7b5c0eb3a0efc404994cfeb5c455324d72452d610efef43577c149eb00000030690681e24691e09bde800002595704065466d71b72f15c3f12df6ab0c0a8074b1c0b1741afd400000000001e9b760c1ef068fc88864c0000021ee78f275055f10de71abe9e7110e834b6ec781a5024fc0015fac0a5c71156959ed83775800001abf64241d1060d6887b19dc30a56a6b5c77c349e0c707e06dcb900000012fbccaa3b291f15a965804fc4a177c435a79254eb742652bc0c1e6d42774f079f0c441990678c019658000006878508dd32eddc0ad29047782cdbef00000000000cb861373b5142565116804436c5ad331d5cc83bfe8000004b5ec16f360e9fd8099fcd21de47b088e96bd7d9e24f3ef9e5d18ffd181c1b21c0b2061e60e82dc1f01821ec47d7e50ee3fdb212a0c1ce0616880000028d2e57ad011247a71c901f324210c11ca6c9c733c93b30c78b7110428343b074fc0d7ba6000000702a49ad980e0e80208eb94e6c44310202fc5b96200d2c56c7a1437e915a520e46204c9160d9aa39a6fae07bc707c60000062d5a0ce6085eff00a58109f569edb6419b3e33f98544a60a12c400000eaf976fcc93bc2d9fc5d21aaf91549a8882421bbb8035e8
else
0x67374ce629d4df5e04b2f6cb52861b31e53f40e0d7077fa809a10cd3380dcc9516d9b27a20b5cf2b699e19769836f0c4b3ae5a32d6b0d3031aaddd9e6220ab0000008c38827bda000004e65a0000015172a0d994946fb8527b11c978eed9d19f59b3831c43d94d5d950705780f38a461ccf4c8f7d641033ea8000001afaa08347b39a6021fc23a781000003c5e6602b8083757077d22d2e5000000a84d7066c748cfd005f7200000423d3184a65ced960efae481b4c813f0455772e4d6089ec80000118bf43b8f450303037e7493b8c1b82310f42438a501854a134921126d0462dcde1b228d85540d00e92a000000f57952acdc0a9a882b7fa193f9110ca031ff46734091d84064ec880a4c913b823eb8430ea0882141c56632c9a205e748434c4659a113a11017f86f274191fa3889a4d620a011b400000c358c995f7088ab8000006fafd34de3088f78a01a4d3e8b5624803077045d1a09c862d391339ae86fe52299ba8584a05268282d252dfad50270832bf81d9640c6de059f9a900d585fa8b16a40000000bfb4709f03b6c3064f944533828dfa418b4295f51e2af81dfc8000001d1e9a6678e1addeb4ae1000000000013a0b242ee212c42d21ac9d95c280d7f30258b4cfc004daf3e2d6a2f66c8aea850d8e0f5ba120f3bd970845fa51bbc00e0ea1d47f4aafb0208d70a0d6831fe4e902019695063db87ff20b7a2e202c35a9f786f3c48046d0baa215374c5cbbc44330228c91c67e8a9b04441f03a3c21d07e86dbddebd2614a7b4eadd831b284833abdbe5064d9888b920a31cf56a10d84905df9962f82432f71727b9f6275cef6a21ec51ac9f06670ce4bc6f8696059fe83366456588228e0063e2c6769c18d3049ed911d1a4da761455742341d00000379be87d0face6900615988e68c43d1c419892326e0e9f50361700c1e0))
else
(if j < 86 then
(if j < 85 then
0x110f108a29103a4e00000360a0048351b8332e81bf09cef3eaae0371600cf876f2c4d02b09087930068807df3a131641dfba0d6b5696c98323f1b5fe213cce0000049c214a07a6d47f05bc65babbd01a96e2428b08447353ac65495d2098249ff3904238b351e070d3138f80000005556c4d9cd01e5799da447a96e3a7ef512d7384efc08f5905cdd1105a08a389833bc045ee36af39e3fb40c5a80580b1155f8a272e55793422bf5c35d80f6cc447b21fbbc5fa7f0cffd455fa2220fa1117d8ad3a474f4c02fd5060c1087a54477780d1cc0ecf00066fc185326cc3a000000cbbcc183112b6c68135b07838c6e1de000001787d385f30421ce04dcb2a8f38e83180000023c9f9124a81c2dc56b9400000111d09a5d9a03993219d706fc7855be239fee1adbc05c4219ea6c1b05c289c5816f2842ee0455bc137ce0a47e02a38c443fc7b66b15353037704441be0c9910000000000118de51aba2206d30157380df1d070cf1852e00a27c7613ab949f1197f12728c285be21ea2819ca38d20971b480000012b77035f448363a00000714441428707cbba8149b1104cbc5710805900d3ff0d84884d3a41bfc4343db0000049bb215822e33aa39956e8fdc2414350704b012d45445218269e47d66a4e8e28e22ac000003d4110000004abf443db20d78a30e1b9036041dbc821efe572f180cb51d71b60d9928a1f808c7e026902231670b66d08ee54894f684d100a0c7c6ab9476d2c07cd2000000aca45d1dda10ea24537404eb9107570289b506fc9010b0400000102aa111d54f2e58771c62cc0b1105f9575700390e388ee249df152f5d65b5ce90887385d9babf5da590000005a7c90cffd400000d67b2117d28e935c1bdbc0d6e86fec41e9be0501740cfac459fc8ce0f809b460d6b614264c5136000000000001a1fb0f29b5b2f70e01ad
else
0x7765eb7be7107ca28118f158cea48f54065d8223921ece30ad2c0293c923788178660636f989d64ed9a92c4b68a2a1ddab2ad91b41107086bf600ebe43a7db01c758058d633b707b70500000273bb89b53c242d80b65b033b601ebb03a0e2238ba84d6fd585c01b93d6e1d880000081320220d11a4ea0326f835f561c0e41c7584f923c0000049dc90000032fad450dec9bb43067f08f371c21f0cb86f624811088be800000611c47a67c08f3705f176cb1e124d5f0ace68718080c1ac178b83ebe70a79282aaf743ecc4806dccd6ad3928210f4c031ecd239d6311fd01e6e00000026976284bc00000004e1211b6a0669c4b08834be28a4d4900dce3b1f188830090ff204ceb210e620555c485620cd9056c3e016b1045524793fc5c26c0883140db529d93c5dfd4836358445c0230980da23223740483641d288111d8a50a0d30b0e0f7508bced88a21197f4ca86bb1116d8ec295184920d9916f55f832b041a122000005abeab36aa46c48002e97509e08517ec76360e2bca1a2448d26a058b0a222e0089e083b3fa4bbe20efde060c4c45b58c4dcad98f6070721cbbdc19fb6ef2de064d20e93fd717343b6a3111f288ab8cabbf64c6b71104e3d3b34541f80000009a428b90d019568cc0e98eedb835ef25fdfef60f104d420bc680a2560c0dc00000031e63c195e4ba7f579e51846e301ada42b0e000000475eb40f938672a11026e2ed360ac9b8344d20616822268dde57a130fa12b5308a32c43ddc492170a57d06b7a64e386222da88af692a32d4f3c00000019fd9b3b3bde79ea000000a1ff4c73400adde429711d5c81ddf48483d00c7a2988c503eff0f861ec539611063c942c43a084edcf30d872cf92103e35c91fb5000000000017871a0000063ff3ac9ad8b4d56747310906aaaef7c053231c5851d5c703437843dfc37bc1)
else
(if j < 87 then
0x1a1c30acb44000004a4331d3d0a73b4000b98000009f7db49de110816e5c2602ffa2815660775a693aa60dcce95da85108023a5af04feb8aca2d0c57e3a5d034e2d287fc0269c8743bc2e4999fb2e4000009e536967e747a2e9867dc0398e089f337c2941a924d26a500000015779c279e2a6ab70fdf852741c511e8b6e61d05c456f40419821907d0d54408ebc462bfe9cea855072275bb66d7eccdca90000023bf4cb050674a273b99e043e3e74dc719dd107f6bb88fec44132241f1278de835b0c86f324e223110ce0d0fb019f4279e9f21c4a45b2d4af7ec5bfac0000008a36809d8a502d4248cf0aaf1c1dfae6da8c1cbf8aecaa1b9fb20d3a5000000f9359409620000010f7e8a121df27ee055bb06fe6880a08000001e18b8ec46c7624582b50228a87a6ee888b1471154ac834063d38000006870b03ca4069ee84b7061dfee134cd2c4fe026aa03e349114f40000007ff6c9bd240e0ed0a0d93a3fb81958e0302306b7201b6c840580378df64ed4887b44360da37b85000000955614a7ae40db4566950ae734719603a0b4020d99c6fe4d732d217c810148087bd51f55c0cfc961751bd23f046da8eacc063bca06c368477d00000091479000001f595c22c8c467fd80c22d2ab400cfbe11045149a15be7763a7ff0706f0eaf7420d4a0b3a22373d339b78e5cae9fcf2341a9cd8a64930a62579e2d8c51bf2b09cdb92a3ed5f7c188e7b818344149f9802f983062c9e1120115b5567d0000014bdaf114a99abca8e9735ba3ef453ef10f73888744477fcdf1b838f2c179944455ac0e0ba1026f0b323047d146bc980d7c08d16bd155e001af253a83a7e4ac1d9d20e0ca7384e800002357fc000002f4db852b9cd18e8dc2871e3fa0883e8d76683e9a31008f0000000000114cae17c792f73684ff3a07cc402c8688c68a0699c3a9c8
else
0x17431c4c7e13bd0c0de60987d3646a08c3a8163ff10f5584d32043dda0c6e7000003b8b263bddc3b75869bca888bd8957d00d3d70636588e65040505251cb09eed4ce2f45cb9651fb4060f1cb43884be8e97794509eeb31ecce89b509b84057eb8373d40000035b2f0e5d908a22c000002269e1104c8000004475c0cfb23b095c99275893f60c2bb925f62212043ab76dbcc8137f89f21ea1af5109eba6766184ae98689a6000004594c0d27e59b97c5e961167b887822c43d6450f9b98363843eb02834e3c7b401b7dc7d75c183024f1de096dd13e60827d622259817c5f8516401333a2038b3d472278e9800000e01e75f6de8000004450e626ca0d551800000377181afac9f268c99a2660702224e65c25b8edb51ce17e5584612c67ad8a0c00000607bf9faf80000003618c385ef1d27e35ee1c727a018c81110fe2a41c005525472901146e4afbe1e036cdf58aa3fe908c7e82c1402029453e13cf92e249bf800000250f688db2a8c740be4ce5fb7c887ab035f0f0e3d41146c8a7214185fe236f41a1c60be3f843d783abf209e7b88823c1df4a732ae1800e80000000000220de261c9000001527c8c2cef00000037e6499cb40f3fa9e5e946ea70749ac5d3e4454f5bb4b147033e226bb4edeb4cbe95db94c9d31901e7ccedbb0ef158107e507aed22fb9040036403a03e50a000001a971600000290dbd2064c09ff63a0c715575822368cf336106c07c9ec0ebeb622d5e0a58c1b95906aaa044bf92e8f2092e2c94328ddb8a3ae926fef787302800000028ce35fa0a6917633d82d5fcc077f10327640000081bb2898fe945214711cd3e4cb1b6a2d16be50cd26289ac1bc41c76a3e7c948289a127f670ad255573ea22cf9292c92aa4d1863d2220ea477d18186481af0c1a59c1d2630f2430740280a2ad538630e936484eb7114e1)))
else
(if j < 92 then
(if j < 90 then
(if j < 89 then
0x11052aa33f80000111ee59d3612757dc07fca13fa8000002c637847962000003aa518b124800000526b488a62a3533018d620b3d306ed9826bb4707a8149863645a42e3145993023cd11086724de64323720a9b8169fb86f3d007b640bdc7666e642fb08db81e102a56b9d50e11892816c4c9c515463462a7848e2e000001c563cf97726d170d1c936945238a2983e097144e015fef0aaa344b904879bd2e47f088221464eb3cbf309ae883079d1d1e400000000001a6efd2a38c000001f4d88ceadd18f16e3bfa128312af0ac35b520e0c31d843031fec00000055a602f6fbeb68c43dc00d7af1d5d11f328e73d0a68bee0ffe00366181f2e4000000de51087afdd5dc433ca502f6d1433d0455ae2f30b1a243bc56e1be76606db93c7f30e82bc26f303b69b72a79359b801b3ce1349a09a49b8a32e00fd80d092022c08d47ec08499146ee01ecb0e26c0565060fce30707acfaa8988f1b055f51a1d706ae9070bbc21e8509c4503426ce931cb72d5125d78463c5ed9f08282b98fdb84e66d04cec5328d3151a8883d4475ec9101112d908e0e8c000001f8be471f3800000707c2d8cec1127c0abdb839b8e13789064cf01f39456968202bb0e2d8ae1f746753b2afae84e6f84e750361120d4e75275c88fa7646d600f98c32d1488aaec46d3609af853398077e840ebcc000000fb758e93201bf4aa1297206ce88de8c445e2b8e8d6f5fc90db1476126000001106827577e4df2234c9f02b4b86c31872f380cfc558d4837a2b4b376b475bd000000000003552a3a7ab469f09b5bc8759d8220cf3c3fd0253ede7b6407ca21214284d219f5f9a7fe10550ef026b2570d9a0a89c00c810526280000030cf89f25e0cd815db9ec2f3e809a730000019f79e138bb4017003be842735c5b5be2aa2f0000023b14a00000000000000008de103a7e0
else
0x11d411442682b7c4dbca30b07d80000018b1c1e3bc98fe7d21ffc1933400000101794f2f9c071653a4ae3802706c36800000f219992744927a78241fc220e9059ca2b91e2463be0c3929647c88ae106879efba896ae568a266d86f46379bd000002697b962d7c03c991d25b882b0d11f0a00000904d780000035b02f31ae2a2ab08ab4d86d769a713114df81571418d3f0f9b40a4f8034dc4673ce228c61d6db0000001bf4a4a07f0e95b23604c3ae760e2bf38c6e8e221c3275618f269096e080ab4675d00ef8f643cc2ae72e19f48dbc9b0000000f69000000032c5063f604e670ae7ce0000009a79087a6dfe37a339ce1d3d8cf0e58445551b59626e793b9f614f964d548873bd02157ec7ad38855160000021dfb868ddcb389839cac0dd62433702fa7916da6c02d3c4ffe3278cb643ba295b2f247f410a1e38545c0b3e7c27bdc220c5067ca8526393d989305a017bfe4776b0ab760711f6296b4a1088c000000c7ad8abe1127a0c5f10a00000115d53bebd867cf6000004ef4983ef5c5093e8bcf33f3b038cad0195430babb635f23176980e1b20c6ea068384b5218ceb78222ae07e46cd52880835646eeb09cfa8000001852cd91ef00000013f855fb7821e8849adb8d0fd4711147de1479e59423615452e8ccbe70f361096b248b8402f7a0079d38857843b33233adf6e67d82b23cfa9e4075a26ccdab00700477410b4f59f24100a6210e1e60d6d200000133d403db5e1af840abe00000011b65c83af38c87f009be94b3e42f2b20b065087b74253ca4c2941fc5986c29999b40e84d58ecc0c9c76145b62141b7111410d0fe052fd0912df51faa000000af1641f2eb0505d04fe1404dc8424035f5cf0c12581b3645a473036c908876634106387dd842471c7e1845f4af9d87065ee9597d20f1aea5e9818c50aa8a6843de671fb7)
else
(if j < 91 then
0x9b554d679036f2b174be09a6b0172c212932aa0536faed0fe8ec43df3036bf278c807ff683b3be1119041ed49e13aa851c8d97a90435d011ad0405b604c551155a84d240687fe349c514e3fc2aa1081686ce0821c47b0306aa397640c1e801ee710ef9818304a2ad404a7a06c3a62c972a0db4467eda73ab8000002288f3b83ea3a4c01fb14223911d949835b4cbc7be21eb9747e94c378430e6cedc9f85d4fa1bb2c357a82368e0035600f71c576020000028ac40e92a01835ed4a8c0657800beb0b18488c478064e3b5821c00001481a8970671ad646213b814985686d2c9be640000003d9310f54831b240271c3b7b6022fd1186b047d5022ba233c57962ac826f980c1a83136c189b9c2b74a0000013ae785afae7973a0000035ae089ea588a39000000060f30e3af8441421abcb053c80cfcc84459b3da826b4dfc942f868b2054860118d088bfa474b3ed73831a1ee080b503ffb309ef20e7fb80022400001412fc4b9f4058f55ac7f139bc242b4389fddc6c53c202bd110fcb3e72e1a7fa232b2147fa0ab38851306023d61d84b016bec1bf70032a730a6704bff43a5fea8c3211151845b9c76b7e0788304fd802c78411bc677d48062668e23381892a0000050f4d031b79bdfcd2de8225e5083be714a26d114f20a55103d6bd1b4a00c7cf0ecdd3ba7a17dd260f7ba0d5c5af92584430471ad67f0f78e4dd01ad543dd8a1c4620fabc489d5a134b70000043075000000bfddb141730000010aff6202c3013729783e83792a21ee81d6c6831b34741b61b8c411dcf4cbe099b1f145896120f9442e7c00000ea6df09a51c5ff549b52ed30c6000000893e970d3e3b0cd7005d880a494fc6472dd14da4e9ceb79cdd0a6015e1c36b81be941a794000003154600000019bb68874700000082a5575de20caec1577a0b6ee874b7c1ced6
else
0xfb750131a6135fe19d573c1630629165336700dba18b1d006dd01bcd6121e9000000193c2bbfa690ddd033fd891be814b9b8a3780382990551a0000055855cf8bdc675fa896e8154e5d0e3d11ee9d3cbd0064e486abbc17fe88fdee917f80c93108135614b9676e4f880b564ad0213106219b507673ca46040dee535ab208c78a7c5e20b197473c886c3bc749ac9e3e30ddc28c02d04435800000000000ede8de7d682a6f9a34f30000003577e0c6ad674cd2b9dec19dc6b52d811eec870f2e80918a50a50d8648112844478ec7dc03ab7d4362d84050d26fc1728cb1e074936e0c0c2bd0125d835a384f78600000179648157440732539be669b6f84d37443dae721380d85433b3391a1f8222c505351340e042d70a000001c75b02c69c7f52c0beb692ec13dbfe23a13a3a5ff07b4a9e5a2400000138a13041d080b38661523a78f000003b8ad829b3410d971778a3d3a71f2d72250930ffd33ffe8e30772341d6361d30ad5ec187762aff785f50823bed204a2f119117acf088a7c40574339bd15562856f90361700cfc10684a164a28094162a6e400000071e544410e525c883ed980000046d72695bc1a0dea07dc41837e1d88d1ec16c3d3ac3897e3a4984e7598eae8cb159e0c9d8234f0afef5c0f621444aa1de4c4e6f80000001b0ae5e86f06aee27f14400000496e50fea9005f0c1da17637d3052b4181f50e90f4111e980000123b30134d64b9bb90262400000000001338887e3a01a75e22ab712d4488df08ba5043a7b058d478e22d4c4d7c6bfeb884f00000021c5c8457f49275827f320588f200000142e98adc1e05b769d5e35c3d84f9314441ea344bc000000343c0c59409d5f801358880be84415647d5a6a8e5960b705b53e385aa14e8508a7683830d15dce43efd312e342c7e8ca3d98c8530d16aa5f7b60cd94))
else
(if j < 94 then
(if j < 93 then
0x15540874ad400000388b400000056fe0443721d8d0000000896d1156c6aec9f07148204668ca1eadcccf03e8e0e9eac193120d8960134a06aa79a15c2772dc24f4ea782b8355a2236cd3bc1e034ee8000002aaa031d1b00000074ff61348607ff7479b4cfb712222ce4eaeaa341781bb88c77c411071459e0400000817bf10f65887b01425503a18d048e2000000081d6222fb21748849f901bfa6202b00135c800000709c126e9c0dffda86ea08e17a1a2c92037d3e329874fa88782a077d1be67c05f1060d7b4087d8bef6348edec1d283726ead1e6823e7e4054f600000093c6c98f18ff5880d8e00de161a591c5ccdc10af2241995e6b5aa02b70674c04e70445148fcdda7ced417d6d82ff52157dc2b2b00a5ffc0f9ae0168c000000000014aeba396c808247b7d61c1df2a3facc998e7bf27c8375e29f035305fd800000fab88c18bb06550303718509d80000088b40921ee528844deffa0d6791ed39c4052416ac510164800002203e8c2de4432ab1e5fb86918c289f326d57b903e01a870ecbc3070539022a847d4a0e0b4111574452be4133af82870b68cbeaf61db9a200000110fb8883a4000000ded609a6c8ed724a37ac23ed301ac781ebc844388315ad067d0aedee80000003ce9067e14e078075d7a0efd2780d539fb501ad700000006ff58000004091c22fd31a1c288830c37989264dd46353a5e078241dcabcdd05f4080b6d8065f2220b30000001b7b005fc215bb8000000fea98000000000090a6026c6b80000079cd99127d12a2f44bfbc0c05a1d3ed321f55fad923abf303e553ee3bc5faf800000144ff1778322a7290148a6ddd83cc684b9158000000d5c90aab126470a59f1c0000027166400000224de0cdf88383d000000171ce5b1ce000000363802276c0b88aaf8aec183702188a00000052628dd7ec222fc
else
0x2aca1cc07a5e990538e2061659e00ac4470afdde60d7d41c8238513101adfa4af89b0eae843d7b34edb06552030fd150826e8da20704a2ed35c099f6244f3013461b3afe7c9820c9941f2e69c2cf868d702815f1a1ff88bface561e8ae2d1d3c5837ffc37f3699666013730e92c0000000368415a4148f2980000014127060f18383545b82c48a9f486d796bb2e439e717afb47a6892724c3d154b6ee62d7fb8a12ec5ef110c9ff1127545cadc97676caa9082fe583d6e52cb8e461de21fcc80767c689a64d7c810f5504f6ed18c4e0c7cd3623f05c2e0edfa222af5079f28eda85dbb3e0c3cc000000907291dc241bca80a4c99a96490329e0dfcc91e70000000361e6f01e37577d363bf014330531960bcf702fa08407bac19b8120ea3022bc18dd44a3c21a1fa113a593b8661bc9e46a640ebfdccec188d88f1d5a2887b4c5138821588000000582244cd50000009ae6024766c9ff64ae4d969e7f027b006c1941c9ab50a594763a41c8f8d15ff75be929fb51df9d23eef103857887af807b3c0bc9e1ca4c0000001c150418a415947826b8c19d411beca832450886a83f54222ad904f55800001d035891d930a0c706c725efd9a224ba20e7e0ceafe2c59a0000012dda37d7c80bfe51cda52ec6d35f64a747ccefe87000004f9a6c0f1b23edd30000004d2813ab0cd23e177d47aebabc68d8a950ea1d94500f23db23c2000006d34549c6e25e588e52cf8be5c00000007976a4bab080ea8a127843d14427ad493f4044b2055dca098a170ce037d6ac0000016b8900f95035e04189b695c5f6017da38b2a3779603cad0fc603c573a10fd2f5d861d3e60507c4000000c2a5894560273d80697c526d1497c5041b524e1c00c1eb058e1035fde5135c202890d7cd86c27400000133bb29d9b08e6c8065f0b83e905ea5b9127a02d9813ac1)
else
(if j < 95 then
0x94c451aeaf0b4c7a0c2ee01e4c80000067d2423ef7623460e1abd78f68c4a86114678bec9c000001afc3a3f6c20722c11de80c1b0060c800000067d440000084a4a2ab26827750149931a14e8306bc619a6e16ca9bde5a990902feacc17e3387e78336684458c202db28bd40e2744492ced249c1ef5807096808f66efbf143e7f86ef4429164b218923b9236eb64000007b4eb115c780000043d34455d51aa4a4a6ab57dbe930fcb114481ecb400e9883cfb35394719f3d2377442209f144f886c26c4053e37ac010f4d882b9c64302343e20a5cf0882fc4ff6a0000001ad6ae1bb413198469b53a835918e201c1ca1499d18bef9197b0379164a8b74e76687ff9835bd63a4db15365d0761ccd4d0f3ce51535d873ad8675ca3a4a5089cec0866120b4821e9e06142b4b7f448f70d41c3171db89771d0e5fe0c1900000000bf7433dc9241da3414180f6981e38d2359c06cbe247661ffdda87f5803164030fd5695980c79a01ff4ab399da23ecf5ac94745786de740000144dbc0000003c6997cf43187fe06de1800000749e53cbf343b2f1c3640449aafffba060c6800001f45b2000002a3198a321663f86000009bd5f837f8074908ffff74eada80000043d8f1c1ff2bb643ba75018720a3bf60264c1e8cec355248735f82df71b68a5ba9081a85e07dcf39e690135680000003e5b0041c5a8722246c91114cb2db884cbce3a7881a1ec2836de4a10e1adf8248fd3706b419ff0e7de71a1d3096add3affe708b30000010c76cc97c4b0de81607f0562c13f818dffc44555324b7c0187a2822d60eed981705d67722928ff3d54c1c62ac3851c113c47a77c888ad91353255fbc5c47ad023e5a0d3440eb2001b9000000000013cbc5110e88e93f5201a2194c09df78a986bc82cb808c281154d03be5c2690e102eb044d38a9bf9c7b5c0d9ab
else
0x52e7f0ce62c7f1dcfb4b20d19a880b2c477d0000000000051829644d410ba8a1116800000076d140000009cdf0e83281eb2234d98592d78887887dfa0dc2bd6ff7c0337b8000008cfbc83f4e00000043d4a5efb591bee874ae89b338648e8060d68152bc076c021ef3067d18046860db142a6d806bf600a3e1a052e48692066d01d3a30da42a2b4c203a56452b9d1a32602fae3a97c8336f137520533c41116e0000013ae6908df4000000ab0217c5e42b0b3166fba476dc44144030ba48daba33e6e0ab38a3614864d5d16a245652400000993d650062444506620657e1e108839c5e560121c9015ec84827043876f7cdc0a17812f6b83525c000001d86d0c7b841dae2ad57824544800001957d23a49b092768f982c47e762ccfc995594aefdc35bc60dfb67384b8d0e88761b2d9bff0a1421e61401bde012ba71d063939c1436131219a609f7d0a26e4d05526d88e132e40acaa00f9640ebba1534d0000024e120000008f3ec17ea5c74f14e268d4c2450d0e364a1af0c3a5067d38d123c475fa760a1067ef088bd5f27381ffe6105640000002416c863a613f624c6a495ca2c0e7860000000000093b66035c506bd7851a1842bd22b2c59f25d0fe62018f5921cde35b95835ab009dc219519026e8bf4619cbd0d1b5c206c780ddf50477700b29400000427ec0121ec0f3f60dac48000017d17c6e31d5d76b43135264b0d243e10d8e685c31c6af10a34c21d04c9667ec000002a699100f31b67a51a1d8555c306568833e14079b2035b72c3e90e22a80c7763a3c20d741a723b5dd9d43ebb69e5e6a147483183a2a6a79f25c2bf604aaea88fb6e44332c9b3ae11d871ccce1d7068fe2fc183f860f8f000001ca77800000566681d078b07a1c2174080a61060e8087b28dcd864117a88ac74f2fb1d5d42222b8238d988da14c91bc00000)))))

set_option maxRecDepth 100000 in
private def slotBook328Slab3 (j : Nat) : Nat :=
(if j < 110 then
(if j < 103 then
(if j < 99 then
(if j < 97 then
0x9d04a835bdcf278aa8e0b37badcce3d8e0ac03f46c0000015136c74fa8003f90e0c239c288f7a5284e1900000087adc01ee6055f86f2670c6214000000cd970c45792730e229ca3918b47d5d806b50183ce0deb1155620d0eb210b0e529df08bf8ade3fc361220000006fc53f8e11194c4bbec08085b1665ac8d7241ded275c41800000447ec8d98732ee80a187942796147870707e04e6c41611d45af80d57bc762da32f1abaebd0c9ca8306c045ffc8eb9c87bf39fea7456930abbc2002fd4e1e7d073b63f51603e71b8f768d20c0239ee3f4ac8000000bbf0b798c0e0c58cf38dd71f64f5c56e4440a9bba4bba0ca1d627471883ed0205aa0dfae1d2408ac7f054d780d0fd477c0c452ec235e80b8bb2702dce6fb815576029a6332328cc33239d4e468ab1106b1b3a0493d20b87af09cc0880a99352ca39b9e2aaddcd276dbeb5e352970637e21f31000000d97e8937f50b0e88183600000000000087ac40000024bb9000cd80cb81f6dbef3e998354b045a28287d221e82022dc9a1304b2aca000001d3c30000001355ad29f01206b4fd7e25a548408d202ad747224050996016f80a5c580eb283810cac96c09e5d850b284af668c28c5cdde06d63c4191d24edb939e3094b647db66049710815602b7001a17225e8a0616503574839fe0d11f1254670483454c3b41ffa0682688fcab16e5e00f5d81d0e000000043de014d507a2fb9ee50800000eddde11047a4dac84475a0c2de51eb68c5a80675a48ff4b1d041c8e71800000b78bd11f70065d705551c581ae693e08f9748065ce873c8111408000000000025ac04e77d8000003617438fb4063e8c9bf00ca16c220aa1f4de80f2c4435be00000a317d090afca0ee037b8e0a370000000b745a228c46a0da8000020859450ebb0ecef0eb6053e61e239bd4fb860aee44473c658111
else
(if j < 98 then
0x635f026a10441be000000a4ca0883041ef626521e060c8c357b44971b20b9120cf200bd78000000ef86000000ec6140000119daf10f691e0da02696623bff3548e087b501351295db329b35074b3c1b9e621efb3df160e43dc3ff4a3a09f484c8bd4ee0227d21925d83b534f2ecc85d6f02dd6000000be21426b692e88c0000000aa649221c3b6930176fa5aac09750a265d01534e1714907118e00000254c704e670e0178865dc068418d5a5d72142231c919ff90ca250c6e94236fd117d2803fb075dd25c6970684790673800000728ea217458102d64e38327eaa637431d191c26f560d59a42e67087a1044382220979f27f088aa8cc021271a30000006d25c455a4b38952805286bee420f284ac8f204e4cc965e727f4b71b31c77bcc7f0000000fa7e3110d7afbf6cd9db621e995ba7c0fef04a43de4c686460751b922c443d24d9935601f106308483fa1b09c19d4d0eda40d9d8600000117ec03376cde51801b967ff70a316b09754401a9c077f2c412c035fb2dd6b80e27b314a5c00001060c5197478cb23055d14657750000029827035bc022089749d1194264361a85c6b18e0d628d74678ddcd918a8da448307e81c1962f8ed784ec8ec3e13aba00ced5064490ce6115c3788aa83022c41f63642731e4daf02469a94c2b528085115c77c8788353a809f920cfd910f7d307b3c00000909651217f000001a8bde0000039de5c522dd558ee0558e3f2c1a97afd5be2d271ba0d7fb885724145a0c5982a14f00fcfe5bc9e413fb40d55b8307da5eddf276989f265aecbc1f998c09fbb110f3ce6f443690a1c1ec00000000000375ba034896764c1972b1f27be23b8837fc786ab0043d2a000008ade21dddfc90bcee28e93023a37c2e8000003ec9d635c7bf32d0f25d42edef000004bff44000000c7961d3dd031edc6890e1b0b5
else
0x75c7e86c3b04535a9869a00000492a125bd34000001597b018b713034c0c3af110db106978058a6109f803c2a06defe3e1fe00000423b744532418546145ad3ba76bd664074fb5114d1244d5451b7de67e7250cb060d1856f841a1e81348c0000006bec8475100be1f1d2df9df35198338349988cec0887b6800000220c34ead780000012042157b608dc80d07b8409ad144e1850f6031f1835ad00a7fd6555588a2d829376228eca3f55848764eb714d27b11145c23f67c0555cccddf4c4b71c326dff91e659fc3d9a709925d2743021e9d4314f80000000000062d91537280000036c3c435f9064f204f081e3b3adf3ff49fe90882801bdf40588b1195b939ad52dd2603cb31016906b64c7d8e61579279bf288f318deb8010fc410f76800000bf514f3c9c1fcc826d3e8655b2171ed000004c46fa57fb81ceb5104f586c370a9b223c15792e71af92d03641c900990ffc4935e404457e796192936f011a183a54e104c623ddf029e4c1bf342238e118fc84d36c54fe60c9d8036fc8000008c35eb69df8f4463e57acfbe061cdaa1d3cb3b6a240b9e2a2e111c46f80000019ff69178d24ee20907057671c2fd9c11044000000000000afdf0d8c204dee8445d80000066ee4937cbc1bbac3a0b71dfdc95596c1c1df110ab0efe90737391df9b3e4fd467dfc1c2ac4c9a0029f35c1cf1f453c4518a260d337e4338a3400cb140c5e712d41832bd4143b4149db6f9d42d82b81df123a5db112a20aab00b9936be8ec000000013391a9ba3b2ab0000006fe282d90c0c3e51890383064836176055b932bfa8883b4000001aad106ae686b61c38392936303e9643377082685aea9c724d5a88a2cce077c0deb947c4606c2b4081b4077c609e7f0e92f8397feeaebf000000277340000037d3f10c7129b209d091a03dd5000000a12f405906135c0))
else
(if j < 101 then
(if j < 100 then
0x1a8188cb67c04f290e8d406852a3475044160a69d41014a8000004476e419d5000001f5a9c74fb8b00982a14a8e2228355d80bf8a06ed48a1e98389feb458a48eccb7d6bc171ce1adae03e7a23ea54000006fe6b8f6ca07fed1f5fba4cb8b1a1ea989e095276240d81a09c80cbbe517c8e0dfea11e78887b840752e5bf3c69f4f800000ddd8215bd30656430efb0831c8674fc117d2844704000000c28b105f80a9b7d5e0b27cdc7225d90b36a81fbce33fe8110560d0f3c54db40000024ee30cfad02ea6cc649035ac482e7ad2715e000008bcedc2d32408fb600000000000c5bf4cc964388f010f4585621825ed4318de06352c582e1a5f70d91db06e760f22566fb0e0d7e61d3ca00000007cc40e0cf1186d157eec1adfe21ec68bd6eba02081919aaf8dc7f846480a18381e31cfd05e4e88307f53a5ed46cf92438147fbd6589760b437313b53f9fe40b14657ab520cfb8e92f074f5a99e101d3e99b3b78183043dfcc00000088b6406bfa3f8b012678874b2c61cca40e836737fc596c0000004add463aef8cfa6a7e58e68577000000fda500c356134d50a4de28bbb81c2dd39beb8e0e08feb004777891fc601e4d86c214000002b2a3032fc19ea7a7c92e228af1375c0b9a2d65b92134bc37e411066d63b3d1114bc0556d0ca214455301b0e5000000d0efc00000f4ba61cc0b03b7b541998202d6000000b12a143c6203ccd0ecce0813c8483ac58f425d85404e77435720fafa9061479284d4dbb226e38600000247efa15be12718c1c66580000046d36202e585fde8000001897c24b4c1d074a51cb8dd646260be00c05031fd854d58221be82be70de6b932644220ce8ec7b81d6547134e00000144c388585926f56baebc6e0d38000011df96916631c4fd036fe01212c09ab095a79289640331442a69a1a57b8000001afc400000
else
0x6afca888b3c69f4a228e7059d308a7115cd9ae20fe71460bb72927adec220d64fa610fe3ec7a324328cb1a1f7812aa8b36b01dee48ecc90e38a83615e0322d0615e831a954b9bad5aac1c47f86f25c000006180c9b961aae1f45f199115f9037c391f654dcda6000005538b03bf244859a000006c8cbbaced61b5aa968875e0500eaf263d5f6113c71a14d0a1228445b42029882bc19b86cc363943a4cd06b478483ddd8116000007d66f837ad043a981b0ab02fce1bf56467d941ad9b48ef30326c570f2e000008264bc5f760f1f8c6ba30475c200a2f4409c20000000be696d02034bb0d37cf0e0d8000000000000f7d04856d8327c412bfc0c1e4230c84e9a4000000976641a1f40bdf5875744284a54af51a08ae40000076fa90ace1a082840c256966bb338442a71d195da41ab96606dd8000005653a1d5b40dc4a105f9d4a750a5eb806fec06e26c2b770ce0d243110b87fb99b52c07686129573f6701b89e820ae722b01c9ba4222980111aa3bd5c86c28c8d37c000006c9c706b7ddcfffe273a07bf570336f01bdda06d9a5e9f21758cc7b714eb4f40a8712d52a07f74866add00000482a206f3aa1e69405f56876e30dab60000000904ea7577c1c1282b2d2060f1087bbc1c1160000007555aee7be7d1422aa7e1105b0883906837e1b09e5f45787937e65be41aaa60176d1ad7795dfa40c788067753b7354383340ec88023468e535c475288301d2632080d6d41892a315bc00000153cb4dadf854b6a0000021c3c41ef2693c39013ab0acb3c3bfea000002691742facc463e26ab3b06b5100e3382ef1abe2b100000098d90470b91c1cd1144a45bed4355b70189e176d100000018d6e135bf01a42a757ac40980cfcf95a6688e97e171bf600000637fcc706f808da6289b5196492b5ecd2eab43d7f48eee98cead43d9ca05a95)
else
(if j < 102 then
0x38d62031f4c183ee6c9b4118d3038271b8346045cf014694427540871e0d6a5674e2c94369f237e0000002b1f0aca10c797a202d470ae88327f01e378520f43eb50034e31707307a5f83d0f703722444964d2ba6052e0b84ff40000032cea117eca01468405663a5b0000002672e45efd80f58c18d770883180000011245061598a3b6414fa12aba71104b41b7605692e9e6c306ee4000000285de3a4d06e1d09a5b0000000226a445fcbcbbb1c000012ff966a0cb12028406dccf83a33ae288bcfe517e6422dc817c5d0000024dd180c7b44a73808da8c59b52241bc1bc48c74bda0a5be1b0d80d6fa8d06e0355be89795076f70343e8c2cee13e9f0147a12660c44180236be10f56294e243003a2d38906ffb2c9e724b5820b8fa04d7689066058cf6ada1475c600a9a28c82660d8f70d56008facd72be41bac8051cb800000000010bae027344cf2e0835546224f869be18592c41bffc42edc077e6088b0c73f8c134ae05c1ca805847a71a0f5f400000000001e7926e1b8f214d73ba7f43b38e062e474e452814267c96651bef195da035f21cb3cf1149d144fb0126dd39d12ec49d5ed59369ece4e1aa2a6c87594700000000000000000904e831b484555c505a700000152f180336a111fc354648e9eea169580000061fee0adfdc71136651ed0d7e7873a5831b9e8aab39ab440f9652581bc17a0c000000f93051e65c2aad95361cae9635a87af19d96281310147b800000284aa216d696a5de2291040dcd0000000bfa0443fe3b8c910f79c72e90771fc0f3b010a840cea441aff2239f92aad086c235f5f02df5d91c1351cdf040000000000110d3408b5d0ded2920fe06bfc88b30418ffc0a32ba2cef8342404cd2ca4fc317c563e2b04749dc000002816e9181a42813ed22eb1a861077f452cca06b5aa0902d44a258711f60d0f3
else
0x5f76b03e6547114e0c99c519e00e8278441a82a8f00d567800000189a0239d01427e0aab2474f5c9a7fd01a5a197f3821fe82aac0403a48336fc4dfcc062e80d5d70000000db0e0d7ed9a8ca9f3a905f1cf45de606bf711663519b762b28892f438ee2b66474ce97fe4c65e8507045a74aaf1ce8c4e4c1fb30c9b04202e70ece0087ab824492586d0372e6033e9415596000006317a8e9e70105d6000003cdd73bcfa42979c02a8c2f66c0502b800000728b41056c06f3810446e0c7ce884c5b0e21c35bf621e841d25b000000c05344cdfe1105486601a64f6d07e94144fa3da250b37021d9a31157721d5496df32dd293101788e23ac90bc7326ed10f58051a806c6d6000005235c3af6bc33d36d4bc98dad08a26e018386139894c97b13d010195ccef7f46f0cf0ec2ecff37ea269f060f139af001d71c236db000000000001bf52f80e514271800000000000e0b40000008aa50b6be8bd3dc0ffc812467c00000275d375c7f1bbff50589b1aad310e5ebaef61b73b2124e7670f006f35d2de700f59d65ff53dfa35bafa9039bd1eef63846204057c00000234e92b58f0000003faf80704d82ae9442f64236b22323823f699591ac202860efe7c79f403cb9f43fb17fef2867a700000086151155721dd0e9e155b0229c22347d12e483751cbff9aa45e24c0268495f02f4eb061632150243cb520c685619ee049224361122039d1026f8000020cfa42a6851106e3dcfc844572df3ec10f7793cba400000eb88200000342a75d95b210fb00adeb0e83241af4e07f581104d43a7c523b905ddfe88a5c888620944f021ecd1147d8313a047746d1ae0101708be3ee453ea72713693e60000027f9070b4c16d9ec8aba6ca25c46dfe26facb051728e2d40144f1231ff410b88327f0118d205bd9452a7ca23a33e4c8000001e0be541d32108eb)))
else
(if j < 106 then
(if j < 104 then
0x796c93702437b5a25c841627e4452ec43d8e226dc0000008ab70227a64c4848ddc30cb3790ab52346c206a5f840b7e6cfcf03cb94a4e28172254274501ba4477f988bf2819baa000009f25288aafc43dec1c1c1000003dfad21a94abdd8f4f9c8219b7a7c9c00d4a139254890b59881cb43ccd79a562a9b942690e05771036c94797a4247a60fa8c1fda006c3c9074c0fb4f3000002f4ef91441a104a56da5b06c3d00be5e64c772736b1f0850000003b7fd55e8e1e427c74d31271db1d2500a77191abbb114c71a17f0306102315ca2b309a5e0955794aebce2b3bd06bd291fafd1a796bf39896ffd0e9290931b63890c0ffcb2ae94827744062ba441c906ebdc00000339a37d7fe3572a0711e892a99450cd83425a4fd1c22fcb49c3526b57569d7e202c6920d241ba994ab384f346911d88000002737e0ee3c1c02346270d83b86897044117c090b0a3396d194b40c961036315224933e1bb20bd985636c80bd03448c9f24d47ce04685e8432c37e64808a29a49d76221d3757631e2ff55970ac72990000001a7147496c000005763d44871a3ad9006f9281dec498ea074de8a4b0106bfb0000005da5015bdc116de8e5628715f4202b301ae5080bb83633c91d9706b42010f84771d529ef02d7da0d1324c4fb6f56f088a598306b91d16e228af2d6f8ac17b065114bb4c3144fb83be2832d02000007257c906248689ea531e153c8908066898f323a7b51d25a000000a8f6ea53983725e8680d67cbfc5af5c34a8236e768000002f8c8051ecc6775413bc341ef900000056f34a74f13e4b40c8d38ee318000002b9c70a6d186ab0c5f1f2450520d6f20aa308441fae1f9b09be04c8fb170f4286292110c4366b28000002f7f0016fe000000d37dc1398b51c17833e1d70d08756e6118f9870b913fe54abcdf26ccb8de65a4799c0cfc6
else
(if j < 105 then
0x88a5c0fc2590e1662b7921a6338cbe0c29174289b01214f488b5074f9c1b0a138b421a811175dd6149e152f5300000228de6a48d980f6104cf0270f64506695f949926b2a56b482c4e448a93c73ea496ec40c784000004baf283610c0c38900000192bc822574737d110f7c33def5ddbf0c71dd88a5541cec44df64220d51195903f668452a2f34ff0f98b807334485ea21eeb1106b026b8cae7c932aae36cf6000000e077e0000018ef1152a2c18d5a3045b31258c026a5e8fcc0ccb31d7c180e3499bf0e220e9780da0566302719622186159765062f400000556ea11151d016a800000445e1509522478b83771a2c4b20136882621c7e6520e38819f590e8381f25653cb90a24c8030b9857132000007d7d1cdeb648512d095c26a8f781139c18324397967704f4947d4141162a2861cad9217c2c5f18e822f1323cf833e6c30b3225b87566c48e22ae64fde49a972594c0371ede6d5c4f8840d86c0000001938085c8b132f9038db81bf462b2d101ef786127c445e03b98e53a6f8707794dc86e8df50731235073d131300d6fa2cd4cc2d62c019c85bec86a4df9ca3fc1838e2f8a473048c73ed01bdf0120bb1d5e7143774117de000001523f9d96f96534a149e86845c0e938400dfb37dbf254540aa7bc835ca142d725a2f918a50475bc0e1dd647dc8dff485bb3c222c72524e0000010a23503bc34ace8c67614fb7b8000003ef7804b0c9eedf848af6144f8887ae054da0df9ef46491878a74ffb7c69a671104fcdfbe800000041ed1d27c8ec2a843d40834962c114035bda287880d6e92b3d18e920e16f9c2b4cc6e5e280000074f401c0f98f9f08000002437491d860756186c3ec0e19b098ed9126e90bb3043db8312d3771530767a5a998046cb11a36b3ae35056946000006dae28acab12f4ba9baa75e1760cfa90479b4a0dd9
else
0x335790b569a039925441e86c2b41c10e2229e1b3454ffb2c723bcacbd2391d90000001773e0000010f4c49be6c18fb739bcb04e7a8d9bbd3469e00000847e612536a4a12c231f6129d9009adc6874a17b361a1c7c04eb8c4dca38aea6d94481f2ac1abae56f6d7c55c9225c48e8743b19e344db3a4bae5a1d29fece0d8508f45800000022ba14f7b2a70c3993f6023ba3065d5035abd81178220d114e652db2a047da8000005693a077d400000014984063f7c0b7647437c224c90a4d9a557317d10c535f2069cd80000005fb08011c0d9b0c45360405acbe8d8110650d43d05555e00b3c368c38fa708464d6586cf110501337fc18fba1abf8129783cce2549bb828dc81f7529187d170d5c69e4337ae586c3142b79e149ff51b5d01c318000000c6fc00000478a8c46d20228c4000001e82d96599233ed68a276a73a3844328222c547944a01f3cb4591111f00817c15bb402271a0afe211067a18b18f68ae4cdb51c9d4819e7c19d78bb2d788a5e0887745553603cd06eef5830b34555d6eaea115367000000f277e000000ddd78000003615e455cd4ead2a6d38c455c20c9ac118eea81f70455c64bef05f9641133457c9a03199b1db6707ff1c57f460d7b63da581f2d684814aa6aab0634d000000383c600000022c48157387415c095180000038a238967960c1e082a7dab85e400000c8dad00000026ae231df43a0896a6d288c65228dfe241bc1d5e48313bc43d74000003b034887b9c61f740c7af57a4c91e8283b02828ba046b668de668195d89d58e00000050b014e4c8388da3222bbfde881bb5a0cfbc011ce0aaa901794d112884232b8307bd9793049e4b9157a800000239527a2e0060c8b916d0459d4ce6881106003bf5d427368789d87a5c10370c07f8253e012842a800000405fc202c588b4143830c42b603a589))
else
(if j < 108 then
(if j < 107 then
0x764d2466b8c6895c2ab85414c40aafa5e678a1ebd91fc5f03221844d24029e11d2e906c6e4357e2146e0078e21d351d218ab3fd99060e59011c8b335a220a71106dc4270984f56142cd2aae490bac1366b262f1b159514787bc6d2081bffe11f4604e730f1228000001015c02e214feedc000003476902bfe8293d61add71594eb4f2dc1875eedf880f3640883e894f86ce6b36b0e0228f6c1952e0df986dae94dde29843c22a6dc510a900be2ca088228cad560e30117d86854e2a68f080d40883f02b36d06de3111610897840000057707089fac30b44cb2ce981ad10f568df36c3873e1af96063508000024a12a02ffe79a6119fb6868308edca266ec2037f94000006fab28ec6a03be1400000144da0b86206b644455982f89b4eec50762686ebc4000000a17e8000006830803d8d2bfc717e15e357361e6bc111644df73c195a0eea8e190490483fc1a920aaa4b1107404e7141abde233d702de3000000c95b42c33a06b610be2c58675a0c1f548737999ee41d946122e09fada09067018d921dfbe1ab7447c20a1696a9139512aea0fbfe03750a6d1b154ecf0a126019bac0d68e65e7d901dac35fb0ed7cf000003dde2a24d4b114c36086e814c84000001caee00aec0fa784000005bce71d8561b3be0527a4000002d1e2abfb79102e0de4b195e594e6f2a64b160b0940a22a276ccc289f0202ce1ee7ec443d48702024854587f3b492a81ffee16be37747b088bec1bf993e5a90000004d4a05ef9c202ff2bb350ce624941fa20db1063fe033790f4510de5e36f1709acad8477a099b6f8ff4e35c2ec6ad2506de94eae18d37c035f3e223ed06b6d0aa3b42fa70026a82e0ecb57f80687ce5fdcd0a5e4882b14d8d16ad3f047e36948bd011d50d4ff334dfe9f724c46d3c252c11595245428800000d84cc2d2880000004436d286f6
else
0x1c1e3a5f1e81dfb6935ee485634686911c292593f110f578906c80000081fbd6606a096260000000f1a2270d58776a4aa642145ba066fe02599409bff16ab69d872800000057621e4a4060e84897f245bff1c2b21c1da05c2a045182000002cced80000023128c72e07714f800000749420fdb800d6f07d706839e62b2c4155778658b5ab1c21b0c001361c8b3c9a814a328eb286054f5f08405980dff80f365027a2400000957d2066f003cea1b2f4cf68f60d6df81bf503615822f8c4e9dbbfde184abca13482045cb81622414bc0f338709071090be41dfd8000001425d90f03c06b66139b69f5dd92937043d10330be045dd880a08e1318343f61c44f8000003b32006fc00b4508e9f2829378276270d87a0133204451a345b31137ca32c24fbbc528c8f3052233cb0513f850f1f930cdb8526be41566a4d0f3373748e25019b3c7fc250657901bffe7454400000a2de41043ac193df2929f4c82388832c355feb23f5117c1338fe485d624c4ba258624f92163f9a605ee01a1d3049709b7584f65b501a7a88834d1a986220b4000003ebe551f2249d5b42e00c2701a1beb7e623219cdcb47524539dbe03c9500000017284171ac6f7911b0cd986d0a111ac8e3db11b470f9fa4455340c69e0d85f0306a00c5c823b9d060f3888b606425aaef92731c20a5a31db9a054d2d486fe0157741555225aae75c5ca4dc7843d1051f0b43c5a0c8f2a32530edf9703e538000020fb5e3b8af5bc7a456fa1dbb503fbba2f41f832bb8187fe0c60901efc2e7e142c12e0cab5509c2107259e772efacf283dfc0000004f18f146be8f1e29f9794000003e4e121954cd664067bad356b3064ed032bdc281d60c1cf36851cfd7b83cab021e918e0ce8000004476025cc1387e40a9a281a1f66b09b87cda03d334441e05c62117c668882a4473ee22afe)
else
(if j < 109 then
0x1ace8796400f56e2aae86654c0f7ea42877a84593077eb8882505573200000064ca980cc83ada00e88b2b949830709373ec471ad1a1f50a8af6297304a51417c5c9a745d25e200c1c50b8f1020b4d25f42389ef0704708f01818faebbabd8c1e33a7fadb9be3050eb52ebc83262c4ffd9114900a0dd862e2c48531325892325186b6d8453180c9b71f810ba3700463b0000001dbde00000105f0821eec118ee92320550e54223bf1d0548886685894414bfd558693eeeb49fa901948a4c0fd845d9c3817e1d9eb111f08a0d20677060dfbc48ee6060ed00e5760bce01536e800000187ac0dbad063c20f63b820f5e034a148552000000289f8228bd9ef78072e94cabc91f2cb1216b35fb3407972343f8392540e8390761631b7fd4fdd8483f69ae98cc82c707ad3cb6b8c43d82220b303e5e052728509ff1a3d22aae0085e886aeee5db400f2fa9a2a644bafebe4ff212c84d6bd57e3ea343e411560c92abc7775c220e90000015124c195d255f9800000131a850a1c4e55b89375808933c7410c00000781550e8399bebd206dff3949802fb9c23922d4d87120d80febe80b55c0ab3a1a27583428d81d4a034bd3d6053647fe86382228e38ec53a4864c1c1a4202890a0ea03be40517b00c6e377145a11e24463481eb87060fca72db400000127ca06b7e04fbd4741ca1aac00a2ff000000447bc32ca51c45e9e579835502a7b224453a03668162dc119dee1d41a08bf380000022e8a260b70000007f18c10ff5673e2c537f042198631bf26151149f6e797460c7f52bcb38e778d0d36e91fa73bc9f037594f368613cb90a27b30c7660ddf029b904fe588e5e6a35baa00000136910b9548441623e98a0f875000000902d4000005837d26ebba23b4a0e0f88eac3af23c014d4c0dbca3fc1f34cf34361680c9be0fe0b9a6b8000000fb4fc
else
0x29e5e0000001b1441cdc46967486c3605cfacc38ca1e5afc76e4d369d02a6fc000000e9f642939d34ac800000232ad43831b31df24307a80000163337473e10804f0dd7359cdd209ed6110719d0d9800000b5cc4017dd40eae43d7640dfe51fc6a850a360db463a09b11e683d32305557b292a94762b0ee23422df40c1fd5e6dd9659e4000001348c596771bcdf87412659fd69065e84a7549326a3a085000001292144416d07caa43b7880f20c000004bfdd472e2800000589a83c0b50bef88372d818fb28e78f3c9f700be508319cf04c8358878032040000014ac632ee0088abc54d9927c9a11441c6aea1070f4222f6060ed101fcc29f3c0c1a61d262acbb6c5651248b940d6fd2dd37068b28f4af10acf6a987f4083c60d6c1114658b1711403d21a2a111ce7880af893b0c00000063d9b132c6449bafbfa833444830f2400000a2802047ce3b73acf3df8938e319ff28ee3bc35b0a27fa521b798527202d5fe33eb32a5e2911884565cd3cc8110f7890f39279788afbee000004c363da4f2d3f6fa0d8788ce60dd5de6a34ed7cbf84f92e8443626faa00635441cb18295e2040a57ac5e3d97ca49da3270902c53783d63029170a5b431175d3b6ef819370204ed1d8f534db8e7c5120099c07ae01c59a46f3060000005c604262a80799e21e9e060cc47dea44635106d8e4eafacd1a84e24940000067c5600000054d82361fb2f219087b721c7e01c0c200000023ae4abccc1208447337165bac1eb7126fa87a35291c938565ce4cdae78564c5869429ed2000001215f890b3812b5e27c6f1107b06e2e443ddf114a30267a0000010b952f2a8e10ad0989aac361fd1f6e609d0692a234d94b621eb0094f184afcda195a33e9c000001eca9000000488bc471a9ba26ac0000001a9e377e0a353ec183a0844a22cd62888bdd7bf4a587d0))))
else
(if j < 117 then
(if j < 113 then
(if j < 111 then
0x174d0ceb0c7717c0cfe600000031ec474f663a0c426b48076384679da2aabd11462469b34ae77e0d0ff0e0f800f3cd23b245703c1d9790aca740000065e9210f4c8520a074992988d08cc7382861056f7e0cfa91136a0cb2d44dc08221b69d0cc8cfbe0873de204870000006b7244451a21edb6c566036e6c36150997ac1d278299bf9e5d44228c3490e994714c04dc73a7f1891600e921c43d3aeb8910845e892be04154b08dc1471d19702f45139a03f8a000000526682d9a20c28d27fc10736405ef3e0c6e932a6c0000002713836e559fb7088872c80de642e932a3bcc12a420db2abedde061f104d2dc1bfda14a8a090cb0000000c57871eb75de68903b7c46d46111fb0207f85822ccf51a236d22a74180000026b9e0c2aa79ef5052660ca150149ad483c8b1b264445ba3f26b0000021e33c000002aa951014d309244b2148487f5325da1612b87399706d951d3ec946a1c67d380debe0646e88829c19f6231a910000008c6b0000000c68a639de8f9f142b2989ceac147d538bf6c5d4fe92ee42182983d75c54d529c465a006105de2428d1c289e988a4f9a66dde7d2c0cf952b6d9965a25efd3421e908bcfc83c7244132cfede64aab993ac38dac202808f5ba60044ac069d43004fb9e3da0516900000000a841867f0336a978914d2dfa111634ed2bcb5d23056c1431e8afa208183e042faa0b1d2a2eb401b3a33e4fd35e771366680713e639af04d4c80cb5041910efdb00d84385836081d42c92d300000383b652442e0efd233691080a500eb524e40506349ce9fa000000139ab2c1453b770d4983c3a7a20c8ef24776400000000004f512a18a8d0c52a504bc76e7c28a8ee63f42228fd00000112d6cf4923292b1383171b23423b5a8000001a0d0032aac54240f7eb30000004d7e139d5ef37d410f4208c741cb59c4d9f9
else
(if j < 112 then
0x40d4288928d5daecd41a700000035eae24fc025cc11e905c1e21da194e0f3c0064ed30c3b842b600c6cf16370108ff4293d91148d538cc087a8445f783e2bf966f5a84408a52e498dfb117c3874b58c4f86000000a14d887a9c1bb0ca99b4102c6ba46342414c79bde9f1df03b2d5b7f603499b061559962293c8f8418da023638f97e850935488b97c9eeb707b4db55b36ec40fd8508821d84d0a9ddf1069d3a11731075e6104908a6f7882b8e359f0198e701af7c36b28203be1e5dd04d6114eb3476d26fd5a74bca1822e341af36106e810f7b071d3c00000147c255fb04a2e4506f923e2b01015303b34c0c11a344dd298e885ae882b1f03adad1d1d39bbe7df878aa899e1115a9402a9c63f8436782174b8373b83b35c0b0961cee2a45bac76111295c046a52d1fabc28d87115dc117cc0000001d77000000881d84fc7741f33e2abba9cdc136e6e49e33c98f6d0df5e03bfa6351f4188bd20749835eb800000b95c212f69841fea8579c0000020d7d880204377e20d094715de088f9dbbd820000077a7103d470aed5e258ac0fffc8c910a4df4887ece710ddb49fa0689e42a6db73ff5babb218fffc210880c1ce87dba83cd74860d642ad59d02de29756391d40f5e101824840556221c64816ea1631000001250f3757428336fd98d9a0c1e8011ee1a98e43814800000250f001ef34000003c2460b1948ad2d435f7e3a08186440d096a93f5e848e153087f029efc0bd7aeb8b033fbe4e6e284839406d11651758cb3ed365543def4218de9ea50595f8ad83fd12c688e96983715eae69008045bebe7c1ad1063e3800000000001e9d844238d0a0c20306440b1e6404a743acb0ad21c67d82fffca368b808a3590039c0c1de062538373184419f0599806fe78547a44cf32cc58725ce00506f57cb5021ea6000004453bcc8f6299d49
else
0x88a6487774067d68088f42c69e837e50000009749812bc7b646fc2030e1adae7574f236a4d975d62c5950634a08869cf6b5e241d4920f5c05734509cab58e22cf673b0ed0daa309ce93290fc2b6b8043dbaeae91a254384e64ceb38e64f2901ce50e0ec679708e5cb43254a880a4c36220144cf41b5783df68463ec0f59a32b1008bf1658dc01e2a910f608506e02771f1a8c36045680f7c5a634af15bf0a4f483ee28749b6239cd0616e04d3dd379eb0a0c5089cb8423f8000000c99f4e2be088395b71e42b1bc6fefa85175627992ee6cd66f5b962a08513b6000000000000b209a9b2a1abea5bc5f03cff0000003abaf15945936cc000000a13f9655c9896b0c0c66aeb89e53454071e6000000220cf643e988aa381dd380c7e110f41035be075d6c388ae118528367a9214b71cebd19f48aa5ef43b6f221e9c0dfeb83d7781df2e218230a1c9c7072e169caad4bb0e0d54013281adcc314ab0dace03bf58b5d7b33ae21d3d191ee4985158fea9709cc580a66c405aa8c8b7000001fbd9a1c9d6a65ae5f24506fee8ee99a00000159580f376043de8e74bb10f4b86af1e8f7b03e6e9529d31f66ea6c192045951d942b3d3b80000000000000000e3e38f697a2208d272deb387c139d481498f11056035af4000000000088a44011244d41ea14aea132f488bfb8679ab26ec20705aa3ff9846d920e0c90ffed8703e80790e289c14f7fe03827045fae697a386156a3c57400001055d506be40a9af87274a220fc0000006abd0654440dff4362d6a30ae03d2c03f8f7220cf85263415dc82100c1f7b6a8db34441942bfc109a7f9eadb8479303b1d90000006ab9663b6e0677f1d272c1bb7c18d0614d901617b0377bc1e5fca4b9d1a26f06c25521b7e1d59a9acf5087b6d199400b8bc064cb856f80000003a4e48626624e6c8abbc63c091))
else
(if j < 115 then
(if j < 114 then
0x11067076f6229bdc0dbf49f2d98acf3063d22120df07dee207a6a4a1948c5788a2d3a456b016c301d28c069e9c9be2028b264f2e800000000000241228170a062d7032b34d427106deb1a16f4d5ad0e1f9a04ae2663e480000016555147ff01a5a162f5687dc83abed41887a960386f3cb356b11d7c237bf200000104c82290e70d514c0f92621ea36fad1880b8e229f40d09d6cbc61f90ca1c15e0e0911105583064c5ad080cb8d268058fe71085d5e0c184472ca800001bfd2823a84661cb310adde2792000004757494b64576ba622ff70a13d880b15719d4579827feca035ba126dd822ff86ab5688a2c4000001a44a00000013e6c8e3fa113ea1a0e2800001375cc256c75f27f0000010b87600000063cf977f840e960526db499c7c5d62066ff0bb0db0707680000249d72822d81146ac45318d0bdc1449d9ab7687a2f09bf92406de2b9dd124ede4a1e0000001e35584e74419f9c000001a35589078400000000001fc5680000117fba000004bf2b356b247c03f250eb8245106b7490457b46ae710f720000010abd713afa16f491b9be10c94842aba1425385c22a7bf463b9d00a8f1830fc9eb3c66b30520f7404138431b7c2b4ad455c383fb1d2e5d423ebd094c811efd0273c85ed32101628173c8565320cf9444e7f000001bfd22cc1a536762c9ba7c998a40d6b77576589f6114bf14202c607f72127bc813f889ceeb000000152485f1887814410f71088fb48313070bef090c495561ddb908558ed000002ee69dcaf1a221c4035e40000008ab0a22acf00000000e64a31be008af019cf8e2b141bf4e23ac70a2cb0133c800000a716b67475a8ccd80000022ab83111f93ff56687fa471c30dc66855e307ac1eeffe62b37487b3b47c57b0ba9d7d7ca02a6b8569c6406c0030f013a4ddc6b56e7ff1111eb832618b3b8807cb7
else
0x37d8af22c99adb124fc9486c439e2d17bf531d8b31106bac86e800000231aa000004cfada0cfb8221aea3078cd5a59187e00000005d6e0fbbd0445d6920cf026750fb2642232ed4fed068728fa3cd3b0fa61a38264fd2224b5a83d00d8860704aba8bed9d90e2d8bb2194d082ab00000033ee00d6d7b64778555e82069587af5888b4836b3a3a4d2000004f7699a4faa38fc61d2509a3360886de9f98e24d7f3c3f02029dc6ac5479e7b090b4939d770bdd5161048e0bc0209589008852ec0887afc323863a4c400000000000000012d6f45b0e382fa60185eb312e54f1278107894dbfa855999d674829b7c8cf240ff941d3d8080bd81af044e9a703e53800000c04a2243f33c3978a130c000003a0cb000004986bc673e81e024000003d23ac2d72e02dab99af886b68474f2e220d500000000000279560f1ab1106982465835b900c7c50000002569016f911b5de3a29c099258455e4000000eff4b697601c11e1b0911dc4903bf48021c2b8f9d616d3aa23c404def0e9da06cea8307ec831ec220981967f8d0e404554c2c12409cf7103ab0b53f927db00925a031e0819394df0d25caf3a08a944afc62aa8273859088259d65683889681cc40ec2bd338fa29eff0c9c4830a5e07d8a134f411f4980000076d86f7eaa638d40e1e780790a0c2f10d86a087b48673728aae31017e00000008d38173bd06e75800001fffc906be450fd1ccf3718f5605a8e5907fe9607e0687caa178f1015b800001421c603d8a09ba5835f5c05fec000008115d8d469dcedf41fd046e14d194ed593d5126194486cc8adf59b77ef036cd00000030e5814f060c6d70d9d29e3798087f2b52b0000004f92e4b87fe2229c3a8c08383fe279767cfd602b54bf6274f278f387c40d6fd844f3c1dfa62f8cd09c4286aaa01afba113c544ae4af92413abc663864)
else
(if j < 116 then
0x4081288bfc89690eaec8509a5e842008dbf2a00000017df0a4ac0b9412992701979a8000004b75a3ab840ddfa044e744b53e388ed09aea34b6b0509e6f65bf142638d17f1fb70e000001e39e15ead50d6bb38efb02e86835a240000024bb811554055b70b6fd63a5be00000080f94241b8eaec43ec464993f0867206f1100705d83e27cf4dd600000798c1800000293e010faa2175108653808b23268cf066f7b2f3681af42b14989f2434447c404d8a0c7f29adcbafbe5c631363a5c3077c4218a1408746e13a53ec66087a3400000cdba20ccff80000055572222a900000055be102148137823444c800000a29b00cd9a063c2afafb4aa278b02f009a558000002fde4ac6127246d8f9f8c1b988054be0e95f249bf075d10e83ee09d428883f4327d854a47138fb10a269217b8060fb4373f018a754b914210cb154f60102e4205e22f8ab860f0cc737a0312ac4d9800000088710183be3a7e28006386c3a462b461f1904146d80000026d1e4553002f699edf144affef57f44147a82b6fc06b530ac9b322ab1de9e835f686933c6d85a9bf238000001b0b11505187aea921bae31e174f162026ae00db1624e79255049999a5fabb03a7bb234d99373c5b331cff2ba115689bbea94ac7e000005c66099c858cef607c0c2060dea18ae26ad5e344bf448ab0e9f500f95a000004968f087a8112dac098b100000031a3436144d97c935cdc87d2542d7228d2f01d25aa01734000002cf8435ca580efc0000001aac91c47281c360bdf1e391c542007bdba4d079ac0c684000000000001b1323a4f939f4d08c28c5537a3b8972b95e80db94164945b6830196d286a524e126388c93568f124bb0383a91b3e8000000cfbfc355fe3200d00000088266797c88fdda000003ce77529e92406c9283590000000000023ca709a5e887a0442bde3a091
else
0x8bb74d0e7b84b5daa223d6facdaa6a1c7489e0a88307f660e970cef6a109ecd7a675cf7a68a91501395c9fb7b88faa80000021ed9282528000012e75426221a33fd8b7b48f1f0a614d138678880ab2535bd0c9bf09cf535f78da5baf3fa91842e580d7f00000030ca107cf60e237000000773cc3199b86d6a1b839edd8d4770f9866f784bb68148eb8add68032613ab48896c1132dc031ed824ccc90d97206658000001f5dc7523f216e60ea622631822605a6697b800002229748459993dee000000079d40c19d2751f0507e074932befd61104444526539dc00000024ac68177482c157055c726cdb88ca2c087ac1c189108d5aebad10cbc73ccc7000002a4a48441f0032e101ac7289c7cb15401b0e4139522a329e74d1a139cc8c6fa350fa400000425200a2cb80000221f2a8d4868f4fc8ad35c0000136dae000001a910054d0621ed09bdf9cba3d95146cc3c90000000853be229ce000000e083082b25e03581b18b4eeaf8117884159125a9306acaa3372c379b21e4c502758ae1ad8a869c051951dcb849b6fc4737023baa00000035fd492df8343c7200e41072fe907de0efaa00d7e887ba080372d41d69375527567136dcc000000d86021b79537b526dab97cce403be943d77853381063590ae3657197c489eb1effdb99e5608b16b67d41c7fda2bf2d369d8379924e75a38a255e09040d8b70e34e888b884439222dda2602585ca741d71480fb710f6da3364c0000021ef224ff58bd71462bd4120981d2fc272af419f0cf41fb6f7d68000000000002ae13f0371087f047d5032c9e0000003236891b7c000004e4cf8000028b956906df0c3328366dc361e40fef249625030eb000000000000656db3734cbbeb61b0dd0e0651cef4c00fecb8ed1836ca4ba7780d444a4a404404f896e803fb8400000110f91d466019f5e17784)))
else
(if j < 120 then
(if j < 118 then
0x3b9294e675c538a3000000cfb28000009c4fc19cf48dcf705016a10fb507fc78883742691a067d02f0c8046df1284acd4de7247e800d72c3a5eac0dc00d85c903d0845f0c5503d35af0800000df9ac026b7166ec84e66c9ad3a2955e65e5a834fdd70d810b4c034f9f000000479d85b79a0d6ed4fce287f1aa09ce45df548b9824183b225888a13f7050b448134a349eb06fd8940290bcbe4a5cbc060c93d33a8183cc3cbce1a37081f366583821aded0817807e998a67bf188e48ef7988a37288540cdf94986dd91a624000000cfe572a704f2f8e76bae491ed11b618fa9995e2c106f8779e6f01e6c83ebca1b5a266ef386f32e1851a4f2d100000230bcdab53c21e981195ea30ef800000289eb0d5454636a0000000000010f7f0e83c4bf29c919c70e0ce911f7c93523144d5654c2037f49ffd6415b9f37cc98c5a5418df9128934a64906b78c361662ee36009ad9d3f204bbc73e4de15368336f4c0000022de9026589552a836168076b7120c40424484c152ae69f027df34b6707f552000004cd7f4ef688000000a4ec33c0d4993b819ff4fd381125c88a7b0a7c96a000008eb54133ab9ab536000005351e13c84c65d2c00000065702fba788e31c206fe7194283be5039be5002c25cefb8ec674443d23a0ae9b14400000123bb10c9f52a2da01621d539ce2a9bb1d3e90e9322121680eff8990c088fb686874a0c2f11393a124a104774081a1f54342088b8042140000000000007d26a3d3020000011f633b8751dc30a32f9324fb58d36844453c58284077d99f65cc9b5502f7b010f59c76720dfb5ca6299090c914fb48357f20adbb49c7909075dcaf7416cdd0000007929405f9e4a38a86ce2ca5bfe02bfe06de000000088b2dc0ffc062f70937ebfebf851706ccec304c578ab6f843d761f66c10f6e8892603a5fc40b92
else
(if j < 119 then
0x4a1c33a66a8eade428be18d57ea5f4510019e7c3ea067ed8f0a21249ce226ec7cdf2175bb00000041f290eae1018b6c28ac083ee1263d68d0eb813d7c000000685190d27177336034c40d853b55e7d30cb852c9c3c64ed09fd121bb3135ab5f7420193684bd38062ad266608a9b3116e14423b1747d5246420000001aaf61105c0000012f9b2223c00385912c8e461e7005ce4a45670a12546de1407ab406bc7000000455b62a69d110ea1dab35741782c6ea9f260be0fd1659dcf64d81c6fa13c564361142a6a26704742e6b800000257cb058c6c9bad818fba343fa26bda3b77e443d820c6a555b4903dea0441162ba76676cb8263b8679f27d0cb92868a0c9700448a343d30000047ceddf1dae0000028bd1cb4b440000021e874fbe84f8668000002ebeb0de618aab88455aa83d7b0d84e0aab20441be02f9814b45238fdd6f5ce108bd1107b08da8df65640f1bf013660bdf1d215a33a1893f7d921e91d522369dfe668de94f3ede63f6e452aa1a1e692b6b1cd5d60cfc107d7b8ce785765f6856ff607fa8e231628924f71f74a27a08db20675c6d4df9438848000007717ac17a07754b80000000000dfdc2000000e9609c73543a4d6066d49e3f241833809c931b39a0887ae0494a3b0d2111658762e96e9491f4fd390c6cd464851b18ca6a00ecc48d0e34daba60e0e80f2ea84e6a81af271229a0a45a1b8f6455de60d78143945087b8043d1c5846a1c45400000000000058961aaa3aeba2130af221ea1059e200dae62372ec48eb076539412f4000000c1e875755835af0451f00d48f13775c0db686ebf339ffe955d60563d0709f8222c218f4dbaaeb043d7b12ee40de74922f81863fa1f8c019cc8054e5867d7e0dffa0000032eb386758e000007895a030b0511e8e1aa122a5f008c68c7336a3f8ff11460a43609133fa1f3c9
else
0x6bcb8d0ff613d54000001487e0dd62c00000230ff463e8000000000009cebe387c70000028b9482228f3e27b8cba2020fba0d8a5118d500000039d0a345bc399db0000013ce74589960add92a97301955008ede1fd763363a0361e445a84111d888c7504651c6fc9585a570bd77c2f0f832d8b0004c019eba7ad4c0eff711cd587065c1833ee70ee2260788be3816b9a3a48347aae08ab8438130f2dcd0f6ab0000005d90c32ce04315c9b4adc781540a5be000003cced04435a202ab8d273800000000003faf16ff4d246a9245d2f1ec9f7bb448e86f5094582cefc0000031ca5000000202e31435980000015f8e23eb188ac6890acc4efb0bdc89110cecf8a6461a7c3b6994e76208da959b9147287931342cf9224d9d2828f8d19f6404d3b043dbe0cfc07c2da12e154323c40000011f43933b8415dd8c048671f508bce1d765c03dd6b460700000017abec4128993274326e4c4552c21e8e91cc600000043d08095d0618f0832785d71b84084408159080b3843d34420bf147dc4572e81c1dec63e2118de04d745db9a00efb412bdb8cf4427c9dc390fc9c5c4b7ebe800000226e706fd0010f1092f2a0cdb0a2bc807ff20253f62a6d669ce38acb202e318000000b13695c230c19cc156c31426097207d43848431c30000003befc18334d8f870f30600f630201b094b3000000051bc043dba697e613a2b88a2b01ed120deba0000025826c2736e0d6e9145cbc48e39525d01add97a6e2a09ddc000008e27e7c04a0892f64af6280b0b10f7d8f2bcd23b52ab4af06c7603c7c48d3340385f089f34283e24e1608561e1b776b7260944192437e712be708aac80b96d401cd069dea6a19054d244d6e401e763377a8445800000007ae69be5c49f9ea3bbba55709031e287dbfe1b09d91ccdce3644f1f76055b61324a3b87b920fa04ba20))
else
(if j < 122 then
(if j < 121 then
0x5af7c49ff634dc5000000b2cdc3711611ff15dbfe2587703c3e4cd6b3117ed312f80361cc9d5b04e74cbef3e019f952b4df09bcbbcf78836186343c601ac4009a3222d873e4b85431680000036185239a77e2738000001c5aa57dfa82d659a97ac1bf6821e8f396a4089ba8771dd116f4000000e039a22d30569de72c6ac51b4964bf9146ba1c57101569e49d2a1b0c9325f0d207e470baa0d6a101ab5888a854104a1c7887df45029a259d91460f710000006b6a4cfc92314e3000002ec2d8555b8d5aea9f2741b7ef8741600abca91bfa870c24000000c6ff110fc0002927ed44111c2120c40336bc09976228852187e2ed7424dfc8220dd0000011ac9c5c5ba21eff08157b81689c1d5b0e2ab596f206c3a81514a0fbf110f6c00216d202283edfa0704581bec00df9400000000000e9f1c4417f222841d3c6052fec44192000000000046d21c355571f1dc077f7b6af2007f280c1c5367564357c0405800c69100000018aae7dbbe0a1ec017dd8d0ee2523d0be8b63cdd9a79f28467a40ce8e10f5b026a187730a70ac5647f1cddf0036110228a530f6ea4f230223b200000606f480000076d225999501ed9251b08000000c7ef4a87796002c35738419ab000001c80c630d4a0c1c8318448cfa884530c91d9256b750177a1433808ee9e1125e2a1eb018d705379403e378526a400000564491b1e800000045f1c1f5940bb9f8ce748000006d2b53784f0437665e7130d59111618088ae2509c2c0ea700000087bd8a17fa218f5207473ffffc000002d7b7060e0273ab16ed861e0b7757540be381169ecf81bf00000233c0863d1e0000072cc9b99ab444160223d9157dbcdca18473fe202fc41b7e880bcc2819213492117c34fb3b468c5aea0950000017ff942934cc79a01a667800000445082208406ac5887b24203b4463a8
else
0x56acf3b9a38a7124fffa25c0fc0be3495056c202c41d05c0ce7582d7e6f349404d56800000405de0000010f694d3634441f62da506577783cb18129a00cec6060cb033fd8df11c14ac0166ea887aa654316191c00b059873e0499f6a2a4c91516a8116d523b860287b387f4817b89857188f0781f12ace27b043d921bc9f1d8ee2dab8019b0c062c91d3e3cd1f965ff8e3b6cb036ce818894509180c3e3110cc8d129d369d2a94634674e901664000007b4d002acc088ad53abe43abcf3674e930bf41353af68fc07f620d5950135e526fe58cedc11264c5575c46395000001f1fe476d9223e930108e837f1418334dd3a470fc6192cc1ca72c000004d75e15f9568954306de81d8418e9e501439a308fb15364800000ab3163b7f41116e01afa20db54bb58100000185b401adca2d18a425f588c7d055d26538750dae28062d55cdd62aaae080c88a12b21918e38388029190baefe4bb8a854c65c3cb83a6700b7929d5ee00000087b28143564e4cf11dcc9ad7cc405623abf7148899ea6581bdaa326c613355a4a7e1a65d80f9ee9f178043ecc4410c07ad4000000373890d5fc6340715365147880405b81b5c6174398d0ebcc3fe442dc348c0d8e22d8f3908c45c08897e0337f115f33356b28524419ce650c591183b30e05382cb28e88f456d3237b5b9b7b6c3612e118921a1fb84c35c6cd7424be21cbf2000000375de7102e077f28000003178c56d9a0d85d8adbc81e5d400000068648a12e054d80dc49d46d640883a400000218e33142b035a420db7102bd01c1e88882315edee03da8773ee887ab84c5aa0e0cb0d5bc4a5214c9dbb2b9ee60f71b7f6f076f14124ff03052989aec000000000077fe88e835a2b1ce0559718a9188cb68405061c0ee73fdb19d2757e5b4140ab10874872e3c43d6259ad819ce1d217e871118df582)
else
(if j < 123 then
0x9f27a8d0f781100e3a4c9110761640143d3d22b4f01155b0ce62e211f600000060d52e1bed5dba8a27e50dbc10e5384cf5fe49ed71d25e813cb0421f2075f9067c38883e57dd5064a19159d446a3fc75b460d0b71d3e2958f244433f054fb05f480907b49e1c80c2a4321e108897c4635c03c6e2e4e208138c11df00f7df1d5d90000000000145bfb1fd4d0a27e0000000c6bd5d75807fe0e7c9980b8b62f595887bcc1afd4d29b24477b000001dc3909a56b75bda279fa99bf8a000005dcf7166afc257a01afc6204c6445261213460000000000000000485ae41fdd4e4af1f113c2df880deae07dce80000054d8c0000062dcc880b6091b280e918117f18e82e88a5205eddf473d8150f6db2352226d338e111b6ec4383ae3a7830634a3276a04050a9cfdd00000439a0c70750d23c4879f63b72861a5e22d8c42e181000001bebce31c35117d60a07128e9460000022ad28737880e146000009536c246f7d36c080c1e309a4086c24600fd6215f486acbcade8c00000d54de789ce448310bc9a6c508c0d85e8343703712c000000d6ed034541d05d40a1ff00000000000541240c79c2817301697613dd85413614be21d5ad002ea61a7ce0077047ee5c1c1da42e9f88a6e0756e54a7ea566ed821773d034562d1c1aaaa7d7fd4452c66ad880dfc917ace8be368028e078f535f9fdb0dff80000028d2e76dc8bcf780183e2000000d6d704e768f98d40d0aa02ac40cd7306a126000005f17d88c3d41bfc03dfa5070fb4063000000077fce06bc3888fd800000b10ab064df030b514a44649ae2013702e664845f78343881adcc80000000001018f368c708d2606229bef37e30000008a3d883353327f97a67883068821db62208e0ee643cf3441b7783419302de551de687499695fe711b9f990c5413567023dc067fd8a770c000002b38e
else
0x119f220eff1130da28303487a860000011054a38f94451021d4da000003bfb70000006bad0808769666b845f5a4f05e063dc8000024c90844d8728e5dbae2a18ff2e22f2a022c943576c000008b9e90c8d8a4d6ec15bc40c2f201fcd887b5523bce537ee0bc5294864019f4928abb11f6d2da68859d3aa5436)))))

set_option maxRecDepth 100000 in
private def slotBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := (if j < 64 then (if j < 32 then slotBook328Slab0 j else slotBook328Slab1 j) else (if j < 96 then slotBook328Slab2 j else slotBook328Slab3 j))
  (w >>> (21*(i % 256))) &&& 2097151

set_option maxRecDepth 100000 in
private def recBook328Slab0 (j : Nat) : Nat :=
(if j < 6 then
(if j < 3 then
(if j < 1 then
0x6cc01ed198029db30053a5d00a748a014e598029ca3800c56700278cc004f158009d330013a5600272cc004e558009c93800c000000968e002a0000018b6024b81504a6028094c580125e2b800c35a00188da08ced5c0061af8223b56001868e00311b4101daa0203a570018ad406cf59c0d9e3301b3b6a03676cc06ce9500e593301b385d03670ae06ce91c00611b800c157001828e00304dc006093800c46f02578da04af19c095e2a812bb4702b66a804ae9bc095d36812ba6702578c804cc91c095c2b800c06402364ce040e974081d2281038470018ace03ce0dc0062b38093b4801276ac032cd500659a00093c6601764ac024e59c049e2a809b14601360cc024e09c0061ad0073b5600e748e01ce07400611d006381700186b4004ed58009d23801392b002748800ac55c01582b0013935003608c004e05400600000048370015000000c0000019a3800a80000066ae003055c00609b800c0000009000000c8dc00551a808a137001548c01c8518039093800aa3500b426a01680dc005523003a125007408c00e809c0054a30012136002408c00480d800900b800a8000006000000d15800602a015383602a702c054ed7c0060b6013b96002776ae0031590091c2a0123a5f00188ac042f150085d2b800c04d01f746e003015006dc1b00db81601b72be0030db0061db000c3957001826e00300f4055c93800c56401270a8024e17c00622b006bc5400d704801cc95c035c2b800c24d00b706e00305c0025a338023b5800478e000cc59c011ca380238270018474004e05c00600000048270015000000c05c00540000031270015000000c09c005400000334f001649e002c8dc0058a7800b127001609e002c0dc00580b800b0000007078074e0d00e9e2f800c45700186be00305b00d5cb001abb57001868e00301700c5c2a018ba5f00184ae00305c00b99b3816ba47001846e003057c0061b60133b6002676e004ec91c099cab800c14700184ae046e4dc006093800c05f00180b6003015c00602e00b3854016709802ce110059c1e00b3834016705802ce090059c29800c04b00184b8020e940041d30008b137010708e00300b0035c12006b83b001806e00300ac0061ac0033b5000676c000ec51c019c13800c04c0037088006e06c00600b800c000000926e002a000001893800a800000646e002a00000189b800a8000006
else
(if j < 2 then
0x8e806f09dc07a73d018c57a03188ec0630d900c9d3b018c25501e94c805f08dc07a52a816c17a01e98c805705d807a52a814c13a01e98aa04d055409a09b00f4c64022868a045051408a03b00f484601e92a803f009807a433001557a0039aee00735d800e6b3801cc7a00398ec00731a800e633001cb7600396cc0072d5800e6ba008c27700394ce00728d400e4bd001c97600392d4007259800e532004c07600394a800f019800e42b001c934004804c007211800a80b800d800000c06c0a8e058151e2f800c26d05170da0a2f15c0061a3827bb560018aca096e15812dc0b025ba5f00188da086f17410de2b821bc55043768a08acd5810dc36821ba570018ade06cf5a80d9c3801fb56703678cc06ced580f19b301b3b5603964ac072c9980d9c2e81b3857036748e00315940c1db28183b5703070ac060e0d80c1c2f800c46d02478ba048f15c091e2a8123b4502a66ac048e9b4091d2e8123b5402664ae048e954091c2b800c56f0147ad4028e9c0081ab380a3c6601476ac03acd98051d3780a3a5d01474ae028ed9806192280a3b5601564ac02ac198051c23800c56f00278cc004edbc009db50013d7000e66ce004ed68009dab8013b5600a64cc004ed9802192b0013b5600562ac00ac198009db3001b056002704e0030000002536024b82504a6048094c980125e2b800c35a00188da08ced5c0061af8223b56001868e003095c006123800c23700188da07aed500f5cab800c56a0337ace066f1980cddb5019bb6603374a806cc5980cdc2e819b857033728e00304dc006093800c46f02578da04af19c095e2a812bb4702b66a804ae5bc095cb6812b96702578c804cc51c095c2b800c06402362ce040e574081ca281038470018ace03ce0dc0061ad00d3b5601a748e034e0b400609e80c382700186b401ced58039ca3807392f00e7488022c15c04582b007383500f608c01ce0940062b38013b670027490004e95802192a004324000278cc00cc558009e2a801b04600360cc004e05c00600000049370015000000cd980a9d378153a6d02a72e005ec99c0a9cb7815396d02a74e0056c59c0a9e2b800c35d02876ac0031168099da3000c46d02076cc046d154081da3010396d02074ae00315a8065db300eb46601976cc032e998065cae80cba4700188da024ed98059a2a8093b4601274da024e954049cab800c56a00a7
else
0x70c26729f04ce53c099ca7613484e02672d9c00ab430924d8a1249af424935d84926430924d7412c870c2492dd849252e0924a5812494ec24d099849a128092495c124968e0054d9c47a5a388f486611e908c23d20d847a53d001538d11b931823729dc00aabe88a4d6511496fa22929f445251b88a497e11494ec00555e84366bb086cb4710d90ec21b211843641b086ca6a002a6fa217299c00ab3d0804b701088cec20135d840263d0804c7610096da2012d1c4025368804a3710094cc00559dc3e663b87ccc670f990ec1f321983e642307cca5a002a4ae00555e83d26b507a4b5d0f494ac00555e83b66bb076cb670ed90ec1db21983b641b076ca4a002a6ba1d7291c00aabd06ccd770d99aec1b3359c36663d06ccd700e488ec1b331a836663306ccc5b0d996ec1b32d983666ba06ec2770d994ce1b3293c36652686cca46002acee1a335d834663b868cc670d190ec1a32198346423068ca3a002a8d019f28dc00a9b8066c5760c096f41812dd83025b50604b660c096b2181219831a1ac0604b4a0c0968c181319030a13b0604a660c0946c00555f42ae6b2855cc570ab96ca1572d1c2ae53e855cd740b884ae1572dd02da11b855c95a0ab98c816705582ae49d055ca640b0826c15735942b61b2856c12a0ab924c15725d800ab3d04a4b700a88cec12924d0299cb8052c57609498f412931dc25263b04a49600a086aa1292d1c25263a04ec27709494da12928dc2524bd04a4c6409882ec12924e825252a04ac13609492cc00555e82466b5048c956002aaec10b2de82165bb042cb6a08596cc10b319022a13b042ca66085948c10b25e82164bb042c936002aafe08535f410a6bb8214d6e0808aca08531fc10a63b8214d7d07c88ca08531bc1d622f83ac45707586de0eb05b81d60b103ac46404298ae08535d01ca1bf8214b7d04298c80df0ddc10a5a38214d7406c84fe08531901aa13b8214d7d06884ca08535d019223a032427406484ae08535d018613a030c23704298c80bf056810a63202e436405c82ac085319016a09d0214c7705488ca0a911901520bb82a4165054826c0853594146232028c12a04298c809d059013a0930214c6404c80fc085319011e1b2823c36404782ca08f015810a4230214c6404382c8087009810a43b001567a01e9cec03d35d807a63d00f4c7701e98ec03d315407a5b680f4b4701e9))
else
(if j < 4 then
0x8ce41335d88da22b904cc6722186de45cedb48b9db3917396f22e72da45ce59c8b9e2a910c46522b78aa456ed9c88622b914bb5522188c844eed1c8862329113c5522276ca444ed54889cb3910c36620998be4150dbc865db690cbb6721972de432e5b4865cb390cbc5720a8aca42ce158859daf905445721476ae4151198849da3905456520f70ac41ee57c82a22b905b93420c66ae416e55c82a1b2104cb5016ba8e040f15d87f663d0fecc761fd98d43fb31987f662c8fec86620088b03fb2dd87f64a68fecb4616baafa3e931907d263a0fcc3571f496c83ef09587d26320fac2361f494ec2d759e876a73b0ed49801f076ee3db0e007b9cbb8f6c5761da98ec3b535d07aa1bb8ed4b641e884ec3b52d9c795cb38f2bc661dc84ae3c4c55c7899aa0f0ba661dc84ae3bcc55c7799ab0eeba641dc84803b528d876a5330b5d68d1c899203af1a1c7224c70eac6751c8991a391321c72263a8e44b8c1c896b0391319c735db38e6bb641cc86a039135d07261ba8e4c2661c892ee2d75e286de7430dbcd861b798fa36f31946de5be0dbcb581b79aec37711906f9dbb0ddc4661bc76e83770d406de63a0dcc2861b7930c36f259c5aebc38cb4e861969b1432d361c65a6bd0cb4d771969cea35f121865a63b0cb4b6819692a8356cdd869dd320d432541a862ec34eedd86961ba0d2c36019696b832d3a346862ba0d0c2861969f143391a186722c30ce438619c84ec32d39d466213a0ccb966198830c32d25d865a4a38b5d37f18e8100326eddc63a0bb0c7407f18e870031ee1dc63a2b28b64c6416c9ae831511d062a1ab8b64c6418786c830f09585b26320c2c23616c98c830705f85b26368bf424717e828c2fd04985fa0b20b64d701798ac82f311905e61b20bcc15616c9ae82eb11d05d60ba0bac05716c9cea2db15d05b60c70b6c57d17072e82db1a005b9cb30b6c03716c90ec2d7409c006d460b2ca8816594882cd08d059a1400b2ce77002aaf40055a3457a6468af4a8c15e94cc2bf0a0057a6bb801557f15898fe2b129f856252b0acc2721589aec005559c00a9460a94a8815295002a5263054a63b801527c14d94f029b29c05364be0a6cc67002ad1428d39e851a5360a34a7614884c028d25b051a62b801568d13e9ae827d32344fa54609f4a8813e94cc27f0a004fa5bb801578a1339d0c26736184ce63e899cc741388
else
(if j < 5 then
0x8cc66f1200cce63a19ac366333931a66729dc9dabc5192ce863259b0c64b3228c9663e192cc7832598ec65711c0c966ba194c38632598e864f0a18c964be992ca67276acee63b35d8c766b2990c47631d90ec63b2198c7641318eca4d276aad0637291c9daabb1884c7a31098ec62131a8c426331884b7a31096ec6213190c4a13b1884a66310946a4ed5230c1e644183cc8030798b460f2e30c1e5ba183cc74308849a60f25dc9daa3e17f4c782fe98e05fd3168bfa5be17f4b5030086c85fd2934bfa4b393b568a2f49cf45e931d8bd263617a4c762f888c05e92e18bd25bb17a4b6c2f492ae4ed55e8bae6bb175cc762eb98cc5d72d9cbae43b175c8662eb906c5d725349da92e974c947276ad0c5a53628b4a6c31694d7a2d29aec5a53218b4a63b1694b8a2d296f45a52dd8b4a5ae1694b582d296ec5b50d98b6a1a81694b482d29ae85af0a18b4a53b1694a442d296e85a70618b4a49393b557f2989afa53135dca626b7166c56529898fe53131dca626be964c46529898de585117cb0a22b961436e2c286c458501bcb0a23214c4c5729898c857f0d68a6263215e43642bc86ac5313190aea13f14c4c642b686ca56d0d90ada12b14c4a462989ae856705fca62632158c1772989afa55d0958aba0b294c4d742aa88e855505d0aaa0ab94c4d652a788c854f04f4a6263215241642a4824a53135d0a8a03f94c487d29898c853f01dca6242394c4c6429c807a53135d0a660ba14cc01729890ec4ed59e89de73b13bcd7627798f44ef31dc9de63b13bcc5527796f44ef3190a3a1bb13bcc6428b868a51709d89de52313bcc7428882ee4ef39e8a022bd140447628086f450109d8a021b2140b97628082aa4ef25509fa09293bc86d277908e4ef29549ea01e93bc964278802e4ef21989da81b800dc8f26a991a4d526409ca2439354b8c26a970c4d52a189aa4c7935498d26a99204d7061c9aa73b8b5d57616bad1a4c1264099a3439304c8e2648cea4c12e309824c6930498726098ee2d75e2896674312ccd86259990c4b32df09664be92ccc6716baafa4a131f894263e1284c6425096fa4a1319094a13f128497d25096ec2d759e891673b122cd762459ae049711d8916637122c86624888d848b2db49164b6922cb6616baace481319c90262b920486624096b02d751fc8e623e91cc47723982fe47305f48e60bb91cc5672099
else
0xaf486535d90ca5a3a194876432908c86520d90ca4b69e6d23743092ce79b5a190a66c5214cd784299aec85715c10a65aea14c9473cdaf2084f161d0726bea0e4d6541c98f883931e107263820e4f9041f8b0883f0a1d07253ea0e4a6541c926e79b5e2901e7c3a03ce864079b0c80f31f501e63ba03cb8a40796f880f2de101e5bb208c370407969480f2d1901e63a206c2864079474817099101e523203cd74408830c80f249cf36a3f1e74b6f3fb86ce7f709bcfee1339fdc04440072de7f705b4fee0b39fdc06f3fb80ce7f71190f3a4139fcc3653ce98dc7eb1188fd61af1fac3643ce968a79d35d0fc623a1f8c27f3ce9ae87df09f4f3a6b21f644643ec84ba79d35d0faa11b9e748273e882ca79d3590f962321f2c15d3ce9ac87c30d90f860b21f0c1453ce9ae87bb11d0f760ba1eec1273ce9ae87b511d0f6a03f9e74d743d880fa79d3590f562321eac05d3ce9ae87a700dcf3a6ba1e7c4743cf82e879f005cf3a43b1e6d057001bb0c7853218f0a5c79e14b8d3c2932078f0e1cf0a4c79e1498d3c29720787061cf0a73b9c9557d3bd96fa77b29f0ef64be9decd76392acf47732db4ee64b69dccd66392aafa76f31d8e4aa331c9568d3b19cea7633198ec64c69d8cb77392af147553a18eaa6c31d54c863aa970c75525f4eaa5b39c9568d3a49cea7493198e925c69d24b753a492ee7255e28e727431ce4d8639c990c7392df4e725b29ce498639c92ce7255e1ce4e6c31c9cd76393990e7272e18e4e5bb1c9c98639392ec72724dce4a823800dc8c38c99107192910e360a21c6c48038c9cee4ed55e89dab469c2cc8c38598cc70f1200e164c69c2cd77276aafe6ff31f8dfe62b1c0c47237f92fe6ff35d89daab393b506637a906c6f52098dea63d13b538c377951a6ef31dc9daabe9b8cd6537196fc6e329f4dc64be9b8cc76276aaf46d735d8dae43b1b5c83636b904c6d731a89da93e9b4cc67276acf46c125c0d9a33b1b04d7636098f46c131d8d825369b0496d36098cc4ed59dcd6e43b1adc86635b904c6b731689daa2b93b557a3569ad46ad2574d5a62b13b557d34e9aca69d315cd3a5ad1a74c6435086ac69d29f4d3a5bb13b567a34092e069719d8d0249a1a4bb703488aec68131e8d0263b9a04c7634096f46813190d0a1bb1a04a6d34096cc4ed55e8cf66b519ecb56276ad1a66735d0cce646199cc883339)))
else
(if j < 9 then
(if j < 7 then
0x2a8a6ef5814ca0c029abb775328700a66e5dd4ca2ba297cc7452f94e8a5f295d2b2b3aa914d745229918a45322148a633294c48052298d4a4535f54961ad292c27452296e8a47053548a51ba5656855179ceaa2f359547a2ba28bcd7451c890aa2f31d146a03328bcd74518808ca2f25fd2b2b3aa894866512908ca2520d944a4bea56546450c9ae8a1f0e354326ba286c37d50c92ee9595a313ba7442774e804ee92fca0f15d13ba742282c48f4ee991a9dd35d140a243a774c754ee90fc9ff11d13ba73a27e45744fc86da9dd31d53e623a27cc3554ee9d089ed16113da147a774d844f4851a9dd35d13ca143a774b554ef84fc9df09d53ba4aba5656754e89b109d136013a26b52744b5d4e8928e9595a3d2ea746a5d4e874ba9cea975363d2ea6c6a5d4d874ba9d1a9bf15d52ea6bfa6d456f4da8ace9b501f936a2ba25d4d674ba991897532212ea64025d4d744d488d497535d134223aa6844744d086cc9753a1133a147a5d4e844cc851a9752a1d2ea746a63c3664c784fc98f09d52ea7c826146844c28b089850a1130a133a5d4d744bb88ea97711d12ee12a25dc2544bc72ea97705992ea49ba5656754ad9ae895b2e312b65c4256cb664b4870095b2da92b65a5256cd7d4ae84b495d08e92ba13a256c9274aca0ce00361192a241b25448264a89cf479b5631296446252ce773cdaafc93f2df527e53ea4fc97d49f90fc93f39d8f36a3fa49cc7749396fe9272ddd24e42a24cc27f49394fa92729dd24e4bfa49c97749390fc92735d8f36a3d1e6d68c48f9d0091f31dcf36abf245c93748c8ae491731d8f3683b243c846487904c90f31b4f36a339e6d4553cdad188fb3a211f674023ecb7e4808ae88fb31b51f662aa3ecb773cdacec8ed35e91da6bb23b4876476906c8ed20991da5b69e6d3673cdad0c8dd36291ba6bc2374d764708ae08dd25751ba5a39e6d68c4699d108d33a011a663a234ca773cdacec8c335d918673a232c47746190ec8c32119186413230ca6d3cda8f88bf299cf36b3d22b4e764569af48ad35d915a63b22b4b7745696c88af09d915a52a9e6d78a4459f0e88b3a191166c3222cc8a44598f888b31e111663b226c4704459ae88970e1911663a224c28644594c888b2d9111a0a6a22ca373cdad188753a210ea74021d497e4408ae887531b50ea62aa1d4e7443c84da87529550ea4bb9e6d6764329
else
(if j < 8 then
0x8cc6d20598da5bd2d7d3775afaafac632df58c643eb18cb765afaaf4c5735d98ae43b315c84662b902cc572da96be9b3ad7d67a62096e0c4f19d98826bb3104c7a62098ecc412db58825a3b10486d62096ccb5f59dd86663bb0ccc6761990ecc33219986642330ccb5a5afa6aeb5f55e98526b530a4b5d61496acb5f55e983a6bb307487660e90ccc1d205983a5a52d7d3475afaaf4c0735d980e6b3b01cc7a60398ecc0731a980e633301cb76603909ac072d196beabeaf9cc655f394dcbff11917ce62baf9cb7d5f3968ebe731917ea12d2f9cb645f884acbe731917da11d2f9cc645f4846cbe729d96beb3d2f34e765e69aecbcd31e979a63b2f34c555e696dabcd2d1d79a53d2f34a765e69474bcd28d979a5332d7d57a5d89aecbb1359d76263d2ec4c765d898d4bb131997625bb2ec4b565d894f4bb129d97625352ec4a665d8948cb5f559571a62bae34b655c6968eb8d296971a6322e8c2565c69474b8d299173a11b2e34c645cc82acb8d299172a09b2e34e755c786d4b8f01f571a4bb2d7d57a5c192ecb83259970649b2e0c9565afaceeb6535d96ca63bad94c675b29afab7511916ea1bb2d94b665b29acab6d0d956da13b2d948765b290ccb6521196ca41ead7d4685b0906eb5f449c006ebfa5650465aa906cb5520996aa6bea56538f5a4971ab49263d6924c6ad2488c5a49aee95955b965663facacc7759596feb2b260167a1bbacac85459c84feb2b29f565653bacac97f5959700b2f05dd65643f2cacd654aca8fe95941996424232c8482659098fa9594a3163a63ba56557d58c98ca95951bd60262fac04b7f58486fab0905fd6120beac2407c58488aeb012dbd6024b7ac0486e58098c8959515d2b2b42abb4e755769acaaf715d15da63a2bcc0665769ae8aef00995da5bfa56567557190ccae320d95c64132b8cb7d4aca8c8adb35d15ba0c6ab6cb774acad18ab93a215727402ae4b7e5688ae8ab93a1159a247aae4c8d55c9ae8ac7121d57263aaae487e56088e8ab939d15762ba2aec16d55c96ae95959d555a6c42ab4d805569ad4aad257555a5a3a5655745519d08aa5161154a233aa8ca7f4acaae8a95361153a233aa5486654a908ca95209952a53ea56548c54598c8a8b35d151a1abaa2ca774acaafaa812d5d5025abaa0c26e54094ca9595a314be744297cb6453b82c8a771a014be73a297cb545377
else
0x8d8e6531d9cda2303994b86732950ce6529d9cca51bb97d67773090bae5f451c006e463944c887289488e530115ca6022394c4807289ceecab55e9956b46b90cc8c7219900e432a35c86446b90cd77655a06ce3d0059c7a2bfb89cd7771398fce2731c9c4e53fb89cd8d71884eee2721fdc4e6c6b8a428071480eee2735d9956bc33884d867109acecab4199c3241b386481670c98f4cab51dd956abeb834d6570694fae0d21f5c1a63b32ad57a6ff9aeedff35d9bfe43b37fc8366ff902cdff31a9956a33b2ad67a6f79aecdef31e9bde63b37bca6d6f790dadef319995683b37a48666f498b4cab515d956abd3784d6a6f098accab55f5baa6b2b754b5a6ea98c8dd70d59baa5bb32ad67a6df9cecdbf35d9b7e63d36fcc776df94eedc711d9b7e5bd36fcc646e086ecdbf2d99956b46b64ce876c99b1ad93361db266bab64cd7f6d68acedad09f9b5a2ba364cd676c99918d933221b26640364cd746d088d4d9331d5b3623a366c3666c99d08d970235b26443b64ca77655af14d5d3e1daba7c33574e866ae9b14d5d3e41b0a2c3b574e826c08b0cd5d35f5aba6bbb574d656ae9914d5d31f1aba63c3574c706ae98d0d5d35d1ad622ab5ac3866ae98ead6311d1ac622ab58c2866ae90fad5d21ddaba533b2ad6866a69cecd4d3619a9a5c33534d866a7890cd4f0dd9a9a52bb2ad57a69f9aecd3f31d9a7e43b34fc86669f902cd3f2935956923b2ad57d6889acad112d69a2263234cc35668898dad291175a5212534a424669484c8d1135c1a422b2348446469084acd1135d1a3222ab46427468c82aed11251da225b2344c13d68892eccab59e99a673b334cd7666998f4cd331dd9a64bbb40c47666996f4cd331919fa1bb334cd7067a8ac8cf511919ea13b334cd6a6718accce311a99c6233338c36a67186ccce309a99c6133338c25466998eacdb11d19b612a336c1776699b0ccd512199aa0a3b34c966655aaf4cb335dd9666bb32ccc7665998cccb335d198a1bbb2ccb6765996c8cbf09d99665aa32ec26665990eccb3219996641b32cc84d655aad4cad297595a423b2ad137001b718ca32e219465c0328ce775afaaf4b5f4e319325b3326c38064c9aeeb5f4df99225ab324c3726489aecb5f559d6be9c6321cb886439700c8731dd6be9be31f4b7863e96e0c7d25f18fa633ad7d36c63a96ecc770d818ea62bad7d0666369))
else
(if j < 11 then
(if j < 10 then
0x11b06f29de032b464134e888269d0104d35820be23bc17c17e82f80ef05f15d209a636c134c558269d090570e3609a62ac14c3758269ce904f01b609a52bc06568d8209ceb041359a0825c6c104b75820948f019523206264440c4c8081898b50312dd206263a40cc04d818946f01959d60426b3c084e8481486cf021219a042423408483681090fb0194a360364c6406c87780ca2ce003611a02241b40448168089cf4ee94e320125c0402498c8049ceeee94df9fea5bebfd4b7c7fa96e4ff52dc1fea53ebfd4b707fc82fcff521f5fea73b3ba54777f496fafe929ddfd24bf3fa48777f49aecee951e9dd2b463f74e807ee951afdd2235fba63bbba557e7e69ae4fcd29fdf9a53bbf3487f7e69500fcf01ddf9a63b3ba50767e3908cfc731b5dd2a33bba568c7d99d10fb32991f72032bee40647dc8d00fb339d1f666ba3eccb77774acecfa335e9f466bbbe8cd767d190ecfa320d9f4640b3e8cb6d774a6ceee959e9f1673b3e2cd7a7c59aecf8b31e9f1663bbe2ca777c888ecf8b3191f1a1bb3e2cb55774aaf0f8535c1f0a5a3bba568c7b19d10f633a01ec6646bd8cc877b198eaf6329f9eea23a3d8cd747b886daf6331d5ed623a3dac3557b19b08f670235ec6443bd8ca77774acecf5535e9eaa6bb3d548767aa908cf552059eaa536bba547d7a790faf4f299ddd2bc53cecf8779d9d0cf3b3619e766433cecb7d79d9b0cf3d1219e7a1b2bceca47774a8f8f2d31e1e5a6383cb4c5a79696f8f2d2135e5a51bbba526d79282cef25019de4a2323c24d7479084faf092995e126b23c6c25d7849ac8f150991e2a122bc24d6478882baf0924dde126ba3c2c07d78492ecee959d9de26bd3bc4d777789aecef135d1dfa1bbbbc4d6477c84ecef121d9de24233bc483677890daee951f5dd653ebbac867774a2ae0037621dc66c03b8ce7772fa0cced92119db241b3b6481676c9af4e5f55f5da65bebb4cd7672fa0ecec92119d9241b3b248167649ad4e5f59e9d865b6bb0cd6672faafaeb931a1d7262d3ae4b7d75c98ece5f51e9d6a633397d5887579b00eaf2dddcbeabc3aa4d7075496cee5f55d9d366b33a6c87674d90cce9b20d9d3640b3a6cb5d72faaf4e9135a9d2263d3a44c6a748968ae5f5621d166c03a2ca7772fad0ce7b3629cf66bc39ecd767408ae0e7b2d75cf654339eca6772faceee752d99cea52eb97d4767329
else
0xd0125935824ce23bc99c37e93380ef26715d24b2636c964c5592c9d0925f06364b2742496c08d92c96ef1ed59da4966bd492cd7692590ed24b209a49640b492cb6d8f6a2fb2472d9e3dab4348dcd8a91b9af123735da47a2b848dca5c91b92bb2372d1e3da9b2c874c6e91788c522f0d9243a5a2c874a7d90e98c9227097643a51bc87497d90e98e921f01f643a53b47b56769059af520b35da416632484c37690590ed20b211a41640b482c96d8f6a6fb207259e3dab3b47ccd768f99ce91ff11de3e663247ec3768f990ed1f3211a3e641347cc86d8f6a8f91ef219e3da92b800dd868f2971b1e526363ca73bc6dd57d8ee96fb1dd25f63ba6bb46dd67a8ea96db1d525b63aa6b346dd4768dbad1b1c939d63926b3472498d8e496ef1b75e2a3727c3c6e4e868dc9b0d1b9321a3725c346e497d8dc96cf1b7491c006e4646bcc888d799011af39de1b2abd436548c8d298cd1a7120234a6bbc36547e8ce98ad19f11ca33a6bb436556786ca0cd193209a32640b464cc7a86ca8ef0d955f63124bec62487d8c498ed0d955ea2fa6bb45f48768be904d17d205a2fa635436546786cacf516925c22ea33b45a4d768b498f516931da2d24b6c5a486d8b498cd0d959de2be43b457c8668af904d15f316a1b2a2bc36557a8aa9ad515525762aa62b43655658a198af1432d6a286632452c3568a19ceb14511aa28a03ec50cb7686caaf513f2d5a1b2abec49cc6589396dd137119224e62bc49cc6489886b51272d9225a1ab449ca4689392fb12729da1b2b3d4434e768869aed10d31ea21a63b4434c5588696f510d2dda21a632444c276886948d10d25b621a533436557a87c9aed0f931da1f2632440c37687c96cd0f921da1f243343e481687c929b0d9451e1b2b3bc37cd7686f9acb0ef11da1be6bec3a446487486ed0df2d9a1be43b437c86686f904d0df21361b2ab4436c84786ca46e003611a1a241b43448168689afb0194e321925c0432498c8649aef01951de16e5bec2dca7785b904d0bd005a17a0bf42dcd8c85c80ef0b7359603283342c484685898fb0194a36156446c2acc7780ca8af01959d613e433427c83684f902d09f2df60329bbc06557d84b9adb0972d96032b46420ce8884194c908b0196116032422c6808419ce908335d21065ba420cb5780cab1107d36020fa5a3c06556783990cd073211a0e640b41cca7d80ca)
else
(if j < 12 then
0xcd46b209a8d640b51aca7da23a11b46729de88eb3ad174866a2e906d45d205a8ba4bed11d177a23aceb44f359e89e433513c836a27904d44f21f688e9c65124a8da2490ef4474d9c006c1b50fc826a1f902d43f39ea72e9c650dc98ca1b930143739de72e9bf508ca7da1192fd42325f68464be508cb7ca1482e542325c284643ed08ce769cba8ef4172dfa82e53bd05c97da0b90ef41735da72ea3d4e5d68ca059d0140b2a36816446d02cc779cbaafd3fb35ca7f653fcfeca779fd90ff3fb2a027fa03bcfecc769cba0ed3f5209a7ea636ce5d4679cba4cf3eb05b67d6033cfac4649f09ae93e705f67c26ba4f8c07d9f096ed39759da79e6bd4f3cd769e79ac93d711da79e43b4f3c8269e7902d3cf29b672ea3ecf2487d9e494cf39759da76a6bd4ed4d779da9aed3b5359277a23b4ed48769da906d3b5205a76a4b6ce5d1679cbaced39f35ea73e6bbce7cd769cf9ac93a711da73e43b4e7c8369cf904d39f21b672ea3ece64a7d9cc90cf3974d5c006ec44e44d809c89cef34b419a70e41b4e1c8269c3902d38735ea696abece0497d9c09aed34b41da6ee41b4ddc8269bb902d37735aa696b3d4dc496d9b89acd34b55f66ce6344d9cc5a9b392fb36731da696a3d4d8cc669a5acef35f2976696abb4d44d669a890ed351219a6a241b4d448169a892bb34b59de69a42ecd2d347001b08d343209a68640b4d0cd7d967a51933f35de59e8334cdc84699b904d33731f659ea3bcb3d465967a8df32529f265a22bcc94b6f99294dd32525be64a6324b3d457967a0cd31b209a63640b4c6cb7d967a8c93172dde59eb464bf4e8897e9d012fd32365fa643cbf4c7597e94fd30711d25fa6ba4c0c16d97e9ae92ff01b65fa5abcb3d58897b9b012f72d1e59e8334bbc846977902d2ef25f659ea324bac977967aae92dd36125ca233cb7486696e908d2dd209a5ba43ecb3d48c96898c92d12d5e5a26324b4c28c96890ef2cf499c006c234b1c826963902d2c739ea3da9c6caf484c96085192bd263657a73bc7b537d95994fd2b325f656643ecacce768f6a8ff29531de52a5bfca5498095486ef2952952549c264a8c27e94a92ff2952e0253a0bbca5487f94a90fb29521de52a6bb47b547a8f6ad1928b3a025165464a2cc778f6aafd28335ca50653f4a0cc768f6a0ed27b211a4f641349ecc6d8f6a8cf1ed51563dab464964e8892c9
else
0x1b5784816af098ff533411abb6413576cc7da99a51b5d52236baa63bd4cd585ae590ad5cb20dab9640b572cb7fa99a0af5bd20deb7a41b56f4826ade902f5bd205ab7a5bed4cd18cadb93015b72ddea66ac2d6a4a64ad880b95a9215ab5242a56a4816ad494ff5334dd2b4a02ed65c85cacb90ab5972152b2e423565c826acb902d59729f6a66a46d62cc7dac598eb58b2df6b16446d62ca77a99ab0b57f2e16afe42b55fc836abf902d57f25fea6682bd5c4846ab8906f57120daae240bd5c4816ab892fb5334e32ad65c055ac977a99ab0b5612e16ac242b5584836ab090ff533415eaa24a0556c046aa8906f55120daaa2520554c026aa890fb533563aa6a6c654d4c8fa9a991b53531f6a6a63ad4d4b7da9a951f5352a36a6a42a54ec27da9a94eb53525f6a6a43bd4cd567001b8d4003611aa4e41b549c826a93902d52735f6a1a8335474836a8e904d51d205aa3a5bed43527da86a0cd511211aa2241b5444816a8892fb50d41f6a1aa33800d846a81906d503209aa0640b540cc6fa59a6fb4fd25f69fa633d2cd575a7890ad4f120da9e241353c4816a7896df4b351f69d2636d3a497da7496cf4b349be966a3ed37cb7da6f92fb4df299e966abad344c75a6890ad4d1211a9a241b5344816a6892df4b351f698e636d31cb7da6396db4c7259e966837d2cd47da5a98db4b52df696a53e52d4c6da5c84e14b525f696a433d2cd466001b6fb4ad25f695a73b529537da5392fb4a731da94aa2b800d836a4e904d49d205a93a6bed11d38ca4a9319495260292a6bbd11d477a41906d48d005a91a1bf520ca77a4192fb483363290a03bd20cd65a23a0cd47d209a8fa63ed11d28da3b911b47731de88ea2bd11d567a359))))

set_option maxRecDepth 100000 in
private def recBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := recBook328Slab0 j
  (w >>> (27*(i % 256))) &&& 134217727

set_option maxRecDepth 100000 in
private def hiBook328Slab0 (j : Nat) : Nat :=
(if j < 2 then
(if j < 1 then
0x2185218421702165216421602156215421532150214521432140213621302106210521042103209620952087208620852084207620752074207320712067206520642063206120562054205320512047204620452043204120372036203520342031201720162015201420131854184018321830182017651760175417521743174217401732173017201703167016541652165016431642164016351632163016251620160516031602158415821560154315421532153015201506150415031473147214631462146014501432143014201403137613651360135413521350134013201305130412541243123012061205120412031084108310751074107310651064106310561054105310521046104510431042103710361035103210260875087408720871086408620861086008540853085208510850084308420841084008320831083008210820081007650764076307620761076007540753075207510750074307420741074007320731073007210720071006540653065206510650064306420641064006350632063106300625062106200610058305610543054205410540053205310530052105200510048304810473047204710463046104320431043004210420041003750365036403620361035403520351032103200310026502640254025302430241021001730172016401600153014301420010
else
0x4270426542634261426042534251425042374236423142304218421742164215421342104207420642054203420141964187418641854183418241804176417341724170416541634162416041584153415241504137413541324130412641254120410741064105410341024092408640824081407540734072407140654063406240614053405240514036403240314025402140164015401238543840380137653760375137503742374137403702370136713654365236513650364136403621362036153610360536023601357135613541354035213512351035063502350134703461346034513405340234013287328032753271327032653261326032543251325032453241324032173216321532143210320632053201319831963186318531843182318031763175317431723170316731653164316231603157315631543152315031483147314631423140312831273126312531243120310831073106310531043102309530863082308130753072307130653064306230613054305230513045304230413027302630253021301730163015301430122860285428432841284027652760274327412740273127062703265426512650264326412640263126302615261026052601258025702560254025302510250625042501248024612460245124502431241024012354235123502340230623042301)
else
(if j < 3 then
0x6290628462806275627162706254625362516250624762436241624062376230621462106205620462036201619461936184618261756174617361726170615461536152615061476143614261406137613461326130612761246105610461036102609360926083608260756054605360526051604560436042604160326031602560246023602160146013583158305810576357625732573057025701564356425632563156215613561056035602560154805472546254615460543754365432543154305421542054135412541054035402540153915381538053765371537053645362536153605342534153405326532153205310530653045302530152905280527652745271527052645261526052435241524052375236523152305218521752105206520452035201519351835180517451735170516451635162516051435142514051365134513251305126512451205106510451035102509350925084508350825081507650735072507150645063506250615043504250415036503250315024502350215016501350124762476047324731473047214720471047064702465046324631463046214620461246104603460246014571457045214513451245104503450245014381437143704361436043524351435043254321432043104306430543024301429042874286428542814280427642734271
else
(if j < 4 then
0x8730872086318621862085708530852085028501847684708461846084528451845084318421842084128410840684028401837583718370836183518350831083078301827582708261826082518250824082148210820782068205820481768173817081648163816281548153815281438130810781068103807380728062805280428041803780327810765476537652765176507643764276417640763276317630762176207615761076047602760175827581756175437542754175407532753175307521752075137512751075037502750174827481746574627461746074507432743174307421742074127410740674027401736573647361736073527351735073417320731673157310730573017284726572647263726072547251725072407215721472107206720572047185718471657164716371627154715371527150714671437142714071367135713471307125712071067105710471037098708570847065706370627061704370427041703270317024702167516750672067106704670367026701657265716543654265416540653265316530652165206513651065046503650265016481647364726452645164506437643264316430642164206413641264106405640364026401639163816375637263716370635463526351635063416340632763216320631563106305630463026301
else
0x93819260918390629052875487518750874187408731)))

set_option maxRecDepth 100000 in
private def hiBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := hiBook328Slab0 j
  (w >>> (16*(i % 256))) &&& 65535

set_option maxRecDepth 100000 in
private def loBook328Slab0 (j : Nat) : Nat :=
(if j < 2 then
(if j < 1 then
0x3490469108d2111a40d3480468d08d1811a2c23450468908d1111a20d3440468608d0a11a1223420468308d0511a08d3410468188d0211a02d3404468034d00119c823380466808cc811988233084660bccc111980f3301a66008cb811964232c1e65808ca81194c23290465108ca111940f3281a65008c9811928232484648bcc9111920f3241a64808c8c119142322446443cc8869910a3220464308c8511908f3211464208c8311904f3209a64108c8179902d3204464044c8079900d3200463c08c72118e0f31c0463408c66118c823188463088c60798c0d3180462d08c58118ac23150462908c51118a0f3141a62808c4c118942312446243cc486989023118462288c4479888d3110462188c4279884d31084620bcc416988223101e62034c4011870230d0461908c3111860f30c1a61808c2c11854230a446143cc281184c2309446123cc241184623089a61108c2179842d308446103cc206984023070460d08c1911830f3060460b08c15118282304c460934c121182223041e60834c101181c23034460608c0b1181423025a60488c0879810d3020460388c061180a23011a60208c0311804d30084600b4c0111800f3001a60010c00113102261044a40894411280d24604486089001119022301e460088a0111202222044420888211100d2200444004860110a0221204422088421108112101e4203484021080220c04414088241104022060440a0881211020220304405088081100c220104401088008900021601a2c00c54068940d1241a2443448468904d1201a24010460688a0d1111a220b444078880d110082143442268840d1061a20834080680800
else
0x7201ae4021c802b900471c08e3411c64238c447180ae3011c502b8a047120ae2411c442b888471088e2091c406b88087100ae2011c3823864470c0ae1811c282b85047090ae1211c222384247081ae1015c202383447060ae0c11c142b828470488e0891c102b82047030ae0611c0a2b81447024ae0491c082b810470188e0291c0423806470088e0091c003b800570008d8811b082360846a208d1811a0c23300465208ca02594023240464412c88119084b210464112c821190223202464008c60118a04b140462806c483189023110462206c42118841b104462008c400d8800b0c0461806c2825850230a0361212c24118481b088961108c220d84223084361008c18118301b050460908c120d82223040460608c0a1181223020460308c05118082300c460108c01118002300035a048b401164022b01056008aa0115202aa4045404aa80915002aa0045300aa60114a02a94045220aa421548422902552048a4015480228c0551808a28154502289055100aa20114302a860450a0aa14114202a840450608a09114102a82045020aa041140622808450088a00954012280044600888111101222004420088301103021f1023e1047c108f4811e8823d08478c08f1111e2023c28478488f0811e0c23c14478208f0211d9023b10476108e9811d1423a24474308e4411c70238c8471888e3011c5023898471108e1a11c3023858470a08e0d11c1823828470308dc811b882370846e008da411b402366046c83cd9011b142362046c308d8411b042360446c034d8021b002359046b008d5011a922352046a208d4211a8223501a6a008d3811a64234c1e69808d2811a4c2)
else
(if j < 3 then
0x901092020e4021c802390007188123082460848c08912412242244504888891109221824424488449105122092441048818910292202243104861090c1121812430078600b0c0121801c2904850890a01614024280384a09092121222424078480b090121201c230484489088921102c2204844070861210a242107842090840e106242087841090820e103242045840890810e1012c20248400b080121001c190483109061120c05c1805830090600e0a02c14048280704c120903c120482407046120885c11078220b044120881c10c4821090420e0832410448204f040960812410078200b040120801c0d048188903016060240c0381609029120502c0a04814070261204a24090481207022120441c08648108b021120412c0824810170201e0402c08048100701c1203224060580c09015120285c050480a0701312025240487809090120e0223c044580889010920205c0405808090100e01c2403448064900c120142402648048b009120121c0224804170081601024020380309005120093c01248020b004120081c00c48014b002920042c008480107001920022c0044800870009200094000b8000f000120001be4047c408f8411f0423e0447a208f4211e5023c84479008f1811e2023c14478188ec811d8823b08476088ec091d802bb00475408ea411d4423a8447500aea011d3023a50474888e9015d2023a3047440ae8811d0a23a10574208e8311d042ba084740c8e8115d0223a0247400ae8011cd023990473108e6111cc043980573008e5211ca223940572808e4c11c922392247240ae4811c882b910472188e4291c842b9084720c8e4115c82239024
else
0x358026b003d4007a5013180362206c420d8821b102362026c400d8481b088361086c200d8281b048360886c100d8181b028360486c080d80c1b014360206c020d8021a9803d3005a500f4a0169202d2205a420b482169022d2007a400b4601e8c02d1407a280b448168882d1085a200f440168603d0c05a140b424168442d0845a100f420168302d0505a090b41116820750407a080b40c168142d0245a040f4081680c2d0107a020b403168043d0085a008b4001678024f0039d0093900e71024e0849c0493808e70024e0039b0093500e6881cd02499047320126401cc60498807306125c024b404968072c40e5811cb005960092c00e56024a824950472a0125401ca423948092900e5111ca204944072848e50824a103941092820e50224a043940492808e50024a00393809260924c024980392847250164a024940392447248124901c9123922092440e484249083920892410e481249023920092400e4602c8c0491807228124501c890491207222124441c8844910872208e44024880390c092180e428248503909092120e42224844390847210124201c83049060720a124141c8223904092080e40c248144902872048e408248103))

set_option maxRecDepth 100000 in
private def loBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := loBook328Slab0 j
  (w >>> (19*(i % 256))) &&& 524287

set_option maxRecDepth 100000 in
private def groupBook328Slab0 (j : Nat) : Nat :=
(if j < 1 then
0x2704d89992d2524909011c22c44c8810c20e41c821001fa3ec7c0f71ea3cc788f01de3b8758e91ce394720e01be37c6f0dd1b636c6d0d81aa354698cf19a32c638c117c2f05c0b51662c4588b015a29c528a414627c4c097124238450851041fc3e87a0f01d8390710d61a4328640c4184300600be1742e85c0b41682c0560ac1542a8540a814c298520a21402804f09e1342604c09612c258490901202404708e1182304508a1142204308610c210410821042004007e0fc1f03e07a0f41e83d0780f01e03b0760ec1c8390700e01c03806e0dc1b83506a0d41a8340680d0198330600c01802f05e0bc1782e05c0b81702d05a0b01602c0580ac1582b0560ac1582b0540a81502a0540a4148290520a4140280500a01402804e09c1302203e07c0f81f03c0780f01e03c0740e81d0380700e01c0380700d81b03606c0d81b0360680d01a0340680a011022044080100200400780f01e03c0780b01002003000
else
(if j < 2 then
0x580af15c2b0554aa152aa153ea794ea9d538a6d4da9b530a5d4b294526a4147a8c518a2d45a89510a1942a8550aa1142284508a1140a81500a013f27e4f49e93c2774ee9d93aa744e89d1382704dc9b535a6b4d499d322614be9792f25d4b89652c2584b095d2aa544a49452724c49092122a444829052023e47c8f91f23d4748e11922d454899132234448790da1a43285d0aa1242283d0720e41a83506a0a41282102203406801001ff3fe7f8fe1fc3f67ecfd9fa3f27e4fc1f83f07e0fb1f43e87ccf89ef3dc7b8f71ed3d47a4f21e03bc774ee1db3b4764ec1d83ae758e99d23a4748e79cf39a72ce49c7386700df9be37a6f0de1b93726e4dc1b836c6d8d91ac34c688ce199330650c899031e63cc5989310614c09802fe5f4be97a2f25d4ba9722e05b4b59692cc598b21642c6588b09612c2578af15d2b8570ae15c2b8560ab9572ae554a895129e538a694d29852ca41442845009f93f27c4f49e93a
else
0x2033ff7f2fd5f93ec7cef91f03dc7b4f5de8bce792f0de03bb76eed5da3b2762ebdd73ac754ea1d139f738e6dcbb9371ee29c4385706e05bf37b6f0de1bab736e2dc1b736d6d4d9db23626c0d7dadb566a0d35a4b4868ad11a0b3a66ecd599b32662cc59832f65ecb996b2c652c9991b2063ec798eb1d63ac718e31c632c618b316628c418730d618c2d8430660cc1182304602c05802fe5f4be57c2f65ecbcd792f25e4bc177aed5d8bad732e25c0b7d6fadb5b6b6d6cad65aab55692d05a0b2d642c7588b0d612c1))

set_option maxRecDepth 100000 in
private def groupBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := groupBook328Slab0 j
  (w >>> (11*(i % 256))) &&& 2047

set_option maxRecDepth 100000 in
private def packBook328Slab0 (j : Nat) : Nat :=
(if j < 10 then
(if j < 5 then
(if j < 2 then
(if j < 1 then
0x5982bc1540a6051825c12808804281ec0f206f03601580a604922290bc8301480a3051428613d09c84e026c12c095048423e11708a042c21210107f03c41de0e9070837c1b40d506903381880bf05b02a814e0a304c025011607c03c81c80d8058029812c08a04201e00e807203701a80cc06202f21690a084c41808b845421610a08083fc1e40eb07083801aa0d306282fc1740af05502a013209404781f40f2075036016809c045022010c06e03601780b803e018ba6cd4a02cf3458b2c18e2c3385831c1862c30612603581a20ce06483181660ab053028c13a09a04402040fc06f030017409204508e045021c10906f83681ac0d2067032c18c0b605782ac14e0a304f026811608203f01c80d806102e812c08a03901880c004e01808e046422a10e08684081fe0f707183881c00d606983381980c605d02bc1560a8051827c13408f042820c0fc07503601900ba04e02280e006c03301800b804e0258114061b00b3439c1c60c963185869c00b320e207083581aa0cd05f82ac1540a104d025010807e43ca19d0a684541ba060e4231fb9a40c9e62f1859c2c34e3e000
else
0x22810407403801b00b80500181ae8d4869a3471a20cf06703311970c9864231f18c0c2c60c30008c845c2160f907a83cc1e00ef070836819a0c9063030c17e0a104e8268128085034819c0c005d22b114c88a4180a104fc26a134094048c23611808b84501f20f607883841b40cd065831016c0a104f026813009404582140d406703081740b0053025811408403a01c00dc05e028011807403401808a83e41ee0f2066833018a0a104f826410a06b03381900b403f21f10a084642220f906c830323986bc8de1ab4a5869c8ce2034a791bc35624b105869c50e1a3341918c6061a0ea06f83741b40d106702e415e0a6051823811608804281d00e406f036013409604519a0c8c63030d08f0474238115089844021e10a08404181fe0fd07d83941c80e307003741b40d3068833817a0ba05982bc1500a6051824811e08804281dc0ea06f236114089c44508a04241fc0df06d034c1a40be05b02a014e0a3049822c0f007503901b00a204521d109484834a19c0cd064c32318c0c3460019908e045c226110087042c21010608083ec1ca0e307083741b40d506883381860bf)
else
(if j < 3 then
0x7c83d81b20d806702fc15e08404101f80f8079035019c0c2058229912c88a43321190808301a105d021010607d03581900b404e622ac8563ab1b3858d746a434d19c0c604980dd06d02f817208f045822010a051027013409604518c0450226110086042420c0ef07503a41ce0e106f83681860bf05c82d81660af04b825011c08b04402140b205802b014c09a04b22491146ba3521a68ce064c31808a84402140f207683841c00dd06d03141860bd05d02bc13209704a024811e088042816c0b4056228113889244507903b81c20da05f0264130094049822c10a05c22d11608a244521d107c8303381988c8463030617e898c496119089844021010607a839c1c40dd06d03241660af04e826811608824291808ba44d22591146703311908c6060c2fe0a3851028214009d84e826e131090046422a11308684281ee0f507983b41d60e507103801ba0da066032418c0bd05d02cc15e09f04e826812408f04402140ca06403001740a004e224911486013c099048822c11508a03d81dc0e006f83681960be05d02d813e09e04d024c11e08b04281980c806102e814409c04b
else
(if j < 4 then
0x7283181880bf05b02cc15e06703181840c005d02c81600ac053226912c88a11908803c818c0c505d02cc15e06b034819c0c806022d11588a044e224911418c0b605781ac0d406603201840b8058228913889644521990886c43571a50cd064c30d17e83a41ce0ce22891345fa13e099844c1fa0fb07803bc1d40d506883381860bf05b02cc15e07b03c81d00e406f03601640ac053026812c0920451b10d5c6943341930c3424a12407903c01da0ce06282fc1740af03e81ec0f207703a81b00b605a22b114c8a044e222907c83a0f207883b819c07d03e01e00b805a02c014c0a204b022807c03c01825d8d0066232a1868c185fa2a007a83cc1ac0c906302bc0fc06f230117489a33118b0c3460c2fe09704b424c11908804081fe0f707a83941ac0d3067033018c0ba05982bc10608103f01dc0ea06c23291908c045d228113888a12b09384001f00f707b035010608203f01e00ea06603201840ba051425a11504282040c192c9803611ab0d1065c31618a0c3460c30008104041f20d506682fc15e08403d81e40d806703001740ac053211868426012f09484142080fa
else
0x4182040fa07b03601ac0d2067232116c8b445622811141ca08304101f40f806a02e01680b0051225911487a108083022c11008522904341da09a04281740a2050227113488a108078026811608804281a40ce06303081640b00562299114214106079026810a06b034819c0ca06402d81680a004e422926890a46b23511988b836a3a51cf0a1c44d18183f41f60a304b825011c07b03c81d00e406f22b114c89a44b22491146d434a19e0c6021c0ff07282640fa07b03a81b00b4056029814009c04942291608a244b20f90788383473909c58e2046f236112c68e32118b0c242040fb079839c1ca0ab054027c10a08304081f80ea06f23611808ba450227112488a0a9054028010608203c01d40e406c23311848a244b222909483834a18a0c34616306055028413408423c91bc8ce44508083f81ec0f107783a41ca0ae05682a814408504202080f2072035019c0c2058225911484c4232108404106079235919c8b444521e90a083032a150093422611005f82d81660af02e016c0b405902901440a004e226846418c0af03081800ba051228113889a44b2228ca82260f1)))
else
(if j < 7 then
(if j < 6 then
0x9d94eb274937c725a92cac224b7832db92b27182b195744982497d0aec9758ba85cf1c60c9630d9384575f46bab2da966c7683ae7d336ddb3ca90547297c88c26a72fac64cfe67722310a449415b39a9b2cd4e65f2af0cd40fe0464581d34e706ce3571a9cc942c7553aa3908c74d39c11183be0b0436921866832318c0c345ba2d695a4a6651cf18786a3988da08622f0ce06623181868a6452805ea5842159468a3442911419c05c42917f899c482231833810606b635214891e48522e914489c094233918c8c245922281ac0d2067432a1910b484523591a88cc334391829c14609704a023811607923a11b08a644d225911466832305782a013209704901f40f605b22d114013209804981700b405125182bc1500a604f827413408f04282040fc07703a81900c005d227112488a0a8053824c0f0064430a14509672338f92a89420aa053828413c08404101a80ce06142c214d08a4a107683a81ce0e527e93ec9ca45c22d916488a34708103b41d40e503c01d40e805d228913889a44507e83ec1e00e704102040f2074039019c0c6061229913489644507f83ec1e40e5
else
0x36699a8cbc64a2240d4c64e2f917b8b2c5862a413989784b425032515788da4461838ad04a018123f8ee476c35319a8c9c61c04628912c08bc2f917b8ba05cc2cb1618aa854829014509784b42503259928bda5722b492188a833958ca9410c485e39c9c64b5c1df65232193be8b043692186683181870b7456e2a414d8a64514273537a230e306992c096008da0e6636b17910c85e23685942c00b0436a178bda5df273129090c112467a2c10da5ff26d9218716383836be2d960c5e58d1accd3031ad845a4e51ee4c5249c68e303185a6ad2950ca4b3810d286462d53a39c60e1e7083831bf064226e78fb9b9abeb892c00bec55a2a057da930b0034c19b8cd05fc2fc56c2b2149674c39b8cd05aa2b35371a8069233e19e0cd06663311940c9861e30d1840c185f82fb1988c9861a2cf15789b84c02495501cb8d946a93301964ade38bbcede42716f1858c160069e31857e293149674f38c0d3c67032838d1c60df86fb331992c67032138c1a74d0666018f8c6053a2597cf2e78f367923c59e0cb6e30dd86dc3661ad5d54f9c34ce230d341992461a2830b985c42c815d)
else
(if j < 8 then
0x53ba95149486d25210202240cf24311786623161830bec50020f6fb37d1b009ed4ef913c3fe05ea36ce2dbfcd5d58d1d6ce1a35b986b9b94986491b50d3469834a9b54d29e94ed57372d1cf28394770bab5d40a4c3708d486502fc7a93ca1e00b343989c18aea331d306926d413af725ae2cb8836e4d525d52d473838c1ad8d0638a78c3a0d662b214c01ac473e38b7c1bdb9d0adc45b715746dc179ab8d5762a4d6a6b1a9c4b003ad1d48e9471e37c1b708bc4201f76e235756706622ac8db84c41668acb58dababa33d79e9cf463767b73989baadc46acaaa8d2034e5421d4cd9666a1658b0057c25a7252cd562eb0c53792d081e2e835f1aa8d2064b325115051024a3a41cc8e5e7223861b2cd0809538c1adccde5ac1a70cbc64832058aac394dea5a4c0917862e1812b31594ac04b024311b474639f3ca133c96040f1d10e746ee3742430ecc75e3ad1d48e8c73e38b7c1b33d948c6d43fa178d0226a52f2928c9428214089f82c004639c9594ab429013e09cc4bc0a438b992869c2f117709a84cc25e325156888c32418c89282ce06d78cac9163247f1a98bc45dc2d4
else
(if j < 9 then
0x13b89bc4d226112a09283461616a4b31d8bc88942512d06302fc1710b1c57c2bb1538a8453c28e3441a10cac64b32515a49603393911bf0d1066432515646d63691b40d8c6bc3591a98d3869034319c8cc865a3271910c7863230a1838b885a02c71580a9c52828e14209a44a824a0d1864c3021728b4c5658948e847311284e41782b395708da34e1a58c9061c2b714c89dc4de25412506042f61780b985c42e01670b105742b80a444321b506844a074039811204a823b2c189488625211b43ec1930c8860430017b0b905a42c40b044320d09b64a408383d01cc0a424d92188da40d204101074011227e133c96044720b90508263771b8844820e0db05802180bc04720a904c82240f206102c7060fc26792908da3b41d70ea874c3a07b737118dac0252c19e888c3396232bad4b0a4a38310a460c27f53ba9a53be6eb36499288902c34231d4ccfe666325154c7723b63a99bfccd2554258111881c34d1648aa051c28a14209282d204c1a68b7456e28a13309403da1d42b91564aa62dd1638adc54e28e13487fc3da1a30c005501b6086603a854d3267332811b4632299
else
0x3c09db8bfa5e72f19710ad41636bbb5b149873835b1a0cb00321783392d6dc71832597f4b443a01d00e6870e36e117889c3ea1c41d00e6c72438e1c60e2c7143871c28e0c6dc227110882c40a1f58f8c711ad0a702bc957453e16a4a916e87223881bd8db84281f72ef171072237f1be0db845e2146fbb78dbbcdc46aea9bccfe2d2730ab594fea6643f998462e24a1a40c1c5a02a413f89984c22503251798bba56122f0b8858a2a554f2a2150872238c8d4c69033d1990c8856e2941450a104141d46aca854e1c55c2368c9056e29933795c0ace4a424311b489808984331b51688b042391b488e280126083c3e81910c085c8160086636b1792245ba20990307683ae5d52e99740b6e4e22008cfe27f734a9514946a7334992856e24a3320cec67232415b8a6452828e53ba9a529464b3250c645a02567252b74e7a71933095806ca3511a70d2067a2d014c8a104fe269525259d2c087f2740be85f02d01638b005602a713489904c225632a192cc945fc22f0b0057c2773391950c945a32368c9c62e2642de131c6da35c1ac0d4c6963351938c5c62630a1710ac054e27f))))
else
(if j < 15 then
(if j < 12 then
(if j < 11 then
0x19c8bec52028814209704940c124a8d0c65a32718c8c1452025f7253605ac4c86423902061a2fb338184cbec5dd2e1960066829813708b84261f60f807883ba1c90de06e434018f0c7063030618142a12186682b314c0a0c4dc2080f207303781b90d606ac34019a4c8263130a85427612909203a3458211c89e3911bd8db84281c43d79e8cedc5c426092544f827332f111853829b14d0a404e625e748397d88c84632c0c905e82f373e39cdc94a5f3250b0c4e62583250db86282f917b8b2c5862aa35219f0ce665e3281928b003353891b2ccbe4461738b9854e28a32c1928bd83191700b7c5962c315e0ae852028a12f09684a024a548297d4949ff4d711b46943341930c8c63030d17d8b5c53427011808b845221610988444021f82fb17bcbc25dd2e196006943231890c3445c2290fb07243261802430cd065c3181868a684e0239114883c4101f20f207743981c38c0c6020a8c6d4431e2cf0631ab374dba388e4c55e9988bd834dba645d5e94ed57372e50f121527502b84f186051a90b8454c29dab74cd1e2cb163500cc460c2a06feb6897167812f38e7472038a
else
0x2ae8db868a3151888c3860830117c8bdc5b62d916b0b2c5862aa15209f04e626f12f09684a024a2d616a0b485812b495741680b02430ce4632290144092835c1a30c085a42c410706d82d0160086225111c6a634119e8cac6402e21700b7c5962c315e0ae85542a41480a2850825e12d09404941a30c085f42f61720b4858816e0b04462219098834274139891204a2ee9718b4658013808c043a216109884441e1f80fb07bc3c21dd2e396b0b4058c2c095c890c0b443813a09cc48924311c08140e845a22c10da84a423921888e08614d09c047222e114888c43020f10407c83d41e40ee870c3781b90d706b03561a00c605ec2e41702a792188da44021a10a88020a442610488203911c10dec6dc2142e210406dc22f0fb871036a19ba09497dcb8a5f5272928cbe2549273a41d10a8e52f99f08da33d56d29dd4e4a6f52519bc67a32434c99f0cee65f2ae11b455425f32e1938c942e21600af854e2a13391950c945e02ee95745962c035f1928b4635a1898c145962a734e997cca864a2d19604aba0861738b9454228814209584a824a0f605e82e4169083836c160086)
else
(if j < 13 then
0x70daa98e1e70d1c78c4861a21078839d95b0acc555a92cc9e38f1c68dec6e636e10808243bc1cf6e6b7114eca532d68e5c71e38d3b71890c206092e69710b5a3759b7474e388e854b19c60c9636e6e22db93887001c90db83d61c41ce0e5472438b1c30e086dc28531a97ccbd65c42b18e0c6dc1c44d999505b4277137895049415c2398b885802a712a09283c01dd561a928d422e71728a9c54228832a1928ac444a2238ce450824a4c0a54116e88c42610204e227030997d8bba5c325291c48dc22e10987d83ba1c70d606803181812528b5c53427011708a442621210207e43ec1f00f507883ba1c90e186f03721ae0d0063c31c18c6c0ae8cf563af1d38e8c7223823b71850b883911b708bc4281f72e216ccb302bc15d09f04e624a7252bc95daa525282928c9433a3939c64d1065a17b0bd45d82e914e0a6c53429014509f04e62507253605acea7c52d1cf46ce35019f8cf46482d613e09bc4b424a2ae0c905e82f316d8b6453829b14c89f04e625e12d09404941b82c095708e646d15f0aa84b825a52929414947291b00cf46523271658b0055427c127092835e181
else
(if j < 14 then
0x52b295149472733516f06a61fc2c08d3c67031a18c0bf05f628511a08c444021a10b88183e01ee2f51728b925c32c98c6045c21a2f70d345b82830f8074830e1815d5a03cd0a24b11d08b84181f42f717a8bac5c32c0126c5b822e113088042620a10207d03e01ea0e487083801b60d906a434c1a52d19674b2e58a2c4160cb02112458196c8a834d1708b705061da2db16a4b1658022a0e5022405e4079dd4edc5d32e20e3871838a3b71ae0d0a6052fe97acb8836e6e22aa14b06b234b19a8c9425f52c196063e2f014b09a84941c48ad31194946eb32c1928aaa36e1788b4c4d4266125071030015b6ad2c754d4a5f32f996064e2a83331960c943531858ac84d42667252c24e707182f8170c69a3381930c7c63024412008e446e23030e9858c266012f79730b8e31d2580d746a434d19c0c9863030617e8b8c5bc2b8131092c48e24111d08dc466230113087443221610508043e81ef0f5075c3a81c72e1926c69a32c18e8bf834618056f2ae10a86de35c0c2c49622850728213e49da4c0215096038ad2ad2564faec67612c8ce46323991cafe50d24b7882a18f28393
else
0xde06e435c1a30ce864c30414e24e117c6623211830b8c5bc2b812a892c47423811888b844c22010b884c4142040fe07d03e01ea0ec07503921c30db06c83521a60d2868c33a1970c50620306181648203cf567823b7171076a3a71c38dd86dc2de15c0a1444e1f52e2103c81038e1c60e286f236e15c0a1444e22110588143fa1eb4eca710d2c66a32f19286722f014b0a104d4266128092838816284339854b4a4a36599a8cb436e1788bb85a82cd14b8a444d426652f29414949814b19b14aec3533351968ad235319e8c304d426612f09404941a30c085f82f61742b515a4a9854b27312c088e33838d18d0bdc5ea2e1921845c1f22f716bcb26486141891048023911b88d046021d10b084c4021f20f787a83981c70de06ec3341958c9c60591284a2d7956093638a141898838e1bc0dc86d835e1ae4d4a68d3269824b4a26c8ae05712588a044620e10407c83b41c34d42614a2445e1ce0e1870436e16f0ae050a25111a88783e61eb2e2103c8103761b70a143881ba5d5ae356dca094e2200cd762a772a392967265f2b18b1c4c225672a392969cb2036712c04c8261)))
else
(if j < 18 then
(if j < 16 then
0x2f3175cb865922c00c183cc180771ab8cdc66b51830ad44682238f4c76a222f8b52a9c7463628df46e932c9934d7a6ae0cf062a0aabcb92540efe5501db8b883315832a80f3a78b3c5171071437a6edb7117169fd32f99604b424a762ac9d59ca5f5251978aa00892580c605722870f5070c1bc0dc246922849823410987b83d418126e12449144872048c6050e222109881c3d419306e024411a02b142896c46823211188604261f22f717a8b9c5cc2e1925885623410987c83d41c70e186f03761b10d2066832a1930c082580aa03b61630ad6dc76e18c0c004261ea2e9170cb645a62c0960074e3823b71710b7439c1c30e1070436e528a8d53887a73b717105762b03539984ca82ef17509844ac2547252960cc22c714a0a384d22643309958ca864a2b1921863825872531312d27272de15d861026413089584a824a0bf85d02d816b2b495349d04b4258112888e26112c09504941a30c085a409804730f980cb2620610208003e01c92e3164c47023710087a838e1934c0944896044a207892c47422e3061828be85ee2f5170c93824712088e846622610c88283e81d4
else
(if j < 17 then
0x17188f044a2080ed073035e1a75d79868c005fc2ee9720b8625b2e61718b5058c2c2896c46820f10407f03c21dd0e8073038e1c30e086fc3681b10d606a03461904c6a6193024e827307983ae1a22c91608b0245e1cc8e5c6dc1c435a97a4bb437a1b70b8c3b61c41cc8e5c71e3801bf0db85c62243081824c045c42031014702376bb7d79e53f00672fa9fccb8302736b9714949dd33c9990c9433d3a28d4865832615188204001fc2e9170c72c3311830bf85f824512108e046822010208003f81c98b6bcb9b989a74d193985f62c11510a7c496248122890847022010e083c4082000fe07883c01dd4e527253867463981cb8b8c1e26e936f5b1ed876c0a11cf322e333818d0c4c60a2fe16006a833611a07f03cc1e20df068c32418f6c1b6058bc8e63b717f46dc29f3c59dd4edc5fd2e9971073838f1c58e046e036e1718ad43fa1e7ae2d71253ee7a5412a04cf4282740a9b0f7075235017f04762343111810c0230017188203b41d76e62c014686ac19508043961c31b08d5868832e1868c0041e1e12e397106843000e206002220461830b8c5ae2b511f08d045a20a
else
0x30017f0b90399124087041e2002f016bcb4658126811b861a20f2ee8db861e30d1608a8853e24b1240918486239111883c4102000fe87f03c81e00ee87383981c32d411e846822310e883c3c81e10ee87403981c70e1870437e1b40d886b03501a30c8063430207a60caec0f327973b7171062830d3079810ba45c32c08ec475e3ab3d89e8cb883a31cc8e5c71e3801bf0db858821010488083ca1de4e8a73538876e2fe89fc4ee2697252958e7a33d13b89904ac1514251d04cee6582a98d546a432c3941a8cd406002fe08d843420130017f072c24512108e046820430017f0b5256d1a90b844682046d8a8013c49e04d1a604b5e0e638b19c0c68626305179862c2e315a88f845a20a0f3071436c1a94d126093027761be8d5066c3161868c185c62d715a88d043420a0fe07983c41d80e1868c3141836c0add96e0b6e54fa710b883af1d58e607023761b78db85c62b5313979c73838f1c08de46e036e571aad53ce9e34eca710d0224a7413a05cfca6839e89f04d42662ab0db06aa3521970ca86502ac34f9820c005ce2e6171cb8633151b2869402a004fe188cb98326))
else
(if j < 19 then
0x6c0b1b56f4a893c40a6833e18155f9de8edc6671cc8e2070c37b7b73a69d16e2a636a9accbe21a4e9270ce946232c60d1c5822bf523a898e045e412588803e41c31a38c2060c28914288b83ac1c37813a25b869f22368b0457e24bb14d70e8db1c36c0ab04d12388b92d63eb032896c0ae50b88382636ae1d6feb6e54d2710c9426c72fb96176ea2650d2740e8e28031197a0bc85d72e8170c3c81d25882b115167143869a68c4630d2fb0d2861a30616f0a6844c21a6fdb70d62469a14d088c4341e4d3155664f6e765ca1e607303947bc3db9c36b6e5152710cd026d2fe0ab446c20110002e016a0b142418d0c005fc26112f0890234302168c60c23410508003f81d62ea171cb864ca264112071420a10007f03ac1b00d486042340c8259117c89030611a08283f81d42e5970cb465812be11208323311830b8c53e23410508003f81da2e191a04681fc0ed070c3781af2d19688b0246822410646ec36e1858bf85c623410207f03461816be2eacee47703b71a7cb883ab7bd3db9bb6dc454f997ccb833d5882c3d4945cc2e4171cb861d26e7370d3464e82730c3443420f
else
(if j < 20 then
0x8fa475238ee4b50e2868c9824c50ea87143462330d1748b9c1b12c0939845221a0ee870c2f006e30e170c8e246e12408a443417823b11b84521c30dc06bc2f015c33a9898c3861a2400c484f022030e1868bc05032400c404ec2264d898a4c4661c2f2099445221a4e1a6e135e9894c099744ec22951028693a49813cc9afc7322bfabac9a1cdae6b4e92738c5c08a643a8b93d45b910e08683a81c76e1b2714389d644e172cb0824b317188cbb45c311707683ae1b98c5c626302e575bd18b86e436e7bd3db9cceb6e346194852425f79e3871c34a1d50e2868c461d0ac0c131e46b883918b0457e29a525a8a53866292d7964cb02388591aa693026bf1cc8e2070c37b5b72a2d4e8a2a3c11df06cc3645a12cf9678abf5132620e982c175fb91dc4cabd4e595645122857173871b869cb2f117803f61f46ce2b04d126571928b785a229a14a88983ec1c30cf867032c18f6c0adc96dc7873bf9db8d342523b21d1ce8873e39e18706d434c5a52875438a1a3a38a0045822b2f21784bba5d72e188704341f24e6271d3866890fa07c83de1da2eb96245342290f786bc328193
else
0x11e66e1a798b861c3d1fd8fe90d1816fb26049581c3cc0d6061aedda4c09770b021cb6ed3625b02b785b71db8b8823d6e1a7493966702e9173830215dae44749ac49ee2f9066832a1819c3374938878f3c31db86dc1c45af97e4be85f02f11750b921f98fc3831c0cb852e58ae05341d48e4bdb96dc75d0fd07e03d01da4e8270d3025da10688204021c36c0a600bb45892c0958890c19accae606f0d1da7b72710ef038f7c328f53865f92f11750b921819384739b869da4e197a870a1c3ae1c7c23dcd8f5c1adb8edc36e6e2272cbd05da2e188343ae1c4ae1c70de3edef58e9db857029a)))))

set_option maxRecDepth 100000 in
private def packBook328 (i : Nat) : Nat :=
  let j := i/256
  let w := packBook328Slab0 j
  (w >>> (13*(i % 256))) &&& 8191

set_option maxRecDepth 100000 in
private def progBook328 (i : Nat) : Nat :=
  let f := packBook328 i
  let hi := hiBook328 (groupBook328 (i/8) + (f >>> 10))
  (hi <<< 19) + loBook328 (f &&& 1023)

set_option maxRecDepth 100000 in
def count328 (m : Nat) : Nat := metaBook328 m >>> 68

set_option maxRecDepth 100000 in
def record328 (m i : Nat) : Nat × Nat × Nat :=
  let base := (metaBook328 m >>> 28) &&& 4095
  let r := recBook328 (base+i)
  (r &&& 15, (r >>> 4) &&& 4095, r >>> 16)

set_option maxRecDepth 100000 in
def stateHash328 (s : Nat) (ws : List Nat) : Nat :=
  ws.foldl (fun x w =>
    let a := w % 4294967311
    let b := w % 4294967357
    x + a*a + b*b*b) ((s+1)*2166136261) % 2305843009213693951

set_option maxRecDepth 100000 in
def hint328 (m s : Nat) (ws : List Nat) : Nat :=
  let b := metaBook328 m
  let h := stateHash328 s ws
  let nb := (b >>> 40) &&& 8191
  let sz := (b >>> 53) &&& 32767
  let u := h/nb
  let k := offBook328 ((b &&& 8191) + h%nb)
  let j := ((u ^^^ (k*11400714819323198485))*11995408973635179863 % 2305843009213693951)%sz
  let t := slotBook328 (((b >>> 13) &&& 32767)+j)
  let code := t >>> 7
  if t % 128 != 1 + u/65537 % 127 then 0 else
    if code % 2=1 then 2*progBook328 (code/2)+1 else code

end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux
private def startCut328Slab0 (j : Nat) : Nat :=
(if j < 2 then
(if j < 1 then
0x0
else
0x8008006006004004004004002002002002002002002002000000000000000000000000000000000000000000000000)
else
(if j < 3 then
0x5505305105104f04f04f04f04d04d04d04d04d04d04d04d044044044044044044044044044044044044044044044044
else
0x1c81721251230f00f00ee0ee0a109f09e09e09c09c09c09c098098097097097084084084083083083083083083083083))

private def startCut328 (i : Nat) : Nat :=
  let j := i/32
  let w := startCut328Slab0 j
  (w >>> (12*(i % 32))) &&& 4095
private def cutHead328Slab0 (j : Nat) : Nat :=
(if j < 6 then
(if j < 3 then
(if j < 1 then
0x4ea809c1413530266404c2a0971412b3025240498c091981212023e40474808d90118a822c5045440899010fa01c7404466071d010fa021a5042c8083a01052020550402807f8c0fd201f4603e2607b8c0f520196203ce6078d00efa01dc303b260749c0e7201cb3038e8070d00dfa01ba20378606e880dc101b7103686065880d8981af203000065880d5a01800032c406a0c0d22019e6033660660c0cb101924031c8062cc0c3a01800030680600c0c000180002fc405e900ba90177302ea405c140b620164802c26057500ad18156402a48054440a71814a4028c80505409db007b10270604d8809a1013040254c049180902011b5023240455007c90111401f6404148086a00fd2020e40425007f901072020a40405007f900fd201f6403e4807aa00f5401e6403bd006c180d440152803410064200cc40190803b0c074980d4401d260398c06a200e2401b6e0360c06a200a9401a0803210066200c840186a02fd005c380b530164602a50059180af3015a402b48054a00a54013ce0264804aa009b30132402550048a008c5011080205c03e2807b100f0601d8803920071100dc601b0803420064200cc40198803210066200cc401908032100642003440184c0309805d4008260104c02098041300b0a0068802a98055300a28011c40221804d40090a0104c020980413008e20110c0209803c50070800d10017a801a2005a4006880169002d200344006880169002d2003440068800d1001c300466008cc0110801f300466006880151802a3004c80070c01198023300442007cc00e1801a2002e6005cc009a000f4001c2002cc005080073000620010c001880003
else
(if j < 2 then
0xd24e1a2dc3423867f50cf0e19cd4336b066670cc0c19620329a864d60c8b018f6031c2863260c56e188a430cc861270c18c181d4300385f970be3017a9c2f1b85db80ba8e1735c2e3385c060b71016c982d4c85a180b3301649c2c63058570afce15ddc2b8b056980ac6c156a42a9b854b80a88e14f2029ab852e70a4ee1481c28cb851270a1c81429027c2850640a04813f5427c284f3509de813ad0273a04d2509c68137d026da04d74080a613494267204c95098c612c4c236884c33097ca1040c25ca84483088a612d142589845440958a12a102522049f509368125d0241284934091e8122d0243a041830904a0fdd023f20451308f4811d90238a846e308b0611b44235184655084061181422da8458308a881144c225b04483088a61101421da843650862a10b8c2139842d108546109cc211a042030836a1060c209a84103081a61021420298400507f6a0fdd01f9a03ce4044660f3901f9a03ee507d480f8a01ef203d9507aa80f48c1e7203ca4078e60f0d01deb03ba3076e60ecd0199103b03075880ea101d2983a230736e0e5d01c9a038e2072060e3881c6101b71071260cc881c3183842030000cc881c0201800066440df4c1bca0373606e060db4c1b41036a306d040d8d41afa0357806a860d4101a6983494068a80d1041a09833d4067280cd141991032f3065680c9d0192183204030000c7100c0001800063440c5901883030f1061860c15c180a02fc505d840bdd4179a02ee505d840b9d4171282de405b0c0b510167302bb4059480b15415fb02bb4056ac0a750158a02ac5054cc0a85414ea02976050880a4d01472828860508809fd413cb02664
else
0x19f6e33d94678a8cec519ccc337dc66c38cd261998c330e465eb0cb761960e32a5c650a0a7e5194a832950650a0c9b61927032358643b0c81618f6c31d5863828c6b518cca3181862d30c537189ac3121462040c3a61865030b5461428c226183aa305d8608b0c0c5180ea2ffe05fc38bf2617d8c2f9205ee40bd391798e2f0e45deb0bb49175722e9945d030b9a6172aa2e3d85c4b0b84516fae2de145b9a8b6e516cd02d8545ae28b56616a2a2d2d85a2b0b4051676a2cce0595c0b229163322c46058538b04615fae2bd9c577b8aea515c322b62456840ac79157d22ae54559b0aaa9154aa2a81454d30a946151ea2a258541b0a7e514f4829cdc536b0721714cec2989452e30a57514a4a2931852330a4061474c28ca051540a2281436e28558507b0a0961404e27edc4fb289f3313dac27a504f1389dc613a72272a44e2309bc81367226bd04d5289a46133ae2659c4c83098a61305025f904bc30972612d8c259984afb895a512a6e2531c4a33094061276a24d1c497309268123d0246184884090791200e23ed447b288ef70dbac23a58470c08db611a702331c462b88be7116ee22c58455388a46113ae2259c4474088951106c21f1c43950869910c3021624427508468107d020e18418b882a71048c206e440a3880c8100901fee43fa387ec80fcae1f79c3eac87cd80f8ce1f0543ddb07b650f60c1ea5c3d22879d70f3281e5143c64078390ef701dd943b83076b50ec521d6643aaa074e70e8d01d09039ea873760e60e1ca20390b871a70e2aa1c3d83843870170df8a1bd98378306ea60dc6e1b75836bb06d160d94e1b11835eb86b580d5ce1a9dc350b06998))
else
(if j < 4 then
0x22aec454948a6310f541e304451d48a290f1f22280a44f8887ea911f22274844d548991912c6225084485c88f9111b41e344445d08892910c621ea84424c881210102220c644090807110fd521f2843d50878a10ee321d2a4391486fa90db421ae8434d086818f1a2219a643214862210bf52172c3a4dc859b10ae52150c3d0d4851a909d6212ec4241c84531083720fca41e5483a2906e620cd0417a082b4104e82090c39894820b901f1207c64078481d9903651c98c40c9081630e5c6204ae40408807110205203e24078480ca901272020440388804a900451ffcc3fda07f830fec41fd443f9cc7f290fdf61fb683f5947e830fcc41f8cc3f0cc7dfa0fb961f66c3ebd071910fa961f46c3e7d07ccb0f9361f1e83e2587c2a0f7f61ef4a3dd907b7b8f6a51ecaa3d7d87ad28f5461e9cc3d2187a1a8f3d6194a83cdd8799a0f2d61dd023c9d8790b0a3a61e3e43c70c78d10f1821e2a63c39c784a8f0361942838c0877f28ef861c6443bd4c77918ef021dd2e3ba0471910e3221dc4c3b71876b30eca3030003b508766b8eca3030003b208761a8e6751d7e83ae9475aa8eaf61d50e3a85c74d38e9371d1ac3a214740b8e7c51ce9039b20733a8e6251cb8c395d472928e4c61c908390d471f28e3951c48638d1471910e3021c54c389cc71218c4851c3ea38694709b8aa551c1e838294701b8dfc71becc37c186f530de461bbea2d8546ec38dd171b94e371186dfa8db961b64e36b186d420da261b38c365986c6c8d8941b06c35f586bbb0d6e91ad0c358986aca0d5d51ab28354d86a5c0d4561a7ce34e18699a8c6b51a5ca34a18690b8d1b61a2ac3439c68430d026
else
(if j < 5 then
0x2e28a5c398b843170262df8c5bd5cb77b16e962dc4e5b718b6ba96d252d9aa5b1d8b62196be62d70c5ac5cb55b16a472d3ea5a694b4b2169062d16a5a158b3fb150952cf6859d1c9ceb166e62ccd059818b2c4165262c96e5911cb1eb963672c60c36a10b153162462c3cc58618b08b960c52c0cc57f646c4a15f762be2c57ad8af2b15e052bb2e574d8ae5495c462b7cc56d646aca15b051ab2856a5cad13959c62b290563d4ac52958462afcc55e18ab9a956d62acec55894aaea955582a9ce55218aa04153a62a63254a9ca91b951d62a2ec543a4a84a8ca14194a832950650a1503629fac53d9ca77b94e8729c8853798a6b414cf72990e53020a5da94b56295ce52928a4dc949382915252028a3c41472628d6e518e0a2e39456628a4851354a22c143c92869050b5ca142942262836e5051ca07314086280104fe5c9f9393e9927c304f7149eab93d052794c4f1549dfb13bb4276ca4ec189d5313a37273ac4e5249c6b9385826fb04dd249b6b9368526c4c4d6dc9ab2934f72692c4d0d899e393366265ee4c9e09903931972626c4c2e0981c12fc725ecc4bbdc974392e1725b4e4b4dc967292c772584a4af5495c292b262556e4a8e094e392966251d04a254941b127d624eb049b9c933b9262524a8c497cc92d2925461c72a49320923a92416247c648e5471ca8c485246a848cc89181922e22450c489109102121b5242ac48450905b1205623fec47ed08fba11f1623d6c479948f030e67523b4c474a08e5b91c56237ec46e5875aa91b36235ac3a85c8d4291a262338c465988c83118971d6aa460d88beb1177622e4a4424c8b6a916a3220c6459548b11915d5
else
0x38f6a71d94df7b1c71538d6c71958e14a9c61438b30714d8e272996443892a65910e21b1c3c7386ea70d0ce0cb1c2e63852a36250e1229c1f51c6443bc8ce0cb1c1273815070118e0111bfc637eae6fbd8df5a1be5637c0a6f6d4deb29bd153796c6f068dddb1bb47375ea6ea1cdd0409f333734c6e4dcdc729b734370ee6e01cdbbc9b73436e686db94db3b9b60736af26d458da719b459367ec6ce1cd98b9b2a73648c6c75cd8a49b0d7360b06bf9cd7ca9af9535e6c6bb94d7430e30235c2e6b714d6ba9ad163596c6b158d5f39ab863566a6ab58d54a1aa363538e6a4e4d4639a84834fae69e14d3c29a72634daa699d8d3129a5c634b0869498d2631a457347ec68e1cd19a9a2d63454668990d10a9a1b634306685108aea9a0e63410c68098cfe319f6633e2a67b14cf3a99e0733b6a67558ca6299d143396c45754ce3a19c16337a866dd8cd8399a973346c667d08a63199b4332ac66414cc62198663300c65f10cbb3196f732d0e65910caf3195861ebec42fd4ca8b994c5328cc65018c9d319346325cc3c0d885fa992772d3ea64894c8f2191773220e64298c82318fe631f2a63d14c77318e7731c0e63698c6aa98cf63190e6305cc5db18b56315ec62a58c522989f52e32a62658c49b188c7310cc387d4c4031878830e6a61b94c34a9863630bac61614c29a984b83088e60f98c1c31830830510607e4c0cb181273013260114bffa97f962fe6c5fb94bf3b97e252fbaa5f614be8417ca62f88c5ef98bdc317af92f4d25e854bcd3979462f1cc5e1a0bc12177c62eecc5dc18bb53176372ebac5d560ba6c174852e82e5cf14b9ba973072e54c5c8dcb8f297195)))
else
(if j < 9 then
(if j < 7 then
0x1c644856540c002156303000854cd0a6b0e5c6428ec8505909e2a13664260c84995095aa12654242a8475108ca21136421e884295082320fd741eb083c15074420e3541b8e8355d0682a0c884184c82f1905aba0ae7414d0827dd04c3a09084112e8209d03eaa076740db28199d030aa05b640ae88141d0271204b34088e8108901f2203684062a80a9d012aa02054036a7cac900a3a00b9401068014d000a1ffc53feae7fcc8ff818e3023fdc47fa18ff0b9fdc516f0a2de14feba9fd253f96e7f194fdf41fba43f68c7ec4cfd539fa643f4667e71cfcc99f9543f2467e354fc3b1f8343ef8e36a10fbba9f7343ede87dad0fb491f6363eb8e7d64cfaaa1f5053e92e7d18c71911f4423e8267ced8f9ab0e3221de463bc8cf98a1f2d43e5647c958f8f38e3021c6047c5dcf8838e3e53e14c7c118f7d29eff53df4a7bd54f7829eec43dd087b910f6f31ed863da4c7b318f6331ec063d76a7ad94f58a9cbd53d58a7a99871ca9ea063d36a788dcf4b29e8e83d0ee79f68f3c29e7853ce4c79aa0f31b9e59a3ca8a7935cf23b1e4163baaa78e9cf1a31e3043c54c788dc96729e1d63ab4c6f814f0b39e1063c16a78194f0031dfc43be9077b98ef431de083bb4c77554ee829dcb53b8ac76fd8edd29db283b58c769d4ccfa1da253b3aa765d8ec839d8b50cfea76158ebf39d7773ae2c72f54eb629d666259ca75818ead31c2953aac8753dce9e31d4873a84c46cd8e9e31d3663a5ee74a1ce9131d1c63a34474518e86b9d0763a04a73f54e7c29cf352d88673b58e73b1ce0739b2e73514e6731cc773984a72f54e5bb1cb343957072958e4fb1c9a53928c72398e4341c806
else
(if j < 8 then
0x499e89c2d93832a6fe84deee9bc1d375326e194db8a9b5d5368b24c344d96c9b19535f426b7717e4c9ac59354c26a184d3129a45d3444a68264cf3299d153373266954cc6c9975932ca265454c9ae99215321aa63e54c6d098c553162a62664c40c986991efaa61374c152980292fbca4cf44bdf0328512f3c25df819428975692e7b25c784b84a96edd2da3a5ae64b4ee968952ce32592a4b132961152bf32574a4ad729591d2af3255684aa0c9525d2a13a53b74a6ac94b61293b251e94a30c943e52843a500849f1093c21267a24e88498689382126cba4d36499e8931e1261a24bb84967092b59253b24a074934c92519245ca482948f8c91d9923742467748c0e916d522a3a4513489c6912552213a43d5486ce90bdd214b24227483aa7bc1520bb24125481e690295202323fe647f488fd911f8323ea647c8c328511efa8a7a447b0e8f45d1e5b23c47477ae8ed9d1d7ba3ac3474cc8e8cd1ceb23985472108e298db9a2384646f908de891b8c9b73446d8a8d9d51b03a358846ac48d3651a42a3426467aa8cdd9198b232b6464ac8c81518bca30f84610e8c02117bca2f5245dce8bb09172ba2df645af08b3e1163c22c254578c4575515aba2ad84550a8a82114cba2945451908a19914032279744e4e89add131c225c744a908935d1233a23d9446ce88c55115b222744440e88788fd89a2177408447e991107c220a54406e87f950fcaa1f4543dae87a14bf1297e2543c6a877950ebba1d07439a67d64d0e4a21c36437ca86e550d93a1ac6434cc868190d0311e654332e7fcc8fa31a19181d02e862d90c492183642fac85dd90b92a16e442d48859190af30ef02
else
0x1ab28b0c906aca2c2c64b4eeb092160eb997c45830ab045d604c2c04557feaafe595fa2abec857c90af75d5eb38de4657a48af2dd5e5babc1a577c6407c55dbbabae95750cae8d55cdc2b983571f2ae21d17a92b82656f50adca15b542b63756b8ea06155ac22b5265698cad0e55902ab3a94ea4836a11597dab2c3564aeac815471aab1c4562ccac419583cab02555f32abc25572da74041b128ab6ad56b22ad24559aaab161560a0d594556f4aac595553a8e3555432aa625547caa89655030a9e9d53a32a6aa54ce6a976940c2aa54954972a90a551e32a3935466ca8b59512c2a22354404a869950942a0f31a66aa82d15032aa00653f6a7da494fa3a9ed753ceca78594ef1a9d6853a0ca734d4e24a9bc8536aea6c154d6229a8453410a665d4ca2a98d7530cea60194be22977552e2ca5b154b5129619369c6a5660f959295185296ca51d149f4a9359525b06545cca03101e11de0464e98781b292a3524c8a2b114912291e45232aa451548642906651feea38d547b4a8ed951d0aa3a15471aa8dc751a90a335d4633a84a75086ea3054f95928b985161264d19456228ac451472a275944ac288e75110ca1fa943d9a871a5030aa1a2542fca858750a2ea129d421ba83e5506eea0c95415ba8256503b0a0615408ba80a73e564a01193feba7f67203e238c88c97327ed94fd289f8d93ef2a7c854f86a9f6193e9aa7cd64f90a9f2153e1aa7c354f7e89eed13dba27b1615d4a2ae553d44a7a084f32e907553c9b278c74f0cc9e0193bdaa77564edce970953b4aa76364eb8e9d5993a9224cf44e98c9d1213a02273b54e6ca9cc19393ca72254e3c83565138bba7116))
else
(if j < 11 then
(if j < 10 then
0x62f8ac5d218b7aa172562d2cc58d98afa315a562ae6c53e18a43b14266276ec4d1cf959312c8624eac485988c4999b46224cc42a0cc62198663300c9d491267a3104661fccc3ddd879a30ed661cb0c379d86d230d5561a0ac3299863230c156178a3f6d185bab0b1661530a0c95851b309d6612ecc1c51838a3091661130c211583e43075760e28c1a618313b05e460ad0c13dd8234b03d960692c0ae5812b301d8602cec041980532cfd46006ec00dd7fd4aff465fdeabf9e17ef4afd775fa2cbf2617e0c2fbb65f6e8bec957d5bafa655604abe8917ceaaf9945f230be2257c042f7795edf0bdad17b14af5c65eaaebd3d97a4b2f4365e770a0f95799c283255e570bc8e178cd2f1635e1b2bc16177ec2ef495de08bbad57723aedf55db4abb555767b2eca55d850baf1975a42eae65d50c7cac9750bae9a75d28cba398ff992e8685cfee65f1173d2ae7464e808b9bd57352ae6645cc2ab9660cbe22e5635ca0cb91e5720399644203e238c88caf32e3a64e8089ced571aaae3055c54cb895570e4ae1575c1b0b819d6ffbadf875be10b7a216f0badd985ba30b72d96e1c2dbd65b6ecb6c596d5b2da565b3b0b65d8cbe22d9165b18ab61d56c12ad7c65aeccb5c196b622d6755ac4ab57916af22d5685a9d065f116a4aad4365a7e8b4ed169b2ad3155a58ab499968fbad1695a20cb2091685aad0655a02ab3f5164d22cf5859decb3a95671bacdd659aceb3455665b2cc7459868b2ee165ba2cb255956eb291d64d22c9e659348b25556482ac1855916ab20916432ac82458f509921563aaac6d858cecb1894cb222c5e432c88b1655628c2c4a732f88b111961faac369
else
0x6d9ccdb219b62236bf56d786dad21b56bb6a766d40eda65db4a2b68f56d0d2da019b3dab67656ce2ad9ad9b32b16d756cbecd95a5b283364b5333e8d9195b20ab63b66c6cad8bddb134b62156c36cd851db06bb60766c04ad7f19afa435ee66bceed7859aed3b5d466b9ead7295ae2ab5bf66b74ad6d19ad730cf656b50cd67e47312a17256b34ad6519ac7ab58961cc4ad60d9abeb0cf653aac8d5d9dab74356776ac2cd56d9aab2b55156a98ad51d5a9fc353a56a6aad4c15a94b99f6633a28d48d9a8dc19c743382c66f51a8c1b51266a132d409da7e3199f469ecc42fd5a77bb2b5569d2cd389da6e334d6669a2ad32d9a623b38e5697ead2e59a593b4ac6694cc933d1a503349b569270d231da42bb47f668ed2d1c55a362b466649868d1819a2dab45386898e60f99a233343e8686d0d0b65a133b4206682f2d0495a063340664cb28d00559fd3b3f5567e0acfad59f1c33dd667aeccf4599e44b3bf967786cee4d9da2b3ad76750ace85d9cdb33938671cace1dd9c03b37b566eaccdae99b14b35b766aaccd39d9a43334086674ccccdd9963b3257663eccc5a5987bb30876602ecbed997a3b2ef565d4acb91996fab2d9665a6ccb359963b32c16650cacae9d95aaa10a565628caad99541b2a35653acca5d9948b328b619428ca194b3da327f764f0ea3a159393326d564cecc1c51838a3261664b30c94619244b23f964768c8e0d9193322e4644d0c87a190caaad646428ac83d59052b202863f6ec7ce18f63b1e666178ac78198ec428e8551d0ac73e57d32ab02563968c71958e1231ba863632c6a618d0c31989598e89fa518c84199b46314c9d4918c3231815)
else
(if j < 12 then
0x782cc9d491e0923c0d57810af0021dfc43bf1777d6cef295df2b31d8877bceef691dea33bcf5618c8ef295de2a92204777eceede1dd8b3bac5774ccee819dcd3305e460bc8ee4a1dc543b83776fcaedda1db7bb05e460bc8ed9e1db03bb579769d2ed219d9fcbb369765d0ec9ddd90b3b1b672e48ec51dd8a3bb0b9760acec015d7c43aef975d0eeb899d6d43ad287598cbedd1d63abac0775710eac5dd553baa377538eea521d4733a88675010e9e5ccdea3a74574dcce9a19d3132740474baae9615d2a23a4f5748f0e8fe1d1da3a3297458ce895dd0ec3a1677420ce8299d0232f3b873fcc66f51cfc339f3573dace79d9cf0b39dc55ad88e75d5ce9a39d3473970e70e0cdea39be57370ce6d11cd7ab9ab4734cae6855ccdb3994773172e6159cc02ac82472f6ae5d95cb92392a472d50e5919cafab958772a4ce52ddca32b9406337a8e4ed5c9a3b92a4725cce4a91c92ab92057236a66f51c8dab9147721cce4219c8131d8b571faae3dd9c792b8ec671ccce3855c6cc38d187196ce3159c5f3b8b867164ce2b19c52bb89f67134ae2519becb171e571172e20e1c3f2b879570e8ae1b997652b866870c0ce1621c293384c6708eae1095c1d433f55706aae0b61c142b82267038c34cd5c09cb80b8700acdffd9bfcb107956fe6cdfb58699a91e656fcce7fcc9befba18366fb2cdf49dbe6337c666f80cdeed5bdab37b056eaaadea99bd1bb79d66f2ecde45871cab78986f08addf21bba4376f56ec96dd7d5bad2b75556e9b0dd215b9edb73856e64cdcaddb923b71e66e30cdc499b863370486c42ad86d9b7f336f771cc4adbc59abeb36eb66dc8edb799b6cab6d45
else
0x1f46a3e8d4803cb005de0083c00a68006efff59ffac3fed87fcceff7ddfecb3fd277f98cff1d5fe03bfb797f64afeaddfd1c305e47f3cafe4edfc63bf8757f068fdf59fbc2be8d47ee4cfdb55f46a115d57ed0afd899fad43f52824a8cfd2dccc82bf4567e7b0fcd61f973bf2597e3b0fc561f873bf0777e02cfbe9df7a33eeb97dccafb7ddf6d2bed377d970c1c51f632bebbb7d6acfabd9f54b3ea367d38efa351f4c9be9187d1a849519f451be8287cf6ef9d1df3733e6c23320a7a595f3243e5d77cb6438e55f2b29e7857c9b2f919df1f43e3777c62cf8ad9aa8abe2567c3ecf8659f0a2b54c57c1ccf8219f01abdfd67bf0af7c99aa3abdec67bcea37919eef4bdd777ba2cf729dee1bbdbd67b6b0f6b61ed2c3d9d87b2ecce395ec83bd8977b06cf5ee1eb9c3d6b87ac70f571deab3338e54b84af53a1ea343d3e87a70cf4c5d2e12bd2a77a48cf4721e8a43d0c87a090f3f21e7b33cef779cf0f381de6cbbcd54799ecf321de60bbcba7796aaf2c15e54bbca45793eaf2659e49b3c8d65640af2215e4133c65660bc8c1791e3d43c72878dc8f1acde32b3c5c978a72f13d1e23c3c3f87874aab591e1aabc3057856af08e1e0e399d14))))

private def cutHead328 (i : Nat) : Nat :=
  let j := i/256
  let w := cutHead328Slab0 j
  (w >>> (19*(i % 256))) &&& 524287
private def cutWord328Slab0 (j : Nat) : Nat :=
(if j < 16 then
(if j < 8 then
(if j < 4 then
(if j < 2 then
(if j < 1 then
0xd12b42ac52b12a95a31628b3edde2b2ad95b728aca2b6ee95954eed3b75e7ca2b7ad95b73e515b77a795bd6e295bd6e795af7adc52b5cacab35ecdbbb3e5159578ade9456515bc5655e9f28add2b2ab5dad5ef4f9456ed7956e2ca9f6cacaaf6e2cfb75eecaae5655caf72ede9e56557b77aecfad72b4ab316e598a569d9a72a9c5ad4e2958b2a5455ea8abb5ea8aaf4edd51576a8aaf76a8aaf7add53b66dd5155ea97955eecaaf5af551554bdb956ebdd9576e5eaa2a555372aa9eb75455eb754dd5372addeaa5455e9554dde9554bdbbb7ab56b92acdcb3549d9954eb53aa
else
0x2acd9e22bcf0b3e6df115c4569d366569c5e6571732b179b32b4d9e12a57153ad4f161a75f995c515bc5c38bb612b17b612a571618b5f115c3db115ac57b152b88af66e57133c4dfb622a57156ad4cae28b5abf6c454ac5c4de2e22b89be1af8a2e16f8b0c5c4df0c5c5869d7c58b0956f89bd7c38b0f62b88ac5edd7115ae571748adebf4edd4ae22adf1622adfb572b89bd7c5d3b372b8b115c4deb15af8ab15c55fab7afdb137af9f9f6ebd2b622b859e1a6cf0e24f9e7af8ba96ed9ebe2ea5f9f5455fb73cfd517462d0aa54ad0ab12ad12b14ac4ab462d0aa52ac52b42a)
else
(if j < 3 then
0xf36ddeaa6cddeae7e6cea77e79db77a9de1b2e5deaf3e79bbb7abcf3b6a9ddbf3cf52af3cddca776fcf3d52955bd5cd9aae7aadf39586dbbd586dea66cf9dbc2ef54a77ab9d395cf53be6ab0bbb7aa9b3d4eede177aa9d3e6ef0dbd4aadeaf2e5579d56fccac36ddeac36f53972cd56ac2e7cdbc2ef54a77abcd995e753bf2ab0bbb7ab0bbd566cd395ab0d973a9ddbb3e5de1b7a9df3b78555be6ef561772b9dbd5859ea77869eab785cea7786ceab7879bbb7ab0bbb7e79ea7386cb9c3a22e12b17b732b873b7c5179e22a9f9e1ec9dbe7c457b732a9f3f3ecdcaf32b8a2e2
else
0xe97be76d57be76d517e792b876bdd117ce82ab7ce1f8b5eedd057e792ab76fcf2f4af92ba22fcc2562fcc254ae88b8741572e7415f2e7cbdd0570e82b66cb92b662f92ba3c958be5c95b2e70952ba2cdcb3a22d9bbe7415c2f62e1d177415c3f3415b857e15d057e3d2ba1ce87bf0ae82ba2e5cb257445b977e15d0562e87b17461f8574158bf3ae82b74ae8e915edde9f3a95d055ee8d055efcba5743dbba3a7c7a574682ba1e95bb7345c2ba2ef57b77e682ba34612af70ddd1170bdd1862e87b862e8c366ee87ba1eddc3a1edddbd7e79b9d2e6894ab9f9776f573a7a9df3))
else
(if j < 6 then
(if j < 5 then
0xed7b56aedf2f2abdf3b2ad57ab76557be7655f2f7655f3b5ed5dab5e55aaf2aecab55eedaaf7cecaaf76f9a957cbddb55ed55955ead29556d5dbe2abddb562555b55ef9aab56f97bb6abd73e2aedd3e2af97b576557bb7c55daf7c55dbe5ed5f2e5e55aaf2af8ab55ef9aaf76f8abe74ecab57655f156aedf1576bdf355ed572f2abd7252ab9abe76557be6aed7b57c55db55ce97ae56edabe5cad2b576f97b52a55aaf68557355eb9daf7cd57b576f8aaf2af9db576d5d3b2aedd2f6ae973b74acab57cc4aba6af97b57ce95b55ef8ab576eda956855d3576bdabb74b9aaf76
else
0xf8fe777d93f55fbde5ff7b7f353fbdf3cf7bfabe5e7fdf55ffbb334ffaffbb5d57fe767ff7beaf9dafea7fdfebfd99b577fb3effcd5f5ff6ecd7e5fefa9ffd7ff357dbfdbb5eabf1ff7bfabeb7bff3b3ffba9ad77ff3b5ffbaaaf67f3f666fba9afceddf57dbff3b3feff753ff9daff7fba9fdff9db9fdd57fb6aeeffe7ced7febfefa9abfedabbdff9f2f767ff6ff7d555ff7bfdbe6a6af6ff6f8ffbea6b7fbbfedf3555baffb7cbfdf555f8fe7e6d9df5777f7fe76e3a9fdfedf3cf7d5f3b3fbfabbfdf9f9fdfeff753fbfbfbfbfdf7b7cbcabe76bcabe5eedabb5ef9a957c)
else
(if j < 7 then
0xeff2feaf977beabeffe4fefb1fea7fe6ffcefa9ff9bfdddfcd57fe79eeff57cbfdf57d7fdfe6afafef5ef9defbfd5f7e5eefabebfd93bbfdd4fe7dff97bbbfd5f67fcbddf53fbff5fecbddfeea9effe6afbdef477fb2777d5f67bdf97bbdffbabe5eeefeffdd5dfe7dbda9fdbeff5fded5dedfcbdf5feaefaaddefbdedeafb79fbff97bbdbfbab9deef6feeae6ffe5eef7feeab779feaf9def6abeffe3ff8f6f77bff757c7b7bbfd7faafdbbddf57c7f7b55feff2f6ccdabef79f57e5eed6fbdffbabe76ab79ffdd5defbfbfdfe5e7baa7f7bcff66aef7be3fd57be3defaafbf
else
0xbfabbbffb9a7eceeffeeabfe5ff75df753ebeffbfcfba9f5f7cefbbafbabe5f7cefbba7ff753aef7be6abff5dbdbff3bbbfbaa7f777f753bf9deffdd5df55f77f7e77bff5fea6bceffcefabef3d5dddfde77fe77faff577d57fe77d4feffcbd7fe5deeffeeabbf2f7e7fdf55ffbf2f5deff6fea7ed6feaeff1adfd4ffbfcfcbdff7d5fafecccbdffdefa9afcedf9fdfd5dfebb7fdf57cecedff7fbabe766b7feeaeefdddfd5f1df7bfabe3bef7dffcd5e7e3fbfdfeea77f3cdfeeffeeaf9e6ff7faff57e5d7dd77f8faff7f9a9f5f7fdfe5dd4f7f5def3fe6afcfeefcefaafbd)))
else
(if j < 12 then
(if j < 10 then
(if j < 9 then
0x9bdf53fd8ffbea9fb3e6d7f3fbecd57fbfc7fe757977f1edfeeff53feff2ff9d5e6dfcbaffbdfd4ffe3bbfdfceabfdddf9f8ff53fef6fcfcbfabcbfbff3bf1d57fbf9f8ff57cf2f6ff77fa9fdff9e7bea7ff3beabff5f3ef9defeafaffe5e7ddf53fbff67f77ff5f3df9df57dbf3dff7d9f753efd3df2ff9dd73ffbabf2eef3b67dbfa97bdfd7fe2feff757e5d7be77d57feaf9ffaebf5ddf55ffafaf7e7bdf53ebff5776bff3577fabd75feeafeaffcbaff756bfe7e7bf2ff7d5f76777fabecffd7dabf5dabbfd7cfeffcd5dfebef8faff7faff535edfafea6afbbfdf9d9abe
else
0xd8d7bbfd57fe777baa7bdd5dfe3dbeff537e3a9af1bff1af77fabbbdd4feffcbf77e5e7bfbbbfd5f2f5d7bfbbdfd4fefbfefa9afcedf3f777f7daea7bdbe7ebed7bea7fa9edff8d753deff3bdf7affe6af8f7cdfeeff57ef97fbbd7fabf7ceeff55df97dff7d476ebdf9dff5f7fabe5c7faaff7bba9ffceff3f5d7fab64def3dfeaeff2ebf9fabe5dd5ddfdffd7dffcd556ebff9fbbeaaafe3ec9bde7eaf977bbdbfabbfcbafefea7f73bddd4ff8fcbbdefeaef76fea7ff1ffc7b77f77bfabe3dbbfbbbfd57dfdfefaaafcedf3f777f7eaeabbdbe7e7fdefeaabfbe3fef76fea)
else
(if j < 11 then
0x7ed757eeff5feabfd3f7def7dfd5d5ddfcfd5d1bfcedfafb5fba9fd7f9dbf3ffb7f555f9d9ddf6bdfeeaf9d9abbbfdfebfd5f3b55b6ffbfdbfabbbfbfaba3fbfdfef4d5f3b75fcfeffdefabbdf7fabe5feeff57c6b7fbbfd5f2bbfbfdf57cef7dffcd571ff7bff35747f7fbfcd4feff7f9a9fdfefe3cf87f7fbfcd57fbabfaff57dbfdfc3fd5deffd7fabc3feff6fea7fdeffdd5a9fdfefe3c77bff5feafafeff7f1abc3fbff7beae2feffdefabe3ff2eeff7fbabcbbf97fbfd7fabcdbf8ffbfdbfabe797f7fbfdd5fbe77bfa9ef7f9f9edfd5df63d7f3f53dbff3f77d4d72cf
else
0xf9faffdefa9fdcfaffbdfd4d7f77bff5feabdf2ef7fdf753fd93a6f79ff5feaf97bf7dbfdeeea7ffaffd7fabbdcd93a3f77f3fed5d4ffbdffb7357cbd578bfbff7beaf97aefe7fdfedfd5ddfea9ff1acf7fdf57c8effbea9ff3bcf7ff354f7fdfe5cd5d1fcfeff353f9fdfe6af9b5fcfefab64feeff56c7fde7ead8fe7f7d5b3e6dfafe7f7d9aa7f7d4ff65fd4ffbfcb6feff7d5f2fbfd5dfe5c7f7f577f9e1fdff9df53fbfabbfc7f7fb6ae9dbaf47f7fbeaf9b33359ff7bbfd5b33355f7febfefabe76fdf6ff77fa9aeccd55ffdefaa7feeff6fea7fd3ef77faafb5fdf7bdf))
else
(if j < 14 then
(if j < 13 then
0xeff6fbfd4ffbfdd56dff7bff35777ff2deabeffbfcb7aadfc7fdeffdd5f39dfeff5feaf9cefbfd5c7e737f7f571e36eafc7f7fbfdd57dbf3faff55fe6efef7d57ddf7fbcdfea7f6f9fdbfdf55f7fc753fbfab8f17ff2ff3d5cfe3fbff7bf1d56fbdf7fabe71bfddfeaf972ff7d4ffe74bfdf53ff9f2ff7f0ff55fefa9ffcbfddffcd57fbeaf8f9edfeeff57cfddfebfd57fe3deffbeeabffaffd7fabbdfeff5feaf8d78dffbddfeaf8f6ff7d4fbe3dfd7fbfd7fabbcfd4ff677d57dffce2feff7d5f3bbfd57fe747fdf55ff9e1ff7f97f53fef7f57c7f7bbeab97aedc7fdefea
else
0xbff5fead93fbfd7fab677fb7f52fd93fef7d4bdfcfeff752f9fdf52fd8bfe5feeffeeaf9df57ebff57fcbfabf77fabeff7d5f7f2fef7f57c5ffaff7d5f17fcfd7fbfd7fab63feff754ffd7f535fd7fbbfd5f1ffdbff35356bf2ffed4ddbfcfd7febfefa9afe7faaafe7f7fbeaf97febff9aaad5f8fff6aaf5fe7e7ff6ff7d55764fcaff566d8fe7eacb9a3bfcbab33f9fab2e57fb23eacd9b63f9fdfee5d5f3bdffba9dbd77f2ff7fbabe5feff753bbfdfeea777fbfc77a9fdfeff1dea77f2ff77ff757ceff5feab73fbdbfaff55bf9deffd7fabe3feff755bb7dddfdbfa9ddb)
else
(if j < 15 then
0xfbaafbbeff5fea7fabbdfefabeeae2fedf7fb7f55fbef78f77fa9fdde3defeae2feff7fba9beab7dcffd777f51f7fa9eea77f7bdfd53dbf7d4dfedfefabef7beff55eb7f5ff7d56ef3ffbdefeabd6fef7beff573ecfeffdefabb73bff7bbfd57fef75da9f5ffbdf53ebcebef7777f57d77defeabd6ddfdeefefeaedcdddffaffbea777fef7d5f7bbfb7a9ddbfbdefea77f7bdbd56fef7bfabef7bf6dfea9eefeea77deffdd5dddfdbfabbfdbeff535bfdfeeaefab577777fbb7fbab55bef7f577bff7bbfd4feff7fbabf7dbfddfea3baafbff97fbcf7ff3f7defaafbff9f3f77
else
0x9fab9f6b6ffef7bfa9ffdef7edeaef7deead476eea7aecff776f7edfd57fbbdd5c5eea6ed6fbd6fdfeeabfdf53d7bdeffd7fa95cffb8fbabfaf55f79ff753def3febfd4eedfdd5dedfdbeff53dbfdfebfd5ddfddd5de7ddfaff55deff6fbfd4ffbddd4feed7eff753fefaaedd7fdeffdd5365fd7faa5abd5f66abeff67ea7f2d5cdd5f66f7fb3f54d7fdfecfd5defbbfbabbbbfb7dfeaeef6edf7faaebfeff6fea7ff6ff7d4d6ff7faff53defc75376afeff1d577bf1d55eadfe2dfebfd4ff8d7bff752bfb8d5fdeead5f7caafbe5573fef7d4ff2cffbdf5657f3fef7d57fbbb))))
else
(if j < 24 then
(if j < 20 then
(if j < 18 then
(if j < 17 then
0xef3f5479fddd77fb3dd4ffbddd4f57dd5fd9fdf54b571f5778ff7bcfd5367fd75de7fd753fbfd753d5fdeeafeabef3feea9ff7bea7f3fef7d57feabeeff577bff793fd5f6ff77fab93ffbdefead4feffde5cbedfeeff5777f7fef2d5d9bf3bff5feae4feff7fbabb737f7fef7d5f7bdf77aaffdeeef57dbeefbeafaefbdf7faaf3fb6efef7bfaadde77f7bdf7fabb3fe6eeffdefab9f6777fef77faaffdeeedfeab6efef7beff557efaaeeafbf7bdb7fa9ddbefabedbef7dfea776fef77f7f54bfbddfeaeff55cbfbdf52bfbde7ea7f6a3f79bf55fdef2f57def3f55a7f2fef7
else
0xd4ffeeaaeffed7d55dffdef7f53aeff5fdfd5aaffdeee9fdfeff5d6a757febfefa9dae757fef7d4f9ddffbddd6a7ceaff77ff753bbff7bbfd57fbfdb4ff55eb7f7bbfd4afef7beff54f7ff7bdab5f7bdf7faafbfeff755ab4ffedfefaad3fef7feeabd6dffdef7f537fb7fbbfd55dffdbfdf53fbff7bbad4feffdefabbfd7faa7c76fdfef77faa7cd7bf7ef77f3f537fb3fbbfd51e5f77faa3bffbde7ea57dfeea9edfbabfbdf54f7bf63abef3f1cffbddd2b9fddbabfb3fbea96af5778eafef79fa9fcf57355fd9f955fdefa67f7fae95cffbddfea8eafbcb57f7bfdd53d5fd)
else
(if j < 19 then
0xfb79beafb7b34f7faaf766ff755f7fd9fcefb9a7eaed79bfdbfdf576bdf5fdfefabef6ef7b53fb7f7bbfbdabedbed7bbbfd56ef3fd5dbef6bcff57dd56ef77fb6f55eeefdfdeedf6df7d57dfdbe7f6f76d4fef76e7f6fea7fdb577fb7a6bfcd3beeaef3eddefbabb3fbdaaffdede6f7db7df5797f7bb7dbfdf55eecffeeabfdfb7e7f7fef7d5ddb9fbfabb97d55dbdfefa8ff7fb7dfeab6efb9ffb7dfeafaf4fdfd47fef7beff57d3baaebdbff757dbedf56a2f5f5376e7ddfd6fdefeabff7537bff5beae2d5eea6edeffdeeff57d7f5f54ffb5fbbfd55fef7beff57d6f5efbf
else
0xbeffb7defa9f3abeefebed5dfb5f76fbeba7fdf53afb7bb6abfdddb7fbdafea6f7fb7d77df54ffadfbea6fdbedfefabeeabeefbf6fb7fbbfd4eefeaecefedfd5d9dfdbeffb6a7fceff6fba9fdfe7f5df6d57fb73faff57ebed5faed5f7bbe7f7fb6afbddf767d7fef77fa9afcfd7daea7df7bf6f8d5f5fd5f5ff7d93f37d7fdf535bfabef66b7f53ffbd9af9bfdbeeaefe757d77dfcdfedf7bbfd5daffdd5ddffdedabbbfbd7bb7dbeff577ed7beeaeefe766fbdf53f9f7fb5efaff5779f7bb7dd4feff77f9af7defaa7fdbdaafbfecffb37bdf6ff7d5d9bdefbddfeabefeff6))
else
(if j < 22 then
(if j < 21 then
0xeff755f77f7bf97fa9fdbf3deffdd5cdfdfedc7eea7bc7535bfe5ef77fabcf67f7fbfde3a9ff6fbaaff77cfbb7dbfabbbfed79f7dd4feff79ff5ff77cdfb7dd5defcf7f9bef7d4fbf4f7cbfb7d7ebbbeafcbbececddefea5edff5fecbfef7d5f975eedf755feebe7feaefd76afb7fbbebdf9bfd7daaff75d7feabeebff2e5f7feabecbbe5fedabef75ff9bf6bff7577cdf5feaef3feeabfdbeea7f7fb5ebfdabfd7fdf557ed7bf3ffbaaff7ed7abfdef7f53ffcbafbafbd9f5ffbdb53ebeffb7dafa9bfeaff7b4fd5f9fd7edf755fed5feeabeffb4ffb99feabfcdffd5ddf53e
else
0xfba9afe7f7feeaed7fbbfedaaacd7ff754fed57b3ffdaaedf7fdb555aeffb7efbaaadd7f7feeaed77b7e7fdeffdd55734fcaff56cccff2cfd5b334e9bf5fcfef5754d7f97566cb3f335faff53f9b9a3fd9fab2bfcd3756cd999fcffbdf2ea9fabebfcd7f53ffbdafbffba9af67f7feeaabdadbfbff7576beff57ded59fdfd5f7b727f7fb7dd4fefeafbd9fdff9aba7cebd1fdffbabb76f37fef77fab8dffaff576ecd78dfeff5feae2feffdd5dbb5eabc5fdfeff7571bfd9afd7fa9ff1ed5fedfd5dbcdf7fab8f6f2fefeae3c6adbecfeffdefa9fdffbdb5717fdaff9d57fcbb)
else
(if j < 23 then
0xeff753b77daffd7fdf576fbddfeab73fedbeeff55bedf6ff77faadfdbeff5767ff7beab6ffedfedabebfed6f55f7ff7b5bd53dbeaedf5bdf7faadfd77defea776fef7beff5767fdfeeab76fb3ffb7fbeafb7dfeaed7febfd5db537bfdbedf6effb6afb7dff6d559ffdbfdb5747f7fef6d4feffde5cf93fbff7b6abfdbebfe7ab9bbecdeffd7fa9ff6fb7f9eae76fb577ff6feabff79f67fabb736f7febfd4ffb3bbff79eabff5df3ecff53ffb6f9f6bfa9fdfedcfeeafd7febfd5d9ff7bfdb5356b3dffdd5d9af6bffb53d6f7fb7efba9ab5d4dfef66b7febfd5d9ef6fd7fbbf
else
0xd53dffded5b5747f3fef6d4fe7fdedabb677f3feeacd3febfd599ffd9fab33f9ff7566ed9fbbf9ff736afddbedfd4dfef6fcdefeacdf5bbf9fabeb7d4feff6bf5fb5e6ffbebfd5daf576ffbedfd4feff6fadf57eed7feb77fabf76faff557ed7dffdd45ebb7edf7f5f7fabb567faaffdafa9ff6fbdbf577fab347fb3dfeaedf6bbf9fabb57d5f5fdffdf6bdfd4ffb3fecdebfefb7f5766f5ff7d7faafbfadf6beafdd9ffdaf7f547fba9fe67ff754fcddb3bf9ff736aedf6ff7d4edbbbed7fef7d57fef7d4eeffd7fdb55ffbd9dea7f7fef677abb57fadefeaedf6bbfbfabb5f)))
else
(if j < 28 then
(if j < 26 then
(if j < 25 then
0xd4be7fdd4bf34ffba9fe6cd3fbfdd4bd7f6bff5ff7d5db57dfd7fbafbfabef7fcbfedfd5d97febff75765fdafeafdf7bafedfaffdeeff5667ff7bea9f5affdd4ffb76bff793fd5d2ffdd4ffb5ffba9ff6bff75767cdeffd7fabb7efbddfeabfd9bfdfddf55fecdeffdd4fbf5feeff57decdff5ffbddfeafb3f53fcdf755f7fdbebfd57fb727ff7b5fd5d1ffdd57fb3ffb7f5767f7beeaad7abd67ff6feaedfaff7fba9fd6eeffedfd4d7f7dbfddfeabddabfdfddf53fcd3a3fd9fddfeaed7bf77bff6bea7efeff7fb5b57ebfddfeafb5bb5eaff9ffdef7f57d7faa7f6fb3dff6
else
0xeeffeea5f3fef77fabbfd7faa73ffbdf54e7fdfeea9d7a73ffbde7eafbde7afd53fef75eff57d9edf52ffadfbcfd53feb7d4de7fdeeff57d7faa3cefb1fbbfd4be3fd7fde7ea8ff57f77f3f57d6f1dfcfd4ffeea8fde7bdd5dd7bdfb3f577fafe7ea9fddeea9ef5bf7fba9ecfeff5feaeeff54def3a6fd7fa97cdeeffecfd537baffafe7ea7fdf54d7f363f7fbabbbd9afe7ea6b3d7fdeeff53ffbde7ea7bdf2ea6ed67e56effeea7f963cffbaa7e57affbea7f966cfefabf77bff5fea2f7fecf7fdb55f7fdbf77fbaafbfeddbf7dbfddfeacd3fef77fab37def7f52f7f3fef7)
else
(if j < 27 then
0xd4fdbfdd5def37fbabbbfbdf5fceefabeceeeff54f7f7bef7777f53bfbdef6a77f7beabcefef77faaf5b777bef7d4feddefbdf53fb7f7bbbbdaaf7def6dfeafafef77d4def7def7f577d57ddfdbddefbfd5fbbbfbbabebefd75ff75dabedf7cfef77d5f6fbe7f77f777d7beea7d7bbfdbfa9fbdefabede7bdf57d7f7bbbf9df75779df5fea9fddfdefba9ddeeff6feafbaafbbef7bedf7faaf77fbaafbfbdf9ff7fb7f54eeff67bfd4bcff7fafe7ea8ebcff7d47fbfd9eff517efaa3b7efaa6af3ff751ffbde7bfd477eea9af7eea5ddfebf9fa974ffaffbea9fdfeae7fa974f
else
0xbdf5feabde7bdffaff5717fdfeeabddbed5bd7bbdf7fabcbfeff6f6a7fdeff9d5c5fdef3a9ff7bde755e7f7fbeaf3e79dee2feff7fb57577f2eeffdd5dfcbbbff5feabddedf9d4ffbf9b77beeaf3cdff1bfdfeeaefe5edf7faaf797fdeffdd5dfeded4faf1feff57cfd57dff6fbabb9faeddf9ffba8bf7fddfeea3f7bbfd3fa9fdb77dfe9fd57dffcefabe9fbaf5ff73fa8efdfd7fbbffb7b55fef3dffebf7bef75f3f52eeff55df5ff972feff55defcbbbfd7579f7e7f7bbfdd57ef7deefe7eafdf5fd7d5ddf7eaeffeaed5defbe7f7beeaef7df3faffbebebddf53ebdf7bdf))
else
(if j < 30 then
(if j < 29 then
0xbfcf5717f7b9ea7ff6f73d5f79b7beff573faeeff7d5f79bbbfddfea7ff79dbbddf55efb6f9eabcfeffdd5cef737ff6ff7d5fbbdfd4f7bfd7faaf3fbfdf55e7afdefe3efe7f77b7bf7dd4f7bbffbaaf77bdf67bfd4f5deafb79ef7faff55eef7adfd7fa9edefdddfdffba9ef7d4ffedeeff753f9ddf57d7f7bbbfd5f6f567fdf57dbd69ff7bdf757cef56f7cbb71ff7fbaaf4def3bebfd53bbbfd5372bf9baa74e7f37bead939fcfeff66ead4ffeafefdefea7f7bbcffba9ff7fbaaf5ebeff555d4ffebbef55ff7fbaaf3fbd6eaf7fbaaf7e7f7fbfdd557cf7faff55e777a7f7
else
0x7edff1f7f3feb7bdfbbea6ff5ff7d57bedeef3dfea6f7bf7d7f7fbea6ff753fef7bef7d4fe77dd5ddfdefaff577bd69ffdbddf55c7ff7577bcffef7d57bb57acffef7d57a3fd9dddfea9df5fea8f95fc7d539ffdd51e74e7f1feeacd39fcffbde3eaeff6fea76ffef7bcef53f777bef7bfa9ddefbddfdfd4efef77f7b53777abbde6ff7bbfd57ab3ffbdef6ab8ffbfdbda9ffdef6adda7ff7bded4eef5bfbddfeafbdedde7fabef7bd6dfeafb7adf77fa9fde77f7bdbd5f7bbbb779fea7ff7bdeb7ab9fdeeff55e6f7a7fdbdddfeabdcfedfeeff55efb7dfeae6ffef7bda9ffd)
else
(if j < 31 then
0xd57fbbff3abbbfbfabcdfeeff579fb7ddeabeef579eeefceabfdfcbbfbabcdfeff5feafd7fbfd7faab77fba9fdebddfeda7faae77fba9fdeeff753fbddfeeabcf8b9dd578fdeeff753efdf6fbfd5dff77beff57dbc5ceea3f3bbfdd47ef2f9ddfe9f7fa9feafb7bf773f79b9ffb5f5177fdff5eeff751fbc7fbfd7faaf5b77dfe9f7fa9ff7d57bf7d3f79ef73f7751d7ff7f173b7b51f9f7bbfdfcff54efbde7bfd4ffbfd9fa97afbdf7bbfbfabbeafb7ff2ffdf57f7fddfeeabcbef7eeff6fbfd5ddffdbd5b55e9effef7d539ffdef7a7eafdf6fea6ff7bbfd579fdffbaaf37
else
0x7d7feeabafbbdf7ff756a77f5dea76f9ef777f6feabbdff5f7ff75775ff67eaeefe7ead93dff7d5b367d7f3fbbdd5def357d7df35fddf55ffafef77fd7daeaeff7f5fefa9f357d3dff7fbabf775fabbbfd5f9adf5fdfeeaeff97dfeefdf5feffafeaeff57b5bfabbfdfcffbea9ff9f5feff5feafcfefea6baaffe6bfb55f6ad7ed7fdf67cfaed6ffefad7557fdf5fdfeefdf776afb55f7df7bea6afaff77ff757777ab57deed5f35beefbfdd57febfefaadbfef7f535ef77f779f3eeb5bffbbf7afaaeb5fcfdaddd5fbbbfbffaff77ff753577e6ff7fba9d5feff5feabfc5ff9)))))

private def cutWord328Slab1 (j : Nat) : Nat :=
(if j < 48 then
(if j < 40 then
(if j < 36 then
(if j < 34 then
(if j < 33 then
0xd5f5f5dfcf7beafb7df5d5d7febefcf575fefabebe5df7bb57ddbbdf6babebebcbbbdfd5f5f77d57febeed7daaed5f7bbe6b7feeaeef9edfefabebebbddf7efb7f53efddefbfd5f5f7ebfddffdd4d5f3abfddffdd4fbf5feff5feaf8f5f5fefabf7df97f535fbfbbb5fd7f57d7fdd777fad5f7cfb7daeaeefbe3d7dfaff77ff757e7ddeffd7fabf777faaedffdddfeabb7eefe3f3def7bbfbeea7df7eea7d35f777f3feead4bff7d5fa9efebbdd7fd9fabbeabff57bdbbdf55ffbf9a9dfddee9dd5dff5dfdabbbfbb76bb59fdff7dbb5f5559ffbbbffbf5f3ffafdf3bfafb577
else
0xfb5cbeafbfabfed5f5fd7aff7f5f7fdf57d5fde7eafafe7eacd3dffdd59b3777f3feb7d4ed75feff753eeef9fb7eefb53bbfdfeea7cfaff7fbabebebfdf5577df6fbfefa9f7def7dfea7d7fef77fa9f5feff5fea7cedd5ffbdf53e76feffdeeeb537faefbdfd4ddf5ffbdddea7cfeffdeeef53aeff6fbfd5dfebfd56fedb7fabbdb7faaffdeefedeab6efef7bfa9ffdef6f5576faaebdd53ddfdef6f57def6dddfd56fef7beff57d6fdefea6fceffdefa9d5ffbddfeabfc5ff3d57febfe7abebfbfab9f7beef55f77ab9dffbcddf7d5f5df3d57febfd5cf9dffbddfeabd77bdf)
else
(if j < 35 then
0x9ff9faeeff755f7d7fbb7bdabedffddeffd7b7bbeabffbefe7c5ceea3efef3eeff757ebfd975fd5f7f775ff175fefabf7d5f7fbfdd4bdfdfeff757ebd5fedfd5ddf57fcdfeeaef7df575d7fbbefcdd75ffbabbbebcbbedfd5ddf7dd57fbbef97daea5ddfebe6b7fbeafaf9bdffbabbbeaff5f7eef7f53efdf6fbfd5ddf3abff5ff7d4fbf5ffaffbea6afbf5ffbddfeaecddf5ffbabf77ed7f535effbeb5fd7fbea7ff7b377dfaffd7fdf57e7df6ff77fabf7d7faabdffdf5feaaf7ebfe3f3dbfdaffbbea7dde3befafe7f7d4dff57fabfbcfd5f755feebdbd7fbaaff7fcd4bfe
else
0xf3ab53dbfe5aea7bc78df7affcea7fe5cdfe3aaff97f678ea7f7fbeaf3f3c3fbfdfceaf3edfdfeff753feff755f7cfbf7deefefea7cebbfd7f7f53efddfebfbfa9f7eeff6fbfd57ef77fdf6fea7fdefdefbfbbdfd4ffe973afb51fbcfbf77fafefea9effbfdd4f97f7fa7e7eaed7dbeafbfbb9ffc5eb9ffadf517bfdff3beff751feff4fdfd56ddf7fa7efeaf97def7d5fbe9ffc76ef73ef751dbff7f3f2e7751f7fdfefebfaa7f7fba9f3efbde7bfd4fa7fd7fdf53e9fddffdd4fa7f7faff57e9ff7baefcf97bf9ff7baed5fa72efbdd7dfd4fff2fbff7beabcbbbfdd57ff2f))
else
(if j < 38 then
(if j < 37 then
0xf3cefeaeff5ff17fa71f1efabecf76d6ff7faff571b755ff7bff7571e77dafdd4ff8bf9ff71f1d57f53fe2edadffbddfeae2ff55fe36eabffb7fbeae3e79bfbfdfeeae3dfcfb7b7f5777be5fcfd4f6ffbe3df5359fa7bb57fab8bdd4feff9bf77cdb7befbbfd5e6ddd7befbdfd4feff77fa9af97feeff16babcfbbfddaf1d4fdfdfefe6dbdd5dedf97baafbf7f7f535e3e6fb5efa9ff17baafeabee6fb96af757bbfdfcbd7fab2cdd4ff4f99fdd5e97fabcbfef2f4cfd4fe7f7d3c7579dafe7f7d3abbdf7fabcb5ef7dfeae35dfdfd5c6fea72ef8dfd5e78df76ffcea7fc6fdb
else
0xd3571f17fdfeea9fc7df7fafefb5d5c7df7bff5fd5d5cfddffbc5aea7fe7af3f7dfebfbfab8f7f3f755f77edddfefe55fdd57fbeafaafdf9777fbeafbdfcbbfaff54fbfdfeeae2ee7abeff78bfd4ef8eabfe78bbd57dff9f775ff9b7dddeabff7cdbbaefbdffba9fbbbfabbf9beef53fefe7dbff3ceff7faef571f3cdddffbdf5717eefcdfeff753fefe7eea7f6edbbf3defea7ff7bf9b7f753fd32fbcffaff55bf3df55f7ff5ff7f36fecfd4ffbfdd5c6dbf8fa65f79ff7571b77f53ff3e5dbdb7dfebfd57dfdbbfabbf9f3cedbffbdf55fe36fcbfef7f57def8e7e9fafdaea)
else
(if j < 39 then
0xd5e7dfd7fdf55f73efebfbfabbb9fafeff773abcbd77eeff7faff5779fa9fe9efaafbff2e78bfd57fcf9f0feff1d4ffbdfd5e6edbb2ffbdfd5e7ddffbdf53fb3efbdffaff55df36fdf7fba9fe99b2fbcffaff579bb6fdf7bff753ff77febfd5dece9971fbbf9ff6aea7fdeffdb3abcddb7edff7bff75777f3f5796bde7bfd5c63bf9fab8bff2e67f1d567cbf9fc753f9fab8bf9fdfceaf3b5fcfefab4cfeeff5697fde7ead2fe7f7d5a7cedfafe7f7d3aa7f7d4ff4dfd5ddff9737dfeaefe6cbfbfabbf9f0feff9efabaf9e6fefeae3ddafdd38e7f17fabcb5e7dfefbbfa9ff1
else
0xbbc5ffb6b7755f7fdfadd7f3ff7bbfdeaf79fa9af75f7daeacbdefeafcd5af7777f571eeeefea6bdedf17faaaf5abfb535ead7f6aab57f6a6ad7f6aaad6aeae3dff3fbfabaf7f9dba7e7f7f5757f7f7fef7dfef5f7f6ff77fa8efdef7f53ff3e7df7fb7dfead33fbfd7fa9fcfeff752b9fc756956fe7f7d3a95abf37fbbffbab8eabfe55fbbfdf57957e7ddfeff5feaf2ffbfd9fabddfd4d5ffde37f535e3eeffd7fdf535f6ff555f6fefeae3c7ebfd556af17fef557afc7dbfbff7beaaafe7e5d58e3bfcbabbfd7f3f8e5d566ff1d4ffcf9f17dff1d57fbea7fe5ebb737fbbf)))
else
(if j < 44 then
(if j < 42 then
(if j < 41 then
0x6b7eebf9fdff7baad6edfeffbdb59f55fcffdeefb59ffb8df6afeffef73eab57ef6ff7dffbdb5fbde3fef755ad5bff7f7b9ed67d5eef7df79edf53df7c6fcfaaf7535f7defbfabef535eaf6feffdefbbf6b766fef6feaddbffbdbf9fddaddfdee7f77f566f7d4fdacf6b37dfe7baaabfef3f57bef3dadd7bfbddfeefeabf7b7e7f7fdedad57b3ff7beefefb5abdfecdfdeeab5ab7fbfef73dadf7f3ff7baad67fef77dfd56b1ff7b7f55afd9ffbdbfab37f7b7f55af79ffbdbfaad7bcf7faaacfbf77f77f6feacffdc5fd5bf3ff7b7ed6afd7fdff7b9f567dd6beeff7ef5f57b
else
0x77eefea6b3dad76feeffdf6d6beabeffeabbff5df7d4d6ff7fba9df7d4eddfbbeffbfdd4d5af7d4ffedbeeeeddb76d7df7bfa9ffd6baadcfeff7dbf96d7bcffaff56a7ff55f7bfdf54ff7f55f7b6d7577fb7dffbab3dff7fbaade3ef2e3dbaafedf7fb3f54fb7ef8ea7f57dbfeff755be2ff555b77dfeaabee7b5b7ab8cfabf5bfb9ff67d56fa9afbfb7dffb6b6f57d77defb5776feeaef7dfd57fdfeeab77bbeab73edfb7fdfedfd5c5daf56d67bffbdf55b9755fcffbdf54fd4d6ffbd4d7dd5d4d7db5d557a35abd757b7f7f575f3cfbf57f7f5717b3ff7bbed5ecffdefbdf)
else
(if j < 43 then
0x9ffbdf7fb55fb59b1fbfdaba9fcf9ed6ed7bfdfefbfcfeaf5bb5eff7faffdfe9f577cfd4d5acfd5577bf9fabaedcfdfabf9fab2cfd4ff2f5db9f7f7fafe7eacade7fef77dab79ffbdfdbed6fd77f3ff7bfb55ad7bffbdfd6b3eabfeadefeffdefebf6b5e3fef6fead7bffbdbf9ff5ad7fdee7fd7f563fdd4fdacf6bee3fe6faaabffb3f57bfb3dad76ffbddffafeabf6f7e7fef7f5ad56f3ff7bfafefb5abd6bbf9ffbddffb55af7d57febbef6ddb59fdfeea76efdafefa95fb6b7ddafeff752beebfbbb577f577fabdabbbfabbfdf7c75779fc6fea6aedfdfd4d5abbf77f571
else
0x6bdff4fe355af79fc6ab57ff7bcffdeefb59ffbdf77ff6fb5dfde7fd7fab2fb6bdf55ffabdfcfd4d5fb59fdfeea5feff2fbeffbeffba9af756bdafef7deffd5ed67affdefebfef7effbfddfeafbffbdaf6bf9adfd5dfdfd5fefbab56d6faffbedff7d4d6feaeffbeaf577febfefa9adf5ffbebfefab7dffdefbfd7ed57fb6bf753fef3daaffbabbbf9feeabfefabecfaba9ff1fdd2abfd5d6feff7f9ff57bdfab7bfbff7b6af5bcffdefbfd6b7fabd6fdfebfbfbfdfe6baa7b5e3f97ea9ed72cff7fafb56baaff1fdd1adfd5d5fcff7faff5bb5fbf57ffbdcfab3fdfe7f56ed7))
else
(if j < 46 then
(if j < 45 then
0xd4fe6edbb35ff7fbaa7f7fb3f54d5f372afd5b7eafeefe7eadb3fef7d5957afdb3fbbfd5f67e5d4fe6bfefb7eea9f3dfeacbf67ea6bbf2cffaffbea6afe6eacbf63bfd5566bffbdf5559ff57cf7fdf56d5b35feaefb5feaef35fcdefab4bf9babbeccf1f53fcbb66ea7f95fea9f976e77f3fbfdd5967f757ab4ab7fa7ecfeef75779b2febfd52fbbfd5372bfd5365bfefaa6cdeeae5fd9eff54b7f3fbfd9baa7bfcb2f54d7f3fbedd58e5cdfafe7f7abaa6bfcbaa7e36bf5fea7f371cbfb3fbeafbddfcfe39753f9fdf56ddfb5ff79ff755fefeff4f7ff4bcff7faab5abfb8cf
else
0xbb567fef6f7b9d3b3ff7bbfdeabd7b3ff7babdefb56b37f7bbbdce9d9bfbdbfeed6ebffb3fbfef755abf9ffbdb5ab77f7b9ed7bbfaaeeafbbba8ed5f6f5feabbddecd9eff55e6bf9eea3ad7f5dbfa9ebdbb3fbfef77df9dabf9feababeef77faa6f7fcff55d3aefbeabaefbbfd575ed5fd7751dabf9ebfd574efeaaff55d7ffb555b2feaddd5f9ff7d575ff7d573e5eb9f9ff7d576fbfeffbdcffb77ef7d4fe6cdeeffeea9f9753f9b3753fcb372bfd5a66e5d4ff64fefa9fed7fdfeadd53f7fd7f3f5775bb5eafdfde7bffba96ed7f9754f7f967ead2ff2ea9fb1ff79fab6f7)
else
(if j < 47 then
0xfafeaddaefff7b9fdfed57f1f565ef1dfeaab1dff7fbaaacfef7feea77efbbfd575ff7d575dcdeff67ea76efdafd4afdddeeed7cffba95f7d57feaf7aeeef7d57fefb3aef577f775dfbd5ddfddbad6bcff7dfefbbb5f5777ff55f7faeefeabbdfedfd4eddddf7defbffba9d9dabedfeabbdfdbfd574efbaaff55db8feaddd5edff7d575ff7d566dbfefaacf9b7eecbfefaaebdd537bcb9bf5fea76bd5cdeefe7fdd537baf9ff5fea9affbcffbab8f77faaacd7f3f571abc5ffbd576ebfbfab8dde3edfdfeff75556b567fbfddcebfef6ddea3fefebfef7b51ffdf7ecfeffbdbd
else
0xbbddffdd53fbfbfd7feafeffbddd5ffaef7d5f7ddf5eaeef75f7fdbffbaaef7d5f6ffe5eafbfd7f7f55deebf57d7f7ff4feffbddffb75f9dbafeaea9efe7eaaafe7f7d5776dd9effbea9b7fdfe9ed6afe9ad7f4df755afb9b55af7fafe7fef77dabdab7ff7bfb3daf77b57f7b9ff7bb5ab3ff7bfaffbdf6ad66fef675ff7bbabbbf9beff5d5f3f53fef366fbfdddfdd3b37f7b7fdeefbb2ffbeabbfae3fefaaecff7f9ff7bbd6ed77f3ff7baad7f7b9fdfebfaad7f7b9ff7bbfab363cfeff5feaab37dc7fdaaabfeff67eaefeeed79ffbdf7fafeabfef3ff7bfb55ad7fdee7b5))))
else
(if j < 56 then
(if j < 52 then
(if j < 50 then
(if j < 49 then
0xd5c5bdff7c7eea6ad7537e2d7edf7fab8f1f77fbbffba9ade3ad7f5fd4f7bea7b3cedbbda9edbef7f53d3bf9adfd4f6ffed4d5cdf6af757ebfdf53dbed753d7df3f5fefa9edfdfdff7b7ff5efbb355feabbfae557faaecfefeff3fbb37f7b2f74fbd3b3fbfef6feef79ffbd9dbff5ffbfd3fb9dbff5ffbfd3cecffdecedffdefebf9fdcedffaffbfbd4767fef65eebd9ffbd9d2e7effd7fdff6a3b75edfeffbdfd9effdddeebcfea7f3feb53feff4f7ff7b9dbbdedbb3fabdbffb3cbfef774fddef7b51f7ffbeddeffbdcffafe6f7fba9fcf7fde7fdd4be6bfeff67ea5feff2f
else
0xeeff57d9f567fef676ff77a76ffef73fbbdf6e6ff7d4f77fbfd7fbbdeaf5bdfdffbdb57adefeffdefbfd6b57f476bfa3fbaad7dc7aad7ef77f3ff7bbed5bd5bffbdf79ed7eb7abfbdcfeff5ab79ffbdd5fb7dad59ffbdf77ff6fb5df967f77ff75353bedadfd4f6fb57babddfefa9ebbbfdf539f2edcfbbfdf53df7defea7b7dff7d56debfb675aea7b2d5fbfb3dfbdf67ef6afaee7f77b6fdfdd4f67f77ff755bef6fecf7faa7d5f76cef77b3edfbd5defbd9ef5beaf77fbfd76f7eeab6f7bfd7faadcf7b6fbfb7f7feeaeeadecffbaadbd97de7fd7fabbbfe37f5356bf67bf)
else
(if j < 51 then
0xfbdf571b76f9bffb7f5779ff753fc77f57d7fceffd7fa9af3777f57de77ddea7ff79bfb77f57de6cefbfd5f79d37f7f57de7c9fdfe7f7579ebcdfdfd5c7edf7fab9ea6f7f9f1beddff3d57f53377c6feae7c6fbb7fcf53fe37edf3d4cf9bfbfc75537fceff1d4feffdd5cfb727f7fef3d5cfdbfbff7beaf6e5adfd4f7f35bfa9edfefeff4f7b3ff7b2ef4fdd3b7fbfef73debdf7dd79fd5f67b53f3fdfebff7b9d7bdedbb3faaffbfaf5dfb3ff9e9f9e5ff7b7a7ce9ffaf9ef7bda8fdffdf5fbd9fdff7bbff4eb5d4f67efef3f53d573fbea5abe7f7d4b76afdeb7bcfd4f7dbd
else
0xcefe7fdd58e7fd7fab1bffb3f5637f3feeac7cf3f77f3fee3d5f79fb6f7f57d6fcdfcfd5c5bea7f7f9dfafcedb7f7f5feae76ebb7f7f6fea7edf55fd57d9df6acdbeaf77f9fd6eff5658fa9fe3e79dfcffb8f57de7df55f77edddffbcd5f7d57feeaeeafdf3777feeaeff79bbeeff54f77c755fe7c5deabeff9fbaeff9dbfaef55fefcedd777f6ff7d4ff9cffaaf1bfd57fef7d5c5dbbe77fef7d4ffef3efa9fdbb6ef9fdbfa9ff7fbcedf7d4fe5e3fb3fbbfd56f9fdd57dff77ff6df3ef3f571b77f53fe7cddb7b7f7bbfd57dfdfe7f6db7d56f9fd6faafbfe6ffecbc73f53f))
else
(if j < 54 then
(if j < 53 then
0x8f3dfea8effecfefabdf7bff5fea2fdfedfd4ff9f3f7f7bdf7fab1cffbddfea7f3fef7d4ae7f1d58d5bf9ff71ea56af9dffaffbeae3aaff357eeffdd5cd5f3f77fef77fab9bffbde7eaa77f8ea7fcf9f2beff8eabff753fe6edbb3bff5feae7efbbffbaafb3f7ddfdfd5f59f77f7feb3d5cddb7f77fef77fabecfd4ff1fdd57dff367c5feabfcf9f27f7f8ea7ff6feae76ebd37ff6feae7eeff7fba9fd3f7f6ff77faadf3afefef7d4ff1cb8ff67f77fab9dbafefedfefa9ffbbfddfeafb4dfdfeff69eae76ebfb7ff6ff7d5f5fcfd5cd9f37f3f8eaa7cdfcfe3a9fcffbcf573
else
0xd5ddfdb8ff55cbef3dfeaef6efeafaed5dbfbdefbbd57fef7b7a9dbbb7dfedfd4fdef7d4ffedbeff753f97df57d7f6ddf7d5f6df777abebfb7ddfeafb6e9bfefabedbb4ffbfdb7aa7d57fabbd99fe6ed97fdfeeab6edbf7d56dbfdeeff55b77f7beab7f7bbb7f6f5537ff7bdbd565ff7fb6f55eb4ffef7b7aa7db7fdfdfdbfaa5abeff67bfd47e7fdeeff51f9fdfebfd5f7bcf7fabbfd9fa95cffbdf52b9fdfeea56ed7ab9ff7bbfd5dfebfd52dffdefaa5bfeff754bb72dffdef3f52bfade7f7d56dbcbfb3fbbfd4df54797f63f77fa9daf571febf9fdf5475ff67f77fabeb7)
else
(if j < 55 then
0xbebedf7fbaafbff7ddffdb74f54f7fdfedbd56e7bffbdf54b7ff7bdb9fabdfdbfa9bfdeeff55b7f7feeab6ddfdb2ed753757df54f9efdbfb3f7b577773feb7b7efbea6f3febfefaadfdb7de7bfd53eafbb65feb79f6fdeafb7db97b77b537b7f6fea6f3dbdbfbedfdfefa9bfdd4ffbdbfbdf53f97f75777f6febfd5dedd97ff7577b769ffdef6f54faaff57da73f9d7a6ffef7d56e3fd97ddfea97f5fea8f95fc7d52dffd8faa5cf7f965ea8f2dffdd51e5bf9ff7bc7d5eefbbfbdedab9fabbfdd57d5fbeff755b57eedbbeff755f776fef77f3f57db77f57776efeeaef6febb
else
0xd55fef7bfa9df7bff59bbd5f6ff772ef52b757fef777a975ffbdddab7ceaffdeeef53bf77fbfd7faa9fdefa9fdbb3dfeea7f6ed77fb6dfeaeff753fb73fef7d4fed9d2e7f54b9fdfeea7f6e7bbeff5feab7efedf7fabbdb765ceea3fefbdf7fabedb77dfdfdbeff54beff751fb6acff7fb3dfea7faadfd9fefb9fb7de7fb2f6e7b73ff6bea2effbfb572ce97d474bcb3fa8b9db7a8fbfd56fbcff7f4fdb9ff7d9db73def73f7751d7ff7ddbeff751fb7dfe9f7faaddeeff4fbfd53edf7fbef53f97f7bcf7fa9ff7fb3f52b7ff7bcbd4afef7b73f52fbebedfdeefe7eaeff6dea)))
else
(if j < 60 then
(if j < 58 then
(if j < 57 then
0xd4ecfdbeff6fea773fef777abbcffaed9eafb3fbb977aa7f7faef53bf6be7fdefa95fb76beffdeeaf5775ff755f56ecbea3aacfdb57dfeeabeed7dffbabbabbfdfeea76bd7dfefabeab7eeeff7fbabdbbfbddfcfd5f6feaeeedcdffbabbbbe6dd5b3bff757777cdbb3bff7bea77f6ff7d4efdfd7faabbffbaabbb8ff7bcfd4efdd7faed7cfefa95fdd57fbaf6eeebfdd57fbfb2eef57df75ddfbd5f5fd72eefeeaaeefebfd55ddd7f7f6fbfefaa7fdc7a95ab7f8fbcffadf577bfabebb677fbeafaedd5feff5deaf2f55b9bfdf57d77e5eb9bfdfeea76aeffdeeef52bfbddddf
else
0xd55d7d7faff547fbf9feaaedeafeafa8bd5fcddfeaae5ff557faabd37f56beafcffeeaaeffeeaaddaf56fcffeeaaf7dffbfdf67f7afdfeea7f1e3fd7fdf54fcba9fc78f95feac71f53fcb1f2ea7f9a7fdd4ff3bffbdd3ea9fbfbbf9fabea7cedd7effb3dff7d49f3bfcbaa7bfcb3f5637f9754fccffecfd59feea7f1f3d78effef7d53fef79faa3af8f957eacfdd7fd7f3f5679fdfeeacabd7e79ff5feaef3f2ea7f1dffdcfdf54f7f3fee7d5dd7cf7ff75674f1dfeafb9dfeafb1dfc7fbab1bf8fabee67f3feeacfbf3bffb3fbea67f7beabeedcf7fbaafbb75dfedf77a8b9d)
else
(if j < 59 then
0xfd5feeaefeefaf575d7fdbfedff7d55feeaef7ff2f57f7bbfbfaabfd5fabbbfbffa7fbfdf6ff7aefcbd77f5754f7f3feeaaf9ebcf7ff75477ff6dbbd47fdf76b567fbfdf4bbffb7b51ffddfbcff7fbeb7af567fef6dfe972f3ff7bbff6ab7bcd7f37d45dafeaf7f5376f5e7fbfdf6fbf765eafb7faabfdf6ff5577757dd7d45eafb6eff5572feeabfd55eb3fab5f57b7ff75577ff7553b6ffeeaa7cedfba6ffeeaaed63fef65dffdafabebf8feff575f3f53ffb1e3fbfdf5fd76b1ff7baff4b978ffbdbffad6b978ffbdbffb5fdd37ff7557fd59ffdd55e7fbfcffed72f57f3f
else
0xab3ff7b2f7feb72f7ff7b9ff5bfb677feea6fbfdfebff5bde2ed7f5fd4dfeea6f3cbfe6b7f537677dab7d5faffdd4defb5d4ddf76fd7feea6f7f7fbfdf5ff76fee9d57faabc7f7f9fd5fd5aabfd55e7fbfbf9fd78feff1dae7db979feff7d7f5ebb79feff173a7eff77ff7dea2ff67fef65eff77feff4ffa5eff77feff4f2f7ff7beefe7fd2f7fbbffbfb517aedeffbfdf7bcf7feebfd5e7f53f9fde7fbfc76b9faff6dbb3fabdbfeed4ffbfd3dff7fa5ebfdbda8fbffddebfbfdf67f77f1fef7d4fe7bffb3fbea5f1dffdef3f52ff7f97d7faffbea9fefefebfdd7fbfdf6baf))
else
(if j < 62 then
(if j < 61 then
0xfdedffdbfdfeeafcbdffeeff755f5d7bbfdfcbb55f5efff5ffbabbaed5faff7fafd77def7d73fbff7babd4fff5fefabeae7ffaff7fabf56fbfdfdfefaffebfefaa7f77ff754f5fefbfd7faa7fdd5dd7cfefabeaf9ebfbfd7faa7fb7fdfeea9fed9b5bfa9bfe6b7f537bfefefe9edeb97bfeff7d9eddbfbfabcfeaef3dbbbf67ff373f3fdfe3adcfb7fb6dd9fd57fdf76a7e7fbfd7fbfd2e5cff77cdfeded47effeeefdbcff7fbedfee5daea6f3f7fd9fa9bab9ff75275f3feea4f9d7ef4ff67ea6fedbfd7fabbcf2fedadfd4defb56fabddffba9bbbbff7533e6ed9fbbff7537
else
0xfabf5775ff754f4f3fbeafabd74feebfeea9fdf57d5feff2fbfdfeef7fa93abfdf7bdf5ebfbfdd57d5adeeaff7dbebd77eeff755f5fdfefef77d7cf5feff7d7f7fbcf5feff777f7fecf5fdff7df6fefcfaffbefbbfdd7abfdf6ff75eb6fabfdf7baf5dfaffdd5dd7dff7f7f775f3fdfdfdddfdf4f5d3fefaafbdf5fbfbfbfcfeffd4fbd7dff7fbebfeffaff7fbabdaff7dfeeabead7bfbfdfefbd4ae7ddeffbddffabdaa7bff95f7fabfbfe577feaf4f7ff2beff57aefd7fbeafabeff7f7fbeaf9fdfdfefafefadbab7bfe57f6fafdfefefe7f7fbad6ab6ffe57f7bafdebeff7)
else
(if j < 63 then
0xf7fa7f7fa7fdcfeff751f3f7fbbffdee7fd2fefbfdd47cffbef7dfeafbfbbfdd47cffeef7dfeafa7effbfdde7fd7ff67fef676ebd3f7fbfef6fe7fd3b397f7fba8fdb77dfeea3f397f7fa7f55b77dfe9fd53dff7fbfb51ffda8b9fef7febffda8bf7fa7f57ed474ffdbfddffed474ffeeff6fbfd578ff775f67be9fdfe9fd4fa76a9cbcff7fafe7eabdfbb7dd5dcfded578b9d3faadde767fbfdbeff55efdf3beafa7ef1ffddfedf7faaff7f7fbecf7fbfbfd9eff527fbdd7ea9eb7bfd5faa7aeeff57dfd5efbfdd57d7fd5fdf54f5b3feeaeebd74ffabfbea9ff75775efe7f7
else
0x7f3f57b5e7fbfd7faa7aff71e7fdd5dcffb5ff7bea9e7edbbfbdf57b3f7bf7dd5dcfb7f7fa7fdee7fdcffbdf51ff7f7bea3e7fdfdbeff5773f7febff7fa7f73bfbef7d47cffefb7dfeaee7effbfdf67f77fde7fef65ebb73f7fdfefafe7f72f2d5fbeff4fea3a5d59fd5f7b9fd5ed5f7fa7f577fbabd9f77dfefbd47d59d2e7f577f7f751feff755f7fecfdfeeffefbd45cfdffaffbfbd477d9feff6fbfd52d5f7fa7f54b567fbfd7f3f55b77ef9fdd5dcfdb77dfedf7faadbb3fdfdfdbeff52ff7367f7d5f4fdb77efcf7d5f4ffb5fdfeea9e7edbbeff757b3f7bf77d5f4fbd)))))

private def cutWord328Slab2 (j : Nat) : Nat :=
0x13fbfdd47cfbfeff4bea9e7dff7fa7754f3fdfebfd53d5fbeff5fcfd4bfbfd

private def cutWord328 (i : Nat) : Nat :=
  let j := i/256
  let w := (if j < 32 then cutWord328Slab0 j else (if j < 64 then cutWord328Slab1 j else cutWord328Slab2 j))
  (w >>> (7*(i % 256))) &&& 127

def sliceList328 (m i : Nat) : List Nat :=
  let entry := cutHead328 (startCut328 m+i)
  let start := entry/16
  (List.range (entry % 16)).map (fun j=>cutWord328 (start+j))
end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux
open PEqualNP.Outside.L_meta_32836_aux.Core
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairList328 (m : Nat) : List (Nat × Nat) := match m with
  | 47 => [(1,5), (1,33), (4,5), (2,10), (6,38), (8,10), (36,44), (36,38), (6,7), (32,33), (3,7), (3,11), (8,40), (9,13), (9,11), (12,13)]
  | 55 => [(1,33), (4,5), (32,34), (4,20), (6,38), (16,20), (18,19), (3,7), (3,19), (36,38), (18,50), (32,33), (48,50), (36,52), (48,52)]
  | 59 => [(1,17), (1,33), (16,17), (2,10), (8,10), (18,50), (48,56), (48,50), (18,19), (32,33), (3,19), (3,11), (8,40), (9,25), (9,11), (24,25)]
  | 61 => [(1,33), (4,5), (32,40), (4,20), (12,44), (16,20), (24,25), (9,13), (9,25), (36,44), (24,56), (32,33), (48,56), (36,52), (48,52)]
  | 63 => [(6,14), (12,14), (18,22), (6,22), (6,7), (6,38), (9,13), (48,50), (24,25), (24,56), (9,25), (48,56), (1,33), (32,33), (3,11), (9,11), (36,52), (48,52), (3,19), (36,44), (3,35), (36,37), (3,7), (12,44), (18,19), (36,38), (12,13), (18,50), (9,41), (12,28), (48,49), (18,26), (24,26), (24,28), (1,5), (1,17), (32,34), (32,40), (0,33), (3,33), (3,34), (9,33), (36,33), (48,33), (0,5), (0,17), (0,34), (0,40), (1,37), (1,49), (2,11), (3,5), (3,10), (3,17), (4,7), (6,5), (6,10), (6,34), (9,17), (18,34)]
  | 79 => [(3,7), (12,14), (6,7), (3,11), (3,67), (12,76), (64,66), (64,65), (64,72), (64,68), (6,14), (9,11), (9,13), (12,13), (6,70), (9,73), (0,65), (0,66), (0,68), (0,72), (3,5), (3,10), (6,5), (6,10)]
  | 87 => [(1,17), (1,65), (64,66), (1,5), (4,5), (18,82), (6,22), (18,19), (18,22), (4,68), (64,65), (64,68), (80,82), (3,5), (6,5)]
  | 91 => [(1,17), (1,65), (16,17), (2,10), (8,10), (18,82), (80,88), (80,82), (18,19), (64,65), (3,19), (3,11), (8,72), (9,25), (9,11), (24,25)]
  | 93 => [(1,17), (1,65), (64,72), (1,5), (4,5), (24,88), (12,28), (24,25), (24,28), (4,68), (64,65), (64,68), (80,88), (9,5), (12,5)]
  | 94 => [(2,66), (4,20), (16,20), (2,10), (8,10), (12,76), (80,82), (80,88), (18,22), (64,68), (6,22), (6,14), (18,82), (12,28), (4,68), (12,14), (24,28)]
  | 95 => [(1,17), (3,11), (9,11), (6,7), (3,7), (80,82), (80,84), (80,88), (18,82), (6,22), (80,81), (9,73), (6,14), (12,14), (12,76), (24,25), (24,28), (12,28), (24,88), (3,67), (6,70), (9,13), (12,13), (18,19), (18,22), (1,65), (64,65), (18,26), (24,26), (64,68), (64,66), (64,72), (1,5), (3,65), (4,5), (9,65), (80,17), (80,20), (0,65), (0,66), (0,68), (0,72), (3,5), (3,10), (6,5), (6,10), (64,5)]
  | 103 => [(1,5), (1,33), (1,65), (4,5), (32,34), (6,38), (6,70), (32,33), (64,66), (64,68), (3,7), (6,7), (32,96), (36,38), (64,65), (64,96)]
  | 106 => [(2,10), (8,40), (32,34), (2,66), (64,96), (8,72), (32,40), (64,66), (2,34), (64,72), (8,10), (32,96)]
  | 109 => [(1,5), (1,33), (1,65), (4,5), (32,40), (12,44), (12,76), (32,33), (64,68), (64,72), (9,13), (12,13), (32,96), (36,44), (64,65), (64,96)]
  | 111 => [(1,5), (1,33), (4,5), (2,10), (8,10), (2,66), (6,38), (9,73), (64,68), (64,72), (64,65), (64,66), (3,7), (6,7), (8,40), (36,44), (36,100), (12,13), (36,38), (9,13), (64,96), (32,33), (3,11), (9,11), (12,76), (3,67), (6,14), (6,70), (12,14), (3,65), (9,65)]
  | 115 => [(1,17), (16,17), (32,34), (32,96), (64,96), (80,82), (32,33), (3,67), (18,50), (18,19), (48,112), (64,65), (1,33), (3,19), (80,96)]
  | 117 => [(1,5), (1,17), (1,33), (1,65), (4,5), (36,52), (36,100), (48,49), (48,52), (80,112), (48,112), (64,65), (64,68)]
  | 118 => [(2,66), (4,20), (16,20), (2,34), (32,34), (36,100), (80,82), (80,112), (18,22), (64,68), (6,22), (6,38), (18,82), (36,52), (4,68), (36,38), (48,52)]
  | 119 => [(36,38), (36,52), (6,38), (48,52), (3,19), (80,82), (6,7), (48,112), (3,67), (80,81), (3,7), (80,112), (1,33), (64,68), (36,37), (36,100), (18,19), (18,82), (6,22), (48,50), (6,70), (18,22), (18,50), (48,49), (1,65), (64,65), (6,34), (1,17), (3,66), (64,66), (1,5), (64,96), (3,35), (80,84), (36,33), (36,68), (3,34), (6,66), (1,49), (3,65), (16,22), (48,33), (3,5), (3,17), (3,33), (6,5), (18,34), (18,66), (80,68)]
  | 121 => [(1,17), (16,17), (32,40), (32,96), (64,96), (80,88), (32,33), (9,73), (24,56), (24,25), (48,112), (64,65), (1,33), (9,25), (80,96)]
  | 123 => [(16,17), (1,17), (32,34), (32,40), (80,112), (48,112), (3,11), (9,11), (32,33), (3,67), (9,41), (80,88), (80,82), (24,88), (18,50), (3,19), (64,65), (9,25), (18,19), (24,25), (18,82), (24,56), (3,35), (9,73), (18,26), (24,26), (32,96), (64,96), (48,50), (48,56), (64,66), (64,72), (3,33), (3,65), (9,33), (9,65), (1,33), (1,65), (2,34), (2,66)]
  | 124 => [(4,20), (4,68), (16,20), (8,40), (24,88), (32,40), (80,112), (80,88), (24,28), (64,68), (12,28), (12,44), (32,96), (36,52), (36,44), (48,52)]
  | 125 => [(36,44), (36,52), (12,44), (48,52), (9,25), (80,88), (12,13), (48,112), (9,73), (80,81), (9,13), (80,112), (1,33), (64,68), (36,37), (36,100), (24,25), (24,88), (12,28), (48,56), (12,76), (24,28), (24,56), (48,49), (1,65), (64,65), (12,40), (1,17), (9,72), (64,72), (1,5), (64,96), (9,41), (80,84), (36,33), (36,68), (9,40), (12,72), (1,49), (9,65), (16,28), (48,33), (9,5), (9,17), (9,33), (12,5), (24,40), (24,72), (80,68)]
  | 126 => [(16,20), (4,20), (2,10), (8,10), (2,34), (48,112), (80,82), (64,68), (80,112), (36,44), (12,76), (80,88), (36,38), (12,44), (18,82), (6,22), (12,28), (18,22), (36,52), (24,28), (48,52), (24,88), (6,70), (36,100), (24,56), (48,50), (48,56), (64,66), (64,72), (64,96), (4,68), (6,14), (6,38), (12,14), (18,26), (18,50), (24,26), (6,68), (12,68), (36,68), (0,66), (0,72), (0,96), (64,10), (64,34), (64,40)]
  | 127 => [(36,52), (3,11), (9,11), (3,7), (80,81), (6,38), (48,112), (9,25), (36,38), (36,44), (48,52), (12,13), (9,41), (3,67), (80,112), (80,82), (12,76), (80,88), (64,68), (32,33), (6,22), (18,19), (24,28), (18,82), (36,100), (12,44), (6,14), (12,14), (9,73), (3,35), (48,56), (6,7), (48,50), (9,13), (24,88), (3,19), (18,50), (24,25), (18,22), (36,37), (6,70), (12,28), (24,26), (18,26), (24,56), (64,96), (64,65), (64,66), (64,72), (48,49), (80,84), (1,33), (1,65), (1,17), (36,68), (3,66), (3,33), (9,33), (48,20), (1,5), (48,17), (18,17), (24,17), (6,66), (3,65), (9,65), (32,34), (32,40), (18,20), (24,20), (36,33), (48,96), (18,34), (9,72), (48,33), (3,17), (9,17), (32,96), (80,68), (4,20), (1,49), (36,96), (6,68), (12,68), (32,42), (6,5), (12,5), (12,40), (0,20), (3,34), (4,68), (4,5), (80,17), (2,34), (3,5), (9,5), (9,40), (36,20), (2,19), (3,75), (9,75), (16,84), (2,66), (6,39), (48,114), (48,120), (3,10), (9,10), (36,5), (1,19), (1,25), (2,7), (6,20), (6,34), (12,20), (16,112), (1,37), (3,43), (9,43), (36,65), (80,20), (80,65), (2,11), (8,11), (18,66), (0,65), (24,40), (32,100), (32,112), (64,10), (1,69), (1,81), (4,38), (4,44), (4,52), (6,10), (8,13), (8,25), (8,41), (12,10), (12,72), (24,72), (32,35), (32,41), (64,5)]
  | _ => []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pairListOK328 : ∀ i : Fin 128, (pairList328 i).all
    (fun p=>(dom328 i).testBit p.1 && (dom328 i).testBit p.2 &&
       !(target328 &&& dom328 i).testBit p.1 && (target328&&&dom328 i).testBit p.2) = true := by
  decide +kernel
end PEqualNP.Outside.L_meta_32836_aux

open PEqualNP.Outside.L_meta_32836_aux.Core PEqualNP.Outside.L_meta_32836_aux
namespace PEqualNP.Outside.L_meta_32836_aux.Cubes

abbrev Gates := List (Nat × Nat × Nat)
abbrev Bank := List Nat
structure Book where
  count : Nat
  record : Nat → Nat × Nat × Nat
  hint : Nat → Bank → Nat
  picks : Nat → List Nat := fun _ => (List.range 128).reverse

def insertWord (w : Nat) : Bank → Bank
  | [] => [w]
  | z::zs => if w ≤ z then w::z::zs else z::insertWord w zs

def ordered (w : Bank) := w.foldr insertWord []
def makeStep (d : Nat) (st : Bank × Gates) (edge : Nat) : Bank × Gates :=
  let w := st.1
  let a := w.getD (edge/256) 0
  let b := w.getD (edge/16 % 16) 0
  let op := edge/4 % 4
  let z := opD d op a b
  let rest := (w.erase a).erase b
  let next := z :: ((if edge.testBit 0 then [a] else []) ++
                     (if edge.testBit 1 then [b] else []) ++ rest)
  (ordered next, st.2 ++ [(op,a,b)])

def bankPath (m : Nat) (book : Book) : Nat → Nat → Bank × Gates
  | 0, _ => (ordered ((roots328 m).map (· &&& dom328 m)),[])
  | f+1, idx =>
    let (_,par,edge) := book.record idx
    if par=0 then (ordered ((roots328 m).map (· &&& dom328 m)),[])
    else makeStep (dom328 m) (bankPath m book f (par-1)) edge

def evalCube (d y cap : Nat) (ws : Bank) (hint : Nat) : Bool :=
  let t := tiny (hint % 32)
  let off := hint / 32 % 1024
  let flip := hint / 32768 % 16
  let inds := (List.range t.roots.length).map (fun i => hint >>> (19+4*i) &&& 15)
  let axes := inds.foldl (fun m j => m ||| (1<<<j)) 0
  let sorted := ordered ws
  let sub := sorted.zipIdx.foldl (fun z v =>
    if axes.testBit v.2 then z else z &&& signedColumn d v.1 (off.testBit v.2)) d
  let cols := inds.map (fun j => sorted.getD j 0)
  cubeOK d y cap ws t sub (selectRows t sub d cols flip)

theorem evalCube_sound (d y cap : Nat) (ws : Bank) (h : Nat)
    (ok : evalCube d y cap ws h = true) {q} (hq : q ≤ cap) : ¬ RunD true d y q ws := by
  dsimp only [evalCube] at ok
  apply cubeOK_sound (tiny_valid _)
  simp only [cubeOK, Bool.and_eq_true, decide_eq_true_eq] at ok ⊢
  exact ⟨ok.1,by omega⟩

def sliceCheck (m k s : Nat) (path : Gates) (ws : Bank) : Bool :=
  let sub := dom328 k
  let root := roots328 k
  (k &&& m == k) && decide (k < m) && subValidB (dom328 m) sub target328 target328 &&
    checkPool true sub (lb328 k) s (runOps true sub (0,root) path) ws

theorem sliceCheck_sound {m k s : Nat} {path : Gates} {ws : Bank} (pri : deps328 m)
    (ok : sliceCheck m k s path ws = true) {t} (ht : t ≤ s) :
    ¬ RunD true (dom328 m) (target328 &&& dom328 m) t ws := by
  simp only [sliceCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨hsub,hlt⟩,hv⟩,hpool⟩ := ok
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have sup : ∀ v∈ roots328 k, Avail true (dom328 k) (roots328 k) v :=
    fun v h => Or.inr (Or.inl ⟨_,h,rfl⟩)
  obtain ⟨bank,hr,hb⟩ := runOps_sound hv.1.1.1 path (0,roots328 k) (roots328 k) rfl sup
  exact checkPool_sound hv.1.1.1 hv.1.1.2 rfl hv.2 (pri _ hsub hlt) _ bank hr hb
    (checkPool_le68 _ _ _ _ _ ht _ _ hpool)

def childCut (m : Nat) (book : Book) (s : Nat) (picks : List Nat) (path : Gates) (ws : Bank) : Bool :=
  let d := dom328 m
  let y := target328 &&& d
  let h := book.hint s ws
  let idx := h/2-1
  let lhs := if h==0 then false else if h % 2==1 then evalCube d y s ws (h/2)
    else idx<book.count && s==(book.record idx).1 && ws.isPerm (bankPath m book 12 idx).1
  lhs || (s==0 && ws != [y]) || (s+1<ws.length) ||
    !(determined68 y ws d) || picks.any (fun k=>sliceCheck m k s path ws)

theorem childCut_sound {m : Nat} {book : Book} {s : Nat} {picks : List Nat} {path : Gates} {ws : Bank}
    (hd : dom328 m &&& mask256 = dom328 m) (pri : deps328 m)
    (rec : ∀ j<book.count, (book.record j).1 = s →
      ∀ t ≤ s, ¬RunD true (dom328 m) (target328 &&& dom328 m) t (bankPath m book 12 j).1)
    (ok : childCut m book s picks path ws = true) :
    ∀ t ≤ s, ¬RunD true (dom328 m) (target328 &&& dom328 m) t ws := by
  intro t ht hr
  simp only [childCut,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq,
    Bool.not_eq_true',List.any_eq_true] at ok
  rcases ok with (((h|h)|h)|h)|⟨k,_,h⟩
  · split at h
    · contradiction
    · split at h
      · exact evalCube_sound _ _ _ _ _ h ht hr
      · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at h
        exact rec _ h.1.1 h.1.2.symm _ ht (Run.perm h.2 hr)
  · exact h.2 (zero_done hr (by omega))
  · have := run_len hr; omega
  · exact Bool.noConfusion (h.symm.trans (determined68_run hd hr))
  · exact sliceCheck_sound pri h ht hr


end PEqualNP.Outside.L_meta_32836_aux.Cubes

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core PEqualNP.Outside.L_meta_32836_aux
def stepCov (d slack : Nat) (pairs : List (Nat × Nat)) (ws : List Nat)
    (f : (Nat × Nat × Nat) → List Nat → Bool) : Bool :=
  nextD_cov true d (maskP pairs.length) slack
    (ws.map (fun w => (w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)))
    (fun g dzs => f g (dzs.map Prod.fst))

set_option maxHeartbeats 1000000 in
def pairsOK (d T : Nat) (pairs : List (Nat × Nat)) : Bool :=
  pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T&&&d).testBit p.1 && (T&&&d).testBit p.2)

set_option maxHeartbeats 1000000 in
theorem stepCov_eq (d T slack : Nat) (pairs : List (Nat × Nat)) (ws : List Nat)
    (f : (Nat × Nat × Nat) → List Nat → Bool)
    (hd : d &&& mask256 = d) (hp : pairsOK d T pairs = true) :
    stepCov d slack pairs ws f =
      nextD true d slack ws (fun g zs => coversP true pairs zs && f g zs) := by
  have hr1 : ∀ r ∈ pairs.map Prod.fst, d.testBit r = true := by
    intro r h
    obtain ⟨p,hp',rfl⟩ := List.mem_map.1 h
    have z := List.all_eq_true.1 hp p hp'
    simp only [Bool.and_eq_true] at z
    exact z.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, d.testBit r = true := by
    intro r h
    obtain ⟨p,hp',rfl⟩ := List.mem_map.1 h
    have z := List.all_eq_true.1 hp p hp'
    simp only [Bool.and_eq_true] at z
    exact z.1.1.2
  unfold stepCov
  rw [nextD_cov_eq,nextD_decor_eq true hd pairs hr1 hr2]
  congr 1
  funext g zs
  rw [coversD_eq]
  simp [List.map_map,Function.comp_def]

abbrev rowPairs (m : Nat) := pairList328 m
theorem rowPairsOK (m : Nat) (hm : m < 128) : pairsOK (dom328 m) target328 (rowPairs m) = true := by
  have H : ∀ j : Fin 128,pairsOK (dom328 j.val) target328 (rowPairs j.val) = true := by decide +kernel
  exact H ⟨m,hm⟩


end PEqualNP.Outside.L_meta_32836_aux.Cubes

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core PEqualNP.Outside.L_meta_32836_aux
abbrev Pool328 := Nat × Nat × (Nat × List Nat)

def area328 : Nat := (dom328 106) <<< 16
def shifted328 : Nat := moveBits (dom328 106) 16 target328
theorem areaLower328 (h : prior328 106) :
    Lower true area328 (roots328 106) shifted328 7 := by
  apply lower_iso (d1:=dom328 106) (T1:=target328) (roots1:=roots328 106)
    [(dom328 106,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact h

def areaCheck328 (m s : Nat) (ws : Bank) (path : Gates) : Bool :=
  (106 &&& m == 106 && 106 < m && area328 &&& dom328 m == area328) &&
      checkPool true area328 7 s (runOps true area328 (0,roots328 106) path) ws

theorem areaCheck_ok328 {m s t : Nat} {ws : Bank} {path : Gates} (pri : deps328 m)
    (h : areaCheck328 m s ws path = true) (ht : t ≤ s) :
    ¬ RunD true (dom328 m) (target328 &&& dom328 m) t ws := by
  simp only [areaCheck328,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  have hd : area328 &&& mask256 = area328 := by decide +kernel
  have spl := areaLower328 (pri _ h.1.1.1 h.1.1.2)
  have ini : ∀ w ∈ roots328 106, Avail true area328 (roots328 106) w :=
    fun w hw => Or.inr (Or.inl ⟨w,hw,rfl⟩)
  obtain ⟨bank,hr,hb⟩ := runOps_sound hd path (0,roots328 106) (roots328 106) rfl ini
  exact checkPool_sound hd h.1.2 (by decide +kernel : target328 &&& area328 = shifted328 &&& area328)
    (by decide +kernel) spl _ bank hr hb (checkPool_le68 _ _ _ _ _ ht _ _ h.2)
def scopes328 (m : Nat) (picks : List Nat) (path : Gates) : List Pool328 :=
  (picks.filter (fun k => (k &&& m == k) && (k < m) &&
    subValidB (dom328 m) (dom328 k) target328 target328)).map fun k =>
    (dom328 k, lb328 k, runOps true (dom328 k) (0,roots328 k) path)

def pathCut328 (cs : List Pool328) (s : Nat) (g : Nat × Nat × Nat) (ws : Bank) :=
  cs.any (fun c => checkPool true c.1 c.2.1 s (stepOp true c.1 c.2.2 g) ws)

theorem pathCut328_sound {m s : Nat} {picks : List Nat} {path : Gates} {ws : Bank} {g}
    (pri : deps328 m) (h : pathCut328 (scopes328 m picks path) s g ws = true) {t} (ht : t ≤ s) :
    ¬ RunD true (dom328 m) (target328 &&& dom328 m) t ws := by
  simp only [pathCut328,scopes328,List.any_eq_true,List.mem_map,List.mem_filter] at h
  obtain ⟨_,⟨k,⟨_,hok⟩,rfl⟩,hpool⟩ := h
  apply sliceCheck_sound (k:=k) (path:=path++[g]) pri _ ht
  unfold sliceCheck
  rw [Bool.and_eq_true]
  exact ⟨hok,by simpa only [runOps,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpool⟩

def scopesPos (m : Nat) (picks : List Nat) (path : Gates) : List Pool328 :=
  let cs:=scopes328 m picks path
  if 106 &&& m == 106 && 106 < m && area328 &&& dom328 m == area328 then
    cs ++ [(area328,7,runOps true area328 (0,roots328 106) path)] else cs

theorem pathPosSound {m s : Nat} {picks : List Nat} {path : Gates} {ws : Bank} {g}
    (pri : deps328 m) (h : pathCut328 (scopesPos m picks path) s g ws = true) {t} (ht : t ≤ s) :
    ¬ RunD true (dom328 m) (target328 &&& dom328 m) t ws := by
  unfold scopesPos at h
  split at h
  next ok =>
    simp only [pathCut328,List.any_append,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true] at h
    rcases h with base|pos
    · exact pathCut328_sound pri base ht
    · apply areaCheck_ok328 (path:=path++[g]) pri _ ht
      simpa only [areaCheck328,ok,Bool.true_and,runOps,List.foldl_append,List.foldl_cons,List.foldl_nil] using pos
  next => exact pathCut328_sound pri h ht

def cachedCut (m : Nat) (book : Book) (s : Nat) (pool : List Pool328) (g : Nat × Nat × Nat) (ws : Bank) :=
  pathCut328 pool s g ws || childCut m book s [] [] ws

theorem cachedCut_sound {m s : Nat} {book : Book} {picks : List Nat} {path : Gates} {ws : Bank} {g}
    (hd : dom328 m &&& mask256 = dom328 m) (pri : deps328 m)
    (smaller : ∀ j<book.count, (book.record j).1 = s →
      ∀ t ≤ s, ¬RunD true (dom328 m) (target328 &&& dom328 m) t (bankPath m book 12 j).1)
    (ok : cachedCut m book s (scopesPos m picks path) g ws = true) {t} (ht : t ≤ s) :
    ¬ RunD true (dom328 m) (target328 &&& dom328 m) t ws := by
  rcases Bool.or_eq_true_iff.mp ok with h|h
  · exact pathPosSound pri h ht
  · exact childCut_sound hd pri smaller h _ ht

def cachedRow (m : Nat) (book : Book) (j : Nat) : Bool :=
  let cap := (book.record j).1
  let (ws,path) := bankPath m book 12 j
  let d := dom328 m
  let cache := scopesPos m (book.picks j) path
  ws != [target328 &&& d] && (cap == 0 ||
    !(stepCov d (cap+1-ws.length) (rowPairs m) ws (fun g zs=> !(cachedCut m book (cap-1) cache g zs))))


end PEqualNP.Outside.L_meta_32836_aux.Cubes

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core
abbrev ProjBank := List (Nat × Nat × Nat)
def initProj (m : Nat) : ProjBank :=
  let d := dom328 m
  let rs := (roots328 m).map (· &&& d)
  let ps : List (Nat × Nat) := match m with
    | 47 => [(0x6c03,0xef07),(0xd18,0x4db8),(0x81d4,0xa5d5),(0xf020,0xf868),(0x2c0,0x12d2)]
    | 55 => [(0x181,0x9c3),(0x5d0,0x17d4),(0x221a,0x62ba),(0x5460,0x7568),(0x7a04,0x7e15)]
    | 59 => [(0x6c03,0xef07),(0xd28,0x4db8),(0xf010,0xf858),(0x81e4,0xa5e5),(0x2c0,0x12e2)]
    | 61 => [(0x181,0x9c3),(0x221a,0x62ba),(0x5d0,0x17d4),(0x5460,0x7568),(0x7a04,0x7e15)]
    | 63 => [(0x43b038c1054d440,0x4ef3ecc5574f550),(0xbbc01808954403d,0xb5441118b54c0bf),(0x3c0040026a9003b,0xc9100626eb007f),(0x400020334808742,0x1148023b488cf43),(0x8000803c9020b84,0x422200be9070f8c),(0xc30422b2880,0xa03cff05abb3aa0)]
    | 79 => [(0x309819,0x51b89d),(0xf0441d,0xa24c5f),(0xc06426,0x547627),(0xb822,0xa8bd2a),(0x3c0,0xfc3f0)]
    | 87 => [(0x200b,0x649b),(0x61e0,0x11e4),(0x4250,0x6b58),(0x11a0,0x11e1),(0x1c04,0x1e26)]
    | 91 => [(0x6c03,0xef07),(0xd28,0x4db8),(0xf010,0xf858),(0x81e4,0xa5e5),(0x2c0,0x12e2)]
    | 93 => [(0x200b,0x649b),(0x4250,0x6b58),(0x61e0,0x11e4),(0x11a0,0x11e1),(0x1c04,0x1e26)]
    | 94 => [(0x1d09,0x9d59),(0xec22,0x1ef26),(0x1a030,0x1a8b8),(0x111c4,0x135c6),(0x2c0,0x52e1)]
    | 95 => [(0xc0b02280817,0x545f06e88c1f),(0x3c020998131a,0x28805998333e),(0x300400527208,0x552521737258),(0x81067e804,0x2a009867f886),(0x30198585e0,0x30198787e1),(0x4030e40004e0,0x3cae61c4de0)]
    | 103 => [(0x407,0x4c8f),(0xc60,0x2d70),(0x2868,0x2e69),(0x3090,0xb0b2),(0xc300,0xd344)]
    | 106 => [(0x109,0x58d),(0x422,0x663),(0x844,0x956),(0x290,0xab8)]
    | 109 => [(0x407,0x4c8f),(0x2868,0x2d69),(0xc60,0x2e70),(0x3090,0xb0b2),(0xc300,0xd344)]
    | 111 => [(0x62c81083,0x62ea3487),(0x2e403068,0x1ec43878),(0x1d07a044,0x1d0fb145),(0x518a4090,0x15cac298),(0x258000,0x35c042),(0x100f00,0x6b110fa0)]
    | 115 => [(0x3081,0x3ac3),(0x2380,0x23a4),(0x4722,0x2723),(0x44c,0x555c),(0x4830,0x4cb8)]
    | 117 => [(0xf,0x89f),(0x70,0x1171),(0x780,0x7a2),(0x5e0,0x7e4),(0x1a00,0x1e48)]
    | 118 => [(0x1d09,0x9d59),(0xec22,0x1ef26),(0x111c4,0x135c6),(0x1a030,0x1a8b8),(0x2c0,0x52e1)]
    | 119 => [(0x1cd159001510,0x3ec54b815750),(0xfcb114770554,0xc131347f0575),(0x202c0414c047,0x1250a4034e44f),(0x1c30200eb0aa8,0x94208ef0aba),(0x20c0088c08b,0x525584c8d88f),(0x10002a2002a20,0x180aab312aba0)]
    | 121 => [(0x3081,0x3ac3),(0x2380,0x23a4),(0x4722,0x2723),(0x44c,0x555c),(0x4830,0x4cb8)]
    | 123 => [(0x3f00c286c2,0x3f00cf87c3),(0xc30154c240,0xc05354d2c4),(0xc02aa2480,0xa3aa2cc8),(0x333c7831,0x333ef833),(0x3400012c,0x553c60453c),(0xc8011810,0xaacc913a30)]
    | 124 => [(0x6c03,0xef07),(0xd18,0x4db8),(0x81d4,0xa5d5),(0xf020,0xf868),(0x2c0,0x12d2)]
    | 125 => [(0x1cd159001510,0x3ec54b815750),(0x202c0414c047,0x1250a4034e44f),(0xfcb114770554,0xc131347f0575),(0x1c30200eb0aa8,0x94208ef0aba),(0x20c0088c08b,0x525584c8d88f),(0x10002a2002a20,0x180aab312aba0)]
    | 126 => [(0x2d8042c014,0x191f8a42d05c),(0xe3c0c5b602,0xe3c0dfb683),(0x5201292408,0x2a1695292e0c),(0x1c073a4961,0x1c073fc963),(0x8006941220,0x340927943330),(0x3800380009c0,0x7e078e04de0)]
    | 127 => [(0xc00706c19c2011a030bb8000a3000308e,0x1c70c2ef0f09cd8611c437b3a40aab028389e),(0x80142384cc62240911a1800958a4b0202a,0x48921c62addc2210010480808d59acb0a12e),(0x18f0008710820cee8040804003808f110b21,0x10174811590a2cd6cc0300c4403c28f550f29),(0x3f004844081180c81222420016261a411884,0xbfa24c604e190090020800011e265e431a86),(0x200053080320100045b074061c7540e2c450,0x249010d63261101983074261e7d40f2c4d1),(0xc00180801302001224cc1442008141080741,0xc471c07a0381229325cc030a309163085761),(0x1000203000000100040000005e0000006c010,0x300db2880378040e628380d5e1041187e050)]
    | _ => []
  rs.zip ps

def PairWord (ps : List (Nat × Nat)) (w : Nat) : Nat × Nat :=
  (projBit (ps.map Prod.fst) w,projBit (ps.map Prod.snd) w)

def accurate (ps : List (Nat × Nat)) (b : ProjBank) : Prop := ∀ e ∈ b, e.2 = PairWord ps e.1

theorem initProj_valid {m : Nat} (hm : m < 128) : accurate (rowPairs m) (initProj m) := by
  have H : ∀ i : Fin 128, (initProj i.val).all (fun e=>e.2 == PairWord (rowPairs i.val) e.1) = true := by decide +kernel
  intro e he
  exact beq_iff_eq.mp (List.all_eq_true.mp (H ⟨m,hm⟩) e he)

def readProj (ps : List (Nat × Nat)) : ProjBank → Nat → Nat × Nat
  | [], w => PairWord ps w
  | e::b,w => if e.1 == w then e.2 else readProj ps b w

theorem readProj_ok {ps : List (Nat × Nat)} {b : ProjBank} (h : accurate ps b) (w : Nat) :
    readProj ps b w = PairWord ps w := by
  induction b with
  | nil => rfl
  | cons a b ih =>
    by_cases he : a.1 = w
    · simpa only [readProj,he,beq_self_eq_true,if_true] using he ▸ (h a List.mem_cons_self)
    · simp only [readProj,beq_eq_false_iff_ne.mpr he,if_false]
      exact ih (fun e hv=>h e (List.mem_cons_of_mem a hv))

def addProj (d : Nat) (ps : List (Nat × Nat)) (b : ProjBank) (g : Nat × Nat × Nat) : ProjBank :=
  let pa:=readProj ps b g.2.1
  let pb:=readProj ps b g.2.2
  let mp:=maskP ps.length
  (opD d g.1 g.2.1 g.2.2, opP mp g.1 pa.1 pb.1, opP mp g.1 pa.2 pb.2)::b

theorem addProj_ok {d T : Nat} {ps : List (Nat × Nat)} (hd : d &&& mask256=d)
    (hp : pairsOK d T ps=true) {b : ProjBank} (hb : accurate ps b) (g : Nat × Nat × Nat) :
    accurate ps (addProj d ps b g) := by
  intro e he
  rcases List.mem_cons.mp he with rfl|he
  · have M (f : (Nat × Nat) → Nat) (h : ∀ z ∈ ps, d.testBit (f z)=true) :
        ∀ r∈ps.map f, d.testBit r=true := by
      intro r hr; obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hr;exact h _ hz
    have ok z (hz : z ∈ ps) := List.all_eq_true.mp hp z hz
    have A := M Prod.fst (fun z hz=>(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (ok z hz)).1).1).1)
    have B := M Prod.snd (fun z hz=>(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (ok z hz)).1).1).2)
    simp only [PairWord,projBit_opD hd A,projBit_opD hd B,List.length_map,readProj_ok hb]
  · exact hb _ he

theorem iterProj_ok {d T : Nat} {ps : List (Nat × Nat)} (hd : d &&& mask256=d)
    (hp : pairsOK d T ps=true) (path : Gates) {b : ProjBank} (hb : accurate ps b) :
    accurate ps (path.foldl (addProj d ps) b) := by
  induction path generalizing b with
  | nil => exact hb
  | cons g path ih => exact ih (addProj_ok hd hp hb g)

def projectedStep (m slack : Nat) (ws : Bank) (path : Gates)
    (f : (Nat × Nat × Nat) → Bank → Bool) :=
  let d:=dom328 m
  let ps:=rowPairs m
  let cache:=path.foldl (addProj d ps) (initProj m)
  nextD_cov true d (maskP ps.length) slack (ws.map (fun w => (w,readProj ps cache w)))
    (fun g zs => f g (zs.map Prod.fst))

theorem projectedStep_eq {m : Nat} (hm : m<128) (hd : dom328 m &&& mask256=dom328 m)
    (slack : Nat) (ws : Bank) (path : Gates) (f) :
    projectedStep m slack ws path f = stepCov (dom328 m) slack (rowPairs m) ws f := by
  have hb:=iterProj_ok hd (rowPairsOK m hm) path (initProj_valid hm)
  simp only [projectedStep,stepCov,readProj_ok hb,PairWord]

def projectedRow (m : Nat) (book : Book) (j : Nat) : Bool :=
  let cap := (book.record j).1
  let (ws,path) := bankPath m book 12 j
  let d := dom328 m
  let cache := scopesPos m (book.picks j) path
  ws != [target328 &&& d] && (cap == 0 ||
    !(projectedStep m (cap+1-ws.length) ws path (fun g zs=> !(cachedCut m book (cap-1) cache g zs))))

theorem projectedRow_eq {m : Nat} (hm : m < 128) (hd : dom328 m &&& mask256=dom328 m)
    (book : Book) (i : Nat) : projectedRow m book i = cachedRow m book i := by
  simp only [projectedRow,cachedRow,projectedStep_eq hm hd]

end PEqualNP.Outside.L_meta_32836_aux.Cubes

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core

def symTag := 0xcc00cc00cc00cc00cc00cc00cc00cc
def symW (v : Nat) := moveBits symTag 6 v
def symIndex (j : Nat) := if symTag.testBit j then 6+j else if (symTag <<< 6).testBit j then j-6 else j

theorem symBit (v j : Nat) : (symW v).testBit j = v.testBit (symIndex j) := by
  rw [symW,moved symTag 6 j v (by decide +kernel)]
  unfold symIndex
  split_ifs <;> rfl

theorem symIndex_inv (j : Nat) : symIndex (symIndex j)=j := by
  by_cases h : j<128
  · exact (show ∀ i : Fin 128,symIndex (symIndex i.val)=i.val by decide +kernel) ⟨j,h⟩
  · have pow : 2^128 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    have a : symTag < 2^128 := by decide +kernel
    have b : symTag<<<6 < 2^128 := by decide +kernel
    have eq : symIndex j=j := by
      simp [symIndex,Nat.testBit_lt_two_pow (lt_of_lt_of_le a pow),Nat.testBit_lt_two_pow (lt_of_lt_of_le b pow)]
    rw [eq,eq]

theorem symW_inj : Function.Injective symW := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  have x := congrArg (fun z : Nat => z.testBit (symIndex i)) h
  simpa only [symBit,symIndex_inv] using x

theorem symRun {d y : Nat} (hd : symW d=d) (hy : symW y=y) {s ws} (hr : RunD true d y s ws) :
    RunD true d y s (ws.map symW) := by
  have hop (op a b : Nat) : symW (opD d op a b)=opD d op (symW a) (symW b) := by
    exact applyMoves_opD [(symTag,6)] (by decide +kernel) hd op a b
  have h0 : symW 0=0 := by decide +kernel
  induction hr using Run.fold with
  | done => simpa [hy] using (@Run.done true d y)
  | perm e _ ih => exact Run.perm (e.map symW) ih
  | @two t a b r op ka kb ha hn hnd hnin _ ih =>
    simp only [List.map_cons] at ih ⊢
    have kn (w) (z : List Nat) (b : Bool) : (kept b w z).map symW = kept b (symW w) (z.map symW) := by
      cases b <;> rfl
    rw [kn,kn,hop] at ih
    apply Run.two op ka kb ha _ _ _ ih
    · rw [←hop,←h0];exact fun e => hn (symW_inj e)
    · rw [←hop];intro e;exact hnd (symW_inj (e.trans hd.symm))
    · rw [←hop];intro e
      have hit : symW (opD d op a b) ∈ (a::b::r).map symW := e
      obtain ⟨v,hv,eq⟩ := List.mem_map.mp hit
      exact hnin ((symW_inj eq) ▸ hv)

def posRow (link : Nat→Nat→Nat) (m : Nat) (book : Book) (i : Nat) : Bool :=
  let x:=link m i
  if x=4095 then
    let q:=bankPath m book 12 i
    areaCheck328 m (book.record i).1 q.1 q.2
  else if x=0 then projectedRow m book i else
    let j:=x-1
    decide (j < i) && ((book.record j).1 == (book.record i).1) &&
    (symW (dom328 m) == dom328 m) && (symW (target328 &&& dom328 m) == (target328 &&& dom328 m)) &&
    ((bankPath m book 12 i).1.map symW).isPerm (bankPath m book 12 j).1

theorem posSound (link : Nat→Nat→Nat) (m : Nat) (book : Book) (hd : dom328 m &&& mask256 = dom328 m)
    (hm : m < 128) (pri : deps328 m) (num : ∀ j<book.count,posRow link m book j = true) :
    ∀ s j, j<book.count → (book.record j).1=s →
    ∀ t ≤ s, ¬ RunD true (dom328 m) (target328 &&& dom328 m) t (bankPath m book 12 j).1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro j
    induction j using Nat.strong_induction_on with
    | ind j prev =>
      intro hj hcap t ht hr
      have hh := num j hj
      unfold posRow at hh
      dsimp only at hh
      split at hh
      next => exact areaCheck_ok328 pri hh (hcap ▸ ht) hr
      next =>
        split at hh
        case isFalse _ =>
          simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at hh
          obtain ⟨⟨⟨⟨less,cap⟩,symD⟩,symY⟩,perm⟩ := hh
          exact prev _ less (less.trans hj) (cap.trans hcap) _ ht (Run.perm perm (symRun symD symY hr))
        case isTrue _ =>
          rw [projectedRow_eq hm hd] at hh
          simp only [cachedRow,Bool.and_eq_true,bne_iff_ne,hcap] at hh
          obtain ⟨hne,hn⟩ := hh
          cases t with
          | zero => exact hne (zero_done hr rfl)
          | succ t =>
            have pos : (s==0)=false := beq_eq_false_iff_ne.mpr (by omega)
            simp only [pos,Bool.false_or,Bool.not_eq_true'] at hn
            let ws := (bankPath m book 12 j).1
            let ops := (bankPath m book 12 j).2
            let F (g : Nat × Nat × Nat) (zs : Bank) := !(cachedCut m book (s-1) (scopesPos m (book.picks j) ops) g zs)
            have hf (g) (zs) (hz : RunD true (dom328 m) (target328 &&& dom328 m) t zs) :
                F g zs = true := by
              simp only [F,Bool.not_eq_true']
              cases h : cachedCut m book (s-1) (scopesPos m (book.picks j) ops) g zs with
              | false => rfl
              | true =>
                exact False.elim (cachedCut_sound hd pri
                  (fun e he hcap => ih (s-1) (by omega) e he hcap) h (by omega) hz)
            let Fc (g : Nat × Nat × Nat) (zs : Bank) := coversP true (rowPairs m) zs && F g zs
            have hfc g zs (hz : RunD true (dom328 m) (target328 &&& dom328 m) t zs) : Fc g zs = true :=
              by simpa only [Fc,Bool.and_eq_true] using And.intro (coversP_ok hd (rowPairs m) (rowPairsOK _ hm) hz) (hf _ _ hz)
            have hn' := nextD_of_run_le68 hr (show t ≤ s-1 by omega) Fc hfc
            have he : s-1+2 = s+1 := by omega
            rw [he] at hn'
            rw [stepCov_eq _ _ _ _ _ _ hd (rowPairsOK _ hm)] at hn
            exact Bool.noConfusion (hn.symm.trans hn')

theorem posWindow {m : Nat} (link : Nat→Nat→Nat) (book : Book) (hd : dom328 m &&& mask256 = dom328 m)
    (hm : m < 128) (pri : deps328 m) (num : ∀ j<book.count,posRow link m book j=true)
    (root : childCut m book (lb328 m-1) [] [] ((roots328 m).map (· &&& dom328 m)) = true) :
    runWindow328 m := by
  apply childCut_sound hd pri _ root
  intro j hj hb
  exact posSound link m book hd hm pri num _ j hj hb

end PEqualNP.Outside.L_meta_32836_aux.Cubes
namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
def leafTwin328 (m i : Nat) : Nat :=
  let j:= i/64
  let w : Nat := match m with
    | 63 => 0x2b02a029026025000000000000028027000022000000000000000000000000000000000000000000000018017000000000000000000000000000000000005004003002000000000000000000000000000000000
    | 79 => 0x6000005000000000002000000
    | 95 => 0x1e01d01c01b01a019018000000000000000000016015000000000000000000000000000000000000000000000000000000003002007006000000000000000000000000
    | 106 => 0xd00b00a008007000000000000000000000004003000000000000
    | 111 => 0x3000000000
    | 123 => 0xfff02e02d02c02b000000000000000ffffffffffff018fff016fff014012011fff00ffff00b00d00a000fff000fff000000000000fff000fff000000000000000ffffff004003000000000000
    | 126 => (if j < 1 then 0x2102001fffffff017fff01501b01a01400002801c000000000000000000000ffffff000000fff000000000000000000000000ffffff000000000fff000000fff000000000fff000000000000000000fff005fff003fff000000fff000000000 else 0x55000000052000000ffffff03503203103002f02e02d02cffffff029024023022)
    | 127 => (if j < 22 then (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then 0xfff000fff000ffffff000000000ffffff000000000000000000000000000000fff000000000fff000000fff000000000000fff000fff00e00d00c00b009007ffffff000000004000000000000000000000000fff000000000000000 else 0xfffffffffffffff000000fffffffff000fff000000000000000ffffff000fff000000000000fff000000fff000000000000000000000000000ffffff000000000000000fff000fff000000000000000fff000000000ffffff000000000000) else (if j < 3 then 0xfff000fff000000000000000000000000000000000000000000000000000000000000000000000fff000000000ffffff000000000000000000000000000000ffffffffffff000000000000fff000000000000000000000000000000 else (if j < 4 then 0xffffffffffffffffffffffffffffffffffff000000000000000000000000000000fff000fff000000000000000fff0b0095fff000000000000000000fff000000000000000000fff000ffffff000000000000fffffffff000000fff000000 else 0xfff000fff000000000000000000fff000000000000fff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff000000))) else (if j < 8 then (if j < 6 then 0x4f000000000000fff000000fff000000000fff000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffff000fff000000000000000000000000000000fffffffffffffffffffff000fff000000000 else (if j < 7 then 0xfff000000000000fff00000000000019b1981970001a91a8000000000000000000000000fff000000000fff19900000000000000000000019119018f000000000000000fff178fff175000fff000fff04efff000000176 else 0xfff0ac0c50c0000ffffff1b9fff000fff0c20000000001ef1ee000000000fff1cb1c9fff0001e60000001e30000000001df0000000000000c1000000000000000000000000000000000000000000000000000000000000000fff000000000000)) else (if j < 9 then 0x23c23b23a0000000000001cc1c01bb00023123022f0000000000002262252221cf1cd1bf1be0000000001ce00000000021c21b21a00000000000021121020f20e20b1bd1bc000000000000000000000000000ffffff0cc0cb0ca0c9ffffff else (if j < 10 then 0x3102001f03afff02a02903002f01e00226e26d26c26b000000000000000000000000fff1d91d81d71d61d51d11d41d31c81c71c6fff1b81c21c41b7000fffffffff251fff000000000000000000fffffffffffffff2460000000001d01c1000 else 0x6005f05e05d05c04d04c04bfff049047ffffff06cfff06a069048068067fff065064053fff051fff04404307307207107006ffff05b05afff06206104204104003f03efff03cfff02d02c02b025fff022ffffff037036035fff02e023fff032)))) else (if j < 16 then (if j < 13 then (if j < 12 then 0xa00d514dffffffffffffffffffffffffffffff0f30f20b20970f10f00ef0ee0ed0ec0ebfff1221161111010b609b13113012f12912a128127126125fff12c12b0880b712e124084083082081080fffffffffffffff07a079fffffffff075fff else 0x94fffffffff145fff14214114013ffff09d14313e13d13cfff1231371361351340b90b8fff13813a1330d8fff0af0ad0d40d30d20d1fff0cffff08f08e08d08c087086fff08a089085156155154fff1530bc0ae0d615215115014ffff14e0a1) else (if j < 14 then 0xfff158fff12111f12011e11c11d11b11a11911511711811411311211010e10f10d10c10b10a109108107106105102104100ffffffffffffffffffffffffffffff0bf0befff0b50b40b30ba0ab0aa0a90a80a70a60a50a4fff0a209a09909809c else (if j < 15 then 0xfffffffffffffffffffffffffffffffff3a93a8fff3a63a43a33a2ffffff39d39f39c000000fff000000000000000ffffff000000000000000ffffff00039539400000000000016a169167168166165164ffffffffffffffffffffffffffffff else 0xffffffffffff000000fff3dc3db3da3d93d83d73d63d5ffffff000000000fff000000fff0000003d2fff3d03cf000000000000000000000000ffffff000fff000000000000ffffff3c63c53c43c3000000000000000fff))) else (if j < 19 then (if j < 17 then 0xffffff000000000000000000000417000000000000416000fffffffffffffffffffffffffffffffff000000000000fff000000000000000000000fff000000000000000000000000000fff000000000000000000000000ffffff3fd3fcfff else (if j < 18 then 0x440ffffff43a439438437435433434432430fffffffffffffffffffff000000000fff000000fff43d43c000462000000fff000000000000000fff43bfff00000041b41a419fff415414413412411409408fff40d40b40c410407000000000000 else 0xfff000000000000000000000fff0000000000000000000000000000000000004a90000000000000000000004a1000000000000ffffff496495fff000000000000000000000000ffffffffffffffffff000ffffffffffffffffff444443442441)) else (if j < 20 then 0xfff000000000000fff000000000fff000fff000000000000000000000ffffffffffffffffff000000000000ffffffffffffffffff000000fff000fff0000000000000004c1fff4bf4bbfff000fff0000000004bc000000000000fff000000000 else (if j < 21 then 0x53c000000000538000000534533000000000fff0000004b9fff4b74b64b54b44b34b14b04ae4af4b24ad00000000000050e50d000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffff else 0xfff52152051f51e51b51a51951851751651551351451251151050f50c50b50a509508507fffffffffffffffffffff4ff4fe4fd4fc4eefffffffffffffffffffff4f8fff4f6000ffffff4f400054b000000ffffff4f34f20000004ef4f0000))))) else (if j < 33 then (if j < 27 then (if j < 24 then (if j < 23 then 0xfff000000000fff000000000000000000000000000fff0000000005ab0000000005a75a6000000000000000ffffff599598597fff000000000000000000000000ffffffffffffffffffffffffffffff000587586000000000000fffffffff else 0xfff000fff000fff000000000000000000000000000000000000000000fff000fff000000000000000000000fff5dc5db5da5d95cafff000000000000000000fff000fff000000000000000000000000000000000000000000fffffffffffffff) else (if j < 25 then 0xffffffffffff000000000000000000000000000000000000000000000000000000000000000000000fff000000ffffffffffffffffffffffffffffffffffff000000000000000000000000000fff0000000000005ce000000000fff else (if j < 26 then 0x677676000000000000000000000fff000000000ffffff000000000fff00065f65dfff000000000000000000000000000000fff000000000000000000000000fffffffffffffffffffff000fff000000000000000000 else 0xfffffffff00000000000000068ffff68cfff000fff000000000000fffffffff68bffffff66a00000000068900000000000000000000000000000069700000000000067d67c67b67a000fff000000000000000000000000000000000fff000))) else (if j < 30 then (if j < 28 then 0x69d69c69b69a699688687686685684683fff68168067f67e669000000ffffffffffff000fff000fff000000000000000fff66f66dfff000000000000000000000000fffffffff else (if j < 29 then 0xfffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000ffffff000ffffff000fff000000fffffffffffffffffffff000ffffff000000000000000000000000000000000000000000000000 else 0xfff000000000000000000000fff000000000000000000000000ffffff000fffffffff000000ffffff000ffffffffffffffffffffffffffffff000000000000000000ffffff000000ffffff000ffffffffffffffffffffffffffffffffffff)) else (if j < 31 then 0xffffffffffff000000000fff000000fff000000000000000000000000000000fff000000000000000ffffff000ffffff000000642641640fff63f5bd63e000000000000000000000000000000000000000000000000000000000000fff else (if j < 32 then 0xffffff000000000fffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000007cd7cc000000000000fff00078c78a000756755754000 else 0x759758757fff000000000000000000000000000000fff000000000ffffff000000fff000000000000000000fff000000000646645644fff5d55b75be643000fff000000000000000000000000000000000000000000000000000000000000000)))) else (if j < 38 then (if j < 35 then (if j < 34 then 0x5e861161060f60e60d5c0fff5b85b65bcfff5ba5b95b55b45b35b2fff5b05af000000000000000000000000000000000000000000000000000000000000ffffff00000000000000000000000084c0000007e17e07df7de7dd7dc7db7da78f7d9 else 0x62d62c62b62a629628627626625624623621620ffffffffffffffffffffffffffffff5d7fff5d35d25d15c95c85c75c6ffffff602ffffff5fffff5fb5fa5f95f8fff5fd5f35f25f15f05ef5eefff5ea5e95cd5ccfff5ec5e66136125d05f75f6) else (if j < 36 then 0x828827fff0000008fa000000fff000000fff8f3000000fffffffffffffffffffffffffff825824fff8228207a67a57a4ffffff7877a179d000654653652651650fffffffffffffffffffff648fff63963863763663563463363263163062f62e else (if j < 37 then 0xffffffffffffffffff836835834833fff83183082fffffff82c82b81581482690d90c90b908907906905904903fffffffffffffffffffffffffffffffff000fff91190a909fff000fff000000000000000000000000000000000000000000fff else 0xfff77e7b1fffffffff000000000000000000ffffff7b300096f000000ffffff7b2fff00000000096500000000095f00000000000095b000000000000ffffff95094f94e000000000000000000000000000000000fffffffffffffffffffff000))) else (if j < 41 then (if j < 39 then 0xfff768fff767fff764ffffffffffffffffffffffffffffffffffffffffff751750ffffff74dffffff72f9a3000000000000000fffffffffffffffffffff000000fffffffff000fff97a9799789779769757c17c07bfffffffffffff7ba7b97b8 else (if j < 40 then 0xfffffffff7e67e57e47e37e27947957937927917907867857847b07af7ae7897887ad7ac7ab7aafff7a87a77d87d77d67d578e78d7d47d37d27d17d0783782fff78077d77c77b77977a778fff776775774773772771770fff76ffff76cffffff else 0x85a859858ffffff855854fff83c83b83a83983883785385285185084f84e817fff81381181281080e80f80d80c80a80b8098088058078068047fc7fe8038028017fd8007ff7fb7fa7f97f67f77f87f57f47f37f27f1ffffff7ee7ed7ecffffff)) else (if j < 42 then 0xffffffffffffa6cfffa6bfffa68fffffffffffffffffffffffffffffffff000000ffffff000ffffffffffffffffffffffffffffffffffffffffff000ffffffffffffffffff00086a86b86986886586786686486386085f85e86186285d85c85b else (if j < 43 then 0xfff000fff000000fffaaaaa9000000000000000000000ffffffffffffa9b000000fff000000000000000000a95fff000fff000a8cfffa8bfffa88fff000000ffffff000fff000a83fff000fff000 else 0xffffff000aee000000ffffff000ac4ac2ac1ac0abfabeabcabbabdabaab9ab8ab7ab6ab5fff000000fff000000000000000000000000acd000000000fffffffffac3000000000000000000))))))
    | _ => 0
  (w >>> (12*(i%64))) &&& 4095

end PEqualNP.Outside.L_meta_32836_aux.Cubes


namespace PEqualNP.Outside.L_meta_32836_aux.Witness
open PEqualNP.CircuitLowerBounds

def ed : List ℕ := [0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ed.length / 2,
  (List.ofFn x).getD (ed.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (ed.getD (2*i+1) 0) false = true)

def gs : List Gate := [
  ⟨.or, [0, 4]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [4, 1]⟩,
  ⟨.or, [3, 6]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [1, 8]⟩,
  ⟨.and, [5, 9]⟩,
  ⟨.and, [11, 12]⟩,
  ⟨.or, [10, 13]⟩,
  ⟨.or, [15, 16]⟩,
  ⟨.and, [14, 17]⟩,
  ⟨.or, [18, 19]⟩,
  ⟨.and, [2, 7]⟩,
  ⟨.or, [20, 21]⟩]

theorem legal : (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    gs.length = 15 := by simp [gs]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,22⟩ (List.ofFn x) = target x := by decide +kernel

end PEqualNP.Outside.L_meta_32836_aux.Witness

namespace PEqualNP.Outside.L_meta_32836_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_32836_aux.Core

def targetBits : Nat := 0xfffffffffffffffffffffffefffffffeffffffeeffffeeeeffeeffaaeeccaa00
def minorDom : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def minorBits : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0f0e0f0f0e0e0f0e0f0a0e0c0a00
def minorRoots : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem gainFromMinor (h : prior328 127) : Lower true minorDom minorRoots minorBits 13 := by
  have h' : Lower true (dom328 127) (roots328 127) target328 13 := h
  exact lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000,16), (0xffffffff000000000000000000000000ffffffff00000000,32), (0xffffffffffffffff0000000000000000,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) h'

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem lift36 (h : prior328 127) : Lower true mask256 xs256 targetBits 14 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(xs256.getD 2 0,128,132)] (by decide +kernel) (by decide +kernel) (gainFromMinor h)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem goal_eq_f' : ∀ r : Fin 256, targetBits.testBit r.val = Witness.target (pt8 r.val) := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem notGateLower (binaryLower : Lower true mask256 xs256 targetBits 14) (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Witness.target x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 15 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = targetBits &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit gates xs256 r hlt (fun g' hg' => (hfan g' hg').1)
      have h2 := congrArg (fun l => l.getD o false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN gates xs256).map (·.testBit r)).getD o false =
          ((execN gates xs256).getD o 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN gates xs256)[o]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt8 r)).trans (goal_eq_f' ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
  have hav_out : Avail true mask256 bank ((execN gates xs256).getD o 0) := by
    by_cases hi : o < (execN gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := binaryLower p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem closeFromMinor (h : prior328 127) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfan _ hcompute
  by_cases has : ∃ g ∈ gates, isNotGate g = true
  · have fan : ∀ g ∈ gates, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨op, inputs⟩ := hfan g hg
      refine ⟨?_,inputs⟩
      rcases op with h|h|h <;> simp [h]
    have bound := notGateLower (lift36 h) gates o fan hcompute has
    exact ⟨Witness.gs,22,Witness.legal.1,(Witness.legal.2.trans_le bound),Witness.correct⟩
  · refine ⟨gates,o,?_,le_rfl,hcompute⟩
    intro g hg
    obtain ⟨op,inputs⟩ := hfan g hg
    refine ⟨?_,inputs⟩
    rcases op with a|b|c
    · exact Or.inl a
    · exact Or.inr b
    · exact False.elim (has ⟨g,hg,by simp [isNotGate,c]⟩)

end PEqualNP.Outside.L_meta_32836_aux

namespace PEqualNP.Outside.L_meta_32836_aux.Cubes
open PEqualNP.Outside.L_meta_32836_aux.Core
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def verifiedBook (m : Nat) : Book := ⟨count328 m,record328 m,hint328 m,sliceList328 m⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def rootOK (m : Nat) := childCut m (verifiedBook m) (lb328 m-1) [] [] ((roots328 m).map (· &&& dom328 m))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def batchOK (m b : Nat) : Bool := (List.range 16).all (fun j=>
  let i := j+16*b
  count328 m ≤ i || posRow leafTwin328 m (verifiedBook m) i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fromBatches {m : Nat} (hm : m < 128) (pri : deps328 m) (hd : dom328 m &&& mask256 = dom328 m)
    (hr : rootOK m = true) (hb : ∀ b<(count328 m+15)/16,batchOK m b = true) : runWindow328 m := by
  apply posWindow leafTwin328 (verifiedBook m) hd hm pri _ hr
  intro i hi
  change i < count328 m at hi
  have H := hb (i/16) (by omega)
  have hh := List.all_eq_true.mp H (i % 16) (List.mem_range.mpr (by omega))
  rw [Nat.mod_add_div] at hh
  simpa only [decide_eq_false (Nat.not_le.mpr hi),Bool.false_or] using hh
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_21 : rootOK 21 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_21 (pri : deps328 21) : runWindow328 21 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_21
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_39 : rootOK 39 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_39 (pri : deps328 39) : runWindow328 39 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_39
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_42 : rootOK 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_42 (pri : deps328 42) : runWindow328 42 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_42
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_45 : rootOK 45 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_45 (pri : deps328 45) : runWindow328 45 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_45
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_47 : rootOK 47 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_47_0 : batchOK 47 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_47 (pri : deps328 47) : runWindow328 47 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_47
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_47_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_51 : rootOK 51 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_51 (pri : deps328 51) : runWindow328 51 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_51
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_55 : rootOK 55 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_55_0 : batchOK 55 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_55 (pri : deps328 55) : runWindow328 55 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_55
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_55_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_57 : rootOK 57 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_57 (pri : deps328 57) : runWindow328 57 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_57
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_59 : rootOK 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_59_0 : batchOK 59 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_59 (pri : deps328 59) : runWindow328 59 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_59
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_59_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_61 : rootOK 61 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_61_0 : batchOK 61 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_61 (pri : deps328 61) : runWindow328 61 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_61
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_61_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_63 : rootOK 63 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_63_0 : batchOK 63 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_63_1 : batchOK 63 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_63_2 : batchOK 63 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_63_3 : batchOK 63 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_63 (pri : deps328 63) : runWindow328 63 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_63
  intro j hj
  change j < 4 at hj
  interval_cases j
  · exact ok_63_0
  · exact ok_63_1
  · exact ok_63_2
  · exact ok_63_3

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_69 : rootOK 69 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_69 (pri : deps328 69) : runWindow328 69 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_69
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_74 : rootOK 74 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_74 (pri : deps328 74) : runWindow328 74 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_74
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_79 : rootOK 79 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_79_0 : batchOK 79 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_79 (pri : deps328 79) : runWindow328 79 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_79
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_79_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_83 : rootOK 83 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_83 (pri : deps328 83) : runWindow328 83 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_83
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_86 : rootOK 86 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_86 (pri : deps328 86) : runWindow328 86 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_86
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_87 : rootOK 87 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_87_0 : batchOK 87 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_87 (pri : deps328 87) : runWindow328 87 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_87
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_87_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_89 : rootOK 89 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_89 (pri : deps328 89) : runWindow328 89 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_89
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_91 : rootOK 91 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_91_0 : batchOK 91 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_91 (pri : deps328 91) : runWindow328 91 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_91
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_91_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_92 : rootOK 92 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_92 (pri : deps328 92) : runWindow328 92 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_92
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_93 : rootOK 93 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_93_0 : batchOK 93 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_93 (pri : deps328 93) : runWindow328 93 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_93
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_93_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_94 : rootOK 94 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_94_0 : batchOK 94 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_94 (pri : deps328 94) : runWindow328 94 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_94
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_94_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_95 : rootOK 95 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_95_0 : batchOK 95 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_95_1 : batchOK 95 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_95_2 : batchOK 95 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_95 (pri : deps328 95) : runWindow328 95 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_95
  intro j hj
  change j < 3 at hj
  interval_cases j
  · exact ok_95_0
  · exact ok_95_1
  · exact ok_95_2

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_97 : rootOK 97 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_97 (pri : deps328 97) : runWindow328 97 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_97
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_98 : rootOK 98 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_98 (pri : deps328 98) : runWindow328 98 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_98
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_103 : rootOK 103 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_103_0 : batchOK 103 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_103 (pri : deps328 103) : runWindow328 103 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_103
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_103_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_104 : rootOK 104 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_104 (pri : deps328 104) : runWindow328 104 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_104
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_106 : rootOK 106 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_106_0 : batchOK 106 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_106_1 : batchOK 106 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_106 (pri : deps328 106) : runWindow328 106 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_106
  intro j hj
  change j < 2 at hj
  interval_cases j
  · exact ok_106_0
  · exact ok_106_1

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_109 : rootOK 109 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_109_0 : batchOK 109 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_109 (pri : deps328 109) : runWindow328 109 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_109
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_109_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_111 : rootOK 111 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_111_0 : batchOK 111 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_111 (pri : deps328 111) : runWindow328 111 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_111
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_111_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_115 : rootOK 115 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_115_0 : batchOK 115 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_115 (pri : deps328 115) : runWindow328 115 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_115
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_115_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_116 : rootOK 116 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_116 (pri : deps328 116) : runWindow328 116 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_116
  intro j hj
  change j < 0 at hj
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_117 : rootOK 117 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_117_0 : batchOK 117 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_117 (pri : deps328 117) : runWindow328 117 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_117
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_117_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_118 : rootOK 118 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_118_0 : batchOK 118 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_118 (pri : deps328 118) : runWindow328 118 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_118
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_118_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_119 : rootOK 119 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_119_0 : batchOK 119 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_119_1 : batchOK 119 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_119_2 : batchOK 119 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_119_3 : batchOK 119 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_119_4 : batchOK 119 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_119 (pri : deps328 119) : runWindow328 119 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_119
  intro j hj
  change j < 5 at hj
  interval_cases j
  · exact ok_119_0
  · exact ok_119_1
  · exact ok_119_2
  · exact ok_119_3
  · exact ok_119_4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_121 : rootOK 121 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_121_0 : batchOK 121 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_121 (pri : deps328 121) : runWindow328 121 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_121
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_121_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_123 : rootOK 123 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_123_0 : batchOK 123 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_123_1 : batchOK 123 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_123_2 : batchOK 123 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_123_3 : batchOK 123 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_123 (pri : deps328 123) : runWindow328 123 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_123
  intro j hj
  change j < 4 at hj
  interval_cases j
  · exact ok_123_0
  · exact ok_123_1
  · exact ok_123_2
  · exact ok_123_3

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_124 : rootOK 124 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_124_0 : batchOK 124 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_124 (pri : deps328 124) : runWindow328 124 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_124
  intro j hj
  change j < 1 at hj
  interval_cases j
  · exact ok_124_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_125 : rootOK 125 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_125_0 : batchOK 125 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_125_1 : batchOK 125 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_125_2 : batchOK 125 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_125_3 : batchOK 125 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_125_4 : batchOK 125 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_125 (pri : deps328 125) : runWindow328 125 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_125
  intro j hj
  change j < 5 at hj
  interval_cases j
  · exact ok_125_0
  · exact ok_125_1
  · exact ok_125_2
  · exact ok_125_3
  · exact ok_125_4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_126 : rootOK 126 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_126_0 : batchOK 126 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_126_1 : batchOK 126 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_126_2 : batchOK 126 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_126_3 : batchOK 126 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_126_4 : batchOK 126 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_126_5 : batchOK 126 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_126 (pri : deps328 126) : runWindow328 126 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_126
  intro j hj
  change j < 6 at hj
  interval_cases j
  · exact ok_126_0
  · exact ok_126_1
  · exact ok_126_2
  · exact ok_126_3
  · exact ok_126_4
  · exact ok_126_5

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rootOK_127 : rootOK 127 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_0 : batchOK 127 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_1 : batchOK 127 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_2 : batchOK 127 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_3 : batchOK 127 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_4 : batchOK 127 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_5 : batchOK 127 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_6 : batchOK 127 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_7 : batchOK 127 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_8 : batchOK 127 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_9 : batchOK 127 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_10 : batchOK 127 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_11 : batchOK 127 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_12 : batchOK 127 12 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_13 : batchOK 127 13 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_14 : batchOK 127 14 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_15 : batchOK 127 15 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_16 : batchOK 127 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_17 : batchOK 127 17 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_18 : batchOK 127 18 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_19 : batchOK 127 19 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_20 : batchOK 127 20 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_21 : batchOK 127 21 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_22 : batchOK 127 22 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_23 : batchOK 127 23 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_24 : batchOK 127 24 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_25 : batchOK 127 25 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_26 : batchOK 127 26 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_27 : batchOK 127 27 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_28 : batchOK 127 28 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_29 : batchOK 127 29 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_30 : batchOK 127 30 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_31 : batchOK 127 31 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_32 : batchOK 127 32 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_33 : batchOK 127 33 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_34 : batchOK 127 34 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_35 : batchOK 127 35 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_36 : batchOK 127 36 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_37 : batchOK 127 37 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_38 : batchOK 127 38 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_39 : batchOK 127 39 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_40 : batchOK 127 40 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_41 : batchOK 127 41 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_42 : batchOK 127 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_43 : batchOK 127 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_44 : batchOK 127 44 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_45 : batchOK 127 45 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_46 : batchOK 127 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_47 : batchOK 127 47 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_48 : batchOK 127 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_49 : batchOK 127 49 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_50 : batchOK 127 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_51 : batchOK 127 51 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_52 : batchOK 127 52 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_53 : batchOK 127 53 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_54 : batchOK 127 54 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_55 : batchOK 127 55 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_56 : batchOK 127 56 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_57 : batchOK 127 57 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_58 : batchOK 127 58 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_59 : batchOK 127 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_60 : batchOK 127 60 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_61 : batchOK 127 61 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_62 : batchOK 127 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_63 : batchOK 127 63 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_64 : batchOK 127 64 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_65 : batchOK 127 65 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_66 : batchOK 127 66 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_67 : batchOK 127 67 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_68 : batchOK 127 68 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_69 : batchOK 127 69 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_70 : batchOK 127 70 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_71 : batchOK 127 71 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_72 : batchOK 127 72 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_73 : batchOK 127 73 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_74 : batchOK 127 74 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_75 : batchOK 127 75 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_76 : batchOK 127 76 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_77 : batchOK 127 77 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_78 : batchOK 127 78 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_79 : batchOK 127 79 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_80 : batchOK 127 80 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_81 : batchOK 127 81 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_82 : batchOK 127 82 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_83 : batchOK 127 83 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_84 : batchOK 127 84 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_85 : batchOK 127 85 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_86 : batchOK 127 86 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_87 : batchOK 127 87 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_88 : batchOK 127 88 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_89 : batchOK 127 89 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_90 : batchOK 127 90 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_91 : batchOK 127 91 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_92 : batchOK 127 92 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_93 : batchOK 127 93 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_94 : batchOK 127 94 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_95 : batchOK 127 95 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_96 : batchOK 127 96 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_97 : batchOK 127 97 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_98 : batchOK 127 98 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_99 : batchOK 127 99 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_100 : batchOK 127 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_101 : batchOK 127 101 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_102 : batchOK 127 102 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_103 : batchOK 127 103 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_104 : batchOK 127 104 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_105 : batchOK 127 105 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_106 : batchOK 127 106 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_107 : batchOK 127 107 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_108 : batchOK 127 108 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_109 : batchOK 127 109 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_110 : batchOK 127 110 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_111 : batchOK 127 111 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_112 : batchOK 127 112 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_113 : batchOK 127 113 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_114 : batchOK 127 114 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_115 : batchOK 127 115 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_116 : batchOK 127 116 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_117 : batchOK 127 117 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_118 : batchOK 127 118 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_119 : batchOK 127 119 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_120 : batchOK 127 120 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_121 : batchOK 127 121 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_122 : batchOK 127 122 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_123 : batchOK 127 123 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_124 : batchOK 127 124 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_125 : batchOK 127 125 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_126 : batchOK 127 126 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_127 : batchOK 127 127 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_128 : batchOK 127 128 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_129 : batchOK 127 129 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_130 : batchOK 127 130 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_131 : batchOK 127 131 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_132 : batchOK 127 132 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_133 : batchOK 127 133 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_134 : batchOK 127 134 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_135 : batchOK 127 135 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_136 : batchOK 127 136 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_137 : batchOK 127 137 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_138 : batchOK 127 138 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_139 : batchOK 127 139 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_140 : batchOK 127 140 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_141 : batchOK 127 141 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_142 : batchOK 127 142 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_143 : batchOK 127 143 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_144 : batchOK 127 144 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_145 : batchOK 127 145 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_146 : batchOK 127 146 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_147 : batchOK 127 147 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_148 : batchOK 127 148 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_149 : batchOK 127 149 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_150 : batchOK 127 150 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_151 : batchOK 127 151 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_152 : batchOK 127 152 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_153 : batchOK 127 153 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_154 : batchOK 127 154 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_155 : batchOK 127 155 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_156 : batchOK 127 156 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_157 : batchOK 127 157 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_158 : batchOK 127 158 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_159 : batchOK 127 159 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_160 : batchOK 127 160 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_161 : batchOK 127 161 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_162 : batchOK 127 162 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_163 : batchOK 127 163 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_164 : batchOK 127 164 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_165 : batchOK 127 165 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_166 : batchOK 127 166 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_167 : batchOK 127 167 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_168 : batchOK 127 168 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_169 : batchOK 127 169 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_170 : batchOK 127 170 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_171 : batchOK 127 171 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_172 : batchOK 127 172 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_173 : batchOK 127 173 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_174 : batchOK 127 174 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ok_127_175 : batchOK 127 175 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_127 (pri : deps328 127) : runWindow328 127 := by
  apply fromBatches (by decide) pri (by decide +kernel) rootOK_127
  intro j hj
  change j < 176 at hj
  interval_cases j
  · exact ok_127_0
  · exact ok_127_1
  · exact ok_127_2
  · exact ok_127_3
  · exact ok_127_4
  · exact ok_127_5
  · exact ok_127_6
  · exact ok_127_7
  · exact ok_127_8
  · exact ok_127_9
  · exact ok_127_10
  · exact ok_127_11
  · exact ok_127_12
  · exact ok_127_13
  · exact ok_127_14
  · exact ok_127_15
  · exact ok_127_16
  · exact ok_127_17
  · exact ok_127_18
  · exact ok_127_19
  · exact ok_127_20
  · exact ok_127_21
  · exact ok_127_22
  · exact ok_127_23
  · exact ok_127_24
  · exact ok_127_25
  · exact ok_127_26
  · exact ok_127_27
  · exact ok_127_28
  · exact ok_127_29
  · exact ok_127_30
  · exact ok_127_31
  · exact ok_127_32
  · exact ok_127_33
  · exact ok_127_34
  · exact ok_127_35
  · exact ok_127_36
  · exact ok_127_37
  · exact ok_127_38
  · exact ok_127_39
  · exact ok_127_40
  · exact ok_127_41
  · exact ok_127_42
  · exact ok_127_43
  · exact ok_127_44
  · exact ok_127_45
  · exact ok_127_46
  · exact ok_127_47
  · exact ok_127_48
  · exact ok_127_49
  · exact ok_127_50
  · exact ok_127_51
  · exact ok_127_52
  · exact ok_127_53
  · exact ok_127_54
  · exact ok_127_55
  · exact ok_127_56
  · exact ok_127_57
  · exact ok_127_58
  · exact ok_127_59
  · exact ok_127_60
  · exact ok_127_61
  · exact ok_127_62
  · exact ok_127_63
  · exact ok_127_64
  · exact ok_127_65
  · exact ok_127_66
  · exact ok_127_67
  · exact ok_127_68
  · exact ok_127_69
  · exact ok_127_70
  · exact ok_127_71
  · exact ok_127_72
  · exact ok_127_73
  · exact ok_127_74
  · exact ok_127_75
  · exact ok_127_76
  · exact ok_127_77
  · exact ok_127_78
  · exact ok_127_79
  · exact ok_127_80
  · exact ok_127_81
  · exact ok_127_82
  · exact ok_127_83
  · exact ok_127_84
  · exact ok_127_85
  · exact ok_127_86
  · exact ok_127_87
  · exact ok_127_88
  · exact ok_127_89
  · exact ok_127_90
  · exact ok_127_91
  · exact ok_127_92
  · exact ok_127_93
  · exact ok_127_94
  · exact ok_127_95
  · exact ok_127_96
  · exact ok_127_97
  · exact ok_127_98
  · exact ok_127_99
  · exact ok_127_100
  · exact ok_127_101
  · exact ok_127_102
  · exact ok_127_103
  · exact ok_127_104
  · exact ok_127_105
  · exact ok_127_106
  · exact ok_127_107
  · exact ok_127_108
  · exact ok_127_109
  · exact ok_127_110
  · exact ok_127_111
  · exact ok_127_112
  · exact ok_127_113
  · exact ok_127_114
  · exact ok_127_115
  · exact ok_127_116
  · exact ok_127_117
  · exact ok_127_118
  · exact ok_127_119
  · exact ok_127_120
  · exact ok_127_121
  · exact ok_127_122
  · exact ok_127_123
  · exact ok_127_124
  · exact ok_127_125
  · exact ok_127_126
  · exact ok_127_127
  · exact ok_127_128
  · exact ok_127_129
  · exact ok_127_130
  · exact ok_127_131
  · exact ok_127_132
  · exact ok_127_133
  · exact ok_127_134
  · exact ok_127_135
  · exact ok_127_136
  · exact ok_127_137
  · exact ok_127_138
  · exact ok_127_139
  · exact ok_127_140
  · exact ok_127_141
  · exact ok_127_142
  · exact ok_127_143
  · exact ok_127_144
  · exact ok_127_145
  · exact ok_127_146
  · exact ok_127_147
  · exact ok_127_148
  · exact ok_127_149
  · exact ok_127_150
  · exact ok_127_151
  · exact ok_127_152
  · exact ok_127_153
  · exact ok_127_154
  · exact ok_127_155
  · exact ok_127_156
  · exact ok_127_157
  · exact ok_127_158
  · exact ok_127_159
  · exact ok_127_160
  · exact ok_127_161
  · exact ok_127_162
  · exact ok_127_163
  · exact ok_127_164
  · exact ok_127_165
  · exact ok_127_166
  · exact ok_127_167
  · exact ok_127_168
  · exact ok_127_169
  · exact ok_127_170
  · exact ok_127_171
  · exact ok_127_172
  · exact ok_127_173
  · exact ok_127_174
  · exact ok_127_175

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem minorCertified : prior328 127 := finish328 certified_21 certified_39 certified_42 certified_45 certified_47 certified_51 certified_55 certified_57 certified_59 certified_61 certified_63 certified_69 certified_74 certified_79 certified_83 certified_86 certified_87 certified_89 certified_91 certified_92 certified_93 certified_94 certified_95 certified_97 certified_98 certified_103 certified_104 certified_106 certified_109 certified_111 certified_115 certified_116 certified_117 certified_118 certified_119 certified_121 certified_123 certified_124 certified_125 certified_126 certified_127
end PEqualNP.Outside.L_meta_32836_aux.Cubes

theorem PEqualNP.Outside.L_meta_32836 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := PEqualNP.Outside.L_meta_32836_aux.closeFromMinor (PEqualNP.Outside.L_meta_32836_aux.Cubes.minorCertified)
