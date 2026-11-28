import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51762_aux
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
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
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
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
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
  cases b
  · simp [kept]
  · simp [kept,List.countP_cons]
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
theorem perm_erase_two {α : Type} [DecidableEq α] {rest:List α} {a' c' : α}
    (hnd : rest.Nodup) (hne : a' ≠ c') :
    rest.Perm (kept (decide (a' ∈ rest)) a' (kept (decide (c' ∈ rest)) c' ((rest.erase a').erase c'))):=by
  refine (List.perm_ext_iff_of_nodup hnd (nodup_kept _ a' _ (nodup_kept _ c' _ ((hnd.erase a').erase c')
    ((hnd.erase a').not_mem_erase)) (by
      rw [mem_kept]; rintro (⟨_,h⟩ | h)
      · exact hne h
      · exact hnd.not_mem_erase (List.mem_of_mem_erase h)))).2 ?_
  intro x
  rw [mem_kept,mem_kept,(hnd.erase a').mem_erase_iff,hnd.mem_erase_iff]
  by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;> simp_all
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
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) :=
        perm_erase_two hrest_nd hne_ac
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
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
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
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
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
theorem negD_eq_xor {d:Nat} (hd : d&&&mask256 = d) (w:Nat) :
    d^^^(w&&&d) = negD d w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have hdi:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at hdi ⊢
  cases hd' : d.testBit i <;> cases hw' : w.testBit i <;> simp_all
def availM (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  if m==0||m==d then true else
  let nm:=d^^^m
  bank.any (fun v=>v==m||v==nm)
theorem avail_of_availM {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail true d bank v ∧ v&&&d = v) {w:Nat}
    (hb : availM d pool w = true) : Avail true d bank w:=by
  unfold availM at hb; dsimp only at hb
  split at hb
  · rename_i hc
    simp only [Bool.or_eq_true,beq_iff_eq] at hc
    exact Or.inl hc
  · rw [List.any_eq_true] at hb
    obtain ⟨v,hv,he⟩:=hb
    simp only [Bool.or_eq_true,beq_iff_eq] at he
    obtain ⟨hav,hvm⟩:=hsup v hv
    rcases he with rfl | hnm
    · exact avail_of_eq hvm hav
    · have hneg:=avail_neg hd hav
      have he1 : negD d v&&&d = w&&&d:=by
        rw [← negD_mask,hvm,hnm,negD_eq_xor hd,negD_invol hd,Nat.and_assoc,Nat.and_self]
      exact avail_of_eq he1 hneg
def stepOp (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB true g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availM d st.2 om then st
    else if availM d st.2 g.2.1&&availM d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem stepOp_sound {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach true d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail true d bank v ∧ v&&&d = v) :
    ∃ bank',NatReach true d roots (stepOp d st g).1 bank' ∧ ∀ v ∈ (stepOp d st g).2,Avail true d bank' v ∧ v&&&d = v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availM hd hsup hab.1
        have hb:=avail_of_availM hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩),opD_mask_self d g.1 g.2.1 g.2.2⟩
        · exact ⟨avail_cons _ _ (hsup v hv).1,(hsup v hv).2⟩
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach true d roots st.1 bank → (∀ v ∈ st.2,Avail true d bank v ∧ v&&&d = v) →
      ∃ bank',NatReach true d roots (runOps d st ops).1 bank' ∧ ∀ v ∈ (runOps d st ops).2,Avail true d bank' v ∧ v&&&d = v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp d st g) bank1 hr1 hsup1
def checkPool (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availM dSub st.2)
def checkPoolG (dSub LSub s:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat) (ws:List Nat):Bool :=
  let c:=ws.countP (isConstB dSub)
  if decide (s + st.1 < LSub + c) then
    let st':=stepOp dSub st g
    decide (s + st'.1 < LSub + c)&&ws.all (availM dSub st'.2)
  else false
theorem checkPool_sound {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower true dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach true dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail true dSub bank v ∧ v&&&dSub = v)
    (hchk : checkPool dSub LSub s st ws = true) :
    ¬ RunD true d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail true dSub bank w:=fun w hw =>
    avail_of_availM hdSub hsb (List.all_eq_true.1 hall w hw)
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
theorem cpcs {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower true dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPoolG dSub LSub s (runOps dSub (0,rootsSub.map (·&&&dSub)) ops) g ws = true) :
    ¬ RunD true d (T&&&d) s ws:=by
  unfold checkPoolG at hchk; dsimp only at hchk
  split at hchk
  · simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
    have hsup0 : ∀ v ∈ rootsSub.map (·&&&dSub),Avail true dSub rootsSub v ∧ v&&&dSub = v:=by
      intro v hv'; obtain ⟨r,hr,rfl⟩:=List.mem_map.1 hv'
      exact ⟨Or.inr (Or.inl ⟨r,hr,by rw [Nat.and_assoc,Nat.and_self]⟩),by rw [Nat.and_assoc,Nat.and_self]⟩
    obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub.map (·&&&dSub)) rootsSub rfl hsup0
    obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
    exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
  · contradiction
theorem checkRootSub_sound {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower true dSub rootsSub TSub LSub)
    (hchk : checkPool dSub LSub s (0,rootsSub.map (·&&&dSub)) ws = true) :
    ¬ RunD true d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub.map (·&&&dSub),Avail true dSub rootsSub v ∧ v&&&dSub = v:=by
    intro v hv'; obtain ⟨r,hr,rfl⟩:=List.mem_map.1 hv'
    exact ⟨Or.inr (Or.inl ⟨r,hr,by rw [Nat.and_assoc,Nat.and_self]⟩),by rw [Nat.and_assoc,Nat.and_self]⟩
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub.map (·&&&dSub)) rootsSub rfl hsup0 hchk
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
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,bne_iff_ne] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1 hp.1.2 hall
  exact hp.2 heq
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
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==6 then 63 else if w==11 then 2047 else if w==13 then 8191 else if w==14 then 16383 else if w==19 then 524287 else if w==20 then 1048575 else if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let r:=(w^^^seed) % 1048573
  (r * r + r) % 1048573
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&1048575
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
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
def mkWire (dictB:Nat → Nat → Nat) (ndict dw dmask i:Nat):Nat :=
  if i < ndict then (dictB (i / 256) (i / 16 % 16) >>> (dw * (i % 16)))&&&dmask else 0
def addP (pm i d L:Nat) (rs:List Nat) (ops:List (Nat × Nat × Nat)):List (Nat × Nat × (Nat × List Nat)) :=
  if pm.testBit i then [(d,L,runOps d (0,rs.map (·&&&d)) ops)] else []
theorem mem_addP {pm i d L rs ops e} (h : e ∈ addP pm i d L rs ops) :
    pm.testBit i = true ∧ e = (d,L,runOps d (0,rs.map (·&&&d)) ops):=by
  unfold addP at h; split at h
  · rename_i ht; exact ⟨ht,List.mem_singleton.1 h⟩
  · simp at h
def isoOK (ms:List (Nat × Nat)) (d1 d2 T1 T2:Nat) (r1 r2:List Nat):Bool :=
  ms.all moveOK256&&(d1&&&mask256==d1)&&(applyMoves ms d2==d1) &&
    (applyMoves ms T2==T1)&&r2.all (fun r=>availB true d1 r1 (applyMoves ms r))
theorem lower_iso_b {d1 d2 T1 T2 L:Nat} {r1 r2:List Nat}
    (ms:List (Nat × Nat)) (h : isoOK ms d1 d2 T1 T2 r1 r2 = true)
    (h1 : Lower true d1 r1 T1 L) : Lower true d2 r2 T2 L:=by
  simp only [isoOK,Bool.and_eq_true,beq_iff_eq] at h
  exact lower_iso ms h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2 h1
def sliceOK (d dSub T TSub:Nat) (r rSub:List Nat) (singles:List (Nat × Nat × Nat)):Bool :=
  (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&r.all (fun x=>!x.testBit 0) &&
    (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub) &&
    !(isConstB d T)&&!(isConstB dSub TSub)&&r.all (availB true dSub rSub) &&
    decide (singles.map Prod.fst).Nodup &&
    singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (r.map (·&&&d)) e.1 e.2)
theorem lower_slice_b {d dSub T TSub L:Nat} {r rSub:List Nat}
    (singles:List (Nat × Nat × Nat))
    (h : sliceOK d dSub T TSub r rSub singles = true)
    (hprior : Lower true dSub rSub TSub L) : Lower true d r T (L + singles.length):=by
  simp only [sliceOK,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at h
  exact lower_slice h.1.1.1.1.1.1.1.1.1.1.1 h.1.1.1.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1.1.1.2
    h.1.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.2 h.1.1.1.1.1.2 h.1.1.1.1.2
    h.1.1.1.2 h.1.1.2 singles h.1.2 h.2 hprior
def essOKB (d T:Nat) (r:List Nat) (singles:List (Nat × Nat × Nat)):Bool :=
  (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&r.all (fun x=>!x.testBit 0) &&
    !(isConstB d T)&&decide (singles.map Prod.fst).Nodup &&
    singles.all (fun e=>essOK d (T&&&d) (r.map (·&&&d)) e.1 e.2)
theorem lower_ess_b {d T:Nat} {r:List Nat}
    (singles:List (Nat × Nat × Nat)) (h : essOKB d T r singles = true) :
    Lower true d r T (singles.length - 1):=by
  simp only [essOKB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at h
  exact lower_ess_count h.1.1.1.1.1.1 h.1.1.1.1.1.2 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 singles h.1.2 h.2
def mkReadSt (wireAt:Nat → Nat) (stPool:Nat → Nat) (idw:Nat):Nat → Nat → List Nat
  | 0,_=>[]
  | n + 1,p=>wireAt (fld (stPool (p / 128)) idw (p % 128)) :: mkReadSt wireAt stPool idw n (p + 1)
def mkSS (wireAt:Nat → Nat) (stPool:Nat → Nat) (stOffB:Nat → Nat → Nat) (idw offw s j:Nat):List Nat :=
  let v:=fld (stOffB s (j / 64)) offw (j % 64)
  mkReadSt wireAt stPool idw (v&&&15) (v >>> 4)
def mkReadOps (wireAt:Nat → Nat) (opPool:Nat → Nat) (opw idw idm:Nat):Nat → Nat → List (Nat × Nat × Nat)
  | 0,_=>[]
  | n + 1,p =>
    let code:=fld (opPool (p / 64)) opw (p % 64)
    (code&&&3,wireAt ((code >>> 2)&&&idm),wireAt ((code >>> (2 + idw))&&&idm)) ::
      mkReadOps wireAt opPool opw idw idm n (p + 1)
def mkPO (wireAt:Nat → Nat) (opPool:Nat → Nat) (opOffB:Nat → Nat → Nat) (opw idw idm ooffw s j:Nat):List (Nat × Nat × Nat) :=
  let v:=fld (opOffB s (j / 64)) ooffw (j % 64)
  mkReadOps wireAt opPool opw idw idm (v&&&15) (v >>> 4)
def bar (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov true dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov true dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz))
    | p :: ps =>
      !(nextD_cov true dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !((p :: ps).any fun e=>checkPoolG e.1 e.2.1 s e.2.2 g zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs'⟩,hpairs⟩:=hinit
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
theorem barP_eq (dm Y mp:Nat) (SD S N htAt idxH ori seed mkPools s i) :
    barP dm Y mp SD S N htAt idxH ori seed mkPools s i =
      bar dm Y mp SD S N htAt idxH ori seed
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s' - 1) e.2.2 g zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD true dm (T&&&dm) v ys → RunD true dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD true dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar dm (T&&&dm) mp SD S N htAt idxH ori seed mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD true dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP true pairs zs&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD true dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq true hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD true (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
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
-- [PNP-PREFIX-END]
def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00fefeaa00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefefe0000fefeeeeefefe0000fefeeeeefefe0000fefeeeeefefe0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeeaa00ffeeffeeeeeeaa00ffeeffeeeeeeaa00ffeeffeeeeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefeaa00fffeffeefefeaa00fffeffeefefeaa00fffeffeefefeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafaaaaafafaaaaafafa0000fafa0000fafaaaaafafaaaaafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcccccfcfcccccfcfc0000fcfc0000fcfcccccfcfcccccfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefeeeeefefeeeeefefe0000fefe0000fefeeeeefefeeeeefefe0000fefe0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffccffccffccffcccccc0000cccc0000ffccffccffccffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffaffaafffaffaafafaaa00fafaaa00fffaffaafffaffaafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcffccfffcffccfcfc0000fcfc0000fffcffccfffcffccfcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffeffeefffeffeefefeaa00fefeaa00fffeffeefffeffeefefeaa00fefeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeeeeeeeee00000000ffffffffeeeeeeeeeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaaaa00aa00ffffffffffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffffccffccffccffcc00000000ffffffffffccffccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffeeffeeffeeffeeaa00aa00ffffffffffeeffeeffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffcccccccccccccccccccc0000ffffffffcccccccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffeeeeeeeeeeeeeeeeeeee0000ffffffffeeeeeeeeeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffafaaaaafafaaaaafafa0000fffffffffafaaaaafafaaaaafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffcfcccccfcfcccccfcfc0000fffffffffcfcccccfcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffefeeeeefefeeeeefefe0000fffffffffefeeeeefefeeeeefefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffaaffaaffaaffaaaaaaaa00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffccffccffccffcccccc0000ffffffffffccffccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffeeffeeffeeffeeeeeeaa00ffffffffffeeffeeffeeffeeeeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffff0ff00fff0ff00f0f00000fffffffffff0ff00fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffaffaafffaffaafafaaa00fffffffffffaffaafffaffaafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffcffccfffcffccfcfc0000fffffffffffcffccfffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffeffeefffeffeefefeaa00fffffffffffeffeefffeffeefefeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffccffccffccffccffccffccffccffccaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xeeeecccceeeecccceeeecccceeeecccceeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0fafa0000fafa0000fafa0000fafa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfefefcfcfefefcfcfefefcfcfefefcfcfefe0000fefe0000fefe0000fefe0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaff00ffaaff00ffaaff00ffaaff00aaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffccffeeffccffeeffccffeeffcceeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffafff0fffafff0fffafff0fffafff0fafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffcfffefffcfffefffcfffefffcfefeaa00fefeaa00fefeaa00fefeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffccccccccffffffffcccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0aaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfceeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffffccffccffffffffffccffccffccffcc00000000ffccffcc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffccffccffffffffffccffccffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ff00ff0000000000ff00ff0000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffff0fff0fffffffffff0fff0ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffccffcc00000000ffccffcc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffcfffcfffffffffffcfffcffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffaaaa0000ffffffffaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeccccffffffffeeeecccceeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f00000f0f00000f0f00000f0f00000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafaf0f0fffffffffafaf0f0fafaaaaafafa0000fafaaaaafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefcfcfffffffffefefcfcfefeeeeefefe0000fefeeeeefefe0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaff00ffffffffffaaff00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffccffffffffffeeffccffeeffeeeeeeaa00ffeeffeeeeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0ff00f0f00000fff0ff00f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafff0fffffffffffafff0fffaffaafafaaa00fffaffaafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffcffccfcfc0000fffcffccfcfc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffcfffffffffffefffcfffeffeefefeaa00fffeffeefefeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfceeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffccffccffccffccffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffcfffcfffcfffcffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffeeeecccceeeecccceeeeeeeeeeeeeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcccccfcfcccccfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefefcfcfefefcfcfefeeeeefefeeeeefefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffeeffccffeeffccffeeffeeffeeffeeeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffafff0fffafff0fffaffaafffaffaafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffcfffcfffcfffcfffcffccfffcffccfcfc0000fcfc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffefffcfffefffcfffeffeefffeffeefefeaa00fefeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_224 : Nat := 0x100000001000000010000000100000001000000010000000100000001
def goal_224 : Nat := 0xffffffffffffffffffffffff00000000ffffffff000000000000000000000000
def roots_224 : List Nat := [xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffccccccccffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffff0f0f0f0ffffffffaaaaaaaaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcffffffffcccccccccccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffcfcfcfcffffffffeeeeeeeeeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffeeffeeffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0ffffffffff00ff00ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffff0fff0ffffffffffaaffaaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffffcfffcffffffffffccffccffccffcc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffcfffcffffffffffeeffeeffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeccccffffffffeeeeeeeeeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f00000f0f00000f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffafaf0f0fffffffffafaaaaafafaaaaafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffffffcfcccccfcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffefefcfcfffffffffefeeeeefefeeeeefefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaff00ffffffffffaaffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffccffccffffffffffccffccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffccffffffffffeeffeeffeeffeeeeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0ff00fff0ff00f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffafff0fffffffffffaffaafffaffaafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffcfffcfffffffffffcffccfffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffefffcfffffffffffeffeefffeffeefefeaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_41
def pG:List (Nat×Nat):=[(1,9),(1,33),(8,9),(8,40),(32,33),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_41.map (·&&&dom_41)
def gM:=goal_41&&&dom_41
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xc64ca
|3,0=>0xc64ca
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30300000000c0000000c020200000202
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 42 0x3ffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_41 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_41 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_41==dom_41)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_41 gM v ys):RunD true dom_41 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_41 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_41 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_41 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_41 roots_41 goal_41 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_41
theorem lowS_41:Lower true dom_41 roots_41 goal_41 4:=S_41.noCircuit
def isoMvS_73:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_73:Lower true dom_73 roots_73 goal_73 4:=lower_iso_b isoMvS_73 (by decide +kernel) lowS_41
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_41
def isoMvS_98:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_41
def isoMvS_104:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_41
def isoMvS_162:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_162:Lower true dom_162 roots_162 goal_162 4:=lower_iso_b isoMvS_162 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_224:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_224:Lower true dom_224 roots_224 goal_224 4:=lower_iso_b isoMvS_224 (by decide +kernel) lowS_41
namespace S_27
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,18),(3,11),(3,19),(8,9),(10,11),(10,26),(16,17),(16,18),(24,25),(24,26)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_27.map (·&&&dom_27)
def gM:=goal_27&&&dom_27
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x526b1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000f000f00c0c0c0ca0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 28 0xfffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_27 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_27 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_27==dom_27)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 gM v ys):RunD true dom_27 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_27 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_27 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_27 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_27
theorem lowS_27:Lower true dom_27 roots_27 goal_27 4:=S_27.noCircuit
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,32,34)] (by decide +kernel) lowS_41
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_slice_b [(0xa0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_98
namespace S_105
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(8,9),(8,40),(8,72),(32,33),(32,40),(32,96),(64,65),(64,72),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_105.map (·&&&dom_105)
def gM:=goal_105&&&dom_105
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xa3c7b36bad0b047
|4,0=>0x5ef5a56d164b08941ad53e3192943b0e7df
|5,0=>0x8401343d8911e8a
|6,0=>0x84013
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0000080800000c0c0000080b03000003030000020200000202c0800000c0800000c0800000c0b03000003030000030300000202404000004000000040400000400030000000300000002000000020000000000000000c0c00000c0101000001010000010100000100c0c00000c0000000c0c00000c0303000003030000030300000000c0c00000c0c00000c0000000c0202000002020000020200000202c0c0000000000000c0c000000030000000300000003000000030080800000808000008080000080303000003030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x3240324035240632407f240632e473d40c3240324b0324a093240328076543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 16 106 0x3ffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x204c1324d1404c1424c930409
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x200
|4,0=>0x62422200000000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf76530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x18
|4,0=>0x52000
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_104 4 roots_104 ops++addP pm 1 dom_97 4 roots_97 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_105 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_104 4 s (0,roots_104.map (·&&&dom_104)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_105 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_104 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_105==dom_105)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_105 gM v ys):RunD true dom_105 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_105 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_105 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_105 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_105 roots_105 goal_105 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_105
theorem lowS_105:Lower true dom_105 roots_105 goal_105 7:=S_105.noCircuit
def isoMvS_29:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=lower_iso_b isoMvS_29 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_58:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_43
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 4:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_27
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_27
def isoMvS_106:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_99
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_43
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 4:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 4:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_27
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 4:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_27
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 4:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_27
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 4:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_27
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 4:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_27
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_27
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_99
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_99
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 4:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_27
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 4:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_43
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 4:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_27
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_105
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xcccccccc,16,18)] (by decide +kernel) lowS_29
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,16,17)] (by decide +kernel) lowS_54
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_57
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_61
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(5,13),(5,21),(5,37),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,33),(32,40),(36,37),(36,44),(36,52),(48,49),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_61.map (·&&&dom_61)
def gM:=goal_61&&&dom_61
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb6d8e19fc8
|5,0=>0xa5e019bec497d24
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccc00cc00022002200220022cc88cc88cc88cc8b30033003300330000cc00cc0088008b333333300000000cccc0000cccc0003300330022002200c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x436109436104361084376104310543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x182
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x19
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dzo_57_4 5 roots_57 ops++addP pm 2 dom_53 4 roots_53 ops++addP pm 3 dom_41 4 roots_41 ops++addP pm 4 dom_29 4 roots_29 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_29 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_61==dom_61)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 gM v ys):RunD true dom_61 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_61 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_61 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_61 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_61 roots_61 goal_61 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_61
theorem lowS_61:Lower true dom_61 roots_61 goal_61 7:=S_61.noCircuit
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_slice_b [(0x5050505050505050,16,20)] (by decide +kernel) lowS_58
theorem lowS_107:Lower true dom_107 roots_107 goal_107 8:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_105
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_slice_b [(0xa000a000a000a000a000a000a000a,16,17)] (by decide +kernel) lowS_114
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_slice_b [(0x3030000030300000303000003030000,1,17)] (by decide +kernel) lowS_105
def dzo_106_16:=0x5050000050500000505000005050000
def gzo_106_16:=0x5050000050400000504000004040000
def gsh_106_16:=0x505000005040000050400000404
theorem lowS_zo_106_16_104:Lower true dzo_106_16 roots_106 gzo_106_16 5:=lower_iso_b (d1:=dom_106) (r1:=roots_106) (T1:=gsh_106_16) [(dom_106,16)] (by decide +kernel) (lower_slice_b (T:=gsh_106_16) [(0x404000004040000040400000404,0,2)] (by decide +kernel) lowS_104)
namespace S_122
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(8,40),(8,72),(10,26),(10,42),(10,74),(16,18),(24,26),(24,56),(24,88),(32,34),(32,40),(32,96),(48,50),(48,56),(48,112),(64,66),(64,72),(64,96),(80,82),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_122.map (·&&&dom_122)
def gM:=goal_122&&&dom_122
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x6df90
|5,0=>0x1adac
|6,0=>0xc00bf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x141414141414141414141414000000028002800280028002800280028002805050505000000000505050500000000a0a00000a0a00000a0a00000a0a000101010101010101010101010101010100280028002800280028002800000005050505050505050000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea1a3a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 123 0x7ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0x3f3c0
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_90 4 roots_90 ops++addP pm 2 dzo_106_16 5 roots_106 ops++addP pm 3 dom_106 5 roots_106 ops++addP pm 4 dom_104 4 roots_104 ops++addP pm 5 dom_58 4 roots_58 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_122 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_106_16_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_122 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_122==dom_122)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_122 gM v ys):RunD true dom_122 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_122 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_122 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_122 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_122 roots_122 goal_122 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_122
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=S_122.noCircuit
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_slice_b [(0x10101010101010101010101010101010,16,20),(0x11110000111100001111000011110000,4,20)] (by decide +kernel) lowS_104
namespace S_155
def pG:List (Nat×Nat):=[(1,9),(1,17),(2,18),(2,130),(3,11),(3,19),(3,131),(8,9),(8,136),(10,11),(10,26),(10,138),(16,17),(16,18),(24,25),(24,26),(24,152),(128,130),(128,136),(129,131),(129,137),(129,145),(144,145),(144,146),(144,152)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_155.map (·&&&dom_155)
def gM:=goal_155&&&dom_155
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7128104b7d
|5,0=>0x4fe140b8b009aa9
|6,0=>0x9aa9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0000000000000000000000000a0a0a0af0f0f0f0000000000000000000000000c0c0c0cc0c0c0c0000000000000000000000000c0c0c0cc0c0c0c0000000000000000000000000c0c0000f0f00000000000000000000000000000f0f0000f000f000000000000000000000000000f000f00a0a0a0a0000000000000000000000000a0a0a0a303030300000000000000000000000003030000f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x43620436820437620436204352043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x1563d8a5
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 156 0xfffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf8820
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x18
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_154 4 roots_154 ops++addP pm 1 dom_153 4 roots_153 ops++addP pm 2 dom_27 4 roots_27 ops++addP pm 3 dom_147 4 roots_147 ops++addP pm 4 dom_139 4 roots_139 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_155 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_139 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_154 4 s (0,roots_154.map (·&&&dom_154)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_155 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_154 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccccccccccccccccccc,126)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_155==dom_155)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_155 gM v ys):RunD true dom_155 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_155 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_155 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_155 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_155 roots_155 goal_155 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_155
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=S_155.noCircuit
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
namespace S_171
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,34),(2,130),(3,11),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,42),(10,138),(32,33),(32,34),(32,40),(32,160),(128,130),(128,136),(128,160),(129,131),(129,137),(129,161)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_171.map (·&&&dom_171)
def gM:=goal_171&&&dom_171
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x57c85
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000000000000000000000000000f0f00000000f0000000f00000000000000000000000f0000000f00c0c00000c0c000000000000000000000c0c00000c0ca0a00000a0a000000000000000000000a0a00000a0af0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 172 0xfffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xf0
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_170 5 roots_170 ops++addP pm 1 dom_43 5 roots_43 ops++addP pm 2 dom_169 5 roots_169 ops++addP pm 3 dom_163 5 roots_163 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_171 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_163 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_170 5 s (0,roots_170.map (·&&&dom_170)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_171 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_170 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_171==dom_171)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_171 gM v ys):RunD true dom_171 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_171 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_171 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_171 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_171 roots_171 goal_171 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_171
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=S_171.noCircuit
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_slice_b [(0x44440000444400000000000000000000444400004444,32,34)] (by decide +kernel) lowS_172
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_slice_b [(0x20200000202000002020000020200000202000002020000020200000202,8,9)] (by decide +kernel) lowS_232
def isoMvS_87:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_87:Lower true dom_87 roots_87 goal_87 5:=lower_iso_b isoMvS_87 (by decide +kernel) lowS_55
def isoMvS_93:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_61
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 5:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_62
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_61
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_61
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_31
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 5:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_55
def isoMvS_157:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_155
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 5:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_55
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_122
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_59
def isoMvS_181:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_155
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_59
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_122
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_122
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 7:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_61
def isoMvS_199:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_167
def isoMvS_203:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_171
def isoMvS_205:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 7:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_122
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_59
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_59
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_122
def isoMvS_230:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_121
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_233
def isoMvS_236:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_121
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_121
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_61
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xcccccccccccccccc,16,18)] (by decide +kernel) lowS_61
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_121
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030302030302000
def gsh_121_4:=0x3030303030303020303030203030200
theorem lowS_zo_121_4_105:Lower true dzo_121_4 roots_121 gzo_121_4 8:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16)] (by decide +kernel) lowS_105)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(32,96),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,65),(64,72),(64,96),(68,69),(68,76),(68,84),(68,100),(80,81),(80,84),(80,88),(80,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>3
|5=>24
|6=>55
|7=>20
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd173078f401d00
|5,0=>0xc21b676c2f6fcd963ea05137e3bc98324392a73c2973726b5d25b1722de6229a8216a31d2d01b8a4190301664913d4d0d1730a65205a73048a101985
|6,0=>0xd784fae93aab96aa6ade9ece79386a88fcd83b25798116cede6939c61eff53ca55137e41a803ab3934fb233acb339cd3243930e3b305672a5e728b9c283a626b5d264b3263d2209102063a201d1201a21e4181e2411d9431d29a1c591175511730016fa9143771316011622106f20f8080e92a0def10de230822b07224044c10401c03e4501b5f01a5b
|7,0=>0x96df88e6606926e4b44148f574583b38f053033316f771306011e831099d0bf98079680719d0528b0377401a5b005da0004d
|8,0=>0x6184e213f10f7ba
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccc888888888888888a2222222222222222222222222002200cccccccc00000000cccccccc00000002222222222222222222222222222222200cc00cc00cc00cc00cc00cc000000033333333333333330022002200220022cccccccc88888888cccccccc8800880333333333333333300000000000000000000000000000000cccccccccc00cc033333333222222223333333322222222cc00cc00cc00cc00cc88cc88cc88cc8b3333333333333333333333300000000cccc0000cccc0000cccc0000cccc00033223322332233223322332233223322c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333330033002222222222002200
|0,1=>0x888888888888888b3333333333333333333333333003300cc00cc00cc88cc88cc00cc00cc88cc8b3223322332233223322332233003300cccccccccc88cc88cccccccccc88cc89111111111111111111111110000000000000000cccccccc00000000cc00cc00000000022222222000000002222222200000000cc88cc8800000000cc88cc8b3333333330033003333333333003300888888888888888888008800880088033333333333333333300330033003300cc88cc88cc88cc88cc88cc88000000000330033002200220033003300220022cccccccccc88cc8800000000000000033003300330033003300330033003300
|0,2=>0x4400440044004400440044000000000000000000000003322332233223322444444444400440044444444440044022002200220022002200220022222222cccccccc00000000cc88cc8800000002222222222222222222222220000000000cc00cc00cc00cc00cc00cc0088008b3333333333333333333333322222222888888888800880088888888880088033332222333322003333222233332200cccc8888cccc8888cccc8888cccc880333333333333333333223322332233220000000000000000cccccccccc88cc8b33333223333332233333322333300004444444444444444008800880088008a2222222222222223333333333223322
|0,3=>0x444444444444444444444444440044033333333000000003333333300220022cccccccccccccccccccccccc0088008b3113311331133113311331100000000cccccccccccccccc44444444440044033003300333333333300330033223322440044004400440044004400cc00cc02222222233333333222222223322332200000000cccccccc0000000088888888000000000000000000000003322332200000000cccccccc000000000088008803300330033003300220022002200220000000000880088000000000088008b3333333002200223333333300220022000000000000000000880088008800880220022002200220022002200220022
|0,4=>0x3333333322222222cccccccccccccccccccccccccc88cc880000000000000000000000000220022
|_,_=>0
def sP:Nat→Nat
|0=>0x1a88801182068320046111a0c8011e8500d064009f1a0ce011820f0606080881a0ce94023c30338400883610190023cb03280461a2c0c9811820190023cc981a0ca011e5cb06065008f120c1011034193200478d06046122234190023c70d060460b1424182022038606140840608080
|1=>0x5e2030d06b8801106c68320046111a0ca0118b440d064008f186448d064008c1034190023160806aca10023040d064008c002020d0608a01181819002a84061a0c08c522140d06088011035310023040d069080118206a5200460806046122e20303200478b2c101a4023118d064008c
|2=>0x1a0c1100230896080ca0118341ba20046081a0ce0118206832004629103418118e440d0608a011e306832804634103419002e0608500c80118dc40d064008c6c206832004635103419002d0c082cc819002304061a0c101242140d0650801181868320058880834190023050d064008c
|3=>0x200463f107830320046081a0d210026043e1a0c8011821e8d064008c105830320047881a0ca10023cc041a0c08c5220683045008f6434190023c4231a0c8011834181182d8081a0de10023040d065008f18d0303200461710341900231d881a0c8011844b0d06b808c106d18d064008c
|4=>0x3c5868320046082c34190023c6081a0ca100230c080d0868320046081a0c801182c40d06908011e3040d0608a01182030d060880118206832004627103419002309086434190023040d06908011820d961a0c8011820683044009f110468320046081a0c801183840d064008c8020683
|5=>0x68320046081a0c80118c04161a0c801182030d064008c107868320046082c10190023040d064008c3420b0d064008c662030d060880110341900231888
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa50154005
|5,0=>0x2618926231886620187a61d186e61a18626171856614184a611183e60e183260b1827508581b605580f6
|6,0=>0x2107825e0277eddf477b5de6777ddd87745dca77119bd76dd9b076a5da2766dd9476399877601d7975cd96c759995f7565952752dd4474f5d3674bdd287485d1a744dd0c7415cfe73ddcf073a5ce2736dcd47335cc672fdcb962c9cab729589e7
|7,0=>0xa91e9d7a59e8e8a1de8079e227089a22608965e518929e4288ede3478b5e26787a2177
|8,0=>0x2b97ac9eab7
|9,0=>0x2c06
|_,_=>0
def wAt:=mkWire dB 67 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10351041184118214843283120211add1e3718212e2318411acd2c321a410c43183508311a212832202160211843042318412c332035182f08431035483428312c3c182120351a3108301a2120a20c2108311a21069d2c30203506393c302c21203528312021304118372c312035080818411a2118412a352830202108081841
|1=>0x2021184118352c3020350c43183560351843283120212c312035182318413c302c2120353c322c2120353c332c2120352831202120215043083110411841182160351843106e2c31203508c31a211e4318211a3104371841106c2c312035042318412c312035106c0435184120211a211a411e37182154410830103554420830
|2=>0x1843203518352c2120351a211a41083310352c32203518411835283220212c21203518212035183720210c231835084310351e4118212031
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xf40000000d20000000000000000000000b2000092000063000000000024002000000000
|6,0=>0x6e36b36830006620000000006516326035e25b30005925725430005134f24d24a34734524230003f33c33930003633420000003132f22d22b22920002720002520000002232021d30001a3182162133000
|7,0=>0x9729529329128f28d28b28928728528328127f27d27b2792772752732712
|8,0=>0x9b19a1991
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x57d124450037c811fc7d1dc6f17c450fc3d0dc310c02f0a82007c1a0601504810024080140400800
|1=>0x3dfe4a9f97e358c177
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80004000000000001001009000003040000
|6,0=>0x5030801000003045c10c01871405440492c63800d174068400040f18410010005c008195016106480
|7,0=>0x9a46e261994a4cd6de81265565f860
|8,0=>0x198d9
|9,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 8 roots_121 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dzo_121_4 8 roots_121 ops++addP pm 3 dom_93 7 roots_93 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_124 6 roots_124 ops++addP pm 6 dom_105 7 roots_105 ops++addP pm 7 dom_29 4 roots_29 ops++addP pm 8 dom_53 4 roots_53 ops++addP pm 9 dom_85 4 roots_85 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_121_4_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 8 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 55 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_125 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_125 roots_125 goal_125 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_125
theorem lowS_125:Lower true dom_125 roots_125 goal_125 10:=S_125.noCircuit
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_slice_b [(0x50505050505050505050505050505050,16,20)] (by decide +kernel) lowS_122
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_slice_b [(0xcccccccc000000000000000000000000cccccccc,16,18)] (by decide +kernel) lowS_157
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_169_4:=0x30300000303000000000000000000000303000003030
def gzo_169_4:=0x30300000303000000000000000000000302000002000
def gsh_169_4:=0x3030000030300000000000000000000030200000200
theorem lowS_zo_169_4_41:Lower true dzo_169_4 roots_169 gzo_169_4 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_4) [(dom_169,4)] (by decide +kernel) (lower_slice_b (T:=gsh_169_4) [(0x3030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_171_4:=0xf0f00000f0f000000000000000000000f0f00000f0f0
def gzo_171_4:=0xf0f00000f0f000000000000000000000f0e00000a000
def gsh_171_4:=0xf0f00000f0f000000000000000000000f0e00000a00
theorem lowS_zo_171_4_43:Lower true dzo_171_4 roots_171 gzo_171_4 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_4) [(dom_171,4)] (by decide +kernel) (lower_slice_b (T:=gsh_171_4) [(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_43)
namespace S_175
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,34),(2,130),(3,11),(3,35),(3,131),(4,132),(5,13),(5,37),(5,133),(6,38),(6,134),(7,15),(7,39),(7,135),(8,9),(8,40),(8,136),(10,11),(10,42),(10,138),(12,13),(12,44),(12,140),(14,15),(14,46),(14,142),(32,33),(32,34),(32,40),(32,160),(36,37),(36,38),(36,44),(36,164),(128,130),(128,132),(128,136),(128,160),(129,131),(129,133),(129,137),(129,161)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_175.map (·&&&dom_175)
def gM:=goal_175&&&dom_175
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xb1100
|4,0=>0xffa72f48c1f148ad9e0ac2b16ba31ab8d28aee57a5856a2fe9a2cd29b4cf98f46937e28def8851027cfcb799757686070b0566a6a50ce9504c939253371353643a307292eded2ccb620844
|5,0=>0xfffccfe27efc4e9facb8f5ca3f2739ec70fec131e876fdf7f4df7b4dc707d8de1d6fa3cf8becc534cb069ca6c5c3b70c078cb6cf6b4ba6b3885b22a9af7bdae03caacb9a845aa3bc99e3849b9f39a8b296b9893d3c931c79240990c0a8fbd28d1068cd448726b86ae786395822ab725ae704776eb9d6801465b7e6576d63cb9610bc5e58b5c66c5afae5746452afa4ff11472bb45840446564323342d494259d3d0b23c9d03707233e48307df2a6242617925d802494023d1e1e5391b9d6169c1143f80d42d0bbe50b64c0388e0231f0230500ce2
|6,0=>0xff099fd8cdfd13df88e8f7bb8f5a6af312eebe9ae9e00e2b7de288ce1104dd372d6d95cf759cefc4cda68c86b5c425ec0a46be56bbe489b5cb5b16a9ab6bfab67fa38df9b7899ac259163d85c1982bc17ec946f3586c4d96a24f62c5b62a6361cfa531364ee0d4e17649255444a33e4793bcba39cf839464358bb2fb842e5612a456294c6285371e9c5192d916e0f15fee077660631e0595102152
|7,0=>0xf1addd8213d21e9c9008bf697bd511aa9da95ec25c4254c16730cf529dcc17be012a04
|8,0=>0x3e74a
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffcc0000ffcc00000000000000000000ffcc00000000ffff0000ffff00000000000000000000ffff0000ff00ffff0000000000000000000000000000ffff00000000cccc0000cccc00000000000000000000cccc0000cccc00000000ffff0000000000000000000055550000aaaaffff0000ffff00000000000000000000aaaa0000aaaaff000000ff0000000000000000000000ff000000ff00ffff0000cccc00000000000000000000eeee0000ccccffff0000ff0000000000000000000000ffff0000ff00ffff00000f0f00000000000000000000ffff00000000aaaa0000aaaa00000000000000000000aaaa0000aaaaffff0000ffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff00000000ffcc0000ffcc00000000000000000000ffcc0000ffccf0f00000f0f000000000000000000000f0f00000f0f0ffff0000ff0000000000000000000000aaaa0000aa00
|0,1=>0xffff0000cccc00000000000000000000ffcc0000ccccff330000ff0300000000000000000000ff330000ff0033330000330300000000000000000000333300003300ffff0000ff0f00000000000000000000ffff0000ff005f5f00005f0f00000000000000000000555500005500ffff0000ffff00000000000000000000ff000000ff00ffff0000aaaa00000000000000000000ffff0000aaaaffff0000ff0000000000000000000000ffaa0000ff0000000000ff0f0000000000000000000000000000ff001313000003030000000000000000000011110000000000000000ffff0000000000000000000000000000ff00ffff0000fffc0000000000000000000000000000000000330000000300000000000000000000003300000000ffff0000aaaa00000000000000000000ffaa0000aaaa0033000000000000000000000000000000330000000000000000fffc0000000000000000000000000000fffc
|0,2=>0x550000005500000000000000000000005555000055003333000003030000000000000000000033330000000000000000000000000000000000000000555500005500f0f30000f0f000000000000000000000f0f30000f0f000ff000000ff0000000000000000000000ff000000aa00ff0000000f0000000000000000000000ff0000000033330000333300000000000000000000003300000000ffff0000000000000000000000000000aaaa0000000000330000003000000000000000000000003300000030ffff0000fff000000000000000000000ffff0000fff00000000000000000000000000000000055550000000000000000ffff0000000000000000000000000000aaaa00ff000000000000000000000000000000ff000000000333000003030000000000000000000000330000000000ff000000fc0000000000000000000000ff000000fcffff0000ffff00000000000000000000ffff0000aaaa
|0,3=>0xff000000000000000000000055000000ff005555000055440000000000000000000055550000554400000000000000000000000000000000ffff0000ff00fffc0000fffc00000000000000000000fffc0000fffc00330000003300000000000000000000003300000000ffcf0000ffcf00000000000000000000ffcc0000ffcc55550000555500000000000000000000555500005500ff0f0000ff0f00000000000000000000ff000000ff005f5f00000f0f00000000000000000000555500000000ffff0000000000000000000000000000ff000000000000ff000000ff0000000000000000000000aa000000aaffff0000f0f000000000000000000000ffff0000f0f055550000000000000000000000000000555500000000f5f50000f5f000000000000000000000f5f50000f5f05555000055000000000000000000000055550000550033330000333300000000000000000000111100000000
|0,4=>0xff000000ff0000000000000000000000ffff0000ff0000ff000000ff0000000000000000000000ff00000000ff330000ff0000000000000000000000ff330000ff00ffff0000fffc00000000000000000000ffff0000fffc00000000000000000000000000000000ffff00000000ff000000ff0000000000000000000000ff000000aa00ffff0000ffff0000000000000000000000ff00000000333300003333000000000000000000003333000033000fff00000f0f0000000000000000000000ff000000000f0f00000f0f00000000000000000000000000000000ffff0000ffff00000000000000000000aaaa0000000033330000333300000000000000000000333300002222ffff0000ffff0000000000000000000055550000000000000000000000000000000000000000ffff0000aaaaff330000ff3300000000000000000000ff330000ff00ffff0000ffff00000000000000000000555500005500
|0,5=>0xaaaa0000aaaafff00000fff000000000000000000000fff00000fff0f0ff0000f0f000000000000000000000f0ff0000f0f0f5f50000f0f000000000000000000000f5f50000f0f0ffff0000ffcc00000000000000000000ffff0000ffcc00ff000000f00000000000000000000000ff000000f055550000555500000000000000000000555500000000ffff0000ffff00000000000000000000ffaa0000ffaaffff0000ffff00000000000000000000ffcc0000ffccaaaa0000aaaa00000000000000000000ffff0000aaaa0000000000000000000000000000000000ff0000000033330000333300000000000000000000333300000000
|_,_=>0
def sP:Nat→Nat
|0=>0x3004604067c4810a34f090a106890a7420704148043834105083448c3610189022050330046051a6808c0064c011810189023000d0414b841a24296083410114546821214a0d12149840e4808c0824291201038f021420e1a0808a120460b081c182022818902202870c082840608080
|1=>0x1a2408c5a1068212b02841a04605561068918155041a24085521068f1204284062408c14a018d042408a063411a021468212153840c341090a1038d340460a062408c14913071a082841204625481070d120460a062408c148c198023050d04040041a3cd010a3448544106820a84220
|2=>0x12302840e35e020a106890215d841ae81090a1070d04042841a2408c721068270142070608085083448c0adc20312d808c0a3410114d42341a24631082408c669020d123029708186890ab820d300460a08344b218c420d12042b00834909023020d120460a2a3448118bc20d1215704
|3=>0xed808c0a1068918163841a246310918c8902314041a080852a1068902305450e35c0c0a1038d04058841a24085881068902305431a0460a561210d120460a1a0848520106c112042841a2408c80103b41a082841a0460a7e106821205f047a341010a1038d04045041a240880a10e0d
|4=>0x230507066808c0a1848c0a8c2070c246050834d011829a831a2408aa13c68202142071a082848c34481102822012046280834c01181420d046808a4c3448c6210689023054e1a0a6810a1260d04242841a2408c00103cb04042841b2808c14106890230549062408c0aa06890216404
|5=>0x120460a4a1038d3404605086468918142461c344811814203120460546106b812302841b504811828207062408c0a1068902305350836982120428468341090a1018d12042d0094868902302840e341010a1068902302d10834109022820d12045440835e090a4420d3e24085081c189
|6=>0x120460a1a25b0118142201a2408c0a1068902302d5081e58902302841a2408c14cc20d04242848c3410902148841a2408c0a5420d12042d0081c68902318841a2408c14a0207683448c0a10689023052408f468902302840634109021420d120460a461038d120460a0898689181420d
|7=>0x12042841a2408c0a902031a68481181468902302c908d0c8d1230284063448118282a60e3448c0a1068902318841a2408c0a942191a2408c141018d120460a1a2408c0b0c20d12302d6090868902302840c3448c0a1068918151848d3c68902302840e3448c0a1230d96084810a1069a
|8=>0xa1069a120460508d0689181420d120460a0a1068902305041a084810a10c8d1204605083658902302841a2408cb6106da12302841a24605091868902302b308344d918142201a2408c141068234042841a2408c0b3820d7808485083448118154041a26c0c0a1068918159848d5c682
|9=>0xd1204605080c68902302841a2408c0a8c2071a2408c
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x424c831903320063f4c7d18f731e863c4c7718eb31d06394c7118df31b86364c6b18d331a06334c6518c731886304c5f18bb317062d4c5918af315952a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41588028fa61e8c3b987430e261b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b25f64b2c94d926b2476482c8f151b32306454c89190f32186
|6,0=>0x218b42a7848d075e0bb4107814d00ddfe3bf577dcef9ddf03bd977a4ef319e2bbbe7770cec5dd5b3a4773cce5ddc83b897704edf19babb6e76ceed81dacbb536698ed15d9fb3387662eca9d91bb1c762aec39d83bb0165f4ebcdd763ae575bceb61968baca7586eaf1d5b32af7550ea8994dba956
|7,0=>0x2463c8578fcf1dde38b46a78c8d179a2bbc507894d111a1f34377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 176 0xffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1319021212290a111a251a11122a0a11041112311a05123106331a111a2512311a6b12110a1112311a0b12311a251a111a25122a06331a130212123112110a111a251a0b0e281a6812311a251af212311a050e1304051a2506251a11123102121a68122a12310c3306081a111a28123112311a251a2a0e051a691a270e281a11
|1=>0x1a2b0a111a150a111a1166111a1768271a0532131a151b19021202121a2796251a131a25021212311a1312110a111a68121106151a111a251a130a111a17123102121a0b12311a6a121106331a110e171a251a280a111a251a051a2a0a110e131a251a1112310a111a271a250a110e051a251a2b0a111a25021206251a111a27
|2=>0x1a111a271a2512111a050a110a1112311a151a130a13120502121a17028d1a271a290a111211123106271a11040512311a280a1102cd1a171a1702121a0912311a2a0a111a1146111a271a051a110e051a250e171a25
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000000000000000000000000000000000000000000000000000000001000000000000
|5,0=>0x1c10000000000000000001a20000000000001820000001710000001610000000001420000001220001020000000f10d20000000000000000000000000000000c10000000000000000a2091081071000000061051041000031021
|5,1=>0x2a20002912720000002612512412310000000002031f10001e10001d1000
|6,0=>0x9b29929729529329128f28d28b28928818628518418228027e27d17b27927727527327126f26d26b26926726520006326125f25d25b25925725525325124f24d24b24924724524414314124013e23c23a23823623423220003022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0xa80053c0298014600a08047c023a011c008a80450021a010c008380418020a010400800020000980044002000080002800100006000280010000400018000800020000
|1=>0x848120430c2be614f20ae9056c8008314f16af88d7c449e215f10ad8852c423e21091021081004020134208a10300c12be095b04a9824000a00020200af8057402b60154
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2000000000000000000000000000000000002000000
|5,0=>0x3c010d0001040820000203800800800000002c0000000008000000940002000080000a80283006000148000000000000000140000000044104280104900084
|6,0=>0xf11a51ddac6dfd4311209b1b405657e16c2e4af76279300c53399051f56b61275d775407213e7270d83ed15027422
|7,0=>0xefaea3f638a8ebb8f6cfa
|8,0=>0x21
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_173 7 roots_173 ops++addP pm 1 dom_166 5 roots_166 ops++addP pm 2 dzo_43_4 5 roots_43 ops++addP pm 3 dom_43 5 roots_43 ops++addP pm 4 dom_174 6 roots_174 ops++addP pm 5 dzo_169_4 5 roots_169 ops++addP pm 6 dom_167 6 roots_167 ops++addP pm 7 dom_170 5 roots_170 ops++addP pm 8 dom_171 7 roots_171 ops++addP pm 9 dom_163 5 roots_163 ops++addP pm 10 dom_169 5 roots_169 ops++addP pm 11 dom_165 4 roots_165 ops++addP pm 12 dom_139 4 roots_139 ops++addP pm 13 dzo_171_4 6 roots_171 ops++addP pm 14 dom_143 5 roots_143 ops++addP pm 15 dom_41 4 roots_41 ops++addP pm 16 dom_141 4 roots_141 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_175 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_169_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_171_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_173 7 s (0,roots_173.map (·&&&dom_173)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_175 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_173 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_175 gM v ys):RunD true dom_175 gM v (ori ys):=h
def Z (s:Nat):=barP dom_175 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_175 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_175 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_175 roots_175 goal_175 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_175
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=S_175.noCircuit
namespace S_183
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,18),(2,34),(2,130),(3,19),(3,35),(3,131),(4,20),(4,132),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,23),(7,39),(7,135),(16,17),(16,18),(16,20),(32,33),(32,34),(32,160),(36,37),(36,38),(36,52),(36,164),(48,49),(48,50),(48,52),(48,176),(128,130),(128,132),(128,160),(129,131),(129,133),(129,145),(129,161),(144,145),(144,146),(144,148),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_183.map (·&&&dom_183)
def gM:=goal_183&&&dom_183
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa60d68894847933436f31f66a
|5,0=>0xeb9b1cdd599673f950ef7f42c6d51d5a9b454c8f45e6f41b4f391e62dfe922fc221f3e204930fa3a
|6,0=>0xff647fdaa3db5bed8916d721cd6005c0867c03aabe2f28b74a83d7774bf268cde66cf164c625f3825d3ba500f24f5e34e0924683d451cb44f674489c4354d4044035d50351c8329002857327f35223b421f3e173aa152320de96
|7,0=>0xfdaa3a886da75eea4c5d7dc0c490a5241c714b6813292
|8,0=>0x8a6fe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00ff00ff0000000000000000000000ff000000ff0000ff00ff00ff00ff0000000000000000000000000000000000000000000000000000000000000000ff00ff00ff000000000000ff00ff00000000000000000000000000000000ff00ff0000000000000000000000000000000000000000ff00ff00f000f0000000000000000000f000f000f000f00000ff000000ff0000000000000000000000ff0000000000000000ff00ff000000000000000000ff00ff00ff0000cc00cc00cc00cc000000000000000000cc00cc00cc00ccff00ff00ff00ff000000000000000000ff00ff00ff0000ff000000ff0000000000000000000000ff000000ff0000ff00ff00ff0000000000000000000000ff00ff00ff0000ff00ff00ff00ff000000000000000000ff000000ff0000f000f000f000f0000000000000000000f000f000f000f0ff00ff00cc00cc000000000000000000cc00cc00cc00ccaa00aa00aa00aa000000000000000000aa00aa00aa00aa
|0,1=>0x5500550055005500000000000000000055005500000000aa00aa00aa00aa000000000000000000ff00ff00aa00aa000000000f000f00000000000000000000000000000000550055005500000000000000000000005500550055000000000000ff0000000000000000000000ff000000ff000000000000ff00ff00000000000000000000000000ff0000ff00ff00000000000000000000000000ff00000000000055000000550000000000000000000000550055005500005500550055005500000000000000000055005500550000ff00ff00aa00aa000000000000000000aa00aa00aa00aa00000000000000000000000000000000ff00ff0000000000000000ff00ff000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff00ff000000003300330033003300000000000000000033003300330000aa00aa00aa00ff000000000000000000aa00aa00aa00aaff00ff00000000000000000000000000ff00ff00000000
|0,2=>0xff00ff00ff00ff0000000000000000000f000f000000005500550055005500000000000000000000000000000000ff005500ff0055000000000000000000ff000000ff0000ff00ff00ff00ff000000000000000000f000f000f000f0f000f000ff00ff00000000000000000000000000000000ff000000ff00ff000000000000000000ff000000ff0000ff00ff00ff00ff000000000000000000ff00ff00aa00aaff00ff00ff0000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000ff00ff000000ff000000000000000000ff00ff0000000000000000ff00ff00000000000000000000000000f000f0ff00ff00f000f0000000000000000000ff00ff00f000f0000000000000ff000000000000000000000000000000000f000f000000000000000000000000000f000f00000000ff00ff000f000f000000000000000000ff00ff00000000ff000000000000000000000000000000ff00ff00000000
|0,3=>0x55005500000000000000000000000000550055000000000000ff000000000000000000000000000000ff00000000aa00ff00aa00ff000000000000000000aa00aa00aa00aa00000000aa00aa000000000000000000aa00aa00aa00aa
|_,_=>0
def sP:Nat→Nat
|0=>0x1a3931421c02c40c21c02d35050870046421c03901421d83901421d73841421d63941421c01421c024b10528700e4c50810101420123900c50810101421d13903c21c038d1421c03061421c02c40ca1c01420402481421c01850810040c2040
|1=>0x3901421c03a81101421dc3a640508700e4050870253a44c508700e40508700e8d31421c088e4050870093905431421c08501421c039080508700e40508701f39e40508700e40508700e7501421dc3906c21c03903c21c03903c508700e405087
|2=>0xe4050870323a440508700e40508702238640508700e4d01421c038440308700e40508100e54508700c1421c0c8e3101421f13901421f03901421c0bce10508700e2d0b421c03a4405b0700e40508700ead0a8508700ea501421c039014a1c0
|3=>0x40508700e4d01421c03900c508700e4050870333901421c038b40508700e31016c087
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x38b1ad8cac5f62cb14d89ca4862130f546ec31615b09583ec196
|6,0=>0xb13d6dea8f4e6a43505e76d356973c9de42d1a789bc31e0aeff67c3bc5dd4ee376e3b55d9cec77603ae5d64eab7523a75d2ec91645b211cfae776
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 52 184 0xffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x40e4539010903840e82391508241090900d14e503b40e809d14e802f40e0e4016e403a88e903a08b4e40100c5419d05039384ce42100c54114bd03814b5038403903940e153140ed03a
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xc0000000000000000000000
|6,0=>0x7c80000000748006c99200181588005454100122001023c400384d100000304000000000000288821880014432
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xd6dbb5badb65b2d5bd53d37536d24124020018013d10808004002401a019014009008005004002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x200080000000
|6,0=>0x916294002100c2c6c008028e07ac00180000002408066
|7,0=>0xea6ed5d4f37
|8,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_181 7 roots_181 ops++addP pm 1 dom_149 4 roots_149 ops++addP pm 2 dom_167 6 roots_167 ops++addP pm 3 dom_151 5 roots_151 ops++addP pm 4 dom_55 5 roots_55 ops++addP pm 5 dom_182 6 roots_182 ops++addP pm 6 dom_166 5 roots_166 ops++addP pm 7 dom_147 4 roots_147 ops++addP pm 8 dom_179 6 roots_179 ops++addP pm 9 dom_163 5 roots_163 ops++addP pm 10 dom_54 4 roots_54 ops++addP pm 11 dom_178 5 roots_178 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_183 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_178 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_181 7 s (0,roots_181.map (·&&&dom_181)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_183 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_181 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_183==dom_183)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_183 gM v ys):RunD true dom_183 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_183 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_183 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_183 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_183 roots_183 goal_183 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_183
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=S_183.noCircuit
def dzo_168_16:=0x10100000101000000000000000000000101000001010000
def gzo_168_16:=0x10100000100000000000000000000000100000000000000
def gsh_168_16:=0x1010000010000000000000000000000010000000000
theorem lowS_zo_168_16_168:Lower true dzo_168_16 roots_168 gzo_168_16 4:=lower_iso_b (d1:=dom_168) (r1:=roots_168) (T1:=gsh_168_16) [(dom_168,16)] (by decide +kernel) (lower_slice_b (T:=gsh_168_16) [] (by decide +kernel) lowS_168)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0e0000
def gsh_171_16:=0xf0f00000f0e000000000000000000000f0e00000e0e
theorem lowS_zo_171_16_168:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso_b (d1:=dom_171) (r1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (lower_slice_b (T:=gsh_171_16) [(0xa0a00000a0a000000000000000000000a0a00000a0a,0,1),(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2)] (by decide +kernel) lowS_168)
def dzo_169_16:=0x30300000303000000000000000000000303000003030000
def gzo_169_16:=0x30300000302000000000000000000000302000002020000
def gsh_169_16:=0x3030000030200000000000000000000030200000202
theorem lowS_zo_169_16_168:Lower true dzo_169_16 roots_169 gzo_169_16 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_16) [(dom_169,16)] (by decide +kernel) (lower_slice_b (T:=gsh_169_16) [(0x2020000020200000000000000000000020200000202,0,1)] (by decide +kernel) lowS_168)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000504000000000000000000000504000004040000
def gsh_170_16:=0x5050000050400000000000000000000050400000404
theorem lowS_zo_170_16_168:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x4040000040400000000000000000000040400000404,0,2)] (by decide +kernel) lowS_168)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,17),(16,18),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(32,160),(48,49),(48,50),(48,56),(48,176),(128,130),(128,136),(128,160),(129,131),(129,137),(129,145),(129,161),(144,145),(144,146),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|4=>11
|5=>96
|6=>287
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe37bed830e87a857f8ce7a0df600ea5799e3d10b3c04431cdc0fee1
|5,0=>0xf9d45eb2b1e05eedccfbd94bdd6744d48a0d289dcd1a9c3b37bff92bddb9b6338b08e4ae7e4a81b6a63f89ff509f8709e00c9b0f295ec591f0d8721085c877db057b78c7b28e7a94b79ffd78e8d7807e775907492b732786fcc86812767deb61b6d5fcb75c02456db1568ed525cb501aa500f44eff84dcd44d5444d44c4a53949c5548aa947bfc4706846a3140b8f3f1c03a18c38e9632ac3316d1305702b0132a92429fee255b724b2022a8f2031a1f8201d04c1b4f91aa4518811183c717fba1657a153381403111a6f105b70f3f80ed5a0e7fc0a6100911507e5c07afe06660055b7050900488d038bf02d6200fad
|6,0=>0x5317b512a34e5fb4c9c04bccb49ee348327480714641f43ed943ab54295141b0a4195f41635408bc405753f1c03ef583e60e3e0ac3dede3ba6c3b79b3901638d923821b3628735da73562434f81335ad3329b32b752f93a2ed982e6792e04d2df9b2decd2d9082ab232a96029c91292d027fa526a71269e6261232597f2577123edf22d41222a6220a720b31208e41fae31fa701f8311f1931ec351ebd21e7f01e6d81e59b1e3e31d9f51d3361d04c1cd1c1cca61bb3e1bab81ac261aa491a9131a02619b6d192e91928b1866c1781616a3a1658515cee154c91533814de014da814192140201399a12cb9111ba0f3ea0e6ba0dae10c95b0b3010b0c00a4660a2c409d6409b28097ee0941d090400902308e6308cf2082db07c5107b3807a850780006719066c30640705be0053b60488d045e303d05037850252b004a100357
|6,1=>0xbf917bf279be73dbac4cb9a23b891fb44b6b2f3eb26d0b048bae7e4ac971abaf3ab0b3aa740a9deba81b6a77a1a5e90a478ba33ada2a7aa118ea08249f0da9ef779e3ef9ca769863a9832b9749694e1292a6891d13915ef90ed28fdb28e6058dcfc8d5a68c1208ad858ac5d8aa6f8a5b78852f877ce87138863d5861058464483d5b82e55828598154380f707ed6c7e8d07e3727dd837d8cb7ca557b9cb791b8780f4780407791276c5f764a975ada735bc72e4272ccd72014713576f8a96f3ea6e7e86e3066d7cb6c9986c50c6bfb76ae3d6a916698c76970568a4266d3066c8f66731649486481e6473b6438a6425b63d26635dd6104a60ac060ab45ff845fb445ed585e44a5dd515d8d85d5275cdbe5c9865c14e5bb1a5b7f45a7f6586c658461583f75825c56b115685a5675356592563ef553125514454a4d53aab53305
|6,2=>0xf8bddf8a75f2c9df1ea9f0a27efbdcefa44e5e78e35ddde1d8dbfb2dad1ddac84da5e9d98ccd742ad7301d6d6cd4e8ed431dd1480d107bd0e73d0126cfa28c9953c95d0c8ab8c0cfdc0be7bfb1b
|7,0=>0xefa2dec63beb415eb156e0bc4dc34bda77bd8ef1d54ccd4ae9d0126c90cbc51b9c0f2dc0cc7bfba6bf963bec1dbe73dbb9b2b5207b4d0eb0ff3b0f96ac979a92ed9ed31996a492ece900698f77f8e1bc8b9c78852f86eb08615985cb683f1b8091e7e6a77d43f7c5897c54c7830172a65728d8720a1718e9708c4700386a88868a3564948604b95f8295a8395a460598e95948758f6c53b4052dbc523a550aed4f67f4eda94ea474dfb14ca3649dde4641f45ec14519f433603b56437d7635db834d773422c3329032f5e3155030828301ee2fb912cc5528da8287c827fe7257712553b24c41234552258b21bfc20c401ed531ebf71e35a1c80e1afcc18bf917f71174401742d172011705f16263136b912b81112411100010a1e10869103a60e0710da780d89c0ccb40c40b0aea00adbb0a0f007a4d06719064fc050d400f2b
|7,1=>0xfefabf93f9
|8,0=>0xe06bbcc721cb946c2d55a87f4956bf824c96a888649bb4e61246ab53dbb0391d037c702d78826f6b1deb10d98d
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0e0f0e0f0e0f0e00000000000000000f0e0f0e0a0a0a0af0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af0f0f0f0f000f0000000000000000000a0a0a0a0a000a00f0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a0000000000f000f0000000000000000000000000f000f00f0f0f0f0000000000000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0c0f0c0f0c0f0c00000000000000000a080a080a080a08
|0,1=>0xf0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a0020002000200020000000000000000000200020a0a0a0a00000000f0f0f0f00000000000000000000000003000300f000f000f000f0000000000000000000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f00000000f0c0f0c0f0c0f0c00000000000000000f0c0f0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0ac0c0c0c0f0f0f0f00000000000000000c0c0c0c0f0c0f0cf0c0f0c0f0c0f0c00000000000000000f0c0f0c0000000000000000f0f0f0f0000000000000000000000000f000f0000f000f000f000f00000000000000000f000f000f000f00f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0c0c0c0c00000000000000000a0a0a0a08080808f0c0f0c0f0c0f0c00000000000000000f0c0f0c0f0c0f0cf0f0f0f0c0c0c0c00000000000000000f000f000c000c00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000
|0,2=>0xf0f0f0f0f0c0f0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f0000f000f000f000f00000000000000000f0f0f0f0f000f00f000f000b000b0000000000000000000f000f000a000a00f000f000f000f0000000000000000000f0f0f0f0f0c0f0c00000000000000000000000000000000f000f000f000f005050505050505050000000000000000050505050000000000000000f0f0f0f0000000000000000000000000f0e0f0ef0f0f0f0c0f000000000000000000000f0f0f0f0c0f0000f0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0cf0f0f0f0f000f0000000000000000000f0f0f0f00000f00f000f000f000f0000000000000000000f000f000a000a00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0af0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c00000000f0f0f0f00000000000000000000000005000500f0f0f0f0a0a0a0a00000000000000000f000f000a000a00
|0,3=>0xf0a0f0a0f0a0f0f00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0c0f0c00000000000000000e0e0e0e0e0c0e0cf0f0f0f0f0f0f0f00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f030000000000000000000f0f0f0f0f0f0300f0f0f0f0f0f0f0000000000000000000f0f0a0a0f0f0a00f0f0f000f0f0f0500000000000000000f0f00000f0f0000f0f0f0f0505050500000000000000000f0f0f0f0000000000000000000000000000000000000000f0f0f0f0f0e0f0e00f000f000f000f0000000000000000000a000a000a000a30303030303030300000000000000000000000000000000f030f030f030f0300000000000000000f000f000f000f0000000000000000000000000000000000f0c0f0c0f0c0f0c00000000000000000000000000000000f0f0f0f0d0c0d0c505050505050505000000000000000005000500050005000000000030303030000000000000000000000000300030030003000300030000000000000000000300030003000300
|0,4=>0xa0f0a0f0a0f0a0f00000000000000000a0a0a0a0a0a0a0a00000000f0f0f0f0000000000000000000000000f0a0f0a7030703070307030000000000000000050005000500050030300030303000300000000000000000303000303030000f0f0f0f0f0f0f0f00000000000000000f000f000c000c00f0f0f0f0f0f000500000000000000000f0f0f0f0f0f0000f0f00050f0f000500000000000000000f0f00050f0f000000f000f000f000f00000000000000000000000000000000c0c0c0c0808080800000000000000000f0f0f0f0a0a0a0a0000000000f000f00000000000000000f000f000f000f0000f000f000c000c0000000000000000000f000f000c000c00000000000000000000000000000000f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef000f000f000f0000000000000000000f000f000c000c00c0c0c0c0f0c0f0c00000000000000000c0c0c0c0f0c0f0cd0d0d0d0d0c0d0c00000000000000000000000000000000
|0,5=>0x5050505050505050000000000000000050405040504050430303030300030000000000000000000303030303000300f0f0f0f000f000f00000000000000000f0f0f0f00000000f0c0f0c0a080a0800000000000000000f0c0f0c0a080a08f0f0f0f0000000000000000000000000f0f0f0f000f0000f0f0f0f0f0c0f0c00000000000000000f0f0f0f0f0c0f0c30303030303030300000000000000000303030303030300f0f0f0f0000000000000000000000000f0e0f0e00000000f000f000f000f0000000000000000000f000f000e000e00f0a0f0a0f0a000000000000000000000f0f0f0f0f0f0000f0f0f0f000f000f00000000000000000f0f0f0f0f000f0000b000b000b000b0000000000000000000b000b000a000af050f050f050f0500000000000000000f000f000f000f00f0f00000f0f000500000000000000000f0f00000f0f000000f000f000a000a0000000000000000000f000f000a000af0f0f0f0f0c0f0c00000000000000000c0c0c0c0c0c0c0c
|0,6=>0xe0e00000e0e000000000000000000000e0e00000e0e00000000505050500000000000000000000000000000000f0f00000a0a000000000000000000000f0f00000f0f000000f000f000f000f0000000000000000000f000f000a000af0f0f0f0f0f00000000000000000000000f000f000f0000f0f0f0f0f0f000000000000000000000000000000000000f0f0f0f0f0f0f0000000000000000000f000f000f000f000000000000000000000000000000000000f000f000c000c5050505050505050000000000000000000000000000000000f000f000f000000000000000000000f0f0f0f0f0f00000000f0000000f00000000000000000000000f0000000f00f0f0f0f00000f0000000000000000000f0f0f0f00000f00f000f000f000f0000000000000000000f000f0000000000f0f0f0f0e0e0e0e00000000000000000f0f0f0f0e0e0e0e00f0000000f000000000000000000000f0f00000f0f0000f0f0f0f000f000000000000000000000f0f0f0f0f0f0000
|0,7=>0xf0f0f0f0f000f0000a000a000a000a00000000000000000a0a0a0a0a0a0a0a0000f0f00000f0f00000000000000000000000000000000f0f0f0f0f000f0f00000000000000000f0f0f0f0f000f0000000000f0e0f0e0000000000000000000000000f0e0f0ef0f00000f0f0f0f00000000000000000f0f00000f0f0f0050005000500050000000000000000000500050005000500f0f0f0f0f0f0f0f00000000000000000500050005000500c0c0c0c0c0c0c0c00000000000000000f0c0f0c0f0c0f0cf0a0f0a0f0a0f0a00000000000000000a0a0a0a0a0a0a0a30303030303030300000000000000000000000003000300f0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0e00000000000000000000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f05000500f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0c00000000000000000000000000000000000000003000300
|0,8=>0x3030303030303030000000000000000030003000300030000000000300030000000000000000000000000003000300f0f00000f0f030000000000000000000f0f00000f0f0300f000f000f050f0500000000000000000000000000000000000000000000f0000000000000000000f000f000f000f00f0b0f0b0f0b0f0b00000000000000000f0a0f0a0f0a0f0a10101010101010100000000000000000100010001000100f0f0f0f0300030000000000000000000f0f0f0f03000300f0f0f0f0f0f0f0f00000000000000000c0c0c0c0f0c0f0cf0f00000f0f050500000000000000000f0f00000f0f0000f050f050f040f0400000000000000000f050f050f040f04f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0c0f0cf0f0f0f0f0c0f0c0000000000000000000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0ab0b0b0b0b0b0b0b00000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000505050504040404
|0,9=>0xf0f000f0f0f000f00000000000000000f0f000f00000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f0000f000f000f000f0000000000000000000f000f0000000000000000000000000000000000000000f0f0f0f0f0a0f0af0f0f0f0a0a0a0a00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000300030003000300f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00005000500050005000000000000000000000000000000005040504050405040000000000000000050405040504050400500050004000400000000000000000005000500040004a0f0a0f0a0f0a0f0000000000000000000000000000000000000000f000f000000000000000000000000000f000f00f000f000f000f0000000000000000000f0f0f0f0f0f0f00a0a0a0a0a000a0000000000000000000f0f0f0f0f000f0050005000f0f0f0f00000000000000000500050005000500f0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0a
|0,10=>0x30303030303030300000000000000000303030303000300d0d0d0d0d0c0d0c00000000000000000d0d0d0d0d0c0d0cb0b0b0b0b0a0b0a00000000000000000b0b0b0b0b0a0b0af0f0f0f0500050000000000000000000f0f0f0f050005000000000050405040000000000000000000000000504050430303030303030300000000000000000303030302020202f0f0f0f0f0f0f0f00000000000000000f0f0f0f0e0e0e0ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0300030030303030303030300000000000000000303030300000000f0f0f0f0f000f0000000000000000000000000000000000f0f0f0f0a0f0a0f00000000000000000f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0000000000000000000f000f000a000a00c000c000c000c0000000000000000000c000c0c0c0c0cf0a0f0a0f0a0f0a00000000000000000f0a0f0a0a0a0a0af0f0f0f0005000500000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f0000000000000000000f000f000c000c
|0,11=>0xf000000000000000000000f0f00000f0f00000000000000000000000000000000000000f000f000f00000000f0f00000f0f000000000000000000000f0000000f00f0f0f0f00000f0f00000000000000000f0f0f0f00000f00a0a0f0f0a0a0f0f00000000000000000a0a0a0a0a0a0a0ae0e00000e0e000000000000000000000e0e00000e0e0000f0f0f0f0e0e000000000000000000000f0f0f0f0e0e00000050005000500050000000000000000000500050000000000000000f0f0f0f00000000000000000000000000000f00a0a0a0a0a0a0a0a00000000000000000f0f0f0f0e0e0e0e30303030303030300000000000000000202020202020202f030f030f030f0300000000000000000f020f020f020f02f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f0000000000f0f0f0f0000000000000000000000000f0f0f0000000000f0f0f0f0000000000000000000000000a0a0a0aa0a0a0a0a0a000000000000000000000f0f0f0f0f0f0000
|0,12=>0xf000f000000000000000000000000000a000af0f0f0f0f0f0f0f0000000000000000000000000f0c0f0cd0c0d0c0d0c0d0c00000000000000000d0c0d0c0d0c0d0cf0f0f0f0f0a0f0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0303030300000000000000000f0f0f0f03000300c0c0c0c0f0f0f0f00000000000000000c0c0c0c0e0e0e0e00000000000000000000000000000000300030003000300c0c0c0c0c0c0c0c00000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000000000f000f00f0f0f0f0f0f0f0f0000000000000000000000000f000f0010101010101010100000000000000000101010100000000f0f0f0f00000e0e00000000000000000f0f0f0f00000e0e0000f0f00000f0f000000000000000000000f0f00000f00c0c0c0c0c0c0c0c00000000000000000f0f0f0f0f0c0f0c00000000a0f0a0f0000000000000000000000000000000000f000f000f000f0000000000000000000e000e000e000e
|0,13=>0xb0b0b0b0b0b0b0b00000000000000000b0a0b0a0b0a0b0af0f03000f0f030000000000000000000f0f03000f0f0300f030f030f030f0300000000000000000f030f030f000f00f050f050f050f0500000000000000000f050f050f000f005050505050505050000000000000000050505050404040400000000f0f0f0f00000000000000000000000000000000f000f000f0f0f0f00000000000000000f000f000f000f0050105010501050100000000000000000500050005000500f0f0f0f0c0c0c0c0000000000000000000f000f000c000c0000000000f000f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f000030303030303030300000000000000000303030303030000f0f0f0f0b0b0b0b00000000000000000f0f0f0f0a0a0a0a00000000f0c0f0c0000000000000000000000000f0c0f0c00f000f000f00000000000000000000000f000f000f0000f000f000f000f0f00000000000000000000000000000000
|0,14=>0xf0f0f0f0f0f0f0f00000000000000000f0e0f0e0f0e0f0e00000000000000000000000000000000504050405040504f0f0f0f0f0f050500000000000000000f0f0f0f0f0f0000f0f03030f0f030000000000000000000f0f03030f0f0300c0f0c0f0c0f0c0f00000000000000000c0e0c0e0c0e0c0e00000000000000000000000000000000f0f0f0f0e0e0e0ea0a0a0a0a0f0a0f00000000000000000a0a0a0a0a0a0a0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0a0a0a0af0f00000f0f000000000000000000000f0f03000f0f0300f0f0f0f0f0f0f0f0000000000000000000000000300030030303030202020200000000000000000303030302020202a0a0a0a0a0f0a0f00000000000000000000000000000000f0f0f0f0504050400000000000000000f0f0f0f0504050450505050404040400000000000000000505050504040404f0f0f0f0f0f0f0f00000000000000000505050504040404f0f00000f0f000000000000000000000f0f0f0f0f0f0f00
|0,15=>0xf0f0f0f00000f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f000000000000000000000f000f000f000000f000f0f0f000f0f00000000000000000f000f0f0f000f00000000000000f0f00000000000000000000000000000f00f0f0f0f0f0f0f0000000000000000000f0f00000f0f0000a0a0a0a0a0a0a0a00000000000000000f0f0f0f0f0a0f0af0f0f0f000f000f00000000000000000f0f0f0f000a000a00a000a000a000a0000000000000000000a000a0a0a0a0af0f0f0f0c000c0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f0050505050505050000000000000000000505050505050500c0f00000c0f000000000000000000000c0f00000c0f0000c0c0c0c0c000c0000000000000000000f0f0f0f0f000f0000300030003000300000000000000000003000300000000f0f0f0f0f0f0f0f000000000000000000000f0000000f00a0a00000a0a000000000000000000000a0a00000f0f0000
|1,0=>0xf000f0000000000000000000000000f0f0f0f000000000000f0f00000f0f000000000000000000000f0f000000005050505050005000000000000000000050505050500050000000000f0f00000000000000000000000000000f0f0000f0f0f0f000f000f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f000000000000000000000000000000000000f0f0f0f0f0f0000c0c000c0c0c000c00000000000000000c0c000c0c0c000cf0f0f000f0f0f0000000000000000000f0f00000f0f0000f0f05050f0f050500000000000000000f0f00000f0f0000c0c0f0c0c0c0f0c00000000000000000c0c0f0c0c0c0f0cf000f0f0f000f0f00000000000000000f000f000f000f00f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x38181c0b018080e1f0200c0407030001c10018484406048500e061083008030a0800e1f0200c28070f0301214038183a0c0406c040703010061a0a018180e0800c320703024281803818180e0185c0e06060242a070305812120881818090a81c0c050800c28010984006120881820030781c140e018340e0c0580c0407050240407030141002038180a04018080200
|1=>0x1c01006140381808031a01c0c370704006350381812261a0500c0c198100614038181c100181c0c32048500e061883008030a004000c0481c0c300b0305e04018500e061681006020381808031601c0c0c0482c4807030305604018a80e060700c0407030a4061403818500c0d80c04070309c4c14038181809128500e060601006240081c18090d8080e060708c0602
|2=>0x8300803011180e060800c28220311408030101c0c050482c04140387c88040184854061304006142181812140387c0c160580c2807050300803091080c0c0489828410303008030a01c0c400200c2e020381812040a01c7e0c0200c283e0303012261e8500c0c1e09828070303008031201c0c0c0d80c040703014083b0a01c0c0c020e82807030301c39018080e06
|3=>0x200c2a0703014080303818a80c0d80c0407030581c100194c0e060214828070303008030393ca20c0800c28500302416140393c1810018502207030242807031381810018500e060981006140093418090101c0c160e01006140313018040184896060602408150381894040a01c0c0c02124280703030120b0a01c3e48048bc4c14038185c1b018080e06238100614
|4=>0x800c280703178185d0200c28070f81808030a81c0c162a810061503818080309008021f0200cb8140083012140881c0c0c0702c06120083008030781c140c0496c280703030b4100185044061701006150381808030a018b20c0702c06190383006580a01c0c0c0200cae07030301c10018080e06048500e060b030ac040a01c0c0c04810041503818aa04018080e06
|5=>0x18500e063803008020a01c0c6f0602c086d0a01c0c0c0200c2807031b01809020500e06358301204348500e06060240802038183804018500e063403008030a01c0c0a060400803010500e0607010065303818182f07010061403818cc040a01c0c0c320400614038181804018682806061880803090500c0c3001028070303008030a01c0c5f0603816030101c0c0c
|6=>0xa01c0c8341010060f0a01c18100200c28074081808030a01c0c80061fc08030a01c0c7d0481028073f030f804018500e0606010061403818f60c04898282203030087a018500e060601006140081cf00c04810ee14038181809020500e760602408020a01c3e060704006141101c0c04018500e063a8301c04019d00e06061cc08030a01c0c0c390100614038181804
|7=>0xa01c0c04018480e06288300803450500e06060100614038183a0c0200c28070322418880200c04070303008030a01c0c000601006144381c0c0c058110c140381818040180828070f8c808030a0600e0606010da1403818182f0200c24140381846040185002070601006850a01c0c0c42010061403818180b0200c321403830101b0a01c0c0c0d80c0407031680803
|8=>0x60100614038192c0c080100614038192a040184844064a03012040a01c3e062424c12040a01c0c0c490100614038181804018500e06488301223058500e0606024361403818180e1180c2807030301c0b018500e1f060b808030a01c0c6704a40161403818180401848280647830088d0a01c0c0c0200c2807030841804018500e060623012040a22c0e06060bc0803
|9=>0x60240614038182c0c022780607032741809058500e1f0602c08031201c0c0c0581006120a004182e0200c28070f8193804018500e060601006140387d3608020500e0606010063d03819280c0200c041403818dc0e0200c0e064d03088040184828060626408030a01c0c0c4981006140381818100200c2807032601c040181c0c970606c08030101c0c1b018500e06
|10=>0x2d01006141101818a90200c2807030315004018500e060609808031a0500c0c0200c48070303008030a0040ca7060100602038194ca50200c28070303008030a01c0ca40601006140328c180401a88280706010061403818620c508100614038181804018500e06500301c100181c0c30060100607030c02c0c048102807031e018044f80c2807030301c5d018500e06
|11=>0x38182c0c0200c280103ac418b0020500e06060100614038195e0c0200c28ae038181804018500ead030301c033181c0c0c2201006141501c0c04018508407030315810018500e060601006070323d280c0200c2807032ac180b1c80c2807030301204298500e060608c08030a01c0c0c0482c0414038181804018d40e064a03008030a01c0caa0603872030a01c0c0c
|12=>0x1b0240814038197c0c070400607031e418900200c28070f83008030a10444060604008030a0040e1f5e010061403818180e0200c28075d830120b0a01c0c0c2404008030c8500e065c8500e0606010061403819700c0200c2807032dc182e0200c0407030716c04018500e060601006340a01c3e060200d68140381818470200c28070303008030a01c0cb2060400614
|13=>0x18f428070303808031a01c0c0c6201028070303008030a01c0cc30608c0803010500e060581006020a01c3e090200828070303008030101c0c5e0603820030a01c3e060200c2807032f81804018500e1f0305808030905086060630808030a01c0c0c0801006120a0880c260200c28410303008030a01c0c0c60810061403819800c022fc28070303008030a004f20c
|14=>0x604006020a01c0c1604810280703031a0040185096070303008030a01c0c4d0609808030a3340c0c0200c28070333c1804018500e06670301604018500eb5060100614668880c0c0200c28076601818cb0200c2807030304c040185002790601006146501c0c0c0481028070332418c80200c2807030302004018500e06632e40814038181804018500e06628302004
|15=>0x18500e0641ab008030a0040e0c080102807031bc1804018500e066c03008030a01c0cd70604008031a8500e060200c28070f819ac09020500e06062542004018500cd40608c08030a01c0c480581006140387c90100200c0407030c01c040184844060604008030a01c0c32698100614038181804018540e061789808030a01c0c7f0200c24070303008030a0880cd2
|16=>0x70100601039e4185a1781006140381808030a01c0ce10602c08030a01c9e0c700100614038181804018500e062703008030a01dbe06060100602038182c1c0200c28010323c18100237828070303008036e8500e0606024cc040a01c0c0c0200db8140381818100200c28070323c1604018508607060b808030a01c0c0c0200c28070336c180401b6428070f8181c04
|17=>0x23b028070303008030a3ac0e060602408340a01c0c0c0489828070323818ea0200c2807030301214038182c0c0581006740a01c1804018082a070301006020a01c0cb10481054070312008030a01dd2060601006020a01dd0060239c2807030301c04018d40e0606010061403819cc0c0200c28070fb941804018500e06063900803090500e0641b8c08030a01c0c0c
|18=>0x200c28070331818260800c2801030301c04019dc0e060609c081403818180e0200c04070f819e604018500e0606010061403819e40c08010061403819e2040a01c0cf00602408120a0880c0c0200c280703058180e0800c04070303012040c8500e060601006ef0a01c0c0c0200c2807033b81804018f4280647831da040a01c0c0c130400614110181c10018080e06
|19=>0x9050021f0601006fd0a01c0c0c0200c2811038181804018500e067e03008fb0a01c0c0c0200c2801031141809020080e06180300803090080e1f03024081403818640c7d01006140381818f90200c28070303008032e0500e0606010061403be01810018500e062283012020a01c0c16060100612010040c0c7b8100614038181804018500ef50603816030901c0c0c
|20=>0xa01c3e060200e0214038181804018080e060e01006020a01c0c32060400900018500e06063fc08030a01c0c0c6a84008030a01c0c0c0200c041403819b404018500e06061b812040a01c0c79060400803010500e060702c06140381818710801006140381818040180828070319c08030a3f80e06060b80614038182c0c0481028fe03818180e0800c5407030300803
|21=>0x60d809040a01c0c0c4401006140381818100200c2807031200803010500e1f0303008030a01c0cb5060100614039f81809020500e060607008030a01c0c94060d808610a01c0c0c0482c2807030310404018500e06060120614038181804018500e066383020040180828070303008033b8500e06060100614039d8185a130100614038181804018520406060100602
|22=>0xa10c0e060602408120a01c0c0c0200c2905030302004018504407030b82004018500e06060980803078500e06061884c04018500e0606010060f0a0880e060602c0803090500e060601006140081818360200c28070f818901b018500e060604008030a01c0c3613010061411018180401850440703250180e0200c2414038181804018500e060626c0803078500e06
|23=>0x38181804018500e064e83008030a01c0c510604008030a0040e0606010061403818520c7b0100614038181804018500e06062980803298500e06060100674090500e060604008030a0a80e060608c08030a01c0c0c0581006140387c18900200c28070303008b3018500e0606010061403818f00c13010061400818181b0200c280703031200b0200c2807030300803
|24=>0xa01d02060603808030a01c0c0c1b010061403819920c0581006140381818480200c32140387c0c0c0200c28070303210045980c0414038181804018082807030304c04018500e063c8301204010500e06060380907018500e060641808030a01c0c0c2e810061403818180b0200c04140381818098301028070303008030a01c0c79060d812040a01c0c0c3501028f4
|25=>0x3818905a07010061403818180e0200c280703030fa04018500e065e83008030a01c3e066d02408141101c0c0c08010061403818600c0801006140387c0c2e0200c28070303008030a01c0c0c4a81006140381a140c0200c2807033941804018500e065883008030a01dd0060601028070f81a120c08010060f0a01c0c0c0481028070303090100200c28070319c0803
|26=>0x601006020a0040e060618808030a01c0c0c0200c28070331818040a2e80e060601006120a0880c0c0200c28010387c18260200c2807032381804018082807032f41804018642807030301c10018500e06060100614038182c0c080100614038198e0c1701006020a01c0c0c560100614038181804018d0280703030b4040184828070303008030a01c0d0b06010062a
|27=>0x303008030a01c0c650601006140381818040184828070303012040a01c0c0c05810061403818180e0200c28070303008030a01c0c0c0e010061403818f20c8600c28070303008020a01c0d09060240803010500e06060100619010500e060601006020a01c0c160601006120a01c3e0606010061403818640c020500e063783012040a01c0c0c3383808030a01c3e06
|28=>0x4018500e06060100614038181867020500e068483008030a01c0c940602408030a01c0c0c0200c28010381818040185044070303008030a01c0c0c2401006020a01c0c0c0240006140381818044f00c2807
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ad61a761a2519c61966190618a6184617e61786172616c61666160615a6154614e61486142613c61366130612a6124611e61186112610c6106610060fa60f460ee60e860e260dc60d660d060ca60c460be60b860b260ac60a660a0609b5095608f60896084507e60786072606c60666060605a6054604f50496043603d60376
|5,1=>0x26c62666260625a6254624e62486242623c62366230622a6224621e62186212620c6206620061fa61f461ee61e861e261dc61d751d161cb61c561bf61b961b36
|6,0=>0x41e74186411740a740373fd63f673ef73e873e173da73d373cc73c573be73b773b163aa73a3739c7395738e73886383537c7375736e73677360735a6353734c7346633f73387331732b6324731d7316730f7308730172fa72f372ec72e572de72d772d162ca72c372bc72b572ae72a862a1729b6294728e62877280727972727
|6,1=>0x5d465cd75c675bf75b875b175aa75a3759c7595758e7587758075797572756b7564755e65577551654a7543753d6537653075297522751b7514750d750674ff74f874f174eb64e474dd74d674cf74c964c364bc74b574ae74a774a074997492748b7485647f64787471746a7463745c7455744e74477441643a7433742c74257
|6,2=>0x78d7786777f77787771776a7763775c7755774e7747774077397732772b7724771d7716770f7709670276fb76f476ee66e776e076d976d276cb76c476bd76b676af76a876a1769a7693768c7686667f76787671766a7663765c7655764e76477640763b5634762d7626761f76187611760a760375fc75f575ef65e875e175da7
|6,3=>0x943693c7935792e7927792079197912790c6906690068fa68f378ec78e578de78d868d178cb68c478be68b778b078aa68a3789c7895788e7887788078797872786b7864785d7856784f78487841783a7833782c7825781e781778107809780277fb77f477ed77e677df77d877d177ca77c377bc77b577ae77a777a0779977945
|6,4=>0xa177a107a097a0279fb79f479ed79e679e069d979d279cb79c479bd79b679af79a969a2799b7994798d7987698079797972796b7965695e7957795079497
|7,0=>0xbe07bd97bd27bcb7bc38bbb8bb47bad7ba67b9f7b987b917b8a7b828b7b7b747b6e6b677b5f8b578b4f8b478b3f8b387b317b2b6b247b1d7b158b0d8b067afe8af86af17aea7ae28adb7ad56ace7ac68ac06aba6ab37aad6aa67a9e8a977a916a898a836a7c7a757a6f6a678a5f8a587a508a497a427a3b7a347a2d7a258a1e7
|7,1=>0xdb38dab8da38d9b8d947d8e6d877d7f8d778d707d697d636d5c7d557d4d8d458d3e7d377d307d288d208d197d127d0a8d037cfd6cf58ced8ce67cdf7cd87cd08cc97cc27cbb7cb47cad7ca67c9f7c987c908c897c827c7b7c738c6c7c648c5c8c557c4d8c467c3e8c377c2f8c287c217c198c127c0a8c037bfd6bf67bef7be78
|7,2=>0xdc26dbb7
|8,0=>0xe3c7e366e2f7e287e217e1a7e137e0c7e057dfe7df77df16dea7de46ddd7dd67dcf7dc87
|9,0=>0xe436
|_,_=>0
def wAt:=mkWire dB 269 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1300806051020510a01d0707c130510101906051150310203106052010730a0300a031010730a0300a031010730a0300a03113008060511307c06019151210200d0a0330a0320a0300a031010730a0300a0311101902031038310707c03031080480a0890601d0d80a0a0300a0310a0d903832170730a0300a031070300a031020710200d0a03002031020510a0310d80d020710a030010190a0310804803851
|1=>0xa0300a031030d903832030730200d0a030071f502051021d20601d0200d0201d061e503052030710200d0a0300200d0a031020510304902051038513885201806019bb058320a1a9048300a0300200d0a0310707c02051030310a121020310a03233851030322d0330701d048730200d0a03002195020310398d08050020310581d02185018730a03002051021210a032010730a0300a0310a01d030310a031
|2=>0x200a0a0310805302031030310200d0201911850058310805102031030310583002019048710200d0a030020090304a03851020710a0300a0310703002051061e703052038310200d0a0320719f02051020710200d0a0300207d0200d0605101a391305228832058532d0331305105853020190a0310907c019b9058320a031019bb05832020192d033020490801902031010190a0310d80d020710a03002071
|3=>0x3031022f50a031031f5018320200d0a0320783103051022e901804020310a0300a0311303309033038510a2d50f81f022ce0a0310a0310207e030310499f0200d0303203179020510805002031020310584a02019021b905832020190a19d030320200d0a0310219d02051020511307d090330385111850058310801f020310703002051060510398f080500318d0805002031030513c831030520703202051
|4=>0x7032020516a81f0800d020310201902051010730a0300a0312d0331305107033020510204a0200a0a0316883204853039e503052020190f81f030310a01b03831030520207e0a08b638310805202031022e90180403819020310101d0a03109033038510180603819058310200d0a1210a0320480b0a0310200a0a031038310703302051130520201d01a9b07030020510480b0a03102031038310205202031
|5=>0x219d030320201d020310383102051020310a031019790701f020510f853130520200a0a031090190a01d010730a0300a0310207e0200d0a0330a032020320a08b038310a0d903832020192d0300204913051063890201d031210a032070330323d060510a0300a0310101f06051018c103852048730a0300101f060511101903831020190a369020322d0300701d021e50305201806038190201d1b05103832
|6=>0x20310a03102051020190801d020310a03103032048080a0310a031048080a031020310205106052130080605101a9907030130530201d0a01d030310a0310101b0a0310f85303031058480a01d0318f08050130530a03103851060517b01b0700d02051020510385102031038a906052023d1018c303852061950203101852018a70801b020310200d0205106051010190a031078890f84a03031060511c80d
|7=>0x383102052020510385105830020190601f03051018710a030020c103852020310a032030310a0310f81f03031030730a0300200d0a0300383202052018730a0300200d0201905833020190199d030320805202031020310a031038a906052030710a030130510201d0399501852030310a0313e851018320a0300a0310101b0a0310203101819021f5018320800d02031060510203205832020190200d03052
|8=>0x18c3038520805302031058530201902031038190801b020310700d0205107030020510a19d0303209019038510203106052058310201903031020190585102019018090a0313c831030520301d0201d020710a030058510201911019038310200d03851039970185202031038310805102031030510201d130190201d0a019038310a01d020190301d03832030310a032020710a03002031038320601d0201d
|9=>0x2051018320180a0a03106019020320200d0383102031038520203103031020090a0313c832030520701b020510581f020190207e0303103369020320200e0303102031030510200d0a0320203103032030d90383202051038320a08b03831020190a0320f851030314a032020520a0310a1210a032030520201d0200d0a0310205101831048330200d021210a0320a031048330200d0383203052048300200d
|10=>0xa0320a031018190185101852038510200d02019020510a03003052020730a0300200e0a0310a0310a0310200a0a03103031038510101b0a03101806038190200d0303202051030310a0310581d020194a0310205201804038190a01d038310303103819130520201d0a0310603d0305102031020510200a0a03108052020310a031021e503052090330385102049038510800f020310a0330a0320701d02051
|11=>0x30320200e020520200d0381903831
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x91000000000000000222000000000001f30000000070c00006880000000000064400000001720000000050c00000000000000000048800000000000000000000000003cc00000000000000000038400000000000290091000000002040000000000000004400000220000002
|5,1=>0x433100c0000f883c20ec40000e84000000038200000000d4c00000003230bcc2c300000000000000000000000002a200002820000000
|6,0=>0x26849820000962000094224880000000911000090100008e22344000228c88221880000000842204c7e300000001f0800000007931dc87611ccc0001c480001b8c6c21ac40001a0c00000006711984642000000018885f300005c3164c572154852314084d3130449300000001204462
|6,1=>0x38480000000e010000de236ccd920000d7200000003548d4134c40003448cf23348ca300000003208c530000c4100000000000c220000c022f88bc22e4cb720000b520000b232bcc00000000000000ae100000002b08a9329c80002948a412888000280800000009d3270400000009b1
|6,2=>0x4d093224c452f24b4800000012b200000004a0d2620000000494524148c4000480d1d347051a2460916200011510001123000000044090e243450b200010920000000418c000410903100010123fc8fd23ec8f923dc8f523d040003c88f113bc8ed20000eb23a84e82394c0000000e32
|6,3=>0x628d8910001872614984160898115f8d7b35e0d7535d040005cc40005c496f25b0d6b15a0c00059c565258c80005884000580800000015f157495b2568400056095625509522000150200014e252cc000000149251c945250c800050854024f880004f093b14e840004e440000001363
|6,4=>0x1b626d45b326c0c0000001ae20001ac26a8800069cda520001a3268499f267859d166c8000660d962000195164c9903000000000018d3
|7,0=>0x8d8a3428c8a3028b8a2c28a8a282898a242888a202878a1c2868a182858a142848a102838a0c2828a082818a042808a0027f89fc27e89f827d89f427c89f027b89ec27a89e827989e427889e027789dc27689d827589d427489d027389cc27289c827189c427089c026f89bc26e89b82
|7,1=>0xac06af1ab4aab2aa4aa72a94aa32a886a02a78a9c2a68a982a58a951a4ca912a3ca8d2a3068a2a20a862a10a822a00a7e29f0a7a29e0a7629d0a7229c0a6e29b0a6a29a0a662990a622980a5e2970a5a2960a562950a531944a4f2934a4b2924a4729186442908a4028f8a3c28e8a382
|7,2=>0xaccab12
|8,0=>0xb146c41b0c6c21b046c01afc6be1af46bc1aec4000ae86b91ae06b71ad86b51
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x101800080000032000010100005c000029800014000009e00004d000024000010a0000830000410000204000100000060000023800010800004800001b00000a000004800002000000e000005000002000000c0000040000018000008000002000000
|1=>0x6408003014001804000c010004c000024000011040008800004080002008000f020007110003808001bbc000a200004ff00027d800137c0009b60004cf00024f00012440008de00044f00020b000102c0008080004020002008001000000520000283
|2=>0x20238010098008044004006002001000c21400600600208500104080053fc0029be0014cf000a4f80052040028be00140f000a03000501400280400124a00084f000427000210200108000083200040d80020160010060008010004004002000000d00
|3=>0x20a1f810004c08001604000402000000e3048063836030c1f014a0900a000004a82402141201002000800000229be01149f008a0f804503c02203601009200802500401200200100100020062090021010010000005036002813001401800885600440f
|4=>0x54689828366c12a8b609149b048a2f824506c12181e090493043a05821122c107b3608368d0416cd8209a2c10491608168f04025582000040e091e050048028005012500808a83e043c8b021a4e810d26c083a0204178b020a6f810527c082936041495
|5=>0x20020b100080080000240000011026f8821090410844200d8110026f88010984008202004000c8645864302c311b3618648b0c1a05860326c30095618048b0c0053851504c286836108d0108200004002941e289e0f064f07826783c112c1a29360b0c0b
|6=>0x838345c04000d8a00148b144b458a05a200008c4283a62041f241ecc9105b7c882c9e44074b210a0d904127c800d3640069120028990014008009be40049f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x23300021c1100090000020000050000020202000000000000000a0002000000001700000000020000000200002400020000000900000200000200000000000200000000000000020000000000100000000811000009000000001b00020002
|6,0=>0x1a00000d002242020012000048093a000214bd430000020f007b0000000200430606b201380100596c00000065be000002304700020401000100a74a11000019b402001f00022200003a0016008e01004522220000024a2f00000200000c063a7a00220018120900030000bc110100000e180020050202177c5f3b1700000901
|6,1=>0x7d090043023a22b57e7463243a00760006392e114b001173020037002200000901021e0022020102000700023d0000010222020004020100021141000900002d22220943ce00003600003c0b0000403a720005c53a02026800110005000007011d220025000007000204000bc269021202c41e00023a010100695b226d000022
|6,2=>0x25d074421000a000201002302000213020902340007010031022b00000005
|7,0=>0x6b57442a90989c1435b12cc5cdcb666a9263505c5d29ccb9a255b94ca5a979bf9761518fae918684146faa884dc14958558c553e6e8bd08912cf4e9ac060acc396a47f82b862b0afada2289f56a69578c6755e3fa82a3f8587558a7727b681527130645a9351704f53b3aca12c62b755ba8d949b2e15d29dd146819962ab6780
|7,1=>0x54c9
|8,0=>0x81c82ca29ec783cad3a38d50bba0ac325528
|9,0=>0x26
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 7 roots_186 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dom_179 6 roots_179 ops++addP pm 3 dom_171 7 roots_171 ops++addP pm 4 dom_57 5 roots_57 ops++addP pm 5 dom_147 4 roots_147 ops++addP pm 6 dom_163 5 roots_163 ops++addP pm 7 dom_178 5 roots_178 ops++addP pm 8 dom_168 4 roots_168 ops++addP pm 9 dom_162 4 roots_162 ops++addP pm 10 dom_185 7 roots_185 ops++addP pm 11 dzo_168_16 4 roots_168 ops++addP pm 12 dom_59 6 roots_59 ops++addP pm 13 dom_58 4 roots_58 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dom_153 4 roots_153 ops++addP pm 16 dzo_171_16 6 roots_171 ops++addP pm 17 dzo_169_16 5 roots_169 ops++addP pm 18 dom_43 5 roots_43 ops++addP pm 19 dzo_170_16 5 roots_170 ops++addP pm 20 dom_154 4 roots_154 ops++addP pm 21 dom_177 4 roots_177 ops++addP pm 22 dom_41 4 roots_41 ops++addP pm 23 dom_139 4 roots_139 ops++addP pm 24 dom_170 5 roots_170 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_168_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_171_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_169_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_170_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_170 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 7 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 96 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 287 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 31 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 287 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 130 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 130 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_187 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_187 roots_187 goal_187 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_187
theorem lowS_187:Lower true dom_187 roots_187 goal_187 10:=S_187.noCircuit
def dzo_173_16:=0x333300003333000000000000000000003333000033330000
def gzo_173_16:=0x333300003332000000000000000000003332000032320000
def gsh_173_16:=0x33330000333200000000000000000000333200003232
theorem lowS_zo_173_16_168:Lower true dzo_173_16 roots_173 gzo_173_16 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_16) [(dom_173,16)] (by decide +kernel) (lower_slice_b (T:=gsh_173_16) [(0x22220000222200000000000000000000222200002222,0,1),(0x30300000303000000000000000000000303000003030,0,4)] (by decide +kernel) lowS_168)
def dzo_185_4:=0x303030303030303000000000000000003030303030303030
def gzo_185_4:=0x303030303030303000000000000000003030302030302000
def gsh_185_4:=0x30303030303030300000000000000000303030203030200
theorem lowS_zo_185_4_41:Lower true dzo_185_4 roots_185 gzo_185_4 6:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_4) [(dom_185,4)] (by decide +kernel) (lower_slice_b (T:=gsh_185_4) [(0x30300000303000000000000000000000303000003030000,0,16),(0x30303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_41_4:=0x303000003030
def gzo_41_4:=0x302000002000
def gsh_41_4:=0x30200000200
theorem lowS_zo_41_4_41:Lower true dzo_41_4 roots_41 gzo_41_4 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_4) [(dom_41,4)] (by decide +kernel) (lower_slice_b (T:=gsh_41_4) [] (by decide +kernel) lowS_41)
def dzo_172_16:=0x111100001111000000000000000000001111000011110000
def gzo_172_16:=0x111100001110000000000000000000001110000010100000
def gsh_172_16:=0x11110000111000000000000000000000111000001010
theorem lowS_zo_172_16_168:Lower true dzo_172_16 roots_172 gzo_172_16 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_16) [(dom_172,16)] (by decide +kernel) (lower_slice_b (T:=gsh_172_16) [(0x10100000101000000000000000000000101000001010,0,4)] (by decide +kernel) lowS_168)
namespace S_189
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(4,20),(4,132),(5,13),(5,21),(5,37),(5,133),(8,9),(8,40),(8,136),(12,13),(12,28),(12,44),(12,140),(16,17),(16,20),(24,25),(24,28),(24,56),(24,152),(32,33),(32,40),(32,160),(36,37),(36,44),(36,52),(36,164),(48,49),(48,52),(48,56),(48,176),(128,132),(128,136),(128,160),(129,133),(129,137),(129,145),(129,161),(144,145),(144,148),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_189.map (·&&&dom_189)
def gM:=goal_189&&&dom_189
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x9400a0707b
|5,0=>0xaf3789036e8f4cb8a12b73658524cc441483fb6e2deda152b3128821113810c840b826026cf
|6,0=>0xe722adca16c4518a60238504a7efbc7efab77e03753d074e02706516e12c6da5a6bb9b60c5759c5257f284df514be9c4b59d45039432c243111423d540cc63ac1239df539a5d3730d35a463075e2b4b72b20c246dc2441f21f831d8351c3fb1b9551b4301a58319a0718c6915b68152b3148ba12e901045f0f7eb0f7770bf260a0a807237069a5012bb00bad
|7,0=>0xdda39d687cb626cb39a1ad26299084984cc7def9746c463d0e60ab654b7853b1750dd7475a2471b1350e32e1bb2896826436201001d62e1a49913111125d4116e70c0960b067097ec0684b024e1
|8,0=>0x9130f8014070cff68be267cf53abd31e7a1051d3
|9,0=>0x3abd3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc000000000000000000cc00cc0088008b3333333333033300000000000000000323232323230323088888888888888880000000000000000888888888888880333333330000000000000000000000003333333300000000cc00cc00cc00cc000000000000000000cc00cc00cc00cc02222222222222222000000000000000022222222222222220000000000c000c000000000000000004040404040c040c333333333333333300000000000000000000000000000000cccccccc888888880000000000000000cccccccc8888888b33333333333333300000000000000003300330033003300cccccccccc00cc000000000000000000888888888800880333333333300330000000000000000003333333333003300cccc0000cccc00000000000000000000cccc0000cccc000332233223322332200000000000000003322332200000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c333333333333333300000000000000002222222222222222
|0,1=>0x444044400000000000000000000000004440444000000000000000000000000000000003333333333223322cc00cccccc00cccc0000000000000000cc00cccccc00cc033333300333333000000000000000000333333003333330000cc00cc00cc00cc000000000000000000cc00cc00000001111000011110000000000000000000011111111111111004444444444444444000000000000000044444444444444033333333000000000000000000000000332233220000000000cc00cc00cc00cc0000000000000000008800880088008b33333333333333300000000000000003333333300000000cccccccccccccccc0000000000000000cccccccc8888888b2320000323200000000000000000000323200003232000044444444440044000000000000000000444444444400440000000000000000000000000000000003333333322222222cc88cc88cc88cc880000000000000000cc88cc88cc88cc8b13131313130313000000000000000000000000000000000
|0,2=>0xcccc0000cccc00000000000000000000cccc0000cc03333333333333300000000000000000033333333333333008888888888888800000000000000000088888888888888032323232323232320000000000000000323232323232323288888888cccccccc000000000000000088888888cc88cc8800000003322332200000000000000000000000033223322cc44cc44cc40cc400000000000000000cc44cc44cc40cc4333333333333333300000000000000001111111111001100ccccccccc0c0c0c00000000000000000ccccccccc0c0c0c332233223020302000000000000000003322332230203020c4c4c4c4c4c0c4c00000000000000000c4c4c4c4c4c0c4c3333030333330300000000000000000033330303333303000000cccc0000cc0000000000000000000000cccc0000cc030300000303000300000000000000000303000003030003044444444444444440000000000000000440044004400440333033303330333000000000000000003330333033303330
|0,3=>0xcccccccc00cc00cc0000000000000000cccccccc008800880000000333333330000000000000000000000003333330000000000000000000000000000000000cccccccccccccc0330033003300330000000000000000003300330022002200cccccccccccccccc000000000000000000000000cccccc0000000000033003300000000000000000000000000220022cccccccccccccccc0000000000000000cc88cc88cc88cc8b3333333333333330000000000000000333333333322332200000000cccccccc000000000000000000000000cc88cc8b33333333333333300000000000000003333333333003300cc44cc44cc44cc440000000000000000cc44cc44cc00cc033333333333333330000000000000000000033330000330000000000cccccccc0000000000000000000000008888888800000000000000000000000000000001111111111001100ccccccccccc8ccc80000000000000000ccccccccccc8cccb33300003333333300000000000000003333000033333300
|0,4=>0xcccccccccccc00000000000000000000cccccccccccc000333330303333303000000000000000003333303033333030c0c0c0c0c0c0c0c00000000000000000c0c00000c0c0000333333333322332200000000000000003333333333223322cccc8888cccc88880000000000000000cccc8888cccc888b3333333333333330000000000000000303030303030303000000000000000000000000000000000cccccc00cccccc003020302030203020000000000000000030203020302030200000000cccccc00000000000000000000000000cccccc033333333333333330000000000000000333333003333330000000000cccccccc000000000000000000000000cc00cc0000000000000000000000000000000003333333333003300cccccccccccccccc0000000000000000cccc0000cccc0000303030303030303000000000000000003030000030300000000000000000000000000000000000000cc00cc0088008911111111111110000000000000000001111111111111100
|_,_=>0
def sP:Nat→Nat
|0=>0x3c3018b022840c06440802e206033a2c08a1030e030228d88180c10b02006031604d08180c58132201980228b88080c10114202150644088182ca0126202120644088180c58114406030228788180c58e14206030c04505180c5811a202070618080180c58a12203830c042840608080
|1=>0x62c08a103018b0229788083018b02b4404182ca011420603160558a10301821604508180c58100a840c06a45811420603160452810301a61604508180c5a5022840c060450f105860316045212c30191160400c482c08a103018b4428404180c08a4220603160451f1010b03160400a
|2=>0x7c21e8c062c08a10301bc022840c062c08a7620603160453a1010b030c045032260581142038c060450f10e06031604508180c080143c40c062c08a6e21b0c062c08014301b51604508180c58114d0416062c08a66206031604505103018b02299082a30181143c431180c5811420630
|3=>0x180c5811420207062c08a103018b0229188180c5811514444190c18b02286031605688083018b0300404180c58a8420603780400a103018b022a088180c5818020207061808a10546030c2c08a08301b9022843f180c5811420a8c06f008a10301b90228b88180c30b022998c062c08a
|4=>0x22840c062c542103230316045085c3018b0228415180c581142060316045331030191172808a10d8b0c062c08a109c603222c08a10301b9222c08a103248316045080e301861604508180c581152040c062c08a8e206031604521101c603222c088180c88b020040c8c0c30b0228444
|5=>0x62d601142020c062c08a103270316045080e3018b022840c062c08014206031604508192c18b022844f180c5811422604180c581142020c062d601142020c9c0c58114206031734508083018b02005085c106031604508983018b0228415180c581002840c062c08014cc404192c18b
|6=>0x3018b022840c
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd86745dca770ddbc76d99af76a1da17669d937631d8575f9d7775c596a758dd5d6559d4f7521d4174e9d3374b1d257479d177441d097409cfb73d1ced7399cdf7361cd17329cc372f1cb572bd8a87285c9b625588e721dc8071e5c7271adc647
|7,0=>0x2c28aea2b28ab1aa48a722957a3628589f627769c1e697989e5b794e24b890e23b88d1e2c8895e1e785de107825e0187e9df377b1de57
|8,0=>0xbe9ef37bb1ee57b79ed86b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 80 190 0x3fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14211602142116011602180214212a2c18011421080214211621182d182118e4222116560e212a2f1801181916212a332c2918210800182d1421180114210e2d0c335c28080d182d06b002290c331621225818211629184616294e441629028f080f182d0c2b1621401f18291029165a18212258182116291801102908001421
|1=>0x18291801142118021421182d0629030e06210c0d1621080d182d1801142118021421162902212c2d182118051629222116293823160d16211829220716293833160d0c2b162116291829162910290c0d16210823182d182d1829080f182d0c3316210823182d5c28080d182d5c2b080d030e06212a2c18011421180114211601
|2=>0x229182d0605182914210629180d0829182d182d02290605182d030c0621182d1421080d182d0e2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x43022000000000000000002000000000
|6,0=>0x4d24a34824624330000000004123f23d20003b23920000003630003423132f22d20002b20002920000002632330002122011f10001d21a31821531320000001120000000000000000e30c20a2000000091000072
|7,0=>0x8b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f2
|8,0=>0x9319219119018f10008e18d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x1006080701bc0340d601806f00803f80301bc01001c0060090030008006000000c000002c30000828000314000186000071000037800019c0000cc000040000010000003c00001a00000b000004000001800000a0000040000018000008000002000000
|1=>0x20301ff0000c260001911401fc80306431206f1880038c0800c4302de21200710803788004142100de10410608003783001fc10006605187f02807781401fc0905de0480ef
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x6080000000080000
|6,0=>0x2d00821400000841005c20000c00990410010010004ca00255600244118700010000000034430000200b
|7,0=>0x2e5346cacf0a89963922b5c7e8498c888327ac771a6f89a
|8,0=>0x867d6b70e9a2
|9,0=>0xf
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_181 7 roots_181 ops++addP pm 2 dom_157 7 roots_157 ops++addP pm 3 dom_61 7 roots_61 ops++addP pm 4 dzo_173_16 6 roots_173 ops++addP pm 5 dom_173 7 roots_173 ops++addP pm 6 dom_185 7 roots_185 ops++addP pm 7 dzo_185_4 6 roots_185 ops++addP pm 8 dom_29 4 roots_29 ops++addP pm 9 dom_168 4 roots_168 ops++addP pm 10 dzo_168_16 4 roots_168 ops++addP pm 11 dom_41 4 roots_41 ops++addP pm 12 dzo_41_4 4 roots_41 ops++addP pm 13 dom_180 4 roots_180 ops++addP pm 14 dom_53 4 roots_53 ops++addP pm 15 dzo_57_4 5 roots_57 ops++addP pm 16 dzo_172_16 5 roots_172 ops++addP pm 17 dom_57 5 roots_57 ops++addP pm 18 dzo_169_4 5 roots_169 ops++addP pm 19 dom_172 5 roots_172 ops++addP pm 20 dom_149 4 roots_149 ops++addP pm 21 dom_156 4 roots_156 ops++addP pm 22 dom_165 4 roots_165 ops++addP pm 23 dom_141 4 roots_141 ops++addP pm 24 dom_169 5 roots_169 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_189 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_173_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_185_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_168_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_41_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_172_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_169_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_169 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 7 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_189 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_189==dom_189)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_189 gM v ys):RunD true dom_189 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_189 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_189 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_189 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_189 roots_189 goal_189 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_189
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=S_189.noCircuit
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005554000000000000000000005554000054540000
def gsh_174_16:=0x55550000555400000000000000000000555400005454
theorem lowS_zo_174_16_168:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x44440000444400000000000000000000444400004444,0,2),(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) lowS_168)
namespace S_190
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,20),(4,132),(6,22),(6,38),(6,134),(8,40),(8,136),(10,26),(10,42),(10,138),(12,28),(12,44),(12,140),(14,30),(14,46),(14,142),(16,18),(16,20),(24,26),(24,28),(24,56),(24,152),(32,34),(32,40),(32,160),(36,38),(36,44),(36,52),(36,164),(48,50),(48,52),(48,56),(48,176),(128,130),(128,132),(128,136),(128,160),(144,146),(144,148),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_190.map (·&&&dom_190)
def gM:=goal_190&&&dom_190
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd4035bad953e56e3d0dd390ae
|5,0=>0xf3ed7d7b3ec8d97c2137be15bb9effb3d27a8754a10e78ddf76208351f4f3cbb72f8f11b01b
|6,0=>0xf68b6f3ed7e8fd1e14b8ddffdda8f8da4f4d5905d075fc241ac19bfbe4b4af12aadc55a4025a24aaa1bc29de4d9b9ea99370916bb7fa627a28a73282704ff6998f68c5665b8c63cae61feb5deea1e3eb0e26c0ddc00b95d08dab04a08
|7,0=>0xddffddbb9abda08b7830a2c2e8d12586ebf7660753afd148d0
|8,0=>0xf79e0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000015555555554015402aaaaaaaaaaaaaaa80000000000000002aaa80002aaa8000550055005500550000000000000000005500550055005500aaaaaaaa000000000000000000000000aaaaaaaa00000001555155515551555000000000000000015551555151515152aa22aa22aa22aa200000000000000002aa22aa22222222255555555555555550000000000000000000000000000000000000000aaaaaaaa0000000000000000aaaaaaaa000000011111111111111110000000000000000111111111111111100000000002a802a8000000000000000002a802a80000000555555555555555500000000000000005555555500000000aaaa0000aaaa00000000000000000000aaaa0000aaaa0001414141414141414000000000000000014141414141414142aaaaaaaa222222200000000000000002222222222222222005500550055005500000000000000000055005500000000
|0,1=>0xaaaa00000000000000000000aaaa0000aaaa0001555400015555555400000000000000015554000155540002a802a802a802a8000000000000000002aaaaaaaaa802a80000000005500550000000000000000005500550055005500aa00aa00000000000000000000000000aaaaaaaa0000000000000000000000000000000000000001555555540000000000000002aaaaaaa80000000000000000000000000000000555555550055005500000000000000005555555500000000aa00aa00aa00aa000000000000000000aa00aa000000000000000000000000000000000000000001555400015554000002a802a800000000000000000000000002a802a80000000555555555500550000000000000000005500550055005500aaaaaaaaaa00aa000000000000000000aaaaaaaaaa00aa01555555555555555400000000000000015401540154015402aaaaaaa8000000000000000000000000000000000000000555555555555555500000000000000000055005500000000
|0,2=>0x2aaaaaaaaaaa800000000000000000002aaa80002aaa8000000000000000000000000000000000000055005500000000aaaa00aaaaaa00aa0000000000000000aaaa0000aaaa0001555555554141414000000000000000014141414141414142aaa80000000000000000000000000002aaa80002aaa8000555555555555555500000000000000005555555555005500
|_,_=>0
def sP:Nat→Nat
|0=>0x8620b6c330218810b0d708620b0c21802070cc0866030865482c32422041c330218b34218020b5821802042c32422040c21953c40d40861030860114c40d208610330204b0c21903ce2cd3021870c21802c32892070c21851030861440c2040
|1=>0xcc0860082da34c0862042d63021882da58c08620b84c0862202c330218810330219520b7cc0862132c34821882de3021886833021994cb34c0862040cc08645d2c33021882c37021882c33020482c35c21882c33021902131033021884da0cc
|2=>0xcc0862112c348c08620b0cc08620f2c330219520b94c08620b0c218020b0cc08690838b0cc0862042c33021882cd3021952042c308600860b0cc0862042c348c0862c30865483cb8cc08620b0cc88620b0d40862042c330218f10b34c08620b
|3=>0xb0cc0862042c33021882da0cc08620b34c08620b58c0862132c33021882c330218864b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c8a5e62ca94d89ac47620b0ed86ca30615309543ec196
|6,0=>0x15f6acb549e96f4479ebcd9e5ef28790bc6da2ad0f6843c05df4ef37763b95dbecd8768bb2d988ebe65c32c5d56ca474f3261924c8b74239f5cece6f7
|7,0=>0x344f9b7cab63db10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 191 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb212c8c3210c8cb312c88b203084c222ccc3452c804332c843212c84b210cf4c220914b203114b202c84b210d9cb222c843472c803652c88b232c883212c84b20311cb201914b2010c0b212c84b232cfda652c8cb225c644302c84c452c84b202c846452c84b20
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x28c001cc00000000000010c000c40300000
|6,0=>0x2f2b480000000b06b1002a10028298a428c4000000088400808007c5d2001b2649815880050922408003c4e134400
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf5fd5c6301bde13812027ddf575d214810440900354d1304370c81a0180400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x60388001006029800
|6,0=>0x9080142100502f187340c7b120aa44ac16c086500291c2
|7,0=>0x35a8cafbdce57
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_188 7 roots_188 ops++addP pm 1 dom_54 4 roots_54 ops++addP pm 2 dom_182 6 roots_182 ops++addP pm 3 dom_156 4 roots_156 ops++addP pm 4 dom_186 7 roots_186 ops++addP pm 5 dom_166 5 roots_166 ops++addP pm 6 dzo_174_16 6 roots_174 ops++addP pm 7 dom_174 6 roots_174 ops++addP pm 8 dom_62 5 roots_62 ops++addP pm 9 dom_158 5 roots_158 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_190 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_174_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_158 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_188 7 s (0,roots_188.map (·&&&dom_188)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_190 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_188 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_190 gM v ys):RunD true dom_190 gM v (ori ys):=h
def Z (s:Nat):=barP dom_190 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_190 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_190 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_190 roots_190 goal_190 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_190
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=S_190.noCircuit
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,34),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,34),(32,40),(32,96),(32,160),(64,65),(64,66),(64,72),(64,96),(64,192),(128,130),(128,136),(128,160),(128,192),(129,131),(129,137),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x9bef0
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x58d11ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa5
|_=>0
def oO:Nat→Nat→Nat
|8,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>1
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_234 8 roots_234 ops++addP pm 1 dom_107 8 roots_107 ops++addP pm 2 dom_233 8 roots_233 ops++addP pm 3 dom_227 8 roots_227 ops++addP pm 4 dom_203 7 roots_203 ops++addP pm 5 dom_171 7 roots_171 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_171 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_234 8 s (0,roots_234.map (·&&&dom_234)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_234 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_235 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_235 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_235 roots_235 goal_235 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_235
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=S_235.noCircuit
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030200000302000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003020000030200000200
theorem lowS_zo_233_4_105:Lower true dzo_233_4 roots_233 gzo_233_4 8:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_105)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,40),(32,96),(32,160),(36,37),(36,44),(36,100),(36,164),(64,65),(64,72),(64,96),(64,192),(68,69),(68,76),(68,100),(68,196),(128,132),(128,136),(128,160),(128,192),(129,133),(129,137),(129,161),(129,193)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xe664b2768e1c83716d08
|7,0=>0xeb17e48ebc487c740c90
|8,0=>0x4e2f6
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc000000cc000000cc00000000000000cc000000cc000000cc0000000333300003333000033330000000000003333000033330000333300000000cccc0000cc000000cccc0000cc000000cccc0000cc000000cccc0000cc0222200002222000022220000222200002222000022220000222200002222cccc0000cccc0000cc000000cc000000cccc0000cccc0000cc000000cc0333300003333000033330000330000003333000033330000333300003300cccc000000000000cccc000000000000cccc000000000000cccc0000000330000003300000033000000330000003300000033000000330000003300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c111100001111000011110000110000001111000011110000111100001100cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300003333000033330000333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x543810574381065438105438b1065743810a5743809a738095432105432106543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x28c35c3b007
|7,0=>0x60ea5d0c1a7
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x105575054a945575055150554545415a31951568d5d415a357505
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0xfffbd7fd7f3fc7f0700e03400
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x4321
|7,0=>0x9587
|8,0=>6
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 8 roots_236 ops++addP pm 1 dom_105 7 roots_105 ops++addP pm 2 dom_233 8 roots_233 ops++addP pm 3 dzo_233_4 8 roots_233 ops++addP pm 4 dom_229 7 roots_229 ops++addP pm 5 dom_205 7 roots_205 ops++addP pm 6 dom_173 7 roots_173 ops++addP pm 7 dom_141 4 roots_141 ops++addP pm 8 dom_165 4 roots_165 ops++addP pm 9 dom_197 4 roots_197 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_233_4_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 8 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 10:=S_237.noCircuit
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_slice_b [(0x444400004444000044440000444400004444000044440000444400004444,32,34)] (by decide +kernel) lowS_236
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_slice_b [(0x50005000500050005000500050005000500050005000500050005000500050,16,20)] (by decide +kernel) lowS_242
def isoMvS_95:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_iso_b isoMvS_95 (by decide +kernel) lowS_63
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_175
def isoMvS_215:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_183
def isoMvS_219:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_187
def isoMvS_221:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_189
def isoMvS_222:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_190
def isoMvS_243:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_189
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_237
def isoMvS_252:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_125
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,16,18)] (by decide +kernel) lowS_125
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
def dzo_99_4:=0xf0000000f0000000f0000000f0
def gzo_99_4:=0xf0000000e0000000e000000000
def gsh_99_4:=0xf0000000e0000000e00000000
theorem lowS_zo_99_4_99:Lower true dzo_99_4 roots_99 gzo_99_4 5:=lower_iso_b (d1:=dom_99) (r1:=roots_99) (T1:=gsh_99_4) [(dom_99,4)] (by decide +kernel) (lower_slice_b (T:=gsh_99_4) [] (by decide +kernel) lowS_99)
def dzo_115_4:=0xf000f000f000f000f000f000f000f0
def gzo_115_4:=0xf000f000f000e000f000e000f00000
def gsh_115_4:=0xf000f000f000e000f000e000f0000
theorem lowS_zo_115_4_99:Lower true dzo_115_4 roots_115 gzo_115_4 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (lower_slice_b (T:=gsh_115_4) [(0xf0000000f0000000f0000000f0000,0,16)] (by decide +kernel) lowS_99)
def dzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def gzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000e000f00000
def gsh_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000e000f000e000f0000
theorem lowS_zo_243_4_99:Lower true dzo_243_4 roots_243 gzo_243_4 7:=lower_iso_b (d1:=dom_243) (r1:=roots_243) (T1:=gsh_243_4) [(dom_243,4)] (by decide +kernel) (lower_slice_b (T:=gsh_243_4) [(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000,0,16),(0xf000f000f000f000f000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_99)
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000fe000000fe000000fe0000
def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000fe000000fe000000fe
theorem lowS_zo_231_16_224:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0,0,4)] (by decide +kernel) lowS_224)
def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000
def gzo_230_16:=0x55000000550000005500000054000000550000005400000054000000540000
def gsh_230_16:=0x5500000055000000550000005400000055000000540000005400000054
theorem lowS_zo_230_16_224:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (lower_slice_b (T:=gsh_230_16) [(0x4400000044000000440000004400000044000000440000004400000044,0,2),(0x5000000050000000500000005000000050000000500000005000000050,0,4)] (by decide +kernel) lowS_224)
def dzo_227_4:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0
def gzo_227_4:=0xf0000000f0000000f0000000f0000000f0000000e0000000e000000000
def gsh_227_4:=0xf0000000f0000000f0000000f0000000f0000000e0000000e00000000
theorem lowS_zo_227_4_99:Lower true dzo_227_4 roots_227 gzo_227_4 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_4) [(dom_227,4)] (by decide +kernel) (lower_slice_b (T:=gsh_227_4) [(0xf0000000f0000000f0000000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_99)
def dzo_227_16:=0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000
def gzo_227_16:=0xf0000000f0000000f0000000e0000000f0000000e0000000e0000000e0000
def gsh_227_16:=0xf0000000f0000000f0000000e0000000f0000000e0000000e0000000e
theorem lowS_zo_227_16_224:Lower true dzo_227_16 roots_227 gzo_227_16 6:=lower_iso_b (d1:=dom_227) (r1:=roots_227) (T1:=gsh_227_16) [(dom_227,16)] (by decide +kernel) (lower_slice_b (T:=gsh_227_16) [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,0,1),(0xc0000000c0000000c0000000c0000000c0000000c0000000c0000000c,0,2)] (by decide +kernel) lowS_224)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,18),(16,20),(32,33),(32,34),(32,96),(32,160),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,96),(64,192),(68,69),(68,70),(68,84),(68,100),(68,196),(80,81),(80,82),(80,84),(80,112),(80,208),(128,130),(128,132),(128,160),(128,192),(129,131),(129,133),(129,145),(129,161),(129,193),(144,145),(144,146),(144,148),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>2
|6=>60
|7=>272
|8=>338
|9=>85
|10=>12
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xcf7b81100d
|6,0=>0xfe62ef5071ea215e75efe4ceddb95dd7b33cc007c77bcc13dcbeb0abd8c0bd5baaf0d2ac0bda9acea30aaa1650a12439ef5a9cdd79a764948d88f70e8c5f98a2368748d86068833e778b6b76836745f76f1786c86d6c56e69ea369d296833d6000c5a926581ab51ebf4d0e741ef33e2513874c2ef2e2ccfc2938b23e3d1ea361de0a152841265111570093cb090a0078300782702e66
|7,0=>0x5a2b359a6f5989c5803d566835636955b07523a751ebf50df7506e04ffd64f33b4eb894dc6b4c5264bee44bd0d4abd84a41849b204905647aa5473e646bc6466804496943c0d43b824371f435d54316b429c4429b14166f408df3d98f3d4d93c7cc3c4bf3b9243b1a03a2853949338298377ee36d2d36156360d735c59359ac33b1732f69324b430aa3308c9301172e3832cb442c7c62bb1a2b158282d027b9426fea26a672620724b6124736230982274c2252221903216a120856206942051c1febe1ec001ea071e8441e3651db5c1d9aa1d0981c9f41c6f71bdb81aa591a3b519e8a1727f160fb1601714e9714c1213dbe13bb013a4213a3f12c99124d311ab610df71065a0ee180bcac0bbbc0a11a0904d08ff7087b107dab07c7d06c9406a0e062fd058e604a210427503cd902fc502d4a022b30212801c9f015da01241
|7,1=>0xdef4cde891ddcafddb57db40bdac59d9e3bd8109d65d5d0c56d0641cfc91cfbc0ce2f6cc587cc465cbe29c9f7fc7a8bc7705c5d47c595ac5831c3af7c266ac041ebf0e5beb05bd6dfbc8b4bb2a2ba4deb92fdb72feb4e32b1221b114eb072eaff37aefb3ad12dacca7ac154ac0bdab50daa678a974ca76eba63bba5731a5142a3cf0a351da347fa2d62a1bd49e5789c8309c5639c5039a7349a1eb996a5978ab96020930b192e16919f790b298dde88c7948bf3f8a57d8a07d89992880ae87ab786ddd8311e8266581fe6807867f9bb7f6ed7ea787e1897dd3778f05774377639474bc373e7471c9671c6b711816ff556fd9f6f8ee6f7da6f1786e93e6e8096d4cd6d2366cdec6bced6b2986a78f68b8168358680be6802367f8c67e7765c8765a6c6594d62ec7622236110260d8f5dbf75c4045bf4c5bdbc5b7915adfb5a4ba
|7,2=>0xfecd9fe62efdc69fc8d7f54d7f5201f4939f2631ef22be9229e6dd2e64fde5c2fe4278e3e2be27cf
|8,0=>0x3f7833f2f73e8f93e3213d9313d8143c8fc3bfa03b6493b4c33add53adaa3900a38e63379d63790a368f33678436580323c83212631f7f31bf53179530ce2305a72fcab2faf92df022de1a2d0f82cfab2c7802bccb2b8d22b6fa2b5f02accd2aa8b2a99d2a9942a96c2a24f278eb276542719226b68269aa24ce02380622d3c22a77228da224ed220e3216a1210a11fbff1fb811f6891ed9d1e3ea1d73e1d05c1cd001be711bc011a76619843197b8194e11937218c0e183711802917f321798d1763e169af160fb157f514d8014cbc14934140c71363d12b8c126b6121ab118df10d04106c90fe2e0fa310f2e90e2790cedf0c7390bea80bd4a0bcac0b1f60acf909e8f0917b08d190802107887076d6074e006a60068360636f059e20590e0509704e340493d0429403e6203c0b02eae029110243701faf016290124e001d7
|8,1=>0x99ba297f539586e9424b92f5392e8292bcc9160190f5e90b298e8298e4548dcc68cbff8c7698b9418b8bd8b4b889c55899078800487c4487ab7869fa8671385d9484e0d8400c8390982a7f82725814f280da0801047f9f37e8da7cf1c7cc0a7bc007a3607815776f0276a94748f973d6973877730ea717b67155b71181702b06fdb76f2906da956d6506d09c6ce4b6c9896b24d6ae956a17f6931468782681ed679316725c67040669b96571064eb764722635186335b62da56119e5f0f15ebad5cf915c2865b74b5b5125aec25ad335a7ff59671584ec5809657d5d57a15570e65418953c6a52d9652638511e75075750667500014ffd64f5594cbf84c9a74c8714c3d24c3374bed14b5a149f1b49c614874a47a42475f54742745f3e451e544eae449694449f43e694330642e4742ccb429c441ece4166f414de408bc3f88f
|8,2=>0xff14dfd2fdfbd15fb5daf7f3cf65e6f4939f0b3aefba6eab95e98abe9229e805ae774be69d9e69c7e5af6e576fe3e2be348eddfc8dde42dc886dc1ffd9e92d94cad8d5ed8757d85bfd43f3d2236d20c8d1f12ce47ecd25bcc92ccc59ccbe29cb076ca838c9ab1c581cc55f7c4a1cc1fc3c0de7bee53bb49cbb420baa2bb9ce5b972fb96afb820ab7b22b3ec6b34a0b2158b0d09aeb12ae68dad4f6acca7ac89dabdc6ab391ab17ba63bba48baa3b2ca1b5ba18dba1865a0e369fa959f5489f0f49d1319ce709c56d9a4909a1eb
|9,0=>0xfef42f1896e9627e9229e829ae79ffe031ada888d8c40d73b2d5529c1f9ac1903b2322ab909ab85ba7cd1a63bba0be398a339646c93ab990afe8c647896fc8794985d968157c7e14e7c0507b98c7b2d372a546fb856f03e6ba716a68e6713a633fa608ac5ff145ea7d5ea6f5e70b5d0ec5cab95b2165684650acd464a7403353d5173a1ef37d6636715360c334a6b341233248b30b152fe902e7902b78e2b0e8273eb233ff217f21bc01170591642915c7214cc7145c41063e0b4670acbe0ac8f0924909031063440328302d7f022ed0204001756
|10,0=>0xf4e48e7273e1000b47c39ac027fd216aad4650425fce33c1d507a190428f
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5500550055005500550055000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000ff000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc55005500550055005500550055000000550055005500550055005500550000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00001100110011001100110011001100110011001100110011001100110011000003000300030003000300030003000300030003000300030003000300030000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|0,1=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00f000f000000000000000000000000000000000ff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff00f000f0ff00ff00ff00ff00ff00ff00fc00fc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff000000000000000055005500550055005500550055005500550055005500550055005500550000330033003300330033003300330033003300330033003300330033003300000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa
|0,2=>0xf000f00ff00ff0000000000ff00ff000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000000000000000000000f000f000f000f0000000000ff00ff0000000000000000ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00000000000000000000000000000000550055000000000000000000ff00ff0055005500000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000f000ff00f000ff00f000ff00f000f000f000ff00f000ff00f000ff00f000f0000000000000000000000000ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00000000000f000f00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000000000000000000f000f000f000f00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff0000000000ff000000ff000000ff00ff0000
|0,3=>0xff00ff00ff00ff0000000000ff00ff00ff00ff00ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00aa00aa55005500550055005500550055005500550055005500550055005500000000000000000000000000000000550000005500550055005500550055005500005500550055005500550055005500550055005500000000005500550000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00ff00ff00ff00f000f000f000f000000000000000000000000000000000ff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f0ff00ff00ff00ff00fc00fc00fc00fc00cc00cc00cc00cc00cc00cc00cc00cc000000000000ff00000000000000ff00000000000000ff00ff000000ff0000000000000000000000000000ff000000ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00f000f000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f000f000f0
|0,4=>0xff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aaff00ff00ff00ff00ff00ff00aa00aa00ff00ff00ff00ff00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff000000ff00ff0000000000ff00ff000000000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000ff000f00ff000f00ff000f00ff000000ff000f00ff000f00ff000f00ff0000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00550055005500550055005500000000ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000055000000550000005500000055000000550055005500550055005500550000000000000000000000000000ff00ff00000000000000000000000000ff0000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000
|0,5=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ff00ff00ff00ff000000000000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f0ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000ff00ff0055005500ff00ff0055005500ff00ff0055005500ff00ff000000005500550055005500550055005500550055005500550055000000000000000000000000000000000000000000000000ff00ff0055005500ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa000000000000000000000000ff00ff00000000000000000000000000f000f0ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00f000f0ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00000f0000000f0000000f000f000f000f000f0000000f0000000f000f000f00000000ff000000ff000000ff00ff00ff000000ff000000ff000000ff00000000000000000000000000000000000000000000000000000000ff00ff00f000f0ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00f000f0
|0,6=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f0ff00ff00f000f000ff00ff00f000f000000000000000000000000000000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff00000000000000000000000000000f000f00000000000000000000000000000000ff00ff0000000000ff00ff000f000f00ff00ff0000000000ff00ff00000000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000ff00000000000000000000000000000000ff00ff0000000000ff00ff000000ff00ff00ff0000000000ff00ff00000000ff00ff000000ff00ff00ff000000ff00ff00ff0000000000ff00ff00000000000000000000000000000000ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff000000ff000000ff0000000000000000000000000000000000000000f000ff00f000ff00f000ff00f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff000f000f00ff00ff00ff00ff00ff00ff000000000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000
|0,7=>0xff000000ff000000ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000000000000000000000000000000000000000ff00ff00ff00ff000000ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000f000f000f000f000f000f00000000ff000000ff000000ff000000ff000000ff000f00ff000f00ff000f00ff000000000000000000005500550055005500000000000000000055005500000000ff00ff00ff00ff005500550055005500ff00ff00ff00ff00550055000000000000000000000000000000000000000000000000ff00ff0000000000aa00aaff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff00ff00aa00aaff000000ff000000ff000000ff00ff00ff000000ff000000ff000000ff0000000000000000000000000000ff00ff000000000000000000000000000000000f0000000f0000000f0000000f000f000f0000000f0000000f0000000f0000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f0000000000000000055005500550055005500550055005500000000000000000000000000000000ff00ff00ff00ff005500550055005500ff00ff00ff00ff0000000000000000
|0,8=>0xff00ff0000000000ff00ff000f000f00ff00ff000000000000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000000000000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000f000f000f000f000f000f000f000f000f000ff00f000ff00f000ff00f000f000000000000000000f000f000f000f00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000aa00aaff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000f000f000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f000f000f0ff00ff0000000000ff00ff000000ff0000000000000000000000000000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff00aa00aa00ff00ff00aa00ff00aa00aa00aa00aa00aa00aa00aa00aa550055005500550055005500000000005500550055005500550055000000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff00000000000000000f0000000f000f000f0000000f000f000f0000000f000f000f0000000f0000
|0,9=>0xf000f000f000f000f000f0000000000000000000000000000000000000000af00af00af00af00af00af00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff0000ff000000ff000000ff000000ff00ff00000000000000000000000000000000ff00ff00ff000000ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff000000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00f000f000f000f000ff00ff0000000000f000f00000000000000000000000000000000000000000ff00ff00ff000000ff00ff00ff0000cc00ff00cc00ff00cc00ff00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00000000000000000000000000000000ff00ff00aa00aa00ff00ff00aa00aa0000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff00000000aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00aa00aaf000f000f000f000f000f000ff00ff00000000000000000000000000000000ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff0000000000000000
|0,10=>0xf0000000f000f000f0000000f000f000f0000000f0000000f0000000f00000000000000000000ff00ff000000ff000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00aa00aa0000ff000000ff000000ff000000ff000000ff00000000000000ff00000000aa00ff00aa00ff00aa00ff00aa00aa00aa00aa00aa00aa00aa00aa00aa00aacf00cf00cf00cf00cf00cf00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff000f000f00ff00ff000f000f00ff00ff000f000f00ff00ff000000000000000000000000ff00ff000f000f000000000000000000ff00ff00000000ff00ff00ff00ff00ff00ff0000000000f000f000f000f000f000f0000000000000ff000000ff000000ff000000ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00000000ff000f00ff000f00ff000f00ff000000ff000000ff000000ff000000ff0000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000aa00aa00aa00aa00aa00aa00aa00ff00aa00aa00aa00aa00aa00aa00aa00aaaa00aa00aa00aa00aa00aa0000000000ff00ff00ff00ff00ff00ff00000000
|0,11=>0xff00ff00ff00f000ff00ff00ff00f000ff000000ff000000ff000000ff0000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff00ff00aa00aaff00ff00ff00ff00ff00ff0055005500ff00ff00ff00ff00ff00ff00000000ff00ff0055005500ff00ff0055005500ff00ff0000000000ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aaaa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aa00aa00aa00aa00aaff000000ff000000ff00000000000000ff00ff00ff00ff00ff00ff0000000000000000550055000000000055005500000000005500550000000000000000ff00ff0000000000ff00000000000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000000000000000ff000000ff00000000000000ff000000ff000000ff00000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff000000ff000000000000000000000000000000000000ff000000ff00ff00ff000000ff00ff00ff000000ff000000ff000000ff0000
|0,12=>0xff00ff00ff00ff00000000000f000f00ff00ff00ff00ff0000000000000000f000f000f000f000f000f000ff00ff00f000f000f000f000f000f000f000f0aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00aa00aa0000000000000000000000000000000000000000ff00ff0000000000f000f000000000ff00ff00000000000f000f0000000000ff00ff00000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff000000ff00000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000000000000f000f000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00aa00aaff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ff0000000000000000ff00000000000000ff00000000000000000000000000000000ff00ff00ff00ff00000000000000ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff00000000000000000000ff00ff00aa00aa000000000000000000ff00ff00aa00aaf000f000f000f000f000f000f000f000ff00ff00ff00ff00ff00ff00f000f0
|0,13=>0xff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff000000000000000000000000ff00000000000000ff00000000000000ff00000000000000000000000000000000ff00ff00f000f0000000000000000000ff00ff00f000f0ff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f000f00000000ff00ff00fc00fc00ff00ff00fc00fc00cc00cc00cc00cc00cc00cc00cc00ccff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000000000000000000f000f000f000f0000000000000000000f000f00000000f000f000f000f000ff00ff00ff00ff00f000f000f000f000ff00ff00f000f000000000ff00ff0000000000f000f00000000000ff00ff0000000000f000f000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000000000000000000000000000000000000000000000000000ff00ff00ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000f000f000f000f0ff00ff00fa00fa00ff00ff00fa00fa00aa00aa00aa00aa00aa00aa00aa00aa000000000f000f00000000000f000f00000000000000000000000000000000
|0,14=>0xf000f000f000f000ff00ff00ff00ff00f000f000f000f000f000f000f000f000000000ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aa0f000f000f000f000f000f000f000f000f000f00000000000f000f00000000ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff000f000f0000000000000000000000000000ff000000ff0000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000ff00ff00f000f00000000000000000ff00ff00ff00ff000000000000000000ff00ff00f000f0000000000000000000000000000000000000000000000000ff00ff00aa00aaf000f000f000f000f000f00000000000ff00ff00ff00ff00ff00ff000000000000000000000000ff00ff00550055000000000000000000ff00ff00000000ff005500ff005500ff005500ff005500ff000000ff000000ff000000ff000000000000000000000000ff000000ff00000000000000000000000000000000aa00aa00aa00aa00aa00ff00aa00ff00aa00aa00aa00aa00aa00aa00aa00aa0f000f000f000f000f000f000f000f000f000f000f0000000f000f000f0000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000000000000000000000f000f000f000f000f000f000f000f000f000f0
|0,15=>0xff00ff0000000000ff00ff0000000000f000f00000000000f000f0ff00ff00ff000000ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00f000f000f000f0
|_,_=>0
def sP:Nat→Nat
|0=>0x40d0c2713110904250d0c13052404080d0c13230904080d0c0115220504080d0c210504080d0c1305080d0c2001001109040d0c1e131c0904080d0c18050408190c130904080d0c1318050408171601001504080d0c0a000504080d061312110904080d100f0e04080d0c0a00080d0c0b0a0100090408070601050403020100
|1=>0x10005280408070c130535080d0c0100050408070c0b0134051f080d0c0114090408070c01330504080d0c010532080d0601003104080d0c1314051f300d0c01092f04080d0c0105040c1602010005040d172e01000504080d0c132d05040816030100110904080d06131104080d2b2a0504080c1601001104080d0c29001109
|2=>0x80d0c390504080d470b01490504080d480105040807060100140904080d4701461104080d3b1305040c162e010045050408070c010504080d4401003a04080d0c0a01420504080d0c0114051f08070c013f0504080d0c003e0504080d3d010504080d3c01002c1104080d3b133a04080d0c01391c050408360c130504300d06
|3=>0xd0c2e01001c0504080d2b3d010504080d0c13180014110904080d0c130905040d0c5301000905040d0c1e13010504080d0c520100500504080d0c130105044f0d0c011b2c0504080d3d01001c0504080d47010504080d170100450504080d47013a05080d0c0b0114051f080d4701114c04080d0c1311094a080d0c13220e04
|4=>0x4080c1601001c05040d0c2e0100110504080d1048001105040d0c1e1300462c1104080d10004e0504080d0c0100110904080d570c1346110904080d10003e1c0504080d0c014e0504080d3d01002c1104080d5700551104080d0c01000504080d10480100110904080d0c3b133e110504080d0c1305040d0c2e130100450504
|5=>0x1c0504080d0c0164096504080d0c013e2c0504080d2b01110504080d2b1359110504080d0c13640504620d0c01001c110504080d102b610504080d0c0100220504080d0c01605f055e04080d0c010904080d0c5c13011a110904080d0c130504250d0c5b0100110904250d0c0100580504080d0c13011c05040d0c1e01000905
|6=>0x904080d0c18015f110904080d0c131104080d0c5c1300110504080d4401006c0504080d0c0100116a04080d0c01005a0504080d2b13011d090e04080d0c131105040d0c2e0100050e040d0c1e010069090504080d0c01116704080d0c010011226604080d0c0104080d0c0b013900140532080d0c01001c0504080d2b0159
|7=>0x4080d0c5c01001c0504250d0c010022057504080d0c013a110904080d0c01110904080d060100760904080d0c01001105040d0c7301000904080d0c130172110904080d0c7022050e04080d0c050408360c13110904080d57100c090408070c0111051f080d0c01640905040d0c2713011c04080d0c5c0100460504080d3d01
|8=>0x1002c0504080d0f01001404080d0c0139000504080d0c7d01000504080d2b012a7c0504080d0c0111051f04080d4701057a080d0c01000504080d100c78001c2204080d0c0139050e04080d0c600049090504080d0c011c05040d0c27010004080d0c26013900112204080d0c1339140504300d0c01001105040d0c27130011
|9=>0x4080d0c011b090e04080d0c13390504080d8401002c1104080d831300110904080d0c13824504080d0c0139001104080d0c3b133104080d0c0100220504080d0c81013a0504080d0c130105040d0c80013900050e04080d0c4100453a0504080d0c010504080d0c7f010005040d0c530100110532080d0c01005f05080d0c7e
|10=>0x904080d0c0a1301220504080d0c0b01220504080d4401002205040d0c1e0100110504080d0c138a0504080c1601001c0504080d0c1338090504080d0c890122051f04080d0c013a1c0504080d0c011c0504080d0601001109045d080d0c13340504080d0c0100140588080d0c0100090487080d0c1301051f04300d0c0109
|11=>0xc138f001c0504080d1701001104080d0c0a1300051f080d0c018e003e090504080d0c012c112204080d0c130904080d0c4b13090504080d2b3d0111220904080d0c135f04080d0c0139004504080d0c0a01005405040d0c53010005048c0d0c01000504080d0c138b0504080d171301001c0e04080d0c3900450504080d1701
|12=>0x93220504080d0c013104080d0c134e3e0504080d0c01920504080d100100110904080d0c0f01140575080d0c0100051f080d0c0b01002c1104080d2b1322052804080d0c0114050408070c010005040d0c27013900110504080d0c90001104080d0c2a001109044f080d0c131c04080d0c0a0100110e04080d0c39000504080d
|13=>0xf1301051f0408070c0145220504080d0c012c0504080d3b13010528080d0c018e000904080d0c5c0100050408950c0100941104080d10001104080d0c0a0100490504080d0f0100110504080d1701006d22051f080d0c011422051f080d0c010504080d0c0b01002c1104080d3b01004d0504080d3d010054050e40080d0c00
|14=>0x3b01001405080d0c0b0100220504080d0601006d0504080d0c01002c1c1104080d10006d051f080d0c01001c0504080d0c0f014d3e0504080d2b013e460504080d0c012c1104080d3d01000528080d0c0b01000504080d0c5b010022050e04080d0c139604080d0c013900050e401f080d0c002c0504080d7801000504080d0c
|15=>0x4080d0c9d01460504080d780100110904080d0c13600504080d0c0b0112150504080d0c13001c7c0504080d0c01460504080d3b13011a0904080d0c1311090408070c01119b04080d0c01004505080d0c0b01009a0504080d0c1300450504080d0c0100059804080d0c1301050408970d0c13140904080d0c0112461104080d
|16=>0x16010005040d0c730100090487080d0c0100051f080d0c016411094a080d0c0100140504080d470100110904080d570c220504080d0c4301450504080c1601003a0504080d0c01004d0504080d0f01000504080d4401004d110904080d2b0105040d0c2e01001405080d0c5b0100052804080d0c13121c0504080d0c01000905
|17=>0x32080d0c01004d1c0504080d2b0111a00904080d0c01110504080c1601002c1104080d0f0100051f04080d47011c690504080d0c014d0504080d4801000504080d9e010011051f04300d0c0149110904080d0c0114051f080d0c01128d28080d0c01390022051f040d0c1e011c050408070c01114c04080d0c01001c0504080c
|18=>0x220504080d0c01680504080d0601001211091f04080d0c13491c0504080d0c013a0504080d0c01740504080d06010074a5220504080d0c0105a4080d0c0100110904080d0c4b132c112204080d10001105048c0d0c0100a3051f080d0c01001c054a080d0c0100a21104080d0c0100450504080d0c0112110504080da1010005
|19=>0x80d0c7e01000504080dab01000504080d1701006d0504080d440100110904080d0c2613050408aa0c010011051f0408070c01a50504080d0c01000e04080d0c3900110904080d0c8313220504080d0c01000504080d0c480f011ca00504080d0c014d110904080d0c1305a804080d0c13000504300d0c0100110904080d4701
|20=>0x6d110504080d0c01001a110504080d0c1300610504080d0cb20100110504080d2b0c13051f080d0c01b1051f04080d0c01390005040d0caf010005ae04080d0c01004d2c0504080d830100ad0504080d0c01000504080d0c5601008d04080d0c130139001411051f080d0c0100451c0504080d0c01000504080d0c4801000504
|21=>0x504080d0c01b700090504080d57100c0105b604080d0c01004e0504080d0c01005f0504080d0c130100460504080d3b01000504080d0c7eac01000504080d0c3d1301001c050e04080d0c13001a1c0504080d0c01000504080d0c01b4001c0504080d2b0c0105040d0c1e1301005f090504080d0c13010504080d0c5c130100
|22=>0xd0c01000504080d0c1801001c0504080d0c3d0100a50504080d0c810100050e04080d2b0c010504080d0c01006311051f04080d0c0112110504080dba0c000504080d2b1301598d0528080d0c01000904080d0c016e090504080d0c700145110504080d0c0100050430080d0c0100110504080db90100b80504080d0c01002c
|23=>0x80d0c010005be04080d0c0139001d0904080d0c1301110504080d57100c00bd0504080d0c0100110504080d0c010091050408070c010054090504080d0c01006f090504080d0c0100bcbb0504080d0c0100220504080d0c01740504080d0c7b01005f1c0504080d0c0100610504080d0c01000504250d0c26010022051f0408
|24=>0x80d0cc301001c11050e04080d0c003a110504080d0c0100bc110504080d0c01006c0504080d0c01001105040d0c1e0100052804080d0c013900c10504080d2b0100c00504080d0c010005bf080d0c01000504080d0c13017200110504080d0c7000090504080d0c1301594d220504080d0c01001104080d0c3b01001c110504
|25=>0xc1301821a05044f0d0c01000504080d0c01cb008d05c9080d0c010005040d0c271301000504080d0c3b1301110504080d0c135900050488080d0c01004d0504080d2b0100090504080d0cc801001c110504080d100c000504080d0cc7002c1104080d1000c60504080d0c010005c504080d0c0100110504080d0c3d01000504
|26=>0x1000905045d080d0c130111220904080d0c0100090504080d0c0b0100110504ce080d0c01005a0504080d0c130100a30504080d0c1301000504080d0c7701000504080d0c780100460504080d1001000504080dcd0c01001c0504080d0c015900051f080d0c0160003e2c0504080d0c0100090504080d0ccc0100090504080d
|27=>0xd0c01000504080d0c4101000905401f080d0c01001c0504080d0c018200490504080d0c01006d220504080d0c010014220504080d0c0100110504080d0c138200116604080d0c01000504080dd10100110504080d0cb2002c112204080d0c01000504080d0ccf01000904080d0c4b0100960504080d0c1301004c0504080d0c
|28=>0xd0c010005c504080d0cb501000904080d0c1301391d0504d20d0c01000504080d0c7f01001c05045d080d0c0100110532080d0c01002c1104080d2b0100110504250d0c01001105045d080d0c13004e4d0504080d0c0100110504080d0c4301004d0504080d8301000504080d0c48830100050487080d0c1301001109044f08
|29=>0x4080d0c012a000905044f080d0c13011c22090504080d0c01057504080d0c01001c090504080d0c01710504080d0c0a1301002c0504080d571301000528080d0c016000d40504080d0c1301000504080d0c01b700a20504080d0c0100220504080d0c01a6220504080d0c1301003104080d0c01000904080d0c0112a0050408
|30=>0x1006f0504080d0c01000504080d0c01009c0504080d0cd80100a90504080d0c1301001c04080d0c013900110504080d0c01006bd7050e04080d0c01001104080d0c1339001c220504080d0c01002c0504080d2b130122051f04080d0c010504080d0c01008611051f040d0c1e010005044f0d0cd601008d05d5080d0c010005
|31=>0x4080d2b0c1301c2051f080d0c01001104080d0c013900110504080d0c0f01000504080d470100110504080d0601001c05044f080d0c0100940504080d1001005a0504080d0c0159004d460504080d0c0100050408da0c010045090504080d0c0100110504300d0c01002c1104080d83010011d904080d0c0100540504080d0c
|32=>0x18d0528080d0c130100500504080d0c0100110904080d0c0171a5110504080d0c0100510504080d0c0100054a080d0c0100050e044f080d0c01004e0504080d0c1301000504080d0c018e000504080d0cc801003e0504080d0c01004e0504080d570c010009055e04080d0c012c0504080d571001000504080d0cdb01001c05
|33=>0x110504080d0c48010005045d080d0c0139001a0904080d0c01005f090504080d0c01ca4e1c0504080d0c01000528040d0c2713010011053204080d0c01000504080d0c0b010005df080d0c010046110904080d0c0100110504080d0c010068090504de080d0c01000504080d0c01dd00050408970d0c010011220904080d0c
|34=>0x138140504080d0c0100744e0504080d100c01000504080d1083010011b80504080d0c01004e110504080d0c01000504e00d0c0100220504080d0c1301550504080d0c010046090504080d0c13011c110504080d2b0c010504080d0c260100742c1104080d0c13000504080d0c010064110504080d0c560100110904080d0c13
|35=>0xc010011050408070c010005e604080d0c0100054a080d0c4b010014051f080d0c010061110504080d0c01001c220504080d0c011105e5080d0c01000504080de301001c0504080d0c0171090504080d0c130160140504080d0c0100120504080d0c5b0100050e4004080d0c0005040d0ce201000504080de1010005044f0d0c
|36=>0x80d2b0100051f04080d0c0112dc0904080d0c01004d3e0504080d0c0100450504080d0c01001a05040d0c4b01001c0504080d0c016000050e04080d0c0171090504080d570c01e90504080d0c0100e80504080d0c1301001c050437080d0c1300110904080d0cac0100e70504080d0c01006d0504080d0c0100461c0504080d
|37=>0x80d0c0100bc0504080d0c0100110904080d0c4b01001405080d0c2601009a0504080d0c01001c0504080d0c01000504080d0cac1301000504080d0c010091110504080d570c00050e04080d0c13000504080d0c2601009c1a1105044f0d0c010011050488080d0c01004d0504080d102b01002205044f080d0c01004d110504
|38=>0xce080d0c01004d110904080d0c010011220504080d0c01a6110904080d0c0112090504080d0ceb010011a00504080d0c0100110504080d0c7f0100050408a70d0c0100150504080d0c010011091f04080d0c0100110904080d0c1349110504080d0c010014110504080d0601000504080d0c01009f0504080d0c3d01003a0504
|39=>0x4080d0c01001c0504080d0cc801006f110504080d0c0100110504080d0c01009c0504080d100159000532080d0c01000504250d0c01001c0504080d0c4b01000504080d0c4301001122051f04080d0c01050437080d0c133900110904080d0c83010009051f04080d0c130111057504080d0c01006f1c0504080d0c01000504
|40=>0x80d0c01000504300d0c01001c0504080d0c83010011054a080d0c0100d70504080d0c0100110504080d0cc801003e110504080d0c01004d1c0504080d0c010014110904080d0c0100110504080d0cdb01001c0504080d0c01121c0504080d0c0b0100110504080d4701000504080d0c5b260100110904080d0c2601001c051f
|41=>0x53204080d0c0100110504080de10100141c0504080d0c0100110504e00d0c0100a50504080d0c01001c0504080d0c260100110504080d0c01006411052804080d0c13000504080d0c0f0100220504080d0c01008d05d3080d0c01000504080d0601000504080d0cec0100110504080d0c0b01001105df080d0c010049220504
|42=>0xe40504080d0c7001000504080d57100c01001d0504080d0c1301002c0504080d1001008d0540080d0c0100090504080d0cac01000504080dba0c010014110504080d0c0100090504080d0c01caea0504080d0c01000504080d0c01006e1c0504080d0c1301000504080d0ced01001c110504080d0c0171110504080d0c5b0100
|43=>0xc130139000504f0080d0c01000504080d0c0100740504080d0c0160000504080d0c130182000504080d0cb20100050437080d0c130009051f04080d0c0100460504080d0c01000504ef080d0c01000504080d0c130159001c110504080d0c01000504080d0cee01001a110504080d0c010005e5080d0c01000504080d0c0100
|44=>0xb5010011220504080d0c01000504080d0c8101000504d3080d0c0100110504080d0c010071090504080d0c130100110504080d0c0100b305044f080d0c1301000504080d0c0100d009054004080d0c0100054004080d0c0100991d05044f0d0c01004d2c0504080d0c010005045d080d0c1301000504080d0c0100120504080d
|45=>0x52804080d0c01001d0504370d0c01000504080d0c1301710504080d0c83010005401f080d0c010005b004080d0c01004d0504080d0c01005f090504080d0c01000504080d0c0100f10504080d102b01001105044f080d0c0100c20504080d0c01000504080d0c4b0100090504080d2b0c012c0504080d0c1301000504080d0c
|46=>0x504080d0c0100a60504080d0cd6010005d504080d0c0100050e04080d0c0100110504080d0c01001205040d0c1e0100110504080d0c0100741c0504080d0c01001a0504080d0c01000504080db90100090504080d0c13010504080d0c3b0100140504080d0c01002c1104080d0c01000504080d0c260100110904080d0c0100
|47=>0x504080d2b0c01000504080d0c0100a6050437080d0c01000504080d0c0100ca2c0504080d0c0100110504080d0c260100110504080d0c8301000504080d0cf20100220504080d0c01004d110504080d0c010046090504080d0c010011051f04080d0c0100110504080d2b0c0100110504080d0c4b0100051f040d0c1e010011
|48=>0x504080d0c010005044f080d0c01000504080d0c0100710504080d0c0100b3110504080d0c01000504080d0c130100054004080d0c0100051f04080d0c0100
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0xcc0006
|6,0=>0xd33867dc330e19170c53860dc2f8e17570b73859dc2c0e15970a93852dc288e13d709b384bdc250e121708d3844dc218e105707f383ddc1e0e0e970713836dc1a8e0cd7063b0301c172e0b27055b8291c13ae096704830225c104e07b703a381b5c0cce05f702c38145c094e043701eb00d9c05ee0287010b8069c026e00c7
|7,0=>0x1cfb0e5e071f038781bfc0de1c6e1036881b040d6206a1034881a040ce206610328819040c6206210308818040be205e2e2e98170c0b6605a4e2ca816140aea056502aa815140a6a0525028a8141409ea04e5026a81314096a04a5024a8121408ea0465022b7111c086e0427020b8101c07ee03e701eb80f1c076e03a701cb80e1c06f1c36901ad7
|7,1=>0x2c7c161e0aff057782b7c159e0abf055782a8395220a8105388298414a20a4105188288414220a02e4fa7279413adc9c704db8269c1331c98ae4bd825ac12b6094b049d824ac1239c90d047e823b411ba08cd045f722c391420892e441821cc10c608530421820cc10460813040181fcc0fc607d303e181ecc0f46079303c181dd38ecdc75ac3a58
|7,2=>0x3c2c1df60eeb076d83b2c1d760eab074d83a2c1cf60e6b072d8392c1c760e2b070d8382c1bf60dece6ee837341b7a0dad06cf736439b020d7106b0835441a820d310690834441a020cf1067263354198a0cb5065283254190dcc7706338315c188e0c38e6148306418120bf905f482f6417920bb905d482e6b97160b7b05b582d6c16960b3ce5977
|7,3=>0x4bc425c212d1096084ac4254212910941749cc24c612530921848cc244612130901847d3a3ca11d508e2846d4234dd19708c3845e3a2d2115908a4844e42252111ae885843ec21d9d0dd0867742fc215e10a0e8488420420e2106108297410c2069d025080a840141fea0fe507ea83f141f6a0fa507ca83e1b9ef1cf6907ac83d241e720f29078d7
|7,4=>0x4f9ba7b1d3c909dc84eaba736138b09be74db426ba134d099e84cb4263a130ee9807
|8,0=>0x6064b01217f72bf295f542f8657b30bd095e4baf02576f2bae95d342e7a172b2b8d85c2c2df256e90b6b95b14ad6a16a50b4995a0c2ce616630b2a759142c6656230b098580c2be255df2ae7856fc2b5a559d0ac5955e4aace55552aa2854d42a4a15132a80953bca9ba54cb2a5d852b3a936548cea3e851aca8b6144b0a1c9509ca82a540509fa8
|8,1=>0x7144b87e5c2f0e0e9702cb7f25be90deb96f14b76a1ba32dc896dfcb6de1b60eda886cfcb65e1b1f0d8696bf435d65ad92d6396ad4b5465a912d40869c434c21a510d1f968bc343a5a0b2cfc967a433b219c90cdc866a4332e59870cbb86594b2a65944ec9b7649c322e19052c7a8638cb1a258bf2c578627c311a587d0c368617bb09a583d0c159
|8,2=>0x81e4c0d220591024880dcc04e2015300287fccbfc61fd30fe097ecbbf461f912fc087dbcbeba5f4eef9e97cb43e3a1f0d0f7e87bb43dba1ecd0f5d97aac3d325e872f3b87994bcaa1e450f1a8788cbc261e030ef987784bb9e5dbf0ed69766cbb125d790eb39755c3a8e1d370e929745bba11dcf90e739735c398e1cb70e5297254390a1c750e319
|8,3=>0x92944926648312398918c48a2643f321699074481a23fb31f588f6c479623bb11d498e644712237af1b588d64c68e6337119388c63c615e2fcf17598b64c59222b7315298a5bc50e227711329894cc482623111108883cc3fe21ed30ed9872c437261a730ca9860cc2e62164f0a998504c25e611f1087883fc41da60dd1066882ecc156209cf0459
|8,4=>0xa3a3d1ae68c7145b8a294d126688134379a174d09a283b34158a064d00e67f533f199f44cf7e67af13d079e4bcf02677113af99d34ce766729338b99c14cdea26e3336899b044d5e669d3345999ec4cd626593325798e4cc4e66171303897dc4bce25d532e2896d44b4a259332c1895cc4ac62551329f994b4ca366509327b9939c49ae24c5325a8
|8,5=>0x2a1335009a7c453c229cf34df8a6bc533a698b34bc9a5a452b22949149d7a4ac52326909147b9
|9,0=>0xb9045c622e2117088b8045be22de116e88b7045b622da116c88b5fcdade2d5f16a69b4f45a5a2d1d16859b3ec59d26cd916648b2dcd94a6c9336409b1c458be6c4d361e8b0acd8326c0915fb9af9c57ae2bc715da9ae94572a2b8335b98ad8c56a26b3f35978ac74d61deaff15778ab74d5966abb15558aa64d5122a7735338a95c548e2a3535128
|9,1=>0x17cf9be34defa2f6d17ad9bd24de6e6f2537899bc0c5de26ee117688bb045d5e6ea0f7479b9fc5cde2e60f7288
|10,0=>0xc18460a2304118188c0846022300117f88bf845fa22fc117d88
|11,0=>0x18387
|_,_=>0
def wAt:=mkWire dB 243 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x501439054009c24070401434e101004dc000801404010d124440005014701311004344911000344911000140101054146d1a00044210501404010812444000400444110501450331104414010100414050c004b04c050c404012808c14010413404010826404010500444131f08c040104004140105004740008054346d1a0004421050140401140cc4400110440415
|1=>0x513514231c044144d01004144d01004684c110844411050141401010055023040e404260500404011f08c100151004744f0508404011a00044210501420014e0cd34012c01430151100430491100014050400444110c1244400050145024010540401050040401044b414011108c14011100004150d124447d04004440022434447e0400444030d1244400040044411
|2=>0x100414050863498001104c1405110040415055d8204d0100414010100444210501420990500444135a00c15650c1380401450dc7011010947c2301054100101004043101054b0010c054304d0501414010100430250500538031c0c4144d0100470331c0c4144d0100414312b01414050c0055815114f80415080043026010540401050053403110c414054508c7011
|3=>0x3700020050500440010c01414010d12444000105450000400444112808c14010413404016f05c70210109414011c0cc3025010941401016e414011d0002015050140401040941401055d8204d01005b433220444403056b468021108404150559404010805404264508c50011104415a114008441101054041511000140501004244b05004440001054b0050c0545000
|4=>0x2c01470171100404150c004b04c050c40401227444403110081405040043049110001405047b488231100c1405017944026010c4140101004440311044204911000140505014a0230413404016f05c68011108404151400c4411010545033050044411770544027010c414017508c11d111008744c0100414010171404150c00814011c01c88011100c14050d3840401
|5=>0x5014204d01004504b110001405111f0100111044144e0400420491100014051a00044210105414010901c04010c86614020540810050100444330813814050500404011305c144d0100430260105404010500468241108404150500514031c044144d0100500270901c10054500c70110513404010b00c144d0100550230e044042605004507c0400444113e0cd3403
|6=>0x1c0c404250500430151100c442305014140101004042505004440301004041505004144e0100634014505c70110109414010e04404260500421fd2204c4403050144ce301004dc000801514331c044144d450cc70110513404012805c104d010044c4b010044400450dc144d010040401370002005770044027010c414011112c4400050145003110044411050141401
|7=>0x1c0cc44010501404260500414e101004dc000801534014d00cb0050c05431e51009804310500444af0105430011104411d11100814050400470130513404010100430150105430011c00c144d0100444110d12444000501406454b00844230501414052c130143101004040105004041508004144d2805c104d01004700711004a017041340401138d01001040553803
|8=>0x5014b0050c054b0014d00cb0050c0544401050144c111c04c144d0100470071c00c144d0100424070500404ed2c004f4031c0cc144d0100410010d124440005014447d1100c14058d1304c1104055bc171c084042505004358d2600044130501414052c00c30150c015141714004441101054303d112bc14050c00514331400444111100c14051100c14052c0044431
|9=>0x501414010100444001c04c44015f01c04018d00410151c12c44011100044210501414010100414010d124440001054167126008441301054102d1c04c144d01006580501006340304054701111744440205014a26713044140201004dc240108414011100014011104404151c04c44011104414051112c44000501444010105430052204410011100c14051100444af
|10=>0x1100c440004004441105014144e010047c231100c14051100434491100014051409014011104404157508c11d1110081405140004411050141001044b414011108c041511044304911000140505004ac05050143001111f810011100d14371c044144d0100414056d0cc88111100c14050105514231c044144d01004440001054104d01005040109408140104014104e
|11=>0x110444400050140401050141001050045003110444402a500c469905014127d4b00044230501444230501414010100430051100c14050c05421fd111fc100143054447e010541001111f410011100031a114008441104884447c0501410011100414051171c3002450dc50011104444af0105430010400430491100014050c9f52c001108c1405040042049110001405
|12=>0x10060c01110cc140501ac4102605004318d2600044130501514331c044144d0100488111100c14050100414011104c04150d9f52c001108c140504004344911000140511684500205014144e1c01c144d010044433050141401010043c01112bc14050c00445c7110041405110c41405050040401a901c160901004229d114f014050800414010c1244400010545033
|13=>0x1c0cc144d0100470070513404011100444210501412d60199414021100414050c00404011f08c100101004102505004157608134040122044440305014040111084140501b3420020100414050c00410014000010051305c100101006c0230499414020166816990400934332c014301501944b0030c054453e0501420011305c04010405410011104414051c044144d
|14=>0x501405b91d00020150513404010581406990400824070c00414012600044130501410011100014051000c04150c01430010c13804011304404010405414011d000201501714300205004500111044140508124440005014329905014100211a6c140504008b04e0100414011000430054099c14020401534012c01430150100634010405430ed0c0981401040981401
|15=>0x2208444030501411b91d00020151d13014210100405c505014300205004304e0100444030501414050c098140111744440205014144e0100404010805414010501440010c01518070c09414014b0084423050143449110001405040e404260500470210109414010571430021100c44020501488231100c14050409404250500416c901b342002082644413050144403
|16=>0x8008101504ca404022808c104d0100404010c098140105014304e01004447c0501410010c004b0050c05470230109414011100404150c01405bb1d00020150501430050c05704012c01c3015b0014126505008703311004140501c4634020405470071100414051400c44110501445c5050143002c200406360405414051f08c100104134144e0100404b20c0543001
|17=>0x5014301501d0474020805444230105414010100634030405416c540000100505004204d0100414011100c04151c04c04250500421d111008140505594304e0100580150413804011009c043105004ec050c09814012c00430150c014e4310513804010c138144d0100410010413804014d00cb0050c054dc2701084140108138140101004442105014200105b2806cd
|18=>0x80553c070800488131100c140508134144d0100410491100014050c05404150c00420991104c140505014204d01004b0050c054447e0501410014d0ccb0050c05444330501420e5051380401050040415080042502050041005050041001040140401220c44403050144403050144403050144c2305014040105a6404150400831b91d00020150501406cd080084403
|19=>0x8500815020401414051f08c10010800414de0801414114000c10052c13014310100414010800404011c00c04250500411d11100814050c00814012805c104d0100430150c134040104604104e010044e360100410155905c304e01004174d1f01c100104008440305014700305134040105384dc000801414011100004151171c14050c0080665050081401051380401
|20=>0x501430010c12444000501450331104414050513404012c00c30150c014304e01004b0012c01430150d6e47400080547011010941401081244400050143015110cc04150574444020105438110109814011c084144d0100498021104c14050e08c042605004160908138040105138144d0100468021108404260500414050513804010100430150c00410011100c1405
|21=>0x40144e370100410153709004210500414011100c0415130440401040577001011d820150105430020500446990501410021d13c142101004112d1108c1405010982001050047031051340401138d004010405470230513404014d00cb0050c054304d01004272b0100814011000430050c0552c011108c14050c004144d010041001018d810151c05c44010105444af
|22=>0xc004204b1100014051c00c144d0100748154f01c20010100430250500444010501430011104c440205014040105014301514000150104014453e050142001010040415050060c01110cc14050513804011108404150500424110100814010513404012808c104d0100410491100014051c04c144d01004104b110001405050143025050045002110441405094001401
|23=>0xc094042505004344911000140501bb815c50c008112d1108c14051104414050400446cd0501420022200444030501411c50501430020ce45000204014144d0c008040105004104e0100444111100014052600444130501424070500410055f08e340104054304b11000140508004dc000801444111100814054d00440154d0cc40150c014469b050141002112b41405
|24=>0x1108c14052b01414050c0047007051340401260084413050142001110841405111f014050400430011005430051100c1405110c414050c00410011100014050500404760805534032c01430151c044144d0100444211108c14050100404260c008140105004304d01007a8070809414012c13c143108014144d01004140504098140111b3c14050800888111100c1405
|25=>0x500444310105410021100c14050500444000105425030500410051171c14050c008447f050141001114f0140508004057e8d0041015050141001050041405050040401220c444030501450331104414054b00044230501470330513404011400c15010401445c50501430020500444230105410991104c14050196634030405445d1110081405010041026050052c02
|26=>0x1104404154b00444230501444011100014050513404010c12444000501498011104c140505004441301054144d01004144d010046801110841405260084413050155c331000430050412444000501420991104c140511004442305014447e05014100104004440305014144e08014040105004443301054040104004140104744440205014144d0100421d1110081405
|27=>0x5014304b11000140511004441105014204b11000140511a64140504008440105014500011044140501054104d0100444af0501430011112c44000501414111f01c1001140cc150104017b4050809814011c04c440105014104b1100014051100c1405081244400050141405044b444230501438210109814011c08c4401050153403110c41405110044431050141401
|28=>0x3700c200511008140504138040108138040101b3420020801404010400414010c094140108ca404020c13804011100414051005c30051108414050471430024000810050171430021000430050508404010c01430150504410050409814011000c30051104414050100814010809414011d00020150513404010809814011100414050c00898011104c1405041244400
|29=>0x105414014000410050508420050c0080401110cc14050400410050499414022c01430150409414018d00010150c0143001050142001018d810151108c14050c0041401050c404010199414021100c140501a6410021f01c10010501430020500404010501420020800404011d00820150500410050500810050805420012c0143015081340401110001405051380401
|30=>0x800430020800814050100410050400430010400820050100830151104c1405110cc14054f05c20011100c1405110c414050c09414010501410010501430011108c14051f08c10010501410020537820054000c10050109814011100014051f08c10011100814050513404010537420050ca6410020500404010c09814010540410050501430151104c1405
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x5750a6813d0000000000000000261800000001210000000008880fd41da000000000000000037400000cd000002f400000ad0000000004ca085400000000000000000001d4030a00000000144020800000000000000000000620093008a00000000000002600040000000
|7,0=>0x1ee83d0c7820ec41d0839107020dd31b4600006b20d421a4433cc0000000196832840000c8218e2000061a0c1200002f8c5d20b82000000000000b53162800005718aa4000029cc0000000146827d000009b41324255048a08d41128000042a08230fe61ed03c907720e681c0c36200000d08191030205c4
|7,1=>0x33860000cc2195300000000000192331e6630cc42185330280000bea17a32ee65d84b9216e42d845a10b3116242be656d0aba00002a680000a8194c429265150a11800027e64f0c000138426884c1096212840000000000000000000498891211e42348000000011732286441086990a320c840907f20fb3
|7,2=>0x4a08000126200004926918d21223f347a48e511b9233400008bd000022d2456489d111a22030000874d0ca21544228835104a20634084808800020113fa87ec80001f743e687bd0f619e843c887810ee99d9400007550e8a1cd4392871c800000003886704cdea1bb236e86d48d8a1ae3354869ccd1a19f4
|7,3=>0xbf517ca00005ec60001799aef45d68b9d172180000000b8116e9ada35ac8b5096912cf35986b21000000005888b0115f8abb45724ad8d5922ae40000aa900002a645448a7914d2297352680001490a8e451a2a25000028540000a05000027d44f469d9139980004de89ad133a26344be896d12c1a544
|7,4=>0x66a8cc51971b2a464c8c8918f9b1b462e8000189a31036188c24d82a3014
|8,0=>0x7de4fb0df49be727c86f84def1bdb37b06f54de91bd0279a6f28de39bc437826efc9de1bba276e6ed0dd89bae37566ea0dd29ba2373e6e70dcc9b9637266e449c71b8b37106e14dc11b8026fa6de8dbb9b7436e26db8db59b6836ca6d88db0135d36b46d5cdaa1b51369c6d2cda41b4536846cfcd9e1b393
|8,1=>0x9525298e519ca1293c726ce4c1c9539283244e47948d2914721ce421c8138fc71ece3c1c7538e471bce361c6938cc718ce301c5d38b4715ce2a1c51389c712ce241c45388470fce1e1c39386c70cce181c2d3854709ce121c21383c706ce0c1c153824703ce061c09380c700ce001bfd37f46fdcdfa1bf13
|8,2=>0xabc756ceac1d553aa65540ea69d4a3a8e7510ea09d3e3a7674e0e9b15333a6254b8e959d283a4a7488e8f9d1c3a327458e899d103a1a742ca8495063000140ce801cfd39f473dce7a1cf139dc73ace741ce629c67380e6e9cda39ae7350e689cce39967320e629cc3298072f4e5d1cb7396872c4e571cab3
|8,3=>0xc30785c70a1e113c1c7830b049e063c067800efe9dfa3bee77d0ef89dee3bd677a0ef29de23bbe7770eec9dd63ba67740ee69dca3b905714ee11dbf3b7876e4edb1db33b6076b4ed51da73b487684ecf1d9c2b327658eca15913b1c762cec41d853b0475fcebe1d793aec75cceb81d6d3ad4759ceb21d613
|8,4=>0xda27b407669eca3d8e7b10f609ebe3d767ae0f5b16b33d607ab4f5596a92d4c7a8cf501e9d3d347a5cf4a1e913d1c7a2cf441e853d065a00f3e9e7a3cee79d0f389e6e3cd679a0f329e623cbe7970f2c9e563ca67940f269e4a3c8e7910f209e3e3c7678e0f1a9e323c5e78b0f1516273c487884f0f1e1b3
|8,5=>0x3829f023dfe7bf0f7c9ef63de67bc4b771eeb3dd07b94f711edf3db87b64f6b1ed42
|9,0=>0xf0c5e10bc117802efc5df0bbd17782eec5dd0bb917702edc5db0bb517682ecc5d90bb117602ebc5d70bad17582eac5d50ba917502e9c5d30ba517482e8c5d10ba117402e7c5cf0b9d17382e6c5cd0b9917302e5c5cb0b9517282e4c5c90b9117202e3c5c70b8d17182e2c5c50b8917102e1c5c30b8517082
|9,1=>0x7b02f5c5eb0bd517a82f4c5e90bd117a02f3c5e70bcd17982f2c5e50bc917902f1c5e30bc517882
|10,0=>0xf7a3ef07dd8fba1f723ee07db8fb61f6a3ed07d98fb21
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x11040000040200000100000000384000000e0000000302000000c000000020200000061800000184000000600000001010000003c0000000e100000021800000084000000208000000810000002000000004000000003c0000000b0000000280000000800000001c000000060000000140000000400000000c0000000200000000400000000
|1=>0x84000000208200000800c0000200200000800000001cef000004210000010070000040080000100000000379c00000dc70000033bc00000ce700000303c000009e70000024040000080f000002038000008080000020180000080400000200400000800000001c04000005c700000161c000005810000014400000050100000140000000480
|2=>0x127dc000049ef00001279c000049cf00001203000004808000012018000045870000114040000448200001120000004402000010794000041cf000010608000041800000104dc0000410700001039400004086000010210000040820000101080000400600001000c00004002000010000000025030000090000000238200000861800002106
|3=>0x400080000fdc700003b71c0000c00000002c6180000a18600002771c00008dc7000020c180000810000002000000007dc700001b71c00006d9600001b61c0000618f00001861000005dc70000173bc00005ce700001701c000059e7000016794000055870000137fc00004def00001379c00004dcf00001371c00004d870000133bc00004ce7
|4=>0x182030000600040001177bc00045caf0001133bc0004480c00010400400040cef0001020180004080000010000400025c2700009609c00024caf00009209c0002100b00008400000020cef00008303c0002080400008002000020000000070218000189c7000061218000184840000486080001208600004371c0001050700004040000010086
|5=>0x61279c001841e700060279c001808e70006001180018000200041279c0010412700040279c0010000200021a61c00085def00021403c00084def00021279c000848ef00021233c00084046000210108000840000002077fc000809e70002005180008004600020010800080040000200010000800010001973bc00064cef00018303c0006080e
|6=>0xa1603c002848df000a1233c00284042000a1003c002809e7000a0239c0028014400088301c0021c48600086371c002048c70008102080020404200081003c0020400800081001c0020248000080400c00200ec700080371c00200cef0008020380020080800080200000200480000800610002000820008000200020000700080001000200002
|7=>0x101371c00404cef00101339c00404cad00101279c004048c700101209c004040e700101001c0040238000100600000401082001004078004010070010040100040100200100400000400cef0010027cc004009e30010020380040080600100201000400800001000784004001800010002180040000700100000800400000000a1637c002858cf
|8=>0x2112008008440080021033bc0084080a002102018008408000021000280084000200210000400824cef0020932bc0082080f002080024008048af0020020200080000000121633c00484def00121279c00484046001200118004410070010206180040818200101771c00405ce700101701c004059e70010142080040500f00101400800404de7
|9=>0x80833bc02020c0f0080820380202080c0080820280202080500808003802004cef00801209c0200480a0080100000200180f0080033bc0200080e00800202c02000002005000100011849e700460279c010849e700420039c010800420040000080100000000380001c00c048c700301001c00c0000700300001400a4480a00211329c0084480a
|10=>0x1061279c041049e701040079c04084ccf01021279c04084167010210110040801470102001180408000601001279c040001020100000080400000000a08202c02804cef00a0120bc0280080f00a0020380280080a00a0000380280000b00901339c02400c0d00889203802220cef00888029c02200ca700810203c02024caf00809203802021000
|11=>0x2004379c080105c702004020808008de702002371c08006de702001b71c08006186020013f1c08004de702001371c080043000200104040800410002000b614080025c7020008608080020c202000820808000ec702000379c08000dc702000171c0800008602000020808000006020000010050849e701420011805080042014000118042848cf
|12=>0xc4200108241049e708400000820604007080a1233c20204def08081231c2020400708021010820080042080200100200049e705061279c140009e704460069c110840e7044210384101849e704061039c101809e704020279c1008004004000279c100000000200622080801858202006151c08014de702005371c08012505020048618080120c4
|13=>0xc0021279d88006cc760020219d8000cfc760001331d80004c8760000331c80084cc720021321c80004ec710001a39c4000686710000271c312809e70c440010831080046
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x1e068180000000003a000000800000107804000000000020006c0002000740000090780000000000006050000006030000000000000c04098000000020200000
|7,0=>0x20005e3c00000000610808060d00802c220015496a530100d80ae06cc49a000280004010c8040400010340031058f80229000000000000083c1801800007c0200c04a748805db30558080ca44a9a4f5290100006e856008003623914001d450001645710340311000007753d000182e90000801102328001324f0062f4a0180057350207c5004438080c0002ae052f2
|7,1=>0x948000010001a01548b40400000f40402008b00402049c1de000a03d141e3b035e61000004017352952620211000100145804001c0001c001101015e008c7b8496010389c092b0f23c02000ec70482822a552c01000180081140a8e40d000100623a880c02021010c01400085400ec8b8a412570744c1a54001245d56008de50003f81006c1ac0a0900d0083002e7
|7,2=>0x8045017278f81a991580002f59ecbc9cdf
|8,0=>0x8f5b68ad0b1d650778c43298cce569a0bcf864976b56631d8c901153ba9cb331d285dc8cb896d74ae5f3eeeba69bbace74254470613f475de3e6366a260278d542124aad7aedf2ea644d19ee6c6d3130d2339ef3af168aa82d04b6140ba287a270c63ea1bf2fc6a49910ba52318a26c638e9dd216515b932eff90e9cf5616b67de112bb427506e9d23aaa11c3091956a
|8,1=>0xc89d4d74fc60132c392eb2d2ede362f2eb0161690c90508962d426d60c972564b51091191867324a09006a29755b2be458ac810a3580620d06a9f2a5a2eb2ccc607129481e2f5b2a4f18d54338c2ce96b78ddd64e2d2e2214d3e71a68be82b035db6795518d630b918094d2477c54c463b72fad261ab8e0e6f14253705687f1f4b0f72ead0c0f692d7596a76ea359962
|8,2=>0x202d331980aa5d838fc988519b76e1a35e928c6c7ae30db38b56d04b4866e4081addb93142aa6a9b4e90b0d4d50e64a863248251ca9767846705f4b36faadecde65a3e1cba33b5419b185bdb75005da742ae9a1b3ce54d3b38e34b434
|9,0=>0xcb6557b354651de4c2dad718e5b844ee6f56dd332f4b86536dad1d6b336117b49655daf53f3f196719ebe2f5371687666017a3043f295b2ee0f06bf9fd90cd269719aed0d7dcb8e8a2afbf9a933d1694cafda863a7f6b374e1aab4c9975f4bf
|10,0=>0xaf180ba35335fef46132cb5648e
|11,0=>0x35
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 34 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_245 10 roots_245 ops++addP pm 1 dom_215 9 roots_215 ops++addP pm 2 dom_183 9 roots_183 ops++addP pm 3 dom_118 7 roots_118 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_242 8 roots_242 ops++addP pm 6 dom_243 9 roots_243 ops++addP pm 7 dom_231 9 roots_231 ops++addP pm 8 dom_227 8 roots_227 ops++addP pm 9 dzo_99_4 5 roots_99 ops++addP pm 10 dom_230 8 roots_230 ops++addP pm 11 dom_246 9 roots_246 ops++addP pm 12 dom_87 5 roots_87 ops++addP pm 13 dom_99 5 roots_99 ops++addP pm 14 dom_119 8 roots_119 ops++addP pm 15 dom_199 6 roots_199 ops++addP pm 16 dom_167 6 roots_167 ops++addP pm 17 dom_214 6 roots_214 ops++addP pm 18 dom_86 4 roots_86 ops++addP pm 19 dzo_115_4 6 roots_115 ops++addP pm 20 dzo_243_4 7 roots_243 ops++addP pm 21 dom_151 5 roots_151 ops++addP pm 22 dom_55 5 roots_55 ops++addP pm 23 dom_54 4 roots_54 ops++addP pm 24 dom_179 6 roots_179 ops++addP pm 25 dom_182 6 roots_182 ops++addP pm 26 dom_115 6 roots_115 ops++addP pm 27 dzo_231_16 7 roots_231 ops++addP pm 28 dom_211 6 roots_211 ops++addP pm 29 dom_147 4 roots_147 ops++addP pm 30 dzo_230_16 6 roots_230 ops++addP pm 31 dzo_227_4 6 roots_227 ops++addP pm 32 dzo_227_16 6 roots_227 ops++addP pm 33 dom_195 5 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_99_4_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_115_4_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_243_4_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_231_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_230_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_227_4_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_227_16_224 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_245 10 s (0,roots_245.map (·&&&dom_245)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 60 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 60 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 272 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 338 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 82 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 338 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 85 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_247 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_247 roots_247 goal_247 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_247
theorem lowS_247:Lower true dom_247 roots_247 goal_247 12:=S_247.noCircuit
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,18),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,96),(64,192),(80,81),(80,82),(80,88),(80,112),(80,208),(128,130),(128,136),(128,160),(128,192),(129,131),(129,137),(129,145),(129,161),(129,193),(144,145),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x3ecf2
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1f4688fac688
|_=>0
def sO:Nat→Nat→Nat
|10,0=>8
|11,0=>0x87
|_,_=>0
def wAt:=mkWire dB 8 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81
|_=>0
def oO:Nat→Nat→Nat
|10,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 5
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|10,0=>1
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 9 roots_243 ops++addP pm 4 dom_123 9 roots_123 ops++addP pm 5 dom_235 10 roots_235 ops++addP pm 6 dom_219 10 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_219 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z10 i (Nat.zero_le i) hi
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_251 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_251 roots_251 goal_251 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_251
theorem lowS_251:Lower true dom_251 roots_251 goal_251 12:=S_251.noCircuit
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,28),(12,44),(12,76),(12,140),(16,17),(16,20),(24,25),(24,28),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(36,37),(36,44),(36,52),(36,100),(36,164),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,72),(64,96),(64,192),(68,69),(68,76),(68,84),(68,100),(68,196),(80,81),(80,84),(80,88),(80,112),(80,208),(128,132),(128,136),(128,160),(128,192),(129,133),(129,137),(129,145),(129,161),(129,193),(144,145),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333333300000000333333330000000033333333000000003333333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003300330033003300330033003300330033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2222222222222222222222222222222222222222222222222222222222222222cccccccccccccccc0000000000000000cccccccccccccccc0000000000000003333333333333333333333333333333300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0xfc0
|_=>0
def pmB:Nat→Nat→Nat
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_189 10 roots_189 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_245 10 roots_245 ops++addP pm 4 dom_237 10 roots_237 ops++addP pm 5 dom_221 10 roots_221 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_221 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_253 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_253 roots_253 goal_253 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_253
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=S_253.noCircuit
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050405050504050500000
def gsh_122_4:=0x5050505050505040505050405050000
theorem lowS_zo_122_4_106:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050000050500000505000005050000,0,16)] (by decide +kernel) lowS_106)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005554000055550000555400005554000054540000
def gsh_238_16:=0x555500005555000055550000555400005555000055540000555400005454
theorem lowS_zo_238_16_232:Lower true dzo_238_16 roots_238 gzo_238_16 9:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x505000005050000050500000505000005050000050500000505000005050,0,4)] (by decide +kernel) lowS_232)
def dzo_114_4:=0x500050005000500050005000500050
def gzo_114_4:=0x500050005000400050004000500000
def gsh_114_4:=0x50005000500040005000400050000
theorem lowS_zo_114_4_98:Lower true dzo_114_4 roots_114 gzo_114_4 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_4) [(dom_114,4)] (by decide +kernel) (lower_slice_b (T:=gsh_114_4) [(0x50000000500000005000000050000,0,16)] (by decide +kernel) lowS_98)
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,66),(2,130),(4,20),(4,132),(6,22),(6,38),(6,70),(6,134),(8,40),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(12,28),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(24,26),(24,28),(24,56),(24,88),(24,152),(32,34),(32,40),(32,96),(32,160),(36,38),(36,44),(36,52),(36,100),(36,164),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,72),(64,96),(64,192),(68,70),(68,76),(68,84),(68,100),(68,196),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,160),(128,192),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|4=>2
|5=>18
|6=>59
|7=>195
|8=>187
|9=>46
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x39b630bcf1
|5,0=>0xda706bfc56bb2d2b951cb11e0a4cd1758174fa8d4c1f526c7f201110f24c0e2d00c79f0acce09d4d091f508aab
|6,0=>0xfda7eed29fd74e2c4345c3d79bcfc4b99ceb7578b6f66b25e2ac696955e59543893e5b9147990b6f8620b850927ec817ea187c51c74ebb73dc0738736a93561f3c5d4ea5a9885875657a3f56933564fe554f2521c0508c44e6aa46d9d404aa3fd0d3c6ee3510e347183308931a522bc832ac4e299b828e9823c011c7ad174211619413596132c71220e0e9150a14b09fb1065ca
|7,0=>0x715fe70bb26f3596e17f6d9d46a50d6a00f661cf64b696382d6339060d595f5c25f4ba5f14b5e4c45dfc65d6125cba35c8a45b63e5b01d5a9375a56b59786589e4585e2579ae577f555a9b5570954c9a5495252b315122e503bf4fa374f9f84d5664cef04ce214c7064b4d94a2da495334899b471bc4632d439ee437e6435b442f334260d3f6913e7623dce63dc953d4ea3c3613bc8e3bb5139a083947a388ef3837f3756b365c435da83526133aba33026323eb31f002f4cd2c6f62b35d290c525b56249b3249a42446823c5b2336e227122244d2052c1ffcb1e9601e26a1dfc01def11d07c1c9371c0951be5b1b8b91b5951a46619df019a2517f5017f3f16bb713e7f135171348612a491170d10d85104b41044f101660e23e0e1aa0cd940c9710c8d80c7bf0b6670a9220a51a0926809085049020395b01f6201c5501b5f
|7,1=>0xfa30cf9ba2f60b2f5a2bf08caedad6e99e2e39d3e3214e23f8e1da0e0542d7dc2d4ae2d1a78cdb72caec5c7b8fc45b0c14a6bfeaabdf8fbc290ba34fb9822b701cb1bdcb1351b0641ac57aaa857a9dcfa6900a4700a45f8a42559e8479df809ca4f9add399c65990a197e74979f3976a596ed8947d291c8b8f9a48e9ae8e6aa89c708426782661816f27fd307d4d57adc4798e5795ae78c247853e7713476f077641674a5a72467
|8,0=>0x819b780ef7805747fdf57dd8c7ca207b6d2799a978e207659a7641674f63747e272a7671f6f6f7fd6e57a6cada6b9bd6aed26ad6866b40665fa653d96523d64503643ce62e0062c246270e6253160eff5eb985e69a5b1cb5aaf75a90058e465857f583855831f579d1577f55663e55c9555a7955969545ea52cf65284b5282351d8d51d004da174cef04c28a4b1d44723c44906440c242b8041c01419ce402c7402413e0903dbbe3c7be3a3bd386803741836c98363db34d53342b73401933ee430a15300a42f6202f23a2e6ae2e1b02a19828e882870c27e8e274e72730b26e4623d3e1d7501d52d1d2771ca061c36b1bec41b62a195f118d1f18af313bd812b9011fad114e20fd080e4eb0e23e0e1c20df230d6d40c54b0c5330ac080a80e09537089e40856907a1f06b7e067ae0544b048d90344402fdb02f78019ab017bb
|8,1=>0xfeba5fdde5f899ef8222f695cf34fef03a7edb31ed266ecd8dea0b6defa3dc38dd926fd7554d6694d5899d43efd2f5ad2a8ecf478ce6bbcd831c7e5bc2473c2166c17e8c1289bbb8bb9bccb96cbb8ecab8182b6ebeb5a3bb4347b13e1b0a5eabea3a823ca6900a4ccca43e7a22b19dfd29c1bd9b3bc95ed0949a592d2a91f89910cb8e9d88da448b6a188a69878fb82d3582d0d
|9,0=>0xf79e2c74f8c1ebcb6f26a5c9aa252892a01919d28d8f47b6be7aa7c748586fafb6c32e6971865b5d60eff5b1cb54eb6500544c92e49db738d90389b33271b325a53154730a152f8c82ddff2d67c2ace1275262571c205401fb6a13a97138e81302711bb80f44b0ed650886a084c90551502814
|10,0=>0xbddde8a4256f64d62c055e2e946dd4420a22224d
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x88888888888888888888888888888888888888888888888888888888888888895555555555555555555555555555555555555555555555555555555400000002aaaaaaaaaaaaaaaaaa22aa22aa22aa22aaaaaaaaaaaaaaaaaa22aa2222222225555555555555555555555555555555555445544554455445544554444444444aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000001414141414141414141414141414141414141414141414141414141414141414002a802a802a802a802a802a80000000002a802a802a802a802a802a800000005555555555555555554455445544554455555555444444445544554444444444aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa015555555400000001555555540000000155555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000005555555555555555555555550000000055555555555555555555555500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa00015555555555555555555155515551555155555555515151515551555151515152aaaaaaaaaaaaaaaaaa22aa22aa22aa22aaaaaaaaaa22aa22aa22aa22aa22aa25555555555555555555555555555555500000000000000000000000000000000
|0,1=>0xaaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8a8a8a8a8a8a8a8a95555555555555555555555551111111111111111111111111111111111111112aaaaaaaaaaaaaaaaaaaaaaaaaa22aa22aa22aa22aa22aa22aa22aa22aa22aa2555555555555555555555555545454545454545454545454545454545454545400220022002200220022002200220022002200220022002200220022000000015555555555555555555555555401540155555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000005555555555445544555555555544554455555555554455445544554455445544aaaaaaaaaa88aa88aaaaaaaaaa88aa88aaaaaaaaaa88aa888888888888888889555155515551555155515551555155515551555155515551555155515151515000000002aaaaaaa800000002aaaaaaa800000002aaaaaaa80000000222222225555555555445544555555555544554455555555554455445555555544444444aaaaaaaaaaaaaaaaaa88aa88aa88aa88888888888888888888888888888888880154015401540154015401540154015401540154015401540154015400000002aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa22aa2222222225500550055005500550055005500550055005500550055005500550000000000
|0,2=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aa88888888895555555555555555555555555555555554015401540154015401540154015402aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a80000000000000000000000000000000000000000055555555555555555555555500000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000001555555555555555555555555555555540000000000000000000000000000000002a802a802a802a802a802a802a802a800000005555555555555555555555550000000000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaa00aa000154015401540154015401540154015401540154000000000154015400000002aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a802aaaaaaaaa802a8000000000000000000000000000000000005500550055005500550055000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa00000000000000015555555400000001555555540000000155555554000000000000000002a802a802a802a802a802a802a802a802a802a802a802a80000000000000000011001100110011001100110000000000110011001100110011001100000000
|0,3=>0xaaaaaaaaaaaaaaaaaaaaaaaaaa00aa015555555555555555555555555511551155555555555555555555555511111112aaaaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaaaaaaaaaaaaaaaaaa802a800055005500550055005500550055005500000000000000000000000000000000aaaaaaaaaaaaaaaaaa00aa00aa00aa00000000000000000000000000000000000000000000000000015401540154015400000000000000000154015400000002aaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaaaaaaaa802a802a800000000000000000000000000000000000000055555555555555550055005500000000aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaa00000000aa00aa00000000015555555555555555540154015401540155555555555555555401540154015402aaaaaaaaaaaaaaaaaaaaaaaaa802a802a802a802a802a802a802a802a802a805500550055005500550055005500550055555555555555555555555500000000aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00000000000000000155555555555555540154015401540155555555555555555400000000000000000000000002a802a80000000002a802a80000000002a802a80000000000000000000000000550055000000000000000000000000005500555555555500000000
|0,4=>0xaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa000000000000000000000000000000000000000155555554015401555555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000002aaaaaaaaa802a805555555555505550555555555550555055555555555055505050505050505050000000000000000000000000000000000000000000000000aaaaaaaaaa00aa015555555555555554000000000000000155555555555555555555555554015402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802a802a80555555550055005555555555005500555555555500000000555555550000000000000000000000000000000000000000aaaa0000aaaa0000aaaa0000aaaa00015555555555555555555555555555555555555555555555555555555554015402aaaaaaaaaaaaaaaaaaaaaaa802a802aaaaaaaaaaaaaaaaaaaaaaaaa800000005500550055005500550055005500550055555555555555555555555555005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa00015555555554015401555555555401540155555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802a802a802a802a802a800000005500550055005500550055005500550000550055005500550055005500000000
|0,5=>0xaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa0000aaaa0000aaaa0000aaaa00000000000155555554000000015555555400000000000000000000000000000002aaaaaaa800000002aaaaaaa800000002aaaaaaaaaaaaaaa80000000000000005555000055550000555500005555555555550000555500005555000055550000aaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000000000000000000001540154015401540154015401540154015401540000000002aaaaaaa800000002a802a80000000002aaaaaaa800000002a802a80555555555555555555555555555555550000000055555555000000005500550000000000aaaaaaaa0000000000aa00aa00000000aaaaaaaa00000000000000015554000155540001555400000000000155540001555400015554000155540002a802a802a802a802a802a80000000002aaaaaaaaaaaaaaaaaaaaaaa8000000055005500550055005555555555555555550055005500550055555555550055000000000000000000aaaaaaaaaa00aa000000000000000000aaaaaaaaaa00aa000000000000000000000000015555555555555554000000015555555400000002aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaa80002aaa80000000000000000000000000000000000055555555555555555500550055005500
|0,6=>0x2aaa8000000000002aaa8000000000002aaa80002aaa80002aaa80002aaa800055550000555500005555555555555555555500005555000055550000555500000000000000000000aaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000001555400015554000155540001555400015554000000000000000000000000000000000002aaaaaaaaa802a802aaaaaaaaa802a805555555500000000555555555555555555555555000000005555555500000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa0000000000000000000000000000000000000000015555555400000001540154000000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaa802a805555555555555555555555555555000055550000555500005555000055550000
|_,_=>0
def sP:Nat→Nat
|0=>0x1e49100320c50f1215094080c68a0018196402c00e0c0cb0c16101873e5c0141c0c68a001819d381420302205000c0cb1b1600d03143c905320cc0a2e2c3032c3028b06445151600a0e063050b0c0c51324143031a305050c0c101160020310284800c0c1080e1430304042840608080
|1=>0x161018a1e25305586430322285a5320c50f1214203143c4b30010c83143c4b23218196222c01906287a416c43033a28f0508c0187143c02c460c38a1e883035e4450b001818c222828b4a3818a1e9058606b450f240150606287a9161818738782a7080c50f4c1528406287a40a8c18a
|2=>0x181880e282860674e0b0039606064450b0c0c088142c00e0c0cb111600c83143c4b20c0c50f2415d8406b9b8a1e38303143d23a08641b6143d0a558641b6143c7060628f1216383031a445005819183143c925320c50f702c203101c5000c0c88a362c00e0c0c50f522da060628792
|3=>0x143dd310094c83143d20b0c0cb111600703143dd3100641b6143d9c2062879216003030e7cb8b001819114805801c1818c222858606287c1802d28e580db0a1efc303143c90b0818196222c03e0c0c88a1601e8606287a40a1018a1e982a1541818a1e48594320c88a1600206063488a
|4=>0x8b0cc30e2878b7a641b60e287854e1818a1e9828b080c50f12985801cb0323061c50f081818a1f045bc1c0c50f242d1001cb03430e2878b8a1818a1e485807ab03030e287854a6418a1e2458088643030e2878b320c38a1e242bd7e64187143c5bf4a1a187143c5bd320c50f1214203
|5=>0x1e150a70c0c50f722c0040d0c50f242c01906d850f122c0040c0db0a1e84025320e48a1e2c3036c1c50f72016190c0c50f242e4060628792160138406d850f00f4219061c50f0a64347143c90b00fcc86061c50f1694243143c48b0011619460c38a1e10c830e287a1321818a1e48580
|6=>0xc0db2e143c21906b850f4c2d299072450f0a2dea50c0d70a1e14303143c4b200643036c2878542383035c287a616b0c86064050f16181876e28785460c38a1e880190c0c50f24905840c0c50f1215e3f081a187143c5840c8c18a1e48006062879274140190c0c50f242de04320c38a
|7=>0x1610cc30e287854a1018a1e2428088103030e287854a6418a1e4858008b0c830e287859418187143c2804a8c1ae143c5bd4a641ae143c5990c0c38a1e905990c0c88a1601ebf0c0d70a1e2d6190d1c38a1e2c706062878916f128406287c1160024806287891601e8606287921600704
|8=>0x61c50f16fc206061c50f0b18303143c90b0094703143c48b00f4c830e2878588383030e2878b1ca83030e2878b08641c96c1c50f0c0c3cc1e2c00e0818191142c03d08181ae143c2a7080c38a1e1420606d850f4800303143e08b78383035c28792161030392287a100fd299061c50f
|9=>0xa2c025080e80a1e0070606d970a1e396060628792161818a1e4920b0038347143c90b00fc706061c50f1695619061c50f161818a1e242bc1c1818a1e485807e1a187143c586062038a1602706061c50f0a2c343143c90b00f470606b850f17343030e2878516b0303143c90b0119f86
|10=>0xc0c38a1e145840c0c38a3c1422c0d1c38a1e1472c0c0c80a1e2c7060628792482d28486d850f0094303143c90b0094703143d30b009471906b850f1638303143c90b789422c06d850f00181ae6e2878b08641b65c28786460c50f24140460c0c38a1e2c0190c0db0a1e2d0868628792
|11=>0x1e485804a3818a1e485800d4438a1e2c02c0c8c187143c28e0c0c38a1e905ac0d0c38a1e1458e0c0c88a1601e8606b850f0a383030e28f0b1cb03470e2878b58191830e287840c0c38a1e902bd320e487143c5bf4a181ae143c5bd0c0c50f482c0190c0d70a1ee45a51c101b6143c034
|12=>0x242c0251c0db0a1e003030e28f054a396030e2878b4ab01b6143c00606287a60a2d0a508b0187143c2843348187143c584320e487143c28606d850f6601384320db0a1e002068e28792160070606445051600303143e08916f02030e287b3009c70606d850f0010c830e287b2081818a
|13=>0x161a38a1e485800c0c50f242c01906287894c2c0040c0da8a1e152840725b0a1e003035c287920a2d28406287921600303143e092160128e06d850f0a0278606d850f0a01506061c50f1610cc70e287854a1818a1e905800818191142c03d0d0c50f122c03f0c0e487143c586072450f
|14=>0x320c38a1e242a50d0c50f122c03d7e1a187143c586064450b00391830e287a20094c836c287854a1818a1ee45807a1818a1e242801c643036cb850fa8181b6143c5801c1818a1e485a81c1818a1e49d003348187143c5ac32181b60e2878e0c0da8a1e2de8606287c1160299906b850f
|15=>0x1e2c019061c50f16a072c0c0c38a1e2c00e6818187143c586067451e1600ca3061c50f0a887550c0c38a1e2c70686287921600223061c50f44002550c0c38a1e14303143c909160128606287c116003030e70f0b0094c8392d850f1610303143c93a0114303143c48b00181b5143c284
|16=>0xc0d70a1e2c027080c38a1e2c0464a18187143c5808a18187143d90b0010ca3061c50f014c3430e2878b001a387143c5a20010cc30e2878b00f43036cb850f1600706460c38a1e022040c0c38a1e2c0045864187143c5801c1a187143c5807a18187143c2800c0c38a1e2eb800d5838a
|17=>0x4a6418a1e9858032181b60e287850c0c38a1f605803218187143c28b4264303202878b00103036cb850f00fc206061c50f16003030e2878b44f0706460c38a1e140270c0db0a1e2c00e0d0c38a1e145809e18187143c5a10064303143c90b00643030e2878b42fc3036c1c50f1601e84
|18=>0x1e1400606d838a1ee85800818187147858008b03470e2878b0094303143c48b0018187143c90b0018187b63c58058643030e2878b1c10303202878b0118206061c50f1600303b42878b00f4303921c50f1600303143c48b00f07040c0d707143c5c50c0c38a1e2c00e081818a1e48580
|19=>0xe287850038206061c50f16f1e8606b850f1600c860725b07143c5a70c0c38a1e145990c8c187143c2840c0c38a1ec80440c0c38a1e2c0190d0c38a1e145840c0c38a1e905800c0c38a1e4828b001035c0e2878b00382068e1c50f16007040c0c38a1e2c0040c8c187143c004320c38a
|20=>0x4a116030e2878b00103600e2878b0010187143d30b0038c8606d838a1e0070606b838a1e2c70606287921600706072438a1e2c0040d7c38a1e2c006061c50f0b74586470c38a1e2c03f0c0c38a1e2c0460c0e487143c5804a1818a1e9858008181ae0e28785a664187143c58008181c9
|21=>0x143c5805818187143c58008b03030e287854a1a1b6143c5801c181ae0e287851694704061c50f16002068e1c50f0a0070606287920a2c00e0c0c80a1e2c0460c0c38a1e2c0190c0db2e143c5ac0c0c38a1e2d5990c0c38a1f885804a12187143c580c218187143c5804a181d0143c580
|22=>0x1600323061c50f0a00206861c50f122c0530c0d70a1e2c00e5818187143c5ac0c0c38a1e145800c0c38a1ee85800c0c38a1e905800d7038a1e2c00e0d1c38a1e2c00e0c0c80a1e145808c18187143c28b018c3030e2878b00103030e2878578383030e2878b00181871478580581a387
|23=>0x143e08b01942030e2878b0064303921c50f0a2d284061c50f0a00264061c50f1600706061c50f0a2de2732181b6143c5800c0c38a1e2d980081818a1e485803218187143d90b08181b5143c580a818187143c5801cb03030e2878516383470e287851600706061c50f16f12840628789
|24=>0x4c2c006861c50f122c0190d1c38a1e14584320c38a1e16786061c50f0a2c0040c0c38a1e242807a943430e2878b00181b60e287a200191835c1c50f16103660e2878b00947030e2878b013c3030e2878b00956030e2878b001b007143c5804a181b6143c2800818190143c5800818187
|25=>0x10c830e287a6160128406d850f00f5286061c50f0a003035c287851684706061c50f4c2c025320d70a1e2c303202878b0018187143e08b00f4206861c50f1601ea50c0c50f122c006062879216003036a2878b012c3030e2878b009430392d850f1600706061c50f122c0270c0c50f
|26=>0x1c10323061c50f0119e86061c50f16007040d0c38a1e2c03d0818187143c280081ab07143c5801c18187143c90b0011606861c50f1600706061c50f16a1ea5320c38a1e2c006061c50f121403d7e18187143c5800818187143c2a84e942030e2878b001b307143c58009543030e2878b
|27=>0xd0c38a1e2c0461c18187143c5800818187143c90b00103030f6c78b0010303b42878b00f4303143c48b0094719061c50f16003030e287c1122c0040c0c50f122c03c8a103030e2878b01543030e2878b00f4706061c50f1601e86861c50f1601eac0c0c38a1e2c0445818187143c580
|28=>0x11606061c50f1602406061c50f1600c868e1c50f1600303a01c50f1600206061c50f16015990c0c38a1e2f3840c0db07143c0250d0c38a1e2c0040c0d707143c5800c0c38a1e9858032181ae0e2878b32191830e2878b00f4206061c50f16003030e2878b4401e8606d838a1e2c02c
|29=>0xe2878b00383030e2878b00b03030e2878b00103030e287850018187143c5805618187143c28b4201299061c50f1603206061c50f1601e86061c50f1600206061c50f1601e06d01c50f16013990c0c38a1e2c00e0818187143c5803218187143c5bc081a187143c5803218187143c28b
|30=>0x16003030e287891600206061c50f122c006061c50f16014250c0db0a1e2c006072438a1e2c006d21c50f1600c86061c50f0a2c206061c50f16014040d1c38a1e2c006be1c50f1601286061c50f0a2c0250c0d70a1e2c0060725b07143c5801c18187143c28b001a187143c28b014c303
|31=>0x18187143c5800d1c38a1e2c0040c0c38a1e2c0250c0c38a1e2c006061c50f1601e06861c50f16003030e2878b019c3035c1c50f1600c86061c50f
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x550005
|5,0=>0x6f60696063605d60576052504c60466040603a6034602e60286022601c60166010600a6
|6,0=>0x20271fb71f471ee61e771e161da71d371cc71c571be71b771b071a971a2719b7194718d7186717f71796173616c7165715e71586151714b6144713d7136712f71287121711a7114610d710670ff70f870f170ea70e370dc70d570ce70c860c170ba70b370ac70a5709e70977091608a7083707c70757
|7,0=>0x3f873f083e883e083d883d083c973c183b983b273aa83a2839a8392838a8382837a8372836a8362835b7353834b8343833c7335732d8325831d8315830d830582fd82f582ed82e582dd82d672ce82c682be82b772af82a7829f8297828f828872808278827082688260825882508248824082388230822882208219721182098
|7,1=>0x5e585dd85d585ce75c775c075b885b175a985a1859985918589858185798572756a8562855a8553754b8543853b8533852b8524751d7515850d850584fd84f674ef74e784df84d784cf84c784c074b884b174aa74a2849b7493848b8483847b8473846b8463845c7454844c8444843d7435842d8426741e8417740f840783ff8
|7,2=>0x7ce87c687be87b687ae87a6879f7797878f878787816779877187698763675b8754774c8744873c8734872c8724871d7715870e770686ff76f876f176e986e276da86d286ca86c286ba86b286ab76a4769c8695768d8685867d86767670666886617659865186498641863a7632862a8622861a8613760b860475fc85f485ed7
|7,3=>0x7e587de77d68
|8,0=>0x9fb99f299ea89e199d989d189c989c189b989b099a7999f8996998d9985897d8974996c8963995b8953894c7944893b9932992b7922991a89119909890098f888f088e888df98d788cf88c698be88b598ad88a4989b9893888b8882987998718868985f9857884f8847883f8836982e8825981c9814880c880487fd77f677ed9
|8,1=>0xc0c8c048bfb9bf38bea9be28bda8bd19bc89bc08bb88bb08ba88ba08b979b8e9b868b7e8b768b6d9b658b5d8b549b4c8b448b3d7b358b2c9b239b1b8b138b0b8b047afc8af48aec8ae48adb9ad29aca8ac19ab98ab18aa98aa18a989a908a888a808a779a6f8a678a5e9a568a4e8a459a3d8a358a2d8a258a1c9a148a0c8a048
|8,2=>0xdf98df09de79ddf8dd78dcf8dc69dbd9db49dab9da38d9a9d928d899d809d779d6e9d659d5c9d548d4b9d429d3a8d319d298d209d188d0f9d087cff9cf69cef7ce69cde8cd59cce7cc77cbf8cb69cad9ca67c9f7c978c8e9c859c7d8c758c6d8c667c5d9c549c4b9c438c3b8c338c2b8c238c1b8c147
|9,0=>0xf768f6d9f658f5d8f558f4e7f468f3d9f358f2e7f259f1d8f149f0b9f038efb8ef38eeb8ee38edb8ed29eca8ec28eba8eb19eaa7ea19e989e908e888e7f9e769e6e8e668e5e8e559e4d8e458e3d8e349e2c8e248e1b9e129e0a8e019
|10,0=>0xfb57fad8fa58f9d8f967f8e8f868f7e8
|11,0=>0xfbc7
|_,_=>0
def wAt:=mkWire dB 106 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2229203d1c1c322d24031c1f322d0e7916011ea108000c2d0a45203d1c1c16012201203d1c1c0a191601080108bb1619541f58ad08030802147916011ea108000c2d4e1f4a010e190c2d0c45222d203d1c1c0801222922011c1c322d0c010c45222d1c1c322d0c010e790c2d221922011c1c0a1916012201203d1c1c0a191601
|1=>0x8010c2d16011edd6c640c010e2d0e7914791ea108000c2d08031c1c08010c2d101d1edd6c640c0122291c1c322d0c010c01081f161916f10e0274021c1f0a190e0116196c640c010e2d0c011ea108001c1f0801222d1c1c322d0c01720316990c011edd16196c640c010e2d1cd70ea1080008011c03203d1c1c322d0c011601
|2=>0x1201081f0c161c1f0a191601080308010c2d060116190c014a2d581d1c03322d081f0c01161916017a036c190e2d7a0306014a2d4a2d242f1c1f08010c017abb4a2d0e012229203d1c1c322d0c010c010e2d4a1416010e1922011c1c322d0c012229203d1c1c08010c2d4a2d1ca308001c1f08010c45322d0c01222d203d1c1c
|3=>0xe651699321f0c011c1f080106016c190c01921f0c2d6c010e2d5c2d0c010e010e19742d6c660c010e2d1c031c1f322d0c010cb916190e010e2d081d0c011619160106031c1f322d8c031c1d322d0c010601081f1619080316660c010e160c01161916018c1f1c1d322d0803161906016c190c014e1f4a010e190c0116190e02
|4=>0x322d0c017a034a2d0e1906031c03322d0c01081f0e0208010c2d120116191c1f081d08010c2d080116190e660c2d0e1516014a2d1601081f161916f10e020e160c01322d0c011c1c1c03322d0c0116016c640c010e2d0c161c2f0a19160124031c1f322d7a03081d06011c2f1c1f08010c2d0e021c1f322d0e160c0116191601
|5=>0xc2d0c016c010e2d14cd4a1416010e19203d1c1c08010c2d16190c2d4a0116010e1908bb16190e010e021201081f0c2d322d0c010e850e1616014a2d0e1906010c01161916011601081f581d08030c2d322d0c0108030c0116191601172d4a1716010e19322f0c010e010e194a2d0c010e010e191cbb0e01322d0c01203d1c1c
|6=>0xe010e2d08031c1f08010c2d0603322d0c017a03081d08010c2d322d081f16190e021601322d0c017a03081d0c2d06011edd6c640c010e2d9e030c850a1f160106011c1f322d0c01081d08010c2d0e0196014a1716010e197a017a034a2d0e197a03081d16191c1d1c1f322d0c01080116190c014a2d16010e191ca308000801
|7=>0x16191cf30e020a1916011ea108000c2d08030c2d060308031c1c08010c2d322d06010c2d0e2d0e198c1f169d4a010e19322d0c01322d0c010e010e19322d0c010e2d0e19080316190e016c640c010e2d0c0116190e010e2d1c2f1c1f0a1916016ce96c660c01921f0c016c010e2d1c1f06010a190c2d6c030e2d0e190a191601
|8=>0xe19322d0e650c010e2d16f10c2d0e020c011c431c1c08010a19160106cd4a1416010e191c031c2f0a191601080108bb0c2d06011c030a191601203d1c1c322d0c016c1916010e010e2d08011ea108000c2d580108030c2d060308031c2f08010c2d08bb0c2d0e016c016c190c010e2d7a034a2d0e190c2d16990c010e2d0801
|9=>0x8020c2d0c2d160106030c017abb4a2d0e01203d1c1c08010c2d0e25081f0c2d06017a030cd96c010e2d1c1f0e150a19160108010c2d0e2d0e1916011ea108000c2d0e2d08030c2d0e190c0116010e19080332a308000c010e150c01161916010e2d4a1416010e190e650c011c1f08010603203d1c1c0a1916010c2d4a141601
|10=>0xc010c010e2d16010e194c2d4a014a2d322d0c010ee96c660c010e2d08001c1f080132a30c01080016190ea1080008010c2d12010c2d4a2f0c010e010e1906031c1f322d0c018a1f902d0cf10e020c2d0c010ea10800161916010c2d6c010e2d1c1f0e010a1916011c1f0e190801161912010c2d0a1916010c85160158ad0803
|11=>0xc014a2d16010e19641b16f10e0206af08020c2d0c0108001619322d0e791ea108000c2d322f160108f308010c2d0601322d0c011c2f080108f316190e0212014a2d14791ea108000c2d0c016c010e2d242f1c1f080108f10e02081f0c2d0ea1160108000c2d0c011601081f0c2d7a1f06014a2d0e19081d0c2d203d1c1c322d
|12=>0x7a03081d0c2d0a1b0e0216011c2f0a1916015c190e010e2d06010a19160142190a1f16011c1f322d0c010e1616010c017a036c190e2d081d0c2d0e010e650c2d0c01169d4a01641916f10e0216660c2d0c0106014a2f0e190a1b060316010c01161906016c190e010e2d1c2f322d0c01581d08030c2d08030c2d0c010601322d
|13=>0x161916016c660c011ea108000c2d08030c2d06037a1f4a2d0e191c1f322d0c0114a108000c2d1c03322d0c011c1c08010c2d08b90c2d0e010ea308000c2d0cd96c010e2d0e02081f0c2d08010c2d0e01902d0cf10e021c1f08010c2d321f0c010e1916010c010e2db2016c1b0e2d0e1616010c011c1c322d0c0116190e010e2d
|14=>0x16010601322f0c017a034a2d0e196c010e2d4e1f4a010e190e01161916010c014a2f0e190e15161916010e0208010c2d4a2d0e010e190c016c010e2d4a0116010e19322f16010c01161916f10e02581d08030c2d060116010c0108bb0c2d0e011c1f0a19160106ad08020c2d08010c2d060308ad08020c2d1c2f08010c2d0c01
|15=>0x6010e2d0e190e010a1916010e190801161916010c2d06031c1f0a1916011c1c322d0c011c1d322d0c010c010e010e2d080308020c2d6c670e2d0e1916190601169e4a010e196c030e2d0e190e190803161906a108000c2d0e660c2d0c01161d322d0c010e01322d0c011c1f322d0c010e150a1916010c2d06f10e020b7b0c02
|16=>0x160106030a1916010e02322d0c010e19081f16191c2f0a1916010601081f0c2d4a2f0e010e191c03322d0c011c030a1916016c660c010e2d1203081f0c2d06ad08020c2d0603322d0c011c1c0a1916011c1d0a1916010d416c030e2d16190e02160108ad08020c2d1ea108000c2d08030c2d06031c03322d0c01080316191601
|17=>0x16010e2d322f0c010e0106a308000c2d0e190a19160142190a1f160108030c2d0e1906a108000c2d0e2d16010e191c1c08010c2d1201081f0c2d16194a030e190e1516010c010c2d16010e190cad080216190e020a1916010e650c010e2d4a1416010e191c1f08010c2d16f10e020c010ea108000c2d0e8d322f0c011c030a19
|18=>0xc2d0e2d0e194a2d16010e190a1f16010e010e66322d0c010c010e010e191c1c322d0c011201081f0c2d081d0c2d06017a1f4a2d0e191c1f322d0c010ea108000c2d4a1716010e190c1d6c010e2d0801081f0c2d0e99321f0c01081f0c2d0601160106030c010c01161916010c850a1f16011601081f0c2d06014a2d0e190a1b
|19=>0x8f10c2d0e0208f30c2d0e02081d08010c2d081d0c2d0601081d08030c2d08030c2d1c2f08010c2d4a2d0e1908010c2d0601081d1619160106af08020c2d1c1f322d0c0108030c2d0601080008010c2d0c014a2d0e19081f161916017a034a2d0e1908001619160116194a010e1906a308000c2d08f30c2d0e020e660c2d0c01
|20=>0x8010c2d0e020c010c2d060116010c0108030c2d0cf10e0206030c016c030e2d08020c2d16020c0116190e2d06010e190c2d0e01321f0c010c010e01322f0c01081d0c2d0a1b16016c190e2d08030c2d0601322d0c011c1f08010c2d14a108000c2d0ea308000c2d081d081f0c2d0e19322d0c011201081f0c2d0e02081f0c2d
|21=>0x6030c2d0e190e02060116020e010c01081f0c2d081f0c2d08000c2d0e2d0e196c010e2d077b0c0216010c0108000c2d0c2d060306f10e0216010e190e010e196c010e2d0a191601060116014a2f0e19322d0c0108030c2d1619160108020c2d0a1f16010c010e190d9d16024a2d0e190c2d0e02079d1602321d0c01
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xb28000022a000006280a20000000000000000000000002a8000000a00000000000
|6,0=>0x294451189e4132a00004a280000000000048200000000000045a80001142000043208330fca1e543a287040d881a1031a86030b6a00002d080000ac8149000004f3094a0000232000000001054200800000000f101c983450000000018202b50506000012201f5038606c40000000
|7,0=>0x2ba856c8ac195622a485390a52146428484f909d9937426684c4800012d425644a489391252242847c88e9119422a844508718000216641d0000104320083f107c98f721e683bd075a0e74000038d06fa0dc31b08354c6918ce41966320c6310c33182400005f18ba416c800005a88b3216062b105498a63
|7,1=>0x454889cd11a21f4436885d109a20f441868211029a04140447fccfe19f843ea67c50f809ec43d087988f121e023b887610ea21d0439a67250e319c2437c86e900001b7336686c84d721ac235086910d0219c433086510000190431a66250c39183400005fd0be197842e885cc4b7a16c32d085988b199612
|7,2=>0x5d26b98d7212e130000b7c96da2d835aa6b45166a2c9458a8b0c95fa00005768ae495c0ab625648abcc0002ab40000a9d15292a1453a8a6514b929345206a31144228625084a0893f227a44ee69cd137a26b44ce898d12fa00004b6896492b925434a0893112512473486800011fa23b446e88d0d19122e4
|7,3=>0x17722ec2
|8,0=>0x7566ea0dd29ba2373e6e70dcc9b9637266e40dc69b8a370e6e10dc09b7e36f84de4dbb1b7336e06db4db51b6736c86d84daf1b5b36b06d54da91b4f36986d24da31b4336806cf4d9d1b3736686cc4d971b2b36506c94d911b1f363a4c68d8b9b1436226c38d859b08360a6c08d7f9afc35f26bd8d799af21
|8,1=>0x8d27198e319c6038ba7168e2b9c5438a27138e259c48388a7108e1f9c3c387270d8e199c30385a70a8e139c2438427078e0d9c18382a7048e079c0c38127018e019c0037fa6fe8dfb9bf437e26fb8df59be837ca6f8c9f01bdd37b46f5cdea1bd1379c6f2cde41bc537846efcdde1bb9376e4ed0dd89bae3
|8,2=>0x145ce8a95123a1e7430e849d063a067400e7e9cfa39ee73d0e789cef29d873a8a739ce439c27378e6d9cd839aa7348e679ccc39927318e619cc0397a72e8e5b9cb4396272b8e559ca8394a7288e4f9c9c39327258e499c90391a7228e439c84390271f8e3d9c7838ea71c8e379c6c3
|9,0=>0x2ba15722ae055b8ab6156a2ad05598ab215622ac05578aae155a2ab05558aaa15522aa05538aa6154a2a905518aa215422a8054f8a9e153a2a7054d8a9a15322a6054b8a96152a2a505498a9215222a405478a8e151a2
|10,0=>0xafa35f06bd8d7a1af235e06bb8d761
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x712000d2c0019180030a000610000c000014580020b000410000810001010002010004000007a40009080010a00021000040c000810001010002000000800000800000c0000140000240000400000600000600000800000800000
|1=>0x13960025ac004850009080011120022040041000081a00101400202000401000800000fd6001f2c003e48007ab000f16001ca800394000722000e140018a800310800620000c1000180000291800408000800000fac001e50003c0
|2=>0x401200800400fa5801beb0036d6005e8c00b008013ab0026d6004ca8009910012a30024560044280088100110000204400402400800000feb001ec2003ca800784000e6900191200308000600000beb001654002c2800584000a4b
|3=>0x7a9600ec2001d04003a0000729600e42801a1080338b00670200cc200198100320800621400c4240188000300a00601000c004015a5802b08004f96009eac01385002708004c16009828011d580230000441000852001085002100
|4=>0x4b796096dac12da5825acf04a796093f2c127b5824beb049796092dac125a5824acf04939609252c123f58247cb048ed6090fac121e582436b048696090d24120e582414b04808209000410465814a5b0284a0030b1002525804201
|5=>0xcb296192f2c325a5864a4b0c93d619272c321e584210008369610612c20805841009082002102c282050004078b080a14101400201d58403a9080556100808200800400090800100c252c180a48273cb04e59609bf2c135f5825beb
|6=>0x180200300228600008c000014d696292f2c525a58a49cb14929629232c521e58a43491047562080084088508100b101b96202d0c404e588098b1012d6202428404058805281008102004204008108010010001620000c40001065beb
|7=>0x200dd6401800801f590038b200640400c28801841003002004004006ac8008010000b200010400008725a58e4a4b1c939638232c608258c0a4b18141030262c604b58c090818111030082c601050c0208180402300800600850c0108
|8=>0x424b4b849296e92d2d925a5ac024a34969650402ca080494084b249796492d2c924a59247eb24879640ec2080900101100202000403ca880600100bcb20160040292c8050590084b
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xe00008000209000000000000000200020000000
|6,0=>0x4c0a0f410002400000000200000001000098000a1604188706e0100402021880046000280400a9100000a00001381400000140aa5000000a04058000a830104c0000
|7,0=>0x382d84a324451ba4e0a86c8a135c1d983161a9b8268b062b8e60b0e0c8b20301090045a39004000b00c248e0b438858a870d80c006e229b9f04b00390481f3e8983a151d1c58e3440bce0a1a1b80ca62e07a708ca80bc200014322c4c6281db495c4e35acc0a00028180005210340a266419c1c06001505c050303c0e1d028d84caa059340a0171801eefb02878720b
|7,1=>0x3714c056f82d4e350002d08270285d1410088d1284d3c82dfc71060140018003983457430e816d934144a20b30310308502a50525e2f9dda9070c82de407158cc9e053800044101f014a080
|8,0=>0x3525e14653499604e12b26124e9872e586de753d9da10223d1929f87a49de7027a419f0e4aa4d2b00479ccead608291485d80815189b183e92ab0399ed1061491017a8d37ab4da5c343a098492dad99b0b78070a49573c06249506c546efd4bc5e207d3a24cd83f3f3bc78ac3fa4194971792998d02c3958c926590c5a58303816a966c2f054b4830dde24c6c2252ae2
|8,1=>0x254e27a8c24dfe75818f1d09320a65f2f5889f1d62d499cc6eec1641095132aa247ab2488b19caf4f2361e2d12a49248e333e5569577249a2fa1634d6e933c355f892
|9,0=>0x2170b4aa45449349439269250a6144d76ca392b0e4aa55b4a04aa45269560435769578c3574ba4d4392a904b25d7c9d5fc31b691
|10,0=>0x49a211c934aa552e95
|11,0=>0x88
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 9 roots_190 ops++addP pm 2 dom_244 7 roots_244 ops++addP pm 3 dom_222 9 roots_222 ops++addP pm 4 dzo_122_4 6 roots_122 ops++addP pm 5 dom_214 6 roots_214 ops++addP pm 6 dom_250 10 roots_250 ops++addP pm 7 dom_230 8 roots_230 ops++addP pm 8 dom_246 9 roots_246 ops++addP pm 9 dom_118 7 roots_118 ops++addP pm 10 dom_182 6 roots_182 ops++addP pm 11 dom_126 8 roots_126 ops++addP pm 12 dom_86 4 roots_86 ops++addP pm 13 dom_54 4 roots_54 ops++addP pm 14 dzo_238_16 9 roots_238 ops++addP pm 15 dzo_114_4 5 roots_114 ops++addP pm 16 dom_124 6 roots_124 ops++addP pm 17 dom_238 9 roots_238 ops++addP pm 18 dom_94 5 roots_94 ops++addP pm 19 dom_62 5 roots_62 ops++addP pm 20 dom_158 5 roots_158 ops++addP pm 21 dom_156 4 roots_156 ops++addP pm 22 dom_122 7 roots_122 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_122_4_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_238_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_114_4_98 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_122 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 59 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 59 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 195 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 67 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 195 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 187 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 59 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 187 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 46 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
  · exact z11 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_254 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_254 roots_254 goal_254 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_254
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=S_254.noCircuit
def isoMvS_223:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_iso_b isoMvS_223 (by decide +kernel) lowS_191
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003332000033330000333200003332000032320000
def gsh_237_16:=0x333300003333000033330000333200003333000033320000333200003232
theorem lowS_zo_237_16_232:Lower true dzo_237_16 roots_237 gzo_237_16 9:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x303000003030000030300000303000003030000030300000303000003030,0,4)] (by decide +kernel) lowS_232)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000fffe0000fffe0000fefe0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000fffe0000fffe0000fefe
theorem lowS_zo_239_16_232:Lower true dzo_239_16 roots_239 gzo_239_16 10:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,0,4)] (by decide +kernel) lowS_232)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0e00000f0e00000a000
def gsh_107_4:=0xf0f00000f0e00000f0e00000a00
theorem lowS_zo_107_4_107:Lower true dzo_107_4 roots_107 gzo_107_4 8:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [] (by decide +kernel) lowS_107)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0e0f0f0a00
theorem lowS_zo_251_4_107:Lower true dzo_251_4 roots_251 gzo_251_4 10:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_107)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000a000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0e00000a00
theorem lowS_zo_235_4_107:Lower true dzo_235_4 roots_235 gzo_235_4 9:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_107)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,34),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,96),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(80,81),(80,82),(80,84),(80,88),(80,112),(80,208),(128,130),(128,132),(128,136),(128,160),(128,192),(129,131),(129,133),(129,137),(129,145),(129,161),(129,193),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|9=>12
|10=>25
|11=>16
|12=>4
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0xe8838af451932d89033d8c1ca7733d61db3357d9351032f7bd289cc21ddd
|10,0=>0xe3eb9beb0bb158aaca28aa9149cd929c1348d83484dcf7b63767cdb5c02a5a98c553b4532ea4e2a64c51a46bd44008f3ce9b394192ab0523e8f1b3c40d4c8
|11,0=>0xf2f5cecb32b41029d9fc975d277077732c85cbf947d6c433cd28a2e188461406b092f707de901f4c
|12,0=>0x9892d8fd7c792e40eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa3333333333333333333333333333333333333333333333333333333333330000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f000000000000000000000000000000000000ffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000f0f0fffff0f0fffff0f0fffff0f0f0f0f0f0fffff0f0fffff0f0fffff0f0f0f000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x398a450c208a4e629143080e629062081a9398a450c28398a41882043206291437a4e62906278409398a41882061cc520c41034e629143785c8618a450ded430c5228616a5873148a18528398a418820
|1=>0x398b850c2041cc52287408187818a450de15a0e629143080e629143b840b49cc52286f081c8398a450de06a0e629143081273148a1d020398a450ea102d273148a1840c398a450e8102d873148a18412
|2=>0x2a87d08187f98a450c2049cc52286f080e629143b040b4a0e6291430810731543e84073148a1d020430c52286f59cc52286106ce629143081a73148a18411430c52286101cc52287a081c9398a450c20
|3=>0x50de1020e629143081273148a1840e398a450c20e1cc522861025073148a1840e41cc522861030e6291437850c3148a18407818a450de101e062914308107f18a450c20398a450f2101e6629143080e6
|4=>0xe629143080fe3148a18407f98a450c20398a4
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x19a05d915244b910683890be4269076414902a800a
|10,0=>0x152b52654094e212f949a51d944e90a94028f883ba8e4a36a8d1931acbca2ca8a8a27e495a22e881a1e246ea
|11,0=>0x7a65e0975e5cda70e9ba96c65a7a67a594a62e58295ea170a59a95d9
|12,0=>0x83660497ee5f29
|13,0=>0x2168
|_,_=>0
def wAt:=mkWire dB 32 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3814993bd08149b0b13814990b13819990b23813310b13815ab4993bd0817034014193855ab49940138538533d3810815ab4993bd0815ab4993bd0815ab4990b13815834993bd08138141938508170341909d3815834990b13815ab499401385
|1=>0x3813bd081332381499401385385f1330149b3bd0813853810814993bd081e1940338570341938561909d381c8141b38540141938526541b38549b40138533d3810814994013853c233d0814993bd08141938508170341938549b3bd081b05332
|2=>0x3013050813853bd08141938540338540138541938538108109d38133d08133d08138530141b3850b2381f13301099
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x2c42842442041c41841441040c4084044004
|10,0=>0x7837537236f36c36936636336035d35a35735435134e34b34834534233f33c3393363333303
|11,0=>0x9929729529329128f28d28b28928728528328127f27d27b2
|12,0=>0x9e19d19c19b1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 12
def pmP:Nat→Nat
|0=>0xd2ffe175fec2ebf584d7cb076fbe0a5ffc0ebe58117cf022f96025f2c03bf78077cf00ef96015f2c027e58027db002ffe005f2c00b7c801479001ffe003f2c003ff8007fb000fd6001f7c003ed8007cf000f960001f00001f000000
|1=>0x4007ff4f2b7c601f2c3cbe786b5fc
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x28d29908b4434d0301
|10,0=>0x2388e25638e6ce3e239e84e81550f39f39c59a
|11,0=>0x24e12450819d59838589290e
|12,0=>0x5d21c4
|13,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 11 roots_127 ops++addP pm 2 dom_159 8 roots_159 ops++addP pm 3 dom_223 11 roots_223 ops++addP pm 4 dom_95 8 roots_95 ops++addP pm 5 dom_63 8 roots_63 ops++addP pm 6 dom_191 11 roots_191 ops++addP pm 7 dom_253 12 roots_253 ops++addP pm 8 dom_251 12 roots_251 ops++addP pm 9 dom_247 12 roots_247 ops++addP pm 10 dom_239 11 roots_239 ops++addP pm 11 dzo_237_16 9 roots_237 ops++addP pm 12 dzo_239_16 10 roots_239 ops++addP pm 13 dom_207 9 roots_207 ops++addP pm 14 dom_175 9 roots_175 ops++addP pm 15 dzo_107_4 8 roots_107 ops++addP pm 16 dom_107 8 roots_107 ops++addP pm 17 dom_75 5 roots_75 ops++addP pm 18 dom_43 5 roots_43 ops++addP pm 19 dzo_251_4 10 roots_251 ops++addP pm 20 dzo_235_4 9 roots_235 ops++addP pm 21 dom_143 5 roots_143 ops++addP pm 22 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_237_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_239_16_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_107_4_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_251_4_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_235_4_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 12 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 25 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 25 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 16 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 4 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)
theorem checked (s:Nat) (hs:s≤13):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
  · exact z11 i (Nat.zero_le i) hi
  · exact z12 i (Nat.zero_le i) hi
  · exact z13 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 7 7=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤13) (h:RunD true dom_255 gM s xsM):False:=by
  have hmin:7≤s:=by have hl:=run_len h;change 8≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_255 roots_255 goal_255 14:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_255
theorem lowS_255:Lower true dom_255 roots_255 goal_255 14:=S_255.noCircuit
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 15 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = goal_255 &&& mask256 := by
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
      exact h2.trans ((hev (pt8 r)).trans (goal_eq_f ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
  have hav_out : Avail true mask256 bank ((execN gates xs256).getD o 0) := by
    by_cases hi : o < (execN gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := lowS_255 p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [11, 5] }, { op := GateOp.or, inputs := [1, 11] }, { op := GateOp.or, inputs := [3, 14] }, { op := GateOp.and, inputs := [0, 4] }, { op := GateOp.and, inputs := [13, 8] }, { op := GateOp.and, inputs := [12, 15] }, { op := GateOp.and, inputs := [9, 10] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def b2n (b : Bool) : Nat := if b then 1 else 0
theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide
theorem b2n_testBit0 (b : Bool) : (b2n b).testBit 0 = b := by cases b <;> rfl
theorem testBit0_b2n_add (b : Bool) (m : Nat) : (b2n b + 2 * m).testBit 0 = b := by
  cases b <;> simp [b2n, Nat.testBit_zero]
theorem testBit_succ_b2n_add (b : Bool) (m k : Nat) : (b2n b + 2 * m).testBit (k + 1) = m.testBit k := by
  cases b <;> simp [b2n, Nat.testBit_succ]
  have : (1 + 2 * m) / 2 = m := by omega
  rw [this]

def natOfBits8 (x : Fin 8 → Bool) : Nat :=
  b2n (x 0) + 2 * (b2n (x 1) + 2 * (b2n (x 2) + 2 * (b2n (x 3) + 2 * (b2n (x 4) + 2 * (b2n (x 5) + 2 * (b2n (x 6) + 2 * b2n (x 7)))))))

theorem natOfBits8_lt (x : Fin 8 → Bool) : natOfBits8 x < 256 := by
  have h0 := b2n_le (x 0); have h1 := b2n_le (x 1); have h2 := b2n_le (x 2); have h3 := b2n_le (x 3)
  have h4 := b2n_le (x 4); have h5 := b2n_le (x 5); have h6 := b2n_le (x 6); have h7 := b2n_le (x 7)
  unfold natOfBits8; omega

theorem pt8_natOfBits8 (x : Fin 8 → Bool) : pt8 (natOfBits8 x) = x := by
  funext i
  fin_cases i <;> simp only [pt8, natOfBits8, testBit0_b2n_add, testBit_succ_b2n_add, b2n_testBit0] <;> rfl

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 22 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 22 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 22 false =
      ((execN witGates xs256).getD 22 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[22]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 22 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 15 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 22, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 15 := rfl
    omega
  · push Not at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_51762_aux

theorem PEqualNP.Outside.L_meta_51762 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51762_aux.main
