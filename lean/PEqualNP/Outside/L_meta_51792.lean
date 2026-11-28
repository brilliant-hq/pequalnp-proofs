import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51792_aux
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
def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefeaaaa0000fefefefeaaaa0000fefefefeaaaa0000fefefefeaaaa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaa0000ffaaffaaaaaa0000ffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeaaaa0000ffeeffeeaaaa0000ffeeffeeaaaa0000ffeeffeeaaaa0000
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffaaaaa0000fffafffaaaaa0000fffafffaaaaa0000fffafffaaaaa0000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffeaaaa0000fffefffeaaaa0000fffefffeaaaa0000fffefffeaaaa0000
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafaaaaa0000aaaa0000fffffafafffffafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefeaaaa0000aaaa0000fffffefefffffefeaaaa0000aaaa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_98 : Nat := 0x5000000050000000500000005
def goal_98 : Nat := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffeeeeeeeeeeeeeeee00000000ffffffffeeeeeeeeeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffaaaaaaaaffaaffaa00000000ffffffffaaaaaaaaffaaffaa00000000
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffccccccccffccffcc00000000ffffffffccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffeeeeeeeeffeeffee00000000ffffffffeeeeeeeeffeeffee00000000
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffcfcfcfcfffcfffc00000000fffffffffcfcfcfcfffcfffc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffefefefefffefffe00000000fffffffffefefefefffefffe00000000
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffffcccccccccccc00000000ffffffffffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffeeeeeeeeeeeeaaaa0000ffffffffffffeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f0f0f000000000fffffffffffff0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafafafafafaaaaa0000fffffffffffffafafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffffcfcfcfcfcfc00000000fffffffffffffcfcfcfcfcfc00000000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffff0000ff00ff0000000000ffffffffffff0000ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaaaaffaaffaaaaaa0000ffffffffffffaaaaffaaffaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffccccffccffcc00000000ffffffffffffccccffccffcc00000000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffeeeeffeeffeeaaaa0000ffffffffffffeeeeffeeffeeaaaa0000
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffff0f0fff0fff000000000fffffffffffff0f0fff0fff000000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffafafffafffaaaaa0000fffffffffffffafafffafffaaaaa0000
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffcfcfffcfffc00000000fffffffffffffcfcfffcfffc00000000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffefefffefffeaaaa0000fffffffffffffefefffefffeaaaa0000
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeaaaa0000aaaa0000aaaa0000aaaa0000
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccfffcfffc00000000fffcfffc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeefffefffe00000000fffefffe00000000
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xffffffffffff0000ffffffffffff0000f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xffffffffffffaaaaffffffffffffaaaafafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xffffffffffffccccffffffffffffccccfcfcfcfc00000000fcfcfcfc00000000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xffffffffffffeeeeffffffffffffeeeefefefefeaaaa0000fefefefeaaaa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffccffcc00000000ffccffcc00000000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xffffffffffffff00ffffffffffffff00fff0fff000000000fff0fff000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xffffffffffffffccffffffffffffffccfffcfffc00000000fffcfffc00000000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffffffeeffffffffffffffeefffefffeaaaa0000fffefffeaaaa0000
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffcccccccccccccccccc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xffffffffffffffffffaaffaaffaaffaafafafafafafafafa0000000000000000
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xffffffffffffffffffccffccffccffccfcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xffffffffffffffffffeeffeeffeeffeefefefefefefefefe0000000000000000
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xffffffffffffffffffffaaaaffffaaaafffffafafffffafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xffffffffffffffffffffccccffffccccfffffcfcfffffcfc0000000000000000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xffffffffffffffffffffeeeeffffeeeefffffefefffffefeaaaa0000aaaa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffccccffffcccc0000000000000000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffeeeeffffeeeeaaaa0000aaaa0000
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xffffffffffffffffffffff00ffffff00fffff0f0fffff0f00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xffffffffffffffffffffffaaffffffaafffffafafffffafaaaaa0000aaaa0000
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xffffffffffffffffffffffccffffffccfffffcfcfffffcfc0000000000000000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xffffffffffffffffffffffeeffffffeefffffefefffffefeaaaa0000aaaa0000
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffffccccccccffffffffcccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xffffffffffffffffffffffffaaaaaaaafffffffffafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xffffffffffffffffffffffffccccccccfffffffffcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xffffffffffffffffffffffffeeeeeeeefffffffffefefefefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffaaaaaaaaffaaffaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffffccffccffffffffccccccccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffeeffeeffffffffeeeeeeeeffeeffee00000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xffffffffffffffffffffffffff00ff00fffffffff0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xffffffffffffffffffffffffffaaffaafffffffffafafafafffafffa00000000
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xffffffffffffffffffffffffffccffccfffffffffcfcfcfcfffcfffc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xffffffffffffffffffffffffffeeffeefffffffffefefefefffefffe00000000
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffffffffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeffffffffffffeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xffffffffffffffffffffffffffff0000fffffffffffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xffffffffffffffffffffffffffffaaaafffffffffffffafafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xffffffffffffffffffffffffffffccccfffffffffffffcfcfcfcfcfc00000000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xffffffffffffffffffffffffffffeeeefffffffffffffefefefefefeaaaa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffaaaaffaaffaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffffccffffffffffffccccffccffcc00000000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffeeffffffffffffeeeeffeeffeeaaaa0000
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xffffffffffffffffffffffffffffff00fffffffffffff0f0fff0fff000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xffffffffffffffffffffffffffffffaafffffffffffffafafffafffaaaaa0000
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xffffffffffffffffffffffffffffffccfffffffffffffcfcfffcfffc00000000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xffffffffffffffffffffffffffffffeefffffffffffffefefffefffeaaaa0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_81
def pG:List (Nat×Nat):=[(1,17),(1,65),(16,17),(16,80),(64,65),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_81.map (·&&&dom_81)
def gM:=goal_81&&&dom_81
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xea9d9
|3,0=>0xea9d9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x30000000000000003000080008000000000008000b00030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 82 0x3ffffffffffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_81 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_81 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_81==dom_81)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_81 gM v ys):RunD true dom_81 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_81 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_81 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_81 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_81 roots_81 goal_81 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_81
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=S_81.noCircuit
def isoMvS_98:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_98:Lower true dom_98 roots_98 goal_98 4:=lower_iso_b isoMvS_98 (by decide +kernel) lowS_81
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_81
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_81
def isoMvS_208:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_81
namespace S_51
def pG:List (Nat×Nat):=[(1,17),(1,33),(2,34),(3,19),(3,35),(16,17),(18,19),(18,50),(32,33),(32,34),(48,49),(48,50)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_51.map (·&&&dom_51)
def gM:=goal_51&&&dom_51
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xc1dd9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000f0000000f0000c000c000c000ca000a000a000a
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 52 0xfffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_51 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_51 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_51==dom_51)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_51 gM v ys):RunD true dom_51 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_51 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_51 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_51 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_51 roots_51 goal_51 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_51
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=S_51.noCircuit
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xc000c00000000000c000c,64,66)] (by decide +kernel) lowS_81
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_slice_b [(0xa0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_98
namespace S_209
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(16,17),(16,80),(16,144),(64,65),(64,80),(64,192),(128,129),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_209.map (·&&&dom_209)
def gM:=goal_209&&&dom_209
def NN:Nat→Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x76c5d74ede03f89
|4,0=>0x594054087f3b7e0397dc38d5d27c4e
|5,0=>0x8b70744f2b21bc4
|6,0=>0x8b707
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc000c00000000000c000000000000000c000c00000000000c00030003000000000003000300000000000300000000000000030000400040000000000040004000000000004000400000000000000000000000000000000000000000000000300030000000000030000c000c00000000000c000c00000000000c000c00000000000800090001000000000001000100000000000100010000000000010000c000c000000000000000000000000000c000800000000000000020002000000000002000200000000000200020000000000020002c000c000000000000000000000000000c000c00000000000000030003000000000003000300000000000000000000000000000000c000000000000000c000000000000000c000000000000000c00030003000000000002000200000000000300030000000000020002c000c00000000000c000c0000000000080008000000000008000b0003000000000003000300000000000300030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x36543654c3654d3654c3165c3605365b4a36543260439654385436743210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x344bd6a5
|6,0=>0x384
|_,_=>0
def wAt:=mkWire dB 14 210 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3454d464d1544d16551546551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x624200002200
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xf976530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>1
|4,0=>0x13028
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_208 4 roots_208 ops++addP pm 1 dom_145 4 roots_145 ops++addP pm 2 dom_193 4 roots_193 ops++addP pm 3 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_209 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_208 4 s (0,roots_208.map (·&&&dom_208)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_209 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_208 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_209==dom_209)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_209 gM v ys):RunD true dom_209 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_209 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_209 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_209 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_209 roots_209 goal_209 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_209
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=S_209.noCircuit
def isoMvS_53:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_51
def isoMvS_57:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_51
def isoMvS_85:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_83
def isoMvS_105:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_83
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_83
def isoMvS_113:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_99
def isoMvS_114:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_83
def isoMvS_116:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_83
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_51
def isoMvS_180:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_180:Lower true dom_180 roots_180 goal_180 4:=lower_iso_b isoMvS_180 (by decide +kernel) lowS_51
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_83
def isoMvS_226:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 7:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_209
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 5:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_99
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xcc00cc00cc00cc,32,34)] (by decide +kernel) lowS_53
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xcc00cc0000000000cc00cc,64,66)] (by decide +kernel) lowS_85
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_slice_b [(0xa0a00000a0a00000a0a00000a0a,32,33)] (by decide +kernel) lowS_106
namespace S_115
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(3,19),(3,35),(3,67),(16,17),(16,80),(18,19),(18,50),(18,82),(32,33),(32,34),(32,96),(48,49),(48,50),(48,112),(64,65),(64,66),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_115.map (·&&&dom_115)
def gM:=goal_115&&&dom_115
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000000f000f00000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000af000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 116 0xfffffffffffffffffffffffffffff
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
addP pm 0 dom_114 5 roots_114 ops++addP pm 1 dom_113 5 roots_113 ops++addP pm 2 dom_99 5 roots_99 ops++addP pm 3 dom_83 5 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 5 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_115==dom_115)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_115 gM v ys):RunD true dom_115 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_115 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_115 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_115 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_115 roots_115 goal_115 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_115
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=S_115.noCircuit
def dzo_113_8:=0x3000300030003000300030003000300
def gzo_113_8:=0x3000300030002000300030002000000
def gsh_113_8:=0x30003000300020003000300020000
theorem lowS_zo_113_8_81:Lower true dzo_113_8 roots_113 gzo_113_8 5:=lower_iso_b (d1:=dom_113) (r1:=roots_113) (T1:=gsh_113_8) [(dom_113,8)] (by decide +kernel) (lower_slice_b (T:=gsh_113_8) [(0x30003000000000003000300000000,0,32)] (by decide +kernel) lowS_81)
namespace S_121
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(8,40),(9,25),(9,41),(9,73),(16,17),(16,80),(24,25),(24,56),(24,88),(32,33),(32,40),(32,96),(48,49),(48,56),(48,112),(64,65),(64,80),(64,96),(72,73),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_121.map (·&&&dom_121)
def gM:=goal_121&&&dom_121
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x68044
|5,0=>0x490ca
|6,0=>0xb9efe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3030000030300000303000003030000c0c0c0c0c0c0c0c080808080808080b030303000000000303030300000000c000c000c000c000c000c000c000c020202020202020202020202020202020000c0c00000c0c000008080000080b030303030303030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x99a133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 122 0x3ffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x41
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
addP pm 0 dom_113 5 roots_113 ops++addP pm 1 dom_120 4 roots_120 ops++addP pm 2 dzo_113_8 5 roots_113 ops++addP pm 3 dom_105 5 roots_105 ops++addP pm 4 dom_57 4 roots_57 ops++addP pm 5 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_121 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_113_8_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_113 5 s (0,roots_113.map (·&&&dom_113)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_121 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_121==dom_121)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_121 gM v ys):RunD true dom_121 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_121 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_121 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_121 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_121 roots_121 goal_121 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_121
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=S_121.noCircuit
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_slice_b [(0x5000500050005000500050005000500,32,40)] (by decide +kernel) lowS_114
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_slice_b [(0xc000c00000000000c000c00000000000c000c00000000000c000c,64,66)] (by decide +kernel) lowS_209
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_slice_b [(0x300030000000000030003000000000003000300000000000300030,64,68)] (by decide +kernel) lowS_209
theorem lowS_227:Lower true dom_227 roots_227 goal_227 8:=lower_slice_b [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a,32,33)] (by decide +kernel) lowS_226
def isoMvS_59:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_59:Lower true dom_59 roots_59 goal_59 5:=lower_iso_b isoMvS_59 (by decide +kernel) lowS_55
def isoMvS_61:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 5:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_55
def isoMvS_110:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_107
def isoMvS_117:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_115
def isoMvS_118:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_107
def isoMvS_124:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_122
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_87
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_107
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_115
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_121
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_122
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_107
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_122
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_122
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_122
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_107
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_213
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_107
def isoMvS_220:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_122
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 8:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_211
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 8:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_211
def isoMvS_233:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_211
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_211
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_115
def isoMvS_241:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_227
def isoMvS_242:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_211
def isoMvS_244:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_115
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_115
theorem lowS_63:Lower true dom_63 roots_63 goal_63 6:=lower_slice_b [(0xcccccccccccccccc,32,34)] (by decide +kernel) lowS_61
theorem lowS_111:Lower true dom_111 roots_111 goal_111 7:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa,32,33)] (by decide +kernel) lowS_110
def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000a000000
def gsh_83_8:=0xf000e00000000000a0000
theorem lowS_zo_83_8_83:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (lower_slice_b (T:=gsh_83_8) [] (by decide +kernel) lowS_83)
def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000a000000
def gsh_115_8:=0xf000f000f000e000f000f000a0000
theorem lowS_zo_115_8_83:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (lower_slice_b (T:=gsh_115_8) [(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_83)
namespace S_123
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,34),(2,66),(3,19),(3,35),(3,67),(8,40),(9,25),(9,41),(9,73),(10,42),(10,74),(11,27),(11,43),(11,75),(16,17),(16,80),(18,19),(18,50),(18,82),(24,25),(24,56),(24,88),(26,27),(26,58),(26,90),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,80),(64,96),(72,73),(72,74),(72,88),(72,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xfdf58
|4,0=>0xf7b74f7374f0dc9efe8dd9fb8d6883ce5d9c4894b9a24b8e4a9b5449850895602941a08aeb68a111756586b07b6831a5e3294bcbe37a5131027296b5288932591b1a14b171a70f8040f673
|5,0=>0xffb79fe38df6b8aeb68be6d70e14b6e0a87deb86da494d7213d3267ceee7cbfe1cbc1bcb8cdcb5aec8a84c86d1c5721b8de1b7651b71b1b29d7b1abbaaeeba5623a0daaa004c9f4599ecbc94eba94c569408a92a3e8fe928f20a8f02b8c52e8be408935986f6c86e69842ca801437fa1c7f7867e5e67c9887a44b68c8d6309f61e805bf3e5be6c5b70c5722f56bf553708517f24fe924db864ce994cb304768b470db432083f5573f2913bf09396ca387743806037da835f7a3532e319b7302c729af227c14263981604f148e40cca10562b02725
|6,0=>0xff0b0fc32dfbc6aeae0de0d5bdab45d658dd569bd4f72d0d42c9061c756dc64b5c5be9c4352c3f20c181ac0143bd94bbd848bcfb5baca9b9fbcb6133b3367ac67aa67ed97eaa8fb9a8fac88f3c08c8fb847d479cff714dc6d32666b9c6105b5f1ce5748b56aeb4bca949ffa47d3d475b73c00a3bfce39104389f03752c36ae03655830ad5242d4217281fafa192a317e950dfc709d3905bcd025fa
|7,0=>0xf8906e3f54c16e0b397f5f96247c68450bc3f1c732d0c1cf4b15bd40ffdf0e7a107721
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0a0a0f0f00000f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000000000000000000f0e0f0e0f0e0f0ea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a1010101010101010000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f000f000f000f000f000f000f000f00e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f00000a0a0a0a0a0a0000
|0,1=>0xf0f0f0f0f0f0f0f0a0f0a0f0a0a0a0ae0e0e0e0e0e0e0e0e0e0e0e0000000000303030000030300030003000000000000000000000000f0f0f0f0a0a0a0a1030103010101010003000300000000f0f0f0f0e0e0e0e0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f00000f0f000030303030303030302030203020202025050505050505050504050405040504000000000000f0f0f0f0f0f0f0f00000000000000000000a0f0a0f0a0a0a0af0f0f0f0f0f0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0000b0b0b0b0b0b0b0b0a0b0a0b0a0a0a0af0f0f0f0f0f0f0f000f000f00000000f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a
|0,2=>0xf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0000000000000000f0f0f0f0f0f0000e0f0e0f0e0e0e0e0e0f0e0f0e0e0e0ef0f0f0f0f0f0f0f0f000f000f000f005050505050500000505050505050000000000000000f0f0000000000000a0a00f0f0f00000f0f000f000f0000000030303030101010103030303000000003030303030303030303030303030000a0a0a0a0a0a0a0a0a0a0a0a0a0a000010101010101010101010101000000005050505050505050505050505050000f0f0f0f0a0a0a0a0000000000000000f0f0f0f000000000f0e0f0e0000000000f0f0f00000f0f000f0a0f00000a0a1010101010101010001000100000000
|0,3=>0xf0f00000f0f00000e0e00000e0ef0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e50f050f05050505000f000f000000000000a0a00000f0f00000a0a00000a0af010f010f010f010f000f000f000f00f0f0f0f00000f0f0f0f0f0f00000a0af0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e3030303030303030003000300000000a0a0a0a0f0f0f0f0a0a0a0a0a0a0a0a000000000000a0a0a0a0a0a0a0a0a0aa0f0a0f0a0a0a0a0a0f0a0f0a0a0a0a00000000f0f0f0f000000000a0a0a0af0f0f0f0f0f00000f0f0f0f00000000f0f0f0f0f0f0000000000000000000000f000f00000000000f000f000000000000f0f00000f0f00000a0a00000a0a
|0,4=>0xf000f0f0f000f0f0f000f0a0f000f0af0f0f0f00000f0f0f0f0f0f0000000000000000f0f0f0f0000000000000000b0b0b0b0b0b0b0b0b0b0b0b0a0a0a0af0f0f0f050505050f0f0f0f000000000000f0f00000f0f00000f0f00000a0a303030300000303030303030000000030303030303030303030303000000000000f0f00000f0f0000000000000000505050505050505000500050000000050505050505050500000000000000003030303030303030303030302020202b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a101010101010101010001000100010000000000f0f0f0f000000000f0f00005050505050505050505050500000000
|0,5=>0xf0f0000000000000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0000000050505050000000000000000f050f050f050f050f000f000f000f00f0f00000f0f0f0f0f0f00000f0f00005050505050505050500050005000500f000f0f0f000f0f0f000f000f000f00f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0000f0f00000f0f00000f0f00000000000000000000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe08f0c101c29d182010100304070c0448e0608a051c0c10a2038e02023070304044880e14d8c061c11a0a20c8214404070a606030428280101c0971858402141440702546030e08a051e08500184c402144040724146080e04491061c10a2038682023040b04284880e182840608080
|1=>0x101d6810a30407580448c1e0c382142470f042958c10085055430407141548c061c10a0a8c402141400c101c1055030407041538c1c2010a4c30407041528c1c2010a483040704284a3101c085223071c042828c1c0c10a12143a20214608141508c101c2a018203823c24407027c60f
|2=>0xaf460e0608085182010a0af06080eec08518e8402141460e1008510183840202246080ee4089182038522e06080e080b7184c402141590e1008536182038234146080e05a8c1a2038202304070405a0c1ccc10a0a3018704282b2101c51f0a3040a0ac580c101d781123072e0608505
|3=>0x182010a0b286080e1808518203820b246080e15c0c1c0c105903170804282c7101c10a4830407141630c101c5090a4440714148c51c3c10118203820b106080e080c318203810b086080e29a89183810a0b0460e04282c01838682141460804042bf18203be021460e1008a05182038a
|4=>0x14168089e282b0183a70214146080e08510182010112c06080e080899a203823c146080e0a60518704070404603101c101123a582141460e10080ab182178a0ac060e06085056438782142460858282b0182038a2a146083208505642038112c460f061c10118203b90a3020e10082a7
|5=>0x6232383101c10a121470804282ab18384021414650101c10a0b44603101c10a0b14407041640c101c5090ac46080e282b119147830e08505184c708042828c9c2038214146080e0850518c87030e085051839708042828c9620382141460e06085058a203822814608160850518b8402
|6=>0x101c10a0a30708040428c101dc810a30708042828c642038214146575c20382141460e106410a0a30407ac2828c101d6010a30402141580c101c50522304550e085051820c87582828c101c505a83040214242b018203d31414652101c1010a3040704284859a70407042828c101c505
|7=>0xe282b11838182141460e10085090a304075e2828c1c2010a0a3228f101c101182038214dc28c101c1010a302080e080851936c0e10085051820382141608c101c10a0b006080e29a851834407042828c101c10a0ad06080e0850519401880e0808518203af142428c101d60a1214613
|8=>0x1008505b630407042828c8e20382142428c101c10a0a322880e282b1183c407042828c1c2038214146080e085051934407b42828c101c1010a301880e08505183c407042848c1c3c10a0a30407042828c46203810ac460e1008505191c407040448c101c1590214603101c1059030419
|9=>0x80e085051820c87042828c1c2010a0a30407582828c
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x422c82d902b1ff63f2c7cd8f6b1e853c4c7718eb31d06394c7118dfa9b96366c6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5898292a6248c47988c31126218c41988030fa61e8c3b987430e261b8c35986830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b25f64b2c94d926b2476482c8ed91ab22f6452c88d90eb2176
|6,0=>0x2183c2a6846f075a0b3c106812f009dfdbbf567dcefa19f0bbdb67a8ef35de33bbf7770eec5dd5b3a4773aee59dc7bb887702ede9dba336e66ceed81dacbb527698cd199a0333a6666ecb1d93331f7632cc49d85bb0475faebd9d77bae875c2eb69d6a32cd758ceafdd5c3ab17554ea8dd4e3a957
|7,0=>0x2463c866900d1e9a39bc6c78caf17da2c3c517894f111a1f34377
|8,0=>0x4936
|_,_=>0
def wAt:=mkWire dB 92 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x101d0a32062b10310a31100b100b0a3210311c31101d111d0e321c30101d10311c33101d11150a320a320a311415060410311c1714150a311c300a31100b141502321415723314151446062b101d1415101502321e3114150a31040510321415100b1e311015102604251c33043110310a311c171e301c241e300a311c241e31
|1=>0x1415103214151c15101d10660e31061710310ac5100b1e31101510260a311c32101d1415103104250a310a31043110650e311415101d040514151c30101d1e3210151c33101d0e3105150a32043114150e260a316231100b0431581704310e260a31051d0e32100514150a3110321e331015100b0e320a3110311c17101d1c32
|2=>0xe31101d0431101e0e320a310a32100b1015101d10320415141510310a31101d10151e3010151415100b101d0e320a31141502311415062b1031100b1031101d0a31101d04250a310a32101d141510150b3510320232
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000000000000000000000000000000000000000000000000000001000000
|5,0=>0x2112011e20000001c20001b11a10000000000000001730001610000000000001510000000000001410000000000000001220001110000000000f20d20c10000000000000b10a1000091072061000000051041000000000000000031000000021
|5,1=>0x2b1000000000000000000292000272000000000000252241231221000000000
|6,0=>0x9c19a29829629429229028e28d18b28928728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25c15a25825625420005315124f24d24b24924724524324123f20003e13c23a23823713523323123012e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x57802b40158009f004e00250011a008c00420020801000048001e000e0005a002c001200080003c0019000a00040001e000e0006800300010000400018000800020000
|1=>0x40231081460bf304f9427c89fe42bf214b902fc817640af204d90224804040122008082f44176121a080d02000097e04bb0221810ec081002020080002fc017a00bb
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2000000000000000000000000000002000
|5,0=>0x400000000038004000000e8c41000000841400140151000000004c00aa0000020000001000000009c008000058308000002412a09a100015080000000280004
|6,0=>0x5e1735626f5939e6f76e92256cd407cc92066ecac9879646615ef633200ee92d3e2c6c5a4c6017630bcb1d17cf747
|7,0=>0xb61f22b6db758a2bb8a2e
|8,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 17 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_106 5 roots_106 ops++addP pm 2 dzo_83_8 5 roots_83 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_122 6 roots_122 ops++addP pm 5 dom_107 6 roots_107 ops++addP pm 6 dom_113 5 roots_113 ops++addP pm 7 dom_83 5 roots_83 ops++addP pm 8 dom_99 5 roots_99 ops++addP pm 9 dom_114 5 roots_114 ops++addP pm 10 dom_120 4 roots_120 ops++addP pm 11 dzo_113_8 5 roots_113 ops++addP pm 12 dom_51 4 roots_51 ops++addP pm 13 dom_59 5 roots_59 ops++addP pm 14 dzo_115_8 6 roots_115 ops++addP pm 15 dom_57 4 roots_57 ops++addP pm 16 dom_81 4 roots_81 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_83_8_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_113_8_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_115_8_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_123 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_123 roots_123 goal_123 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_123
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=S_123.noCircuit
theorem lowS_126:Lower true dom_126 roots_126 goal_126 7:=lower_slice_b [(0x44444444444444444444444444444444,32,34)] (by decide +kernel) lowS_124
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,64,66)] (by decide +kernel) lowS_213
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_slice_b [(0x30303030000000003030303000000000303030300000000030303030,64,68)] (by decide +kernel) lowS_217
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_slice_b [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,32,33)] (by decide +kernel) lowS_230
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_slice_b [(0x303000003030000030300000303000003030000030300000303000003030,32,36)] (by decide +kernel) lowS_233
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,80),(16,144),(18,19),(18,50),(18,82),(18,146),(32,33),(32,34),(32,96),(32,160),(48,49),(48,50),(48,112),(48,176),(64,65),(64,66),(64,80),(64,96),(64,192),(128,129),(128,130),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xfc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21
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
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_179 7 roots_179 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_241 8 roots_241 ops++addP pm 4 dom_227 8 roots_227 ops++addP pm 5 dom_211 8 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_211 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 8 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_243 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_243 roots_243 goal_243 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_243
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=S_243.noCircuit
def dzo_177_4:=0x3000300030003000000000000000000030003000300030
def gzo_177_4:=0x3000300030002000000000000000000030003000200000
def gsh_177_4:=0x300030003000200000000000000000003000300020000
theorem lowS_zo_177_4_145:Lower true dzo_177_4 roots_177 gzo_177_4 5:=lower_iso_b (d1:=dom_177) (r1:=roots_177) (T1:=gsh_177_4) [(dom_177,4)] (by decide +kernel) (lower_slice_b (T:=gsh_177_4) [(0x300030000000000000000000000000003000300000000,0,32)] (by decide +kernel) lowS_145)
def dzo_241_4:=0x30003000300030003000300030003000300030003000300030003000300030
def gzo_241_4:=0x30003000300030003000300030002000300030003000300030003000200000
def gsh_241_4:=0x3000300030003000300030003000200030003000300030003000300020000
theorem lowS_zo_241_4_145:Lower true dzo_241_4 roots_241 gzo_241_4 6:=lower_iso_b (d1:=dom_241) (r1:=roots_241) (T1:=gsh_241_4) [(dom_241,4)] (by decide +kernel) (lower_slice_b (T:=gsh_241_4) [(0x3000300000000000300030000000000030003000000000003000300000000,0,32),(0x3000300030003000000000000000000030003000300030000000000000000,0,64)] (by decide +kernel) lowS_145)
namespace S_245
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(4,36),(4,68),(5,21),(5,37),(5,69),(5,133),(16,17),(16,80),(16,144),(20,21),(20,52),(20,84),(20,148),(32,33),(32,36),(32,96),(32,160),(48,49),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,96),(64,192),(128,129),(128,144),(128,160),(128,192),(132,133),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_245.map (·&&&dom_245)
def gM:=goal_245&&&dom_245
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x5406411cc0
|6,0=>0xcaccca9996a3f6566fac6666a5baf436dff285a8
|7,0=>0x795b273d1e6176941c603abae2341814b000ff4d0ad74
|8,0=>0x79993356de2cd2a
|9,0=>0xbf1f1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc800c800c800c800c800c800c800c91001100110011001100110011001100100010001000100010001000100010c800c800c800c800c800c800c800c800c800c800c800c800c800c800c800cb3003300330033003300330033003300330033003300330022002200220022cc00cc00cc00cc00cc00cc00cc00cc00c000c000c000c000c000c000c000c00003300000033000000330000003300000033000000330000002200000022c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c33003300330033003300330033003300220022002200220022002200220022cc00cc00cc00cc00cc00cc00cc00cc0000000000000000000000000000000330033003300330000000000000000003300330033003300000000000000008800880088008800880088008800880088008800880088008800880088008b3003300000000003300330000000000330033000000000033003300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00033003300330033003300330033003300320032003200320032003200320032cc00cc00cc00cc008800880088008800cc00cc00cc00cc008800880088008b3003300330033003300330033003300330033003300330000000000000000
|0,1=>0x11001100110011001100110011001100110011001100110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4a0a6390696140639062298e41b4263906b094c720d2c298e41a4a681c83485063906f298e41a42501c834850020cae018896154639125500c720d6c280c4188263906d080e44954639165500c418820
|1=>0x41a4a63906d298e41a42531c83
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x56005
|6,0=>0x3863262b72471d71761160b6
|7,0=>0x7386d66766075975274b74563e7
|8,0=>0x8968277b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 246 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x49531529d01531d4a129d49531549d31541929d01731d31539569f49531d31529d31d31559749d31d41929d1b201501549d31d4a131539531d4953151b241929d4a129d31d315
|_=>0
def oO:Nat→Nat→Nat
|5,0=>4
|6,0=>0x5cd434890234ca31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0x1cebe5153ae8d6ceb635b080fde7ee3bf9deccf466f2bf13ac8d644901f0080004000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>3
|6,0=>0x7a44171d84
|7,0=>0x135b5548c112
|8,0=>0x20cf
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_241 8 roots_241 ops++addP pm 1 dom_181 7 roots_181 ops++addP pm 2 dom_240 5 roots_240 ops++addP pm 3 dom_213 8 roots_213 ops++addP pm 4 dom_113 5 roots_113 ops++addP pm 5 dom_229 8 roots_229 ops++addP pm 6 dom_117 7 roots_117 ops++addP pm 7 dom_180 4 roots_180 ops++addP pm 8 dzo_177_4 5 roots_177 ops++addP pm 9 dzo_241_4 6 roots_241 ops++addP pm 10 dom_244 7 roots_244 ops++addP pm 11 dom_116 5 roots_116 ops++addP pm 12 dom_53 4 roots_53 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_245 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_177_4_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_241_4_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_53 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_241 8 s (0,roots_241.map (·&&&dom_241)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_245 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_241 h
def symsG:List (List (Nat×Nat)):=[[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_245==dom_245)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_245 gM v ys):RunD true dom_245 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_245 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_245 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_245 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_245 roots_245 goal_245 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_245
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=S_245.noCircuit
namespace S_252
def pG:List (Nat×Nat):=[(4,36),(4,68),(8,40),(8,136),(12,44),(12,76),(12,140),(16,80),(16,144),(20,52),(20,84),(20,148),(24,56),(24,88),(24,152),(28,60),(28,92),(28,156),(32,36),(32,40),(32,96),(32,160),(48,52),(48,56),(48,112),(48,176),(64,68),(64,80),(64,96),(64,192),(72,76),(72,88),(72,104),(72,200),(128,136),(128,144),(128,160),(128,192),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_252.map (·&&&dom_252)
def gM:=goal_252&&&dom_252
def NN:Nat→Nat
|3=>1
|4=>6
|5=>13
|6=>9
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x7bfb3
|4,0=>0x7041d1f57a0998e074dd03e0b03582
|5,0=>0xf4decb234d61c874ba47480b83014123c781ecea1721515a83121980491b03c5f
|6,0=>0x7eb49674a0438ed2af4a1b29c154e212ffc0f87a0a134
|7,0=>0x1881501d5e
|8,0=>0xbd29c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x8888888800000000888888880000000088888888000000008888888800000004444000044440000444400004444000044440000444400004444000044440002222222222222222222222220000000022222222222222222222222200000000101010101010101010101010000000001010101010101010101010100000000888888888888888888888888888888880000000000000000000000000000000000000000000000044444444444444440000000000000000444444440000000220022002200220022002200220022002200220022002200220022002200220111111111111111100000000000000001111111111111111000000000000000088888888888800008888888888880000888888888888000000000000000000044444444444444444444444444444444444444440000000044444444000000020202020202020202020202020202020202020202020202020202020202020211111111111111111111111111111111111111111111111100000000000000008888888888880000888888888888000088888888888800008888888888880004444444444444444444444444444444444444444444444444444444400000002222222222222222220022002200220022222222222222222200220022002201111111111111111111111111111111110101010101010101010101010101010
|0,1=>0x2222222200000000222222220000000022222222000000000000000000011110000111100001111000011110000111100001111000000000000000088888888888888888888888888888888888888888888888888008800880088000440044004400440044004400440044004400440044004400440044000000000000000000000000000000000000000020202020202020202020202000000011111111111111111111111111111111010101010101010101010101000000000808080808080808080808080808000008080808080808080808080808080000044004400440044004400440044004400440044000000000044004400000002222222222222222222222220000000020202020202020202020202000000000000000000000000000000000000000011111111111111111111111100000000
|_,_=>0
def sP:Nat→Nat
|0=>0x110f75c2542c4f724a85b4ce4948f716c85b4ce4810f726a858da12ac6d4810b1bc2042dee4d10b1bd3342ccf702487b93142c4f7240883dc12ac6608103124081b42c58d49020c92a0e3304a418820
|1=>0x1ee4950b7b9252216f724085bdc92a32b699c92a1637a4085bd25461667b8b242daf724085bdc9
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x1d51851350e5095045
|5,0=>0x6966365d65765254c64664063a63462e6286226
|6,0=>0xa479d79769168a78377d67676f7
|7,0=>0xb17ab6
|8,0=>0xb86
|_,_=>0
def wAt:=mkWire dB 26 253 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x42d2ad79242d5bd43d73d2ad71242d49a7ad7a12ad42d2ad0ad4a179142d42d5bd7a173d4a16807a179142d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x72000000043000000000000880400
|6,0=>0x192b954a6512793496492
|7,0=>0x383b1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xa87f7d3f3b31201d120c0a060100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2000100000110
|6,0=>0x749653bd8
|7,0=>0xac
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_220 6 roots_220 ops++addP pm 2 dom_188 6 roots_188 ops++addP pm 3 dom_124 6 roots_124 ops++addP pm 4 dom_244 7 roots_244 ops++addP pm 5 dom_236 7 roots_236 ops++addP pm 6 dom_120 4 roots_120 ops++addP pm 7 dom_116 5 roots_116 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_252 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_116 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_252 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_252==dom_252)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_252 gM v ys):RunD true dom_252 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_252 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_252 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_252 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_252 roots_252 goal_252 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_252
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=S_252.noCircuit
def isoMvS_125:List (Nat×Nat):=[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_123
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 7:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 7:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_207:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 7:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_126
def isoMvS_219:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_iso_b isoMvS_219 (by decide +kernel) lowS_215
def isoMvS_222:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 7:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_126
def isoMvS_235:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_231
def isoMvS_238:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_237
def isoMvS_246:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_237
def isoMvS_249:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_245
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_237
theorem lowS_127:Lower true dom_127 roots_127 goal_127 10:=lower_slice_b [(0xcccccccccccccccccccccccccccccccc,32,34)] (by decide +kernel) lowS_125
theorem lowS_223:Lower true dom_223 roots_223 goal_223 10:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,64,66)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 10:=lower_slice_b [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,32,33)] (by decide +kernel) lowS_238
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,32,34)] (by decide +kernel) lowS_245
theorem lowS_253:Lower true dom_253 roots_253 goal_253 11:=lower_slice_b [(0x3030303030303030303030303030303030303030303030303030303030303030,32,36)] (by decide +kernel) lowS_249
namespace S_254
def pG:List (Nat×Nat):=[(2,34),(2,66),(2,130),(4,36),(4,68),(6,38),(6,70),(6,134),(8,40),(8,136),(10,42),(10,74),(10,138),(12,44),(12,76),(12,140),(14,46),(14,78),(14,142),(16,80),(16,144),(18,50),(18,82),(18,146),(20,52),(20,84),(20,148),(22,54),(22,86),(22,150),(24,56),(24,88),(24,152),(26,58),(26,90),(26,154),(28,60),(28,92),(28,156),(30,62),(30,94),(30,158),(32,34),(32,36),(32,40),(32,96),(32,160),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,80),(64,96),(64,192),(72,74),(72,76),(72,88),(72,104),(72,200),(128,130),(128,136),(128,144),(128,160),(128,192),(132,134),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|3=>6
|4=>48
|5=>200
|6=>282
|7=>164
|8=>38
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x82c2c7643e3678e2fe2b214851abc2
|4,0=>0xd7b4cc0726b4098b3b16a68f69a7d592a7e8f3198d6535e7b35b8b25a33f586b146dcd446783e6c83d03f3cdc0387bb341ae31c802f5d82ef072da402c94626d302366a20afd1f3ee1ef5b1d8421cb3919eb31863017c8f16e0816cc4145ed13ad2138281317811dc30f86f0be120bc530380902d8300373
|5,0=>0x36b0b35f90346f233dbc33a6033a523342d331d83213a31f6031c4031c2e2fdd02e5ee2e3c42c6982be4b2bdf02bd4c2ba9c2adfb2a2cd2a2ad293c128cc627cf32789d2730326cfb262a624f2b23dc3237a223407217ab20b45204bc1f9db1f42f1e1011db311d4301c5941c1c61bc5e1bb9f1b3de19fd519f4219abd198ef197bc190801906518c52184ea175411731c1707a16d2a15bfe14e6414a6b1426613a201387b1382813596132f7132ec12a0b125a611e691190c10c3e100e40fd7c0fce20fc380f7050edb60eb4c0e9660dde90dcaa0db970db1e0dafe0d9600c9720c4a10b8750a6590a64809e2009bb5098a409711093360923c08f2708e6508c140880806f0f068a4064ef063bf05cb705c1805502053f4047f0041be035980288e01dc401882017a4016280160401602013680135b010d7006c00015b00092
|5,1=>0xd7b4cd2daaacdbeab8a39f40d9bced999ef86f8184e8f81927801d17f64b7ee2f7df507c80e7ad1978f2f77f7e74f747266c70d84705056d6e56cec86cc246b0086836466b9a65f8761e55610d66081b5f8095dd375c20e5ac7659fc759e5b58bb2589e95670d55c8655a5d541c6525d7514dd512f64fc314f7af4b1e248c9048552478e746d8746bda45ba64513b43933430e1430dc41fd341c5240b083f48a3ec4c3ea9e3ca7f3bdbd3a4a73918037df9372a4
|6,0=>0x1fdc01f36b1f2461ea1c1e5111e25a1dff01dfc01dcca1d75b1d31d1d22f1ce881ce3e1c1381b4e91b3de1ae641acf81a4eb19f4219d5b198ef1943a1919e18c2e18aa017e1c17cd41795f1721916c291685b1610d15e751570c15659152c5144481439c13e1713a71138d6135c71344c1320512d6a12a68129c81267b1266411b10119ee119da1181f10c3e105c4100a80fce20f3830efe00ed430ea790df450d8dd0d60e0cfd30cbc20ca570c4500c0470bfe80bf880b8100b16c0a9dc0a92d0a4fd0a3ef09f1609e4d09c0509bca09b2f099c10905508d6808b5b08ab107e7b07c1106afd061a0061940599605566050d904e5b04981046d30442b04407041be03e7c03e440362003598033c00327502ee502d8002c2402b5102541024e4023fb01cd901b6601b1401a57019ab018820162801604013260114c00bcd00bb9
|6,1=>0x6f6416f4b36ea516df976cd816b25466f5965a796434b621b96209f60e7460d136058b5fc5f5f4e15eb985e80b5e4c95c5615be375b52558bb257fde5736e5694f55e52546c3536945360b51d9c512344fa0b4f6384ed654e25c4cb214c9ff4c7334c3404b1e249d244934748aa347ea346f5d45f4a442a743af0426334224a4113840f7940daa402273dbe73ceec3c8973bf723bb2e3bb0e387f73854f383d93697535978358aa356e9352fd35260351ca3514234c19346a63408133fec33f7433370328563239132284320b731c8131abc31346312952f8442f6c92f40e2f3432f2302e34d2dd1c2d2bc2d1202ce812cd3c2c9d42c4202b85b2ae602a3b52a2cd29df9296582903c28d9c2870c2867c2803827d5e275c126fbb26cfb262a62535f2527724ce724a24241b223ec022dda2269021cbb2176f2150c2085d2012b
|6,2=>0xc7735be2d3bca43bb6d6a39e2a34e99f40d9bced984b697f5f95ef4949a5941db8fcac8c2d78796f878a9833788254f8147f79f3a7857c75a9d758ef744c0720ed
|7,0=>0x49f1449ad9473214710d44d46442a743af042eed4263341c804189e40f7940b183cf073afa639fce383d93795037143356e9349d13450a334b3322b131deb3021f2cb822b5a62b27e2afc828d9c289092878e2870c281c827e8e2704726aa524869245712307b22c69221be2210121f8621cf421b7920e8d207eb1fdc01fd171f7cb1f36b1f1331f0531ef4f1e62d1dd3e1dcca1d8251d31d1ca721c56d1c1381bedf19edb19d0f1943a194051787f16174150e61439c13f2913dbd12e2012dc311b1f112611125510d9910a24105040f4fe0f3830e33f0e23e0dd330d8b90d1bf0d0d60c7a30c4500c1670b9390b3550b16c0aee60ae270ab3c0aab30a80e09fe409fdd09f150979509581086a50844807e08070b106b7e066d30645b05d52055f505515043fd039f20365c0327502f1201d4e01b5e019ab014c401326002b0
|7,1=>0xa34e9a2d579da0a9b8de99d499937f975f7949a5934568cec38b63a867d5833787cf547aa3d758ef7251171c5d6e9f46e3fa6a7146434b6416e60eff60c145eb985c5615908557ddd577fc55c9554eb653562500544b9414a78f
|8,0=>0x9da0a934568cec372f416ad7a60eff54eb65356250054344fd32a22325e13220630a152d67c2a17c252fd2224d1fb6a1f46c1f3ae1e2e71ca721bd261ae931a04a19edb168ea105040dcae0d6170886a085c308448055f5055150534802842
|9,0=>0x35d9a2224d180a6021e8
|10,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa00aa000000000155555555555555555555555400000001555555555555555400000002aaaaaaaaaaaaaaaaaaaaaaaa22222222a2a2a2a2a2a2a2a2a2a2a2a222222225555555555555555000000005555555555555555555555555555555500000000aaaaaaaaaaaaaaaaaa88aa88aa88aa88aaaaaaaa88888888aa88aa88888888895555555555555555555555555555555555555555555555555555555400000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80005555555555555555555555554444444455555555545454545454545444444444aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015555555555555555555555115555551155555555555511115555551155551112aaaaaaaaaaaaaaaaaaa2aaa2aaa2aaa2aaaaaaaaa2a2a2a2aaa2aaa2a2a2a2a5555555555555555555555555555555555555555555555550000000000000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000154015401540154015401540154015401540154015401540154015401540154028282828282828282828282828282828282828282828282828282828282828284444444444444444555555555555444455555555555544444444444444444444
|0,1=>0x22222222222222220000000000220022222222222222222200220022000000000000000000000001555555555555555400000001555555555555555400000002aaaaaaaa22222222aaaaaaaa22222222222222222222222222222222222222244444444444444444444444444444444444444444444444444444444444444440000000000000000aaaaaaaaaaaa0000aaaaaaaaaaaa000000000000000000015555555555555555111111111111111111111111111111111111111111111112aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80000000000000000000555555555555555555555555444444445555555544444444444444444444444400000000aaaaaaaa00000000aaaaaaaaaaaaaaaa00000000aaaaaaaa000000004444444444444444004400440044004444444444444444440044004400000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555550505050505050505050505050505050aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa8888888888888888888888895555555541414141414141414141414155555555414141414141414141414142aaaaaaaaaaaaaaaaaaaaaaaa2222222222222222222222222222222222222225555555555550000555555555555000055555555555500005555555555550000
|0,2=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000000155555555555555555555555555555554000000000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa800000000000000055555555555555555555555555555555555555550000000000000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000015555555555555554015401540154015555555555555555540154015400000002aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaa800000002a802a80000000005555555555555555555555555555555500000000555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaa00000000a0a0a0a0a0a0a0a0a0a0a0a0000000011111111155555555111111115511551155555555111111115511551111111112aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaa802a802a802a802a802a80111111110000111111111111000011111111111100001111111111110000000000000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000015555555555555555111111111111111155555555111111111111111111111112aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000005555555555555555555555555555555555555555000000005555555500000000
|0,3=>0x22222222000000000022002222222222222222220022002200000001555555540000000000000001555555540000000155555555555555540000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa800000001111111111111111111111111111111100000000010101010101010100000000000000000000000000000000aaaaaaaa00000000aaaaaaaaaaaaaaaa000000015555555555555555555555540000000155555554000000015555555400000002aaaaaaaaaaaaaa22aaaaaaaaaaaaaa22aaaaaaaaaaaaaa22aa22aa22aa22aa25555555555554444555555555555444455555555555544444444444444444444000000000000aaaa000000000000aaaa000000000000aaaa00000000000000015555555555555555555555555555111155555151555551515555515155551112aaaaaaaaaaaaaaaaaaaaaaaaaa22aa22aaa2aaa2aaa2aaa2aaa2aaa2aa22aa25555555555555555555555555544554455555555444444445544554444444444aaaaaaaa00000000aaaaaaaa0000000000000000000000000000000000000001555555555555555555555555555400015555555555540000000000000000000222222222aaaaaaaaaaaaaaaa2222222222222222222222222222222222222225555555555555555554455445544554455555555555544445544554455444444
|0,4=>0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaa0aaa0a0a0a0a15555555555555555414141414141414155555555414141414141414141414142a802a802a802a802a802a802a802a802aaaaaaaaaaaaaaaaa802a802a802a800000000055555555000000005555555500000000555555550000000000000000aaaaaaaa888888888888888888888888aaaaaaaa8888888888888888888888895555555555555555555555540000000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaa80002aaa80002aaa80002aaa80002aaa80002aaa80000055005500550055005500550055005500550055005500550055005500000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000000000000000000155555555555555540000000155555555555555555555555400000000000000000000000000000000000000000000000028282828282828282828282800000001111111111111111111111111111111111111111111111111111111100000000020202020000020202020202000002020202020200000202020202020000000000440044000000440044004400000044004400440000004400440044000000008888888888888888888888880088008888888888888888880088008800000005555555555555555555555550000000055555555555555550000000000000000
|0,5=>0x22222222222222222222222222222222000000002222222222222222000000015555555555555555555555554141414155555555414141414141414141414142aaaaaaaaaaaaaaaaaaaaaaaaa802a802a802a802a802a802a802a802a802a800055005500000055005500550000005500550055000000550055005500000000aaaa0000aaaa0000aaaa00aaaaaa0000aaaa0000aaaa0000aaaa00aaaaaa00015555555555555554015401540154015555555555555555540000000000000000000000000000000002a802a802a802a8000000000000000002a802a800000001111111111111111001100110011001111111111111111110011001100100010aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0000000155555555555555555555555541414141414141414141414141414141414141400000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000055555555555555555555555555555555000000005555555500000000000000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000000044004400440044004400440044004400440044444444440044004400000002aaa80002aaa80002aaaaaaaaaaa80002aaa80002aaa80002aaaaaaaaaaa80005555555555555555000000000000000000000000000000000000000000000000
|0,6=>0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00aa00aa00aaaaaaaaaa00aa00aa00aa015555555555540001555555555554000155555555555400015554000155540000000000000000000000000000000000000000000000000002aaaaaaa800000000000000000000000000000005555555500000000555555550000000000000000aaaa0000aaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa00000000000000000001555555555555555555555555555555540000000000000002828282828282828282828282aaaaaaaa828282828282828282828282828282800000000000000000000000055555555000000000000000000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000015555555555555555555555555555555555555555414141414141414141414142aaaaaaa8000000000000000000000002aaaaaaa800000000000000000000000555555555555555555555555000000005555555550505050505050500000000000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaa000000000000000155555554000000015555555400000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaa80002aaaaaaa800000005555555555555555555555555555555555555555000055555555555500000000
|0,7=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaa00000000000000000000000000000000000000000000141414141414141400000000000000008888888888888888888888880000000088888888888888880000000555555554444444455555555444444445555555544444444545454544444444400000000000000000000000000aa00aa00aa00aa0000000000aa00aa000000015555555555555555555555555401540155555555555555555401540154015402aaaaaaa80000000000000002aaaaaaaaaaaaaaa8000000000000000000000000505050505050505050505050505050505050505050505050505050500000000aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aa00aa00aa00aa015555555555555555555555555555111111111111111111111111111111111112aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaaa80002a802a802a80000055555555555500005555000055550000555500005555000055555555555500000a0a0a0a0a0a0a0a000a000a000a000a0a0a0a0a0a0a0a0a000a000a000000000001555400015554000001540000015400015554000155540000015400000002aaaaaaaaa802a802aaaaaaaaa802a802a802a802a802a802a802a802a802a805555555555555555000000000000000055555555000000000000000000000000
|0,8=>0xaaaaaaaaaaaaaaaa0000000000aa00aaaaaaaaaaaaaaaaaa00aa00aa000000015555555400000000000000000000000000000000000000015555555400000002aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaa82828282a802a80280028000000000000000000000000000055005500000000000000000055005500000000aaaaaaaaaaaaaa00aa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa00aa0141414141414141415555555555555555414141414141414141414141414141400002aaa80002aaa80002aaa80002aaa8000000000002aaa80002aaa800000005555000055550000555500005555000055555555555500005555555555550000aaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000000155540001555400015554000155540001555400015554000155540000000282828282aaaaaaaa82828282aaaaaaaa8282828282828282828282828282828000000000000000000000000000000005555555500000000555555550000000000000000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000004040404040404040404040404040404040404040404040404040404000000000088008800880088008800880088008800880088008800880088008800000000000555500000000000055550000555500005555000055550000555500000000
|0,9=>0xaa00aa00aa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aa00aa00aa00aa015555555400015555555555540001555555555554000155555555555400000002aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000005555555505050505050505050505050500000000aa00aa00aa00aa00aa00aa00aa00aa00aa0aaa0aaa0aaa0aaa00aa00aa00aa000000000000000001555555540001555555555554000155555555555400000002aaaaaaaaaaaaaaa800000000000000000000000000000002aaaaaaa800000000000000000000000555555555555000000000000555500005555555555550000aaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa00015555555555555555555555540001555555555554000155555555555400000002aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000000055005500000000005500550055005500550055000000000055005500000000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaa0000aaaa0000aaaaaaaaaaaa00015554000000015555555400000001555555540000000155555555555400000000000000000002aaa8000000000002aaa8000000000002aaa80000000000028285555555550505050555555555050505055555555505050505050505050505050
|0,10=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00015555555555555555555555555554000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8282828000000002aaaaaaa8000000000550055005500550055005500550055000000000000000000550055000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000000000015554000000000001555400000000000000000000000000000002aaaaaaa800000002aaaaaaa8000000000000000000000000000111100001111111111110000111100001111000011111111111100000000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaa00aaaa00015401540154015555540154015401540154015401540155555401540154015402aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa8000000000000000000000000000000000000000000000000000000000000000555555555555555500000000aaaaaaaa0000000000000000aaaaaaaa000000000000000000000000000000015555555555540001555555555555555555555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000282828282828282800000004455445544554455444444444444444444554455444444444444444444444444
|0,11=>0xaaaaaaaaaaaaaaaa0a0a0a0a00000000aaaaaaaaaaaaaaaa000000000000000155555554000000015401540000000001555555540000000155555554000000000000000000000002aaaaaaa8000000000000000000000002aaaaaaa800000000000000055555555000000000055005500000000555555550000000000000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a000000014141414141414141414141414141555541414141414141414141414141414142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa802a802a802a800000000055555555000000005555555500000000555555550000000050505050aaaaaaaaaaaa0000aaaaaaaaaaaaaaaa00000000000000000000000000000001540154015401540154015401540154015401540155555555540154015401540002a802a802a802a802a802a802a802a802a802a80000000002a802a8000000005050505050505055555555555555555050505050505050505050505000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aa015555555555555554000000000000000155555555555555541414141400000002aaaaaaaaaaaaaaaa8282828282828282aaaaaaaaaaaa82828282828282828280000000055555555000000000000000000000000555555550000000000000000
|0,12=>0xa0a0a0a0a0a0a0a0000000000000001555555555555555555555555555555555555555541414141555555554141414282828282828282800000000000000002aaaaaaaaaaaaaaa80000000000000005555555500000000555555550000000055555555555555555555555500000000aaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa00000000aaaaaaaa000000000154015400000154015401540000015401540154000000000154015400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8000000000000000002a802a800000000000000000000000005500550055005500000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa00a0a0a0a0a0a0a0a0a0a0a0a0a000a0015555555555555554000000000000000000000001555555540000000000000002aaaaaaa800000002aaaaaaa80002aaaaaaaaaaa800000002aaaaaaa800000000000555500005555000055000000555500005555000055550000550000005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0a00000000000000015555555555555554000000000000000155555554000000015555555400000002aaaaaaa800000002aaaaaaa800000002aaaaaaa82828282aaaaaaaa800000000000555500005555000055550000555500000000000055550000000000000000
|0,13=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a000000000000000001414141414141414000000000000000014141414141414141414141400000002aaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaa222222222222222222255555555555555555555555555555555050505050505050505050505050005000a0a0a0a00000a0a0a0a0a0a00000a0a0a0a0a0a00000a0a0a0a0a0a0000000001540154015401540154015401540154015401540154000001540154015400000000000000000002aaaaaaaaaaaaaaa800000002828282828282828282828280055005500550055005500550055005500550055555555550055005500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa00015555555400000001555555540000000000000000000000015555555400000000000000000000000002a802a800000000000000000000000002a802a800000000000000055555555555555550000000000000000000000000000000000000000a0a0aaaaa0a0a0a0a0a0aaaaa0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a1555555555555555555555554015401555555555555555555555555540000000000000000000000000000000000000002aaaaaaaaaaaaaaa80000000000000000000000000000000000000000000000005050505000000000505050500000000
|0,14=>0xaaaaaaaa0000000000000000aaaaaaaa000000004444444444444444444444444444444444444444444444444444444444440002aaaaaaaaaaaaaaaaa802a802a802a802aaaaaaaaaa82aa82a802a802a802a8055550000000000005555000000000000555500000000000055555555000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaa00aa001414141414141414141414140000000000000000000000000000000000000002aaaaaaaaaaaaaaa802a802a800000002aaaaaaaaaaaaaaa802a802a800000000000000000550055000000000055005500550055000000000055005500000000a0a0a0a0a0a0a0a0a0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a15555555555555555555555555555555555555555555555554141414141414142aaaaaaa800000002aaaaaaa800000002aaaaaaa80000000282828280000000000000000555555550000000000000000000000005555555555555555000000000000aaaa0000aaaa000000000000aaaa0000aaaa0000aaaa00000000000000015555555555555554000000000000000155555555555400000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82aa82aa82aa80000555500005555000055550000555500005555000055550000555000005550
|0,15=>0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0155555554000000000000000000000001555555555555555400000000000000000000000000000000000000000002aaa8000000000000000000000000000000055555555555555555500550055005500555555555555555555555555550055000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000a0a00000a0a15555555555555554000000015555555400000000000000000000000000000002aaaaaaa80002aaaaaaaaaaa800000002aaaaaaa80002aaaaaaaaaaa80000000555555555555555555555555555555550000000000000000555555550000000000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa015555555555555555555555555555555400000000000155540000000000000002a802a802aaaaaaaaa802a802a802a802a802a802aaaaaaaaa802a802a802a805555555555555555550055005500550055005500555555555500550055005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a1414141415555555555555555555555554141414141414141414141414141414000000002aaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000000005555000000000000000000000000000055550000000000000000
|1,0=>0x2aaaaaaaaaaa80002aaaaaaaaaaa80002aaa80002aaa80002aaa80002aaa8000000000005555555500000000000000005555555555555555000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaa00000000a0a0a0a0a0a0a0a0a0a0a0a15555555555555555555555555555555555555555555541415555555555554142aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa8000000000000000000000000000555500005555000055550000555500005555000055550000550000005500
|_,_=>0
def sP:Nat→Nat
|0=>0x15850382a1182452010e0a01202138702e09130042a0a078503819080284a140e01c1e1412010460901004442110024161410024021f0a8781202008742007058040807048081a040501c120b0a00c04010e06c140200868320a0480802180182404010985c12010b054140907850260a048082411080281e0d07024040d060241601050240408038180a04018080200
|1=>0xa1102e09058042a07219082a2f1002402412008012011f8547c0901004383d04808782f1d82404010e0e804011201020071800408211c804702f108240a0b17840420f068bc140f0a0706e071b0d42a2f08080040d0a880123400854140905804660a010043832108240408160a01202008c45c09010483810108c0022f080b81e010e01c1601020b44209010345810
|2=>0x808004270e0544009008745415080841e1c2b8bc7a0901158382f0815404010e0100e0907850385410824041c298b00e09009482a2f288801e140e0540e02008680819108249e0f0e0bc420901004262f10824044e0e0bc422004934281c1582404140e130140901004964a03924021c2401006090100438470801c1e140e1182020010708a15080281e140e040140f
|3=>0xe1004009010043015038080224021407a0901004be2f080841e140e0107409011783804108240413298bc42092e848382f080841e1c228bc42020a07008191d02404010c0100e01121702a2f0801c1e140e1300e0213870082d1016c1e010e010420901048882f050241e140e130202007804385a08080021c2c810202107804882f0382428580a8bc4009010044440
|4=>0x36808021a0201c1202068104009378043815101b804140e054da0901004386c039ac04010e1a80e0901050440405008021c0c9404209011a4382c080ac04140e0547a09010503868080ac04140e19c203a01004380410824045e0e0b0420901190382f0818c1e010e1880e0f0a07008190818404010e010201e01004382f0818004140e0542020008582a2f100245201
|5=>0x160841202009f45e1010094281c0a88404010e0645e1005008021c35080127a008702a2004808f8140a81c12010b0545e2004804387b0a880127a00870ce5504808021c2388412020a070f2100503c281c0a88012020e1e08020049dc281c0a8400e02009d80810109d4021c1782804140e05432200382416140a9d00e0200870d4070e1cce41517828127100870e010
|6=>0xe2245e070100434041b8b8120200870ca880383c281c0221c400200870082101004382c16840420f0e14c5e101003c021c020280e0f0a0710c070483d0a1c2a01c0424218545e104203c281c0201c04010e20008103683c281c0201c04010e20c080a0483c02131781c1282408545e07010043880351fc0e020086808070105070151781c1e140e0b4982104808387e
|7=>0x10a2c021c17840c6020e15c2a0a038241e14220844009058045e200483c4e1c0a8400e010b0545e2b04808021d33884120f0a070980701004386a0d8e804010e010642104808025f178280e09058045e8810934021c178840401098b45e0a1082404660e0280e090a070b2070480802133508412022b12c5e10038c00215179fc0e0f0a070081010009141c0a8f40401
|8=>0x2002842090105096961d008021c020412a140e2502a0701004386a0c880120200910809310008281c0aa4804010e0545e2101240382d1788004140e2442a07049dc021a0201c120248070d410050801e140e084400907958381704804388f0a8411c0200870d4101000828220a880120b0085466101585038590a884128d0a0705e1704804388c0a8401425008705e10
|9=>0x870940704a7c021c3505c12020e1e02a07048083478022780401098545e104e808281c0201c12020e2702a072480802130221c740200870081010a6c281c1781c1205058545e9a03808021c020a07a09010503807048081a040a8f412020e1e05e200483c021302264120200870983a04809201c0226040020a0702a0a038241e140e01d2e02008700820048043848
|10=>0x4808021c548f41202009105e21048082813178f412020e15c5e101005038480a8e804010e0106e211402404140e0841202259e05e0a0383c281c1681c0401540545e215383c021c1784040a60a0702a0a04808021c5281c04010e1a86ea404808021c5184144020a0702a210480838a11788412022b07058871083c021c1781c1201500a85e7f03808021c35040140f
|11=>0x808404010e010c42104808021c161280e090a0715815178801202008702a4a10824041c2b9945e21048080213178841202270705e070483c021c338bc20212e8043815178840e090785038ab0801c04010e1a8200a07850380a0480802221988012010e0a8806d24808021c2601c04011c0545e101083c281c178f41202008c45e0701004380455220420f0e14c5e03
|12=>0xe2182a330382404140e2c8081003809621c0a8bc42092e80438651781c120f0a070a8070100438040c9412607010503815178800e0914804380410824041c298b020200100438155701c120f008708c2f08084041c228545e101080438480a8bc420901004886517828400901004384003ab412020a0702a070105038910a8bc20070105038152602812020a0702a4c
|13=>0x38241e140e1a0420901070a6bb178800e094d85038150801c04ba0e0545e9e0380802240a8bc20215c83c021c1788012020a07170150801c04140e0556e0704ad8281c0a8bc20630100438153101c04140e0102a190801c1e010e010c421048083845328bc4009008716a1523884120200870082c0808404140e0102a070480838b40a8bc0e0f008716615178800401
|14=>0x1781c12020e15c2a4a0830404140e0545e2104808cc140e0bc0e0f00870a8c0178412a0f008702a2f03824041c29afc5e21048080213020bc0e0907804384c17828120200870e0330801c04010e010d4215f0241e010e0bc20070100438042501c12010e0a82a2f10024041c2985494070483c021c020b020070785038040aa557a09010503815038241e010e2f05e21
|15=>0x4808281c580840e2b04808281c1082404140e0b05e5103809141c0a8bc0e0901050380463084400901050380403808281c430545e07048716a730a8bc20c50100438151781c120f0084c082f0383c021c620545e210382404140e30c202b010503815038241e850e0102a101030804010e054203a0100438041081c120f0a0705e0704894021c020bca207078043804
|16=>0x178805609388043815050240401098545e1010808021c230bd98200483c021c178800e0907850380403824041c228102a200480438480a8cc14070485038b50a88c4009010043815081b404010e010a020049c4021c0a9c00e020a0702a2d2604196010e3282a2f050241e010e11c5e0704809201c0a8bc0e0200870d42d03824021c6485590070483d8e1c0a8bc0e2b
|17=>0x501c04140e2182a2b04808021c260bc202107804382f0383c281c020545a8703808021c0a8bc0e0901070a6cd1781c1202428702a540382404270e0102a950382404140e05420200100438152508404010e0645e100383c021c338bc1421038241e140e08440090a0716a1510024f4010e0540e0f00870082d3101c12010b0545e070100438150c8bc2007011383815
|18=>0x160b4202107804382f2501c04d30e0545a2f0801c281c5a8545ed2038241e010e0bcfe070105038040a84040020a0702ad14f01c04140e0545e210480838d0678bc42090124038041781c12020a1102a2f0382404010e1a88e7f03808021c02140202101070a61517840400200870081503808021c021a85a511003c021c0a8bd9c2104808281c02084400926804382f
|19=>0x80ac04010e19c5e07010042615168bc40070480802110a8413a020a0702a2f10a90120200870581010009141c0a841ac020a0702a2f100241e010e35408100383c281c580bd0e3a0100438151781c12022b0702a2f0382402a05a8545e210382404560e0102084268043815178f41202008705ed4038241e140e1182a101083c385317840400f008700807010043815
|20=>0xc8bc4007010503815168800e090136438150801c1e8a0e0545e0704808021c3513040070482c02151781c12010e3602a2f0801d4c140e0545e070483c281c5818842070483c281c31040c60f008702a2f57b5c0e020087008bd0100438151b8bc0e02008900815178413c02008702a2f578400e020a070081010809141c0a8bc14070480828440a8f41202008705e68
|21=>0x8709850080804a010e0545e100508004140e0540e090105038045804042020a0719e2f0382404140e055be2104808021c3c8bcfe0701004381517a740e0907871bc2f0801c04016e8545e070483c38dc0a8bc200a07804381517a780e020e36c2a2f1082404010e2945e0a0382404560e0542007458043815178801277008702a2f08084021c6d0545e0a010043815
|22=>0x501c120200868080a03824021c2c8bc0e090e1e16a151781c120f0084c2a2f100241e010e0108e0a0382404140e054420704934021c1781c04010e055c62f0801c04560e0545e07012403815168bc0e02008702a37178e8120200870084c039b804010e010a00a1e82404010e0bc2007010043804710847a0901071762f108240414258bc0e0f0a071c015179b41202
|23=>0x4287008b0100241e010e01098070480838570aba8400704850382a0a81c120f0a071d22f108240401258bcd0200480438e80a84042070105038041001c120f738702ace04809ca1c0a8bc0e020e1e10c151781c56090105038043181c120f0e1145e21038249a1c298bc0e02008902a2d17884400900870b22f1081c120f0e1e05e0a038241e140e085c80901004382f
|24=>0x1781c12ed0a0702a2f1088012010e2d408ec0100438151b8bc0e090780438401781c12020e15c8a154f008021c0a9305e070485038590a8bc0e0f008702a1917a4c4002008702a2f4388404010e0545e030382404010e0100e0901004221517884c60901004962f0382404443c0545e2004808021c2000c0e0901004386a7581c120f008705e871d008021c0201c1202
|25=>0x483c281c0208412020087058680bbbc1202008702a20048043ab50a8400e0200bb82a2f1d01c120200870083d04808021c17a8c0e1e04808021c178840e0907804882f0808056020a0702a070480488b50a8bc0e0901070f0151784040020a0702acf10024e2010e054ce070480888820a8bc4009008716a400a8400e140e3682a2f1d02404010e0114a3d0480838bb
|26=>0x5e82404010e055560704809e41c0abc440090100438152508412020087008471781c120f00870ce2f0808004010e055e02f0382404010e010d821048080211328bc40093d00438400a8280e490100438040508412020a070ca070480802440a8bc0e02008e02a2f080841e140e0bc4009010043a15381b404010e0546e2f0382438535a8545e211002404010e0100e6d
|27=>0xa8bc940704bd0021c0a8bc0e09010503815788840e09010503815179440e02008700815178400eb9078043815178280e2b04808021c1781c04010e054a8c01781c120f0087008471781c120f730503815178800e090105038150382404010e054982f7981c12020a0702a2f0382404010e0102a2c0501c120200870e02f038241e010e1185e210382404140e054d020
|28=>0xa98820f9010043815178400e02008702ae21781df0090780438151781c120f00870982f1005c1202008702a0704808cc140e0545e070483c021c7b8545e0704804382a0a8bc0e090a0716a15178800e09010048815178400e02008702af61781c12020084c081517884402b04808021c1781d7c09078043815178417a0f008702a2f0801dea010e0545e070483c021c
|29=>0x480702a2f0801c04010e054ce2f050840e0901050381503808021c020545a6203824041c298545eea0382404010e0102afa0382404140e054582f100ac1202008702a33660801202008702a2f1001c12020a0700815102f41202008702a2f038241e140e2c05e21038241e140e0bc20200380438b50a8bc40070480438480a8bc4009010043815380cc0e095c83c021c
|30=>0x4808281c0a8bc0e0901070a6450a8bc0e09008716a15688bc202107804382f1081c120f008705eab4381c04010e0545e0704808021c200bd9c0704808281c020552a0704808281c0a8280e0901070f0151781c1202008702a541781c12020e15ca6151781c04010e054322f03809cc140e3ec2a2f038241e010e010982f0801c04010e345560724808021c0201c1202
|31=>0xc8bc0ebd04808281c02054420901070a665178400e02008702a2f7e8404202008700815178400e020a0702ab0178404207010503815178800e0901004380458084400704808021c0201c04010e0548e2d17bf00e090780438151784042020e14c2a2f03824041c680559e2f0382404900e0102a2f0808004010e0102a101001c04140e0542007010043815260bc0e2b
|32=>0x8716a151781c04010e0545a4c1781c1202790702a2f038ac120200871602f1081c120200870e02f10a10120f008702a2f1001c12020e14c2a2f1001c120f008702ac8438e804010e0545e0704808281c0aac0c4210382404140e054c40704808ac1c0a8bc0e09012143815580bcc6200382404010e0552abd04808021c0a8bc42070483c021c179a00e02008700815
|33=>0x501c12020a0702a21038249a010e0bc0ef804808281c0a8bc0e02008702ae31781c12020087009011781c1e010e4002a2f03808021c0a8dc5e7f03808021c020545e0704a6c281c0a8bc20077f80438151781c12020a12c2a2f0382404140e011600a1081c120f008705e2110024021c5a8545e7f03808021c0a8bc2007010503815678bc0e090780438fe178280e09
|34=>0x20545e070480802110a8bc400901004384003824041c298545e68102f4120f008702a2f0801c04010e0546e2f3181c1202008702a681081c120200870082f1d01c1202008702a2f0382404010e0545e680501c12020087008501001c12010e1642a2f578400e0200870082f0501c1202009102a2f3181c12020e1142a2f0801c04010e055fc2f6701c1202730702a2f
|35=>0x20840e0901070a6151781c12010e2d42a2f038241e140e0102a2f810400e020a0702a2f1d01c1202008700807049e8021c200545e100501c04010e0545e070480838780a8bc4009078043815198840e0901070ae151784042070100438041781c12f50a0702a2f1002404010e054ce33038241e010e1005e2103808021c430545e0a0382404010e0545e0737008021c
|36=>0xa8bc0f050100438151781c120f008700815178800e2b04808021c0a8bc0e09010503815580bc420704808281c0a8bc400704808281c0a81c1202008702a4c178800e09010043815380bc0e090100439041781c1202009102a2f0382404010d0100e09010043815380bc0e090140c3815178400e0f0a0702a2f03bb004010e0545a2f1e82404010e0bc422004808021c
|37=>0xab445e0a1081c1202008702a2f1001c12020087008151781c12020a0702aab0382404010e0545ef11001c1202008702a2f1081c1202008702a2f3401dac090100438151781d08090105038151781c1202090702a2f0382404010e1005e100383c021c0a8bc0e09010503815678bc42090100438651781c1202008702a54178840e0901004381517aac40bd04808021c
|38=>0x5e82404010e0545e200382404010e0545e0704808021c0a9945e070483c021c0a8bc0e09010043815380bc42070480838530a8bc0e09008716a151781c1202008682a2f6b8400e02008702a2f0501c1202008702a2f1081c120200870082f1d01c1202008702a2f0382404010e0545e684202404010e054c4070483c021c0a8bc668803808021c0a8bc0e8404808021c
|39=>0x382404010e0545e07
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x288010400620021000880004
|4,0=>0x81a83f941f2a0f45077a83a941caa0e0506da835941a2a0cc5063a8309417aa0b85059a82b94152a0a4504fa8269412aa0905045a82194102a07c503ba81c940daa0685031a817940b2a0545027a8129408aa040501da80d94062a02c5013a8089403aa0185
|5,0=>0x140b09ed84eca27061353099184bcc258612930931848cc240611d308d1845cc228611130871842cc21061053081183fcc1f860f9307b183ccc1e060ed30751839cc1c860e1306f1836cc1b060d530691833cc19860c930631830cc18060bd305d182dcc16860b13057182acc15060a530511827cc1386099304b1824cc120608d30451821cc1086
|5,1=>0x200b0fed87eac3ef61f4b0f8d87bac3d761e8b0f2d878ac3bf61dcb0ecd875ac3a761d0b0e6d872ac38f61c4b0e0d86fac37761b8b0dad86cac35f61acb0d4d869ac34761a0b0ced866ac32f6194b0c8d863ac3176188b0c2d860ac2ff617cb0bcd85dac2e76170b0b6d85aac2cf6164b0b0d857ac2b76158b0aad854ac29f614cb0a4d851ac2876
|5,2=>0x2c0b15ed8aeac56f62b4b158d8abac55762a8b152d8a8ac53f629cb14cd8a5ac5276290b146d8a2ac50f6284b140d89fac4f76278b13ad89cac4df626cb134d899ac4c76260b12ed896ac4af6254b128d893ac4976248b122d890ac47f623cb11cd88dac4676230b116d88aac44f6224b110d887ac4376218b10ad884ac41f620cb104d881ac4076
|5,3=>0x2d8a96ad8b4ac59f62ccb164d8b1ac5876
|6,0=>0x3b539d8dceb8e75573a739d1dce80e739739939cadce48e71d738b39c3dce10e701737d39bcdcdd8e6e5736f39b5dcda0e6c9736139aedcd68e6ad735339a7dcd30e691734539a0dccf8e67573373999dccc2c65a7329b9931cc8cc63f731c398c5cc54e623730e39855cc1ce6077300397e5cbe4e5eb72f239775cbaec5d162e53970dcb78e5b66
|6,1=>0x491ba471d22ae90e7483ba401d1f2e8f2747632395d1bce8d774683a325d184e8bb745ab22b9d14ee8a0744d3224dd11ac886743fba1e1d0e2e86a7431ba171d0aae84e7423ba101d072e8327415ba091d03ae816740832025d004e7fb73fa39fb5cfcce7df73ec39f45cf94e7c373de39ed5cf5ce7a863d0b9e69cf28c78d73c339dfdcef0e7717
|6,2=>0x5703ab65d5a4eacb75623aaf5d56ceaaf75543aa85d534ea9375463aa15d4fcea7775383a9a5d4c4ea5b752a3a935d48cea3f751c3a8c5d454ea23750e3a855d41cea0775003a7e5d3e4e9eb74f23a775d3aec9d074e4ba709d376e9b474d6ba699d33ee99874c8ba62d930ac97e74bbba5c1d2d2e96274adba551d29ae946749fba4e1d262e92a7
|6,3=>0x64d3b24dd918ec85763fb31e1d8e2ec6a7631bb171d8aaec4e7623bb101d872ec327615bb091d83aec1766083b025d806cbfc75fabafb9d7ceebe075ecbaf4d9798ebc575df3aeddd760eba975d13ae6dd728eb8d75c3b2e01d6f2eb7275b5bad91d6baeb5675a7bad21d682eb3a7599bacb1d64aeb1e758bbac41d614cb03757e3abd5d5dceae77
|6,4=>0x1a9aed46769fbb4e1da62ed2a7692334799a2eed107684bb409d9f6ecf47676bb39d99c0ecd976693b32dd988ecbd765b3b2bdd950eca17
|7,0=>0x79bc3cbe1e4f0f20778c43c421e12ef03677e3bbd21dd90ee4876e43b521d990ec4875e43ad21d590ea5774f3ba5a1d1d0e86873f439dddcdf0e6787303b965dca30e4987213b8eddc670e2b8711c386e1c270e0c7702bb7f61becedef76f3c377e1baf0dcf86e3c36fe1b6f0db076d4436821b310d9086c4bb6061af30d7276b5bb58e1ab8ed548
|7,1=>0x89044462222111088880443e5e1e4f0ea8871bc36e21a8f0cd7862c42f9e16ef0b07854bc2862133109278454420de0f7107388363c19220b91054882644112207af0358816c4099e03d101688074401a1ffd0ff687f7bbf9e1fbf0fd787e7c3f1e1f7f0fb787d7c3ea1df410f9887c8bbe29df050f7a87b943daa1ec8cf5c87aabbd39de8d0f3f7
|7,2=>0x9183c8a9a445121b790a3c832240cd1ff78fbc47c1e3d111e088ecbc746239311c278ddbc6ce235711a478ce44655e31b118588bec45d9e2e0d16888b04456222a1114888a0444e2226111288
|8,0=>0x26b5135289a5bcd11e6791334899644c92263913157986c4c19e5fb32f49975ccb91e5b912d48965ccb0e257712b47956bca99e53d12977947c4a1a64fd12777937c499a64bd12568927bc91e247d32377
|9,0=>0x9bcc4dc626d313627
|10,0=>0x13817
|_,_=>0
def wAt:=mkWire dB 262 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa8bc108bd008bd038550481d010551e8bd10997038550a81c138710a084008bd1785503855178850a81d0e1950a81c08010021430a8bd1785410055038bd0481d008bd081a802143178550a8bc438100a8bd2801d17854108bd0a195038550a81c02143178540201d178550e09d0a0840a81d17855008bd109980a195038550a81c01055008bd0204017855078800a8cd038bd1781c020400a8bd0e1410a8bc
|1=>0x8bd039410481d0a8bd178540a195038550a81c038550e11d0201c178552999703854038550e27a1681d020270a8bd0481d008bd020401785503855238bd0201c0a8bd0a8bd03855008bd0481d01055580bd008bd038560a8bc02040178551080703855328bd0a81c578bc10101038bd198551781c178551799503854108bc03855108bc0a81d0e11d0201c178550a81d009c110054038bd0481d0214317855
|2=>0x201c0a8bd021430a8bc0201c0a8bd0214317854178550a81d1785605027108bd0a81d5e8550a81e010550481d0a084008bd1785503855108bc080100a8bd038550481d01055108bd03855078cd01055038bd1781c0e0aa5a8551000b038bd02040558550a8be0a882108be1781d1000b10055038bd10055010cd038bc10054038bd0214317854020271785517995038550a81c038550385510057038bd0481d
|3=>0x201d0a8bd01055108bc0111d0201c038bd0a8bd0201f021430a8bd178541781d17855008bd0507310055038bd108be10997038550a81c0e129108bc1781d0a81d108b303855328bd0a81c038251781d558050a8be1781d17855108bc038551e8bc10997038550a81c10807038550481d010551781d0a8bd0481d01055108bc038550481d0105503825010821781d008bd008bd17856038bd0481d038550091d
|4=>0x10553501d178860a81d0e1950a81c038bd25055108bc038553501d02143178550a8bc048e90a8bd2801d17854178870a81d0e1950a81c5a8cf038bc1000b038bd7301c1781d0201d17855008bd01055038110a8bd0e1410a8bc1005510057038bd100110a8bd038bd038122801d178550a8bc1099703854108bd0385510997038550a81c178050a81d0e1950a81c708270785110055038bd0481d008bd108be
|5=>0x38550a81c0e06502040178550481d008bd038550481d010550a880038bd0e0cd038bc038bd0a8bd0201e17855008bd01055108b203855328bd0a81c0b857100cf038bd1781c01082038bd0e0cd038bc10880178550a81d1781d1e8be10997038550a81c10057038bd0481d008bd0a056038bd0481d008bd10056038bd1781c0135e080bd008bd020e80a8bd2801d178541e80710997038550a81c020400a8bd
|6=>0x5800903856178840a81d0105563009420561781e008bd328be0a81c008bd178555e8250481d0a8ad10057038bd580bd03856010550201c178550a055008bd010550398917805038be0211f0201c0a8bd670550a01d008bd238bd0201c0a8bd3105501055038be038550a8be038bd00bc5328be0a81c1781d108bc0a81d038550201c178550105510056038bd1781d080560481d04941178540201d17855108bd
|7=>0x10057038bd1781d6881d17856008bd0a8bd038bd100540a81f008bd010550a81d008bd010550481d1000b1781d10055038bd038bc10054038bd010557801d080560481d6b854080bd0481d5e8bd010550201f17855100cf038bd1781c0a195038545c81f078bd010555a8551000b038bd010821781d008bd0507310055038bd17bc10e11d0201c0a8bd100571781d03b23078be010550a81e010550481d0481d
|8=>0x201f0a8bd008bd10057038bd1000b038550481d01055178570a81d010552481d049410a8bc25055108bc03855178550a01d008bd03aad178050a8be0500710055038bd260bd0201f0a8bd298bd108070385502040178550481d730270a055008bd0201f0a8bd010550481d0a8be1785617855049410a8bc0091d0201c0a8bd0481d100561781d108bd0385502027298bc10807038555e8be1799503854038bc
|9=>0x38bd01055048e92801d178540a81f17805038be0a81d1780500929108bc038550a81f31005038be1781d108bf0a81d0a8be108be0a81d0105502040178550a81e17855008bd038541080703855578be080550481d0481d038551785503856008bd0481d008bd038bd0a8bd178550a81d1781d020270201c0a8bd07a11010551781e10807038550481d0091d0201c0a8bd17855038bd0481d1781d008bd0481d
|10=>0x481d31056038be100551781d008bd0a81d68809178565e8bd008bd0a81e0491a31055038be5c827078bd01055049320201f0a8bd0201e178550133d0a056008bd0481d011410a8bc178050e1950a81c008bd0a8bd0385601055108bd03855049b50201e17855038250a056008bd0a80931056038be1000b10055038bd0201f0a8bd00bc5328be0a81c10057100540a81d1781d010551781e008860a81d1781d
|11=>0x8bd01055080510481d008bd2801d178550a8bc19855038bc0201d178550481d0500710055038bd01055038bd1781c298bd0385517855008bd580090385610056038bd1781c0a8cd038bc0105505027108bd0a81d039310201f0a8bd0201c0a8bd0e129108bc03855038bd198551781c01055038bd0a8bd100840a81d1781d108be5e8550a81e178540201d17855038bd178550507310055038bd108bf0a81d
|12=>0x8bd1781e009950a81c198551781c0481d010550a056008bd038550a81c580bd038560a81d0a8be038bd0a81e048cd038bc0a8bd0105510057038bd008bd0385603855008bd1781d008bd0201f0a8bd10054038bd198561781c0507310055038bd0a8bd0e1410a8bc10054420bd1781e0a19703854008bd008bd0481d0105510997038550a81c038bd1785503855108075e8550a81e1000b420bd1781e17855
|13=>0xa81e038bd0a81c0105510054038bd10807038551000b038bd0e1410a8bc080bd0481d10055038bd17855038552801d0a8bc108be03855038be1781e038bc01055420251781e178561781e108bd038550a8bd038bd178050a8be328be0a81c420bd1781e108be038556881e17856
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x4140000000000000000000000000000000000000000000c4000008400000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000
|5,1=>0x214075000000000000000194000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015400000000000000000000000000000000000000000000000000000000
|5,2=>0xd9031500000000000000000000000000000b50000000029400000000000000000000000002540000000000000000000000000000
|5,3=>0xe94000000000000000000000000
|6,0=>0x1e0c00000000001d1000000000000000000000000000000000000000000071300000001b506c1000000000000001a4c0000000000195061400000000000000000000017505a30000000159055100000000000000145000000000000000501131000012c400011d0434000000000003f4
|6,1=>0x2dcc0002d84b512c8c0002b9000000000000000aa40000a912950000288c000279000026909730000961000095125040000000000244c90100008c400000000000000221000000000000000853000000021040000000000000000020c47f400000001ed000000000000000000
|6,2=>0x400400000000000000fd30000fc100000003e10000000000000000003d10f31000000000000000000f2100000000000f110000ee33a900000000e640000e243790000374400000000000000da30000d640000d243390000329000031900000000c2400000002f900002e90000
|6,3=>0x528d46450900000000000000000000000004fcc00000013e100013a400013644c900004b90000000000000000004a9126400000004944000000000000000004904000481000047111930000000000116300000000000000000112400010e400010b341d105200000004050000
|6,4=>0x18145f8c0005e917645c9000000017025b11684591160400015c456100000001544000000054114d3
|7,0=>0x894e22387ce1c3864e16384ce103834e0a3820a071810e0318049fe37ecdf837dc5f437c4dee37b09e937a05e53788de11778ddb37649d6374cdd03734dcc1724dc72710dc136f8dbb36e0db536d05b226c45ae36b09a93698da33680d9d3668c00065cd9616509913638d8b3620d853
|7,1=>0xb146c23b00abd30002ba3adceb43ac4c000ab8eab3aa4aa63a8cea03a74e9a30002973a50e913a38e8c2a24e881a14e832a00e7e29ece7839d8a7339c0e6d39b0669399ca643984e5e396ce58395c6552948e4f3930e493000246390ce4038f8a3b300023a18dce3438c4e2e38ace283
|7,2=>0xc64f163c4cf103c34c000c28f073c10f013bf8efb3be0ef62bccef03bb4eeb2ba86e73b90ee13b78edb3b64ad63b4cc000b4480000002d01b34eca3b1cec61
|8,0=>0xd98b642d88b602d78b5c2d68b582d58b542d48b502d38b4c2d28b482d18b442d08b402cf8b3c2ce8b382cd8b342cc8b302cb8b2c2ca8b282c98b242c88b202c78b1c2
|9,0=>0xdac76a1da47681
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x20f00020000010d00010b00010000008e00006400004400004000002900002800001b00001800001400001100001000000f00000e00000d00000c00000b00000a000009000008000007000006000005000004000003000002000001000000
|1=>0x320d00310f00310b00300f00300200280000211b00210f00210b00210000204f00204700201b00200f00200200200000110200110000104000100f00100d001008001004001000000a0000080f00080d00080c000806000802000800000400
|2=>0x702700700f00700e00700800700600700400690f00680f00680d00610000608e00602f00600f00600400600100600000580f00580d00504f00504000500f00500b00500400480f00480000402700400f004008004004004002004001004000
|3=>0x80100e70080408100008010208010004304f04200a04104704004202300f02000f01690f00980f00800000710f00704f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x810000000080000000000000000000000000000000000000000000000000000000200000000000000000000000000000000300000000000000000000008000800000002000000000000000000000000000000000000000000000000000000800000000000000000
|5,1=>0x1e0000000000000000000000000000000000000000000000000000000000000000000000004040000000000000010000020000000000000400000000000000
|6,0=>0x1002e40400120000000100404c004002200502004001e360000011000140000000060000000200005a000000000b85018818000000002a000000400000000000000000000020000186c000000010000001040000000000018200004a100000001e0000000847808000d160000003
|6,1=>0x10f12000000000000040003000200051e00180000000010140002e000000000d801e0078400000080000000000800f0020d2000007800002000000000201000001000000000011b000000000840000078008100000200202803600000002000f0024080120008000100000401900
|6,2=>0x203c4004824d000140108086800210000040000c04
|7,0=>0x4e3c449003db8456c0e8d04d5e55683c00f30f4e02a70215086b9e4998b24c180211318a22943814210f27200029d3412900a32087f2cce81e083a6cec5e1f8c115280ec0443a21a033710c245db612b6723caec16b022185417d7a6de9df80eb581042f4c5041d880785e8539609ba3
|7,1=>0x1d965d31e007de8929dee644878f8a223b2097840f85bc780ac00040042079b
|8,0=>0x2f53979b18fbd7964bc33edacbbaaf4b557a6d49765ac5a772f4f7d6b0609b7995e
|9,0=>0xa72e9b8
|10,0=>0xf
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 9 roots_252 ops++addP pm 1 dom_238 9 roots_238 ops++addP pm 2 dom_246 9 roots_246 ops++addP pm 3 dom_250 9 roots_250 ops++addP pm 4 dom_214 6 roots_214 ops++addP pm 5 dom_218 6 roots_218 ops++addP pm 6 dom_122 6 roots_122 ops++addP pm 7 dom_220 6 roots_220 ops++addP pm 8 dom_182 6 roots_182 ops++addP pm 9 dom_174 6 roots_174 ops++addP pm 10 dom_242 8 roots_242 ops++addP pm 11 dom_206 6 roots_206 ops++addP pm 12 dom_126 7 roots_126 ops++addP pm 13 dom_190 7 roots_190 ops++addP pm 14 dom_222 7 roots_222 ops++addP pm 15 dom_110 6 roots_110 ops++addP pm 16 dom_230 8 roots_230 ops++addP pm 17 dom_188 6 roots_188 ops++addP pm 18 dom_186 6 roots_186 ops++addP pm 19 dom_118 6 roots_118 ops++addP pm 20 dom_234 8 roots_234 ops++addP pm 21 dom_202 5 roots_202 ops++addP pm 22 dom_106 5 roots_106 ops++addP pm 23 dom_124 6 roots_124 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_124 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 9 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 48 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 48 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128 : ∀ i, 128 ≤ i → i < 200 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 72 128 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 200 → Z 5 i = true := (range_split z5_0 z5_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 282 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 26 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 282 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 164 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 164 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 38 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 38 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_254 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_254 roots_254 goal_254 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_254
theorem lowS_254:Lower true dom_254 roots_254 goal_254 11:=S_254.noCircuit
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 10:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_251:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_iso_b isoMvS_251 (by decide +kernel) lowS_247
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0e0000000000000000000000000a0a00000
def gsh_155_4:=0xf0f0f0e0000000000000000000000000a0a0000
theorem lowS_zo_155_4_155:Lower true dzo_155_4 roots_155 gzo_155_4 6:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [] (by decide +kernel) lowS_155)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fe0000000000aa000000
def gsh_87_8:=0xff00fe0000000000aa0000
theorem lowS_zo_87_8_87:Lower true dzo_87_8 roots_87 gzo_87_8 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [] (by decide +kernel) lowS_87)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000aa000000
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000aa0000
theorem lowS_zo_215_8_87:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_87)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000a0a00000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0f000000000a0a0000
theorem lowS_zo_219_4_155:Lower true dzo_219_4 roots_219 gzo_219_4 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_155)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00aa000000
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fe00ff00ff00aa0000
theorem lowS_zo_247_8_87:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_87)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0f0f0f0f0f0a0a00000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0f0f0f0f0f0f0f0f0a0a0000
theorem lowS_zo_251_4_155:Lower true dzo_251_4 roots_251 gzo_251_4 8:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_155)
namespace S_255
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,34),(2,66),(2,130),(3,19),(3,35),(3,67),(3,131),(4,36),(4,68),(5,21),(5,37),(5,69),(5,133),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(8,40),(8,136),(9,25),(9,41),(9,73),(9,137),(10,42),(10,74),(10,138),(11,27),(11,43),(11,75),(11,139),(12,44),(12,76),(12,140),(13,29),(13,45),(13,77),(13,141),(14,46),(14,78),(14,142),(15,31),(15,47),(15,79),(15,143),(16,17),(16,80),(16,144),(18,19),(18,50),(18,82),(18,146),(20,21),(20,52),(20,84),(20,148),(22,23),(22,54),(22,86),(22,150),(24,25),(24,56),(24,88),(24,152),(26,27),(26,58),(26,90),(26,154),(28,29),(28,60),(28,92),(28,156),(30,31),(30,62),(30,94),(30,158),(32,33),(32,34),(32,36),(32,40),(32,96),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,80),(64,96),(64,192),(72,73),(72,74),(72,76),(72,88),(72,104),(72,200),(128,129),(128,130),(128,136),(128,144),(128,160),(128,192),(132,133),(132,134),(132,140),(132,148),(132,164),(132,196)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|5=>24
|6=>146
|7=>411
|8=>448
|9=>190
|10=>42
|11=>7
|12=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf2d3ee9c4ddfaf5d109ac2036c16f9bbb23b7d8cb1294983738decc89c62881ce7cc9e67a1547cb0473133eca82c1f6292782566f134400c7ca01a97
|6,0=>0xbbc63b82b5b7f7db4f84ad915a9a54a82c0a4d67a4a9da4636a453ca2ae5a16ef9fe7d9dc569983795d6d943978f4ad8c4248b6798a2a788e67872c285ec9831a482933822c080ef47847877cd27668a740c973b29732086e21e6cf686bca064edc63eac61e9a6146760eaa5b2275ac33597b8583dc56e465695f534dc521c14e4e54ae714a5d1498bf482954615445e11445544354342ffa4246e4220842179417984122a411f840f1d3dca83d2373bc523ba72383bf3756335a4d35762354ea354c935441347ab341263183830ac5309ff3051d2e54f2cc932c8412b0602775125a52236fd22e9a214b920b7c1faf41f6a71f5541dc4c1db161c9611c1c51afa61a19b18993179fe154761313e1280911dee10f4b0fbf80f8ea0f8d70eb230c8ab0b20a0afef0aa7908967081eb074cd0702e063d20612105d1303dae000c8
|6,1=>0xf014ae90e5e8602dde3bd9349d7046d6c28d67ccd63ead2e70d2cf9d290bcb6f8c7cecc62dac3ca6bd45dbca93
|7,0=>0x2ccb32bcbd2b7912adbf2aa8b29f7529cdf28b2a28add283fb2823927ddd27b88274a0271ab2716f25b792593a2503724dc6240a12361d2324122f1e22a52228ac2259b2246621d7e21d6c218ca217f32068d1f03f1e9d21e50a1dfec1ce8e1c0cf1bdc11bad91b3161b3101acec19a9418a741818818120173d3171b816c4216aa416a5f1684d166f8160931605915f1c15dae159ae159a9153b814ecb14c2a14b30147bb140a213e4e13cfd13b3613ac71369612ef112aef1270011edc1188b1111c10b4f101090ff770fbb20f2450e7960e66f0dd680db2d0cb2f0c6370c31a0c2910c05d0b7b60b3a00aad00a9890a6bd09d5a0993c094e008e2a0871107f80077430738f06958068b2068450668e0613905b8405b7d057f2056250519b0415303f6103f2003c960345403420033930334f032910231b01e9e014b300d2b
|7,1=>0x687326839a673f0672d96729b66ebb65c5965a3a65557647516454c642ef635b062e1962cbb62b2860866606e6600dc5e5d45e38a5dbc65dab65d76a5d6525d1cc5d0bf5abb55a9e55a7365a0a159a4958a885868957e1655a8854b52548925476d5464a53e045301e52c53527c351a305126650cbf50bb850b7a50390501fb4f70c4efd54eda14e3424e2ed4dec64de0b4d9614d2d54d0e64d0b64cdc44b2004a3954a2854a09f4982c47e0f47c3b4779946a8e45655452c14410a43339430f3429b3425fe425314192b4169241340405b7402ef3fe8f3fa8f3eac63de4e3d6ad3c9ed3c6e63c69c3c47c3bac63aa4a3a71839cd139b22399b83971f3907a38e5c3765e3705c36f7836e4136abc3689c3646635aa3357da3576b329a631c1b30ee930a03305f82ff0a2f8c62f23f2eff22e9812e38d2df352d9672d0fd2cd39
|7,2=>0xcd89fccc18cc797c8e75c8d66c8c5cc70abc55a9c3e33c3e17c33c5c114dbf6a8bf4f2bf138bee1fbc844bb205ba975b9adeb705db6b58b6441b5c1db57dbb4078b14f0b14b9afd2daebd1adae7ada88aaa19a87b3a70c2a53b9a5117a3bc7a2feea218fa1f36a19c6a0fc5a0c1ba08a09ffbe9f4cc9e3849e1c39d8f49d17b9b86d9b3df99561991b097de697842975879687f96470963c69598194cb39233c9209291f9d916df910aa8eafc8e4fd8e4898cf088c0be8ba5d8b1ac89fbe88f3f861f08517e84edf84a9583e9b8347382c1182b808250a80ef480ccd802927fd227f3d17ef777e9d77db857d4267c51f7c3c37b6ed79cdc7926377e167745e773a77726876b0b7668074bdb74253734f87325670fb470a9670406702f96fe086fb6a6faaf6ed5a6ea686dcd36d0736cd4c6b2646b0d369db9693636882868762
|7,3=>0xfe9e9fcbb7fc762faa00f7fc0f7980f0171ed970ebf28eb5d2ea0a2e1196e08aae083fdff14dcf2fdaabed85a0d7250d67bbd264ed138dd1149d0819cfe6fcf78bcf33d
|8,0=>0x2d0fd2d06c2c37a2a7a32a5882a1f728e62284702843927c5227797274df270d725c4a2582e256542521d247a32470f237f9234f0223dc22199220e521caa215812068d202de1fcd51fb161f8061e9751e8c91d5f11d2f01d04b1cdf91cdb61cd181c2d21bccc1ba441b00b1ad991a1721a13f1a0e019cf6188001866018007178ba16ef7169e6168861660d163bb15f2315b05157e1157c01572e156a915433152f514da514b59148c81487013b9713602135531328612d6612c2812b2111d4d11c32110e610bb310b8a1032a0ec930e8a30e2f20e2210e0670d9d00d78d0d7360cd210beef0b2b40aaa20a84409648085c707af7075ce071be0715d06cb706c3b069520541404a63043fc041ba04189040a103bf903b71039b003909036f5036cf0329a0324e02ed702c6c02b830201f0192300e7100a9400a9300971007f3
|8,1=>0x6558e650ee648bb63f4e63bfd63163624376211661d8261d06610a160936605e95f9b85f6415e9d15c9f35c5a65b57c5b4c55b4765b4475a2c859e8359dc0591fe58f8557f885784155f2554a80538af535675356452e915241b506ec505174eda14ed104ecef4ead54e6b74df294dbb54d7d24d5ed4c7804c4474bb874b7884a2854a0e749ecc49956491dd48d7b486bd4742f473e846c1346b6246a1a4684a4641a463b3461e6459674580345676445c44403e43e4243e3d439ac437fe435dd4344a43419432254300a42cd241faa41f59414aa4123f41186406193fe0a3f8433e5df3d8ac3d3673ccaf3c7053c3833b5f23b4253b4083aa233a9023a74d3a6113a17939cab397d238e7c38b9b38afc38a7e37fcb3717b36e67350ca34e9934ca6349553452233eb8338d6333743213d319252f5d02e9f42db932da932d9a2
|8,2=>0xaa172a8430a7e43a7b58a70c2a674da5fdea572aa5379a5028a4dbca3faf9fef29fd879fa539e1669e0b39e0429d4069d0cf98f539826b9708995afc9583c925e091b569109e90710906b7902428fdd38ed498ebc98d9c38d8c98d6f98d3b88cc888bf508b1408a12687f8d87eab878b6874ec86b6e8613685eb484a028413d840db8311882f2d82f0f82cd4827768250882420812ea81001806f8806757ffe97e73a7dea67d31b7d10d7c4c27b8a57b4227aeca7a4ad7a05c78eae78a3c759e7749f17463f74563743fe743a673b4c7309d7304172ba3728857206071e6c717b670f7d7091a7081b704b8700346ff436facf6f8596f7016f3fa6efc96ee846ea6c6d82b6d42c6d1086cf256c8af6c6cc6c4336c22b6bd1f6bb896bb706ba1b6b7146addd6a79d6981b684ee681ca67e8a66fae667e26620765fdb65c1265650
|8,3=>0xffc26ff47ffe9e9fcbb7fb970facc8f9c7bf3e61ec7f2eb59de3770e0f81de3ccdd7dbdd140db4b5d7997d6a5ad61ead5fe9d570dd503ed4c4ad133ccff74ce0f3cc778cc455ca556c939ec9184c8d66c737dc50f9c3226c1810c1211c119dc10b4bedffbdb2abd6b9bb6c0ba3beba363b9809b919bb7c52b561bb4345b3da0b32f2b31abb2fa6b20e5b1582b03a3af6e9aebd1adbf4ad55facde4ac187abcc5
|9,0=>0x75f3975d1e7317772f5d710b570a066f56e6eb046e3496d82b6ce8d6c0286bb906bb816b80a6926f69126689a7679ba6666b661d46562463cd462437607a7604b15f72d5d7645561754f8154295535b152be352824515dd503054ee9b4e9e04d5a74ca0a4bb874b45e496fa48c83488ce4854c475ab46cff44d6444cc544c474453042aed3e91c3854336e9d3426a33507331b732c1b32b87324fa324323235931ad52fa7c2f5592ef2a2cf732a74d2994d2919a28f7f26fdf26ab3266222529924cd624a5223880230c1230c02198920e491f7cb1f00b1edf11ceb81cc781bade1b5831aa611a4bb1a452180451747d16e7e16e6514c1b1479013c9513a08137971332612dfa11311110e01026a0dc600d79f0bdef09a2c097630887e07d52074f605eec05eac05e44059c30497e0483e020fc0203801c410178f0141d00ffa
|9,1=>0xf74fcf5f3af317cf03cdeec65e9c1de4296dfaf8dee9bd8876d808dd6f57d5858d1f5dd0e7ad0b56cdfe5c8f1cc6587c34cbc2347bf374bde54bcc1bbb8b2ba5cab8e4ab752baf1d6ac7c9abf73a919ba8088a7277a511ca5038a4b80a362ea142f9f9489f5c39e6739c8809892697b6f974f79732796c6293e2992d59929c4920fc915078f5ee8cad48bf128ab258a5f58830f8597e840db76c25
|10,0=>0xf9e3af929bf2088f1d64ee5c6e8631b3d91abd33a18279d6d09b6bb9a3e6938e2858f783394779d97543866f7e61018533285217a4ce604603a4464140a383f88a3eb0338b5830f012fa492ccef26c2a2100c1fe5e1d8c31d2a91622e0b04b09c6b08aa90806d05ce0
|11,0=>0xd050ad03e4a52e9994432ac3a29a8c2299d
|12,0=>0x83645
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffccccffffffffffffccccffffffffffffccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaaaaaa
|0,1=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000ffff000000000000ffff000000000000ffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff00005555555555555555555555555555555555555555555555555555555555550000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff000055551111555511115555111155551111555501015555010155550101555500000033003300330033003300330033003300030003000300030003000300000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000000000000000ffff000000000000ffff000000000000ffffffff0000ffff0000
|0,2=>0xffffffffffff0000000000000000ffff000000000000ffff000000000000ffff00000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000003333333333333333333333333333333333333333333333333333333300000000ffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000003333333333333333333333333333333303030303030303030303030300000000333333333333333300330033003300333333333333333333003300330000000003030303030303030003000300030003030303030303030300030003000000000000333300003333000000330000003300003333000033330000003300000000333333333333333333333333333333333333030333330303333303033333000000ff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f000f00000000ffffffffffff0000ffffffffffff0000ffffffffffff00000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000003333333333333333333333333333333333333333333333333333333333330000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000
|0,3=>0x333333330000000033333333000000003333333300000000000000000f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f0f0f0f0f0f0f0f0f000f0f0f00000033003300330033003300330033003300030003000300030003000300030000030303030303030303030303030303030303030303030303030303030000000000000000ffffffff00000000ffff000000000000ffffffff00000000ffff00000f0f03030f0f03030f0f00030f0f00030f0f03030f0f03030f0f00030f0f0000ffff3333ffff3333ffff3333ffff3333ffff0303ffff0303ffff0303ffff0000fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f0f0f000000000ffffffff00000000ffffffff00000000ffffffff00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff000000000f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f0000000055551111555511115555111155551111555511115555111155551111555500000033003300330033003300330033003300330033003300330033003300000000333333333333333333333333333333330303030303030303030303030303000000ff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f000f000f0000
|0,4=>0x5050505050505050505050505050505050505050505050505050505050500000000000055555555000000005555555500000000555555550000000055550000000000000000000000000000ffffffff000000000000000000000000ffff00000000000033333333000000003333333300000000030303030000000000000000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff0000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000ffffffff0000000000ff00ff00000000ffffffff000000000000000000000000ffffffff00000000ffffffff000000000000000000000000ffff0000000000003333333300000000003300330000000033333333000000000000000000ff003300ff003300ff003300ff003300ff003300ff003300ff003300ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffff0000000000000000000000000000ffffffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000055555555555555555555555555555555555505055555050555550505555500000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000
|0,5=>0xffff3333ffff3333ffff0033ffff0033ffff3333ffff3333ffff0033ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000111111111111111111111111111111111111111111111111111111111111000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff000003030303000003030303030300000303030303030000030303030303000000000033003300000033003300330000003300330033000000330033003300000000ffffffffffffff00ffffffffffffff00ffffffffffffff00ff00ff00ff00ff000303030303030303030303030303030303030303030303030303030303030000003300330033003300330033003300330033003300330033003300330033000000330033003300330033003300330033003300333333333300330033333300000000000000000000ffffffffffff00000000000000000000ffffffffffff00000505050505050505050505055555555505050505050505050505050555550000555555555555555555550055555500555555555555555555555500555555000033333333000033333333333300003333333333330000333333333333000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000
|0,6=>0xffffffffffffffffffffffff00000000ffffffffffffffffffffffffffff00000000000000000000ffff00ffffff00ff0000000000000000ffff00ffffff00000000000000000000000000000000000000000000ffffffff00000000ffff00000000ffff0000ffff000000ff000000ff0000ffff0000ffff000000ff00000000ffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff000000000000ffffffff00000000ffffffff000000000f0f0f0f0000000000000000f0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffff0f0f0f0f0f0fffff0f0ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff0000ffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0000ffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff0000000000000000000000000000ffffffff0000ffff0000ffff000000000000000000000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000000ffffffffffffffffffffffffffff0000
|0,7=>0xffffffffffffffffffffffffffffffff0000000000000000ffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff0000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffff0000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff000f00ff000f00ff000f00ff000000003333000033330000333300003333000033330000333300003333000000000f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00ffffff00000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000333333333333333300330033003300333333333333333333003300330033000000000000ffffffff000000000000000000000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000000000000000ffff000000000000ffff0000000000000000ffffffff000000000f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0fffff0000000000000000ffff000000000000ffff000000000000ffffffffffff00000000
|0,8=>0xffffffffffffffffffffffff000000000000ffff0000ffff0000ffff0000ffff00000f0f00000f0f00000f0f00000000ffff0f0fffff0f0fffff0f0fffff0000ffff0f0fffff0f0fffff0f0fffff000000000000000000000000000000000000ffffffffffffffffffff0000ffff00000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffff00ff00ffffff00ff00ff00ffffffffff00ff00ffffff00ff00ff00ffffffffff00ff00ffffff0000000000000000000000ffff0000ffff00000000000000000000ffff00000000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff00000000000000000000ffffffffffffffff0000000000000000ffff0000ffff000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ffffffffffffffff000000000000ffffffffffffffff00000000000000000000ffffffffffffffffffff0000ffff0000ffffffff00000000ffff000000000000
|0,9=>0xffff0000ffff0000ffff00000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f00000f0f00000f0f00000ffff0000ffffffffffff0000ffffffffffff0000000000000000000000000000ffff00000000ffff0000ffff000000000000ffff0000ffff0000ffff00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0xb21050d0306010020190201001f08040701001e0f18030601001d190302010b1c0f0306010b091b0306010b0a080201001a191803020100110503060117110506010b160a0503020c0b0f0d15141312110503060c0b0f100306010b090f03060100050e07060c0b050d03060c0b0a0503020100090807060100050403020100
|1=>0x2b1108030b291211190302010022110807060b21220f0d03060b21222f0f0306010b2e050d0306010b2e112c0306010b221105060b2b1f1311080b2914131211190d060b2813200507020c0b120f0d0b272613120f0d0b2524131220050706010b23050d0706010013080d07060100221105030601001d0f0306010b11050306
|2=>0xb1f23080407010b1e230f0d03060100220f390d0b141312190d0201001f13111938010b1f13050d03060b2b371d0f0706010b131119010b361f130f180306010b2311190b2834131209080702010012201907020c0b220f0d02333213121108070c0b1e12110507060b2113110f0b31301312191807020c0b1311050d03060b
|3=>0xd03060b210a070201004013050d03060b2b3f050e07020c0b1205040702010013050e0706010b23050d03020c0b12080407020100220f0d0b3e281312050d0306010b23110f03060b212211050306010b2e0f0d0b313d13121105030b2b3c1211070b313b1312110507060100130f0e07060100220f0d0b3a28131220190201
|4=>0x190e07020c0b22110302010b48220911050306010b111907060b21130a080702010022190d03020c0b221119060b352813110f0306010022190d0b2713471211190201001f13110506010b45130f0d0b3c461312110806010b45222044190702010b1105060b2b4313090f03020100120f0d0142241312200f0701004112050f
|5=>0x1312111903020c0b220a0f0302010022201b0706010b222f0f0306010b2d110706010b4d22080d030b294c1209190302010b231102010b164022201907010b4123054b0d0306010b110503020c0b1211050306010b23110f0b313d13120f100302010b121119010b4a1f13200f07060c0b22190d060b2813490a050702010013
|6=>0xf0306010b23110503060b2b110502010b161211050b3c3213120f0e07060b52220f0d025328131211050306010b2d0f0d03060b5222110802010b16121151050706010b0f0e07060c0b222019070201000f0d03060c0b22190d020c0b1f1311050306010b50050d030b3c3f12090807020c0b121107014f4e13120f0d071529
|7=>0x131211085906010b220f0d0306011722111b0306010b220f0d06010b16220818070201001211190302011722190e070201000f0d0b58571312091b0302010b120f0d020b561312115508070b291220190738010b220f0d0701541312111902010b1622110f03060c0b221105030201171220050738010b121108030201171209
|8=>0x2010b23112f050306010b050f0d030601172f190302010b2e110503060b2b22110f030601172211051b0306010b1d080702010b121105180306010b1107025d4e1312050f0d06010b16110f06010b16220f180302010012110f0b58571312050d0306010b5c1c0f0302010b12110306010b5c2211055906010b130f0d0b5b5a
|9=>0xf0d0b2b1e431312112f190302010b2211050803020b2b1220641902010b1f13190e0702010b230f0d070b3113120f0402010b621312111907010b612213600d0702010b5c130f5f0d020b28131211070201174e13121119070b2b5e13121108180706010b22200f0702010022120a1b0702010b22130f0d0b31301312191803
|10=>0x13110507060b2b2213110f07060117221311051b0706010b1360110702010b40130f0d0338010b22120f0d02015335131208180702010b23120f0d070b215e1312111906010b35130f670d010b24131211080d02010b16120f660d020b32131220190d02010b1f221105180706010b130f0d0702010b22650f0407020b521312
|11=>0x1264190702010b132e080d0302010b2e12110f03010b61221211050738010b13121107020b214013120f4b0d0306010b37050d03010b5e37122011050706010b220f0e0738010b2212080d0702010022122f190702010b132e510f0d02010b68121102010b1a4022130f0d010b1e45131211080738010b2212110f5906010b22
|12=>0x1f131211641907020b2b130a550802010b1a1211080d03020b2b121107010b41401312600f0d0302010b22080d07020c0b1211190d020b28131260110f07010b63130f0d0369010b220f0d0306010b5c2220050702010b23121108010b1e1a13120f0d020b2b461312050f0d070601171320110706010b3b22050d0702010013
|13=>0x2010b2e12050d0302010b2e12112c0302010b2212110f070b63311312110807020b211312190f0d0b282713120f0e0769010b220702010b505c1312080d070b29136a12110506010b43136011080702010b22200702010b3b2312050f0d03010b61122f0f0d0306010b2211510802010b1a120f0d0201531f13121105020b2b
|14=>0x20b21131211190738010b2213110507020b211312111b02010b431312110807010b1e2312110f07010b4a2213200a0702010b402211050d03020b2b120f6b0d020b281312112f050706010b131108010b2a241312110807020b2122126011050702010b130f0d03020b212212110f0701176113120f0d0b2b1e3213122f0f03
|15=>0x20117431312110f070b31131260110702010b5c13200a080702010b22050f0d07010b4a13200f0d07010b4a22111907010b6113120a110702010b4d220f6607020b52131220190702010b22230f0d0b1e292413120f0d0702172113120f0d010b346c1312080d03020b2b3712110f180306010b2260110702010b3b22110f07
|16=>0xd03060b2b220f0d030201002212190e0702010b222e0a0f5902010b22131105010b5e4313121107020b215c1312050d03020b2b37121d0f0702010b1312050f180d0306010b0f0d0701174113121102010b1f6d131220111902010b1f22190d0302010b222e11080407010b1e22190d0706010b5c130f180302010b23120f0d
|17=>0x807020c0b12700d0702010b1312110507020100131211080302010b2e120f0d0b35282713120f0d0b2b5e4313121107010b415c13120f0e070201002212200f0706010b222e6f11080302010b120f6e0d02010b35120f0302010b40222d110807020100221211641902010b35130f0d02010b451312200a050702010b22050f
|18=>0x110f03020b212212111b190706010b131102010b68401312080f0d03020b2112080d03020b2b3f121107010b3674131211050302010b2e1260110702010b7313112f0f0306010b2211720702010b221311050d0306010b22112f1902010b1f130f0d07010b7113120f0407020100130f0d010b5e45131260110f0302010b2211
|19=>0x12050f0d03020b2112050d03020b2b3f12190f0d07060117130f0e0d07060b2b22050e0702010b2312110302010b40220a0f02010b1a13231107010b4a3b13120f0d070b252a13120f0d0b1f2827131260050f0d0302010b050d0302010b2312600f0702010b132e1102010b4540131220190d07010b412211050e0706010b22
|20=>0x2413120f0d020b211f13126011190702010b13110f07011741131211190302010b222e0a0f07020100131105020b2b4313120911080302010b120f0d0701174f1312080d07010b1e762220110f07010b4a22110f070217211312602c0f0702010b130f0d0b2b5e321312110f0d020b7513121108070b2913121107010b417313
|21=>0xb453b13120f0d0201174513120f770d020b2813120f040d03010b5e220911050302010b120f1807020c0b1312110f02010b4513121119020b35281312110503010b1e1220190d07010b4a130f0d070b21611312110f03020100221211080d03010b2a12110502010b451312190d0302010b22230a080d03010b1e120f0d0b29
|22=>0x306010b222e600f0d07010b2a131102010b455c13120f0d030b2b3c2212200f07020c0b22120a080702010b23190f0d07010b4a13200f0706010b222311700702010b13120f0e0407010b5e2220190702010b222d0f0d020b2b4513121108020b2b3213120f0e0d07010b4a220f0d020b28261312190e0702010b2223110201
|23=>0xd0302010b12080d07020c0b22122c0f0d0306010b220911190302010b22050f0d060b2b1f1311050302010b23121107010b416d1312111902010b45221320111907010b41220f0e0706010b222e0f1807020b52131211080403010b1e12084b0d0302010b12200a080302010b121105020b2b32131211510807010b1e120f0d
|24=>0x221311050d06010b1f13110f0701174f13120f180d0306010b37110702010b4d22120f0d0b3c3213120f0d010b633013120a110702010b3b220a0f0d020b2813120f0d010b78621312080f0d030b291211050306010b050d07020c0b13122c0f0e0706010b226008190d0302010b0f0d020b52621312110506010b432213054b
|25=>0x20b2b220f0d010b1e7a13120f0d0b28271312090f0d0306010b22190f0d0b2834131220111907010b4a13110f070b2161131211190302010b22230a110803010b1e120f0d06010b4522132f0f0302010b2d120f0d020b327913120f0d010b611a1312090f070201001312190d5902010b130f0d020b525a13120f0d060b2b43
|26=>0x10b1e13120f0d010b614513120a080702010b222e110f0306010b222e20440f0702010b1211550802010b431209080702010b231211080302010b501211085902010b12110702010b48221311190706010b6d13050d06010b1f1337200f0d070b3113121107010b4a6d1312194b0d0302010b227b11190702010b220f0e0407
|27=>0xd02010b1f22200f0706010b222d0f0d0701171e13120f0e07020c0b22127b0f0d0706010b22600f0702010b50130f0e0706010b2223110807020c0b2212110802010b1612050f0d030b2b3c120f0d03020c0b22120f0d070b2141131211050302010b50120f0d0306010b2223190d02010b1f13230f100702010b1312111b07
|28=>0xf0e07010b782212600f0702010b132d0f0e07020b52221209110f0306010b22050f0d060b2b43130f0d03010b78221211050302010b2d12110803020b2b120f0d03020b522212110f010b611a1312190d020b2813471211195902010b1311080702010b7c120f0d0b3528341312110f010b63301312110507020c0b13120a08
|29=>0x2211190302010b222d200f0407010b4122110f010b61451312050d020b32133f120f0d010b411a131211050d06010b4313080d03010b2a6a1255190d06010b1f1309050f0d0306010b190f0d060b352813090f0302010b23127d190d0706010b1320110f070b311312110503020b2b12080d010b24136a12080d020b32133f12
|30=>0x13120f0d0702175d131211800702010b2211510802010b16120a0f0e02010b1f220f0d0702011713120f4b0d0306010b227b110f0706010b220f0e0706010b50220f0e0d070b3113120f0d020b21571312110f03020c0b2212110f070b214113120f770d010b341312110f0306010b2223117f0802010b7e120f0d0306010b50
|31=>0x20100121108070201171312110f010b411a13120f0d070b251e131211551906010b1f137b111902010b1f13111b0302010b22120f0d03060b2b22190d5902010b221311070201174013120f0d02010b1622120f0d010b3e3513120f0d0b3c3222131211050306010b220a080702010b8112200a0f07010b4122110702010b5c
|32=>0x2010b5c12110f0702175d13120f0d0b2b3c321312090f07020b5213120f0d0702172b13120f0e0407010b4122050f0d0306010b50110f070201171312110302010b5c22121105070201171312111b07020b2b1312110f020b215713120f0d020b6875131211080702011722120f0d030201172212090f07020c0b1312080d07
|33=>0x120f0d0702332b1312112c02010b62131211050d0306010b1108070201001208190d010b1e1f22190d0302010b5c22050f0d03060b2b050f0d0b3c32131260510f0d0702010b050f0d0306010b2d091b0702010b13122c0702010b5c131211070201175c1312110f0306010b222d0f0d020b286c1312111907010b3613050d03
|34=>0xb5c13121151080d0702010b120f0d070b1e2913125108190d0702010b1211640807010b1e131220190d07010b1e13120f0e040702010b22370a110f0d0302010b220f0d07020b211312112c0702010b13126011510f0702010b0f18070201001312050d0306010b371105010b5e1f13121c0f0702010b1312112c07020b5213
|35=>0xb130a110f0e0702010b220f0d02010b831312050d0302010b3712110f0706010b22132d0a0f0702010b13811282080d0702010b1312510f0e0d0702010b1220110702010b4013120f0d800702010b220f040702010b5022130f0d010b2a2413120a190f0e0702010b2208190d02010b1f2211080d07010b1e2212050d070201
|36=>0x12090f0d02010b451312050f0d0706010b132d0f0d010b5e43131211190e0702010b2260110f07010b411312190f0e0d06010b1f13110706010b3b1312080f0d0706010b222d7f0f0d0702010b2213050f0d0306010b22200f0407010b41131211190d0302010b2211050d07010b1e131209110f07010b411312116419030201
|37=>0x1105180702010b13120f0d0702010013120a0f0e02010b1f13120f0d02010b43501312080d07010b1e223712110f0738010b13120f0d8802010b1312110f07010b36131220110f0706010b220f048702010b13121108180702010b221220110f07010b63131220600a0f0702010b1311081b0702010b1312850f0e0702010b13
|38=>0x40d07020b21131211051b0702010b13120f8d0d07010b2a13127d0f0d07010b8b1312080f0d070201171312190d0302010b2237190d02010b1f8a1312050d07010b1e133712200f0702010b2312111906010b1f13190d0702010b5c22130f0e0d0702010b89120f040d02010b1a2213050f0d07060b2b13111902010b351312
|39=>0x2b13120f4b0d0302010b37122011050702010b2212200a0f07010b411312200f0d0702011713120f180d07020b2b131220190d0706010b130a11080d0302010b12110f5902010b2213127b110f07010b36131211800702010b1312110507020b2b221312110f070201172213120f180d0702011713120a050f0d0706010b130f
|40=>0x120f0d0302010b5c2212080f0d03010b2a1211180702010b5c1312200f040702010b220a110f07010b61131211050d0706010b13050f0d07020117131220110702010b3b2212050f0d03010b5e22120f0d010b351f3413120f0d07010b4a1312112c0702010b132d12110802010b4313120f0e0d07010b631312200f0d07020b
|41=>0x2010b22132d0a0f0d02010b1a2213112f080702010b22120f040702010b501312110f0d07010b631312600a0f0d0702010b13110502010b4313120f0d07010b1e8e13122f0f0d0302010b2212110f07020b2113120f0d02010b43132d1260110f07010b4a131220110702010b5c13120f0d07010b61221312080d0702010b23
|42=>0x6010b50130f0d02010b6813120f0d070b291312600f0e040702010b13117f0f0702010b22132008190d0702010b221107010b413b13120f0d020b2b431312050f0d070b2b5e1312112f050702010b13120a0f0d07020b2113120819180d0702010b220f040702010b3b2211510f0e0702010b120f8d0407010b1e13120a0f07
|43=>0x10b120f180702010b132e12110d0702010b5c1312110802010b1a1312110f070201001312190d0702010b5c131220110702010b73131211050d07010b5e13120f0e0d07010b5e2212200a0f0702010b2209110f02010b451312110f180302010b22120f0d02010b7e13120f0d02010b4513120a0f0d07010b411312190f0d07
|44=>0xb1a13120f0d020b2b32131211641902010b1f13118f0302010b1220110f0702011713120a080d0702010b22050f0d03020b2b22122011190706010b13110f0d0306010b22050f0d06010b1f13080f040702010b222d200f0702010b132e1211050807020b2b13120f0e0407010b4113120a0f0702010b501312050f180d0302
|45=>0x120f180d07010b61131211080702010b2312090f0d07010b1e1312050d07010b5e1337120f670d07010b2a13121105190706010b13110f0407010b411312110f07010b4a1312110f0e0706010b220a08190d0706010b132c0f180702010b13120f0d0738010b221312200f0702010b222e12117f0702010b4813120a080d0201
|46=>0x7010b1e13120f040d02010b451312600a110f0702010b13200f0d07010b6113120f0d07020b2b7913122c0f0d07020b52131209510f0d0702010b12190f0d07060b2b13112f0f0302010b221211050d0302010b22120f0d06010b4322130f0e0702010b2312080d0702010b132e12110f07010b612213122c0f0d02010b6213
|47=>0x12050f0d07010b6113120f0702010b5c132e1251190f0d0706010b1311050e0702010b221211080d07020b2b13120f0d0306010b2237600f0d0702010b22130f0e0d0702011713120a110f02010b1a2213080d0702010b222e12510f0d02010b1a13120f0d0769010b2213190f180d0302010b220a0f0702010b132d12600f0d
|48=>0x70201171312110e0702010b5c131255190d0706010b1320110702010b6d1312050f0d010b5e1f13120f0e0d07020b2b2212110f02010b6813120f0d0702010b132e120f0d07020b212213126011190702010b132f0f0702010b132e12050d0702010b132e12112c0702010b22131208190d010b1e1f13120a110f07020b2113
|49=>0x13120f0d010b5e432213120f0d02010b356c1312080d07020b2b1337120a1102010b1a401312200f0d07010b2a131211900d0706010b130a0f0d02010b68131211051907010b5e1312190f0d0702010b73130a08040d0702010b22110f02010b4513120a110f07010b41131211080d0306010b1211050d07020b2b1312110f0d
|50=>0xa190f0e0706010b1308190d06010b1f130f0d07020100221312050d07020b2b1337120a110802010b1a1312510f040d0702010b22190d0706010b13370a11080702010b220f0d010b1f3413120f0d070b2a1e2913120f180702010b13231205080f0d03020b2b120a0f0d0302010b22110f0d02010b161312190f0d070b2b5e
|51=>0xb222e1220110f07010b6113120f0e0702010b132e120911510f0702010b12116405190702010b131105080d0302010b1211080702010b132e12110702010b4d1312090f0d0702010b131211190d07010b5e13122011190d0702010b226f11080702010b13120f0702010b4022132d200f0702010b222312190d0702010b8a22
|52=>0x12050f0d06010b431311050702010b132e1260080f0d0702010b22080d0702010b222312090f0d07010b5e1312050f0d020b2b1f13120f0e0702010b222e1260110f0702010b2213600f180d0702010b1311080702010b222e1211190e0706010b130a550f02010b1a13120f0d07020c0b1312110702010b7c13120f0d030201
|53=>0x6010b1360050f0d0702010b13050d0702010b1323127b11190702010b13110502010b4322131220190d02010b1f1312110f0702010b132e12110f07020b212213120f180d07020b2113120a510f0d0702010b222c0f0d0302010b2212080f0d07020b211312080d07020b2b133f122c0f0e0702010b1312090d0702010b5c13
|54=>0xb220f180d07010b411312200f0d02010b431312110702010b4022130f0702010b7c1391120f0d02010b62131205080d0302010b371209110702010b401312080f0d010b2a24131211050302010b120f180d02010b4313122c0f0e0702010b2212190d07010b5e1337120a0f040d0302010b220f0d07010b1e50131211551907
|55=>0xf0d0302010b22120a55080702010b120f0d0369010b13120f180702010b5013120911080702010b1312110f0d07010b611312190f0d07010b61131220110706010b3b1312110702010b9213120f0d020b2b43221312050f0d07020b2113120f180d0302010b37120f0d07020b521312050d07020b2b133f120a0f0e04070201
|56=>0xb2a2913120f040d07010b5e221311190702010b6d13120f0d0793010b1e1312112c0d0702010b13120911050702010b131211190302010b22110507010b1e1312050f0d010b5e431312110f0702010022131211080d07010b2a13120911080702010b22120f0d02010b1f6d1312110807010b1e2212080f040d07010b1e2209
|57=>0x12200f0d07010b4a13120f0d0302010b22231260110702010b3b1312090f0d07020b2b1312110f07020c0b1312110f0302010b222e120f0d020b2b322213120f0d070b2b1e13120a08040d0302010b12090f0d070201171312200a0702010b4013120f6e0d02010b1f131209110f0702010b13120a51080d0702010b120f0d07
|58=>0xb13120f0d07020b52132d12084b0d0702010b221211050702010b13231220111902010b1f1312050f0e0d0706010b220f0d02010b62132d1211080407010b1e13120f0e0702010b2223120a11510f0702010b2209110702010b5c1312084b0d0702010b1312200a080702010b131211080702010b22231211510702010b4d13
|59=>0x120a1151080702010b12190f0d020b3528131260190f0d0702010b132f0f0702010b132d12111b0702010b131209110f0302010b2212190e0d0702010b2237200f0d02010b45131209080f0d0302010b120f0702010b5c132d1211190d06010b1f13080f0d070b291312110702010b4813120f0d0302010b4022054b0d070201
|60=>0x10b4a13120f6b0d02010b1f1312110f0302010b2223120f0d0302010b502212092c0f0702010b131211080702010b501312080f0d020b2b3213120f0d5902010b131209110f0702011713120f0d0702011713120a510f0e0702010b12110f0d07020b21131255190d02010b1f131209050f0d0302010b12090f0702010b132e
|61=>0x4a131211080d02010b1a1312110f4b0702010b13120f0d07020b2b5013120a0d0702010b5c1312200a0f0d0702010b22110f0702010b5013120f0e0706010b222d110f0306010b220f0d07020c0b22131211050702010b5013120f4b0d0302010b2212050f0d020b2b3213120f0d0306010b222d110702010b5c131220110f07
|62=>0x10b12110507020b2b1312110f0702011713120f0d07020b2b132d12112c0702010b132e120f0d03020b2b221211050702010b132d12110807020b2b13120f0d07020b52221312050f0e040702010b220f0d02010b6222131211080702010b222d1211050302010b22120a550702010b401312050f0d0306010b0f0e0d07010b
|63=>0x510f0d02010b1613120f0d010b5e1f1312112f080702010b12200f0d07010b1e2212200a110f0702010b2208190d0702010b222d050f0d0302010b5012110f07020c0b2213127f0f0d02010b7e13120f0e0d0706010b2237080d07010b2a136a12190f0d0706010b6d130f0e0d02010b451312090f0702010b13231211080306
|64=>0x22120f180d0306010b2209110f07020b2113120f0d07020b211312112c0702010b1312110702010b5c221312090f0702010b132d120f0d0306010b370f0d07020117221312111b0702010b221312090f0702010b501312090f0d07010b41131208190d0306010b0f0306010b9422090f0d07020b2113120f660d07020b2b1312
|65=>0x10b1312050f0d0702010b5013122f0f0d0702010b13120f0d0702010b961312950f0d0702010b13120f0d0302010b3712600f0e0d0702010b13120f0d07010b4113120f0d0702010b5c13120f0d02010b4313120f0e0702010b401312050f0d07010b5e1312090f0e0d0702010b131264080d0702010b13120f0d0702010b3b
|66=>0xb1f131208190d0706010b13110f180702010b1312080f0d0702010b222d12050f0d0302010b22120f040702010b22132d1105080702010b13120f0706010b942213110f0702010b22132d1260110f0d0702010b1312820f0d0702010b13120f180d0302010b221209110f0d0702010b13120f0d07010b97131209190f0d0702
|67=>0x12050f0d07020b2b131220110f0d07010b411312200a0f0d0702010b1312110f0306010b13120f040d0702010b5c13120f0e0d0706010b2220110f0702010b22120a0f180d0702010b131220110702010b3b1312050f0d0702010b132d12080f0d07020b2b13120f0d0702010b731312200f0e0d07010b411312190f0e0d0201
|68=>0x10b131211050d0702010b13127f0f0d0702010b1312080f0d0702010b4d1312110f07010b41131211080d0702010b2212200f0e040702010b1312640f0e0702010b13120f900d0706010b131164080702010b131220190d0702010b13120a050f0d0702010b1312640f0d0302010b1312111902010b1f1312080f0d0306010b
|69=>0x13080d0702010b2237120f040702010b132d120f040d02010b1a13120f0d0702010b6d1312190f0d07010b5e13120a190f0d0702010b22130f0d0702010b9813120f040d0702010b22133720080f0d0302010b12080d0702010b13371220110f040702010b1312110f18040702010b13120f180e0702010b132d12112f0f0702
|70=>0xf0e0702010b22120a08190d0702010b13120f0e0d0702010b8613120f0306010b9413122011190702010b1312110f0d0302010b2212050f0d02010b1f13120a0f0d02010b1a131211640f0302010b1312200a110f0702010b1312190f0d0702010b501312050d0702010b13371205080f0d0302010b120a110f0d0702010b22
|71=>0x702010b22131251190f0d0702010b13120f0d0302010b2237122c0f0d0702010b13120f0d0702010b5c221312080f0d07010b2a13120f0d02010b43221312050f0d07010b5e22131211190d0706010b130f4b0d0702010b1337120f0d0702010b132e120f0e040702010b220a11080d0702010b1312117f0f0702010b131211
|72=>0xf0d0302010b131211080302010b12050f180d0702010b1312600f0d0702010b13120a110f02010b1a13120f0d0769010b1312080f180d0702010b2212090f0d0702010b1312110f180702010b221312190f0e0d0702010b2211900d0702010b13120f0d0706010b3b1312190f0d02010b1f2213200f0d0706010b13122f0f0d
|73=>0xe0702010b13120f180d0702010b5c13120f0d0702010b1323122c0f0d0702010b132d1211190d0302010b1312110f8c0702010b13120f0e0d02010b1f1312110f0702010b132e12118f0702010b13120f0d800702010b1312050f0d07020b2b2213120a190f0e0702010b131208190d02010b1f1312190f0d06010b1f130a11
|74=>0x702010b4013120f0d0702010b5013120f0d0306010b220f0d02010b351f131205080f0d07020b2b13120a0f0d0702010b2213090a0f0d0702010b13120f180702010b132d1260110f0702010b1312200f040702010b131209110f0702010b131220110f0706010b1312112f0f0702010b22131211050d0702010b2213121119
|75=>0x702010b13371211050702010b1312110f0d0306010b131211080702010b22122c0f0d0702010b2213120f0d0702010b8a2212050f0e0d0702010b22120f0d0702010b22132e12200f0e0d0702010b22120f4b0d0702010b1312200a0f0702010b13121105080d0702010b13120f8d0d07010b1e1312110f0702010b13231211
|76=>0x22132312190f0e0d0706010b130f0d0302010b222d12110f0702010b22132e120a08040d0702010b131208190d0702010b22090f0d0702010b221312090a110f0702010b1312110f0d07010b4113120f0d07020b2b131205190f0d07010b5e13120f180d0702010b13371211190d02010b1f1312110f0e0706010b131205080d
|77=>0x502213120a0f040d0302010b131209050f0d0702010b1312190f0d0302010b220a510f0d0702010b1312200f0d07010b1e131209110f0702010b221312090f180d0702010b13120a550f0702010b1312190d0702010b8a1312050f0d0302010b12110f0702010b132d120f0d02010b351312110f0302010b22120f0d0702010b
|78=>0x1312640f0d0702010b1312190f0d0702010b22130f18040d0702010b1312080f040d0702010b1312110f0706010b13120a11510f0702010b13120f0d07020b2b221312110f0d0702010b132e1211050702010b2213121164190702010b1311190302010b13120f4b0d0702010b221312110f0702010b221323120f0d0702010b
|79=>0x10b221312110f0e0702010b1312110f0d0302010b1312190f0d0302010b13120f180d0702010b2213120f0d0702010b1337120f0706010b9413120f900d0702010b131211640f0702010b13120f0e0d0702010b221211080d0702010b131208190d0702010b1312190f0d0706010b130f0702010b9422131220110f0702010b
|80=>0x132d120f0d0302010b221211080702010b13120f0d0702010b8a1312200f0e0d0702010b13120f0d0702010b221337120f0e0d0706010b1312110f0d0702010b221312190f0d02010b1f131205080f0d0702010b13120f0d07010b1e13120a110f0d0702010b13120a190f0d0702010b13120f8c0d0702010b1312050f0d0702
|81=>0x702010b221312110f0702010b13120f0d0302010b1312110f0d0702010b1312190f0d0702010b13120f0e0d0702010b13120f0d0306010b1312050f0d0702010b1312110f0702010b2213120f180d0702010b13120f0d0702010b22132d120f0d0702010b4013120f0e040702010b13120a0f0d0702010b13120f0d0702010b
|82=>0xf0d0702010b13120f0702010b9413120f0d
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2298084601f98078601c9806c60199806060169805460139804860109803c600d98030600a9802460079801860049800c6001980006
|6,0=>0x921c241708e9c233708b1c22570879c21770841c20970809c1fb707d1c1ed70799c1df70761c1d170729c1c3706f1c1b5706b9c1a770681c19970649c18b70611c17d705d9c16f705a1c16170569c15370531c145704f9c137704c1c12970489c11b70451c10d70419c0ff703e580f2703adc0e470375c0d67033dc0c870305c0ba702cdc0ac70295c09e7025dc0907
|6,1=>0x1015c3fe70fddc3f070fa5c3e270f6dc3d470f3983c770f01c3b970ec9c3ab70e91c39d70e59c38f70e21c38170de9c37460db5c36670d7dc35870d45c34a70d0dc33c70cd5c32f60ca1c32170c69c31370c31c30570bf9c2f770bc1c2e970b89c2db70b51c2cd70b19c2bf70ae1c2b170aa9c2a370a71c29570a39c28770a01c279709c9c26b70991c25d70959c24f7
|6,2=>0x120dc47c711d5c46e7119dc46071165c4527112dc444710f5c436710bdc42871085c41a7104dc40c7
|7,0=>0x19f60675819b6066581976065581939c646818fa0637718be06278187e06178183e0607817fe05f7817be05e78177e05d78173e05c7816fe05b7816be05a78167e05978163e0587815fe0577815be05678157e05578153e0547814fe0538714c205288148205188144205088140204f8813c204e88138204d971349c4ca8130a04ba812ca04aa8128a049a8124a048a8
|7,1=>0x21ea0872821aa08628216a08528212a0842820ea0832820aa08228206a08128202a080281fea07f371fae07e381f6e07d381f2e07c381eee07b381eae07a381e6e079381e2e078381dee077381dae076381d6e075381d2e074381cee073381cae072381c6e071381c2e070381bee06f381bae06e381b6e06d381b31c6c481af206b571ab606a581a76069581a3606858
|7,2=>0x29d60a6d829960a5d82959ca4e8291a0a3e828da0a2e8289a0a1e8285a0a0e8281dc9ff827de09ef8279e09df8275e09d07272209c0826e209b0826a209a0826620990826220980825e20970825a20960825620950825220940824e20930824a20920824620911724260901823e9c8f2823aa08e28236a08d28232a08c2822ea08b2822aa08a28226a08928222a08828
|7,3=>0x31ba0c668317a0c577313e0c47830fe0c37830c1cc2a6308a0c1a8304a0c0a8300a0bfa82fca0bea82f8a0bda82f4a0bca82f0a0bba82eca0baa82e8a0b9a82e4a0b8a82e0a0b7a82dca0b6a82d8a0b5a82d4dcb4b82d0e0b3b82cce0b2b82c8e0b1b82c4e0b0b82c0e0afb82bce0aeb82b8e0adb82b4e0acb82b0e0abc72ad20aac82a920a9c82a520a8c82a120a7d7
|7,4=>0x39a20e60839620e50839220e41738e60e31838a60e227386a0e128382a0e02837ea0df2837aa0de28376a0dd28372a0dc2836edcdb3836ae0da38366e0d938362e0d83835ee0d73835ae0d638356e0d538352e0d43834f1cd34834b20d24834720d14834320d04833f20cf4833b5cce5833760cd5833360cc5832f60cb5832b60ca5832760c9583239cc86831fa0c768
|7,5=>0x418e105b8414e104b8410e103b840ce102b8408e101b8404e100b8400e0ffc73fd20fec83f920fdc83f520fcc83f15cfbd83ed60fad83e960f9d83e59cf8e83e1a0f7e83dda0f6f73d9e0f5f83d5e0f4f83d1e0f3f83cde0f2f83c9e0f1f83c5e0f0f83c1e0eff83bde0eef83b9e0edf83b5e0ecf83b1e0ebf83ade0eaf83a9e0e9f83a5e0e9073a220e80839e20e708
|7,6=>0x1136844ba11268447a11177443e1107843fe10f7843be10e874385d0d98434610ca7430a10ba842ca10aa8428a109a8424a108a8420dd07b841ce106b8
|8,0=>0x4d76535494d32134394cea533284cadd32294c66531094c22130084bde52ef84b9a52dd94b5252cc84b1212bc84ad212ac84a8e529a94a465288949fe5276949b652658497612549492e5243848ea5231948a6122094862120f9481a51fe847d651ed8479611dc9474e51ca9470651b8946c211a79467e11969463a1185945f25173945ae11629456651509451e513e9
|8,1=>0x56361584955ee5573855b1d5639556a5551955261541854e2552f9549a551d95456150c9540e54fa953c654e89537e54d69533654c5852f254b3952ae14a29526654909521e547f851da546e85196545d85152544c8510e543a950c654289508214179503e140694ff653f494fae53e294f6653d094f2213bf94eda53ad94e96139c94e4e538a94e06537894dbe53669
|8,2=>0x5ee257af95e9a579d95e56178c95e0e577a95dc6576895d7e575695d36574495cf2173395caa572285c6a171195c2256ff95bda56ee85b9656dc95b4e56cb85b0a56ba85aca16a995a82569795a3a5685959f25674859b216657597256548592e5643858ee1633858aa562195862560f9581a55fd957d255eb9578e15db8574a55c99570255b7956be15a69567655958
|8,3=>0x67aa59e19676259cf9671a59be866d659ac9668e599a966465988966021977965be19669657659549652e5943864ee1933864aa59219646259108641e58fe963d658ec9638e58da9634658c98630258b7962ba58a5962761894962321883961ea5871961a618609615e584e9611a183d960d2582c8608e581a96046580895ffe57f695fb657e495f6e57d295f2a17c19
|8,4=>0x706e5c129702a1c0196fe25bf086fa21bdf96f5a5bcd96f125bbb96ece1baa96e865b9896e421b8796dfa5b7596db25b6486d6e5b5386d2a5b4196ce25b3176ca25b1f96c5a5b0d96c125afc86bce5aea96b8a1ad996b425ac796afa5ab596ab25aa396a6a5a9196a225a7f969de1a6e969965a5c9694e5a4a969065a38968be5a269687a1a15968361a05867f259f39
|8,5=>0x793a5e45978f61e34978b21e239786a5e11978225dff977da5ded977925ddb9774e1dca977065db8976be5da69767a1d968763a1d86875f65d74975ae5d62975665d509751e5d3e974d65d2c9748e5d1a974465d08973fe5cf6973b65ce49736e5cd38732a5cc1972e61cb09729e5c9e972565c8c9720e5c7b871ca5c69971825c579713a5c47770fe1c36970b65c249
|8,6=>0x81da206d98196205d88152604b98111e03b980ca602998082601978049e009980025ff797fbe1fe787f7a5fd597f325fc397eea5fb197ea25f9f97e5a5f8d97e125f7d77dd61f6d87d925f5b97d4e1f4a97d0a1f3997cc25f2797c7a5f1687c365f0677bf65ef497bae5ee297b665ed097b1e5ebf87ae1deaf97a9a5e9d97a525e8c87a121e7b979ca5e69979825e579
|9,0=>0x8afe62b5a8ab262a398a66a28fa8a16a27c989ce626a98982a2588893e6245a88f26234888ae622298862a20f9881e21ff887da61eca878aa1da88742a1c8886fe61b5a86b261a2a866661909861aa17ca85d2216b98586a1589853e6146984fa2134a84aaa12198462610ea841a20fca83caa0e99838260d79833e20c5a82f620b4982b220a39826a6090a821e607e9
|9,1=>0x9432a502a93e664efa939a64dca934e64ca9930664b8992c224a799276a493a922a6482891e2a4717919ea45e99156644d8910ea43a990c2a4279907a641599032640398fe6a3efa8f9a63dd98f4ea3ca98f0663b7a8ebe23a5a8e72639488e2aa38198de2636ea8d92a35c88d4e634a98d06633898cbe6325a8c6ea31298c2662ffa8bda62ed98b9262db98b4a62c8a
|9,2=>0x9d1aa73d99ccea72a99c8a271a89c42a706a9bf2a6f2a9ba2a6e089b5aa6cd99b0ea6b9a9ac266a799a7e269699a3a2686899f2a673999aa6660a995aa64e89912a63aa98c666298987ea615a98326603997e6a5f1897a265e08975aa5cd9970ea5b9a96bea5a6996766593a962a6581995e62570995a5e5609955aa54d9950ea53a994c665289947e65169
|10,0=>0xa31a28bd9a2d268ab9a286a8989a23e68869a1f668758a1b628649a16aa850aa11e683daa0d2682aaa08a2818aa03aa80599feea7f299fa667e099f5aa7cd99f1627bc99ece67aa99e86679899e42278799dfa677599db26762a9d62a7508
|11,0=>0x29028a3e668f18a3a628e09a35e68ce9
|12,0=>0x290a8
|_,_=>0
def wAt:=mkWire dB 153 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 2000006 zs)
def oP:Nat→Nat
|0=>0xf1341c4d0135808490f0d47c4d1907c3c490f28808a2013587c4d1907c3c49112241407021241c4d0f2b814070f224484d02124448807134484d0713408ae0501c3c890f0d44c4911220084907134484d01358641f0f1344488112243c351213404aa071343c351e124200b0f1340849071343cb51213414070f0d41ca6012a878490802c3c4d0f2244488021243c35
|1=>0xf2243c3507134644d0f12408490f22408490d2241c4d121344488021241c4d110503c890f0d4484d0b234344d0f12444880f0d44c491122008490501c20490f0d43c4d0713408ae072b81407111342c8d0f12444880f0d44c490501c44890f134048d112203c35121343ca6012a878490802c3c4d071343c89021244488071343c351213404d60f0d41435081240849
|2=>0xf0d40849071343c8a121343c89111343c35112203c4d0b234448812134448811220140711050644d0f0d43c49021244488021243c351f134641f0f12420350f134641f0f2243489021244c490501c20490f0d43c4d07134344d0f12444880f0d44c490163904492002c20350f13434a1013587c4d1907c3c490501c3c4d0d224084913124444d0b2344488121344414
|3=>0xf2a804aa1e124200b0f134141f191343c350f124084911220803f0f0d4240b050d43c891213408491122c1c4d121343c4d0a13c44490f0d414070f134048d112203c351213404d60f0d47c4d1907c3c49131241c4d024043c120d1243c62021241c4d1213444880f2243c350802c242f050d43c8913124803f111343c350f2242c8d112203c35112243c89022344488
|4=>0xf134244b050d43c891312420350f1341435510fc44490f0d435492c01c3cb50d2284c49112203c490f0d4140702124348907134484d0802c44880f0d4444d0a0fc44490f0d404d60d3547c4d1907c3c49072a83c351e124200b0f134200b072b820490f1341c4d0f2d4348a12134058e41124800b111343c350228804d61f134641f0f124484d02404344d0f0483449
|5=>0x112203c35121343c890b23444880f0d444160f0d43c4d0713408a2013587c4d1907c3c490d1342c8d11220484d0713590211112c3c350f134484d0f2244449111343c35021241c4d0501c3c8912134484d11220140b0507c14072f2e4448a1122c3c35021243c890d2241c4d12134444d0f0d4641f0d124448807134484d0163904492002c444d0f0d464350f1242035
|6=>0x901c14350f224484d071343cae0501c3c8912134242f0a13464350f0d4484d071343c120d124281f112203c350d2a478490802c3c4d022887c4d1907c3c49112201c4d12134800b080d43c4d0f224084913124644d0f12408490901c8049080d41c4d0f2b81407081243c4d1122c4c49021241c4d112203c89021241c4d1213434490b23444880f0d44c49012343c4d
|7=>0x72b81407081243c4d013587c4d1907c3c491105420490f0d43c4d0713404d60f0d47c4d1907c3c4908124200b0f0d43c4d0713420350f1344489112203c3507134484d190d43c490802c04aa072a878490802c3c4d0b2344449112203c351312414070804434490f0d43c4d07134444d0f0d4140b072b83c891213405a21a134281f1112404aa0f0d478490802c3c4d
|8=>0xd228804b0123444880f134484d0f2d4084907134348a121344489131241c4d0f0d43c491907c1407191343c490f2244488071343c351213444892002c444d0f0d43c11071343449080d43c4d072b814070f2243c35121340849112281c4d121341c4d022b814070f2244c49111243c4d112203c3512135800b0a13464351122008490f0d4140b0f2243449121343c35
|9=>0xf1243c6102124348907134484d0235804d61f134641f0f125800b2012c444d0f0d41c4d112203c490f0d44c490713444490f0d4200b0f13434890b2344488112243c35131243c490723444880f0d4484d0501c08490f2281c4d1213408ae072b814070f224484d1213444490f0d43c3a012a878490802c3c4d071340849081243c350f1341c4d0123444880f2243c35
|10=>0xf224048d112203c351907c64350f124bc4d1122c3c35112203c35021244c49121343c4d5107c284f111243c350713408ae0501c3c89131240849112203c3507134484d1907c44880f0d4484d1122444880f1343c351213420490f1341c4d072343c4d112203c35121348067111343c350f12408492f134448b0f0d44c490501c3c890d124484d0228804d61f134641f
|11=>0x50d42049021243c4d071340849013587c4d1907c3c49190e8344d0163904492002c3c350501c20490f0d43c4d071341caa0f2a878490802c3c4d0f2b81cae0501c20490f134348a112243c351312408490713414070507c3c8912134348a0501c20490f0d43c4d071343ca2013587c4d1907c3c49072343c49112203c3513125344d080483449013587c4d1907c3c49
|12=>0xf2244c49021241c4d1122008ae072b814070f2243c890f0d44c49021241c4d11124800b111343c35131243c35190e0344d0f124641f190d43c49021243c8a07134484d2f134448b0f0d4058e41124800b0f0e40849112201c4d0f0d4484d021243c8907134484d2002c20350f1341cae0f2b814070f224484d071343caa1e124200b0f134444f0f0d4641f0f1240849
|13=>0xf1341c4d022b81cae0501c3c89121341c4d021243c890d2284c490f2344488112243c3513124084907134348a121343c497b02d904d1112c3c352c0d4b0070f2d4348a131244c490d124800b0f0e42049021243c4d0713405a21a134281f190d43c4911224048d112203c35131243c4d0b23444880f0d4484d1907c3c350f12408490713444140f2243c35121341407
|14=>0x121344c490f134641f0f1243c350802c3c4d0f1883c890d2244c49111243c35012a878490802c3c4d0a13c64350f124200b1112c3c350f13420350802c3c4d0d1343c8a0d1244c490713444490f0d44c490d2242c8d112203c35050fc2049021243c4d07134140b1907c3c350812408490f1341c4d0b2343c4d112203c3512134200b13124641f0f1241407081240849
|15=>0x7134800b080d43c4d131243c350f1241c4d08124200b0f13480492002c444d0f0d41c4d1112c3c350f124344d111243c3513126081f0f844104f0d1243c890f2281c4d1213408490f0d4348a1312429571113c3c350f4d420120d1243c4d0913c80490f0e4344d111343c350f04834491312464380d1343c49050dc3c89131241caa1e124200b0f13464350f124344d
|16=>0x111343c35121341ced0d1243c3a0d1343c4d0d224484d41124800b111343c352012c444d0f0d44414081243c350f1343619190ec344d0f124241f2012420350f13408490f224348a13124141f0502c3c89131243c350f124344d12134800b2012c444d0f0d4344d1907c3c490212408490f0d43c3a0d1343c4d02124348a13124bc491122c3c35131243c89131240849
|17=>0x80d43c4d0f1243c8a07134484d1907c143f08124200b0f134444d112203c3512134641f0f0d43c49021243c620d2244c4986134643b0d1343c490a07c3c110d1244c490501c644d0f12408490f0d47c4d1907c3c490d2243c89131242c8d112203c3513124641f190d43c490802c3c8a12134088d112203c35131241db5190e8344d0f125ec0b64134444b0f0d40849
|18=>0x80d43c4d071343c8a121343c89111343c3511124800b111343c35090bc8049080d43c4d021243c49080d43c4d111243c350f1341c4d0723444880f0d4484d7b02d904d1112c3c350f0d464380d1343c490f0d414070f2244c49090bc44890f0d44c4902124644d190d43c490901c284d0f04444140f2243c351312434791e124200b0f1343e310e12c344d090bc8049
|19=>0x90fc8049111343c350902c3c610d2243c4d112203c35121343c620d2241c4d1213478490802c3c4d0713434891312434491213420350f134240b0a13444490f0d420490f0d43c4d02124242f050d43c8913124803f111343c35121341c4d0502c3c891312408d61f134641f0f125800b2012c20350f134348a131243c350507c20490f13504492002c3c390501c2049
|20=>0x1213414070502c3c89131243c891122c3c351312424070a13464350f1243c490f134348912134484d0d1243c3a0d134344d0a13c44490f0d434790d124200b0f1343c350d228281f190d43c491213424370a1343c110d12504492002c444d11124804b111343c350f0d4141f0f224484d1e124200b0f134448b07134484d0901c44890f0d44c496002c804b111343c35
|21=>0xf124ec49200fc444d0f0d4140b0f2244c490d134140b0f2244c4911124444d0f0d4484d0907c44890f0d4484d0d2241c4d12135fc1f55124444f0f0d4241f2012420350f13444492002c444d0f0d40849191343c491a134281f190d43c49012a878490802c3c4d2012c3c390d134bc491122c3c35131243c491213420350f134803f2002c444d0f0d414070507c3c89
|22=>0x90bc8049111343c350f1344c49190d43c490713414070f224484d111343c350f1240849021243c3507134484d19134641f0f12408490d2283c4d0911c8049111343c350f0d41407081243c4d0d124800b0f0e4344d190d41437191343c490f224348907134484d11188348913124243f112243c35131243c4d0a07c44490f0d42c8d112203c3513124243f0a1346435
|23=>0x121343c4d112203c3512134200b2012420350f1343c8a0502c3c891312434a91e124200b0f134644d0f0d43c490212434492002c444d0f0d5800b2012c444d0f0d4344d0f0d408491312408490f13464350f1243cb513124088d112203c35112283c3512135fc3f55124444f0f0d4281f190d43c49072b814070f224484d1907c444b0f0d43c490812c3c350f1341c4d
|24=>0xf04834490f124348907134484d180dc104d0d124804b080d4200b0f134241f0a1343c1111124804b111343c352012420350f13414070f2244c492c01c3cb50d2284c490a134284f190d43c490501c644d0f12408491122c1c4d121341c4d0f2243c351213408490507c3c8912134344d112203c35121343d42050dc20490f134240b112243c3513124b01f0f2d4348a
|25=>0xf18434890f124804b111343c3511228448b0f0d4448a0f2244c490f2d43c350d2284c490802c3c4d1907c3c490901c284d111243c350902c14350f2244c490f1884c490a13c64350f12408490d1343c890f0d4484d0501c3c35081243c4d021243c8a07134484d0912c3c610d2244c49090bc80490f0e4281f111243c35112283c3512134284f190d43c49131240901
|26=>0x80d478490802c3c4d1913c3c350f12408491a134281f190d43c490f0d4140b191343c496d124643a0d1343c490f1343c110d124241f112243c351213444492002c444d0f0d41c4d0f0d43c4d0212414070f2244c49090bc44891312438490d13408491113c3c350f125803f2012c444d0f0d4641f0502c644d0f124344d0501c3c8912134684d0a07c44490f0d42407
|27=>0xb23444880f0d44c490f22814070f2244c490f134281f111243c350a13c3c110d1240849050fc644d0f1243c4d111243c351312408d61f134641f0f12404aa1e124200b0f13444880f0d43489131241407081243c4d071341c4d1312464350f125441f0a13c44490501c140b191343c490507c140b0f2247c4d1907c3c49050fc1407081243c4d0a0fc281f111243c35
|28=>0xf0d41c4d12134240b20124444d0f0d444620e124344d0f0d4244f112243c3512134644d1112c3c350f12420490f0d43c4d071344416081243c350f135443f0a13c44490f0d444b9112283c35131243c350502c644d0f124444d0f0d4484d64084444b0f0d43c4d0f048348a11220444d0f0d4484d0f1244c49080dc3c4d02124344d190d43c49021243c4d1907c3c49
|29=>0x901c8049080d43c4d0f2b81407081243c4d0f2d438490f1843c620d2244c4902124141f0f224484d13124804b080d43c4d112203c4d0f0d4484d050d4140b0f2244c490501c644d1907c3c49112283c3512134244b112243c3513124804b0e1243c390d134448a0f0d4484d0d1343c350f12408490a07c444f0f0d4048d112203c3513125004d0f0d43c120d124448a
|30=>0xf048b01f0f2d4348a12134143f081243c4d07134283f0a13444490f0d41caa1e124200b0f13420490f0d43c4d07134348a050fc140b191343c49071343c110d1244c491113c3c350f12408490912c14350f2244c49112203c890f0d44c4964134444b0f0d43c490f0d4141f0f224484d080d43c4d1907c2407112243c3513124284f190d43c49071343cb50d228484d
|31=>0x7134484d0f134444f111243c350713409010f0483449050dc3c890d2244c49050d43c35081243c4d0902c448913124240b0a13464350f1240849200fc444d0f0d4463f0812c3c350f134141f0501c3c890901c14350f2244c490f2281c4d12134b0070f2d4348a131243cae0501c3c8913124344d0f04434491312420350507c20490f1344c490f0d43c120d125004d
|32=>0x11124444d0f0d5dc4f1907c3c49112d43c350d2284c490a13c64350f12404aa1e124200b0f13434490502c3c89131243c35190e8344d0f1243cb9112283c35131243c89112243c35131244c49071343c350f12420490f0d4200b0f134141f0502c3c89131242c8d112203c35131243c351e124200b0f1343c4d112243c3512134200b0f1343c351213434490f1843489
|33=>0xf22408491312434490d13444880f0d4484d0a13c44490f0d4243f112243c35131243c110d12420350f13444880f1343c3512135443f0a13c44490f0d420350f13444880f0d41c4d12134803f2012c444d0f0d41407050d43c8913124048d112203c3513124448a0f0d41cae0501c3c8912134140708124200b0f1341c4d0f1343c110d124242f0a13464350f124283f
|34=>0x112243c35131243c4d0a13c44490f0d404d61f134641f0f124244b0a13464350f124448b0f0d4348a0f23444880f0d44c490713444890f0d4484d0f228344d0907c8049080d43c4d071348049080d43c4d0f1884c490f0d4641f0f1240849012a878490802c3c4d7f0fd54491113c3c35121341c4d0f04834490f22844880f2243c3513124444d0f0d4641f0f124344d
|35=>0x501c3c8912134084907134348a12134243f112243c3513125800b2012c444d0f0d434d51f134641f0f1244488071343c351213414370f2241c4d12134b0350f2d4348a1312420490f1341cae0501c20490f1341c8d112203c3512134242f112243c3513124242f0a13464350f124284f190d43c490901c448913124641f1113c3c350f1241c4d050d43c8912134448a
|36=>0xf22434490d134484d2c07c3cb50d2283c4d0f0d4348a121343c350f2241c4d12134283f1113c3c350812408490f1341c4d6002c804b0f0e43c4d0a07c44490f0d434b9112283c35131243c62041343c110d124444d111243c35131242437112243c3513124344d02124348a131243c3513124084907134048d112203c35131243c891312434dd0f2281c4d121341cae
|37=>0x12134348a131243c4d0f1241c4d050dc3c8912134048d112203c351312554491113c3c35021243c8a0d134484d0f2a878490802c3c4d02124643a0d1343c490907c80490f0e44488112243c351312408490f0d43c4d0713414070f2243c3513124242f112243c35131243cb9112283c35131241c4d0501c3c89121344c490f0d41407081243c4d2c01c3cb50d2284c49
|38=>0xf2d43c350d2284c49090fc44890f0d44c49112243c350d2284c490f2284c49021241c4d090bc3c610d22444140f2243c35131243541050dc3c891312480492002c20350f1343c49021243c4d071341c4d0f0d808491312424070a13464350f12434ad0501c3c8913124284f190d43c491907c140b191343c490f134448b0f0d4484d0802c20350f1344449111343c35
|39=>0x1213444890f0d44c490806c3c4d02124284d190d43c49050dc3c8913124448b0f0d44c498a12420370f1363c350812c3c4d0f2281c4d12134804b0f0e4344d2002c20350f1343c620d2244c490507c3c8912134344d0f04834490502c3c891312480490f0e4344d1112c3c350f134484d0f0e8344d02124348907134484d0901c44890f0d44c490901c284d190d43c49
|40=>0x21241c4d0f188104d0d12408490d134484d111343c3512134104d0f0443449200fc444d0f0d43c890d2284c490501c20490f134ec490f0e8344d2002c3c390d134344d1907c3c490f1343c49021243c350d2244c490f134348a121343c8907134484d0d22834491312420490f0d43c4d0f0d80849131243c350d2284c492012c444d0f0d43e110413c34490d2241c4d
|41=>0xd124444d0f0d4104d0d1243c35180dc38490d134448b0f0d44c490f2243c351312554491113c3c350804834490f134800b111343c350f1343c35121343c390d13434491112c344d0f0d4644f0f12408491112c3c350f1343c49080d43c4d1913464350f124444b0f0d41c4d0f0d4641f0f12408490f1341c4d0501c3c8913124800b111343c351113444490f0d43c35
|42=>0xf1243c36021241c4d111343c350f1243c3507134484d19134641f0f124281f190d43c491112c3c35071344449111343c35050dc644d0f1243cdd0f2284c49081243c4d0713444490f0d44c490f1343c8a1213460370413434490a07c3c110d124643a0d1343c490502c644d0f1244c49190d43c490804c34490f1343c8a0d1244c49080d43c4d07134143f081243c4d
|43=>0x131243c490d134484d0f0d4644f0f12408490f0e8344d13124641f0f1240849080d43c4d1122c3c3513124284f190d43c490f2281c4d121343cb50d2284c490f18834891312478490802c3c4d0507c3c8912134140b0f2244c490f0d43c49021243c8a131243cb60d2284c490d124344d1213444490f0d43c4d55124444f0f0d43c350d134484d0f13464350f124643b
|44=>0xd2244c49112203c35131243cb50d2284c490f0d43c4907134384b0d1343c350d134641f0f124448a0f0d44c490812c3c350f13464380d1343c490501c3c8913124344d190d43c490f134641f0f124641f0f1240849111243c35071343c350f1341c4d0f224348913124804b080d43c4d0a07c44490f0d409010f04834490f134348912134284d190d43c490f0d43489
|45=>0xf0e4344d1213434dd0f2284c4911124444d0f0d43c35081243c4d0d1e4200b0f13444880f0d44c490f0d43c120d12414370f2244c49131240849071347c4d1907c3c490501c20490f1344c49190d43c490a13464350f12460370d2244c492012c444d0f0d43449080d43c4d112243c35131240849111343c351122c3c35131243c890f0d44c490d1343c350f1243c62
|46=>0xf0d44c490d1343c49021241c4d0d228484d112283c35131243c4d0f0443449131243c4d0f1243c610d2244c490a13444490f0d4800b111343c350501c3c8913124140b191343c490f2284c490f0d4641f0f1243c350d1340849050fc20490f1343c890f0d44c490f0d40849071343c4d0f0d4484d0f2d4348a131244c49080dc3c4d0f224344d12134448a0f0d44c49
|47=>0xf0d414070f2244c49112284c490f2243c3513124444b0f0d43c49071343c350f12434dd0f2284c49112203c351312414370f2244c490f04434490713414350f2244c490f1241c4d12134284f190d43c49080d4200b0f13444890f0d44c490f184348913124444f111243c350f12420370f13420490f1341c4d0f0d4348a131247c4d1907c3c49071343c35121344488
|48=>0x80dc3c4d0f0e4344d0f2284c490d13408490f0d44c491907c3c49081243c4d0802c3c4d111243c35190d43c490e12c344d0f2244c490d1343c350f0d41c4d0f1241c4d0d2244c490f2284c49021243c361913c3c491112c3c350d134484d0f0d43c4d0f1343c490f1240849131243c36111343c351112c3c350f1244c490413434490d1243c4d0f0d408490a13c4449
|49=>0x3c36131243c35071343c350f124344d021241c4d0f2244c490f0d44c490d2244c490d2284c490f04834490d124344d190d43c490d2284c4907134484d0f0d43c4d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3260000031100000000000003010000000000000000000002a600000000000000000000000002640000000000000206000000000000000000000000000000000000000000000000000001c401a20155000000000000000000000000000000f60000000000000000000000b400a100460000000000000000000400000000
|6,1=>0x74100000000000006e600000000000006860000000000000000000000000000000000000671000000000616000005e30000000000000000000000000000058600000000000005710516000000000000000000000000000004b60000000000000000000004560000000000000000044100000000000003e60000000000000386
|6,2=>0x7a40000075500000000000000000000000000000000
|7,0=>0xe61000000000000000000000e150dc500000d750d340d030cf100000cb40c830c44000000000c310bf400000bb400000b830b710b3400000000000000000b210b110b0100000ab500000aa10000000000000a550000000000000a2309e4000000000000000009950000094508f500000000000008a5000008910854081407e3
|7,1=>0x15d5000015c115b1159200001581154414f50000000014c3000014b10000148300001435000013f413b4139213811353130512d300000000000012c1128400000000000000000000125300001214000011c500001175000000000000000011340000000010f410a500001055100500000fb50f6500000f330ef40eb40e740000
|7,2=>0x1d551d411cf5000000001cd2000000001c941c541c0500001bc41b751b43000000001af51ac300001a841a4400001a130000000019e319b30000198300001953190500000000000018c418b118740000000018250000000017d500001794175417050000000016c400001675000000001661000000001624
|7,3=>0x257400002525000024e40000000024952445240423f123e100000000000023a42355230522c42275000022612233000000000000000021e5219500002154000000002105000020b52083205300002014000000001fc500001f84000000000000000000001f35000000001ee51e951e720000000000001e611e241df31da5
|7,4=>0x2db52d742d6100002d15000000002cc52c752c432c0400002bc42b930000000000002b6300002b242b112ac52a750000000000002a2529f300000000000029e1000000000000299529632915000028c5000000000000000028842844000027f527a527642715000026c526752661000000000000261525c5000025b10000
|7,5=>0x3615000035d435940000000000000000000035450000000034f534a500000000000034640000341533c533b100000000000033743325000032e4000000003295000032630000322431f3000031b40000000000000000316500003124000030f3000030a500000000305530052fb52f6500002f422f042eb52e652e152e010000
|7,6=>0x398439353912000000000000000038c538753834000037e537950000374536f50000000036b400003665000000000000
|8,0=>0x482347e447a447914754471446d446a34664462445e445a4457345344503000044d344944454441443d443944363432442f342b44274423441f441b44174413440f440b4407440343ff43fc33f843f533f143ed43e943e543e143dd43da33d643d243ce43ca43c733c343bf43bb43b833b443b223ae43ab33a743a433a0439c4
|8,1=>0x561455d455a35564552454f354b45474543453f453b45374533452f452b452745234521251e351d151945163512450e450b350835044000050044fc44f934f544f144ed44eb24e744e344df44db44d744d344cf44cb44c924c544c234be44bb34b834b444b0400004ac44a844a444a0449c4498449440000490448d348944854
|8,2=>0x64b364836453642363e463a463736334630362c462936263622461e461a46173613460f460b4607460345ff400005fb45f745f345ef45eb45e745e345df45db45d925d635d335cf45cc35c845c445c045bc45b845b445b045ac45a845a625a2459e459a45964592458f358b45874583457f457b457835744570456c456935654
|8,3=>0x7354731472d472947254721471d4719471637124710270c47084704470046fc46f846f446f136ed46e946e546e146dd46d946d546d236ce46cb36c836c446c046bc46b846b446b046ac46a936a546a1469d469a369736952691468d4689468546814000067e367a467736743670466c466846644662265e465a46564652464e4
|8,4=>0x80740000803480217fe47fa47f647f247ee47eb37e747e347df47dc37d847d537d147cd47c9400007c547c147bf27bb47b747b347af47ab400007aa17a647a24000079e479a47964792478e478b30000787400007843780477c477847762772476e476d176a37664762475e475b375747534750374c474937454741473d47394
|8,5=>0x8df28db48d748d348cf48cc38c938c548c148bd48b948b548b148ae38aa48a648a428a0489c489a28964892488e488a40000000088918854881487d4000087c1878487538714000086d486948654863285f485b485748534851284d484948454841483d483a38364833382f482b482740000823481f481b48174813480f480b4
|8,6=>0x9c849c449c049bc49b849b449b049ad39a949a549a1499d499949954991498e398a49864983397f497b497749734970396c496849644961395d4959495549514000094d4949494819444940493c493939354931492e392a49273923491f4000091b49174913490f490b49074905290148fd48f948f548f148ed48e948e548e14
|9,0=>0xa893a863a833a803a7d3a7a3a773a743a713a6e3a6b3a683a653a623a5f3a5c3a593a563a533a503a4d3a4a3a473a443a413a3e3a3b3a383a353a323a2f3a2c3a293a263a233a203a1d3a1a3a173a143a113a0e3a0b3a083a053a0239ff39fc39f939f639f339f039ed39ea39e739e439e139de39db39d839d539d239cf39cc3
|9,1=>0xb473b443b413b3e3b3b3b383b353b323b2f3b2c3b293b263b233b203b1d3b1a3b173b143b113b0e3b0b3b083b053b023aff3afc3af93af63af33af03aed3aea3ae73ae43ae13ade3adb3ad83ad53ad32ad03acd3aca3ac73ac43ac13abf2abc3ab93ab63ab33ab03aad3aaa3aa73aa43aa13a9e3a9b3a983a953a923a8f3a8c3
|9,2=>0xbff3bfc3bfa2bf73bf43bf13bee3beb3be83be53be23bdf3bdc3bd93bd63bd33bd03bcd3bca3bc73bc43bc13bbe3bbb3bb83bb53bb23baf3bac3ba93ba63ba33ba03b9e2b9b3b983b953b923b8f3b8c3b893b863b833b803b7d3b7a3b773b743b713b6e3b6b3b683b653b623b5f3b5c3b593b563b533b503b4d3b4a3
|10,0=>0xc542c522c502c4e2c4c2c4a2c482c462c442c422c402c3e2c3c2c3a2c382c362c342c322c302c2e2c2c2c2a2c282c262c242c222c202c1e2c1c2c1a2c182c162c142c122c102c0e2c0c2c0a2c082c062c042c022
|11,0=>0xc5c1c5b1c5a1c591c581c571c561
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 16
def pmP:Nat→Nat
|0=>0xcc0000005000000027600000110000000840000004080000020000000080000000300000001640000008400000041000000200000000f0000000760000003a0000001c8000000e0000000660000002b000000110000000800000003200000013000000090000000440000002000000008000000018000000080000000200000000
|1=>0x48800000242000001202000009000000042100000210000001070000008020000040000000172c00000a1000000500000002600000011f8000008f60000047900000239000001164000008a00000044900000221000001100000008720000042900000210000001040000008060000040200000200800001000000007a200000300
|2=>0x2021000010104000080800000403a0000201c800010088000080400000401000002001000010004000080000000292000000d9c800006c00000032f20000191800000c8400000610000001af600000d400000068800000342000001a0000000c10000006010000030000000165000000b08000004fd8000026600000127000000930
|3=>0x249c00001208000009000000047f1000023b98000119ac00008af6000045790000227d80001136c000089b20000447f0000223d8000111e8000088f2000044730000223580001118c000088b6000044510000222800001112c00008884000044400000221e00001108c000088440000441000002201000011000000083b600004122
|4=>0x401c00002008000010020000080000000327d8000190a40000bbf200005b3900002d848000160000000ac820000547900002a2c800013dcc00009e7200004dfb000026bd80001350800009a7400004d380000269800001340800009a0000004cfb0000266c8000131ec000098f200004c00000024fd8000125e8000092a00000493a
|5=>0xa22d80005100000021a70000104d9000082390000411800002080400010400000080600000400ec0002007200010020000080000000337ec00019af60000cc7b000064bc8000325e0000190020000c46b00006200000030460000180c00000c01000004cac8000235e8000112f200008978000044000000214200001080000008108
|6=>0x2021d80010104800080802000404000002003c80010018400080080000400000001a23d8000991e400049bf600024db9000126bd8000935e400049a720002457b000122bc8000911ec000488b600022d29000106bd8000834e400040830000202000000c21c8000600ec0003007200014d380000a4808000517ec00028bf20001447a
|7=>0x280e0000120048000898f600044c52000222bd8001113ec000888fe0004447b0002223c8001111800008888600044442000222200001110e4000888200004440200022200000110708000882f2000440790002201d800110080000818f6000408400002023f8001011ec000808f200040472000202300001011400008088400040440
|8=>0x4a6bd8002335ec001199f60008ccdb000462358002200000010c9f600084d3b000424dd8002115ec00108a760008452b0004227d80021132c001089920008447b0004223c8002111ac001081160008400b000420048002026ec001008000008004000040014800200000000e88b60006457b0002a2fd8001511ec000a08f200050400
|9=>0xa26090005115ec00288ad60014447b000a06090005011ec002800a0001140790008801c8004333ec0021088000104c52000822bd8004111ec00208104001040020008200000040102400200000000cc47b000646358003211ac00190802000c456b000622958003015ac00159ad2000a657b000522bc8002915ac00139bf600094f79
|10=>0x42001c8020d11ec01028b36008141c00040a0310020331ec0101007200804c7b0040261580201236c010088f6008044790040200000200150001000a40008005000040023d8020007080100003200400031002000008008111cc004008e6001ccc7b000e223d8006111ec003088d60014cc52000a62158005131ec002898a400144c50
|11=>0x100020580800010004000004010a657b008122bd80400152c020008000090453b0048223d80241110001208804009040420048200000240010c01120a440087457b0042a2bd802151588010a88c4008541c2004282b100214070801088af600844562004222a1002111488010888f600844400004202b100210150801080a7600840479
|12=>0x20c223d8103115ec08000080040000290180227d80c002468052088f6029044020148023c80a0011ec050008d6021044fb010426fd8082102ec041080840204403a010200010080331e404009bf602004d7b0100269d0080131e4040088f602004442010020fc8080101080400807402004012010020010080035e4040012f202000939
|13=>0x10800447b84002235a000911eca410c9965200447b2100227d9000517ec80008bf62808447b100422358800000a424028a5210000000060a26358202035ec101012f20804c47b0400623d82001b7e41000c8f208004d7b0400263c8200111ec10001a2008000910040000340200001000e0088960700090a
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x5980000000180000000900000000000000000000138000014c003c0000000000000000120000000370080000000000000001000000000000058000000000190000000c60000000540013800b3000000019000000000000f800000000000002a8000000220000000000000000000000000000000437008000000000000000108000000000000419100000000000880000
|6,1=>0x80057000000000000000000
|7,0=>0x3f801b0b31e0006e222b8000013000dc0002001b8002a02c1938220088800000028caa00000000000230005400030007e0000000000400000700a0025a16002432800224f15414000c8000000000029215004300422598000b1a11000009c508000437842700400002cc009c5986400070027000000033000000004cae000000000a4003accc000000010001bd4caa13
|7,1=>0x800950037000003e42844374e0003200016826e1c1700166130000000001993c0002000007c006d84c44001200000a00000800000000000b60000081ad83000003759974309a000000000338658a0000418000002008f600050f826000053426000201000550000026020000800225000000002bacc04000019c0000a480044136400000550027400006c000002a
|7,2=>0xa58004802000000000000140000008c800000008800254bacc0000001251ed815000012e0008800028300004000000001110000800130006c0019d21898c54006c04451258d46e000031438370029c0000270d8aa05000884400000020c00123602c450000001120f00000006c0000000008082c005a064000000364480049b18fb09002f16eb3000000023bd0003219
|7,3=>0x11600780000000011773988009829003060100000aa00140000000
|8,0=>0x3982804cd3d365bb44a19c472f0055d6f023d104d70d80180802cb01154e0002c1b142fd986a8ab420bc601d393fb255855698093a021d0a80a0095bfd7c589e224c4005d8082015029930e9c1ebdef95301ae522d32b9d2f200421bcda6f8d9dae62d6cb78060fc21c67a582bceb2223c984cc23883b06c86dc097db25601b88d41ad4d44f03a0088b4d00708e8d34e
|8,1=>0x3100602a61553c1e3b743f82662abd424a631eae869b17335b462452574047e248095adacec504ebd2b548e6178e0080455940b4841566800447111009144c0ba7c055b1d8937023012e1b80ad9cc4ab9d010500a020800640571dc8e78245584000e9d90f4191f2eab28b7101285b8ea5c251da8713584ff2a86b52fc23520a8025a2a80e0af92b1ac703b7b83e5e6d
|8,2=>0x12a8da0f3937004685b005c68b2f08862b5bf0158e029124acb56000025a3016a000037318a81e0070394b3063b3c6994a1112a1eee07b80040f6e69848b40000c23b5d7105de47af8034e375b3961c01ac8095329730d01c02380fad0004ed8004bf528a50243000dd875c00498026272a24260031002a19a32288040168b626a63ce07db82300b724e13a55504826
|8,3=>0xc903ce0313195b72227a8060f214d83c1a0a38bb074e13482dde0ac3695680211c749a730000532d8588911a3412241b317012e40600008ac077f8c98c053028684e709049d47003
|9,0=>0x7823a7c577c616073c669cd0a7346599a524b5220b873816d2e873baccdf74667d20c76ddbe26eba8682333d7dc4ddec6f89e5ac04777c1ddab707d390cb825958b1596af4cb516e436226d8ea05dae4f847be151ac7ed0279157ed0980fabdc751f3b17c4cc79f7c196799058cca7e608f5df118dcaac620699a5572811ddce020f8582c36efcd59cdaf77d4075fb33
|9,1=>0x1ec8f0123df6c2cc3dd156c08edacdaf7916df15a419cd9c7739c5b36f3b3a3dbe30d61cd898f8251d5e4d89a1b175a413d283897ba9b78f8b29ce33ba575a4539739d08e72c
|10,0=>0x2268f39ddf1355bbda71277432c28589a33e1a0b1d35a6df32c64f1f4c2cce2620797c4c9fa8f8b1cdf0f83cddeb110
|11,0=>0x1cce6733bbe0f332
|12,0=>0x73
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 33 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 11 roots_254 ops++addP pm 1 dom_239 10 roots_239 ops++addP pm 2 dom_206 6 roots_206 ops++addP pm 3 dom_253 11 roots_253 ops++addP pm 4 dom_251 11 roots_251 ops++addP pm 5 dom_247 11 roots_247 ops++addP pm 6 dom_127 10 roots_127 ops++addP pm 7 dom_183 9 roots_183 ops++addP pm 8 dom_87 6 roots_87 ops++addP pm 9 dom_249 10 roots_249 ops++addP pm 10 dom_191 10 roots_191 ops++addP pm 11 dom_155 6 roots_155 ops++addP pm 12 dom_245 10 roots_245 ops++addP pm 13 dom_243 10 roots_243 ops++addP pm 14 dom_223 10 roots_223 ops++addP pm 15 dzo_155_4 6 roots_155 ops++addP pm 16 dzo_87_8 6 roots_87 ops++addP pm 17 dzo_215_8 7 roots_215 ops++addP pm 18 dom_207 7 roots_207 ops++addP pm 19 dom_123 9 roots_123 ops++addP pm 20 dom_175 7 roots_175 ops++addP pm 21 dom_205 6 roots_205 ops++addP pm 22 dom_237 9 roots_237 ops++addP pm 23 dom_111 7 roots_111 ops++addP pm 24 dom_231 9 roots_231 ops++addP pm 25 dom_63 6 roots_63 ops++addP pm 26 dom_235 9 roots_235 ops++addP pm 27 dzo_219_4 7 roots_219 ops++addP pm 28 dom_219 9 roots_219 ops++addP pm 29 dom_107 6 roots_107 ops++addP pm 30 dom_215 9 roots_215 ops++addP pm 31 dzo_247_8 8 roots_247 ops++addP pm 32 dzo_251_4 8 roots_251 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_155_4_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_87_8_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_215_8_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_219_4_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_247_8_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_251_4_155 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 11 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 2000006 zs symsG zs (hk 2000006 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 2000006 ys h symsG ys (hk 2000006 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 2000006 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 146 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 18 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 146 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_384 : ∀ i, 384 ≤ i → i < 411 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 27 384 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 411 → Z 7 i = true := (range_split (range_split z7_0 z7_128) (range_split z7_256 z7_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_384 : ∀ i, 384 ≤ i → i < 448 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 448 → Z 8 i = true := (range_split (range_split z8_0 z8_128) (range_split z8_256 z8_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 190 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 62 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 190 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 42 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 7 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem checked (s:Nat) (hs:s≤12):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 2000006 mkCut s i=true:=by
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
  · exact z12 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 7=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤12) (h:RunD true dom_255 gM s xsM):False:=by
  have hmin:7≤s:=by have hl:=run_len h;change 8≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_255 roots_255 goal_255 13:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_255
theorem lowS_255:Lower true dom_255 roots_255 goal_255 13:=S_255.noCircuit
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 14 ≤ gates.length := by
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [3, 1] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [2, 10] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [9, 8] }, { op := GateOp.and, inputs := [15, 12] }, { op := GateOp.and, inputs := [13, 14] }, { op := GateOp.and, inputs := [16, 11] }, { op := GateOp.or, inputs := [17, 18] }, { op := GateOp.or, inputs := [20, 19] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 21 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 21 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 21 false =
      ((execN witGates xs256).getD 21 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[21]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 21 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 14 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 21, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 14 := rfl
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

end PEqualNP.Outside.L_meta_51792_aux

theorem PEqualNP.Outside.L_meta_51792 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51792_aux.main
