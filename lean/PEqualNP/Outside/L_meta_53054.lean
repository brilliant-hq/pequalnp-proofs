import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53054_aux
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
def dom_21 : Nat := 0x330033
def goal_21 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_21 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xfefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0fefea0a0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_37 : Nat := 0x3300000033
def goal_37 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0
def roots_37 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xfefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0fefefefea0a0a0a0
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00
def roots_42 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeecc00cc00ffeeffeecc00cc00ffeeffeecc00cc00ffeeffeecc00cc00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaa0a0a0a0fffafffaa0a0a0a0fffafffaa0a0a0a0fffafffaa0a0a0a0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00fffcfffccc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0fafafafafafaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefefefea0a0fefefefefefea0a0fefefefefefea0a0fefefefefefea0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaa0000ffaaffaaaaaa0000ffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccccc00ffccffcccccccc00ffccffcccccccc00ffccffcccccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeeecc00ffeeffeeeeeecc00ffeeffeeeeeecc00ffeeffeeeeeecc00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaa0a0fffafffafafaa0a0fffafffafafaa0a0fffafffafafaa0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00fffcfffcfcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffefefeeca0fffefffefefeeca0fffefffefefeeca0fffefffefefeeca0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_69 : Nat := 0x330000000000000033
def goal_69 : Nat := 0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
def roots_69 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffaaffaaffaaffaacc00cc00cc00cc00ffaaffaaffaaffaacc00cc00cc00cc00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaa0a0a0a0a0a0a0a0fffafffafffafffaa0a0a0a0a0a0a0a0
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfff0fff0fff0fff0cc00cc00cc00cc00fff0fff0fff0fff0cc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffafffafffafffaeca0eca0eca0eca0fffafffafffafffaeca0eca0eca0eca0
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffaaaaffffaaaaeeee0000eeee0000ffffaaaaffffaaaaeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffafafffffafafefea0a0fefea0a0fffffafafffffafafefea0a0fefea0a0
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaa0000aaaa0000ffffffaaffffffaaaaaa0000aaaa0000
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffaaffffffaaeeeecc00eeeecc00ffffffaaffffffaaeeeecc00eeeecc00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaa0a0fafaa0a0fffffffafffffffafafaa0a0fafaa0a0
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffff0fffffff0fcfccc00fcfccc00fffffff0fffffff0fcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffafffffffafefeeca0fefeeca0fffffffafffffffafefeeca0fefeeca0
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xffffffffaaaaaaaaeeeeeeee00000000ffffffffaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafafefefefea0a0a0a0fffffffffafafafafefefefea0a0a0a0
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_104 : Nat := 0x101000001010000010100000101
def goal_104 : Nat := 0xffffffffff00ff00ff00ff0000000000ffffffffff00ff00ff00ff0000000000
def roots_104 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffffffffffaaffaaffaaffaa00000000ffffffffffaaffaaffaaffaa00000000
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffffffffff00ff00ffccffcccc00cc00ffffffffff00ff00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffffaaffaaffeeffeecc00cc00ffffffffffaaffaaffeeffeecc00cc00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfffffffffff0fff0fff0fff000000000fffffffffff0fff0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffffafffafffafffaa0a0a0a0fffffffffffafffafffafffaa0a0a0a0
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffffffffff0fff0fffcfffccc00cc00fffffffffff0fff0fffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffffafffafffefffeeca0eca0fffffffffffafffafffefffeeca0eca0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffaaaaeeeeeeeeeeee0000ffffffffffffaaaaeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0f0f0f0f0f0f00000fffffffffffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafafafafafafafaa0a0fffffffffffffafafafafafafafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffff0f0fcfcfcfcfcfc0000fffffffffffff0f0fcfcfcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffafafefefefefefea0a0fffffffffffffafafefefefefefea0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffffffffffff00ff00ff0000000000ffffffffffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffffaaffaaffaaaaaa0000ffffffffffffffaaffaaffaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffffffffff00ffccffcccccccc00ffffffffffffff00ffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffffaaffeeffeeeeeecc00ffffffffffffffaaffeeffeeeeeecc00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffffffffffff0fff0fff0f0f00000fffffffffffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffffafffafffafafaa0a0fffffffffffffffafffafffafafaa0a0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffffffffff0fffcfffcfcfccc00fffffffffffffff0fffcfffcfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffffafffefffefefeeca0fffffffffffffffafffefffefefeeca0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaacc00cc00cc00cc00cc00cc00cc00cc00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_142 : Nat := 0x555500000000000000000000000000005555
def goal_142 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0cc00cc00cc00cc00cc00cc00cc00cc00
def roots_142 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffafffafffafffafffafffafffafffaeca0eca0eca0eca0eca0eca0eca0eca0
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeeecc00eeeecc00eeeecc00eeeecc00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fcfccc00fcfccc00fcfccc00fcfccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffafefeeca0fefeeca0fefeeca0fefeeca0
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaa00000000ffaaffaa00000000
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffeeffeecc00cc00ffeeffeecc00cc00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaa0a0a0a0fffafffaa0a0a0a0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaeeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00ffccffcccccccc00ffccffcccccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaffeeffeeeeeecc00ffeeffeeeeeecc00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafffefffefefeeca0fffefffefefeeca0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa0000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaacc00cc00cc00cc00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0cc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaeca0eca0eca0eca0
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafaa0a0fafaa0a0
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafefea0a0fefea0a0
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00cccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaeeeecc00eeeecc00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaa0a0fafaa0a0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafefeeca0fefeeca0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafffffffffafafafafafafafaa0a0a0a0
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffaaffaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffff00ff00ffffffffff00ff00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffffffaaffaaffeeffeecc00cc00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffffffff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffafffafffaa0a0a0a0
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffafffafffffffffffafffafffefffeeca0eca0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffffff0000cccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffaaffaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffff00ffffffffffffff00ffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffaaffffffffffffffaaffeeffeeeeeecc00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffffffafffafffafafaa0a0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffff0fffffffffffffff0fffcfffcfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffafffffffffffffffafffefffefefeeca0
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_21
def pG:List (Nat×Nat):=[(1,5),(1,17),(4,5),(4,20),(16,17),(16,20)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_21.map (·&&&dom_21)
def gM:=goal_21&&&dom_21
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0xd83d3
|3,0=>0xd83d3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330000c000c220022
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 22 0x3fffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_21 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_21 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_21==dom_21)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_21 gM v ys):RunD true dom_21 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_21 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_21 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_21 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_21 roots_21 goal_21 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_21
theorem lowS_21:Lower true dom_21 roots_21 goal_21 4:=S_21.noCircuit
def isoMvS_37:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_37:Lower true dom_37 roots_37 goal_37 4:=lower_iso_b isoMvS_37 (by decide +kernel) lowS_21
def isoMvS_42:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_42:Lower true dom_42 roots_42 goal_42 4:=lower_iso_b isoMvS_42 (by decide +kernel) lowS_21
def isoMvS_69:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_69:Lower true dom_69 roots_69 goal_69 4:=lower_iso_b isoMvS_69 (by decide +kernel) lowS_21
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_21
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_21
def isoMvS_104:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_104:Lower true dom_104 roots_104 goal_104 4:=lower_iso_b isoMvS_104 (by decide +kernel) lowS_21
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_21
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_21
def isoMvS_200:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_21
theorem lowS_23:Lower true dom_23 roots_23 goal_23 5:=lower_slice_b [(0xcc00cc,16,18)] (by decide +kernel) lowS_21
namespace S_27
def pG:List (Nat×Nat):=[(1,17),(2,10),(2,18),(3,11),(3,19),(8,10),(9,11),(9,25),(16,17),(16,18),(24,25),(24,26)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_53:Lower true dom_53 roots_53 goal_53 5:=lower_slice_b [(0x33000000330000,1,17)] (by decide +kernel) lowS_37
namespace S_85
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(4,5),(4,20),(4,68),(16,17),(16,20),(16,80),(64,65),(64,68),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_85.map (·&&&dom_85)
def gM:=goal_85&&&dom_85
def NN:Nat→Nat
|3=>3
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x5bd4055c85319d6
|4,0=>0x8bae8419fa1e5c817049120fd0d46506756036b3
|5,0=>0x5c79a2d7ad168b5
|6,0=>0x168b5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33003300000000003200324400440000000000440000000320000000000000032cc00880000000000cc00880003300000000000000300000000000000000c800c9100110000000000110010c000c00000000000c00083000300000000000300030cc00cc0000000000000003300000000000000330000cc00c00000000000cc00c3300330000000000330000cc00cc0000000000c000c2200220000000000220022
|_,_=>0
def sP:Nat→Nat
|0=>0x4605346052460546054e605460d5460c53b60534105460a52416049605468547053210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0x5eaa952aa0536a5948a8c5
|5,0=>0xf55c2b44
|6,0=>0x424
|_,_=>0
def wAt:=mkWire dB 15 86 0x3fffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x6451540591655915655156551
|_=>0
def oO:Nat→Nat→Nat
|3,0=>2
|4,0=>0x6242002200
|5,0=>0x918100
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfc7630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>2
|4,0=>0x1810
|5,0=>0x16b
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_84 4 roots_84 ops++addP pm 1 dom_81 4 roots_81 ops++addP pm 2 dom_69 4 roots_69 ops++addP pm 3 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_85 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_84 4 s (0,roots_84.map (·&&&dom_84)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_85 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_84 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_85==dom_85)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_85 gM v ys):RunD true dom_85 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_85 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_85 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_85 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_85 roots_85 goal_85 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_85
theorem lowS_85:Lower true dom_85 roots_85 goal_85 7:=S_85.noCircuit
def isoMvS_30:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_30:Lower true dom_30 roots_30 goal_30 4:=lower_iso_b isoMvS_30 (by decide +kernel) lowS_27
def isoMvS_39:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_39:Lower true dom_39 roots_39 goal_39 5:=lower_iso_b isoMvS_39 (by decide +kernel) lowS_23
def isoMvS_43:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_iso_b isoMvS_43 (by decide +kernel) lowS_23
def isoMvS_45:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_23
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 5:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_23
def isoMvS_57:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 4:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_27
def isoMvS_58:List (Nat×Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 5:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_23
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_27
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 4:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_23
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 4:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_27
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_23
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_23
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 5:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_23
def isoMvS_101:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 7:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_85
def isoMvS_105:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_53
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_53
def isoMvS_108:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 5:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_53
def isoMvS_113:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_53
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_53
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 5:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_23
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 4:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_23
def isoMvS_142:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_142:Lower true dom_142 roots_142 goal_142 4:=lower_iso_b isoMvS_142 (by decide +kernel) lowS_27
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 7:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_85
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_23
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_53
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_53
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_53
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_53
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 5:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_23
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 7:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_85
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_53
def isoMvS_202:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_23
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_53
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_85
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_85
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 7:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_85
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 7:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_85
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 7:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_85
def dzo_23_8:=0xff00ff00
def gzo_23_8:=0xfe00ec00
def gsh_23_8:=0xfe00ec
theorem lowS_zo_23_8_21:Lower true dzo_23_8 roots_23 gzo_23_8 5:=lower_iso_b (d1:=dom_23) (r1:=roots_23) (T1:=gsh_23_8) [(dom_23,8)] (by decide +kernel) (lower_slice_b (T:=gsh_23_8) [(0xcc00cc,0,2)] (by decide +kernel) lowS_21)
namespace S_31
def pG:List (Nat×Nat):=[(1,5),(1,17),(2,10),(2,18),(3,7),(3,11),(3,19),(4,5),(4,20),(6,7),(6,14),(6,22),(8,10),(9,11),(9,13),(9,25),(12,13),(12,14),(12,28),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_31.map (·&&&dom_31)
def gM:=goal_31&&&dom_31
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x305f01ca78
|5,0=>0x7e5bd4cf0421390
|6,0=>0x510d7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfafafafa55550000fffff0f0f0f0f0f055555050ffff0000ff00ff00f0f0a0a0ccccccccaaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x436104396104361087436104361543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 32 0xffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x103
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c80
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x53
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_23 5 roots_23 ops++addP pm 1 dzo_23_8 5 roots_23 ops++addP pm 2 dom_30 4 roots_30 ops++addP pm 3 dom_27 4 roots_27 ops++addP pm 4 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_31 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_23 5 s (0,roots_23.map (·&&&dom_23)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_31 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_23 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_31==dom_31)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 gM v ys):RunD true dom_31 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_31 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_31 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_31 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_31
theorem lowS_31:Lower true dom_31 roots_31 goal_31 7:=S_31.noCircuit
namespace S_47
def pG:List (Nat×Nat):=[(1,5),(1,33),(2,10),(2,34),(3,7),(3,11),(3,35),(4,5),(4,36),(6,7),(6,14),(6,38),(8,10),(8,40),(9,11),(9,13),(9,41),(12,13),(12,14),(12,44),(32,33),(32,34),(32,36),(32,40)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_47.map (·&&&dom_47)
def gM:=goal_47&&&dom_47
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xa0e5
|4,0=>0x32b9c270322126c0c7bd
|5,0=>0xaa88b92cb08eb6e7a6b34ced820423128d411eb8106f001e3d
|6,0=>0xa2a8927eef227c803a9c
|7,0=>0xa2a89
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0ff0000f0f0ffff0000fff0ffff0000ff003333000033000f0f00000e0effff0000aaaaffaa0000000000dd000000ccffff00000000ffee0000ccccf0f00000f0f0aaaa0000aaaaffff0000f0f0ff000000ff00fefe0000aaaacccc0000cccc
|0,1=>0x333300000000eeee0000eeee00000000eeee03030000000000ff000000000f0f00000a0a333300002222ffaa0000ffaafcfc0000fcfcfcfc00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1c45010e22808711404ca8e2280871170021c45012e711404b34e5012a710094388a024d47908a038a05010e27940471c45011a71148c388045a922280e501107308a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 26 48 0xffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x3833910113913c438b189395683389
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x6151412202
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0x3feb7be761440c180
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20049351
|6,0=>0x678a
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_45 5 roots_45 ops++addP pm 2 dom_39 5 roots_39 ops++addP pm 3 dom_37 4 roots_37 ops++addP pm 4 dom_42 4 roots_42 ops++addP pm 5 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_37 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_46 5 s (0,roots_46.map (·&&&dom_46)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_47 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_46 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_47==dom_47)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 gM v ys):RunD true dom_47 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_47 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_47 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_47 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_47
theorem lowS_47:Lower true dom_47 roots_47 goal_47 8:=S_47.noCircuit
theorem lowS_55:Lower true dom_55 roots_55 goal_55 6:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xa0a0a0a0a0a0a0a,16,17)] (by decide +kernel) lowS_58
def dzo_53_8:=0x3300330033003300
def gzo_53_8:=0x3300330032002000
def gsh_53_8:=0x33003300320020
theorem lowS_zo_53_8_21:Lower true dzo_53_8 roots_53 gzo_53_8 5:=lower_iso_b (d1:=dom_53) (r1:=roots_53) (T1:=gsh_53_8) [(dom_53,8)] (by decide +kernel) (lower_slice_b (T:=gsh_53_8) [(0x33003300000000,0,32)] (by decide +kernel) lowS_21)
namespace S_61
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(4,5),(4,20),(4,36),(8,40),(9,13),(9,25),(9,41),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_61.map (·&&&dom_61)
def gM:=goal_61&&&dom_61
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x40a0c
|5,0=>0xbe280
|6,0=>0xd596d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3333000033330000c8c8c8c8c8c8c8cb333333300000000cc00cc00cc00cc030303030303030308888888888888888000323200003232
|_,_=>0
def sP:Nat→Nat
|0=>0x99a333a8c688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 62 0x3fffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x45
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
addP pm 0 dom_53 5 roots_53 ops++addP pm 1 dom_60 4 roots_60 ops++addP pm 2 dzo_53_8 5 roots_53 ops++addP pm 3 dom_45 5 roots_45 ops++addP pm 4 dom_57 4 roots_57 ops++addP pm 5 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_61 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_21 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_53 5 s (0,roots_53.map (·&&&dom_53)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_61 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_53 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_61==dom_61)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 gM v ys):RunD true dom_61 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_61 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
theorem lowS_87:Lower true dom_87 roots_87 goal_87 8:=lower_slice_b [(0xcc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_85
namespace S_107
def pG:List (Nat×Nat):=[(1,33),(1,65),(2,10),(2,34),(3,11),(3,35),(3,67),(8,10),(8,40),(8,72),(9,11),(9,41),(9,73),(32,33),(32,34),(32,40),(32,96),(64,65),(64,72),(64,96),(66,67),(66,74),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_107.map (·&&&dom_107)
def gM:=goal_107&&&dom_107
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f00000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0af0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 108 0xfffffffffffffffffffffffffff
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
addP pm 0 dom_106 5 roots_106 ops++addP pm 1 dom_105 5 roots_105 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_99 5 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_106 5 s (0,roots_106.map (·&&&dom_106)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_106 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_107==dom_107)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_107 gM v ys):RunD true dom_107 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_107 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_107 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_107 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_107 roots_107 goal_107 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_107
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=S_107.noCircuit
theorem lowS_109:Lower true dom_109 roots_109 goal_109 8:=lower_slice_b [(0x3300000033000000330000003300,32,40)] (by decide +kernel) lowS_101
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_slice_b [(0x330000003300000033000000330000,1,17)] (by decide +kernel) lowS_101
namespace S_213
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(4,5),(4,20),(4,68),(4,132),(16,17),(16,20),(16,80),(16,144),(64,65),(64,68),(64,80),(64,192),(128,129),(128,132),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffff
def xsM:=roots_213.map (·&&&dom_213)
def gM:=goal_213&&&dom_213
def NN:Nat→Nat
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x724b8
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x330000000000000033000000000000003300000000000000330000c000c00000000000c000c00000000000c000c00000000000c000c220022000000000022002200000000002200220000000000220022cc00cc00000000000000000000000000cc00cc000000000000000330033000000000033003300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>5
|_,_=>0
def wAt:=mkWire dB 5 214 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff
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
|8,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_212 7 roots_212 ops++addP pm 1 dom_149 7 roots_149 ops++addP pm 2 dom_209 7 roots_209 ops++addP pm 3 dom_197 7 roots_197 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_213 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_212 7 s (0,roots_212.map (·&&&dom_212)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_213 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_213==dom_213)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_213 gM v ys):RunD true dom_213 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_213 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_213 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_213 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_213 roots_213 goal_213 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_213
theorem lowS_213:Lower true dom_213 roots_213 goal_213 9:=S_213.noCircuit
def isoMvS_62:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 6:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_59
def isoMvS_79:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_79:Lower true dom_79 roots_79 goal_79 7:=lower_iso_b isoMvS_79 (by decide +kernel) lowS_31
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_93:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_87
def isoMvS_94:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_59
def isoMvS_103:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 8:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_87
def isoMvS_110:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 7:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_107
def isoMvS_115:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_55
def isoMvS_118:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_55
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_55
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_107
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 7:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_31
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_87
def isoMvS_158:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_59
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_107
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_109
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_55
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_107
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_55
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_61
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_109
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 7:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_61
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_87
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_109
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_55
def isoMvS_229:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 9:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_213
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_117
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 8:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_109
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 8:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_117
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_117
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 6:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_55
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 8:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_109
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=lower_slice_b [(0xffff0000ffff0000,1,17)] (by decide +kernel) lowS_47
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,8,10)] (by decide +kernel) lowS_93
namespace S_111
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,65),(2,10),(2,34),(3,7),(3,11),(3,35),(3,67),(4,5),(4,36),(4,68),(6,7),(6,14),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,41),(9,73),(12,13),(12,14),(12,44),(12,76),(32,33),(32,34),(32,36),(32,40),(32,96),(64,65),(64,68),(64,72),(64,96),(66,67),(66,70),(66,74),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_111.map (·&&&dom_111)
def gM:=goal_111&&&dom_111
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x65c2
|7,0=>0xc5c14ac0905b5643880219e8f
|8,0=>0xb0c2d2c61c
|9,0=>0x4f37e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000fafa0000ffff0000fafa5555000050500000555500005050ffff000000000000ffff00000000f0f00000f0f00000f0f00000f0f0aaaa0000aaaa0000aaaa0000aaaaffff0000f0f00000ffff0000f0f0ffff0000aaaa0000ffff0000aaaaff000000ff000000ff000000ff00fafa0000fafa0000fafa0000fafacccc0000cccc0000cccc0000ccccffff0000ffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8371608327160483716048327105437160a837160a48371608371690543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 112 0xffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d9866197661d866097651d8655b8761d865d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x1fff46fe7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x64872
|8,0=>0x53
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_109 8 roots_109 ops++addP pm 1 dom_47 8 roots_47 ops++addP pm 2 dom_103 8 roots_103 ops++addP pm 3 dom_107 7 roots_107 ops++addP pm 4 dom_79 7 roots_79 ops++addP pm 5 dom_110 7 roots_110 ops++addP pm 6 dom_75 4 roots_75 ops++addP pm 7 dom_78 4 roots_78 ops++addP pm 8 dom_106 5 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_111 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_109 8 s (0,roots_109.map (·&&&dom_109)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_111 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_109 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_111==dom_111)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_111 gM v ys):RunD true dom_111 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_111 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_111 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_111 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_111 roots_111 goal_111 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_111
theorem lowS_111:Lower true dom_111 roots_111 goal_111 10:=S_111.noCircuit
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
namespace S_123
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(8,10),(8,40),(8,72),(9,11),(9,25),(9,41),(9,73),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(32,96),(48,49),(48,50),(48,56),(48,112),(64,65),(64,72),(64,80),(64,96),(66,67),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x374011604f0fa5b
|6,0=>0xd6397be1ac4643a192a30f48b
|7,0=>0xcdd9254f9e32d0c07721
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0cf0f0f0f000000000f0f0f0f00000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c5050505050505050505050505050000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f00000000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x8b27058bf27058b2105e8b270538b27054821058bd21038b210c4827058ba210549210548276543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b64ac7d8c3917
|7,0=>0x8aefd9c3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 16 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x81754218562d7549575615756e17555d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x10000
|6,0=>0x7252322111
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x8884103fd3ed3bd1fd006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x353e
|7,0=>0x75b
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_58 5 roots_58 ops++addP pm 4 dom_115 6 roots_115 ops++addP pm 5 dom_122 6 roots_122 ops++addP pm 6 dom_57 4 roots_57 ops++addP pm 7 dom_59 6 roots_59 ops++addP pm 8 dom_107 7 roots_107 ops++addP pm 9 dom_91 6 roots_91 ops++addP pm 10 dom_113 5 roots_113 ops++addP pm 11 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330033003300330032002000
def gsh_117_8:=0x330033003300330033003300320020
theorem lowS_zo_117_8_21:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x330033000000000033003300000000,0,32),(0x330033003300330000000000000000,0,64)] (by decide +kernel) lowS_21)
namespace S_125
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(4,5),(4,20),(4,36),(4,68),(8,40),(8,72),(9,13),(9,25),(9,41),(9,73),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(32,96),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x2f6fd00bc6
|6,0=>0xaac5fa88cd9b3539998b6e1904efd23d6fa036dc
|7,0=>0xc81a2a2824779f374e2462a2b53ae9150560e4b004a58
|8,0=>0xb4527938e28e226
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c0c0c0c0c0c0c080808080808080b3303330333033303330333033303330ccccccccccccccccc8c8c8c8c8c8c8c83020302030203020302030203020302cc88cc88cc88cc88cc88cc88cc88cc880003333000033330000323200003232cccccccccccccccc00000000000000033003300330033003300330033003300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8ca2222222222222222222222222222222c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333000000003333333300000000cccc0000cccc0000cccc0000cccc00033323332333233323332333233323332ccccccccccccccccc0c0c0c0c0c0c0c33333333333333332222222222222222
|0,1=>0x11101110111011101110111011101110
|_,_=>0
def sP:Nat→Nat
|0=>0x41406490680940620dc501924188a649065341241a1a5019241a1a5324835940920d0533d241a0e502483104c9220a0329241b9a13248829949221a5329241ac2501068384041940c491650292418820
|1=>0x41a0a649068394c920dc532483
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x56005
|6,0=>0x3863172a72461d71761160b6
|7,0=>0x7476d76766165985274c64573e7
|8,0=>0x8878267b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 17 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2994153252a532541532541d29971b4152813253a52994193252823253252992a541d3151b62813054152a51b63a52993a52992a54193252a53252995974193253252a541d315
|_=>0
def oO:Nat→Nat→Nat
|5,0=>4
|6,0=>0x5cd5248cf3348a31cc43
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xe75f3831d6ceb5fdafe91d64eb2300ffc7de2fa17787f81d60c902000f8040000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>2
|6,0=>0x30d640b988
|7,0=>0x114a8f29bdb0
|8,0=>0x30ed
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_117 8 roots_117 ops++addP pm 1 dom_61 7 roots_61 ops++addP pm 2 dom_113 5 roots_113 ops++addP pm 3 dom_93 8 roots_93 ops++addP pm 4 dom_116 5 roots_116 ops++addP pm 5 dom_109 8 roots_109 ops++addP pm 6 dom_124 7 roots_124 ops++addP pm 7 dom_121 7 roots_121 ops++addP pm 8 dzo_53_8 5 roots_53 ops++addP pm 9 dzo_117_8 6 roots_117 ops++addP pm 10 dom_120 5 roots_120 ops++addP pm 11 dom_60 4 roots_60 ops++addP pm 12 dom_57 4 roots_57 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_117_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_57 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_117 8 s (0,roots_117.map (·&&&dom_117)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000ccc8000000000000ccc8000000000000cc80
def gsh_205_2:=0x3333000000000000333200000000000033320000000000003320
theorem lowS_zo_205_2_197:Lower true dzo_205_2 roots_205 gzo_205_2 8:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3300000000000000330000000000000033000000000000003300,0,8)] (by decide +kernel) lowS_197)
namespace S_207
def pG:List (Nat×Nat):=[(1,5),(1,65),(1,129),(2,10),(3,7),(3,11),(3,67),(3,131),(4,5),(4,68),(4,132),(6,7),(6,14),(6,70),(6,134),(8,10),(8,72),(8,136),(9,11),(9,13),(9,73),(9,137),(12,13),(12,14),(12,76),(12,140),(64,65),(64,68),(64,72),(64,192),(66,67),(66,70),(66,74),(66,194),(128,129),(128,132),(128,136),(128,192),(130,131),(130,134),(130,138),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7bef668bec358bd
|5,0=>0xcb2988b5526ed665b3dc5a8125584a50dbc44f943cc883596131c8a2c523253f01c3aa0797c
|6,0=>0xbb4219291d8963f87bc681d7d7f3337928276e7c769a96e9165e89f5e7f05b543573fe4bd2e4b78c4a4143dce039cf836bf8302a22f9642eb652d058256ab2447a22e3a20f2d20b061c3aa1c16e174fb0d82a05d2604df4
|7,0=>0x912a790c698d8bf60e3c456423aa2939244379fa2ca8027f50256581d860126bd087cc06ecc
|8,0=>0x5bf255467818802
|9,0=>0x83b1d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000000000000f0f0000000000000a0affff000000000000ffff00000000000000000000000000000000ffff0000000000000000000000000000ffff0000000000000000ffff000000000000ffff000000000000ffff000000000000f0f0ffff000000000000ffff000000000000aaaa000000000000aaaafafa000000000000fafa000000000000fafa000000000000fafaffff000000000000aaaa000000000000f0f0000000000000a0a0ffff000000000000fff0000000000000ffaa000000000000ffa0f0f0000000000000f0f0000000000000f0f0000000000000f0f0aaaa000000000000aaaa000000000000aaaa000000000000aaaaffff000000000000ffff000000000000ffff0000000000000000ff00000000000000ff00000000000000ff00000000000000ff00ffff000000000000ffff000000000000f0f0000000000000f0f0cccc000000000000cccc000000000000cccc000000000000ccccffff000000000000aaaa000000000000ffff000000000000aaaaffff000000000000f0f0000000000000aaaa000000000000a0a0
|0,1=>0x5555000000000000555500000000000055550000000000005050ffff000000000000ffff000000000000ffff000000000000fafaafaf000000000000afaf000000000000afaf000000000000aaaaffff0000000000000f0f000000000000ffff0000000000000a0affff000000000000ffff000000000000ffff000000000000aaaa000000000000000000000000000000005555000000000000505055550000000000005555000000000000505000000000000050500000000000000000ffff0000000000000000000000000000aaaa0f0f0000000000000f0f0000000000000f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000a0a0555500000000000055550000000000005555000000000000000000000000000000000000000000000000ffff000000000000aaaa0f0f0000000000000a0a0000000000000f0f0000000000000a0affff000000000000fafa000000000000ffff000000000000fafaffff000000000000ffff000000000000fafa000000000000fafaffff000000000000f0f0000000000000ffff000000000000f0f0
|0,2=>0xf0f0000000000000f0f0000000000000ffff000000000000fafa05050000000000000505000000000000050500000000000000000000000000000000ffff0000000000000000000000000000fafaaaaa000000000000aaaa000000000000aaaa000000000000a0a0
|_,_=>0
def sP:Nat→Nat
|0=>0x34e10708664534428308134e10a1c260d3841c204b5c40c21803440963553841c218914428c0813844030812c429009438428224d3842830811441c22d31481c218d38448308b3444500861440863cd3843070812c42822452070861440c2040
|1=>0x84708634e1031c27cd38408119634e1070867cd38428709b34e10c1c20463841c280534e1101c250638448708614e10709f14d38478708634e10709d18d3841c218934e10708670d3841c22c63571100c218510218f34e1031c20461441c219a
|2=>0x34e1121c218d3841c22c614d1111c22c634e10708664d3841c218d54e10c08635738428308614d10708115538440308118e1231c218d3841c204d54e11008664d3841c218d88e10c1c280d38430709f34e1120c218d3841c280d38428308b344
|3=>0x10708634e10708614d38428708634e10708b18d3843031c218d3841c204b34e10a0c218d3841c26c634e1101c22c634e1031c22c63441c26c614d3841c218535738428708614d3841c2198
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579f3cdde60f297913c6de28f0d783b4059f4ef37763b95dbced77683b25d84ebb75a3ab5d4ce9f74c3a49918c8573f39ddce0e697
|7,0=>0x706374fb37d63e9233af958c6c6162fcf777b83da22c2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 36 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x18c071534e46391ce461d44dca391c64c1b0cd5b1c04e461534e471538d46301c54d3904ec6351c1463518c871534e471634e43041ce46351cb86391c58d3934e47351ce476e1854d3918387392cdc63940b06391cd43041ce46351c54e350c106351ce4d39406473528e461d1c54e35
|1=>0xd391c646390cd473918d46391ce461d1854d391cd46391ce46391854d391c58d391c64d392cdc63928d471918e4d391cb463918387391858d39307c71534e4d391858e356c6c13918d460e1ce47561858d391c54d391904735
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x79800186288000000e61840000008408800002
|6,0=>0x13ce70cc200000249c72886002114027a6e8db9b52664001892f2586a89412530008c9019e238464cb180000050800122
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xb2fb0f8b277f4033bb3af33f33b32f32d32313f12d1251051031011000e40c102e02802202001000c008006004002000
|1=>0xf2ff0fd07bab
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x240141000206000102001
|6,0=>0xb1830006c23c00445173470401c1447110001582055380002007
|7,0=>0xc89a8ca8214937dc79d656
|8,0=>0x1661f
|9,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_205 8 roots_205 ops++addP pm 1 dom_206 7 roots_206 ops++addP pm 2 dom_143 7 roots_143 ops++addP pm 3 dom_79 7 roots_79 ops++addP pm 4 dom_202 5 roots_202 ops++addP pm 5 dom_203 7 roots_203 ops++addP pm 6 dom_139 4 roots_139 ops++addP pm 7 dom_75 4 roots_75 ops++addP pm 8 dzo_205_2 8 roots_205 ops++addP pm 9 dom_197 7 roots_197 ops++addP pm 10 dom_142 4 roots_142 ops++addP pm 11 dom_78 4 roots_78 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_205_2_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_142 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_78 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_205 8 s (0,roots_205.map (·&&&dom_205)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_205 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_207==dom_207)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 10:=S_207.noCircuit
theorem lowS_215:Lower true dom_215 roots_215 goal_215 10:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_213
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=lower_slice_b [(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,8,10)] (by decide +kernel) lowS_217
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_slice_b [(0x33003300000000003300330000000000330033000000000033003300,64,72)] (by decide +kernel) lowS_213
namespace S_237
def pG:List (Nat×Nat):=[(1,5),(1,33),(1,65),(1,129),(4,5),(4,36),(4,68),(4,132),(8,40),(8,72),(8,136),(9,13),(9,41),(9,73),(9,137),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,96),(32,160),(64,65),(64,68),(64,72),(64,96),(64,192),(128,129),(128,132),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>4
|5=>73
|6=>157
|7=>86
|8=>21
|9=>4
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x38f3c11d030637704210
|5,0=>0xcc7b49ddbf865e08518684306811bb7b198761e36d81a6d1e26c694698a36471a60ebd5f6555d1585ce5159276554a0539a94d72e48518453d5430883dede3c9c83b8ee39a54380c136fa33649b324d431c0931a7c3189330e422d65f2b3a427998276c026d1e22bc6211d11ea621e2b81db061d1261c7c91a904182741463413b8d130db1281311aac116ef0fa3f0f03d0ed950c5110b6ec0ac000a67709267083d807c5d06a53067010554c02957020fc017730075d
|6,0=>0x51c0351a04518564e2ac4da8d4bd8c4b3cc4a6a94a5304a15a496b14890446f47467a44629646182444a841fde40fe1405364026e3e3cb3cd5b3c5d73bac43a3993a04337b933577334ff134e1e343c73393833163323213161e3134830c9230a0b309532d90a2d41e2bd072bb442ac092aaf42a99f29f60285cc28146271e3256512554124ad224a7a2211e217fa2119820e03207ea1f8301e4541e4531d3a71d11a1cecb1b05a1af671ac2f1a7831a1ab1949d18f8617fa01797d1762716e12169de15c6615c23159441502c1311c1303912cea1230511849108c410618103190fd000d97d0d4fd0c8dd0c6850bff70be090b3850b33e0af610af080aef10a9cb09999094b70931a09093087e20847d0845608031073b00722506db00698205e140590205886055ea051ef0442803a2d02f7a02c4c0220001f300075d00304
|6,1=>0xd829ebe4dbb7df4ac698a594a86bec8321f761e37192a6ffdd6e1816c0106851c661cf653a55f8ba5d1585a0e1592a25861e57a5f56d7756aa956917561b7543c9537d95299352384
|7,0=>0xf678bcacd1c4c16b5fc39a37479e0479d5f754226e0b26bd5766e0864b92647c963dc563bd460bcd5e6b25c9475c8915c3965a2f44d7594c719498fc443c742a7c3e6163c6393b0d7397a03688835ded3414c3149430395302702e90c2e2912d89b2cdf22cafd2c7122beaf2a5742721d25700251cb2227520f4520c501fd701f96b1e5831e4e91e22d1da2e1a1f119d2318cdb18a5d17fb817ded17c9214bf51398711af4107fd0e5050dcbe0d3a60c09e0acf30931a08fa908c64079ad0727805e42049d403f3902da202c4a028fa01477012b800d41
|8,0=>0x9cbe85fabc5229c5051840b31369d635a3c318072e8e92cfb9253c821aa22030e1b67a1445a12af60eadd0b90a098cb02daf014cf
|9,0=>0xc5173bd1585b33d43d29
|10,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc0000cccc0000cccc0000888800008888000088880000888800000000000000000000000000000003333000033330000333300003030ccc00000ccc00000ccc00000ccc00000ccc00000ccc00000ccc00000ccc000000003333000000000000333300000000000033330000000000003030cccc0000cccc0000c0c00000c0c00000cccc000000000000c0c00000000222200002222000022220000222200002222000022220000222200002222cccc0000cccc0000cccc0000cccc0000cccc000000000000cccc0000000333300003333000030300000303000003333000033330000303000003030cccc000000000000cccc000000000000cccc000000000000cccc0000000333300003333000033330000333300000000000000000000000000000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c333300003333000000000000000000003333000033330000000000000000cccc0000c0c00000cccc0000c0c00000cccc0000c0c00000cccc0000c0c330000003300000033000000330000003300000033000000330000003300cccc0000cccc0000c8c80000c8c80000cccc000088880000c8c80000888b33300003333000033330000333300003333000033330000000000000000
|0,1=>0x4044000040440000404400004044000040440000404400004044000040433330000333300003333000033330000333300003030000033330000303000440000004400000044000000440000004400000044000000440000000333300002222000033330000222200003333000022220000333300002222cccc0000cccc0000cccc000088880000cccc0000cccc0000cccc0000888b333000033330000333300003333000033330000222200003333000022220000000000000000000000000000000044440000444400004444000000033330000333300003333000033330000111100001111000011110000000000cc000000cc000000cc000000cc000000cc000000cc000000cc00000088000000000000000000000000000000033330000333300003333000022220000000000000000cccc0000cccc00000000000000000000cccc0000888b32200003322000033220000332200003322000033220000332200003322cccc0000cccc00008888000088880000cccc00000000000088880000000333300003333000022220000222200003333000033330000222200002222cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc0000000333300003333000032320000323200003333000030300000323200003030
|0,2=>0xcccc0000cccc0000cccc0000c0c00000cccc0000cccc0000cccc0000c0c030300000303000003030000030300000303000003030000030300000000cccc0000cccc0000cccc000000000000c0c00000c0c00000c0c00000000333300003333000033330000333300003030000030300000303000003030cccc0000cccc0000cccc000088880000c8c80000c8c80000c8c80000888800300000003000000030000000300000003000000030000000300000000cccc0000cccc0000cccc000000000000888800008888000088880000000333300003333000033330000303000003232000032320000323200003030cccc0000cccc0000cccc0000cccc0000cccc0000cccc00008888000088880000000000000003333000033330000000000000000000033330000303000000000cccc000000000000cccc000000000000cccc000000000000888b333000033330000333300003333000033330000333300003030000030304444000044440000444400004444000044440000444400004444000040430330000303300003033000030330000303300003033000030330000303000cc000000cc000000cc000000cc000000cc000000cc000000cc0000000333300003333000033330000333300003333000033330000333300000000
|0,3=>0xcccc0000cccc00000000000000000000cccc0000cccc0000cccc0000888800000000000000000000000000000000000000000000000333300003030000c0000000c0000000c0000000c0000000c0000000c0000000c0000000a23300002233000022330000223300002233000022330000223300002222cccc000000000000cccc0000cccc0000cccc000000000000cccc0000c0c333300003333000033300000333000003333000033000000333000003300cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000c0c111100001111000011110000111100001111000011110000111100000000cccc0000c8c80000cccc0000c8c80000cccc0000c8c80000c0c00000c0c333300003322000033330000332200003333000033220000330000003300cccc000088880000cccc000088880000cccc00008888000000000000000000000001111000000000000111100000000000011110000000000000000cccc000044440000cccc000044440000cccc000044440000cccc00000003333000033330000333300003333000033330000333300003333000022220c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0000080820300000203000002030000020300000203000002030000020300000202
|0,4=>0xcc0000000c000000cc0000000c000000cc0000000c000000cc0000000000000000000000033330000303000000000000000000000333300003030cccc0000cccc0000cccc0000cccc00000000000000000000cccc0000c0c000000003333000000000000222200000000000033330000000000002222000000000000000000000000cccc000000000000000000000000000088880000000000000003333000033330000000000000000000030300000303000000000000000000000000000000000cccc0000cccc0000c0c00000c0c000000000000000033330000333300000000000000000000222200002222cccc000000000000cccc0000cccc0000cccc000000000000cccc000088883030000030300000303000003030000030300000000000003030000000000000000000000000000000000000000cccc0000cccc0000cccc000000000000000000000003333000033330000000000000000000033330000000088880000cccc000088880000cccc000088880000cccc0000888800008888000000000000000030300000303000000000000000000000303000000000000000000000000000000000000000000000000cccc000000000000888803300000033000000330000003300000033000000330000003300000030
|0,5=>0x44440000444400004444000044440000444400000000000044440000000000000000000000000000000000000000000000000000000333300002222000000000000000000000000cccc0000000000000000000000000000c0c333300003333000000000000333300003333000033330000000000003030c0c00000c0c00000cccc0000cccc0000c0c00000c0c00000cccc0000c0c303000003333000030300000333300003030000033330000303000003030000000000c0c0000000000000c0c0000000000000c0c0000000000000003333000033330000333300003300000033300000333000003330000033004444000044440000444400000000000044440000444400004444000000000330000003300000033000000330000001100000011000000110000000000000000cccc000000000000cccc000000000000cccc000000000000000000000000000000033330000222200000000000000000000333300002222cccc0000c0c00000cccc0000c0c00000cccc0000c0c00000000000000000000000000000000111100001111000000000000000000001111000000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000000000000000333300000303000033330000030300003333000003030000333300000000
|0,6=>0x33330000333300002222000022228888000088880000cccc0000cccc00008888000088880000cccc00008889111000011110000111100001111000011110000111100000000000000000000000000000000000000000000000000000000cccc000000000000c0c333300003333000033330000333300000000000033330000000000003030cccc000000000000cccc000000000000cccc0000cccc0000cccc0000c0c000000003333000000000000303000000000000033330000000000003030
|_,_=>0
def sP:Nat→Nat
|0=>0xe5028f000852e181031128153a50c241085a28382562030710295040c1c1282418d1128153864c1c68814188940a9420622246a41400f071a8c2060e14f800818b0728147841c7838d1410385247420636683940a003940a3cc040e145170818b150e50291044078e1a286040608080
|1=>0x121c68a0080a054a1031104147b53444a0500719940a1032f1234500382429d0819007102950664543940a18a9112502865e0c48d14003944ec42061c983820a290070a48e862c543820a28f260e345000e0940a008038a601032f123440a00543940a0030e062468a084448d48b0515
|2=>0x1c1c6a41410d911250280641ca310818f0714a82060ef053008183820a8c206361c29d0819d911a2820622e828a0c70394621030322205210c8068a18103200e2160a42710051e842090eb052a081c29f0819c8714a8206729838d1418a870415c06120940a084413714188b60a28326
|3=>0x70103160e5029208193090e345040c688940a1030744145040c4448d0a28007049c53108181a01a282062c704820a282070a28b840c8038514742060e14fa108183a214a82060e15e38081838546842060e509310819f8728140060e298970819c871a282062c683940a1038a62f4206
|4=>0xc1c28f145c20664543820a2831c4044a050818e0704161840c804872814784062412458282390e0828a081900704151840c583940a103110e1490a4219f071a280040c68e0728140040e502c108183ac0a2a0040c5488904145061c803820a2821a22082920c708820a9c7860e0828f
|5=>0x541031a0e502a70818d110414500121c6a414002200e0829270181911a28006221c6c91418e3304145040c7838214b82063444105243c32f401c12c1410da00e502840d1c3940a103110414546007101104149063914a05081838578290840c722020a3c220121c105243c882101450c
|6=>0x1e280070a28e80081818904297040c8038210b05200e2028a4218e090415c040c710020a3c2390e3520a0818482481450c081ca054e942060e0828f9800d9c120828f08704820a9c004068010814003110e502cb0818f0322345040c2410514a4203120a50a08801051494206121c28a
|7=>0x10d200e082920c708820a3c0500e1454f0818a87041490a0c0c12414302065e241240a2821b12082a714110070af05040c1c105460020634548820a28303041450c0818707041450008803940a48339401c68a0818f111a282069a1c68a08197910e0960a006c88728140063444105
|8=>0x8183820a3c2353c98382102835412502840c808872814784381c10a6210307042988008181890490504220828aa618f11120828a00243ac0a290842c243820a282090e35208141038258151840ce43851484206401c292148430728149520818d8704147802a243940a1031e0e3560a
|9=>0x521031b222410514001871a282590ce43851500206721c6ac1410311120842c141ec05141030728149550cc838214c4206640828a4a103200e0960a5c1038578280040c1c28aac103070a2972a081838210b0555646c3940a1031e0e3520a0819c871a280040cf838d1410332121ca05
|10=>0x4b45040cfc3820a28006221c105157030704151840c0c12c14302064c1c1240a2835b0e345040c6c385145c2060e36d0a081848744145040c7838514842060e0958508183851474206121c28a2e103070a290aa0818d870415c040c444940a48316341c1051410e2028140040c70105
|11=>0x157c004381c1054e482060e3520a0818887042160a0c1c12c0a286040c6c3820a487840cc83820ae02065e2410514004820a2ab80401c28a2e10311120922c0a2838d102aa860e502a50819c871a282060e14538421031b0e14521081838d58286040ce41871a282062c703820a3c203
|12=>0xe0829215482060e0828a70002062a243820a282060e0828ac00031a401c10514103090e3428a00103820ab45040c1c12c1580206121c10514128b90e0828a081818705245040c803820a485063c444820a28206401ca05141031c0e082a70818d910e0828a0018d8704147840c1c105
|13=>0x220840a0cc8d8704145040c44482101450664243820a282060e0828ac41031a0e0828a001038d9228206a82410514103200e0828a5c10320221c1051e282030e3450008181c504145040c1c1080a2aa860e1452108181a0220828a081b08704145040c1c105154820640243851484206
|14=>0x5c0020606983820a28206221c6881418e07041478008444820a48506401c1054e282060e0828a4a0020634543820a2820636703940a1031c12502840d1438d0a282060e082921554307041450c08190110e3428a08197910e345040c1ca051412a86341c1051e280040e0828ac610303
|15=>0x4145040c803820a3c50008803825814504361ca050818d090e082920818d8728149040cbc38210145000c243940a48206221c124581450672243820a2820640243940a2820636703820a280063c1c10858282060e0828a70103071a2b0040ccc3820a28206121c10515042060e0828a
|16=>0x818d9c0e0828a0818e0904145040c1c1085828206121c12c0a2820728149040c7838258145040c243820a2800422241051401907041490a08190070a290840c0c38248280040cc8e0704145040cc900704145040cbcf0704145040cbc3820a280060e502a700103090e14521081b287
|17=>0xe09605141031c0e0828a08183940a28206121c10514103200e0828a0818382481450008183820a9c50008184871a145040c243820a485040c1c105cc282060e0828aae10307041454c0818f0704145040c2438210145040c1ca0514002068a1c1051410320221c10514103030e0960a
|18=>0x3820a28206
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xd5009400450004
|5,0=>0x180617a6174616e61686162615c61566150614b5145613f61396133612d61276122511c61166110610b5106510150fb60f560f050eb50e560e050da60d460ce60c860c260bc60b660b060aa60a4609f50996093608d60876081607b6075606f606a5065505f605a5054604e60486042603c60366030602a6024601e601860126
|5,1=>0x1b661b061aa61a4619e61986192618c61866
|6,0=>0x362735b7355634e73477340733a6333732c7325731e73177311630b630472fd72f672f062e972e272dc62d662cf72c872c172ba72b372ad62a762a0729a6293728d6286727f72787271726a7263725c7255724e72477241623a7233722c7226621f72187211720b620471fd71f671ef71e961e361dd61d671d061c971c361bc7
|6,1=>0x511650a750374fd64f674ef74e874e174db64d564cf64c874c174ba74b374ad64a674a064997492748b7485647e74786471746b6464745d74567450644a6443743c7435742e7427742074197412740c640573fe73f773f163ea73e373dc73d573ce73c773c073b973b273ab73a5639e73986392638b7384737d7376736f73696
|6,2=>0x5d075ca65c465bd75b675b065aa65a4659d7596758f75887581757b6574756d7567656075597553654c7546653f75387532652c6525751e75177
|7,0=>0x7a087997793678c7784877c8774876e676777607758875087488741773b6734772d7726771e871777107708870176fb66f386ec76e486dd76d676d066c976c186b986b276ab76a4769e6696868f76887680867886708668866176598652764b7644763d7636762f7628762086197612760a860375fc75f485ee65e775df85d78
|7,1=>0x846683e8837782f8827881f881788107809780277fb77f387ec77e667de87d777cf87c877c087b887b087a88
|8,0=>0x8de78d688ce88c778bf88b878b178aa78a3789b8894788d7885887e7876886f78687861785b6853884c7
|9,0=>0x8f978f278ec68e57
|10,0=>0x9006
|_,_=>0
def wAt:=mkWire dB 103 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2219081d3c1308195215223c0e1114190415101d0e190a11041558110e110a194e1f0a110e1922b0081d0a1908155a2922b0081d0a190aa51e440829081d14190e3d04291e1114190e110c1d041500150c11148a0a85400b001d381938110429141d3219223f081d14190a4d0e1112480c1d14110c110e15162912200e190a11
|1=>0xe49042914110e11042d12200c1d0a11400b2219081d0a11400b2219081d400b12110c1d04ba4017401512110e190e195215223c0e1114190ad5081d00700c11141d04d5081d00700c11141d087a0e1138000c290c11141d381904290e110c11141d0ed138020819041506110e1908190a1d001d08193413041506110c110a1d
|2=>0x341314250c1d721b401512110e191229081d0c1d14111e110e111419642b223d0e111419361b241d042914113c13041512150c1d0e110c710429141d400b12110e1904150e1108190e1904150e1512110e19361b3811141d640b12490e19141104e212110e19400b12110e197c0106030e150819042914450c110c1d64173619
|3=>0xe1912130e191419141d12110e191411481f10190a11640b223d081d6413223d0e111419042922190e11141d14d100730819141d121104290e1914190e1958110a190a1d110912230e190a11722b401512110e19361b0e49042914111411400b22190e1106030e150415042938190819141d0429124a0e191411720b22b10e11
|4=>0x4ba401712110c1d1e1d1e110429141938190e110c11141d0c1d041500150c11402b2219081d08190415081d0a1d0e11101b04150a11681d00730819141d0a25401712110c1d0e3d0e111419221522190e110a1904290c452229081d0f211e1304291419081d0a260e190819141122190e11141d0e290429221b0e11400b1211
|5=>0x402b001d0c11401712110e190a110c1512110c1d400b2219081d402b12110e190e290c2912110c1d0e910a0108190415481f0a0108194e1f0c49042914111419241f081914110e1908711419141d00290819141d0a1d001d08190429223e141906190415081d0a1d0e19223c0e1114190a1d58130e190a190e9e0e0100290819
|6=>0xc11141da21d00170c11641312490e1914110e9258110a190e19101d10190a110e4924190e1914111485400b12110e19722b0e91001534131e1d1419721f000d08190a1d721b0e9100150819042912110e191411401512110e1906190415081d0a1d04159c1906130a1d0a190a450e11042914450e110c111e1d0e11141904e2
|7=>0x141d0c1d0429042922190e11141964170071081964170071141d58110e190a190a1d081d000c0c110a1d08190a250c1d081d400b12110c1d0a19641b12490e191411041510190e190a11722b22b10e11400b12110e19400b001d0819141914450e110c110429086a12290e190415581d0c110a190829082512290e1914190e11
|8=>0xa110e110a1904b522b00e110a1904291411001f0c11641712490e191411641f12490e191411401712110c1d1485400b001d300bae19222b0e11401712110e190a190a11001f0c1136190e490429141104155811581d0a1906010e150819041506030e15081904153411042912290c1d38000c290c11141d3c1312150e193813
|9=>0xe9258110a1908b13c13581d0a190415881512130e19aa150415001f0c110a85400b12115a2922b00e110a191486400b12110e19640b12491411400b12110e19402b0c452229081d0429081d0c1d1411361b38113819141d0e010e29081904290e29223c0e11141914450c11081d0c1d720b12210e190a1122b10e110a190e19
|10=>0x58110a190e4914191411402b402912110e19101d0c110c1d0a1114460c11081d0c1d402912110e1958110e110a190a110415001f0c1104294e1f241914115e190e2104150a11402b12110e190415481f58110a19000d08190a1d361b0871141d0a1d22b0081d0a19097900720819141dba1122b20e110a19722b12210e190a11
|11=>0xe19124b0e19402b001d0c11086a12290e19101f0c110a11082512290e190e190819041522b00e110a190a19101f0a110a0208190e1912210e190a11101b0a110a1d12110e1914110a250c1d081d0e01081904291e111419141d14450e110c1122290e11141914260e19081924191411141d0a01081904150a110e110a19481f
|12=>0x2215081d0e02081904291e1d0c11141912220e190a110e110a110a1d36193811141d0e110e190a1112490e191411c019101f0a1138190819141d101b04150a1138130e19141d401712110e1922190e1114190e1508190415221b0e110a1d0a11001f0c11400b12110e1922190e110a1d0f25101b0a11124b0e191411400b1211
|13=>0xe1908250e19042938110c11141d581d0a110a19402b12110e190e2204150a11c81d002b0c11124a14114017001d0c113c1306190a1d04150e110a110c290c11141d081d0c1d14110e01002908190e9e0029081934133819141d38110429141d141d0c1d04290415221b0e111411001f0c11481f10190a11041522190e110415
|14=>0x1411581d0a1908190e190e1108190e1912490e191411400b12110e190e150015081900710819141d402912110e19061106190a1d0a450e110c11140108190429400b12110e19882912130e191419001d08190c1512110c1d0e490429141112290e1914110429241d1411101d0c110a1104290e19141158110e110a1908791215
|15=>0xa19141d04290e1912110e19001508190029081904150e190e191411241b1411222b0e11241f141106190a1d0e190a1108190429221b0e1122190e110a190a1d3811141d0e19141d0a110a190e190a190429
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x660000006
|5,0=>0x20907d5000000000000000000785000074400007131b8c0000000695000000019145f51694591000054513d44c311d40001148000110440400000000f880000f44385000034400000000c1000000002f10a942550000205071000000001750000134000000000000f4030c000
|5,1=>0x228c000000000000000002190000
|6,0=>0x5ccd7035b11684594d6145751594558d533540d4c4521144450113c44e113444c112d34a5125448511d4468d16444910e442910644090ff33ed0f833d4cf233b90ea43990e243790da43590d243390cb331d0c34300cbd32e50b542c8cae42a90a6428909f326d000025d094324108d3
|6,1=>0x961254494124c4921000091124138f523948d523148b522a389ce234880e1c4861214484120c48212044804dfd47e51f637ccdef47ad1e7478d1df476d1d83754dd230001ce47291c647091be46ecdb746d0db046b11a84694da2367919a4659193363d18b4620d844604d7d45e8d764
|6,2=>0x2b74acd2af4ab0ea93a952a14a7529a30002964a4ce903a312884a1128049f4e7949d500009c526e300026a49992633980e5c4
|7,0=>0xdd8f733dc0f6d3dacb683d94f623d7cf5c3d64f563d4cf503d34f4a3d1cf443d04f3e3cecf383cd4f323cbcf2c3ca4f263c8cf203c74f1a3c5cf143c44f0e3c2cf083c14f023bfcefd2be8ef73bd0ef13bb8eeb3ba0ee53b88edf3b70ed93b58ed33b40ecd3b28ec73b10ec13af8ebb3
|7,1=>0xee0fb53ec8faf3eb0fa93e98fa33e80f9d3e68f973e50f913e38f8b3e20f853e08f7f3df0f793
|8,0=>0x3e32f84bdf2f74bdb2f64bd72f54bd32f44bcf2f34bcb2f24bc72f14bc32f04bbf2ef4bbb2
|9,0=>0xfa07e71f987e51
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x2480012100088000438002100010140066000310001080008000022a001100004800021000102000800003c00015400080000300001400008400040000150000880004000010000050000200000c0000200000
|1=>0xf5a805a8002b6a0150400a00004ac00244001025007da803ad401b6a00cf50065e8032d40196800c35006080030100106800831004180020800103a00810004028020100100200800003da80140000968004a0
|2=>0x8408042000209681043c080000230040bb6a056a502ada8156400ab0a054b50267e8132d4098fa04c78026340131600987a04800023da811400088f00445d0222c0110000812a040800141080a0440496202411
|3=>0x400d8200040a09685043c2241a9030f4810e040838200281000b08005025db512a1a0936d44996a21cb510e5a0870d042c6820f35106da8832d440a682008510002080000288e81443c0867e8433d4219e810cb5
|4=>0x8065ac031d60187b00805803584016d600b2b0047d800143433d58801ac0cf56063ab030f5808e0c001050a1a2530512196a9043c424002102010296a81435407daa032d50187a80805401d8200cd50066080210
|5=>0xc2250e102570810384031c065ae020030010140c3da043ad020e28105b4042da00104912924196b144008a0184432f6098eb04c3582418c116d60860b040b180f5ac05a8202c61012b08075ac036d6019eb00cbd
|6=>0x348921a0cb5ca65ae520c32082190020c265ae132c70986b84c11c26086120c70904b844b5
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x20002
|5,0=>0x30000000000040000000f1100000000001e00130010240000040000435a2e160029765b3c006600053b00005b001642002200001700000d454000400c00001900090000001b5b00
|6,0=>0x6501af4d50000404a9218c1101b9092d01881a0c386f0e7a395cc924098254a41307181067240048783a2b950125181f2f250997110a8e686d6e4a47b32a44be104cc1088077b750908a063eac5801130cb5818b73692501751f5f7d99c4642698ba7e2401b025c88304015d28097561100b01b477251c3a7c126a00b246275e
|6,1=>0x4557b01808f5d30010014041d540a0711140132003206004131061001
|7,0=>0xc79cc6838427205796c69fc2c063b66356628315ca4fa5326b8606a89b7292ad2c79b663ae718532cd748db635591aaa0e35b86b9dbdc370548932bf359fbc24ab789a2ccc522389323dc5a6cb934e519e916c4b7f49
|8,0=>0xc78794b1a1345234a7a28d52c63f53a037a362a7bb
|9,0=>0x3633609f
|10,0=>0x32
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 21 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_229 9 roots_229 ops++addP pm 1 dom_168 4 roots_168 ops++addP pm 2 dom_232 7 roots_232 ops++addP pm 3 dom_204 5 roots_204 ops++addP pm 4 dom_205 8 roots_205 ops++addP pm 5 dom_173 8 roots_173 ops++addP pm 6 dom_172 5 roots_172 ops++addP pm 7 dom_233 8 roots_233 ops++addP pm 8 dom_169 5 roots_169 ops++addP pm 9 dom_105 5 roots_105 ops++addP pm 10 dom_109 8 roots_109 ops++addP pm 11 dom_236 8 roots_236 ops++addP pm 12 dom_201 5 roots_201 ops++addP pm 13 dom_104 4 roots_104 ops++addP pm 14 dom_141 5 roots_141 ops++addP pm 15 dom_200 4 roots_200 ops++addP pm 16 dom_228 7 roots_228 ops++addP pm 17 dom_225 7 roots_225 ops++addP pm 18 dom_108 5 roots_108 ops++addP pm 19 dom_45 5 roots_45 ops++addP pm 20 dom_77 5 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_104 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_229 9 s (0,roots_229.map (·&&&dom_229)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_229 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff00000000ffffffff00000000,96)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 73 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 73 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 157 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 29 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 157 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 86 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 86 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 21 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 6 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_237 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_237 roots_237 goal_237 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_237
theorem lowS_237:Lower true dom_237 roots_237 goal_237 11:=S_237.noCircuit
namespace S_249
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(8,40),(8,72),(8,136),(9,25),(9,41),(9,73),(9,137),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,96),(32,160),(48,49),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,96),(64,192),(128,129),(128,136),(128,144),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0x37bef
|9,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x303030300000000030303030000000003030303000000000303030300000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00030003000300030003000300030003000300030003000300030003000300030080808080808080808080808080808080808080808080808080808080808080b03030303030303030303030303030303030303030303030000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c000000000000000303030303030303030303030303030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x6b191ac688
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0x76
|_,_=>0
def wAt:=mkWire dB 7 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_248 8 roots_248 ops++addP pm 1 dom_185 7 roots_185 ops++addP pm 2 dom_121 7 roots_121 ops++addP pm 3 dom_241 8 roots_241 ops++addP pm 4 dom_233 8 roots_233 ops++addP pm 5 dom_217 8 roots_217 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_217 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 8 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_249 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_249 roots_249 goal_249 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_249
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=S_249.noCircuit
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_slice_b [(0x404040404040404040404040404040404040404040404040404040404040404,8,10)] (by decide +kernel) lowS_248
def isoMvS_126:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_123
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_95
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_123
def isoMvS_222:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_219
def isoMvS_235:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 10:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_125
def isoMvS_243:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_119
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000cccccc80
def gsh_93_2:=0x333333320000000033333320
theorem lowS_zo_93_2_69:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x330033000000000033003300,0,8),(0x333300000000000033330000,0,16)] (by decide +kernel) lowS_69)
def dzo_77_2:=0xcccc000000000000cccc
def gzo_77_2:=0xccc8000000000000cc80
def gsh_77_2:=0x33320000000000003320
theorem lowS_zo_77_2_69:Lower true dzo_77_2 roots_77 gzo_77_2 5:=lower_iso_b (d1:=dom_77) (r1:=roots_77) (T1:=gsh_77_2) [(dom_77,2)] (by decide +kernel) (lower_slice_b (T:=gsh_77_2) [(0x33000000000000003300,0,8)] (by decide +kernel) lowS_69)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000ccc80000cccc0000cc80
def gsh_109_2:=0x3333000033320000333300003320
theorem lowS_zo_109_2_69:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3300000033000000330000003300,0,8),(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00c800cc00cc00cc0080
def gsh_117_2:=0x330033003300320033003300330020
theorem lowS_zo_117_2_69:Lower true dzo_117_2 roots_117 gzo_117_2 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330000003300000033000000330000,0,16),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccc8cccccccccccccc80
def gsh_125_2:=0x33333333333333323333333333333320
theorem lowS_zo_125_2_69:Lower true dzo_125_2 roots_125 gzo_125_2 7:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33003300330033003300330033003300,0,8),(0x33330000333300003333000033330000,0,16),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec00
def gsh_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec
theorem lowS_zo_119_8_21:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00ff00fe00ec00
def gsh_55_8:=0xff00ff00fe00ec
theorem lowS_zo_55_8_21:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xcc00cc00cc00cc,0,2),(0xff00ff00000000,0,32)] (by decide +kernel) lowS_21)
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(4,36),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,25),(9,41),(9,73),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(32,96),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(64,96),(66,67),(66,70),(66,74),(66,82),(66,98)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>11
|6=>97
|7=>173
|8=>124
|9=>51
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xd58bdd4dccbe7cc7763376b427344469bdd4615e16ca1143e10e2bb
|6,0=>0xfc2afe04d8dd8ffd87a5d6c71d519dd1568d129ccb676cab85c1e0fc131ebebc7b528aac556a82929e30b9d6459c3e09bc0596862926af8d4388251c80627803e37e32d7a6707a51b79ec076ae87632c73bb06f1746ef306e6836e43f6da6f6cac56b81c6a6d06a671697ab68989687456412f630e05c49f58d635644753f5b4f4404bda1481e147def451ac43e3042cd03e97a3e11a3dd653bb8935fca326b031d1f306e33068d304492cf192c4f82bb8a2b79929d6624a5b22e4022bfc21bfb1c3e619b8918b3618a8315a1915474145a30fd830fd590ad3c095c30768306b92064f20507703494031f302b80029180115e
|7,0=>0x8344a81e0c7f7dc7d5827d5587b4077b072799d07996e7756b75b55736ee7205c71e1870cb570528704296d98a6d94f6d5596cb796a8726a6d0685826783666bc265e0f65a026568e629d1617f560d045f3875eec85d58d5cb945b6c65abd55a9f559a8c56e4356bc355f7255eda5495c53e6b5283b512484c70b4a9be4976a48d1c48b35475144745945bb8447ff43939411574103b407873fc963cb983b6153aa003929738cf5387b9378203746236faf36efc360c83588932e87321eb31c3831a4131942316fe2daba2d3cf2c7e72c4272b21928a722843c280db2794321a86203e11f51d1f2ce1ec731dfd11d60d1d3a91cbdf1bf0e180dc15e7512f3712c6b129451256c125531119f0f03b0ca4c0c4ab0bb110bac50afeb0a56b09ff90989a0862807938070b10668f0637c05ac505a68059f90580002d490225a002c1
|7,1=>0xff197fc2d5f3be7e468fe33c0e2d54dfa62d9b59d8002cf327cf0e3cafa7c79afbd7eeb8172b0626af43eacda6ac471ab17aaa13da7a3ba7069a6578a5ed8a5ba8a32aba2e7aa1e7c9fda99f2c89c6d09bdf29b83b974ae93ed2934808be568a5728a32e8684085ffb8550a84dc983734
|8,0=>0xfcafdf6acfe97eee7577dfb74da03ed954dd8292d220fd1fcbcf79dcd825c7ac1bb879b5f52b2f0bb0bd7ac6eba9f51a731ea5d62a4009a288ca1f77a11ef9e7239df489cb789c6ec9b55799ad99627b90ee48d2da8ca958bfa48b8638a2aa88ee38515684cf482f6581b0c8046a7b4da7a188777617774f7442473410729917130c70b556ea216c8786a71e688ea655226402761db060d795fa7c5d8dd5b5815a8de5784457532547c54dfae4d4f04c6524bc5d48d144805e472214673041dfe4149a412f23f78f3dde13da493cdbc3cb623c3233b7333b1d93a13b39c7338c85386d2383e437ec93755b36f1033f3f33aa52e1012d11d2cf5c2852026a532570d23e4320eb91e7211ba42199d118d9f13c4c134e61255f11e44105260d3350c55f0ae50093d908e160721c065a805c310446d032fb
|9,0=>0xfa1a9f96b8e9b32d68f1c08bbbb6c2b601ab2c55a4e5f9cd159a2ee9797e917868f97d88757883e67e1fb7942b73312719096f76069a56613785dfcc5b25f5529e4c0d14a76644cca42e8740bd53e9633e88c3e2c43e0c13cb5b33bb7291b8224dc1fb671b6f51b4f01914a118ea0fe730f8b00b65c0b3ce0a104032b5013a2
|10,0=>0xe0a26a0d88761fa581863fcd23b65b2fbbe063e4
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffffffffffffff0f0f0f0f0f0f0f055555555555550505555555555555050ffffffffffffffffffffffffffff0000ffffffffffffffffccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0affffffffffffaaaaffffffffffffaaaafffffffff0f0f0f0fffffffff0f0f0f0ffffffffffffffffaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000fffffffffffff0f0fffffffffffff0f00000000000000000ffffffffffffaaaaffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00fafafafafafafafafafafafafafafafacccccccccccccccccccccccccccccccc
|0,1=>0xfffffffffffffafafffffffffffffafa55555555555555555555555555550000fffffffffffffffffffffffffafafafa0000000000000000fffffffffafafafafffffffffffffffffffffffffffff0f055555555555555555555555555555050555555555050505055555555505050500f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0affff0000ffff0000ffff0000ffff0000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffafafafafafafafaffffffff00000000ffffffff00000000ffffffffffff0000ffffffffffff00000000000000000000fafafafafafafafaffffffffaaaaaaaaffffffffaaaaaaaa
|0,2=>0xfffffffffffffafaffffffffffff0000fffffffffffffafaaaaaaaaaaaaaaaaafffffffffffffafaffffffffffffffff55555555555550500000000000000000ffffffffaaaaaaaaffffffff00000000fffffffffafafafaffffffffffffffffffffffffffffaaaaffffffffffffffffffffffffaaaaaaaaf0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f5f5f5f5f5f5f5f5f5f5f5f5f5f5f0f00000000000000000fffffffffffff0f0fffffffffffffffffffffffff0f0f0f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0affffffffffffffffffffffffcccccccc0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0afffffffffafafafafffffffffafafafa
|0,3=>0xfffafffafffafffafffafffafffafffaffffffffffffffff0f0f0f0f0a0a0a0affffffff0f0f0f0fffffffff0a0a0a0afffffffffffffffffffffffffffffafaffffffffffff5555ffffffffffff5050ff00ff00ff00ff00fffafffafffafffa555555555555555550505050505050500000000000000000fffffffff0f0f0f0000000000000fafa000000000000fafaffffffff0000fafaffffffff0000fafaffffffffffffffff0f0f0f0f0f0f0a0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a000ff00ff00ff00ff00ff00ff00cc00cc00000000000000000f0f0f0f0f0f0a0a0000000000000000555555555555505005050505050505050505050505050000
|0,4=>0xafafafafafafafafafaaafaaafaaafaa000000000000ffff000000000000f0f0ffffffffffffffff0f0a0f0a0f0a0f0afff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f0fffffffffafafafaffaaffaaffaaffaaffaaffaaffaaffaaffffffffffffffffff00ff00ff00ff000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a000000000000ffff000000000000aaaaffffffff0000ffffffffffff0000aaaafffffffffffffffffefefefefefefefe0000ffff0000ffff0000fefe0000fefe00000000000000005555555550505050ffffffffffffffffffccffccffccffcc555555555555555555555555505050500000000000000000fffafffafffafffa
|0,5=>0xffaaffaaffaaffaa00000000ffffffff00000000f0f0f0f005050505050505050500050005000500fffffffffffffffffffafffafffafffa00fa00fa00fa00fa00fa00fa00fa00faccfeccfeccfeccfeccfeccfeccfeccfe5555555555555555550055005500550000000000000000005550555055505550ffffffffffffffffffaaffaaffaaffaa0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0afffffffffffffffffcfcfcfcfcfcfcfc5555555555555555545454545454545400ff00ff00ff00ff00aa00aa00aa00aaccffccffccffccffcceecceecceecceeff0fff0fff0fff0fff0aff0aff0aff0a0f0f0f0f0f0f0f0f0f000f000f000f00
|0,6=>0xfafafafa00000000fafafafaffffffffffffffffeeeeeeeeeeeeeeee00ff00ff00ff00ff00f000f000f000f0
|_,_=>0
def sP:Nat→Nat
|0=>0x240c1012a304920608a150024908043c0072474e022a00589244c1112a30908043058a2c481822a3058e1a489822a30d0d2408780166448d100808c12344022800902001c3180a2418202302890608a000a249822230492100888c1a4010f0038688043058a12201000e182840608080
|1=>0x3258693043c00b1c48182001c5a1240c115001c50d2408a8c166128926080802c94910040401612492022a00385120c115182c688040058a2c24903045402324881112a30592100800b4258920380878016149821e0059e3e349822a30585124c10f001c908043c00b3c208170444609
|2=>0x10087801649010043c0070aa49820200b0524ac101005828d20087801634913049c60b24a8115182d49210080802c14903040400724714022a005891a2010f002c48804005862c488021e0071624814021e0059226093803c5848d260808f0034910040478024401262a00b12045401e
|3=>0x1234982025460d24401012a3048d2608a1500349100450a801a490021e005892420111005891004540302c48982002d0961a4c115182c71f240c10f002cd892608a800e6c91004540075e481822a00592060878016197122608a8c16b4903045400b244011500b0b124070115182c91c
|4=>0x45460b3e481822a30584240c1012a0090804005b22c48802225461f244c10f001d492260808f00149280404016249040202003851280101005848d2608a8046349100454023240c115002d8891a20115182c28906080802c49402023c0123840115182c28926088802c94483045400b
|5=>0x244c1150068b1c265c115182d2132e080800e3491304540342c48e022a305851a4c10c16182890608780162468804040161a48402182c3132e44a8c16cc920043c0073e349821e00585124c10118582892608a002c24908040461612484022800b12200879500797922608a8c1634920
|6=>0x4e0059624e0101002cb08205c1110058e9c265c115002c91d4808a801658936045400b2c249030404a802c24913049c00b2c80e032e08a801694913040400b2c2490804040160a109822a0059610a0817043c00b124898222540162440115008cb120608a801638b122608a8016d4b0d
|7=>0x1e005a2265c1112a30585120c115002cb125008795002c9977408a8c162019704005b92490101002cb09244c1011e00b20384cb821e0059226087801638b0d244c1011e005924008a800e58f8d2608a8016589130498a80165849240080950058292260800b0c5828926080802c48982
|8=>0x24e0115002cb124820115001c5924008a8c1658692260878016182892608780165829220087801659c102e080802c4cb812a305b32cf0913045400b2c708032e08a80166c6922608a8c1621417040401676489822a0059612484021e005961a48115002cc162420101001cb20200cb82
|9=>0x7e087800e34908045400716a4913049c00b2c4840202305962420114002cb122608a800e78b29244c10f2a005923a80115002cb032e087801664910043ca800e814132e0878016804032e087801614928045400b2c48115002df16244c115002d91624a0802025401624f4115002cb09
|10=>0x2cb122608a8c1638b052608a801678b1c104cb821e0058d244c1012a3058d244c1142a005a0204cb821e003922608a8016c0b121008a801678b051a4c115001c5aa265c115182c908040058a2c249030454007240c1011e005922608a801668b125408a801658e28265c115002c997
|11=>0x12481822a305892420115182cb0d244c115002d1932f00115182c492260800b4258d920608795002c4102e0808c2c2081704500165c489822a005964040197045460b24748022a00596065c115182cc09244c1012a30b09244c1142a00b20384cb822a305a9244c1150078b124070115
|12=>0x2a00596244c1011e003932f081112a3059f24401012a00b1240a0115002cb091a4c1012a00b0d24401012a00b124408095182cb0d244c115182c305124c115182cb12404010f002cb09240c10f2a0058d2608a801638b09244c115008cb12045400b825891304005a12c401970404780
|13=>0x404007244c115001c58610a0b821e0059b124c115002cb1b2440115002cb12043c00b32589030404a8c1648182285400b24804021e005961a492021e5400b2518115002cb122608895182c913040038b4258e10265c115182c48d1008a8016589822a305c42c48115002e1962470802
|14=>0x24808022a305963e481822a005962408a8c1660b0d242010f002c8032e0809518401970450a801040b821e003a0065c10f002c428205c10100588132e088951848402002c31612489821e5400724401112a00b29244c1001684b129608a801658997925460b90481822a005a34820997
|15=>0x3e489822a30596265dfc92a305a0065c115182c28d260800b0c5891d045400b2c94903045400b1a48402002c316404cb821e003891a4c115182c6922008a8c166c913040400b2c94910045400b2c7c913043c00b2cbc913045400b2c2469304540071a490022a005965a489822a00596
|16=>0x9c589972a305b32ce0997040400b2c752132e08a801658d85244c115002cb132e08a801734b10065c10f2a00590265c115008cb12045400b32589201008a801658924043ca8016588032e08a8c1620817045460b2c70997045400b2c489822a005b92c4cbcc043c0071648e022a00596
|17=>0x2cb132e08ad216582922608a800e2cb132f44115002cb25244c115002cb1b1a489822a00596242010f002cb132e08a800f20b08265c101001cb132e08a809e2cb28265c10f2a005a4265c101002cb132ee8115002cb122608795001c5925008a8016590132e08a800e58913045400b
|18=>0x2cb1d404cb822a005961a489821e5400b204cb821e54007265c115182ea16265c115002df163e24913045400b2ca08132e080950059e932e08a801658913045400b0c586922608a8c16488020254016265e6492a305a4104cb822a0038b404cb822a3059652489822a0059624e0115
|19=>0x65c115002cc164070997045400b2c7c9130404a801658910043ca8016586922608095002cb124408a8c1658910045460b2c0c997040478016a4913045400716595132e08a801658997045460b9058997045400bac58428205c115002cb08265c101182cb08265c114002cb1f244c115
|20=>0x265c115002cb124008a8016591132e08095182cb20204cb821e005961a489822a005862c481821e5400b265c115002e096265e615002ec96265e482025460b240c115182c4920608a8016589978008a8016589977e087801658e90265c115002cb20200cb822a00596265c115002ec16
|21=>0x404780165899704047800e49410045400b2c49002025400b2c4cb821e005992c0c9970404a8c160c9970450a8016804132e0878016589970514a8c16589030404a801658997b808a8016589130444a80165842b2e08a801658997045400b8658e10265c115002cb132e08ada1659028
|22=>0x244c115182cb05124c115002cb20204cb822a30596265c115182cc1612484022a00596200cb8202540161040b820200b10265c1112a00b132efc115182cb4b265c115002cb132e08895182c49226080950058997925400b90581932e08a80168c4922608a800e58913045400b1c58913
|23=>0x2e08a8016589977e08095002cb09244c115002cb122608a8016dcb132efe495002cb1d265c115002cb20065c115002cb08065c10f002c9130404a8c16589130450a801658997045400bba5848d2608a8016586922008a8016589978408095182cb08505c115002cb08205c10f002cb09
|24=>0x1c5932f5c115001c5961a489822a00596265e6492a00596104cb821e00596265eb822a00596504cb822a00596244c1012a00596265c115002f016244c115001c596265ef822a00596265c115002cc964020997045400b2c90997043ca801658997045400b4658997045400bbc58803
|25=>0x2cb03265c10f2a00583265c115182c9979208095002cb120608a8016589979408a800e588132e08795002cb22265c115182cb10265c115182cb132f24115182c4102e08a801658997045400bb6589979808a800e2cb132e08a801740b10265c1012a00b38265c115002cb132e08795
|26=>0x16589970450a8016589977e08a801658997045400bc458913045460b2c4cb82023c00b2c4cbc2045460b2c4cbcc945400b2c4cb82225400b2ca08132e08a801658910045400b2c809970404a801658997045400b90581932e08095002cb132f28115182cb132e08ae1182cb20265c115
|27=>0x4cb822a00596265c115182cb10265c115002cb03265c115002cb132f24115002cb132e08095002cb132e08a800e2cb132f30115002cb122608a8016589970404a8c
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x3c60366030602a6024601e60186012600c600660006
|6,0=>0x1f971f271eb71e471dd71d671cf71c871c171ba71b371ac71a5719e7197719071897182717b7174716d7166715f71587152614b7144713d7136712f71287121711a7113710c710570fe70f770f070e970e270db70d470cd70c670bf70b870b170aa70a3709c7095708e70877081607a7073706c7065705e70577050704970427
|6,1=>0x2dd62d672cf72c872c172ba72b462ad72a6729f72987291728a7283727c7275726e72677261625a7253724c7245723e7237723072297222721b7215620e720772007
|7,0=>0x4c584be74b774af84a7849f849874908488848174798471846a7462845a8452844b7443843b8433842b8424741c8414840c840573fd83f583ed83e673df73d873d173c983c183b983b183aa73a2839a8392838a8383737c7375736e7366835e8357734f8347833f8337833073288320831883117309830182f982f272eb72e38
|7,1=>0x6b176aa76a2869a8692868b7684767c8675766d8665865d8655864d8645863d8635862d8625861d8615860e7607760075f975f185e985e275da85d285cb75c475bc85b485ac85a5759d8595858d8585857d8575856d8565855d8555854d8545853d8535852e7527752075197511850a750284fb74f384eb84e474dd74d584cd8
|7,2=>0x80077f887f177ea77e287db77d477cc87c577be77b777af87a7879f87978790778887808778877087697762775b7754774d7746773e873777307728872177198712770b770476fc86f486ed76e586dd86d676cf76c876c086b88
|8,0=>0xa0089f889ef99e699de89d599ce79c779bf89b699ae89a6899e8995998d8985897d8974996c8964895c8954894b9942993a8932892b7924791d7914990c890488fd78f678ed98e588dd88d498cd78c588bd88b588ad88a5889d8895888e7886887e8877786f8866985d9855884d8845883e7836882e8827781f8817880f88078
|8,1=>0xbe18bd98bd18bc98bc27bba8bb28baa8ba28b9a8b919b898b818b798b718b689b608b588b508b497b418b398b318b2a7b228b1a8b128b0a8b028afa8af37aeb8ae38adb8ad38acb8ac29aba8ab28aaa8aa28a9a8a928a899a827a799a727a699a609a579a507a488a408a388a326a2a8a228a1a8a119a089
|9,0=>0xd7e8d768d6e8d668d5f7d578d4f8d478d3f8d369d2f7d269d1e8d159d0d8d058cfd8cf58cee7ce59cde7cd68ccd9cc58cbd8cb67cae8ca68c9d9c958c8d8c858c7d8c749c6c8c648c5c8c548c4c8c448c3c8c348c2c8c248c1b9c129c0a8c028bfa8bf19be98
|10,0=>0xdbd7db58dad8da58d9d8d958d8d8d867
|11,0=>0xdc47
|_,_=>0
def wAt:=mkWire dB 99 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x241d1659265d265d265d265d20552059262d265d265d1257242d265d265d265924550059242d265d2a1e1659265d26310059025b2a2d405b1255242d265d265d26551a2f025b262d0059265516550059242d265d26592a2d02592a2d265d025b0059362f1a552459102f265d265d0e55165924550059242d265d265902592a2d
|1=>0x242d265d265d265d1659105926552455242d265d26052a2d2a1e16592455242d265d26592a59261d2a2d1659265d265d2a2d0059265d02592a2d1e2d2a59102d2655025b16552405265d16551a552459265d243d2a59265d00592055262d2a59265d241d1659265d205b2455265d24552459262d265d005952541a2d2459265d
|2=>0x2455265d14591257242d265d362f1a55265d0059405b26052a2d263d2a5916592a2d362c1a552459265d265d265d00592459265d2a59102d26551659265d0a2d2455265d24550059242d265d1e2d2a59242d16550059265d0e5516593e5b00592055262d24052a2d26590059265d025b2a2d0059265d262d1255242d265d1259
|3=>0x26052a2d36570a592455265d24552a2d242d265d52541259242d265d265d105b265516552655025b262d2a2d405b405926052a2d265d1059265526dd2406265d2a2d242d265d26592a2d52541259265d405b2055262d0a5b2455265d2a2d2655242d265d125b242d265d2a592059262d025b2a2d262d265d2a1e165926590a2f
|4=>0x163e2a59242d26552a59265d24592057265d262d165526551659265d2a592055262d26310059025b2a2d26592455242d265d2059262d2a59265d04450059025b2a2d1e2f2a5926592655263d16552a59265d2a59265d405b260516550a2f2455265d1655265d102d26551659265d1255242d265d2a791a2f2459265d242d265d
|5=>0x20552059262d102d2a5926592655261d1659265d30592057265d262d123f2a59242d265d2059262d2a2d265d268d2a1e1659105b2655242d265d105926551659265d20550059265d262d1a572459265d265d2455262d2a59265d262d105b26551655440b263100592a2d405b2055262d00591a552459265d062d165526592655
|6=>0x26450059025b2a2d26551257242d265d26591659242d265d265916552a59265d362f0a592455265d265d2645025b2a2d3a5b50552059262d16592a5904051655245926551659265d525416550059265d26550e5526551659265d522f241d1659265d1a2d2459265d265d26052a2d2a59102f265926551659262d2a59265d2a59
|7=>0x2a59265d262d005926551655262d025926551655205500592659262d005920572659262d2a2d0059242d265d163d2a59405b005926052a2d16791a2f2459265d265d405b26052a2d00590a2f2455265d1a2f2459265d405b102d265500592a2d2459265d1e2d2a592a592055262d161a1a572459265d26551a2f2459265d265d
|8=>0x265d20552059262d265d2a2d2459265d262d2a2d26310059265d00591a572459265d24550059242d265d2055262d2a59265d26592a59242d265d0a2f2455265d2a1e1659265d482f1059265552571259242d265d2a592a2d2659262d242d26590059265d242d0059265d26552a1e16597e5b005904052a2d52571259265d243d
|9=>0x243d262d2a59265d265d102f2a5926552a2d26590059265d0259265d26592a2d265d102d2a5926552459263d2a59265d271d241e1659265d265d0059025b2a2d5257241d1659265d405b20550059242d2459265d26552f16023100592a2d101f26551659265d405b2055265d262d165916552a59265d0059025b2a2d24052a2d
|10=>0x265d26590059262d2a2d02592a2d2659262d26552a591659262d102d2a592659265526552059262d2a2d262d0059025b2a2d26551a572459265d2a59265d265d025b262d2a2d52571259242d265d265d5655205b262d005994570459042d2659265d2a1e16591659105926551a572459265d062d2a59265926551a552459265d
|11=>0x2459265d203d262d2a59265d26590a5b2455265d1a572459265d26552a59165926052a2d00592459242d265d24590059265d262d243d2a59265d262d0a5b2455265d24051655265d3e5b1255242d242d24591659265d2055265d262d4a2d0a5b245520550059265d262d2405265d26592a2d20570059265d262d265524592a59
|12=>0x243e2a59265d440b26310059105b26551655105926550a592455265d90599457042d2a592659262d262d2a1e1659102f265d2655102d265d2655263d2a59265d00592659262d00592655262d405b26052a2d265d163e2a5916592a590455265d405b26052a2d00591255242d265d0059045904052a2d205500592659262d1a57
|13=>0x265d265d262d2a2d045900590455105916592655005926052a2d1259242d265d105b265d2655014d041e165916592455265d048d2a1e16590a5b2455265d1a552459265d26552a59265d94571659042d165926551655174192570459062d2a5926591059265516550445025b2a2d2a591659265d261d1659265d165926052a2d
|14=>0x2a2d2459265d26310059265d0059265d262d2a5926591655241d1659265d2645025b2a2d94570059042dae579459042d20592655262d0059265516550259265516551255242d265d26052a2d24592a59265d2a591659262d17561855005930592057262d1255242d265d2059262d2a2d268d2a1e16591a572459265d00592459
|15=>0x262d016d04062a2d20552059262d265d26052a2d263100592a2d20552a59262d1a572459265d26592a59265d482f10592655922f04590455005904592a2d26590059265d2659242d265d7e5b04052a2d2a5904051655203d2a59262d20552659262d981f1659045520572659262d405b26052a2d2405265d2a2d262d2a59265d
|16=>0x205b262d0059025b2a2d2a2d242d265d94570459042d26592a1e16591659242d265d0a2f2455265d16552a59265d16592a5916552059265d262d265d26052a2d102f2a592655005926592a2d025926592a2d102d2a592655023100592a2d265d26592a2d7e5904052a2d265d025b2a2d205b2655262d101f16592655405b2055
|17=>0x45904052a2d405926052a2d20552659262d2a59265926552a2d0059265d2a1d1659265d920704592a2d2459242d265d2459265d262d2a2d04310059062d265926552a59262d26550059242d265d2455242d265d20550059262d00592057262d2655242d265d2a2d2659262d2655262d2a2d025b262d2a2d005904052a2d5655
|18=>0x26591659042d2a59262d263100590059262d045900592655262d04062a2d1659045592570459262d2a2d105b26552a591659041d16592459265d045904552a5926559459042d2059262d265d2a2d043e2a591659265d945b042d102f2655102d2655263d2a592a1e1659263e2a592659262d04052a2d242d265d2406265d2a2d
|19=>0x59262d265904592a2d16590455265d00592a2d02592a2d04052a2d26062a2d0059265d2a59165504310059042d0455025b2a2d2059262d265d262d26052a2d9457042d26592a2d0059042d182d005926052a2d2a5926590059265904592a2d265d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2440390000004a00080000000000000000000000
|6,0=>0xd02194c31906120be4174800000000000168c2b985430000000029880000000000000004f40986124c22a040500000f4c1e0800007620000000037400000d841a88000000000000000332000000001908311058a00001510255000009040000213040207880ca81450244044400000f20000000006900a3
|6,1=>0x2a845488a63000028544f189a41304251049100001204238844a80000000211440987e30fa21e503a280000e44000000006e40d2a00000000000
|7,0=>0x31266150c0a17d42f285d8cb9216f32d6859d0b1a15f42b68560cab8953429e852d00001483288850109f113a426c84c9097992b424e848d08fa11b422e8454889190f321a4425083190241fc83e907b20f241dc83a907320e331be836d06c18d531a4633906598c8318c430905f20ba416e62cd057a0ab4
|7,1=>0x4c8898112e225934aa8945126a249448a8908d20123c447628dd119a22f4456889d111a220343c486910b2212441c88291041204440267f8cfd21f6400007c900001ee43d487a08f221e043b887610ea99d2339c87308e499c5438287004de21b8436886c10d621a8434886810ce219b132e864d0c7a18c3
|7,2=>0x30d46128c15180a2fe35f48bd917922ee45d48b991719adf45b86b64d6aa2d2359e6b2d163a2c3457e8aed15ba2b3455e8aad153a2a345424a7514ca29545228a351451a8735068a00d3e227844e889c113622684
|8,0=>0x7986f24de31bc337806ef4ddd1bb737686ec4dd71bab37506e94dd11b9f37386e689cb9b9437226e38dc59b88370a6e08dbf9b7c36f26dd8db99b7036da6da8db39b6436c26d78dad9b5836aa6d48da79b4c36926d18da19b40367a6ce8d9b9b3526646cbcd961b29364c6c8cd901b1d36346c5cd8a1b113
|8,1=>0x90071f4e3d1c7738e871c4e371c6b38d07194e311c5f38b87164e2b1c5338a07134e251c4738887104e1f1c3b387070d4e191c2f385870a4e131c2338407074e0d1c1738287044e071c0b38107014e011bff37f86fe4dfb1bf337e06fb4df51be737c86f84def1bdb37b06f54de91bcf3
|9,0=>0x139ca7294e329c2537ca6e94db29b2535ca6a94d329a2533ca6694cb2992531ca6294c3298252fca5e94bb297252dca5a94b3296252bca5694ab2952529ca5294a32942527ca4e949b2932525ca4a94932922523ca46948b2912521ca4294832
|10,0=>0x9e033bc6770ced19d833ac6750ce91
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0xc100000000060000000000200000000000ca0000000006400000000030000000000150000000000980000000004b0000000002400000000011c0000000008a00000000044000000000200000000000a4000000000500000000002500000000011000000000084000000000400000000001c0000000000a0000000000400000000001e0000000000c0000000000400000000001400000000008000000000030000000000100000000000400000000000
|1=>0x81050000000400600000001100200000004e9800000002344000000010260000000081100000000400100000002000000000008068000000040200000000200a00000001002000000008008000000040000000000189900000000a08000000004a6400000002530000000012880000000094000000000426400000002130000000010800000000080800000000400000000001c100000000088b000000004040000000018200000000080000000000280
|2=>0x614698000002d0264000001441360000009389b00000048c6d80000024026c0000012012a0000009001d0000004084d800000200b64000001001b200000051a990000002874c800000142004000000a00a00000004880100000021000000000104a4000000080200000000400de0000002002b00000010014000000048108000000240800000001200a0000000900400000004800a0000002400000000010e4c800000080000000000210000000001044a
|3=>0xa840c000000504a6000000282520000001410980000008900d800000446a40000002219320000010189d0000008094c000000404a200000020210000000100c9b0000008014000000040020000000200020000000f489d0000007844c800000346a64000001a3132000000d0e990000006864f80000034326c000001a1932000000d0a9f0000006854d800000342a64000001a11b6000000d089d0000006844d800000342264000001a0162000000d0099
|4=>0x16844e800000b4226c000004e393200000251c1000000128d4e800000943a740000044002800000210e99000001084658000008052600000040202000000200c9c000000e8d4f800000746a74000003a3536000001d1a99000000e864e800000742a7c000003a153a000001d089f000000e844e80000074226c000003a1132000001d0819000000c8d4d800000562000000002a353200000151a89000000a8d40000000546264000002a1d3a00000150c99
|5=>0xc0000480000574266c00002aa02240000150211800000820445800003000008000011840360000088029b0000042004f00000200020800001000100000008000100000040000600000200001800000ba4036000004d2c9b0000026946980000134a26c00000801036000003d089d000001a864e000000d0224c00000621c08000002d1cdf00000168e4e800000b4637c000005a313a000002d0c9f0000016864e800000b42a74000005a1196000002d089f
|6=>0x800034c000028746a64000143a193a0000a1d089f0000506874c80002834326c000141a19320000a0d0a9b0000506854c80002834234c000141a11360000a09289a0000504060f000022202a64000102a313200008150e18000040a844c80002050626c0001012353200008051a99000030c840c000010200000000043a113a000021d081900001088d4c0000083422640000412103200002010e1800000e6900d80000634226c0000300090400001800016
|7=>0x8200010800040f4227c000207a113a0001035089d000081a8440800040d42024000205a113a00010250a9c0000812040d800040844810000202a313a000100d4e9b0000806a74c80004034227c000201a113a000100d08990000804a74d800040153a64000200a9d3000010051c1800008028c4c800040143264000200a15320001004468800008009649800040043a2400020021c30000100100510000800234c00004000306c0002000153800010000a9b
|8=>0x100006844c806000342264020001a1132009020d08990040100844c802008042064010005a113a008001d089d0040006844c80200024226400c841b1136006020d88990030102444a001808022240006141a0132001880100810008106c04c80012834a348000941a51360004a0d08db00010d0004400008480032000040400090000200400100001000004c00008000006000040000024000200000100001000000100004134a34c000209a117600010450076
|9=>0x400c283422650040c1a1132802040800943100806844e902408742274812041a1132408001d089d2040006844c900000342264470003a1132231021d0899118000c844c88a408342264450201a113a228000d089910c0814844e886040342274410001a1132181000d089d0808006844c820c2834026408000000000030001d089d018000c844080a40834226405020121132028000d0899
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x80200038040000000000000
|6,0=>0x80404000ac24070081402000e8303c000008c3c0a0109c7c000080000071280000000100c0201060040000000480c06000003a0000000002002018261000010043701000001300008040000000002100000040203800023d000980012010308205008088831000001804
|7,0=>0x2ca20a2710b440ae2932329743901056241b038ac101219174c2a96a0d81ac51aac99efb0e9d884c41a0c8e4ff16ad0087225834e64a078090cad73a5210601c48c2209672a9c80a243b1c2183f2cd704f1d968162f6686c04b64205a4a2884b9a0617839e05650038f19698218cceab5070b825061fafd7260181e48a462c0d06a2b5a1ec08221938182190d149381b
|7,1=>0x550f46d8e052f2ec28838735a08c00f134be1a268b03ed24bb41f4f63d37cfe24199d014568d3892a107281a0a2a69bdc9c40
|8,0=>0x46458e08553b71fd325799670ee4dc3586776bab90292404c0ccc858c59d502612b1faf449badbafc3ec98d71745150da7c940e90f133b871486f8b4d9b4b08bcbd32778e94cfcbd341322ad855c0113228bb8da2fc5f12542f88899978e878196188e8e259bd012dc9d6ef0614294d217acc9da9d44be5de855043d044785c7d34e92e24550db661893d2b
|9,0=>0x325fb3145b55593994a25e667494811f2e9d24146d99a1aa5aa28a35e6a6e8c4aa668d36be66e658ba962ef346465e52c36a414ef04f9b248ae
|10,0=>0x63198d33345bc63c63
|11,0=>0x62
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_79 7 roots_79 ops++addP pm 2 dom_58 5 roots_58 ops++addP pm 3 dom_123 9 roots_123 ops++addP pm 4 dom_126 9 roots_126 ops++addP pm 5 dom_46 5 roots_46 ops++addP pm 6 dom_47 8 roots_47 ops++addP pm 7 dom_63 9 roots_63 ops++addP pm 8 dom_106 5 roots_106 ops++addP pm 9 dom_94 6 roots_94 ops++addP pm 10 dom_31 7 roots_31 ops++addP pm 11 dom_87 8 roots_87 ops++addP pm 12 dom_91 6 roots_91 ops++addP pm 13 dom_110 7 roots_110 ops++addP pm 14 dom_30 4 roots_30 ops++addP pm 15 dom_93 8 roots_93 ops++addP pm 16 dom_111 10 roots_111 ops++addP pm 17 dom_27 4 roots_27 ops++addP pm 18 dom_95 9 roots_95 ops++addP pm 19 dom_119 9 roots_119 ops++addP pm 20 dom_122 6 roots_122 ops++addP pm 21 dom_59 6 roots_59 ops++addP pm 22 dom_78 4 roots_78 ops++addP pm 23 dom_107 7 roots_107 ops++addP pm 24 dom_75 4 roots_75 ops++addP pm 25 dom_61 7 roots_61 ops++addP pm 26 dom_117 8 roots_117 ops++addP pm 27 dzo_93_2 6 roots_93 ops++addP pm 28 dom_62 6 roots_62 ops++addP pm 29 dom_43 5 roots_43 ops++addP pm 30 dzo_77_2 5 roots_77 ops++addP pm 31 dzo_109_2 6 roots_109 ops++addP pm 32 dzo_117_2 6 roots_117 ops++addP pm 33 dzo_125_2 7 roots_125 ops++addP pm 34 dom_21 4 roots_21 ops++addP pm 35 dzo_119_8 7 roots_119 ops++addP pm 36 dom_115 6 roots_115 ops++addP pm 37 dom_118 6 roots_118 ops++addP pm 38 dom_42 4 roots_42 ops++addP pm 39 dom_120 5 roots_120 ops++addP pm 40 dzo_117_8 6 roots_117 ops++addP pm 41 dzo_55_8 6 roots_55 ops++addP pm 42 dom_55 6 roots_55 ops++addP pm 43 dom_53 5 roots_53 ops++addP pm 44 dom_124 7 roots_124 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_93_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_77_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_109_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_117_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_125_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_119_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_117_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_124 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 97 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 97 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 173 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 173 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 124 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 124 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 51 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_127 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_127 roots_127 goal_127 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_127
theorem lowS_127:Lower true dom_127 roots_127 goal_127 12:=S_127.noCircuit
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000ccccccc800000000ccccccc800000000cccccc80
def gsh_221_2:=0x33333333000000003333333200000000333333320000000033333320
theorem lowS_zo_221_2_197:Lower true dzo_221_2 roots_221 gzo_221_2 9:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33003300000000003300330000000000330033000000000033003300,0,8),(0x33330000000000003333000000000000333300000000000033330000,0,16)] (by decide +kernel) lowS_197)
namespace S_223
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,10),(2,18),(3,7),(3,11),(3,19),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(9,11),(9,13),(9,25),(9,73),(9,137),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(64,192),(66,67),(66,70),(66,74),(66,82),(66,194),(128,129),(128,132),(128,136),(128,144),(128,192),(130,131),(130,134),(130,138),(130,146),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|4=>2
|5=>5
|6=>8
|7=>42
|8=>50
|9=>17
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x1b54c03768
|5,0=>0xb9a75a38a090cb2361551acdd
|6,0=>0xbe4a9b17388dbe975aa04686941dc9148381468f
|7,0=>0xa91159c641961cf8e77274cc57390772c3271782704d8622005c9d25beff54b1b4fc614d6b94a60745f16429883f4f03b37337a643510f2ee312cc892c112251441f35b1e49e1da9e1c9f51ac1315f3d15e870f6440eeb90c4e108f53084e70499a02ae1020e1019cb
|8,0=>0xf902bc17e1b4466a7c5579014739076f7a76ef8e6b44667cc2669895cd235928f57dbe447f43ba9c3b3233a7da38437363282fc372f5d32cc9b2ad042777624bfd241fd218cd20ecd200c41e5231dc071d0871c8521940c1784c1758116ac61588413c1f121f611c691115b10ceb10a890ea010ace90a3c50a2e903fe7
|9,0=>0xfc36fc76b09eebe7d2e1787e66cbb2687ab578ef56eb354e2b4fb1e4b0651753d16d121662b02df1023f1
|10,0=>0xc52d46974c4e3a91f206
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaaf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000ffffffff00000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000fffffff000000000ffffffaa00000000ffffffa0ffffffff00000000fffff0f000000000ffffaaaa00000000ffffa0a0fafafafa00000000fafafafa00000000fafafafa00000000fafafafaffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffaa00000000fffffff000000000ffffffa0ffffffff00000000ffffaaaa00000000fffff0f000000000ffffa0a0ffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa
|0,1=>0xf0f0f0f000000000ffffffff00000000f0f0f0f000000000fafafafaffffffff00000000cccccccc00000000ffffffff00000000ccccccccffffffff00000000eeeeeeee00000000fcfcfcfc00000000ececececffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0ffffffff00000000ffffffff00000000ffffffff00000000fafafafaffffffff00000000ffffffff00000000fafafafa00000000fafafafaffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaaffffffff00000000fafafafa00000000ffffffff00000000fafafafaffffffff00000000ffffffff00000000cccccccc00000000cccccccc0f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0affffffff00000000ffaaffaa00000000fff0fff000000000ffa0ffa000000000000000000000000000000000ffffffff00000000fafafafa0000000000000000ffffffff000000000000000000000000fafafafaffffffff00000000f0f0f0f000000000aaaaaaaa00000000a0a0a0a0ffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff00000000aaaaaaaa00000000f0f0f0f000000000a0a0a0a0
|0,2=>0xffffffff00000000ffffffff00000000ffffffff00000000cccccccc55555555000000005555555500000000555555550000000050505050000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000fafafafa00000000fafafafaffffffff000000000000000000000000ffffffff00000000fafafafa0000000000000000555555550000000000000000000000005050505000000000000000000000000000000000ffffffff00000000f0f0f0f0aaaaaaaa00000000ffffffff00000000aaaaaaaa00000000fafafafa55555555000000005050505000000000555555550000000050505050ffffffff00000000ffffffff000000005555555500000000505050500f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a0000000000000000ffffffff000000000000000000000000f0f0f0f0000000000000000000000000000000000f0f0f0f000000000a0a0a0affffffff00000000ffffffff000000000f0f0f0f000000000a0a0a0a0000000000000000fafafafa000000000000000000000000fafafafa00000000000000000f0f0f0f0000000000000000000000000a0a0a0a
|0,3=>0xffffffff000000000000000000000000aaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x28944c18b0593c944c08b05929131418e5ca2513143973ca25130e0405850cc38128545538128544c1814051cc2c128944c0810102073812893473060493513144ce04a20718124d2073812851cc2c13c33060452072c12892071811440c2040
|1=>0x3067013cd44c61438128544c68b3813c544c69339e28d44c18140935130e04040944c4cb38128544c60638100544c60e04f00544c5062c128944c39d28935130e04a40544c19c0813cd44c50e05928944c7023813c044c50e04028944c51a381
|2=>0x18204015130690100944c6ce04a24d44c61a38128544c2ce04a88944c60e0401513212c10090cc38128935131a0813c035131439728945538128935131870e04025131a18204f3513133813c035131a4ce04f35131f08128935131b4ce04a351
|3=>0x4028544c70e04028944c68b38128525131c2ce04f28d44ca0e04a24d44c61a38128935130e04a98935130639e00935131838100935131818e5ca24d44c39e2a524d44c60e5cf2893513069012893513022c13c044c68204f3513060973cd44c
|4=>0x4024d44c4ce04028935131a4ce04a24d44c6062c12893513182c13ca24d44c6c638128935131b3813ca24d44c3813e524d44c08e5cf28d44c3812aa24d44ca4e04f28d44c19c04a24d44c19338128935131838164a24d44c18e04f14d44c08e
|5=>0x32c3813c935131338128935131c2ce04028944c3812a514944c60e5ca24d44cb0e78a24d44c18b04025132d3812893513023812a024d44cace04a24d44c68e04f0093513022c13ca35131b38164a24d44c6da38128935130638164f24d44c182
|6=>0x39e28935131838128935130e04ac0935130ebca24d44c08b04a24d44c2ce04f2893513023813ca35131818e04a24d44c60e04f2893513063af28935131a38128525130e04a40935130e04ab893513022c128544c6ce04a24d44c686381285251
|7=>0x1130e04a24d44c18e04a24d44c2ce04a24d44c38128524d44c39728935130638128524d44cb0e04a24d44c70e04a24d44c70238128935130e04a9493513063813c935130e78028935130b381285251306
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x206069815504140a6
|6,0=>0x14984c611984060e983370b58267
|7,0=>0x641d897609d7b75d1d6c859215c8555d4e751dd3f84e1d3174a61218466111842610183e9cf283aa0e2836dcd473320c482f20b482b5ca6727a096823a08681fa07681bdc67817e0587
|8,0=>0xcc63298c863198c49f0a8c066f98bc62e89b822d88b422c97b062b89ac22a79a7e2969a3668499f227399aa661996264f991a63e88da22e889a21e885660c98121fc87d21eb978a5da87465c987061b986c25a8867e5978
|9,0=>0x3bc9ed23ac8e8e79b8e4e38b8e0e37b8dce36b8d91f5c8d4e74b8d0a7399
|10,0=>0xf723d48f323c57
|11,0=>0x3e47
|_,_=>0
def wAt:=mkWire dB 49 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x28d463560dc62538a4f3538d4a25389402528d4e3504d5837189413560dcf393494a353ceca2545049352cf0a2538d4c4124d4b3c2894e3538a49352cf0a2538d514938d40083894a353894a352cf0a2538d51490800e2928d4e254524e35289420028d4e254504e2924d4b3c2894e35
|1=>0x38a4e810808a353895325689c63538a4b2538a4a2538d583708a4e252894b2938d463538a4b3c38a4a2538d4a352cf0a2538d5a272ca4e3524d462538a4a3524d4f3928958371894a390504b3c2894e3524d4b3c2894e3508d4a393894a256cdd9390094a3528d42353895b376894039
|2=>0x28d4e353894a2518d4e292894e2504d4e292894e2524d4e2928d4e2528d4b2738d4a391894d2518d4e298cd4b3e2894e3528d42293494e25189ce2928d4e354504b3c2894e35389403928d413560dc62538a4c412cf0a2538d422928d4235389463538a4a253895a2700e4a35689c635
|3=>0x2894a2500eca3504d4a253894f2e38d4a2508dce252894e1524d4a39689c63538a4f353ce4a2528e4d252894d2528d4e252c94e3528d4d252ca4e352894b2538d4a912c9ce3518d462538a673508ace250494a3538a422928d4e2504d462538a412500eca3504d4f392894b2738d4a39
|4=>0x18d4e29289463738a5a2718d4e292c94e3528d403b24d4a3504d462538a412518dce2938a4a3538d461724d4e290808a35b09463738a4a2500e4a3538d4e25289402528d463538a4a393cd4a2538a4a353895a2700e4a35689c63538a4e351894a3938d4f3928958351894e2960d4f39
|5=>0xe2938d493504d493538a463738a4b2538d4235389403b28d4a2538a412528d493538d412538a462538a402728d411524d4e2538d4a2538d4a25389462538a4f392894e2904549352ca493538d4b3c2894e3570acb2538d4e2524d4e352cf4a2538d4d25
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x19800c000
|6,0=>0x12a881436a16508a800018a000
|7,0=>0x1788b845a22c1158800054229114089c44c2254d2288d444a21510467f33da1dd0e687033699ac8ce8634301974cb2856329213909484642198fd07683831a20c4c5c62a4
|8,0=>0x2a074d3a51d1ce8874139f1cece707353991cbce587293931c90a4271e38d9c64a2e5143889c38e167083829c08dfe6fc37c9bd8de66f03769ba8dce6e43709b78db66d836a9b48d9e6cc3649b18d866c03
|9,0=>0x1732b895bcada56b2b4959caca5632b0957caba55b2ac955caaa5532
|10,0=>0xbc0ddc6ec3751
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0x17b40512013bc048000ff403ef00fb401ff007f401ef007b401e90071001ad006800185004a000f70031400a500200007d0010c002f0008400200002400080001c0004000040000
|1=>0x520013a804a0011fd047bc11ed043fc1080041f81018037f40db8036c00d5f034e00bfd02fbc0bed02d9c0b2a02aa809fd027b4091002400082201fb407dd01aa005ff017f405ef
|2=>0x281ed617b491ed237f485ed207b481ec187b4608018088600818004519a104a040010afbc2aaa0888021ed077b41c470695019ef05fbc17ed05f1417a805e88178805aa015ed
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x8180
|6,0=>0x102470c1400800
|7,0=>0x24c52b29200221591d24fc6941f10e3f0b4d6a87a2d0bc7079a2726616504c1c0b66e18339
|8,0=>0x2c472f317d78680ace776ed463e10fc26152b52968e0b363566bc546554f7d451489f0559922a603567718a5
|9,0=>0x203f3e7ba4370d5d6aeacae36a9ab5
|10,0=>0x3e64b5e
|11,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 18 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_221 10 roots_221 ops++addP pm 1 dom_31 7 roots_31 ops++addP pm 2 dom_215 10 roots_215 ops++addP pm 3 dom_219 9 roots_219 ops++addP pm 4 dom_158 6 roots_158 ops++addP pm 5 dom_222 9 roots_222 ops++addP pm 6 dom_207 10 roots_207 ops++addP pm 7 dom_159 9 roots_159 ops++addP pm 8 dom_95 9 roots_95 ops++addP pm 9 dom_91 6 roots_91 ops++addP pm 10 dom_218 6 roots_218 ops++addP pm 11 dom_155 6 roots_155 ops++addP pm 12 dom_94 6 roots_94 ops++addP pm 13 dom_27 4 roots_27 ops++addP pm 14 dom_30 4 roots_30 ops++addP pm 15 dzo_221_2 9 roots_221 ops++addP pm 16 dom_157 8 roots_157 ops++addP pm 17 dom_93 8 roots_93 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_221_2_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_93 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_221 10 s (0,roots_221.map (·&&&dom_221)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_221 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 50 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 17 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_223 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_223 roots_223 goal_223 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_223
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=S_223.noCircuit
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,8,10)] (by decide +kernel) lowS_237
def dzo_217_2:=0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def gzo_217_2:=0xc0c0c0c000000000c0c0c08000000000c0c0c08000000000c0c0c00
def gsh_217_2:=0x3030303000000000303030200000000030303020000000003030300
theorem lowS_zo_217_2_193:Lower true dzo_217_2 roots_217 gzo_217_2 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_2) [(dom_217,2)] (by decide +kernel) (lower_slice_b (T:=gsh_217_2) [(0x3000300000000000300030000000000030003000000000003000300,0,8),(0x3030000000000000303000000000000030300000000000003030000,0,16)] (by decide +kernel) lowS_193)
def dzo_201_2:=0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
def gzo_201_2:=0xc0c0000000000000c080000000000000c080000000000000c00
def gsh_201_2:=0x303000000000000030200000000000003020000000000000300
theorem lowS_zo_201_2_193:Lower true dzo_201_2 roots_201 gzo_201_2 5:=lower_iso_b (d1:=dom_201) (r1:=roots_201) (T1:=gsh_201_2) [(dom_201,2)] (by decide +kernel) (lower_slice_b (T:=gsh_201_2) [(0x300000000000000030000000000000003000000000000000300,0,8)] (by decide +kernel) lowS_193)
def dzo_241_2:=0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c
def gzo_241_2:=0xc000c000c000c000c000c000c0008000c000c000c0008000c000c000c0000
def gsh_241_2:=0x3000300030003000300030003000200030003000300020003000300030000
theorem lowS_zo_241_2_193:Lower true dzo_241_2 roots_241 gzo_241_2 6:=lower_iso_b (d1:=dom_241) (r1:=roots_241) (T1:=gsh_241_2) [(dom_241,2)] (by decide +kernel) (lower_slice_b (T:=gsh_241_2) [(0x3000000030000000300000003000000030000000300000003000000030000,0,16),(0x3000300000000000300030000000000030003000000000003000300000000,0,32)] (by decide +kernel) lowS_193)
def dzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c080c0c0c0c0c0c0c00
def gsh_249_2:=0x303030303030303030303030303030203030303030303020303030303030300
theorem lowS_zo_249_2_193:Lower true dzo_249_2 roots_249 gzo_249_2 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_2) [(dom_249,2)] (by decide +kernel) (lower_slice_b (T:=gsh_249_2) [(0x300030003000300030003000300030003000300030003000300030003000300,0,8),(0x303000003030000030300000303000003030000030300000303000003030000,0,16),(0x303030300000000030303030000000003030303000000000303030300000000,0,32)] (by decide +kernel) lowS_193)
def dzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2:=0xc0c00000c0c00000c0c00000c0800000c0c00000c0800000c0c00000c00
def gsh_233_2:=0x30300000303000003030000030200000303000003020000030300000300
theorem lowS_zo_233_2_193:Lower true dzo_233_2 roots_233 gzo_233_2 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_2) [(dom_233,2)] (by decide +kernel) (lower_slice_b (T:=gsh_233_2) [(0x30000000300000003000000030000000300000003000000030000000300,0,8),(0x30300000000000003030000000000000303000000000000030300000000,0,32)] (by decide +kernel) lowS_193)
namespace S_251
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(3,131),(8,10),(8,40),(8,72),(8,136),(9,11),(9,25),(9,41),(9,73),(9,137),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(32,96),(32,160),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,96),(64,192),(66,67),(66,74),(66,82),(66,98),(66,194),(128,129),(128,136),(128,144),(128,160),(128,192),(130,131),(130,138),(130,146),(130,162),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|5=>21
|6=>147
|7=>284
|8=>202
|9=>63
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xd3385c9dcdc80c5a82d98f240815d480beb77daa71e4958d915862a54ba352aad49fd542b7b3ff983c77f342822435014be505f9b
|6,0=>0xacc42a9176a41e3a05b59a02598e6195ccf92d1e91f1a8f7d08ed2f8de8c8d0cf893d08776380c307e1f57cf4977c1b7514d7482c73889717e670ef56fe246f07b6bedf6b2366b0736ab1669787692d76804b65f4a654e9644ad63c93639256169760e5c5eb0b5e13e5c8fd5c6cf5ac355a8675a6e6583d856c9c5613455f66534ff4f8644b0ee493db4628a4349b41ea33fdbe3f1383e8053c8e33c8c23c5173b43d3aa7b38cbe3851635c3d34c1d34328330552f5792ed632defe2d87f2d1372cd0f2b4242b36d2aea929bfa2842128255276472733d2649e25a8b2239021e4221b371e5271e0b01d2b91bb2e1b43b196c418b4d1872a1764316887151861453c13bfd13918134e2117d90e1090dd9b0d16f0c1950c0880ba930b0bd0ad2b0a73409d800981b08f810755105c8c047400407b03fad0320b023200105300697
|6,1=>0xfc118eb7aae79f5de751dd2edd7185cd465cd397cc870c7170c4452bda9eb895ab64b4b43fbb21e4adf7aadc78ad5ab
|7,0=>0x474644723e4655f456cf454ec44348440a943afd438604362d42c39421e6418ec40f264056f402a7400de3fa223f2463e8c43e6da3de123d1613c4c33c0823ba6d3a900398ba38aee36c2b36061358b9355d935547350ee34db4341f834023323ff31fc0303f82ff992f8bc2dee02c91c2c6f42c1062bf322be8a2b7fe2ae98298fa297f9294952904e28327272d3265242627c25e04258e3257c424e82246e0245c5238412333922f7020dda2078320709203c71f73b1f7331ef211c2961b8ca1b8b91b7541afa91a65c1a32819df9198c7195c118ed117b601784a1688215ef015acd156b414b0213e8a11dda10fa010cdb10959102fe0f0ec0ecfe0e6bb0dd480d1bf0c28f0b9a90ac2a0a5120a0f90a0b609c590992208e3607e9f07d120712306dcc0630505df005c50048f40369c02966013bf00633005db004e9003d9
|7,1=>0xc13dac00cebeecabee73bc3baba1a3b8c3eb5cd4b4886b38ecb04fdb0197aff98afe1eae723aa8b4a6b4da627fa5705a3da4a2321a2084a1276a10bca04579ed3e9e38a9d958993ea96ac992f8692a96924d19222e8e27c8e02c8dae38c7b58bba28aef388685874db8551d8412a83c4881f4081bf97e44d7df0f7d8a67ad8b7a2ec797aa793d178b1a788aa775087709176d5d76bca76ab87528e74ba574a4f7470573d9472e92726bb71aa1718f77136d7032b6f4516e2986deac6d1c76ae856a8ce6a8926a544699ba692e968899687d966bab66b2a63a2c631166310f61ea1619dd618505fc835f7515f69f5f5c95ed015d2e95d204599be5935558cdd5767f56dde56bb5568005637a559275577b5533354c395466753c5e5330952fae51e1b51c4651af14fc044e4034c4c04c22f4ba2d4b61d4aabe4a36c4876d47939
|7,2=>0xfede8f7d4df643ff4228eff5bee996eb7aae9593e663fe45fedf922de688ddcc2dd065db86ad6b02d3debd351cd26b5d0010ca72fc9c13c8b0dc82b4c7d95c5b3ec35e3c17f5
|8,0=>0x73a2972a3e726317112570798706d56e6566ca356b5e06b24f67f8066d5d6659d65e4b604b25f9d45f7e55f2445d08d5d0265caf45c59c5c0a45add95a68c5a08c57174566f85536254ae754a22546d8528fa4c9684b96b4b5ba4aeed4a5c5498e545b6c45a764529244b074316b42bb84288f4144c413993ffdc3fe6a3f5893f2923e2c93d2463ba7d3afed39cfb398663883837960373553723235e9134c18343cf33fce3159b3143a2e5142c9ec2b54e2ab29292d526ed82683825e7f25b8a25994256ca21f23204881d6f71ce611cade1c6521c2c41b82d1b3a31b3001af051a6a81a3a01960f18cee13797130f712a57117b41122d0f3170ef560ede50ddba0d7c50cf440cbd20c52f0c48f0c3d70c0a10b0eb0af670939d08eb907fcd0749c06ffc06cc506a58064bc061f905ef80561203a5b02ff30204a0192f001f6
|8,1=>0xf50f0f37e2f330bf15cbf0f19f008beed02ed2feea03be9243e6ae1e19a1dba2bda408d8c55d8c0dd72afd7272d5d41d5530d3788d256cd0fd1cedbace4ebcc1a3cb15bc76abc6af4c5eb0c4d4bc32aec2ee1c1ed1c0998c0986be781ba886b7b78b5f55b5a27b0c8fb0876af8f4ad8a0a6f81a6d08a550ba27729e9a79a71a99f5099ac29630b9416b8fe398b3cf8a7f389b588790d8487e821a2814cd80feb7c0e97bd537ba097ac497a70679cd6771c674faf74434742e8
|9,0=>0xee83bde858cf90fc98c2c3e97c20eec12c8b64c2b1b0bb16e4adc19acc97ac976a7da1a4324a40ab9ec839b702949ec9096a7941375f7a7168b6a9eb6a9956898360c36609385fee85cd775cb885c2ca5b79e5a0b356c18527054adf4481614796844e78425634210d406cd3dbae3b99736b5f363682f8c12e8352e76c29d8f27ecc260292516b1c0961a20419d7d182a816f151609110b3a0c67102ce3
|10,0=>0xfd547c34dfaeeae92b8158b413ecf21497e0b860
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c505050505050505050505050505000005050505050505050505050505050000505050505050505050505050505050505050505000000000505050500000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0000000000000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0ad0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000505050505050505050505050505050505050505050505050505050505050000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000
|0,2=>0x505050505050505050505050000000005050505050505050505050500000000f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0000000000000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a505050505050505050505050505050505050505050500000505050505050000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0000000000000000f0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0a50505050505050505050505050505050505050505050505000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a50505050505050505050505050505050505050505050505050005000500050000f000f000d000d000f000f000d000d000f000f000d000d000f000f000c000c
|0,3=>0x5000500050005000500050005000500050005000500050004000400040004000000005050505000000000505050500000000050505050000000004040404a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0a0af0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0af0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f04040404f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0000000000000000000000000000000050505050505050505050505050500005050505050505050505050505050505050505050505050504040404040404040000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050505050505050000505050505050505050505050505050505050505050505050505050504040404f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0c0c0c0c0808080800000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
|0,4=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f05050f0f0f0f0f0f05050f0f0f0f0f0f05050f0f0f0f0f0f0000000000000000000050505050505050500000000000000000505050500000000505050505050505050505050505050505000500050005000500050005000500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c00f000f000f000f000f000f000f000f000f000f000f000f000f000f000c000cf0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f0505050500000000f0f0f0f0d0d0d0d0f0f0f0f0d0d0d0d0f0f0f0f0d0d0d0d0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0af0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0c080c080c080c08f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000
|0,5=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0af0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f05050505050500000000000000000000f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0a0a0000000000000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0a00f000f000f000f000f000f000f000f000f000f000f000f000c000c000c000c00000000000000000000000000000000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a000000000000f0f0000000000000f0f0000000000000f0f0000000000000000f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000000505050505050505050505050505050505050505050505050505050500000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e
|0,6=>0xf0f0f0f0f0f0f0f0f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a50505050505050505000500050005000505050505050505050005000500050000f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000ac0f0c0f0c0f0c0f0c0e0c0e0c0e0c0e0c0f0c0f0c0f0c0f0c0e0c0e0c0e0c0ef0f0f0f050505050f0f0f0f050505050f0f0f0f050505050f0f0f0f00000000000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0ac0c0c0c0c0c0f0f0c0c0c0c0c0c0f0f0c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c505050505050505050505050505050505050505050505050504050405040504f050f050f050f050f050f050f050f050f050f050f050f050f040f040f040f04000000000000000050505050505050500000000000000000505050505050000f000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0d0f0d0f0d0f0d0f0d0f0d0f0d0f0d0f0d0f0d0f0d0f0d0f0c0f0c0f0c0f0c000000000000f0f0000000000000f0f0000000000000a0a0000000000000a0af0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000a0a0f0f0f0f00000a0a
|0,7=>0xf0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0c0c0c0cf050f050f050f050f050f050f050f050f050f050f050f050f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050500050005000500000000000000000050505050505050500000000000000000500050005000500000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a000000000000f0f0000000000000a0a0000000000000f0f0000000000000a0a00f000f000f000f000f000f000f000f000f000f000f000f0000000000000000c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c00000000000000000000000000000000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a
|_,_=>0
def sP:Nat→Nat
|0=>0x300048b101090d0a70f840634588081c10c162020304008852010c9b2278b8406604852010d0d0a749843260889201038f0a70b84243488b2810c9b222cb8424348892010c98122ca04343448b1010c980a5c2122c3848b261090d2224804062848b101018a12144040e182840608080
|1=>0x385c2191a392852e1018f1c242880864c0e0a402191a6c5853a1018d0050aa2481018d0a202032c307051010c9b1c74b902a10c98222cb8432347053a702031a00485261090d1c44494081c78e121480406351910a402071e30a1544101a11850a9a1a8060e2214984063c7053a20203
|2=>0x1c14e93080cc0c2214b84243470526402031e602aa3e1018d1c2c28808a468c4a24a040634005504c2071a3029c2e1018d0024288080cc000a5c2191a9c7260a5c2121a3888b2e1018d001441f086468e1614a043234d890a5021a1a388852e101861c94494086468e12148043260685
|3=>0x84868e0aa88040e346172a109311a388b0201018d1824290081c78d122ca04063cc090a202071e38885201148d182c29d081c68c0a502122c307053aa02031a00284069d78c1c50aae5ab090d0a74e040e3460550402031e00585101019b181558432347052e1018d4e008852810c9b
|4=>0x181440406dc60e0aa08040e3c60b101018218382a8080c7800a402121ad86350a502191a3888b281090d182ca0406341000a78b840660685265c2193034a1568b03a1182c28406357800a4c2031e6029c2e1038d181440406cc60e0a1090d6430711165c2071a302a83e1018f1c14e97
|5=>0x86468e4a24a04063c7090a402031e605853a10198182c297080c50d222cb84063c7090a5021972385852e1090d16502071a086250a502031e00585081c6af182c29708486800a70804063460520101960030e1728542121a15c041ad860e2e40a842435b082640a840e3c290080c6b7
|6=>0x1a38297086868e385c815086469d2650a8432604102a10c9b7814a040e346051010182003829f261018d1c15d84243460e2214b8406287051010ca7183889e28101981850aa45ab038d222cb840660605107c2031e3888928101861c45314080c78e285522c084868b0a202121a3029f
|7=>0x81c68c222ca04063c0110a5c2071e3a185201018d18242940864b0e0a74f84063471d2e40a8424348852e101980050aad250868e122c40406340053c20203303088b281018a1898288080c78e821480406340110b002031e38a155a486bf1c24588086468e2e542121af873d0a5c203
|8=>0x1c14b84063518e122c984063400528101961838b902a10d0d4c14a04063cc0916202031e3848b2810c981a24594080c6a3222ca040e3c6058c10d0d1838e1f28542031a162843234d8e28556ac2435b0916502031434585101018a1824594084868916502121a00889281220d1d04290
|9=>0x38202031a30705801018f1a388142a10c8d3650a921b2000c1c44294084868c1c20a150864d8e285572d581c68c3a20815080cc0c0a502031a0800e0a1018d8e3071d3850a8406340082e542121a38f9720542031a3858528101b91838a1574b02071e30e902a1018d0014a04323538c
|10=>0x80c6cb1838a155c882071a3041f28542191a385852e10c8d1c2081508a468c28556991b28705921038f1a307053a5c2071a30705201018d043070554742031a3071d3840a8406346142ae96991a38a1574902031e3829f080c68c1c70b942a10c8d1c14b84326068e285490d9030705
|11=>0x80cc0c28556831b280142ad021936384102a1019b184c8142a1018f3050aa45810c8d1c2c297080c78d1c2c288086468c1c98294080cb0c1ca8f942a1018d1c50a8424c468c1c50aba5a0c680285513a080c68c504ca15081c68c385ca15080c6800a5c2033034009281018d4e30705
|12=>0x1a30a1548b02031a00ea828542031a00585101018d0030e9c28542071a3048528101861a3941028542031e01305281018f1a38b9508486ce1c50aae9a10c8d1d04294080c6801d30294080c68c1c74815081c68c0a5c2441a395942a10c8d1c15517080c68c1c2c297080c6803a4ca15
|13=>0x1c24588080c68c1c74b942a1090d1c16904063460e5440a15081c68c0a1018da2307260a402031a006142a9268406347142a89a2c063461408486cf18388852010c8d1838297081c78d1d04290080c68c1c14404883460e2855a2d24347053c502033034605101018218385852e10198
|14=>0x68486d7183899728542193034284323408c1c15408086468c1c4ca15080c798385ca15081c68c6014804063461112502031a007142ab9a0406600110a402031a00605ac1018f18388852e101981838a155c101a11838a1508486b2183941f28542031e38815080c6af0150294080c68c
|15=>0x28542071e30290080c50d1815408080c6801844297080c78e0a2020314307410a502071a307142b556040e346110a502441a30708265ca84063c72828542031e00a15581038d4230290084868c2224804063460e2050a842435b0c0a402121a0060b0a5c2071a32185281018d1838a15
|16=>0x63460e2e542191a04708265ca8406606142b55204063470b0a502031434628105ca84323471116502031e307562e542031e3858528101961838a15b0b038d182c294084868c285522c081c68c0a74b84066060e1614a04243400c0a1018d02006142b54203423071112502191a39410
|17=>0x63401d20542033030a040e3678c1c5c815080c50d5020b95080c6803840a15080c68c2224a040e3460e4a14404066060e105ca8406287110aa02033030738285420d6c307142a896ac063461720542121a44293080c68c1c50ab49ab4c8d1c5c81508486803a5c815086468eb214a04
|18=>0x7e307142ad168342307053a4c2031a3070526402031e34705281018db83071f28542191a38297080c7981c14404326060e2855a2d883470b0a502031a31185101018f00382db081c68c1c50aae5a101980074b902a1018d0014984243460e2214a04062860e0b682031a307142ae96ac
|19=>0x1c50aae080cc002854212843460e1614404063c60e3e4ca15080c68e0a4c804066068c7650a84243460e2e40a8406351942a89a040e346142a1090d7c307090a202191a382dd080c68c1c2c2940864c0d182c294080c78d0024594086468e0a5021a1a307083e50a84063c7142a1090d
|20=>0x2810c8d1c50ade086469b1c50aad08486b61c442940864c0c1c15410080c6801904294080cc0c1c50aba5ab038d1844294080c7801c15508080c68c1c5c8150864c0d4a2c294081c68c3820815080c68c122ca0406340082e5421930384402a1018f1c50aba581090d1824594080c78d
|21=>0xe3460550202031e307090a1018d02307142ad0203423070b0a502071e346055010c8d1838a15c410d0d1838293201038d181541f080c68c1c50aba48b418d1c17004063460e105ca84066005f0a502031a30705261018f1a38a1544b02031a30b942a10d0d1c74b902a1038d1898485
|22=>0xd03460e22148040e346142ad16833000a1508486e61838a1544d0203303041320542071a30294080c6961838294086469b1c74f942a1018d1c44494080c78e2855a2d32607142b942121a30705501018d0030294080c6e418384172a1038f1c2c293080c6801814b84061868e2857184
|23=>0x5cd16031a00585281018f3030a155ab090d28556ac24340114c502031a307090a502441a39289281018d183829c2e1018d1838288080cd8c1c50aad2436b8e3a5c815080cc0c2278a04063460e0a502031e600142ab9d0406340142a882071a305853a1018d1838294080dc8c1c14a04
|24=>0x63c60e0ba42031a307053c202031a307142ad268342307260a502037230705281090d6c307142ae9a2d323471720542031e623142a10d0d18382ab080c68c1c44294080cd8c1d6c815081c68c0aa82031a307053aa02031a3074528542191a6c7142ae920406340090a202031e38a15
|25=>0x1838a15b01038d1838a15681090d1838a1574d02031e307260a502121a30705d41018d18382b8084868c1c15c04243400c1c14404243460e5020a15080c7800a502032c307052810196003070826542031e382a8201038d1898288080c68c1c15513080c68c1c442c0080c68c1c15404
|26=>0x1c74b942a1038d183951d28542031a307142a10c8d3638294091068c1c50ae3080c68c1c7ca15080c68c1c5ca150864c0d1c704142a1018d183a0142a1018f1a38a1568b438d1838a1568b018d0030b902a10c8d1c2c294080c6801850a84a06468c1c2c294080c78d1838a15080c6c7
|27=>0x1c14984063400c1c14404063c60e0a502071e3460e2e50a8406606802e40a8406340142a1018d963071720542031e3470916502031a3070820542191a307142a89684063460e1614404063460e28542191ad860e28542121b3860e2855704066060e9250a840e3c68c1c50ab49a0c68c
|28=>0x183941720542031a3070828542441a307142a882031a307142b356040e346110a402031a30705101038d1838b942a1220d1c98585281018d183951728542031a307082640a84063460e28556031bb460e28542031e60005261018d1838a1509ac68c1c20815080c6801820b95080cc0c
|29=>0x104ca84063460e28542191a0460e2214a040e3460e8224294080c68c1ca04142a10c8d183ab142a1018f1838a1574b02031a006142bc02031a30705080c6811838885281018f18382a8101018d1838a15080c6d118384172a1018f1c5ca15081c78d1c50aba5810c8d1838a15dc1018d
|30=>0x2a101981838a15080c68100314172a1018d18388142a1018a1a30a15aad02031a307281050a84063400c28542121ad860e1050a84062860e2855a2d066060e2050a8424346142a1018dda007142ad02441a3071028542121a006142b6020330307142a128121a307142aea684063460e
|31=>0x634623b450a84063460e1214a04063c68e2855a04062860e285560452346142ad26ac063460e1214a04323471d1040a84063460e0a742031a30705281018f30307090a402031a307142ab9d04063460e2855a24080c68c1c14a040634d8c1d6c815080c68c1c50af15a0c68c1c74b94
|32=>0x3a4ca15080c68c1c15410080c68c1c14e84063c68c1c4c8142a1018f1a38485281038d1838b942a1018f30384142a10c981838a1574902031a3070828542031e007142a1038dda3075b28542071a307142ab9a2c063460e2856aba080c68c1c4ca15084868c1c14804066068c2050a84
|33=>0x5040a15080c6801814997080c68c1c50ab4581c68c2857a84063460e5420a15080c68c1c50ab40864c0c1c50aad586468e2855a04063c00e0a502031a3298e0a502031bd060e0a402071a30990285420330346142b55684063460eba50a84063460e2855684063508c1c50a84e43460e
|34=>0x2a101861a38a1508486d7183940828542031e3070820542071a314142a10c8d1838a155cb56031a307132050a840e346283e50a84063460e2856a84063460e28556ac06340142ae9604063c60e2650a84063c68e28542031a8460e2855734080c6801c50aad084868e2855684243400e
|35=>0x80c6f71838e1728542031a307052e101981a30705101018d003070828542033630705801018d1838297080c6801c50aad080cc0d0050a840637b0c1c50aba581038d1850acd084868c1c50aad0864c0d1c50aae681038d1838a155cb018d1839285281018d18394142a1018d0030b94
|36=>0x326068c1c50ab4de0c68c1c40a84063578c1c44294080c6801838297081c68c1caca15080c68c1c16284323460e1100a84063460e5450a84063460e2855a04066c60e4c14a04063460e3aa0a15080c68c1c98294080c6801838294080c682183829e281018d1838a155c1018d0038a15
|37=>0x188c7250a50203303460e222ca04063460e5040a15081c68c544ca15080c68c1ca0a15080c78c1c50ad59a1018d183b4942a1018d1838a15f01018d1838a159a1018d42307142ab82071a30705281018a1a307142a10d0d18382d6080c68c1c14a04243460e0a502121a0060e2856f04
|38=>0x2855d2c080c68c1c4ca15080c68c1c50aad580c68c1c4ca15080c68018384142a1018f1838a15084838d18384102a1018d183b5142a1018d1839c142a1090d1838294080c78d0039c142a1090d00307142b9c2121a307142a13c8d1838a15ce1090d003070828542121a30705281018d
|39=>0xf66468c1c50a84062868c1c50aad080cc0d1838a15084868c1c50a84243400c1c50aad080c6801c50a84063760c1c50aba080cc0d1838a15681038d1838a155cd02031a307142a1018d02307281050a84063460e28542031a33d0e2855a04063c60e2857784063460e1050a840e3460e
|40=>0x63460e2050a840e346142a1018df8307142a10c981a307142a1018f1a007282050a84063460e3a50a84063c68c1c50acd080c68c1c14b84063460e2856684063400c1c50a8406346231c40a15080cc0d1850aac086468c1c50acd5a1018d1838e942a1018d1838a155a10c8d1c50a84
|41=>0x1a307142a1018d36307172854203303460e1050a84063400c1c5c815080c68c1c14a04063c68c1d00a15080c68c1c5ca15080c6801c14a04323460e2855a2d063460e28542031a3398e0a502031a0060e2856f04323460e28542441a307132e50a84063460e2855704063460e2857884
|42=>0x63400c1c50ab4080c68c1c20a15080c68c1c14a04063460e2e50a84063460e2855604063460e28542031e3460e28542191a3070b0a502031a307142a1018d943075628542031a307110a502031a3071728542071a3074528542191a307142ad02031a0060e28542031e6060e0a20203
|43=>0xa15080c68c1c50a84
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x786039301b180ccc060602d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x119b88b1c44cc21f710c38845c414e20370fe387d5c3dce1e770f038765c3a4e1cb70e2386f5c36ce1af70d438685c334e19370c6b0619c2fee17870b8b85a9c2c6e15c70aab8539c28ee140709cb84c9c256e124708eb8459c21ee1087080b83e9c1e6e0ec70733037dc1b0e0d17065b0311c17ae0b67057b82a1c142e09a7049b8231c10ae07e7
|6,1=>0x1f738f9dc7c0e3d971e938f2dc788e3bd71db38ebdc750e3a171cd38e4dc718e38571bf38de186e2e36a71b230d75c6ace34f71a438d05c674e333719638c95c63ce317718838c25c604e2fc617ab8bb9c5cee2e0716cb8b49c598c2c5715f38addc560e2a9715138a6dc528e28d7143389fdc4f0e27171353899184bae2567127b8921c482e23a7
|6,2=>0x11c5c8d4e464622eb9159c89ee4487220b90e9c866e42c7212b9079c82ee41162053900dc7f8e3f57
|7,0=>0x32b4193a0c8d063f731bc18be0c4f0620730d3184dcc17060472fe417d5cbdce5e772efc175e0b9f05c782dfc16de0b5f05a872d0416620b21058972c0c15e9cae5056a82b1b9571caaae54d82a2c14f60a6b052d82933947a0a2ee50f828439405c9f304f27275b938e09b704d4726641312097904b57256c1299c93d049682474121dc8ff04787
|7,1=>0x41f420ddd060e8288410420621022e809840139fea0fe6e7eb83f239f75cfab07cd83e2c1ef60f6ce7ae83d431e820f31079173c539e0a0ef5077283b5b9d8e0eb8e75483a6b9d160e7b0735839739c9a0e3d0716838741c1dcdff06f78377c1ba1cdc106d97368c1b260d8306ba735941aadcd47069c734ab9a360d0ce67e833b419ba0ccd065e8
|7,2=>0x51242875d42cea0f7503c27fe13f0e9f084f44278213b109d084e4ba706137309b274d5ba68e1337099474c6ba61612fb097584b6c259612bb095674a7ba521d282e93984993a4add247091b848a3a432120ae8fd847b3a3bdd1d0e8e0846c42342119108c1745cc22c6115308a3644dc224e1118e884843e421d5d0db0865842ec2156109b08467
|7,3=>0x604c3009d7f50bf285f632f95d7bb0bd675e742f1a177eebb875d842ea21742eb9985c93ae2a1706eb7c75babadb9d6cd0b5e85ab42d3a168eeb3f859c3acc5d6530b22758d42c4dd6170b04757ebabd615db0ae5856ec2b59d59d0ac7755fc2ade1560eaa97550c2a69d5250a8b7541c29ee14e70a6b8531c296e14a70a4b8521c28ee1468ea2c8
|7,4=>0x66ec3359d99eecc786603b2e21962eca986513b26dd9270c8b8641c31f1d8eaec6d8632c317618ab0c4d86233b0fa186eec2f86143b085d8330c118
|8,0=>0x76fcbb5a5d9d0ec5975ec3ad9dd5d0ea6874f43a5ddd1f0e86973f439d65cdb0e65872ec39561c9cee47771f4b8d65c592e24870ebb859dc1eee0786ffc37de1be0ede886f043765dba30dc986e0c36e61b612da886d0436621b210d8796bfc35da5adb2d6676afbb55e1a9f0d47869f4b4da1a5d0d26868fbb45e1a1f0d06967f433da19dd0ce59
|8,1=>0x8743c38221af30cf88643c302217110b0885534286613130908843cc201e0ef306f8833c417a60ad104e8823440f6606b102d8812c40726027300b88023bff21fe90fec87f243f75dfa92fcd77e24bef5df6b0fad87d24be6e5f270f8b87c1c3dea5ee50f6a87b143d665ea12f4887a043ce21e62ef298790c3c661e230f0987804bbe21de10ee88
|8,2=>0x97644b9225b732d389654cb0a257512b19954c4a862534f29379463ca1224f732738935c498a64b6f25389263c9122479123489164488e6435321289054480a23f511f198f4c478623b311d278e5bc70e237711b388d5c468e2335319288c54460a22f5117288b4cc589e2b5115198a4c45026271113178944c4822231110f98843c40221ef30ef8
|8,3=>0x267d1336899744c96663b13167986ccc1625fb12f49
|9,0=>0x54f62a6b152d8a92c54762a2b150c9a82453f5e9eb14ec9a71cd36e29a714cb8a61c52f1e96914ac8a5245272292af48c9a42451f228eaf46d8a32c517628a9344b9a21c50f1e867342b8a11c506e2825340a8a01bcfee27e713ea99f1bcf6e27a713cb89e14ceea276333a989d04ce622721138889c044dde66df136789af4cd5a269d13468
|10,0=>0xabdc55ce2ad715647aae455522a9915457
|11,0=>0x15837
|_,_=>0
def wAt:=mkWire dB 125 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x303306311a39285528552835303306311a3928552e351a39063128310a35283106310a3928553a3b06010a31285528011c310a3506390a3128551a021c310a35285506391a3128392e39283128551c31103128352e392e352855063128310a35283906390a3128552855285506010a310a392855280118391a0118391e391a31
|1=>0x28353239083906315a3508311a3120352839285530331a39286d303306311a3928552855303306312e3528552e392831060128311c3128551a312855203128390e33063922390a35285520312035285506392839285528551c3130330631068d1a021e3b1a3116350a39285506311a39285516350a3928551a39063128552839
|2=>0x283906011839203106391a3128391a312035285506392839286128551a391a311c3128392855060118394a33063128552e3906311a3928312e370a392855280128551a391a311c31063950332e350e31285506392831104806011c311a31283906390a31285528550a3106391a3128550e330639283928552855285510311039
|3=>0x2e3b0a3528552855068d1a02183928312e352e3906312831283530331a390631283906391e391a310a3928310a35285512390a31285574330631060118392855503306312035283916350a392855285528551e391a3128554c34123906010a39283128551c310a6128551a3906010a3928551c3132393a3b2437060118392831
|4=>0x285528552855068d1a021839286530331a39285508390831243706011c311e391a311e391a31060118390a310a392855060118390a310a3928551235283906390a312855183928550a3506391a3128554c3712392e350e310639283928311c31684806011c3128350a310a39285516331a01183912390a31285512350a312855
|5=>0x601183928552835063130331a395a350639083108391a3928391031283512370a31285502312855203728393a3b283d1a3132392831283506315033203528394c34163128551a310639583508391c3128392e352831163706310a3928551a02283128551c310a310a392855280118392839068d1a02183928310a0128551c31
|6=>0x28350e33063928395837063108390831281d06391a3128552e35285506392831283912370a31285528552e3528313a3b2e3528315835063108390831743358350839503328552035283906313a3b2e35285506311a39283170132849060118393a3b2855103128352e3b28311a31285530331a39063128397013284906011839
|7=>0x1a39283920311a3128397433063158350a3928311a312855283506310a3928554c3716310a3928555433503120352839104806011839083108611a39183968395c3b6831083506392031203528393a3b2e352831283128551a39183916370a3928552855203f1a3128395c3b0639083d1a31503306311039283106310a392855
|8=>0x8391839103110392835183928350a3928553a3b06392e3528311e3b1a311a312035283912390a3128552831284a06011c315a3906315a35083122310a3528551a021839063928392e352831323b285506312831286d063130331a390a39283128551c311a392e392e35283108311839583708390835063130331a3930332835
|9=>0x28350a310a39285506011c312e352831294d0a02285518390639283926372801285518390a01285518397433583158350839683108352b42243506011839063128390a352855063928311a312855223128390a3528552835323b06312855323908350831063116330a392855123728350a31285528310a391a39285574335835
|10=>0xa39285506392831823b0a3d1a310835084a060118392e3906311a392831063128552037283928550631103928352e391a311a39283106393a3b2e352839123b0a3128551c31683108351839283918390a352855103b28351a3128551a3928310a352855aa375c39083d1a3150332035283928391c312e3728316035123b0a31
|11=>0x9a37080118390a3506310a312855203506391a312839303128391a39285518392855103928350a3528311a31285528351e391a3128550a3d06391a31285506390839323b063128552e3928351a3128311a3128611a3918399a3758310839063932392855063128390a3128390a35285528392437060118392855283906011839
|12=>0x28011839285508355a390831063128312839060118392e3506312831283920370631283128392e391a3928317433743108611a3930311a3928310631103928352855103b28351a3128314c371631285568330835083906390a392855060118397433063958352e3528551a3928310a3928550601183928551839203728391a85
|13=>0x5a3508311a3928391c312e35283128552801060118391a011839ac31103b283528551c310831583508391a3928392e3528312b420e3d1a3106391e391a31283128391c3110392835543b203d1a3128390a3506390a31285528351a39303128351a39283128610a351a3928552437060118395c3b5a3508313239063128312839
|14=>0x6310a312855803528552e3b28310a3906311a39285528551a310a3106310a3928552855068d1a0218395033103928355a3908312e3528552e3928311a312855203128394e3116370a39285550330631203528391a3928311a312855283506311a392855323b0835083106311a021839283528551a311c310639103328352855
|15=>0x18390a3d1a31285508310639583508391c311a39063128312839063916350a3928553a3b1031283518390a310a392855283506311a3928312e3b28351a3128310e310639583508392855683108351a3918396848060118390a3928351a3128552031503320352839203128391a39285528311a021c31283906395c3b68312835
|16=>0xa3906391a3128552855063120352839068d1a02183906392855203128395033285520352839743308611a3929850a621a392855183928351a3928312e3928311a312855aa3b583d08391a31068d1a02183928312e35063928392831063112390a312855063130331a390831243706011c310a3506311a392855203528392855
|17=>0x83506392835203128394c3716310a392855303306311a39285550331039103128350a350a311a3128551a3908350831063108d9243706011839285528611a391839163f0a391a3128351a31063928310a392855280118391e3b28311a312855081906391e3b1a3128551a31103928350a31285520372839aa37680108351839
|18=>0x1c310a0118392855323b06310a3128550a611a39285528553a3b2e352831303328351a3928550831084a06011c312e351a39283116330a39285528551a391a311c316839683108351c315c3b0639083d1a3128552e3528314c3416310a392855074d0a0228551839063928390a352855083108351a391839ce37060118396831
|19=>0x1839163328350a392855080118394c34285524370601183968390835083106311a391a3128312839068d1a021839286d285530331a3930331a39063928391033283528553a392e35283128551031103928352865063130331a39743308611a3928350a311a312855683108351c311a3128553239063108390831083908310601
|20=>0x683308350835060118391a316839083506010a0128552855288d1a0218392855284906011839285528490601183906012835285518391839103928354c3716310a3928554c370a0128551839203128351a3128392035285506392839163128350a3928552801285518392e3b28310a3528551a31285520352839285510032835
|21=>0x2855243732390631284a060118395a3508311a39281d1a3106390835080118392e35063928312e352831063130331a39323b0631285508191e3b1a3150332035283906311a3928313a3b103128351a312e3b283108350831063908390835183906312831283918390a39285532611a3906310a391a3128550231203728390639
|22=>0x28350639323b0631283116310a3928552e611a39283128352031283908395a3708311a391a311c3128012855183907b1083e1a3128351c31283928351a39283128552801183928351a31285506391a31285528311a391839183928392831203f1a3128391a31283128390a310a3928552835063128395c3b5a35083128350a39
|23=>0x28352e39283106312037283906390a35285512350a312855063110392835103b28351a31183958350839e231683b08352855203728390a351a31285528551039283526372e39283128351a3128311a3106392831063158350839de355a3b0831203528392831323b283506315c3b083d1a3158310839063928390a3528552855
|24=>0x2855683968310835743368390835285530331a392839103328350831683b08352e351a3928311839203728392831203528391e391a3128396801083518391839103928352437060118391e3928351a31083508311a392839060118391c315a3708310835323b06312839060118391a3968330835243506011839583158350839
|25=>0x6390a3128551a311a3928311a3928350631743308611a3928351a311c3106395a37083110332835063908396831083508611a3928010601183928391a3928551a021c312839ac31103b28350a311a3128551a01083518390e330839063908355831083906310a31285528391031283528552e3528311a391a31285528390a31
|26=>0x1c31083106011c3118392035283928552e39283108350839063968030835183950311039283508351a39063106310839083108351a311c310a02285518390a3e1a3128552855063928391a39203128395a6108311a3980352e3b28319a375a39083107cd080218392e392e352831285520352839283d1a31285520311a312839
|27=>0x58350839080106011839063108311a39063968310835083d08391a310a611a39285528611a39183928311e3b1a31084a060118391a311039283528392835063906312035283908395a3508310639203128395033203528395a6108311a39183908310839583508391a3128011a311c319a3708011839683108351c3108310601
|28=>0x285506392831286d30331a3928650631285528352e3b28313a392e352831083530331a3916310a3928551031103928350a012855183912370a31285516330a392855083d1a311c31da395a3708313a3b2e35283128551a392831283528551839283530331a3928552e3b2831283128551c31183908311a39583f08391a310639
|29=>0x849060118392835060118391a02285518390a611a3928550a390a3528550639203528392e3928311a312035283908011839100328351839088d1a0218399a37080118390639083d1a311e391a312855068d1a021839103b2835285528550601183928550601183908651a39063108355a3b08312e372831283918390a352855
|30=>0x323506311a01183908311a39060118390601183908311c31083e1a3108611a39083506396831083520372839103928352802183908351a315a3b083128350639583508392e392831083108392801183928351a310e31063928352839288d1a02183928490601183928551a311c3128490601183908490601183907e928021839
|31=>0x2835285530331a391a39283128351839283928311a3128552e3b2831183928310631285508310835080218392855183908650631323b06312e392831083d1a31683b08350639283928621a391a3906311a311c3120352839283d1a310801183928552831080118391a0218391a392839083906315a3908312e35283108310631
|32=>0x1839083528352855283108391a3106310a39285558370839103b28350a3528550639283128650631083518391a391a31
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x11500c500000000000000b1000000a1000000460022000200000000
|6,0=>0xa1309c500000000000009b109a1095500000923000008d508c1088408440831000007f4000007a500000764074206f506e106c2068406440604000005e205b30565000005510000054105310000051204f204d204a3047300000443041303c503b1000000000365032402d502c102750234021201c50000000001a20164
|6,1=>0x11840000116200001115110110d3109410811062103310030fd300000000000000000f8500000f440ef50ee10000000000000ec20000000000000e84000000000e530e320e120dc50d930d810d710d520d410d220cd500000ca300000c64000000000c420c130bd40b94000000000b4500000af50ab40a920000000000000a45
|6,2=>0x148500001435140313f113e1000013d113a300001364131512f212d212851235000011e511c2
|7,0=>0x231222e322b322742234220321e221a421642124000020e420a4206420241fe41fb31f831f441f041ec41e841e531e141dd41d941d631d241cf31cb41c741c431c041bc41b841b441b041ac41a931a631a2419f319b419831944190418c418841844180417d317941754171416e316a416731634160315d315941554151414d4
|7,1=>0x31833144310430d33094305430142fd42f942f542f142ed42e942e542e142df22dc32d842d442d042cc42c842c442c042bc42b932b542b142ad42a942a542a2329e429d129a32964292428e428a4000028732834280327c427842744272226e426b326742652261425d425942554251424d424a32464242423f323b423742334
|7,2=>0x3ec33e843e443e043dc43db13d743d433d043cc43c8400003c443c1300003bd43b943b543b323af43ab43a8300003a623a2439e439a43964392438e438a438823844380437d337943754373236f436b43674363435f435c335843544352234e434a434733443340433d3339433543314000032d432a332643242320431f131b4
|7,3=>0x4d034cc44c934c724c344bf44bc34b844b534b144ad44a944a634a3349f449b449744943490448c448844844481347f247b44774473446f446b44674463445f445c345844544450444c444844444440443c443844353431442d442a342644224000041e441a44164412440e440b3407440343ff43fc33f843f7100003f343ef4
|7,4=>0x5353531452d452945254522351e451a45164512450e450b3507450344ff44fb44f924f814f444f044ec44e934e544e324df44db44d744d34
|8,0=>0x5f435f135ee35eb35e835e535e235df35dc35d935d635d335d035cd35ca35c735c435c135be35bb35b835b535b235af35ac35a935a635a335a0359d359a359735943591358e358b358835853582357f357c3579357635733570356d356b256835653562355f355c3559355635533550354d354a354735443541353e353b35383
|8,1=>0x6b336b036ad36aa36a736a436a1369e369b369836953692368f368c3689368636833680367d367a367736743671366e366b3668366626633660365d365a365736543651364e364b364836453642363f363c3639363636333630362d362a362736243621361e361b361836153612360f360c360936063603360035fd35fa35f73
|8,2=>0x771376e376c2769376727643761375e375b375837553752374f374c3749374637433740373d373a373737343731372e372b372837253722371f371c3719371637133710370d370a37073704370136fe36fb36f836f536f236ef36ec36e936e636e336e036dd36da36d736d436d136ce36cb36c836c536c236bf36bc36b936b63
|8,3=>0x78f378c3789378637833780377d377a377737743
|9,0=>0x80e280c280a2808280628042802280027fe27fc27fa27f827f627f427f227f027ee27ec27ea27e827e627e427e227e027de27dc27da27d827d627d427d227d027ce27cc27ca27c827c627c427c227c027be27bc27ba27b827b627b427b227b027ae27ac27aa27a827a627a427a227a0279e279c279a27982796279427922
|10,0=>0x81718161815181418131812181118101
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 16
def pmP:Nat→Nat
|0=>0x11a0000000001180000000001040000000001000000000000d80000000000c000000000009000000000008000000000007000000000006000000000005800000000005600000000005000000000004e00000000004800000000004000000000003000000000002000000000001800000000001400000000001200000000001000000000000c00000000000a000000000009000000000008000000000006000000000005000000000004000000000002000000000001000000000000
|1=>0x22590000000020c80000000020c0000000002058000000002040000000002008000000002000000000001e790000000016f90000000014d80000000014000000000012dd000000001048000000001040000000001008000000001004000000001000000000000c000000000006690000000006000000000004500000000004480000000004310000000004080000000004010000000003d9000000000248000000000240000000000220000000000208000000000200000000000148
|2=>0x567d000000004ef90000000046f90000000044d00000000044980000000042dd0000000042d900000000429500000000425d0000000040d0000000004098000000004090000000004032000000004010000000004008000000003e79000000003e5b0000000036f10000000036e90000000036790000000034d80000000034c80000000034580000000032f10000000032ed00000000325d00000000324b0000000030d80000000030c80000000030480000000030400000000026f9
|3=>0x4004800000004004400000004004000000004000c00000004000800000004000500000004000100000004000000000002133b0000000200400000000200020000000200000000000166280000000164480000000164180000000162690000000146fd00000001400800000001225d0000000120080000000116fd0000000106f90000000102f90000000102db00000001001200000001000c00000001000800000000801000000000800000000000767d000000006208000000006008
|4=>0x816fd00000008167f00000008167d000000081679000000080e7d000000080bdb0000000806ff0000000806fb0000000806f900000008067d00000008067b0000000806790000000804780000000803fb0000000802db00000008025b00000008023900000008007b00000008007500000008006d00000008001800000008000800000008000100000008000000000005667900000005641800000005605800000005401800000005000c000000046259000000046018000000040448
|5=>0x1000000000000d667b0000000d66790000000d627b0000000d62790000000c067d0000000c06790000000c027900000009667f00000009667d00000009267f00000009267d00000009167d0000000906fd00000009067f00000009067d00000009067b000000090679000000090048000000086679000000084af90000000846f900000008467900000008445b0000000836fd0000000836f90000000832fb00000008267f00000008267b00000008267900000008225b0000000816ff
|6=>0x1084e79000001082a4e000001080e7b00000108067b00000108067900000100566800000090004a0000008a065300000081027300000080045e00000080040e00000080040000000080010200000080004400000080004000000080001200000080000a000000800008000000800004000000800002000000800000000000400400000000400058000000400042000000400040000000400000000000200401000000200001000000180475000000100100000000100048000000100018
|7=>0x700000800000408067d0000040800000000039a0602000003980672000003180e7b00000309067f00000309067d000003086675000003084e78000003080e7a000003080e780000030806790000030000110000028104120000021a0e7b0000020d667900000209465f000002084e7b000002084e79000002082e7b000002082e79000002081e7f000002080efb000002080ef90000020046780000020042b80000020032f8000001980a7a0000011002620000010a0672000001086e79
|8=>0x2000000800002000000000001008047100001003004000001000040800001000001800001000001400001000000a00001000000800001000000200001000000000000a180f7b00000810014a0000080c005b0000080a071b000008084e5900000808467b0000080842590000080836ff00000808173b00000808077b00000800133b00000800055f0000080001420000080001000000080000e2000008000042000008000008000008000002000008000000000007080678000007000470
|9=>0x2001267d0000200122a500002001167d00002001166100002001162900002001061b000020007224000020006e6c0000200046fd0000200046f90000200046b50000200044d00000200044980000200040d80000200040d000002000401000002000367d000020002eec0000200026fd00002000267900002000263d0000200022f9000020001653000020000ef9000020000edb0000200006f90000200006680000200004040000200002db000020000090000020000018000020000010
|10=>0x81000e61000080080679000080080008000080000678000080000408000047080e79000045080c79000043184e7a000043086e78000041002e7800002808467f000021084ef9000021082e7d00002108067d00002108067900002108026800002080800800002020066800002009167f00002009167d00002009127d0000200846fb0000200846f900002008467d00002008267d00002008167d00002008067d00002008067b000020080679000020080669000020080004000020080000
|11=>0x32008067900032008005000032008001800032000023d00032000005000030200023800030009027d00022008005800022000001800022000001000020508067900020108126800020008126d00020008067900012508027900012008027900010608067900010009127d00010009067d00010008167d0001000810580001000806790001000010400001000000400001000000100000c70806780000c3080e780000c308047800008508026100008309667d00008309467d00008309067d
|12=>0x60001005800052408026d00052008027d00052001022500050608167900050608027900050008167900050008127d00050008127900050008126500050008067900050008027900050000105800050000104800050000004000048309067d00044708027800042508067d00042009027d00042008067d00042008027d00042008027900040708067800040608067900040508067900040108027800040009067d00040008067900040001004800040000104000032100027800032008067d
|13=>0x904318067200904308067800900320061100900320021100804138067b00804128067900800108267900800108227b0040070008700040040008790020000812380020000800000010422004480010422000480010220846f90010200842f90008080a163b0008019a0e720008011a0e7b0008004211180008000a067b00080002004600080000065300080000021b00068309067d00064708067800060508067900060209067900060009067d000600090679000600090279000600080679
|14=>0xc00047080c78a00045080e7980000408067d400045080c79200306080679200002084ef918200308001118004308067810204108067910204008001808032208067908020208067904000000000002081081005002081009067b0208100104370208008a067302002800852a02002008877b02000888076b020002980e7302000089067302000088077b02000088067b02000080010a0200000200060108091a0f3a0108011a0f3b01000a180b7a
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x220d0000000030000c000f010080000
|6,0=>0x5800e80019871fa130e0080c10050017e0000044001111b1800780000800000008000000347804250500c0602019d1c40032000ce00000bc4206288000052001600c6300000003a00028c200000018418088005c000400c100601800260019800a4021280e041103144f0020503400030000c3800659d0040a0280014051100c0000120ed82390b034040b00002041a
|6,1=>0x5c000e8b80c06000188400c44500804fc158018e1d
|7,0=>0x68de9f7401ebc4ae04e14c27454854a58e30821ca6a65ac07ab6eee4329fe6c88158e635d4872d21f134200200914ad941319a346112e180421b78993d90dcc7b3b50cf90055a0323acc22f5f08b1e2ce4dc53800d7155cea12a3750024d98b9e85d7c00834646d052a0651f71b9ae9b21f6a8fa3dc0d9d20356f400783f92bca0925c912ced0e20d5832d1bb11d9c68
|7,1=>0xbb1df22cdd33e00ce10506e47631e8192c1547b4928c3e067110104246e840188e79145a6a0e0a645da97192076aaad10bb2ad9d193ee8209135c21c73695d8296d8f77839e2714f1db625c4e9080f2cfd0a1e50200348c401c150b3d9bae49c8000063f982342d2349f0ccc1a26b044b7bc0d237d246da765413b01a73c83086d1578260df04231b68c004664c4064d
|7,2=>0x8ca3b7fbc7ac8a3a29386c2307b0f16523c403454517b9c8b1290372ae026c5
|8,0=>0xec5a90771d2db9629e76a1a82a256bf9014a869c5e12f945f4d78873e4c1962aa9a92fafa5f473fad222968dab0ade2885dca128bf369e99a65649ee75ed8b6dd86e1dc45a1dbf14d64c86f7db543e194a5ca9ca17dc24c9b694d242dd1b9e7c910b8aa62f3b46f96add40e99fad95262e617ad7c6acd972fb3d0928fd516e27129532493335797071fb2d654dbe037e
|8,1=>0x15dbe59ef7aa9beb3d15fcbe4ec4f93604a5d5c65cdd36bc927d3e7a79496425d743dd9017570e70579babe2e630836522664ca35ae36e5d2d3e3b2797e54dc99669a75ea99377ccd2da3bea1d2993c4e4266be
|9,0=>0x716e49785bab756da32628747592b13ca25a3772ab058f51b6bdccda9d945a92ce92a7d128f46aea45d744a6c3f6e998c79d830a9dc05bf32a9a4ac2d98473dfd7ba05b27eb4aa
|10,0=>0x585a92e95515c93adb
|11,0=>0x94
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 48 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_203 7 roots_203 ops++addP pm 2 dom_58 5 roots_58 ops++addP pm 3 dom_250 9 roots_250 ops++addP pm 4 dom_187 9 roots_187 ops++addP pm 5 dom_235 10 roots_235 ops++addP pm 6 dom_123 9 roots_123 ops++addP pm 7 dom_218 6 roots_218 ops++addP pm 8 dom_202 5 roots_202 ops++addP pm 9 dom_211 8 roots_211 ops++addP pm 10 dom_219 9 roots_219 ops++addP pm 11 dzo_217_2 6 roots_217 ops++addP pm 12 dom_186 6 roots_186 ops++addP pm 13 dom_155 6 roots_155 ops++addP pm 14 dom_91 6 roots_91 ops++addP pm 15 dom_106 5 roots_106 ops++addP pm 16 dom_59 6 roots_59 ops++addP pm 17 dom_171 7 roots_171 ops++addP pm 18 dom_27 4 roots_27 ops++addP pm 19 dom_243 9 roots_243 ops++addP pm 20 dzo_201_2 5 roots_201 ops++addP pm 21 dom_217 8 roots_217 ops++addP pm 22 dom_170 5 roots_170 ops++addP pm 23 dom_107 7 roots_107 ops++addP pm 24 dom_185 7 roots_185 ops++addP pm 25 dom_121 7 roots_121 ops++addP pm 26 dzo_241_2 6 roots_241 ops++addP pm 27 dom_234 8 roots_234 ops++addP pm 28 dom_43 5 roots_43 ops++addP pm 29 dom_122 6 roots_122 ops++addP pm 30 dzo_249_2 7 roots_249 ops++addP pm 31 dom_57 4 roots_57 ops++addP pm 32 dom_242 6 roots_242 ops++addP pm 33 dom_115 6 roots_115 ops++addP pm 34 dom_179 6 roots_179 ops++addP pm 35 dom_139 4 roots_139 ops++addP pm 36 dom_89 5 roots_89 ops++addP pm 37 dom_241 8 roots_241 ops++addP pm 38 dzo_233_2 6 roots_233 ops++addP pm 39 dom_153 5 roots_153 ops++addP pm 40 dom_232 7 roots_232 ops++addP pm 41 dom_75 4 roots_75 ops++addP pm 42 dom_42 4 roots_42 ops++addP pm 43 dom_113 5 roots_113 ops++addP pm 44 dom_177 5 roots_177 ops++addP pm 45 dom_248 8 roots_248 ops++addP pm 46 dom_120 5 roots_120 ops++addP pm 47 dom_184 5 roots_184 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_217_2_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_201_2_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_241_2_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_249_2_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_233_2_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_184 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 147 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 19 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 147 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 284 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 28 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 284 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 202 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 74 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 202 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 63 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 63 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3333000033330000333300003333000033330000333300003333000033330000,1,17)] (by decide +kernel) lowS_237
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_254:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_251
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(9,11),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(32,96),(32,160),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,96),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(128,129),(128,132),(128,136),(128,144),(128,160),(128,192),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xfac688
|_=>0
def sO:Nat→Nat→Nat
|13,0=>8
|_,_=>0
def wAt:=mkWire dB 8 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 8
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x3f80
|_=>0
def pmB:Nat→Nat→Nat
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_127 12 roots_127 ops++addP pm 4 dom_251 12 roots_251 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_223 12 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [8, 1] }, { op := GateOp.or, inputs := [9, 3] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [2, 0] }, { op := GateOp.and, inputs := [11, 10] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.and, inputs := [6, 7] }, { op := GateOp.and, inputs := [0, 2] }, { op := GateOp.and, inputs := [3, 5] }, { op := GateOp.or, inputs := [14, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }, { op := GateOp.or, inputs := [21, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_53054_aux

theorem PEqualNP.Outside.L_meta_53054 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_53054_aux.main
