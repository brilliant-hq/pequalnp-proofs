import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52946_aux
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

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffff0f0fffff0f0fcfc0000fcfc0000fffff0f0fffff0f0fcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

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
def goal_99 : Nat := 0xeeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafafafafafaa0a0a0a0fafafafafafafafafafafafaa0a0a0a0
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcfcfcf0f0f0f0fcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefafafafafefefefea0a0a0a0fefefefefafafafafefefefea0a0a0a0
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccff00ff00ffccffcccc00cc00ffccffccff00ff00ffccffcccc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffaaffaaffeeffeecc00cc00ffeeffeeffaaffaaffeeffeecc00cc00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaa0a0a0a0fffafffafffafffafffafffaa0a0a0a0
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfff0fff0fffcfffccc00cc00fffcfffcfff0fff0fffcfffccc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffafffafffefffeeca0eca0fffefffefffafffafffefffeeca0eca0
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffff0000cccccccccccc0000ffffccccffff0000cccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffaaaaeeeeeeeeeeee0000ffffeeeeffffaaaaeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafaa0a0fffffafafffffafafafafafafafaa0a0
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffff0f0fcfcfcfcfcfc0000fffffcfcfffff0f0fcfcfcfcfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffafafefefefefefea0a0fffffefefffffafafefefefefefea0a0
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaa0000ffffffaaffffffaaffaaffaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffff00ffccffcccccccc00ffffffccffffff00ffccffcccccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffaaffeeffeeeeeecc00ffffffeeffffffaaffeeffeeeeeecc00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaa0a0fffffffafffffffafffafffafafaa0a0
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffff0fffcfffcfcfccc00fffffffcfffffff0fffcfffcfcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffafffefffefefeeca0fffffffefffffffafffefffefefeeca0
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_135 : Nat := 0xff000000000000000000000000000000ff
def goal_135 : Nat := 0xfefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def roots_135 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 7 0]

def dom_138 : Nat := 0x50500000000000000000000000000000505
def goal_138 : Nat := 0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
def roots_138 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00cc00cc00cc00cc00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeeca0eca0eca0eca0eca0eca0eca0eca0
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefefea0a0fefea0a0fefea0a0fefea0a0
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccccc00cccccc00cccccc00cccccc00
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeecc00eeeecc00eeeecc00eeeecc00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafafaa0a0fafaa0a0fafaa0a0fafaa0a0
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfcfccc00fcfccc00fcfccc00fcfccc00
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffefefeeca0fefeeca0fefeeca0fefeeca0
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefefefefefefefefefefefefefefefefea0a0a0a0fefefefea0a0a0a0
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffccffccffccffccffccffccffccffccffccffcccc00cc00ffccffcccc00cc00
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeecc00cc00ffeeffeecc00cc00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffafffafffaa0a0a0a0fffafffaa0a0a0a0
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfffcfffccc00cc00fffcfffccc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffefffefffefffefffefffefffefffefffeeca0eca0fffefffeeca0eca0
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeeeeee0000eeeeeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffffafafffffafafffffafafafafafafafaa0a0fafafafafafaa0a0
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfcfcfc0000fcfcfcfcfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffefefffffefefffffefefefefefefefea0a0fefefefefefea0a0
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaaaaa0000ffaaffaaaaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffccffffffccffffffccffffffccffccffcccccccc00ffccffcccccccc00
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffeeeeeecc00ffeeffeeeeeecc00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fff0fff0f0f00000fff0fff0f0f00000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafffafffafafaa0a0fffafffafafaa0a0
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffcfffcfcfccc00fffcfffcfcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffefffefefeeca0fffefffefefeeca0
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefafafafafafafafaa0a0a0a0a0a0a0a0
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa0000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffffccffccffccffccff00ff00ff00ff00cc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffaaffaaffaaffaacc00cc00cc00cc00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffefffefffefffefffafffafffafffaeca0eca0eca0eca0
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffff0000ffff0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffaaaaffffaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafaa0a0fafaa0a0
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffff0f0fffff0f0fcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffafafffffafafefea0a0fefea0a0
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffff00ffffff00cccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffaaffffffaaeeeecc00eeeecc00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafafaa0a0fafaa0a0
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffff0fffffff0fcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffafffffffafefeeca0fefeeca0
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffcccccccccccccccccccccccc00000000cccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafafafafafaa0a0a0a0
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefafafafafefefefea0a0a0a0
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccffccffccffccffccff00ff00ffccffcccc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffaaffaaffeeffeecc00cc00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffafffafffefffeeca0eca0
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffff0000cccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffaaaaeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafafafafafaa0a0
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffff0f0fcfcfcfcfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffafafefefefefefea0a0
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffaaffaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffff00ffccffcccccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffaaffeeffeeeeeecc00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafffafffafafaa0a0
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffff0fffcfffcfcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffafffefffefefeeca0
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
def isoMvS_138:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_138:Lower true dom_138 roots_138 goal_138 4:=lower_iso_b isoMvS_138 (by decide +kernel) lowS_21
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_21
def isoMvS_193:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_21
def isoMvS_208:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_21
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
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 4:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_27
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_23
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_23
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_23
def isoMvS_99:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_102:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_27
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_23
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_23
def isoMvS_114:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_27
def isoMvS_120:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_27
def isoMvS_135:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_135:Lower true dom_135 roots_135 goal_135 5:=lower_iso_b isoMvS_135 (by decide +kernel) lowS_23
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_23
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_53
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 7:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_85
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_23
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_53
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_23
def isoMvS_170:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_170:Lower true dom_170 roots_170 goal_170 5:=lower_iso_b isoMvS_170 (by decide +kernel) lowS_53
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_23
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_23
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 4:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_27
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_23
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 7:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_85
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_53
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_53
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 7:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_85
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_53
def isoMvS_212:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_85
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_53
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_23
def isoMvS_226:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_27
def isoMvS_228:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_23
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_23
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
|0=>0x1f59040
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5a
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_23 5 roots_23 ops++addP pm 1 dom_30 4 roots_30 ops++addP pm 2 dom_27 4 roots_27 ops++addP pm 3 dzo_23_8 5 roots_23 ops++addP pm 4 dom_21 4 roots_21 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_31 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
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
|0=>0x3ff3bdf348c288180
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10039245
|6,0=>0x678a
|7,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_46 5 roots_46 ops++addP pm 1 dom_39 5 roots_39 ops++addP pm 2 dom_37 4 roots_37 ops++addP pm 3 dom_42 4 roots_42 ops++addP pm 4 dom_45 5 roots_45 ops++addP pm 5 dom_43 5 roots_43 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_47 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_37 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_45 _ g hchk
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
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_slice_b [(0x330033000000000033003300000000,1,33)] (by decide +kernel) lowS_85
namespace S_155
def pG:List (Nat×Nat):=[(1,17),(1,129),(2,10),(2,18),(2,130),(3,11),(3,19),(3,131),(8,10),(8,136),(9,11),(9,25),(9,137),(16,17),(16,18),(16,144),(24,25),(24,26),(24,152),(128,129),(128,130),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_155.map (·&&&dom_155)
def gM:=goal_155&&&dom_155
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9aa9
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000000000000000000000000000f0f0000f000f000000000000000000000000000f000f00c0c0c0c0000000000000000000000000c0c0c0ca0a0a0a0000000000000000000000000a0a0a0af0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 156 0xfffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_154 5 roots_154 ops++addP pm 1 dom_153 5 roots_153 ops++addP pm 2 dom_147 5 roots_147 ops++addP pm 3 dom_139 5 roots_139 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_155 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_139 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_154 5 s (0,roots_154.map (·&&&dom_154)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_155 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_154 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_155==dom_155)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_155 gM v ys):RunD true dom_155 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_155 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_155 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_slice_b [(0x4040404000000000404040400000000040404040000000004040404,8,10)] (by decide +kernel) lowS_216
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
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 7:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_61
def isoMvS_107:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_59
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_55
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_59
def isoMvS_115:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 6:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_59
def isoMvS_118:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 6:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_59
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 6:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 8:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_47
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 8:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_117
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_87
def isoMvS_158:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 7:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_155
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_55
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_55
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 6:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_55
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_55
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_55
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 8:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_117
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_55
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 6:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_59
def isoMvS_186:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccccccccccccccccccc,126),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 7:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_155
def isoMvS_188:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_59
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 8:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_87
def isoMvS_203:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 7:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_155
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 8:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_117
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_117
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_117
def isoMvS_227:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_59
def isoMvS_230:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_233:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 6:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_55
def isoMvS_234:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_155
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_87
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_61
def isoMvS_244:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 8:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_87
def isoMvS_248:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_61
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=lower_slice_b [(0xffff0000ffff0000,1,17)] (by decide +kernel) lowS_47
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,8,10)] (by decide +kernel) lowS_93
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
namespace S_123
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(8,10),(8,40),(8,72),(9,11),(9,25),(9,41),(9,73),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,72),(64,80),(66,67),(66,74),(66,82),(66,98),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x62b5b32d0c07721
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688b1a23d8d11ac688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x398ee07
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa5a1
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfff6ff3ff2c5000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x53
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 6 roots_122 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_91 6 roots_91 ops++addP pm 3 dom_59 6 roots_59 ops++addP pm 4 dom_89 5 roots_89 ops++addP pm 5 dom_83 5 roots_83 ops++addP pm 6 dom_121 6 roots_121 ops++addP pm 7 dom_115 6 roots_115 ops++addP pm 8 dom_106 5 roots_106 ops++addP pm 9 dom_107 6 roots_107 ops++addP pm 10 dom_43 5 roots_43 ops++addP pm 11 dom_113 5 roots_113 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_113 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 6 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
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
namespace S_159
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,129),(2,10),(2,18),(2,130),(3,7),(3,11),(3,19),(3,131),(4,5),(4,20),(4,132),(6,7),(6,14),(6,22),(6,134),(8,10),(8,136),(9,11),(9,13),(9,25),(9,137),(12,13),(12,14),(12,28),(12,140),(16,17),(16,18),(16,20),(16,144),(24,25),(24,26),(24,28),(24,152),(128,129),(128,130),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x380cd
|7,0=>0xe73dda1dc099b9e6c5301fbed
|8,0=>0x4b6ad025ea
|9,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5555555500000000000000000000000050505050ffffffff000000000000000000000000fafafafaaaaaaaaa000000000000000000000000aaaaaaaaf0f0f0f0000000000000000000000000f0f0f0f0ffffffff00000000000000000000000000000000ffff0000000000000000000000000000ffff0000ff00ff00000000000000000000000000ff00ff00fafafafa000000000000000000000000fafafafaffffffff000000000000000000000000f0f0f0f0cccccccc000000000000000000000000ccccccccffffffff000000000000000000000000aaaaaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x547186543718654271865497186542710854718a6543218654971086543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5739c68
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 160 0xffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1e1764a176619764a3765e17641d86619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff1b7eff5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x7ae6
|8,0=>0x13
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_157 8 roots_157 ops++addP pm 1 dom_158 7 roots_158 ops++addP pm 2 dom_155 7 roots_155 ops++addP pm 3 dom_31 7 roots_31 ops++addP pm 4 dom_143 8 roots_143 ops++addP pm 5 dom_151 8 roots_151 ops++addP pm 6 dom_154 5 roots_154 ops++addP pm 7 dom_27 4 roots_27 ops++addP pm 8 dom_30 4 roots_30 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_30 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_157 8 s (0,roots_157.map (·&&&dom_157)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_157 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_159==dom_159)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_159 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_159 roots_159 goal_159 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_159
theorem lowS_159:Lower true dom_159 roots_159 goal_159 10:=S_159.noCircuit
theorem lowS_175:Lower true dom_175 roots_175 goal_175 9:=lower_slice_b [(0xffff0000000000000000000000000000ffff00000000,1,33)] (by decide +kernel) lowS_143
theorem lowS_183:Lower true dom_183 roots_183 goal_183 9:=lower_slice_b [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_181
namespace S_187
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,129),(2,10),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,10),(8,40),(8,136),(9,11),(9,25),(9,41),(9,137),(16,17),(16,18),(16,144),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,176),(128,129),(128,130),(128,136),(128,144),(160,161),(160,162),(160,168),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x90e6d33d86267da
|6,0=>0xa6c598dea220f09201e105623
|7,0=>0x956bf6a8884e6120efa7
|8,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f00000000000000000f000f000f000f00f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef0f0f0f0000000000000000000000000f0f0f0f00000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c0000f0f00000f0f000000000000000000000e0e00000e0ef0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f000f0000000000000000000f000f000f000f00e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c
|_,_=>0
def sP:Nat→Nat
|0=>0x8327a583207a583e27a58d327a58321754321758c321543207ab4327a5832917543291782176543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b64ac7d8c3917
|7,0=>0x8aef9dbbb16
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d5254c9a7615a74dda755d85615a769d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x10000
|6,0=>0x7252322111
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xa007bd7ad3bd1fd016006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x40
|6,0=>0x4afa
|7,0=>0x926
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 7 roots_186 ops++addP pm 1 dom_58 5 roots_58 ops++addP pm 2 dom_43 5 roots_43 ops++addP pm 3 dom_185 6 roots_185 ops++addP pm 4 dom_59 6 roots_59 ops++addP pm 5 dom_177 5 roots_177 ops++addP pm 6 dom_27 4 roots_27 ops++addP pm 7 dom_171 6 roots_171 ops++addP pm 8 dom_155 7 roots_155 ops++addP pm 9 dom_179 6 roots_179 ops++addP pm 10 dom_184 4 roots_184 ops++addP pm 11 dom_147 5 roots_147 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 7 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccccccccccccccccccc,126),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_187 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_187 roots_187 goal_187 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_187
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=S_187.noCircuit
theorem lowS_215:Lower true dom_215 roots_215 goal_215 10:=lower_slice_b [(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_213
namespace S_219
def pG:List (Nat×Nat):=[(1,17),(1,65),(1,129),(2,10),(2,18),(2,130),(3,11),(3,19),(3,67),(3,131),(8,10),(8,72),(8,136),(9,11),(9,25),(9,73),(9,137),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,88),(24,152),(64,65),(64,72),(64,80),(64,192),(66,67),(66,74),(66,82),(66,194),(128,129),(128,130),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|4=>21
|5=>61
|6=>70
|7=>45
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xfdd1bf54c9e76b6d68cdd5d0acdccdc3ec1ae4aba8b449700f81e7465e676042a3aa8a2f1cc2437718413160f211a990bfa00b809
|5,0=>0xfce5fe06c2d9ac1d28afce3b4c7aaab5fa9b4aeca89199fddd9eac298ed3929ea8f5648b3368643681da87c2cb7b72979b7f78d62701606b00d6a1bb6422a631fb553da5352351b5e4ecd64b27a4a990489d7457434505f42f9a42de63a20a396bf347ff2cc582b59e28a45274c51c1b91c00a1b28d17d4f16f8a13ce811ac10c73a0bad00ba0e0b0f20aee50910b042e803c3702eb6002c7
|6,0=>0xf8774e9e44e9e42d10c9cdde8cac29c3f91c2df8b9233afd39af887aa2d0a5771a4f8ca07c8955438f7a286d1184fe084f5a7e5fe7dbe37a75d79c86714df6daaa6d08965edc64768647245e71559c4c585515834f553c9550895308451a3f4da57404c03f8e63e8113c4593bf253a3be35f64342412cdf02c46225780255d021035200521e6fb1c69c149f311f1d118f910331100070f3180d3a90c0760bf8a049980371f0315b02594009360047d
|7,0=>0xf00f8dd6a0dadacd5208ce7a2cb3d6c9374bef50a9775a8cd4a263799c95925128cdfa861cc7d732761c86fb3d6a70457f4a553a95040047f3e45e14459cf427fb40282347e7346fb314592b8cc29b352711e22dce211171c5c01c5671816113a1e1370d12d0b0cb2d0ca870500101677
|8,0=>0xe4333dadacb456dab5afa019f75c2667fba488e42626f06cbf
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f00000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f0c000000000f000f00000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0cc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00005050505000000000505050500000000050505050000000005050000f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0f0f0f000000000f0e0f0e000000000f000f00000000000f000f00f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f000f000000000f0f000f000000000f0f0000000000000f0f0000f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|0,1=>0xf0f0f0f000000000e0e0e0e000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0e0e000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f0000000003030303000000000f0f0f0f0000000003030000f0f0f0f000000000f0f0f0a000000000a0a0a0a000000000a0a0a0af000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f0f0e0e000000000a0a0a0a000000000a0a0a0a000000f000000000000000f000000000000000f000000000000000cf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0f0f0a000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0303000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f00000000000f0f0f0f000000000f0f0f00f0f0f0f000000000c0c0c0c000000000f0f0f00000000000c0c0c000000000000000000f0f0f0f0000000000000000000000000f0f0c0c00000000000000000000000000000000f0f0f0f000000000f0f0f00
|0,2=>0x303030100000000030303010000000003030300000000000303030000f000f00000000000c000f00000000000f000f00000000000c000c5050505000000000505050500000000050505050000000005050404f0f0f0f0000000003030303000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f000000000f0f0c0cf0f0000000000000f0f0303000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0c0c000000000000000000000000000000000000000000000000303030300000000000000000000000003030000a0a0a0f000000000a0a0a0f000000000a0a0a0a000000000a0a0a0a0000a0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000000a0a0a0a0000000000000000000000000a0a0a0a505050500000000050505050000000005050505000000000404040400f000f00000000000f000f00000000000f000f00000000000c000cf0f0f0f000000000f0f0f0c000000000c0c0c0c000000000c0c0c0c0000000000000000303030300000000000000000000000003030300f0f0f0f000000000f0f0c0c000000000f0f0f0f000000000f0f0c0c
|0,3=>0xf0f0f0f000000000e0e0e0e000000000f0f0f0f000000000e0e0e0ef0f0f0f000000000e0e0e0e00000000000000000000000000000000f0f0f0a000000000f0f0f0a000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0af0f0f0f0000000000000303000000000f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f000000000e0e0e0e00f000f00000000000f000f00000000000f000f00000000000f000c000000f000000000000000f000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000e0e0e0e000000f000000000000000f000000000000000a000000000000000af0f000f000000000f0f000f000000000f0f000a000000000f0f000af0f0f0f0000000003030303000000000f0f0f0f0000000003030300f0f0f0f000000000f0f000f000000000f0f0f0f000000000f0f0000f0f0505000000000f0f0505000000000f0f0500000000000f0f050000f000f00000000000f000f00000000000f000f00000000000e000ef0f0f0f0000000001010101000000000f0f0f0f0000000000000000
|0,4=>0xf0f0f0f00000000000000000000000000000000f0f0f0f0000000000000f0f000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0af0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f0f0f000000000f0f0f0c000000000f0f0f0f000000000f0f0f0c000000000000000000003030000000000000000000000000000000000000000000000003030303000000000000000000000000020202020000000000000000f0f0f0f0000000000000000000000000a0a0a0a00000000000000003030303000000000000000000000000000000000000f0f0000000000000f0f00000000000000000000000000000000f0f0f0f000000000c0c0f0f000000000f0f0f0f000000000c0c0c0c0000a0f0000000000000a0f0000000000000a0a0000000000000a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00f0f0f0f000000000f0f0f00000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0f00f0f000f000000000f0f000f000000000f0f000f000000000f0f0000
|0,5=>0x50500000000000005050000000000000f0f0000000000000f0f0000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0af0f0f0f000000000f0f0f0f0000000000000000000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0a000000000f0f0f0a0000f0f0000000000000f0f0000000000000f0f00000000000000003030303000000000303030300000000030303000000000003030300f0f0505000000000f0f0505000000000f0f0000000000000f0f0000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a00000050000000000000005000000000000000000000000000000005050505000000000505050500000000000000000000000000000000f0f0f0f000000000d0d0d0d000000000f0f0f0f000000000c0c0c0c50505050000000005050505000000000a0a0a0a000000000a0a0a0a0000f0f0000000000000f0f0000000000000a0a0000000000000a0aa0a0a0a000000000a0a0a0a00000000000000000000000000000000f0f0a0a000000000f0f0a0a000000000f0f0000000000000f0f0000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a
|0,6=>0xf0f00000000000000000000000000000000f0f0f0f00000000050505050000000000000000000000000000000000000000000000000000000000000000a0a0a0a000000000a0a0a0af0f0f0f0000000005050505000000000f0f0f0f0000000000000000f0a0f0a000000000f0a0f0a000000000f000f00000000000f000f000000000000000000505050500000000000000000000000000000000a0a0f0f000000000a0a0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f0000000000000a0a0000000000000a0af0f0000000000000f0f0f0f000000000f0f0000000000000f0f00005050505000000000505050500000000050505050000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x850581001030142283a01e68101001828202283861a080800c6811d3e78d023a2820202703841e2c096083c59b143cd023228a0202603970c2c09608189010010a82021c21424043930c4808708441010e4020f040430518045041c2c0800c346011410482101c30504040040608080
|1=>0x40438634080b00e2431a042039008181010e103015e2838412080870c080ae141c31a04b45070818101581c30202951875618d02020100f343008a083c101005151a0404384540808a0e18d0c02294841c2c08a0e101015028384169d30a0e18d024a903940c080a30e103220228397
|2=>0xc4808a0e18d020201f170c2c08a7af0206160438634080bb0e5c206040400634e8101004c20f04043841e2c40a0e181017228384282c080704431a040438634dc1010e1048202003846a2c08a0e103016828384662c08a0e1190b022839708501010e3c31a0405606040588a0e4cb86
|3=>0x21c786340808a8e5031a1808087082458100283841e2ce811418d450404507081860202283841e080800e18d02027c3840c080807078d0202283863408c8a0e1058188283840c2c080850c20604043842808087701078b022a10482505810e1200b022838634fc11d0018d023a29f04
|4=>0x901c9840c2c0800e18d0202a05070c6859d032000634080a4141d006343008a0e3c31a0404007983cd0b3a283cb0818101141c78634301011418d0202283ca0c68602029438634080c9141c2091e2c08a0eac31a04045070c68101901ca0f34080874018d0202003841e0808a0e10a02
|5=>0xb05c30b022838634e8101141c2061604507ae18d550404507861030b0228386342c40a0e18d0b3b50504282c08a0ee079a160698a0e2431a04043d1342ce8a0c685d03b203863408e81001c20f160454f1e18d02020031a04752870c681019c1d506340808a0f3079a1674506342e681
|6=>0x2002410c2c08a0e18d0203743dc0818581141ca0f342c0800e5c206160454f0818581141e10634080db0e18602028c5070c6814d020039308181010e1078b022ab0634fc11d141c31a162000a0e10301b428384b22c08a0e18d3f04040070c68101141df04062c08a0e18d023a06407
|7=>0x342c08a0e18d0bc6045070c6859d03205074018d020228386342ce81002831a160710a0f8431a16045070c6858115803df342c08a0f7831a167408a0e1030b3a045071218d0b0228386342ce810028386342ea0a082c0a6141dc090c68588141c206169c08a0e1030202283b8283cd0b
|8=>0x404507083c581141c31a160698a0e3c31a160454f0c6859d4c28386ca2c08a0e1030b02283cf0c68581156c386342e68100283840c2c08a0ee031a1604507c818d020294386342e81d141e89a16045071e18d0202283940c681010e1030202283890c685810028386342e681141e60f
|9=>0xc685814c28386342c08a0f5831a174008a0e18d0b02283cf0c68581ce2838f0c68581002831a1604507d218d0b3a045071e18d0b02005070c686020228386342c08a0fa031a1674552283cd0b0228386342c080155831a179c5560c6859d022a7840c2c08a0f5831a160730a0e18d3f
|10=>0xc68581141ca06342c08a0e18d0b3a045070c68581141e9040c2c08a0e18d0b0200507
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x6450bea16942aa8505096a119420a83c506ea0c9416a8285046a07940ca814501ea029402a8005
|5,0=>0x1cf6392c70d8deb1b76362c6ad8d2b19f6332c64d8c6b1876302c5ed8bab16f62d2c58d8aeb15762a2c52d8a2b13f6272c4cd896b1276242c46d88ab10f6212c40d87eb0f761e2c3ad872b0e051b4c35186730c86184c2f185ba8b16156c29584fb0996126c235843b08160f6c1d5837b0696
|6,0=>0x6eeedc59b53b6376b8ed55da7b3487682eced99ab32e764eec8598db314761aec1d9803af975e4ebadd723add75aecb459653ac3757acae1558baaa7548ca7994c32926516ea1593f3a7774e0e9a5d313a5b74a8e935d233a3f7470e8c5d153a237438e85990832097406c7f94fbb9f073d2e78d8ee39d57
|6,1=>0x1d02b997724ee2ddc23b7e6
|7,0=>0x4d6799ef321e6044b97964f2b1a52bc9e7930d245e453c8378f8f1d9a37bc6878c2f16da2a3c4d788b10f9e1bbc316854f091a0ebc176822d0262013bfb77e8efb21f2bbde77aeef41de4bbc367770ed1dd6bba58
|8,0=>0x28dbd147a1af41da803cf979e4f3ade723cdd7
|9,0=>0x5226
|_,_=>0
def wAt:=mkWire dB 106 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1d0c2916293419041e1629041d141916290c690c01141d021d34190c1d05190c1e1629041d162934191629141d261c3419261d082934191629081e3419261c0013021d0405045c081d34197e1c16290c1d16296c190876021d081e16291629141d261f281d16290c1d041d1629401c081d0c69141d0c1d1e0b041e1629141d
|1=>0x1629141d0d49021d021c3a2b021d021d1629141d0c69141e0c1d16290c1d141d021d142d022b142d15190c1e041e16290c1d021d021915213a2b021d141d3a2b021d1807041d041d16290c1d1629141d021d021908091629041d142d0c1d041d142d022b34190c1d401f0419142d3a2b021d162914190c1d1629141d16293419
|2=>0x141d14190c1d3419261c0829341916290c02141d3432041d16291629141d0829162934193419021e0c1d021d040512070c01165e081d34190d593419021e141d7e1c040516290ce1081e341916293a2b021d081d080534197e1f040505591629021e00110c69141d12070c01141d3b4b021d021c081e34190c1d3a1b021d0019
|3=>0x142d022b021d02290d49021c142d0c1d14191629162934190c01141da01d02290c1d021903190c1e3a2b021d04191629021d141d4c1d021b0d3d141e0202141d0d4b021c021d3419021d0c01141d021d141d3b4b021d021c081e3419141d02e1081e1629081e34190c290c1d141d145e081d34194a1d142d022bb01d08053419
|4=>0xc29021d021c3419141d021b021e0229141e021f0c1d141d281e0c29ce1d021f0c1d141d041d16294a1e022b021d021c14190c1d021e141d021e021f141e021d3419021e1559021e0405162934190c1d3a1b021d141e0c1d021d021b3549021c141e34190c02141d0201141d081e3419a01e0229
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x620000000000000000000008400000000000000000000000008000000
|5,0=>0x292000000000000000009c848621310080003e21d2000068c32200000000003020000b1000000000000000000001330000484000111000000000000007903840000c20000000000000000024c000000000020400000000000000000000298000082000
|6,0=>0x631b0cd806bd35e0ae4d6c6b335892b8d566a92539290d426a014e9a68d2e694349100011e68c3449a18d0848133f19eccf247633999c0cda66a3341194cc4661100017c8ba45b22c19588a84513000138c0004c225111cc8864221f98f0c7443731a18c4c5c62b3
|6,1=>0x1a86d22688b3c9986c93
|7,0=>0x12e29614a8a505262921488a4051e28e1468a3051628a1448a2050e2861428a105062821408a004fe27e13e89f04f627a13c89e04ee27613a89d04e627213889c04de26e8b6c9b24d72
|8,0=>0x27233819b8cd866a3341998cc86623301
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x18000023740042e0008510010100018000026780048b000810001000001000001df0003b400073c000830001020001c20003240005080009000010a000200000200000200000300000400000400000400000600000800000800000
|1=>0x719e00e33401c658038c900709600e02001a678030cb00519e00a3340146480284b00501000a0000126f8020cd0040b400733c00e038018cf00319a00631c00a858014cd00239600437c008678010c300211000420000810001008
|2=>0x20318e40533c80a629011cb2003144004288004210008118880008c364100680200900400a00801000c06f0100df02012004002005c2580b80801619602a32c0540400a0cb0140020243680484400885401038e02033c0336f8045df
|3=>0x100e3350146da020104000308000208486590908821039e42062881c60901c87
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x1000000000000800000000000010000
|5,0=>0xa000000000141972c00107000430000004003400000000080900080160000000085401100000000030000001800000000002e00300
|6,0=>0x181f0828ba71a741a342628d365056e70a3d2685f7598bcc029031cc0bd886c0dba531a22514aa39a008028a8a8abd4007005a9cd09cf3300555b782954
|7,0=>0x654afb25656dae3b7ced73dd379627c3a9cc292a1c1e76f9314638a45f58ea84d6a9653cb2bb1cc
|8,0=>0x93f7c665b57eddc3e
|9,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_138 4 roots_138 ops++addP pm 2 dom_202 5 roots_202 ops++addP pm 3 dom_155 7 roots_155 ops++addP pm 4 dom_153 5 roots_153 ops++addP pm 5 dom_83 5 roots_83 ops++addP pm 6 dom_211 8 roots_211 ops++addP pm 7 dom_203 7 roots_203 ops++addP pm 8 dom_139 5 roots_139 ops++addP pm 9 dom_147 5 roots_147 ops++addP pm 10 dom_195 5 roots_195 ops++addP pm 11 dom_218 6 roots_218 ops++addP pm 12 dom_91 6 roots_91 ops++addP pm 13 dom_154 5 roots_154 ops++addP pm 14 dom_209 7 roots_209 ops++addP pm 15 dom_27 4 roots_27 ops++addP pm 16 dom_201 5 roots_201 ops++addP pm 17 dom_89 5 roots_89 ops++addP pm 18 dom_193 4 roots_193 ops++addP pm 19 dom_145 4 roots_145 ops++addP pm 20 dom_75 4 roots_75 ops++addP pm 21 dom_216 5 roots_216 ops++addP pm 22 dom_210 5 roots_210 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_138 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_210 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 21 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 21 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 70 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 70 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 10:=S_219.noCircuit
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505040000000005050504000000000504050400000000
def gsh_218_32:=0x5050505000000000505050400000000050505040000000005040504
theorem lowS_zo_218_32_208:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x4040404000000000404040400000000040404040000000004040404,0,2),(0x5000500000000000500050000000000050005000000000005000500,0,8)] (by decide +kernel) lowS_208)
namespace S_250
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,34),(2,130),(8,10),(8,40),(8,72),(8,136),(16,18),(16,80),(16,144),(24,26),(24,56),(24,88),(24,152),(32,34),(32,40),(48,50),(48,56),(48,112),(48,176),(64,72),(64,80),(64,192),(66,74),(66,82),(66,98),(66,194),(96,98),(96,104),(96,112),(96,224),(128,130),(128,136),(128,144),(128,192),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xea11622d09
|8,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a000000000a0a0a0a0000000141414140000000014141414000000001414141400000000141414140000000282828282828282828282828282828282828282800000000282828280000000505000005050000050500000505000005050000050500000505000005050000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a0101010101010101010101010101010101010101010101010101010101010101282828282828282800000000000000002828282828282828000000000000000505050505050505050505050505050500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x34688f1a22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc3c1
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfefcf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>9
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_186 7 roots_186 ops++addP pm 2 dom_242 7 roots_242 ops++addP pm 3 dom_234 7 roots_234 ops++addP pm 4 dom_218 6 roots_218 ops++addP pm 5 dom_122 6 roots_122 ops++addP pm 6 dzo_218_32 6 roots_218 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_218_32_208 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_250 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_250 roots_250 goal_250 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_250
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=S_250.noCircuit
def isoMvS_111:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 9:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_63
def isoMvS_125:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_iso_b isoMvS_125 (by decide +kernel) lowS_119
def isoMvS_126:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_123
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_119
def isoMvS_190:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_187
def isoMvS_207:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_207:Lower true dom_207 roots_207 goal_207 10:=lower_iso_b isoMvS_207 (by decide +kernel) lowS_159
def isoMvS_221:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 10:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_215
def isoMvS_222:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 10:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_219
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_119
def isoMvS_235:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_187
def isoMvS_243:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_119
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_215
def isoMvS_246:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_119
def isoMvS_249:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 9:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_119
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccccc8cccccccccccccc80
def gsh_125_2:=0x33333333333333323333333333333320
theorem lowS_zo_125_2_69:Lower true dzo_125_2 roots_125 gzo_125_2 7:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33003300330033003300330033003300,0,8),(0x33330000333300003333000033330000,0,16),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec00
def gsh_119_8:=0xff00ff00ff00ff00ff00ff00fe00ec
theorem lowS_zo_119_8_21:Lower true dzo_119_8 roots_119 gzo_119_8 7:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xcc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_117_2:=0xcc00cc00cc00cc00cc00cc00cc00cc
def gzo_117_2:=0xcc00cc00cc00c800cc00cc00cc0080
def gsh_117_2:=0x330033003300320033003300330020
theorem lowS_zo_117_2_69:Lower true dzo_117_2 roots_117 gzo_117_2 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_2) [(dom_117,2)] (by decide +kernel) (lower_slice_b (T:=gsh_117_2) [(0x330000003300000033000000330000,0,16),(0x330033000000000033003300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330033003300330032002000
def gsh_117_8:=0x330033003300330033003300320020
theorem lowS_zo_117_8_21:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x330033000000000033003300000000,0,32),(0x330033003300330000000000000000,0,64)] (by decide +kernel) lowS_21)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000ccc80000cccc0000cc80
def gsh_109_2:=0x3333000033320000333300003320
theorem lowS_zo_109_2_69:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3300000033000000330000003300,0,8),(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8:=0xff00ff00fe00ec00
def gsh_55_8:=0xff00ff00fe00ec
theorem lowS_zo_55_8_21:Lower true dzo_55_8 roots_55 gzo_55_8 6:=lower_iso_b (d1:=dom_55) (r1:=roots_55) (T1:=gsh_55_8) [(dom_55,8)] (by decide +kernel) (lower_slice_b (T:=gsh_55_8) [(0xcc00cc00cc00cc,0,2),(0xff00ff00000000,0,32)] (by decide +kernel) lowS_21)
namespace S_127
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(2,10),(2,18),(2,34),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(4,36),(4,68),(6,7),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(9,11),(9,13),(9,25),(9,41),(9,73),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,18),(16,20),(16,80),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,98),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|7=>12
|8=>62
|9=>42
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xa22dc9d1b868582447ff439392c42727aa320f710bb1109d830989a0225a
|8,0=>0xf6acfe7577cc856c4f7fba62da731e8cb098390a8382881b0c8046a7b4da791b976984659f46402761f6961db0619b360d795fa7c5d9915d8dd4de9f48d144708f4149a410bf3e9eb3da493cf8a3c3233bb933bb7638c852fc2a2cf5c2be5129d59289a62852026d0626a532570d23fd4220eb20eb91c77916af2134e61255f11a85105260d3350d28b071ff05c31032fb0273e023b80200501353
|9,0=>0xd68f1d2632a39939bd469987d9797e917868f97d87dfe7f2397e1fb7942b719095bce154f264db0c4c0d14a76640bd53e88c3e2c43cb5b30394291b82150d1b6f51914a118ea10fcf101700fe730f8b00b65c0b3ce0a7920a10409fe006e0805b69037ed032b501b47
|10,0=>0xf69eda0d88761fa581863fcd23b65b2fbbe2654f
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff0000aaaa0000ffff0000aaaaffffffffaaaaaaaaffffffffaaaaaaaafffffffffafafafafffffffffafafafa0000000000000000fffffffffafafafaffffffffffffffffffffffff00000000fffffffff0f0f0f0fffffffff0f0f0f0ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffffffffff0f0f0f0ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00fafafafafafafafafafafafafafafafaccccccccccccccccccccccccccccccccffffffffffffffffaaaaaaaaaaaaaaaa
|0,1=>0xf0f0f0f0f0f0f0f0fefefefefefefefe0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0acfcfcececfcfcececfcfcececfcfcecefcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcffffccccffffccccffffccccffffcccc54545454545454545454545454545454fff0fff0fff0fff0fff0fff0fff0fff00f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0000000000000000fffffffafffffffaffffffffffffffffffffffffaaaaaaaafffafffafffafffafffafffafffafffafffffffffffffffff0f0f0f0f0f0f0f0ffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffaaaaffffffffffffaaaafffff0f0fffff0f0fffff0f0fffff0f0fffffffffffffffffffffffffafafafa
|0,2=>0xafafafafafafafafafaaafaaafaaafaaccccccccccccccccfefefefefefefefefffffafafffffafafffffafafffffafafffffefefffffefefffffefefffffefe0000000000000000fafafafafafafafaff00ff00ff00ff00fffafffafffafffafffffffffffff0f0fffffffffffff0f00000000000000000fffffffff0f0f0f00000fafa0000fafa0000fafa0000fafaffffffff0000fafaffffffff0000fafa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0affaaffaaffaaffaaffaaffaaffaaffaaffffffffffffffff0f0a0f0a0f0a0f0affffffffffff0000ffffffffffff00000000000000000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
|0,3=>0xfefefefefefefefeffffffffffffffffffaaffaaffaaffaa0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0afefefefefefefefefefefefefefefefe0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0affffffffffffffff0f0f0f0f0a0a0a0affffff00ffffff00ffffff00ffffff00ffffffff0f0f0f0fffffffff0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0acfcfcfcfcfcfcfcfcecececececececeffffffffffffffff5454545454545454ffffffffffffffffeeeeeeeeeeeeeeee0000ffff0000f0f00000ffff0000f0f0f0f0fffff0f0fafaf0f0fffff0f0fafa0f0f0f0f0f0f0f0f0f000f000f000f00ffffffffffffffffff00ff00ff00ff00
|0,4=>0xff00f000ff00f000ff00f000ff00f000000000ffffffff00000000f0f0f0f0fffffff0fffffff0fffffff0fffffff0ffffffaaffffffaaffffffaaffffffaa05050404050504040505040405050404ffffffffffffffffccccccccccccccccfffffffffffffffffcfcfcfcfcfcfcfc555555555555555554545454545454540000000000000000555555555050505000fa00fa00fa00fa00fa00fa00fa00faccfeccfeccfeccfeccfeccfeccfeccfefffffffafffffffafffffffafffffffa00000f0a00000f0a00000f0a00000f0afffffffffffffafafffffffffffffafa5555444455554444555544445555444400000000000000005550555055505550
|0,5=>0xfafafafa00000000fafafafa00ff00ff00ff00ff00f000f000f000f00000000000000000ffaaffaaffaaffaa55555555505050505555555550505050
|_,_=>0
def sP:Nat→Nat
|0=>0x320ca010020284061c0883c24284061ce81102429b080c3883424284320c088302490a1c101820224297080c38110385840608a011858284061c0880a10a83280400c1c2c2030e044121410182022490e0a44182022480c0a101870220504060808f123460b080c38110182840608080
|1=>0x641c08812142030e057881258284065038110142035c1c0881215604061c088121422a061c08812882830e0441812a4284060808812a028406080881240305080c3811025305080c3811024284061c088462470b080ca07022110a080c1011024284067c3811024605080c3811024284
|2=>0x2204901a142030e044090a44983040448522101bc0220485080c38110e8485721038110944b80a1018702204921c14203041c0894414983041c0890c28284061c08010142030ed808812142030e0402512142030e044351214203381da0812382030e04433122828406080801214203
|3=>0xa101870220485080c3c5102490d0a10187022048588101870220485080c381110c4901c142030e0440984142030e044091a38584061c0881214203381c44112142030e04440122c2030e0443b1214203381d0881234605080c381102428406fc3811024284061c0887a2490a1c10187
|4=>0x80c3811024291080ce011024284061c0888224284061c0881e242842a0c1070220485080c3a102204850855807022048d1610187022049214101870220485080c381112c485080d587940440a1c10182022428406f03ca1024284061c08890251055a0c3811024284061c0888e2460e
|5=>0x1214219601c0881214984067038110242847c0c3811024905080c3811024284061c088a424284a20c3811024284061c088a024284061c0889e242b9080c107022048d14142030e044090c14203281c08812142030e0443712142030e0444e1216691080c381102470b080c38110242cc
|6=>0xe044090a1018702212891614203041c08812142030e044271214884480c3811024685080c3811024585080ca070220284600c107022048526101820e04485080ce07942048a0a4c2030e0440914382030e044090a1018702223091c14203041c0890a101940e040080a11f030e04008
|7=>0xa1018702204857210187022048e0a10187022048b0a10187022048508c01870220485080c1070220485080c381002048508641870220485080c3811024284061c088a62428406f038110242ad080c381102490e0a101870220485080ce07402048d0a10182
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x14a04b7111c3c80d5c2d8099c1e805a00f701e0007
|8,0=>0x92624188e623188a6222786a212882a20287e65f277a65e187661d097221bf96de1af869e19f865a58e861a17d95d256d759615d855614d851253c84ce52b848e11b844e10b840e0fb83ce0eb838e0db834e0cb830e0bb82ca4aa828a09a824a08a820a07a81ca06a818a05a8
|9,0=>0xe9a39e8e5a38d9e1637c9dd236b9d8e35a9d4a34a8d067398cc63289c823188c423088bfe6f78bba6e68b7a2d68b3a2c68afa2b59ab26a39a6e2938a2a68289ea27289aa26289666518
|10,0=>0xf963dd8f563cd8f163bd8ed63ae7
|11,0=>0x3ed7
|_,_=>0
def wAt:=mkWire dB 84 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa210e250a250a11101d0a1d0e85128202211a271c1d0a21061d10250e25241f1c110a2102610e4e101102113823021d261f0821061d0a1d1c110e210a210a250e250e210a2120272c1d1c251221040d0e25101d1c1d0a210a4d1011101d0a1d1c110e110a211a251a271c1d101d1c130a1d0a211c1d0a2114251025101d0a1d
|1=>0xe0210251c110e210a210a1110110e21142510250a1d02dd0e021025481f1025062112693823021d00051221021d14130a210a1d1025101d0a1d0e3d1c130a2110c5601f0625121d1c250a2102ad04270e215a0504110e2106ad04270e210a110e4e1011101d14110a1d1427101d0a1d14250a1d0a9d04130e214a25481f0621
|2=>0xa1d1a271c1d0a210319040f0e211c111c1d0a212291081d06212292081d06211a251c1d0a21241d1c110a210a251c1d0a210e053623021100661025061d0a251c1f0a2140270221021d1a271c1d0a2178273821021d7c1f482506211c110a1d0a211c1d0a210e210e11101104050e11101d76251c1f0a21481f080d06210add
|3=>0xa2106520e254827062114230a1d06460e1106110e2114210a1d0a510e250e0210250a520e2506450e110a250a21089106210e11021d362302111c130a21040d0e211282022106090e2106250a090e210a250a1d1c110a21360b0e210211120504270e210a1d0e210a21020902250e2192231271021d04110e210a1114031025
|4=>0x6110a210a2506250e211025061d0a0a0e213821021d04110e211c110a210221021d0a090e21481f06210e210a2504130e21081d06211c1d0a210e250a250e21062510110e211205021d10110a1d0a1d0a21040f0e210e210a210e251025060110250625061d1011021d482506211c11
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x10a00003a81a30b205082080d30518190084004
|8,0=>0x1b46d736a1b44d9c6cb3641b14d846bf35e1ae4d6c6b33581ab4d546a73521a84d3c69b34c1a54d2468f3469228d0e68434099f8cf667833a99c8cde66c3349998cc666032e9968cae6543289938c96648323110cc8063d31d18dcc6863131718acc506253
|9,0=>0x25e52d29594a4a4e5252919484a3e51d28d9464a2e5152899444a1e50d2859424a0e50528194049fe4fd27d93e49ee4f527993c49de4ed27593a49ce4e527193849be4dd2
|10,0=>0x9b8cd866a3341998cc86622000
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x1004b3300007008000000700001000068000100004f69b300004c69b700004c22140000456bb3000010000100000e211100000e080300000469b70000036ba700000369b30000026bb70000022b1300000221bb0000020a07000001fa100000016bb300000169b700000169b3000001418300000129fb0000000b030000000b00000000080000000007b500000000fe00000000cf000000000e0000000000
|1=>0x5016fbb0005016bbb0004436ba700040369bb0004022bf30004012fbb00040103fb0003496993000301e99300030179930003016993000301681300018149b30001814933000181483300018140b300014d69b300014969b300010569b700010569b30001036bb700010369b700010369b3000101e99300010179930001016bb30001016b9300010169b700010169b3000101609b0001014bb300010149bb
|2=>0x4018149b304010149b30305814db303058149bb02018149b302010149b301010149b3008c0169b300800205f30060016993001201e81300114969b300114169b300110169b300110149b30010422b13001014291700100169b300090169ff00080169ff00080169b300080021ff00080001ce00080000cf00080000830007416b93000701ed930007016d930005436bb7000541fb830005416bb70005416bb3
|3=>0x901141e9938003416b938003016993800101699340018149b340010149b32005017d932005016b932003016993200301619320010169931012497813100301e99308018149b3080181483307000142b3
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x400c971a141813a10296
|8,0=>0x1a1195a8fc364cdd120f5a3b55072c0e609ca310ccdac83cff00bcd3a4b92b46ad9c23e80bd93d0da4a22b903a3141a77785649681822
|9,0=>0x205b7f32dbd6e6134556bf73ec4f154683537b5b8d66b8c6a6268266e92ed2b73ddd69215f
|10,0=>0xca9166d814db09
|11,0=>0x23
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 40 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_126 9 roots_126 ops++addP pm 1 dom_123 9 roots_123 ops++addP pm 2 dom_94 6 roots_94 ops++addP pm 3 dom_110 6 roots_110 ops++addP pm 4 dom_47 8 roots_47 ops++addP pm 5 dom_93 8 roots_93 ops++addP pm 6 dom_79 7 roots_79 ops++addP pm 7 dom_111 9 roots_111 ops++addP pm 8 dom_95 9 roots_95 ops++addP pm 9 dom_122 6 roots_122 ops++addP pm 10 dom_107 6 roots_107 ops++addP pm 11 dom_63 9 roots_63 ops++addP pm 12 dom_115 6 roots_115 ops++addP pm 13 dom_87 8 roots_87 ops++addP pm 14 dom_125 9 roots_125 ops++addP pm 15 dom_118 6 roots_118 ops++addP pm 16 dom_119 9 roots_119 ops++addP pm 17 dom_91 6 roots_91 ops++addP pm 18 dom_31 7 roots_31 ops++addP pm 19 dom_59 6 roots_59 ops++addP pm 20 dom_30 4 roots_30 ops++addP pm 21 dom_27 4 roots_27 ops++addP pm 22 dom_58 5 roots_58 ops++addP pm 23 dzo_125_2 7 roots_125 ops++addP pm 24 dom_117 8 roots_117 ops++addP pm 25 dzo_119_8 7 roots_119 ops++addP pm 26 dom_106 5 roots_106 ops++addP pm 27 dom_78 4 roots_78 ops++addP pm 28 dom_62 6 roots_62 ops++addP pm 29 dzo_117_2 6 roots_117 ops++addP pm 30 dzo_117_8 6 roots_117 ops++addP pm 31 dom_75 4 roots_75 ops++addP pm 32 dom_121 6 roots_121 ops++addP pm 33 dzo_109_2 6 roots_109 ops++addP pm 34 dom_124 6 roots_124 ops++addP pm 35 dom_61 7 roots_61 ops++addP pm 36 dzo_55_8 6 roots_55 ops++addP pm 37 dom_103 7 roots_103 ops++addP pm 38 dom_109 6 roots_109 ops++addP pm 39 dom_55 6 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_125_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_119_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_117_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_117_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_109_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_126 9 s (0,roots_126.map (·&&&dom_126)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_126 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 62 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 62 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 42 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
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
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00fe00ec00
def gsh_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00fe00ec
theorem lowS_zo_183_8_21:Lower true dzo_183_8 roots_183 gzo_183_8 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff00000000,0,32),(0xff00ff00ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300330000000000000000003300330032002000
def gsh_181_8:=0x3300330033003300000000000000000033003300320020
theorem lowS_zo_181_8_21:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x3300330000000000000000000000000033003300000000,0,32),(0x3300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_21)
namespace S_191
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,129),(2,10),(2,18),(2,34),(2,130),(3,7),(3,11),(3,19),(3,35),(3,131),(4,5),(4,20),(4,36),(4,132),(6,7),(6,14),(6,22),(6,38),(6,134),(8,10),(8,40),(8,136),(9,11),(9,13),(9,25),(9,41),(9,137),(12,13),(12,14),(12,28),(12,44),(12,140),(16,17),(16,18),(16,20),(16,144),(24,25),(24,26),(24,28),(24,56),(24,152),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,176),(128,129),(128,130),(128,132),(128,136),(128,144),(160,161),(160,162),(160,164),(160,168),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_191.map (·&&&dom_191)
def gM:=goal_191&&&dom_191
def NN:Nat→Nat
|5=>6
|6=>45
|7=>106
|8=>128
|9=>61
|10=>10
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xdfecda092c95d1c7a256703455ceec
|6,0=>0xfb001d1f18d0a0dcd6fbcba5dc5eafc01faa63a3a3f309e30a9ab56991898ca748c58d7cd4e79baa6c4e26b17d69b9662ae36024a4c62b4a45946ce04647b43c9343b0340a793c56a3c40d38c6c311962a6ef2993528c152628f235c52066a1a3d117322142f3116700916f060e900355
|7,0=>0xefab1ee628eac0fe6befdb873c9c50c925ebae27b7969b33e5b1938ad826ad8249b7c5993a79092e8b40789be186af88399481f80815f7806b67f7a17ecec7c135778267731a767f475dd374dda6e9986bade6b28a6ad55698bd67f4b67c6b6797c671c366a9964a716363a61bba60b99609455f25a5ded75db9e5813b57f6c574ab5510453b6e534295191c50ca84f8c44f4264e1b64a4e24a22e4458142c5c425ef4252541cc24121140ef33e8633b5343b0c4395cb35dbb35c7930f3e2be95288b1286cf283d826261243aa216ca20c201deae1db711c5071be29170e7157381460513ce2131c112f59102500f3670ee190cc9e0bce008e6f0621f04e910410802dd00205602047
|8,0=>0xf438bf2710ed5c4df668dc3c5cf005cc8b3cc1aaca6a7c06b6bff7dba52eba1dfaa431a6c01a2f06a2743993ad923158b96d89fce8850185cf084349830cf82b567ea9a7cdf57c4477c3317bb247613573d4373758710546f8836e5406b9a46b0a56ac1269e89678646166d6065b5e1355dee15d62e5cea15b9535aa9258d29582f05816b57fa05587153dad53941531eb5273c50a7d5054c4e8ab4bbec4bb1d4ae374945348d7446f2846aea46758456b4450d342dd64131c3f0cc3bb4339d1936b6736b35355c132a493143d2ff092ef1d2cfa727ffb27a352762c26ce623dac237fd2365222c69226f92266d2205021ca9210c3205c11f7ab1f5221e40a1e1eb1d2351b0ef1ad3e16bd1163f1156681524a13fd213f141387212c59127bd102e00edce0ed9b0a2dd098710909c08e0d0764f063ad0627103acf03240011e9
|9,0=>0xc6c64c3587b37e4b3587b09ebad4f6a7ab4a49caa39859f3f49addb96d5f8b4948b3568977b889208736485e6282b807cc777a5ff76a1274486738b8737895e21b5dd625a5525911358cc95697054aaf52dfc513494fcb84ee324e8b84c7bd4a74149961423923eda63e38d3ca533b70e33fec321bc3186d2d08826f6424fd11ebec1d154147f1116560fbbf08eca060250363c034710292c
|10,0=>0x94cff6b2b35dccf57a9d47cdd320cd2eaa6266a61deb511d8d
|11,0=>0x2bff1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000ccccccccccccccccffffffff000000000000000000000000ffffffff00000000ffffffffffffffff0000000000000000ffffffffaaaaaaaafefefefefefefefe0000000000000000fefefefefefefefeffffffffffffffff0000000000000000ccccccccccccccccffffffffffffffff0000000000000000fffffffff0f0f0f0fcfcfcfcfcfcfcfc0000000000000000fcfcfcfca8a8a8a8eeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeeeffffffffffffffff00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00fcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfceeeeeeeeeeeeeeee0000000000000000eeeeeeeee0e0e0e0ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa
|0,1=>0xff00ff00ff00ff000000000000000000ff00ff00cc00ccffffffffffffffff000000000000000000000000fefefefeffffffffffffffff0000000000000000ffffffffeeeeeeee555555555555555500000000000000005555555554545454111111111111111100000000000000001111111110101010ffffffffffffffff0000000000000000eeeeeeeeeeeeeeeeffffffffffffffff0000000000000000fefefefefefefefe0000ffff0000ffff00000000000000000000fefe0000fefeffffffffffffffff0000000000000000ffffffffcccccccc5454545454545454000000000000000054545454545454540f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a00dd00dd00dd00dd000000000000000000dd00dd00dc00dcffffffffffffffff0000000000000000eeeeeeeee0e0e0e0ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f000cf00cf00cf00cf000000000000000000cf00cf00ce00ceaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
|0,2=>0xfcfcfcfc00ff00ff00ff00ff000000000000000000ff00ff00fe00fe5555545455555454000000000000000055555454555554540f0f0e0e0f0f0e0e00000000000000000f0f0e0e0f0f0e0e0f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0affffffffffffffff0000000000000000fcfcfcfcfcfcfcfcffffffffffffffff00000000000000000000000054545454ffffffffffffffff0000000000000000ff00ff00ff00ff00aaaaaaaaaaaaaaaa0000000000000000aaaaaaaafefefefeffffffffffffffff000000000000000000000000eeeeeeee0000ffff0000ffff00000000000000000000ffff0000fefedddddddddddddddd0000000000000000dddddddddcdcdcdcbbbbbbbbbbbbbbbb0000000000000000bbbbbbbbbabababafafafafafafafafa0000000000000000fafafafafafafafa00ff00ff00ff00ff000000000000000000ff00ff00ee00eeffffffffffffffff0000000000000000fafafafafafafafa
|0,3=>0xdddddddddddddddd0000000000000000dcdcdcdcdcdcdcdcffffffffffffffff0000000000000000fffffffffafafafaffffffffffffffff0000000000000000fffffffffcfcfcfcffffffffffffffff0000000000000000fff0fff0fff0fff0555555555555555500000000000000005550555055505550fffafffafffafffa0000000000000000fffafffafffafffa555555555555555500000000000000005555555550505050ffffeeeeffffeeee0000000000000000ffffeeeeffffeeee33333333333333330000000000000000333333332222222200000000000000000000000000000000fffffffffefefefe3333333333333333000000000000000033333333323232320000000000000000000000000000000000000000eeeeeeeeffffffffffffffff0000000000000000f0f0f0f0fefefefeffffffffffffffff0000000000000000fcfcfcfca8a8a8a800ff00ff00ff00ff000000000000000000ff00ff00fc00fc0e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e
|0,4=>0xffffffffffffffff0000000000000000fffafffafffafffaffffffffffffffff000000000000000000000000fcfcfcfcffffffffffffffff0000000000000000ffffffffff00ff00555555555555555500000000000000005500550055005500f5f5f5f5f5f5f5f50000000000000000f5f0f5f0f5f0f5f0555055505550555000000000000000005550555055505550fff0fff0fff0fff00000000000000000fff0fff0fff0fff0ffffffffffffffff00000000000000005550555055505550ffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa0f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0affffccccffffcccc0000000000000000ffffccccffffccccfffffcfcfffffcfc0000000000000000fffffcfcfffffcfcfffff0f0fffff0f00000000000000000fffff0f0fffff0f0ffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaafffffefefffffefe0000000000000000fffffefefffffefe555555555555555500000000000000005050505050505050
|0,5=>0xff55ff50ff55ff500000000000000000ff55ff50ff55ff50ffffff00ffffff000000000000000000ffffff00ffffff000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00ffff5454ffff54540000000000000000ffff5454ffff54540505040405050404000000000000000005050404050504040f0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0c0000eeee0000eeee00000000000000000000eeee0000eeeeffffffffffffffff0000000000000000fffffffffefefefeff55ff55ff55ff550000000000000000ff50ff50ff50ff50333333333333333300000000000000003333333330303030555555555555555500000000000000005454545454545454ffffffffffffffff0000000000000000ffffffff545454540000000000000000000000000000000000000000fefefefe050505050505050500000000000000000500050005000500ffffffffffffffff00000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000e0e0e0e
|0,6=>0xfefefefefefefefefffffffafffffffa0000000000000000fffffffafffffffaffffffffffffffff00000000000000000f0a0f0a0f0a0f0afffffff0fffffff00000000000000000fffffff0fffffff0cfcfcfcfcfcfcfcf0000000000000000cececececececece050505000505050000000000000000000505050005050500f0f0fefef0f0fefe0000000000000000f0f0fefef0f0fefe555555005555550000000000000000005555550055555500f5f5f5f0f5f5f5f00000000000000000f5f5f5f0f5f5f5f0ffffffaaffffffaa0000000000000000ffffffaaffffffaa0f0f0f0a0f0f0f0a00000000000000000f0f0f0a0f0f0f0a0f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e333333333333333300000000000000003030303030303030ffffffffffffffff00000000000000005454545454545454afafaeaeafafaeae0000000000000000afafaeaeafafaeae555550505555505000000000000000005555505055555050
|0,7=>0xf0f0f0f0f0f0f0f00000000000000000f000f000f000f000000ffaa0000ffaa00000000000000000000ffaa0000ffaa00ff00aa00ff00aa000000000000000000ff00aa00ff00aaffffffffffffffff0000000000000000ffaaffaaffaaffaa00000000000000000000000000000000ffaaffaaffaaffaa33332222333322220000000000000000333322223333222200000000000000000000000000000000fcfcfcfcfcfcfcfc0000fefe0000fefe00000000000000000000fefe0000fefe000000000000000000000000000000005454545454545454ffff5550ffff55500000000000000000ffff5550ffff555000ff00ff00ff00ff000000000000000000f000f000f000f0f0f0f0f0f0f0f0f00000000000000000fefefefefefefefedddddcdcdddddcdc0000000000000000dddddcdcdddddcdc0f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0a00000000000000000000000000000000eeeeeeeeeeeeeeee00000e0e00000e0e000000000000000000000e0e00000e0e
|0,8=>0xfffffafafffffafa0000000000000000fffffafafffffafa00ff00ff00ff00ff000000000000000000aa00aa00aa00aa333333333333333300000000000000002222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x1f0905040302070005040f070a10210504200f0e101f0504030f0e101e05030f1a0e10181d0504030212100504030f0e001c0504030f0e001b0503190f0e10180504030f010a1017050403121016050403020a101505040f0e1014060504030213100c04030f010a0504120e1011090c04030b0a090403080706050403020100
|1=>0x102b1f0d04030e2d2c061705040302102b0504032a0e10150504030f0e1029090c042803220e0504030f010e000504030f0e2700050403020f1026170504030b0f0005030f0e1025060c0504030b0f0a0504030f240e000504030f0a2310090403080e1006050403080f0706090504030b0e00090c0403020a10050422120e10
|2=>0xf0a100c05040302120e100504030b0f0a10090c0428030f0e100504030b120e10360504030f0e10090c04030b0e060504030f0a1035050403330f0e10050403320f0e100504030f0a101b090c0403020706090c0403220a0e05040f0e0010310c0504030f0a300c0504032a0f070504030f07002f05040f0e102e0605040f0e
|3=>0x4030f0e101b0605043a280f0e1017050403200f0e1009050403220a0e10170504030f1a0710050403190f1a0e100504030f0a10160504030f070e3906050403120e1016050403190f070e100d04030b0e102c060d04030b12070e00050403080f0e10060504030f0a0e101517050403020f00100504030f0a10370c05040302
|4=>0x20a10090c04030f0a0e100504030f0e10480504280f0e10460c050403120f070e0c05042803220f0e0d4404030f072d0609050403020710060d4342030b070e060d4104030e102c060504030f0e1035060504030f3f0e101d050403120f0e101705040322120e103e050428030f0e100504030f0e101c060504030f0e103b05
|5=>0xf071009050403220e00090504030e1016064d0504030f0e102b0d040302120700170504030b0f10060504030f0e104e050428030f0e1039170504030212100504030f240e10064d050403220f0e000d03020f0e101806090504030b0e10060504034b0f0e10050403020f070005040f0e103106050403020f10340609050403
|6=>0x120e100504030f0e00102f540504030f0e100605043a03120e100504030f0e1053060504030f0e10520504030f0e271006050403190f0e100d04030b120e00170504030f1016060504120f0e101f050403120f0e10370504030f0e10513e0504030f0a0e100504030f0e10500605044f030f0e100d04030f070e2d060504032a
|7=>0x4030b0f1a0e10050403020e102b0c05040f0e10210605040f070e1021060d4342030b0e06170504030f0e102b0504030f0e10550d03190f0e101806050403190b0f0e101d0504030f070a100d4504030f072d063d0504030f071006050403020f1a07100d4342030207060504030b020f0a100c0504032a0f0e100504030b02
|8=>0xb0f0e101806090c0403220e06580504030f0e10060d030f0e1018060504030f0e00390d043a03120e00050403120e104a050457030f0e100d3804030f0e2d061d05040f0e1021060504030b12070e100d0403020f072d060504030f0e2310060504490f0e104c090c0403020e10060d030f1a0e1018060504220f0e101f0605
|9=>0x10050403200f0e100d5c04030f0e10060d04030f0e105b060d04030f07105a0609050428030f0e100d4304030e1016060d0403020f1059060d4504030b0f0710060504030f0e102f060d4404030f0e102d060504030b0f070e10060d4104030f070e10060d04030f070e102c060d04490f0e104c064d050403200f0e100d03
|10=>0x10060504030f0e10630d0457030f0e10060504030f1a070e100d04030f0e1062060d440403020f071006050449280f0e100d04030f0e61100605040322120e100d045f030f0e10060d04030b0f070a10060d04030b12070e10060d04030f0e102d060d04470f0e105d060d04030f0e0030060504030f0e104a06050403020f0e
|11=>0x4030b0f0e1006050403220f0a0e100d04030f0e106a060d04032a020f0710064d050403120f0e100d0403690f0e10060d0403670f0e10060d443804030f0e10061d0504030f0e1006050449030f0e00100d0403120e104a060d04030f0e1065060d04030f0e1064060d040302120e00100d043a030f0e00063d090504030f0e
|12=>0x10060d4504030f0e102d06090504030f0a0e103d050403020f0e10060504032a120f0e100d4204030b020f0e060504030f0e104c0d04030f6b0e10060d434203020e1006050447030f0e000d04030b2a0f0e10060c0504030f070e06090504030f070e10060d040319020f0e10060d044903120e00100d0403020f1a10060d44
|13=>0xd4104030f0e10060d0403021207100605040302120e100d04030f0e10700617050403120f0e100d04036f0f0e10060d6e04030f0e100605043c03120f0e104d050403220f0e10060504030f0e1015063e0c0504030f0e10060d04030f070e40060d04030f0e106d060d6c04470f0e10060d414404030f0e1006050403020f07
|14=>0x4030f730e10060d4504030f1016060504030f0e1016060d4104030b0f0e10060d04030b0f0a10060d04030b120e10060d04030b0f070e00060d4304030b020e10060d0403020e10720605040f0e101f060504030f0e1037060d4504030b0f10060d0403020f71100609050403220e10060504030b0f0e1006050403020f0a10
|15=>0xd7604030f0e10060d414504030f0e10060d380403020f10060d04030f0e103b060d043a280f0e1006090c04030f0e10060504030f0e10750d0403740f0e100617050403220f0e10060d0403190f1a0e10060d040322120e000d04030f0a1016060504030f0e102b0504030f1a0e100d5e043a0f0e10060d0449030e1072060d
|16=>0xd0403190b0f0e10060d4204030b0f0e060d04030f0e1052060d0403190f0e100605043c030f0e100d420403020f070605043a030f0e10060d044f030f0e10060d04030f0e1077060d38450403020f10060d04034b0f0e100617050403020f10060d04280f0e1046063e0504030f0e10060d434203220e060d5e040f0e104606
|17=>0x60d0403020f0710060d04032a0f0e10064d0504030f0e10060d047b030f0e10060d4404030f0e10060d0403120f0e00100d430403220e10060d04030f0e107a060d04030f0e1040060d0447280f0e10060d04030f070a10060504030f0a0e100d0403790f0e10060d04030f0e10780605042803220f0e10090504030f0e0010
|18=>0xf0e107206170504030f0e10060d04030f0e1016060d444504030f0e10060d430403020e10060d04030f0e107d06050403120f0e100d5e0403220f0e1006050447030f0e10060d04030b0f0e10060d047c030f0e0010060d04030f0e105d060d430447030f0e10060d043c030f0e10060d444304030f0e10060d4342030f0e10
|19=>0x10060d440403020f0e10060d040322120e10060d0449470f0e10060d0403200f0e10060d04030f0e105a060d5e04490f0e10060d6c04030f0e1006050403220f0e10060d04030f0e1081060d0403120f070e10060d042803220f0e10060d04030f0e1080060d04030f0e107f060d04030f0e107e060d04030f070e00060d0403
|20=>0x46060d04030f0e1059060d450403020f1006050403020f0e10060d04032a120f0e10060d04030b020f0e10060d043a030f0e10060d0447030f0e00060d8204030f0e10060d420403020f0e10060d0403220f0a0e10060d0449030f0e001006090504030f0e10060d450403220f0e10060d6c4304030f0e10060d04030f1a070e
|21=>0xd04030f0e10060d0403020f0e10060d04030f0a0e10060d4504030f0e10060d0403220f0e10060504030f0e10060d4204030f0e10060d0428030f0e10060d0447030f0e10060d5e04030f0e10060d04030f0e001006050428030f0e100d04030f0e10
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x1e60186012600c600660006
|6,0=>0x1587151714a7143713c7135712e7127712071197112710b710470fd70f670ef70e870e170da70d370cc70c570be70b770b070a970a2709b7094708d7086707f70787071706a7063705c7055704e7047704070397032702b70247
|7,0=>0x34173398332732a8323731b8313830c730482fd72f672ee82e682df72d782d072c882c172b982b182a982a1829a7293728c7284827d7275826e7267725f8257824f8247823f8237822f82287220821882108208820171f981f271ea81e281da81d281cb71c381bc71b481ac81a4819c8194818c8185717d8175816e7166815f7
|7,1=>0x482847a8473746b8464745d7456744f744874408438843084288420841974118409840183f983f273ea83e283db73d383cc73c483bc83b483ac83a4839c8395738d8385837d8375836d8366735e8357734f83487
|8,0=>0x68f8686967e8675966d8664965c8653964c7644863c8635762c9624861b9612960a860285f995f185e985e095d885d085c885bf95b785af85a7859f8597858f8587857e9577756f8567855f8556954f754785407538852f9526951e8516850e850684fe84f774ef84e784df84d784cf84c784be94b684ad94a4949b9492948a8
|8,1=>0x890888888808877986f8867885f88587850884888408838882f9827881f8817880f8808780087f887ef97e787df87d787cf87c877c087b797ae97a7779f87987791778987818779877187698760975887508747973e9736872f7727871f8717870f8707870076f886f086e976e186d986d186c986c186b896b086a7969f86978
|9,0=>0xa867a7e8a768a6e8a668a5d9a549a4c8a448a3c8a339a2a9a219a198a109a0799fe99f599ed89e589dd89d589cd89c589bd89b589ac99a3999b8993898b8983897b8973896b8962995a8952894b7942993a89328929992189189910890798ff88f788ef88e788df88d788cf88c788bf88b788af88a788a078988
|10,0=>0xad48acc8ac48abc8ab57aad8aa58a9d8a958a8d8
|11,0=>0xadc7
|_,_=>0
def wAt:=mkWire dB 131 192 0xffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x70fc38410510438410e0643419000fc40190d0643c41030641441050f4341909070143d0d0643841220e440190f10414390d064381910024383d0510434190c020383d0f0743841050f43419050f4383d0e0643419050f4383d0d064142e02104383d0507438410d0643c190f1a428410e06434190907038410f06408430d064241c0e1040841050f4383d0e0643419
|1=>0xd064383d0f0643c690d0641c190e1043c1d380fc101d0e1043c19070f438410c020383d0510434190c0fc38190510434190e0f414391006434190c0ec381905104341905104383d0e06434190510434190e0f43c1902104383d0e0643419030641441050f434190210434190e0f43c190f0743841050f4341912344141e0e104143d0e0f43419051043819050f43419
|2=>0x70f43841410fc102d070f438413e0ec2441050f434190d0643901101283c191710414390f06434190f064403d050e43419030642441050f434193d10c2439050f434193c10c3419031243c190907c3841050f43419032243c410306488190f10434190e064143d0d06414390d0641c190e10434191a0f438011006408430e0f438190d06424430e104143d0d0640843
|3=>0xd064383d0f06438e50910c143d0d064403d10064140d0d06410660b06408410f0743841050f434190d0643d312810c0c190e0f434190e10440193d03c2439050f434190507838410d064143d0e0f438190d06414410e064143d0d06434194a0652443030f51c3f031040c190d0643c19100e414410d0640c19100f414410d065143d040e4143d0e0f438410d064103d
|4=>0xe0f43c190210c14390e0f434190f0645c0f050e434190c0ec3c190510434190d064c019070fc38410e0642441050f4341909078143d0d0643419032043c01100650443040b41c3d0e104283d0e10438190d06440190f104143d0d064400a0f0e4003f10064140d0d0644019100e4383d0f06488390f10414390d064bc1905028383d0d0640c190910c143d0d0641439
|5=>0x2104383d000fc1439100643419102a8283d0e0643419220a43c410e0642c190d06408410e0f4141d0e10438190d065143d040e414090e0f434190d0643c39070643841040f4383d0410438410e0f438190d06408190e0f414410d06434190e0f43c1905028383d0d0643c1903224403d0d06434192822c3c4103064140a0e0f434190f1a428410e0643419100644009
|6=>0xf10438190910c4019050f43419032243c410f06440190d0643c194910c0c3d0d0640d01101283c194110ce03d4510410391d03c30390510434190d0643c19070f4384104024383d10564243b050f434192810c0c3d030643419050f4383d0d0645c0f0f10414390d0643419070641c3d0e1043419000fc3c3910064740f0c0e434191d03c141d0e1043419040f41041
|7=>0xd0652443030f440190e0f434190d0643c011006410590210c383d4522c3c41040e5143f0e104103903064143d0d064103d0210c383d0f0e4101e0e1041039070f4384105028383d0d0651043450f410390d0641c3d0e104102d070f43841380fc101d0e1040c3d2810c0c19121043c190d06410660b064383d051043c41050f43419172243c41050e43419041988829
|8=>0xd0643419030f440190f0652443030f5983f5e104100d1a0fc38011006440190e0f43c19032243c41100642439050f43419120ec3c190d0640d01101283c190d0641c190e10458190210c383d0e10410090e0f40c3d030643419105a5143f040e43c410f0643419036050c43040f43819070f438410f0641c3d0e1051043450f4103903105783f040343c1e0e1044019
|9=>0xe0f43419120e43c190d064104102104383d2810c0c190d06438ad0f008401904104103d0e0f440190310434190206408410e0f440390510434190e104143d0d0642c1902104383d0f0640c3d10064383d0e00440190402408410e0f434190f10438195e22c3c4104034403902064383d0f064140d0d0643d650407838410f6857843040351441450f410390c0e41441
|10=>0xe1043c41050f434190d06408410e0f4383d0e0643419040b408410e0f440390e0f43c190d064383d0f0650c1e040f43841050e43c190d0642c1b02104383d5e2243c41040340c490f06434190f104140d0d064303f0510434190c0f414410d0644843100e43c19460651c3f031050c0d040f40c41450f410390e104383d0d0651043450f410390e064143d0d0641409
|11=>0x706c38410f10414390d064683d0e00440190f1043c191006438190210c383d000fc40190d06428410e0643419032243c41040340c3d420fc10410e6050c43040f410390210c383d0d06408430e0f4102d02104383d220e43c410e06440090e0f43c19100641c3d0e104103d02104383d0f0e5083f041045c0f050e434190c0ec14410d064103902104383d0e0f41c1b
|12=>0x2822c3c410306488290f10438190d0640c490f064383d041043841032243c410d0640c810f0044019000283c391006514410e0f410390f4c4a0430306414390e0f43419030651c3f031042441050f4341904104403d040f4100d470fc0c41044a52443030f51041450f4103945104383d040e4f043031243c19032243c41030641441050f43419031283c190d065c43d
|13=>0xe0f5080f041043c190d0643c41040340c410d06408410e0f40c0110065783f04034103d031040c490f0650c39040f4103d0410438410e0f438490f064140d0d0651c1b03105143d040e43c1910064403d040f5083b04104404a0f0640c190310438410e06438190d064081b0e0f4102e02104383d0f1040c190d0644019050f434190b06408410e0f4104102104383d
|14=>0xd06438490f06408410e0f51c3d031040c4110065083d0410410410e0f43c410e0640c3d10064143d0d0643c41040e50c0d040f41c190e10410090e0f4403d0f0640c3d031043c0110065143f040e40c3d04035783d040343c410d0640c021006440390f0643c4103064380210064a03f03064111e03104384110065083f0410414390d06408430e0f5143d040e4103d
|15=>0x383d0e06410390f1043419041040c1903104100d100640c190d0651c3f03104101e0e104383d040e4383d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x5200000050000000
|6,0=>0x129000011cc000000044310100000f883a4000000000000000dcc00000003250b90000000029500002450000000088800007901a400001730000000050c000041000000000c402880730000000
|7,0=>0x4f913a44d913244b912a449cd23447d11b445d115244510d442510544050fd43e50f543c8cee43a90e643890df336d0d7434d0cf432d0c743148c142f8cba42d90b242b90aa42990a2427909b325d0943244c8d4225085420507d41e507541c8c6e41a9066418905e4169056414904e4
|7,1=>0x734dca37191c246f91ba46d91b246b91aa46991a2468099c4661195300019146351894618d8245f917a45d917335bd16b45a4966358915e456cd574550d51300014d40001494518d424
|8,0=>0xa30e8a2a1ce843a04e7e39ece7839d4e7239bce6c39a4e66398ce603974e5a395ce543944e4e392ce483914e4238fce3c38e4e3638cce3038b4e2a389ce243884e1e386ce183854e12383ce0c3824e06380ce0037f4dfa37dcdf437c4dee37acde83794de2377cddc3764dd6374cdd03
|8,1=>0xd30f493d18f433d00f3d3ce8f373cd0f313cb8f2b3ca0f253c88f1f3c70f193c58f133c40f0d3c28f073c10f013bf8efb3be0ef53bc8eef3bb0ee93b98ee33b80edd3b68ed73b50ed13b38ecb3b20ec53b08ebf3af0eb93ad8eb33ac0ead3aa8ea73a90ea13a78e9b3a60e953a48e8f3
|9,0=>0x3c72f14bc32f04bbf2ef4bbb2ee4bb72ed4bb32ec4baf2eb4bab2ea4ba72e94ba32e84b9f2e74b9b2e64b972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2df4b7b2de4b772dd4b732dc4b6f2db4b6b2da4b672d94b632d84b5f2d74b5b2d64b572d54b532d44b4f2
|10,0=>0xf487d11f407cf1f387cd1f307cb1f287c91
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x1008800000004000000000008890000000022040000000064f40000000113d0000000019bc0000000040600000000101000000000402000000000c080000000026000000000081000000000184000000000600000000001200000000004200000000010000000000021000000000080000000000190000000000240000000000880000000002000000000004000000000008000000000018000000000050000000000100000000000200000000000400000000000
|1=>0x20504f80000080413100000141c4a800000500126000001040408000004043000000008194b80000020612e00000080041c00000104100000000400c18000001001040000003144b00000008723d00000021c4f4000000862340000002080100000008021400000011c4380000004553f0000001144b0000000240000000000841000000001c13e0000000644f80000001402400000004009000000010004000000011000000000041840000000104f400000004024
|2=>0x4003cc380001000d13d0000400344b40001000713f00004001c4f40001000593d000040014cfc0001000533d0000400144fc0001000513d00004001109000010000400000040000088000100000040000400000040000980413d0000260000a000009044008000020b144fc000082c00240000101164b80000401113e000010014cf40000400513d0000100005b80000201113e0000080044f80000180800c0000044344fc000010ca02d000004134cfc00000a0c12c
|3=>0x4413c4b40001104d33d0000441344f40001104513f0000441144f40001100d33f000044034cf40001100d13f00004283c4f400010a0a02400004141c4fc0001050513f000041410c100001028513d00004081c4fc0001020712d000040814cfc0001020533d0000408144fc0001020513d000040400014000100c512d00004021ccfc0001008732d00004021c4f40001008712d0000402144f4000100822240000402084b8000100802040000401144f40001001067e
|4=>0x2180544fc0008400112c0002000068000005404597f000150016cf40005400593d0001000051000003010403b0000c00100c40001980000c000060f144fc000182c513d000060b144b40001800513d0000600000900001600533f000058014cf40001600513f0000580144f40001504513d000050014cb40001400517f0000500144f40001400512d0000500005b80001200513d00004483c4fc0001120f13d00004443c4fc000110c513d00004423c4b40001108d13d
|5=>0x80002088d00200000401400800000001400c1048513f002000004000008000001200018400949f40061001047f0018000c08900041019513f0010400544fc0041001507f001004040080004002140000010000104340021100547f00084141860c0021020553f0008400155fc0021000067f0008040001f4002004065a00005501364b40015404593d0004580364f40011404512d0004500165fc0011300d93f000440016d380011000513d0004180365fc0009000557f
|6=>0x440400144f41100008713d0400400144f41000000713d04000001c0f41000000513d0400000100d00901000713d024040014cf4090000000040200400144f4080000040240200000000100400000100400c0400144f40300000420000c0000000500300000000400c0000000040201980513d0080660000300201080400400804023ccb40201008733d00804021ccd40201008732d008040218880020100822240080400144f40200980002800800021ccf402000086214
|7=>0x2400002000d08901000713d22004001c4f48800000203420004001c4f48001000533d2000400144f48000000533d1800541165fc4905400513d100550016dfc40110005b2d100440014c244005400513d1000541164f44001400597f1000500164f44001400513d10004c1164f44001000513d0802500164fc2009000593f0802400068102000500d13f0800000040001901000533d0640400144f41900008202d06400001c0f41200008723d0440500144f41101000713d
|8=>0x8244400144f60001400533d8000500144f60001000513d4000c04140fc9000008513d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x2000140000
|6,0=>0x28000c000000c14000102000000000022000002c0a000005400090000004000280c0003000000c00080000007010380000
|7,0=>0x1ce033003ca2ab7992c4e015d874062a4f00c0052488ac486b190887e074b0ec0612263905e250e00c18a3001140650340d130b3108a83c1b021003216691086a3e4c8f4249d0f0608c334b820720a0d11c3e140185c5ccd150a1743a148349454438d82637278e0462d222f4c453590f1620a1318c165f
|8,0=>0x61a4160cb7121998a16f3d4b45b7fa18ea885cb9890a268401128b5c3a0ca73611f8e02c26925b4d56e1719ec664b1580da80ad58266561a4e2d140a0cca7461a2548e95a2dcbaec24338ced4572bd0a304f985c6f7652d8aa4e54a4d7c6f811d9d46581081789c53225247f7a2a8865e4a96df88a7c9e9aac432158926a529f0825b7cbe140db18afcb8d332359b28b
|9,0=>0x8e77195f65c4231d36f173380dca856bea0a947e9e5347e7ca251259462011e7b46bc904dd3a16dfad8709e208f0643b606f653bf9ca673bbaddefd3eb5dbe5e449c8da5b
|10,0=>0xb66c7c960aedf46bba067b
|11,0=>0x56
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 46 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_159 10 roots_159 ops++addP pm 1 dom_31 7 roots_31 ops++addP pm 2 dom_190 9 roots_190 ops++addP pm 3 dom_47 8 roots_47 ops++addP pm 4 dom_175 9 roots_175 ops++addP pm 5 dom_187 9 roots_187 ops++addP pm 6 dzo_23_8 5 roots_23 ops++addP pm 7 dom_153 5 roots_153 ops++addP pm 8 dom_181 8 roots_181 ops++addP pm 9 dom_186 7 roots_186 ops++addP pm 10 dom_155 7 roots_155 ops++addP pm 11 dzo_55_8 6 roots_55 ops++addP pm 12 dom_183 9 roots_183 ops++addP pm 13 dom_185 6 roots_185 ops++addP pm 14 dom_189 9 roots_189 ops++addP pm 15 dom_59 6 roots_59 ops++addP pm 16 dom_158 7 roots_158 ops++addP pm 17 dom_154 5 roots_154 ops++addP pm 18 dom_62 6 roots_62 ops++addP pm 19 dom_188 6 roots_188 ops++addP pm 20 dom_157 8 roots_157 ops++addP pm 21 dom_61 7 roots_61 ops++addP pm 22 dom_21 4 roots_21 ops++addP pm 23 dom_57 4 roots_57 ops++addP pm 24 dom_58 5 roots_58 ops++addP pm 25 dom_55 6 roots_55 ops++addP pm 26 dzo_183_8 7 roots_183 ops++addP pm 27 dom_60 4 roots_60 ops++addP pm 28 dom_63 9 roots_63 ops++addP pm 29 dzo_181_8 6 roots_181 ops++addP pm 30 dom_178 5 roots_178 ops++addP pm 31 dom_23 5 roots_23 ops++addP pm 32 dom_179 6 roots_179 ops++addP pm 33 dom_27 4 roots_27 ops++addP pm 34 dom_30 4 roots_30 ops++addP pm 35 dom_156 5 roots_156 ops++addP pm 36 dom_170 5 roots_170 ops++addP pm 37 dom_184 4 roots_184 ops++addP pm 38 dom_147 5 roots_147 ops++addP pm 39 dom_171 6 roots_171 ops++addP pm 40 dom_174 6 roots_174 ops++addP pm 41 dom_151 8 roots_151 ops++addP pm 42 dom_182 6 roots_182 ops++addP pm 43 dom_173 6 roots_173 ops++addP pm 44 dzo_53_8 5 roots_53 ops++addP pm 45 dom_167 6 roots_167 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_191 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_23_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_55_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_183_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_181_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_53_8_21 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_167 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_159 10 s (0,roots_159.map (·&&&dom_159)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_191 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_159 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_191==dom_191)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_191 gM v ys):RunD true dom_191 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_191 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 45 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 106 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 106 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 61 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_191 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤11) (h:RunD true dom_191 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_191 roots_191 goal_191 12:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_191
theorem lowS_191:Lower true dom_191 roots_191 goal_191 12:=S_191.noCircuit
namespace S_223
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,65),(1,129),(2,10),(2,18),(2,130),(3,7),(3,11),(3,19),(3,67),(3,131),(4,5),(4,20),(4,68),(4,132),(6,7),(6,14),(6,22),(6,70),(6,134),(8,10),(8,72),(8,136),(9,11),(9,13),(9,25),(9,73),(9,137),(12,13),(12,14),(12,28),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(64,192),(66,67),(66,70),(66,74),(66,82),(66,194),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000000000ffff000000000000ffff000000000000ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0cccccccc00000000cccccccc00000000cccccccc00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_222 10 roots_222 ops++addP pm 1 dom_159 10 roots_159 ops++addP pm 2 dom_221 10 roots_221 ops++addP pm 3 dom_219 10 roots_219 ops++addP pm 4 dom_215 10 roots_215 ops++addP pm 5 dom_207 10 roots_207 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_207 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_222 10 s (0,roots_222.map (·&&&dom_222)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_222 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_101_2:=0xcc000000cc000000cc000000cc
def gzo_101_2:=0xcc000000c8000000cc00000080
def gsh_101_2:=0x33000000320000003300000020
theorem lowS_zo_101_2_69:Lower true dzo_101_2 roots_101 gzo_101_2 5:=lower_iso_b (d1:=dom_101) (r1:=roots_101) (T1:=gsh_101_2) [(dom_101,2)] (by decide +kernel) (lower_slice_b (T:=gsh_101_2) [(0x33000000000000003300000000,0,32)] (by decide +kernel) lowS_69)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500040000000000050004000000000004000400000000
def gsh_210_32:=0x50005000000000005000400000000000500040000000000040004
theorem lowS_zo_210_32_208:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (lower_slice_b (T:=gsh_210_32) [(0x40004000000000004000400000000000400040000000000040004,0,2)] (by decide +kernel) lowS_208)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500540000000000550054000000000054005400000000
def gsh_214_32:=0x550055000000000055005400000000005500540000000000540054
theorem lowS_zo_214_32_208:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x440044000000000044004400000000004400440000000000440044,0,2),(0x500050000000000050005000000000005000500000000000500050,0,4)] (by decide +kernel) lowS_208)
def dzo_229_2:=0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc
def gzo_229_2:=0xcc000000cc000000cc000000cc000000cc000000c8000000cc00000080
def gsh_229_2:=0x3300000033000000330000003300000033000000320000003300000020
theorem lowS_zo_229_2_69:Lower true dzo_229_2 roots_229 gzo_229_2 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_2) [(dom_229,2)] (by decide +kernel) (lower_slice_b (T:=gsh_229_2) [(0x3300000000000000330000000000000033000000000000003300000000,0,32),(0x3300000033000000330000003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_69)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e
theorem lowS_zo_211_32_208:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2)] (by decide +kernel) lowS_208)
def dzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def gzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00c800cc00cc00cc0080
def gsh_245_2:=0x33003300330033003300330033003300330033003300320033003300330020
theorem lowS_zo_245_2_69:Lower true dzo_245_2 roots_245 gzo_245_2 7:=lower_iso_b (d1:=dom_245) (r1:=roots_245) (T1:=gsh_245_2) [(dom_245,2)] (by decide +kernel) (lower_slice_b (T:=gsh_245_2) [(0x33000000330000003300000033000000330000003300000033000000330000,0,16),(0x33003300000000003300330000000000330033000000000033003300000000,0,32),(0x33003300330033003300330033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_69)
def dzo_213_32:=0x33003300000000003300330000000000330033000000000033003300000000
def gzo_213_32:=0x33003300000000003300320000000000330032000000000032003200000000
def gsh_213_32:=0x330033000000000033003200000000003300320000000000320032
theorem lowS_zo_213_32_208:Lower true dzo_213_32 roots_213 gzo_213_32 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_32) [(dom_213,32)] (by decide +kernel) (lower_slice_b (T:=gsh_213_32) [(0x220022000000000022002200000000002200220000000000220022,0,1),(0x300030000000000030003000000000003000300000000000300030,0,4)] (by decide +kernel) lowS_208)
def dzo_197_2:=0xcc00000000000000cc00000000000000cc00000000000000cc
def gzo_197_2:=0xcc00000000000000cc00000000000000c80000000000000080
def gsh_197_2:=0x33000000000000003300000000000000320000000000000020
theorem lowS_zo_197_2_69:Lower true dzo_197_2 roots_197 gzo_197_2 5:=lower_iso_b (d1:=dom_197) (r1:=roots_197) (T1:=gsh_197_2) [(dom_197,2)] (by decide +kernel) (lower_slice_b (T:=gsh_197_2) [(0x33000000000000003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_69)
def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc
def gzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00c80000000000cc0080
def gsh_213_2:=0x330033000000000033003300000000003300320000000000330020
theorem lowS_zo_213_2_69:Lower true dzo_213_2 roots_213 gzo_213_2 6:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (lower_slice_b (T:=gsh_213_2) [(0x330000000000000033000000000000003300000000000000330000,0,16),(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_69)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fe00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00fe
theorem lowS_zo_215_32_208:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4)] (by decide +kernel) lowS_208)
namespace S_247
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,7),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(4,132),(6,7),(6,22),(6,38),(6,70),(6,134),(16,17),(16,18),(16,20),(16,80),(16,144),(32,33),(32,34),(32,36),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(66,67),(66,70),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,192),(160,161),(160,162),(160,164),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|4=>4
|5=>69
|6=>235
|7=>289
|8=>124
|9=>27
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x717862e0a32c35f227d7
|5,0=>0x88f3c6dfbe694cd66ac35b68857dec534ff51bba517bb4b6f2448324213141fa64193f3d3083a1bf39bdf393ac387cc3836832727322ee2f96d2f5cb2e0a32d7452cfe22c35f2ac5427e6226f312509623d2d2335720d83207202047e1ff711f32c1e52e1d18e1c5611a94e177fe1637e134bd1271f1226811bc71154f11040100e40ff930ea060d5720c73a0b2ab09926090a608b970879607e2d05ea205435052a304efa034610208a00a44
|6,0=>0x19e21190b41841e17e2317ca51759f1756f16a861627f15d2d153bf14db3149b3147cf1479514719144b513de213886132a312dce1271f1222411db411add116e5116c11138f10b0d10a5c101260facc0f9b30f8180f5820ee170ea340e8680e75d0dc5a0dc020daa30d7540d37b0d2f10ccbf0c5db0c22d0c1e00bb4c0bb320babc0b9c30b8dc0b4f70b3b40b0db0af980a5f809d7109a650947f0915e08e4e08dd408cbd08af90841c08324080d807e6e07d7d07c8907b9a07acc0770d07706075d107518074ec0714306e8106ae0068320618f0610205f4b05ec105db805bef057b205647055430522804f1604d6704c8f048ee046be04666045d1044a4041a403ef003cbd03b0d03662032da02f0b02da8029ef028ec026fa026f302605025aa01627015da0159c0101100dd2009d20096d0095c007cf00759007540043b
|6,1=>0xc720eb7ad4ac996ac63ea4e7ca464998c087abe17a98e720c86e92268609655016446463ad9607905fd4e5f8d35eae55dcac5d8565be7f5938d5774a51c3a4f1f745856448c743ee1410d03f11d3e0023d7f83cfe53bcef3ba233aa4f3a06b394353929938c18389143810a37d9737b7b374683687a35f3835d243534e34a77331093283e3247c322ee321e7306a12f1742f16e2ec242e4ab2de402d0b32cbc62c5172bb7f2baf62b2962b1042aaa92a7a92a41c29e6529d56288172816126ff826a532508024d6724b792433c23c5023a6f23754236c8221802155121524212b4209a12056c201781fa8a1f8d71f0411eb8c1e7681d55c1d18d1cc071c7761baea1b7a61b2171ae1b1a7c8
|7,0=>0x151a714feb14e4614dbd14bd91490b145eb145bd144a1142e2142831420013f9513b9a12f4a12cc71294d128d712521122a611f4c11ee211b1f11986118fe10f1910e5e10d5310346100eb0ffe10fd840fd4b0fb270fac70f7fe0f3c00f2360e45f0e22d0e0f20e0b60d8d00d8230d66b0d3b80c5c40c4920bedf0be2e0bd170bb5f0b8250b79f0b5e10b4fc0b4390a9610a2990a2940a19509faf09ce409a0c0933008e3708cc208bb008b06086ef08540082c108256081be080dd0808907f0807aa1079c2079110746b06f5f06f3706d6106ac506580063930635a05f2305e4a05af3058720540104b3404a1a048ee047f10474f0472a0453f042c803ef203eb203e7403b580335a02ec10282e0269b022f2020f80200501ff101eaa01e7501c4401867013ca013390116f00ece00e8f00dd9009a000510001e10012200110
|7,1=>0x5d8565c9715ad36597f358af151f8650e3f4e7f94e22b4ce5b4a2134846447ecb4652d4600b45d30454174369e435813ffbd3fc6e3fa333f76e3c84d3c4583a9913a89d3a4e83a2a138cbc386bd37d85367573576b34e1334cba34c4234c37332d232db332c0e3230b312fe301f72ef842e8f82e4812dd602cc4f2c91d2bccb2ba142ac872a8382a5d929d1e29708296ab2904e27cf127a03273cd2724026551260a025f9025edf25ad9258e02576f254dd24d7223d5123be123a9a2357f22fdf22ae3223802229d2207b22078216fa2140020faa20f1320dc8206c01fe8f1fb441f9871f7f51ee7a1e7f71e67e1e2cd1e21d1dd311cd2b1c0e41bf071bbaf1b9db1b8d91b13a1aacc1aaa51aa961a276191dc18b6618700184411818117ad117a95174ee1720416ca016c0f16af6163e6162071620415fff15f731590a153a7
|7,2=>0xebb72d0ba8cea65c8f39b7ad4af21eaf017a7d67a78b5a0f22a0a229adbd99ea38ae3b898c087b2982cb27ee2c7849b758c972e7572b0d710a866fa066c3c65fb7655d36446463290619b160f6c605025f4d2
|8,0=>0xaf017aa394a969d9e3dd897f17a2e979d6175686747b16ce8d69ce5658486442d5d62b5c0b358a3b5856c5777056ad55409c4d2034ad3549e5345ff8434ea3efbd3eae83d6e53cfab3c5d93a928392d136a7d369883586e3556934f743439f334ee32707300952eb8d2e3ac2e0be2dcd82da732bf8c29ead29c5027ce527bbc266a824beb24a92228c92126120f7620bee1fdc11e8ad1dc461d57a1d4831cfff1cec11cdb11b7121aeeb1acc41aac91aa9f193e01905f18ea31883617de516c1f1639b1586b157a71579d152de1377e1364211e1b0fe6e0facc0e6510d7f10d6000d58f0d2b90c50c0bca00b5620b1320ab4c0a8be0a5370a35509e2509c2d0909d08bc5088c90881d086330807306a800680b067c705fa005e2205cc30561505400048e103818036b402d140299a0212100f35005bb
|9,0=>0xcc4289e94d6a6305324d468693acc83907a366192f2362e6852810025b6e22f7a1d2b71b92919f3d16cb110dd60f7890ebdc0ade607aeb05a2104dda02daf02ba70261e
|10,0=>0xdc8bcb49746f3f60fdfc
|11,0=>0x9dbb2
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00faff00ff00ff00ff00ff00aa00ff00aa00ff00ff00ff00ff00f000a000f000a0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00ff00f000ff00f000ff00ff00ff00ff00aa00a000aa00a0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff0000fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00feff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aafe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe000000fe00fe00fe0000ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f0ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
|0,1=>0xff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f0ff00ff00ff00ff00ff00f000ff00f000ff00ff00ff00ff00ff00f000ff00f0ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000aa00a000aa00a000000000000000000000000000000000ff00ff00ff00ff00ff00f000ff00f0ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f0ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00fa00fa00fa00fa00fa00fa00fa00faff00ff00ff00ff00ff00aa00ff00aa00ff00ff00ff00ff00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee550055005500550050005000500050005500550055005500500050005000500000ff000000ff000000ff000000ff000000ff000000ff0000000000000000
|0,2=>0xff00ff00ff00ff00ff00aa00ff00aa00f000f000f000f000f000a000f000a0ff00ff00ff00ff00ff00f000ff00f000aa00aa00aa00aa00aa00a000aa00a0ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00f000a000f000a0ff00ff00ff00ff00ff00fc00ff00fc00ee00ee00ee00ee00ee00ec00ee00ecff00ff00ff00ff00fa00fa00fa00fa00ff00ff00ff00ff00fa00fa00fa00faff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00faff00ff00ff00ff00ff00ff00ff00aa00ff00ff00f000f000ff00ff00f000a0aa00aa00aa00aa00ff00fa00ff00fa00aa00aa00aa00aa00ff00fa00ff00fa0000000000000000ff00f000ff00f0000000000000000000ff00f000ff00f00000000000000000ff00ff00ff00ff000000000000000000aa00aa00aa00aa00000000000000000000000000000000ff00ff00ff00ff00ff000000ff00000f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000aff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc0f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a
|0,3=>0xff00ff00ff00ff000f000a000f000aff00ff00ff00ff000000000000000000ff00fa00ff00fa0000000000000000000000000000000000000000000000000f000f000f000f000f000a000f000aff00ff00ff00ff00ff00ff00ff00ff005500550055005500500050005000500000000000000000ff00ff00ff00ff000000000000000000f000f000f000f0f000f000f000f000f000f000f000f000ff00ff00ff00ff00ff00f000ff00f050005000500050005000500050005000550055005500550055005000550050ff00aa00ff00aa00ff00aa00ff00aa00f000a000f000a000f000a000f000a00f000a000f000a000f000a000f000a000f000a000f000a000f000a000f000aff00ff00ff00ff00ff00ff00ff00ff00ff00f000ff00f000ff00f000ff00f0aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa0000000000000000ff00ff00ff00ff000000000000000000ff00fa00ff00fa0000ff000000ff000000ff000000ff000000ff000000ff000000f0000000f0
|0,4=>0xff000f00ff000f00ff000a00ff000a000000000000000000000000000000005500500055005000550050005500505500500055005000550050005500500055005000550050005500500055005000000000000000000000000000000000ff00aa00ff00aa00ff00aa00ff00aa00000000000000000000000000000000ff00ff00ff00ff00ff00aa00ff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fa00fa00fa00fa0000000000000000ff00ff00ff00ff000000000000000000ff00f000ff00f00000000000000000ff00fa00ff00fa000000000000000000ff00fa00ff00fa00000000000000000000000000000000ff00fa00ff00fa00ff00fa00ff00fa0000000000000000ff00ff00ff00ff000000000000000000ff00aa00ff00aaff000f00ff000f00ff000f00ff000f00ff000a00ff000a00ff000a00ff000a0000ff000000ff000000ff000000ff000000ff000000ff000000aa000000aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa3300330033003300330033003300330033003300330000003300330033000055005500550055005500550055005500500050005000500050005000500050ff00ff00ff00ff005500550055005500ff00ff00ff00ff0050005000500050
|0,5=>0xff00ff00ff00ff00ff00fa00ff00fa00ff00ff00ff00ff00ff00fa00ff00faf000f000f000f000ff00ff00ff00ff00f000f000f000f000fa00fa00fa00faff00ff00ff00ff00ff00ff00ff00ff00ff000f00ff000f00ff000a00ff000aff00f000ff00f000ff00f000ff00f000aa00a000aa00a000aa00a000aa00a0ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00f000ff00f055005500550055005500550055005500550055005500550055005000550050ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000aa000000aa00000000000000000000000000000000ff00f000ff00f000ff00f000ff00f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000ff00f00f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000aff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00f000a0ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00aa00ff00aaf000f000f000f000ff00fa00ff00fa00f000f000f000f000ff00fa00ff00fa000000000000000000000000000000000000000000000000ff00f000ff00f00000000000000000ff00aa00ff00aa000000000000000000ff00aa00ff00aa55005500550055005500550055005500550055005500550050005000500050
|0,6=>0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000f000a000f000aff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000a000a000a000a0f000f000f000f000f000f000f000f000f000f000f000f0000000000000000aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00fa00fa00fa00fafa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00fa00fa00fa0f000f000f000f000f000f000f000f000f000a000f000a000f000a000f000aaa00ff00aa00ff00aa00ff00aa00ff00aa00fa00aa00fa00aa00fa00aa00fa000000000000000000000000000000000f000a000f000a000f000a000f000aff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00f000ff00f0ff00ee00ff00ee00ff00ee00ff00ee00fc00ec00fc00ec00fc00ec00fc00ecff005500ff005500ff005500ff005500ff005500ff005500ff005000ff0050f000f000f000f000f000f000f000f000ff00fa00ff00fa00ff00fa00ff00faff005500ff005500ff005000ff005000ff005500ff005500ff005000ff005000000000000000000f000a000f000a0000000000000000000f000a000f000aff00ff00ff00ff00ff00ff00ff00ff00ff00fa00ff00fa00ff00fa00ff00faff00ff00ff00ff00ff00ff00ff00ff00550050005500500055005000550050
|0,7=>0x33003300330033003300330033003300330033003300330033003300330000ff00ff00ff00ff00ff00ff00ff00ff000f000a000f000a000f000a000f000a0000ff000000ff000000ff000000ff000000aa000000aa000000aa000000aaff005500ff005500ff005500ff005500ff005000ff005000ff005000ff0050ff000000ff000000ff000f00ff000f00ff000000ff000000ff000a00ff000a00000000000000000f000f000f000f0000000000000000000a000a000a000a5500550055005500550000005500000055005500550055005500000055000000000000fe00fe0000000000fe00fe0000000000fe00fe0000000000fe00feff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fe0f000f000f000f000f000a000f000a000f000f000f000f000f000a000f000aff00ff00ff00ff000f000a000f000a00ff00ff00ff00ff000f000a000f000aff00aa00ff00aa00ff00ff00ff00ff00ff00aa00ff00aa00ff00fa00ff00faff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00fa00ff00faff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00aa00ff00aa0000ff000000ff000000ff000000ff000000f0000000f0000000f0000000f055005500550055005500500055005000550055005500550055005000550050
|0,8=>0xff000000ff000000ff000000ff000000ff000000ff000000fa000000fa00000f0000000f00000000000000000055005f0055005f0000000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000fe00fe0000000000fe00fe0000ff000000ff000000ff000000ff000000fa000000fa000000fa000000faff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00f033003300330033003300330033003300330033003300300033003300330030ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00ff00fa00ff00fa00000000000000000000550000005500000000000000000000005000000050ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff000f000a000f000a0000000000000000ff00ff00ff00ff000000000000000000fa00fa00fa00faaa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00ff00fa00ff00fa00000f0000000f0000000f0000000f0000000a0000000a0000000a0000000aff00aa00ff00aa000000000000000000ff00aa00ff00aa000f000a000f000a0f000f000f000f0000000000000000000f000f000f000f000f000a000f000a0000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000
|0,9=>0x5000500050005000500000005000000050005000500050005000000050000000000000000000000000000000000000000000000000000ff00aa00ff00aaaf00af00af00af00af00af00af00af00af00af00af00af00aa00aa00aa00aa00000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aa00000000000000000000000000000000ff00ff00ff00ff00f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fa00ff00fa000000000000000000000000000000000000000000000000ff00fa00ff00fa
|_,_=>0
def sP:Nat→Nat
|0=>0x1b0407220b2d0d1a19050b2c0a0013032b010d2a191822211b1a071e170112001929240b0d1b28050f0d00040727060b0d2503020b0004072603010d251903240b0d230703222120041918151f0d1a191e030112000703010d1d00191c050f0d1b1918171612000715060f140d130112111007060f0e0d0703010d0c03020100
|1=>0x322161f0d072705010d25073622081a00071815160d2a1924050b1211131f010d350a072934010d1b130f330d1a00191824080a00090321160100130f010d1b10071e170f0d2a131f0d0a1d0419310521010a0903080100130b121a30001318160d1b2a07030b0d0c0407050f2f0d2a19032221230407060b122e0013291e21
|2=>0xa3d000703010d0c00071834081a00130b2d1200041318123c00040718173b1200193a050f0d1b09031f0112000703062120001905081a200019050b123900073405011211071815140d1a09291f0d1b0407050f0e0d041321011b0a101329140d1b0407060f0e0d130b2d0d1a0019240b0d1b370703010d0c09181f0d1b1a19
|3=>0x22060b0d0a3c0734050f1f0d1a0905210a230004071845210a0004071e0501120a2a131f0b0d0a440407430521010a0009050b1b1a42000722060b0d0a4019050b0d0a3f00071722140b0d0a1315030f1f0d04130321012500190521010a3e0703342b010d13031f01122a0726060f0d2507060f0d1d0007060f0e0d00190521
|4=>0x1004191e05010d1b0a074b050b121a000718034a0d0004071806211b1a0019030521160100071822010d1b1a071e060f0d1a000717050801000703340b0d23040736220f0d1a00070322140b120413051f01120a2a0749050b121a0007051f0d0a4110130508010a2a00074805010d1a000747221f0d0a040746050f010d0007
|5=>0x5080b321a00131f0b0d350a04090321010a000729340b0d1b0419050b121a4e0007170b12440004071e03160d0004131f0d0a4d2a041315170b0d0a2a1903220b0d321a0736052b0d1a000734052b010d0a194b050f0b0d00071817081a000407184c1f0d1b04090b0d1a37000718341f0d1a0a0715050f140d04130f0b0d1b
|6=>0x1a1303140b0d1a000718540f0d0004075306010d0a0019184b0b0d0a000736051211000407030621230004071815140d0a040717050b0d232a1303161f0d0004070324210b1b041905161f010d1b0752030b12000419051f0b12321a070306210b32001918510b0d1a000718220d0a5004074f05210a0004070322010b0d3219
|7=>0xf140d00191824210a000727050b0d2504073405210b1b1a09031f0b0d1a001915050b0d56000718051f121a2a19050b0d0a2e00071805081a2a00074c0521230004072922010d1b0407150621010a00191815210a0004092918210a00040706050f140d1b55050b0d0a000413030b3b120004193a050b120a000715051f010d
|8=>0x5160b0d1b0007050b125a0004070334010b1200191822010d1b0a130b0d0a1110040705330b0d1b1a071e4c0b0d1b041918051f0d1b1a091c180b0d0a00070521010a5900073605210a3e0413180b0d0a3e04133618210a2a00071806140d1b0a075803211b000419570521010a001922050f010d1b07182201120a2a071705
|9=>0x1b041318010d0a2500194b05210b0a001321010a30000413210b1b0a1004195105210b1a0013030b0d562a00075f060b0d0a2a0705210a3d00040729220b0d1a2a073622211a0a0007060b2d0d0a0013050f010d25000703065e0b0d000718062b0d1a00075d05210a000407030b0d0c04075b030b0d1b040718060d0a3c0009
|10=>0xf0d1b000419220521011b0a0734050b12110407360321011a000758032b0d00040903210b1a0007061f0d0a4d2a071c0b0d0a30001329010d0a2a00071834080a00040761050b0d1b2a07051f0d0a602a1936030f010d00192205010d0a1113051f0b121a2a07050814011a0019050f0d1a2000071803010d32001929051f0d
|11=>0x703220f010d2a193a030b0d0a0019180301120013180d0a5000041303010b0d32000717220b1232040763060b1200040722050112110407050b0d1a231009031f0b1200041903051f0112001318010d1b1a0007060b0d1a62000703060b3b12000722052b010d1a1303140b12000419291805211a0013031f010d0a2a0918
|12=>0x22080b2a041929220b0d1b040767050b121a000761051f0d1b041922052b010d0a0706660b0a00131e36210a000407181701120013050f1f0d320409180d0a1100040722060b0d0a50131801120a2a00074c22210b1b0409051f0d0a41000765050b120004191705160b12000764051f0d1b0407340b0d1b37040703064a0b0d
|13=>0x1b10071851160d000407291822211b040736051f0d320a134b030b0d1a000726170f0d000407030b0d0c000407051f0d0a1d040718220f0d3204132917010d0a000703010d5c0013290b0d250004193105010b0d0a07051f0d690a2a075f05010d0a2a07030b0d2e000407050f0e0d0407220b0d1b6804073a030b1200040703
|14=>0x7050b0e0d0a040717220b122a0918010a420007050f0e0d00040717220f0b0d2a134b030b120004071806081a000722061f01120a0705211a232a13050112110004092918010d0a0013052b010d1a000718171f0d0a2a075305010d1a0007220b0d0a6a2a0718060d0a5000071e4c0f0d00040717050f1f0d2a07050f010d
|15=>0x50b0d0a3e041918051f121a000751060f010d0005020b0a00040718513b0d0a04073117050b120407060f380d000736031f0d1a000918080a000407360521320a00072603010d1a0019610521010a000731050b0d0a04073605211b0a2a1953050b0d1a000718060f0d1b2a0726050f0d2504194f050b0d0a000736051f121a
|16=>0xd0a6e000413290b0d0a2a0004071815010d0a00040705080b1a2a000705010b120a0010071806160d1a0a0007050b120a30000407050b0d1b1a6d070305210b1b2a0413050b121a2a0013056c0b0d0a000407052116011b00040703220b0d1a2a1922050b0d0a1104071e030b0d1b0407056b0b0d0a0004072206080b0a2a07
|17=>0x1a0a000705160b121a2a001918050f0d1b0004074b050b0d320a0007050b0d1b1a71000905010b120a000718030b0d70000413291f0d0a0004071e030b0d0a2a040757050b0d1b0a040706052114010a0007050b0d0a6f000407220b0d1b37040717220b121a000407051f0b121a2a13031f0b0d1b04190305210b1a0013050b
|18=>0xd1b1a0004090b0d0a4d00040773050b0d0a00040736050b0d0a25000722052b0b0d1a0407613605210a000407220b0d0a372a041905010b0d0a50001361180b0d0a00041905010d0a4d0013031f0b0d0a2a04077205010b0d0a000722050b0d0a3c04192205210b1b0a040706050f010d1b000722050b0d0a4004072605010d
|19=>0x407050f0d1a7100071805121100040715050f0d76000407060b0d0a750004071834210a00040774050b0d0a0004071805211b1a00041903051f0b120004071806010d1b0a00073605080a0004134b030b0d0a00041905160b0d1b1a001305210b1a0a2a00071e050f0d1a000407052114011a0a001329030b0d1a000413180b
|20=>0xd0a760004071503050b0d1a2a071e18060b0d0a2a0705140b0d1b1a2a070305210b3200040734050b0d0a5600070306010b1200193605140b0d0a001305210b0a250004073618220b0d0a2a07050f330d0a0004072405080b0a000407051f0d1a0a71000718210a7900040305080b7800040722051f0d0a76041377080b0a00
|21=>0x705010b1250000407360521160a0004070305160b0d2a0007150521010a00040705214a010a0004077c051f0d0a00040703220f1f0d04071e18030b120004070521010a2500077b050b0d0a000407050b120a712a0013052b010d0a00040706050b0d0a7a001329030b12000413181f0d1a0a00040703220f0b0d2a04071815
|22=>0x1f0b0d1a0a07050b0d0a83000419052114010a0007050b0d1b1a100718170b1200041918050d0a410007050b0d0a8200048109050b0d0a00040715060b0d1b0a2a09050b0a7f000407220b0d0a7e00040758051f120a00040736050b0d1b1a000706050f0b0d2500070605010d0a1100072931050b0d0a0407051f0b0d0a7d2a
|23=>0xa3c000407060521011b0a00071806080a0004191e050f0d0a00040718050d0a4000041915050b0d1a000717220b0d0a2a07050f1f0d32040718220f0d1a00040736051f010d0a2a0718060b0d0a25000734051f010d0a19050f010d1b0007051f0d0a4e0004070521010a6800041922052b0b0d0a040705210a232a04072206
|24=>0x71505210a760004195105010b0d0a000729060b0d0a2a0007050b2d0d0a0004070521011b1a000718150b0d1a00040703055e0b0d00040706056c0b0d0a000718052b0d1a000419054a0b0d1a0a00071e06010d0a000763050b12000407291805010d1a000736050f0d1a0007050b0d237d000413050b121100040718050d
|25=>0xd1b1004074b03060b0d0a00070322210b0a2a04072903060b0d1a0019030516010b0d001318211a0a00040785050b0d0a00040715060b0d320a0007030b0d5c0004071c050f0d0a0004073605010b121a0007260501120a000407051f0b0d0a44040718450b0d0a00040736050b120a2a00070322210b1b04074305010b0d0a
|26=>0x71503050b122a04070305161f0d000409051f0b0d1b0a040717220b0d1b04070605210b0a250013050b0d0a4000041918220f0d0a0004074f050b0d0a00040705210a7600040903010b0d0a0007154b050b0d0a2a071517050b0d0a2a1905010d0a1100130b0d1b370004070305860b0d00041305140b0d1b0a0407050f0b
|27=>0x10b120a000703241f0b0d0a041329150b0d0a0004077c220b0d0a000407052b010d1a0019220514010b0d0a0729060b0d1b00041924050f0b0d0a00071803160d000407050b0d0a870004190521011b0a0007050b0d1a6200040929180b0d0a00040706052b010d0a000729240b0d0a0004130b0d0a372a00040718060f0d1a
|28=>0x660b0a0004071505140b0d0a04071803210a2a000407050b0d0a3d00040757050f0d0a00040736051f120a00040722050f140d0a0407054a0b0d500004072205010b0d1b1a07050b0d0a1110040722061f0b120a040789050b0d0a0004072206080b0a00040718050b0d0a3e0407050b0d0a8800040736050b0d0a3e04193605
|29=>0x2a07060b0d0a372a0007050b0d0a8c2a00192918050b0d1a00071705140b0d0a00072603010d0a00040703060b0d250007050f140d1a2a00072903060b1200040747050b0d1b000407050f0b0d7d2a0009050b0a8a0004070305010b0d1b2a191505210b0a00041303160b0d000419050b0d0a6200040718220d0a7600040705
|30=>0x12000718051f0d320a0407220508010a00040703051f010d1b0405080b0a8d000407180501120a2a00193603010b0d0a000718050d0a760004071815030f0d0004073405080b0a0004072205210a7600040718050d0a50000407052b0b0d0a10040736221f010d0a0409051f0b0a420004071805010d1b1a000703051f010d0a
|31=>0xa00040717051f0b0d0a2a0731050b0d0a0407052101320a2a00131503210b0a00040706050f140d0a000749050f0d0a00040918210a000407050b0e0d0a040729340b0d0a0004071e1805080a0004070508011a000905210b1b0a00041318010d1a0a0007291705010d0a0013050f010d1a000705160b0d500004190305010b
|32=>0x5860b0d0a00040757050b120a00040706050f1f0d1b040905080b0a00040726050b0d0a25040731050b0d0a00040706050f0b0d1b2a07050b0e0d0a000407050f380d00040790050b0d0a0004076131050b0d0a0413050f1f0d1b040717051f0b0d1b040761050b0d0a2a0007050b0d0a8f000407050b0d0a8e04071e4c0b0d
|33=>0x152205210b0a000407050b0d0a440004071806210a0004075f03050b0d0a0004075b050b0d0a00040703050b0d321a000419050f1f0d0a00040734052b0b0d0a04071803010d1a000791050b0d0a00040761050b0d0a3e0407050b0d0a3e0407573605210a00040761050b0d0a00040706052b0b0d0a2a0731050b0d1a0a0413
|34=>0xa2a0007050b0d0a502a00040705140b0d1b0a04071805080a00040722060f0b0d0a000419050b0d0a41001317030b0d0a000419050b0d0a11000407050f140d0a2a0004130514010b0d0a000407050b0d1a0a200004190305010b0d0a000706050b0d0a5600071805160d1a0a000407050b0d1b7d00040703060b0d0a2a0007
|35=>0xb0d0a0004071e18050b0d1b0a040726030b0d0a000407052b0b0d1a0004070516010b0d0a2a00071705010b0d0a00071805010d1b0a00041905210b1b0a00040717050f0b0d1a00040706052b0b0d0a000413050b0d930a000409050b0d1b0a0004072205920b0d0a04192918050b0d0a000407050b0d350a00041305010b0d
|36=>0xb0d1b0a00040729050b0d1b000407050b0d940a00040718050b0d0a2500040722051f0b0d1a0a04075f29050b0d0a0004075705140b0d0a00040717050b0d320a00040717050b121a00041305080b0a00040718050b0d1a0a2a001315030b0d0a000407051f0b0d320a2a040703060b0d1b0004071703220b0d0a0004070324
|37=>0x40715050b0d320a0004076136050b0d0a00041318010d0a000413050f010d0a00040722051f0b120a0407050f3b0d0a000407060514010b0d0a000703051f0b0d1b0413051f010d0a00040729050b0d0a2a0004130b0d0a001004071e05010d0a0004071805920d0a0004070516010b0d1b000419052b0b0d0a0004130501
|38=>0xb0d0a96000413290b0d0a00040705010b0d0a68000407050b0d0a232a040795050b0d0a0004130521010a00040727050b0d0a0004073605160b0d0a0004071505010b0d0a00040718050f0d1a0004071822010d0a00040722050f010d0a0004077705080b0a000407050b0d0a7e0004072903050b0d1a0004076118050b0d0a
|39=>0x1f010d0a0007050b0d0a4e000407050b0d0a372a0004070605080b0a00041922050b0d1a0a000758050b120a00040703221f0b0d0a04071e050b120a0004071806010d0a000729220b0d0a000407220521010a00040706050f010d0a0007050b0d1a0a71000715050b0d0a76000407050f140d0a0004074c220b0d0a00040705
|40=>0x5080b0a780004071805010d1a0a0007054a0b0d0a2a00040747050b0d0a00048009050b0d0a000413050b3b0d0a000407050f1f0d1b040736050b120a0004071e051f010d0a00040757050b0d0a00040729060b0d0a0004190521010a0007050b0d1b1a2a0706050b0d1b0a2a1922050f0b0d0a00041305210b1a0a00041905
|41=>0x50b0d0a00041922050b0d0a000407050f010d0a00040722050b120a00040703050b0d1b000407050b0d0a7100041305210b0a00040705010b0d1b0a00040761050b0d0a000407050b380d0a00040722050f0b0d0a2a0413051f0b0d1b0a040749050b0d0a000407052b0b0d0a2a041305010b0d1a0a0007050f0b0d0a001004
|42=>0xa000407050b3b0d0a0004071805010d0a000409050b0d0a000407050b0d0a0010040705210b1a0a0004071503050b0d0a000407050b0d320a00040706050b120a0004071703050b0d0a000407050b0d1b0a2a040706050f0b0d0a00040706051f0b0d0a0004070521010a00040705920b0d0a00040736050b0d0a0004071e22
|43=>0x7050b0d0a00040706050b0d0a000413050b0d0a000407050b0d1b0a00040718050b0d0a000407052b0b0d0a00040706050b0d0a2a000722050b0d0a2a040718050b0d1a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x7280254008a0004
|5,0=>0xc4b060d82fac17760b8b05ad82cac15f60acb054d829ac14760a0b04ed826ac12f6094b048d823ac118508930431820ea101607db03d581dec0e96071b037581aec0d16065b0315817ec0b96059b02b58150a0a2604e302598120c08a6042301f980f0c07260363019980c0c05a602a301398092a043601eb00dd8062c02b6012b007d8032c0136
|5,1=>0x1a760d0b066d832ac18f6
|6,0=>0x1b1b8d71c6aae34e71a3b8d01c672e3327195b8c91c63ae3167187b8c21c602e2fa7179b8bb585cce2df716c38b45c594e2c3715e38ad5c55ce2a7715038a65c526c28c7142b89f9c4eee2707134b8989c4b6e2547126b891d8480e2397119388adc448e21d710b3883dc410e20170fd387cdc3d8e1e570ef3875dc3a0e1c970e1386edc368e1ad7
|6,1=>0x290b9469ca26e50c7282b93f9c9eee4f07274b9389c9b6e4d47266b9319c97ee4b87258b92a9c946e49c724ab923d8910e481723d391cdc8d8e465722f3915dc8a0e4497221390edc868e42d72133907dc830e41172053900dc7f8e3f661f7b8fa1c7c2e3da71e9b8f31c78ae3be71dbb8ec1c752e3a271cdb8e51c71ae38671bfb8de1c6e2e36a7
|6,2=>0x36db9b51cd9ae6c6735fb9ae58d64e6ab735239a75cd2ce6906344b9a09ccf6e6747336b9999ccbee6596329399318c8ae63e731bb98c1cc52e622730db9851cc1ae60672ffb97e1cbe2e5eb62f239775cbace5cf72e439705cb74e5b372d639695cb3ce59772c839625cb04e57b72ba395b5cacce55f72acb1549ca96e544729eb94d9ca5ee5287
|6,3=>0x2005cff4e7f373f639f998fbee7d873e931f2dcf8ac7be73dbb9ec1cf52e7a273cdb9e51cf1ae78673bfb9de1cee4c76c63b2b9d79ceaee75163a539d118e7ae7367397b9ca1ce42e71a7389b9c31ce0ae6fe737bb9bc1cdd2e6e27
|7,0=>0x4f8ba7a613c309da74e94272a138509ba84d9ba6ae1347099b84c9c262e1307097b84ba3a5b212c9095c84aa425321289093c849aba4b6124b091d848ac2436120b08fd847ac23b611cb08dd846b3a33a118ee8bf845bc22be114f08a0744c42245d114e883743dc21ce10d70864742e4215210990845741ec20d9d05d0826840fba05e1020e8088
|7,1=>0x5eec2f59d79eebc875e042ee217610ba975d13ae6a17250b8a85c1badee16e70b6c75b2bad79d6aeeb4f85a3c2cfe1670eb30859442c8216310b10858442c0215f10af0857442b8215b10ad08564bab061574eab2855542a8a15350a937545c2a0e14f70a738535c298e14b70a5385263a91214790a3485164289214390a1575073a81a13fee9f87
|7,2=>0x6e6437121b7aedb586d73b69a1b3d0d9686c74361a1afeed7786b7c359e1ac0ed5886a8435221a810d3976993b4aa1a450d1b768a3b4321a090cfc867a433b219c90cdc866abb336198b0cbe765b432ba194d0c9e864b4323a190eec7f863bc31be18cf0c5f862c3b14218910c40861c430c21852ec22760d4304dd8170c0475fe42fd217daebe58
|7,3=>0x7e0bbee61f630fab67d1c3e71df290f8d77c2c3df9deed0f6e87b343d7ddeaf0f4f87a3c3cfe1e6f0f2f8793c3c7e1e2f0f0f8783c3bfe1def0eef8773c3b7e1daf0ed0776443b021d710eb08754bba861d330e92774543a0a1cf6ee738735c398e1cb70e538725c390e1c770e338715c388e1c370e138705c380e1bf70df386f5c378e1bb8edd48
|7,4=>0x10bf885c3c2c2215110a1784cc424621131081883cc41c620d31062782d4414a20951042881dbc0ce20571024780e440522019100577fec3fd61fdcefe687ef43f5a1f9d0fc86
|8,0=>0x96ac4b36258932bc895a44aae6548f29c894a44a2e6507127a9939449aa24c332589927cc91a647b323589173c896643b121499064480e63f711f298f54478a23b331d188e44c702236f31ae98d34467a232d118d98c2c45f622e9316c88b2bc57262aaf14d88a2c44f26267312a98914446a222331098880c43e261e110e978704c362219f30c78
|8,1=>0xa5d452ca295334a18a4cc5246291314809a3cbd1c628d134608a2c451422892f4418a1c4d0c2285114226a0dbd04e2815340289fdbcfce27d533e289ed44f4a279513c289ddbcece275713a389cdc4e4a6715138289bd44dcde6d5336289ad44d4de6971342999ccccc626531320998c44c42260f32fe997accbb265caf2dd8
|9,0=>0x565a2b1d15868abecd5d62adb15667aaf4555a2a9b35458a9ec54d26a5915239a8d4d44dea1715038a7d4d3ca29d514e28a6d4534a2996f4c29
|10,0=>0xadac56b9eb4d159e8
|11,0=>0x15bd7
|_,_=>0
def wAt:=mkWire dB 151 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 2000006 zs)
def oP:Nat→Nat
|0=>0xb0048811050047c150a0d42c01061b41411000a504010a0182c1103044141d03004002d050a41801050441001040b43429070541429030b4141138004040c050a42c29040b4500c0a014682d04224140104054c860040542c2915010286118004342d07054142d140300c110a05424200706414110d0f4282d051a4682d040743429040a42c110a0542420070641411
|1=>0x10a41c11000a4102d1a004342907044002d040a468010d0b428110704484290d0b46801040a41c190d0b42c110504428150422414011a0b4001104034141d0300428150407468010005428111f0a42c010600414110d0f4002d0a0441c190b03814110a05450292a0b40011010a4101d0d0b4102d050a42c11060a410150d0f4282d040b4100107054283504114287e
|2=>0x50743c350a04404010b0a4102d040740c2d050a4ac151b0b42801180a4500c010042c111b0b428010a0557001181a028110b055600104188142d04114287e000b4781307044601107054342d000442c15000a4342905044342d070442c1504228001506004342d050441c19050a41411040a4786818004142d0a2240015070442c1507064342d050442d450300c2815
|3=>0x50b42819040542c111a0041c15040a434290704468150d0a4682d040a5302d0403814291a1f4002d040a4142d0d0a41c110b04428150d0a468011a0542811070643429040541429070441c11050a4141d04004102d0b0441401070442c35000a4142901054342d040b4181d05044342d0a0542811000442c29170b41469040a53411180ac2c15070440415050a4102d
|4=>0xb1b82c350400428010a0442c110607414110b0543c01070542c29030442d450300c281504034a8170004428610b0d40029050b414053218068010a0440c2d070540c110a0542c110a05460680a0442c151b184142d000a478681f054002d38004040c050a42c29040b40c2d040741429290440c2d050a41411380d4040c0a0542c110b0d460010705460110b0543429
|5=>0x441c150a0d428110b0d40429000a4102d00044142900054281107044287e000b42c890500428010a054101504004343d0a0b4142d0d0a41c11000b41029040b424200706410150d0f4282d05044040c050a42c29040b42c150706414110d0f42c290405428110501434290304414010004428150b054102d090dc1c190405428110b05414110d0f42c290d0a4002d
|6=>0xa4102d07064342904054782b18004142d0b0341c15000b414290514404010b04404010d0b410150b0442c0e0500428010a05414690d0a400150a04410010a0d4002d040a4002907054002d050a41c110d0b428150a044108d0b1b80029000443c1507054282d0d0f400110a0b410290a0d414aa00044682d0b0542811051480401040b42caa0400428010a044342d
|7=>0x1a0b410290004428110d0b41c1501004342d040b41029030b41c150a05428110a0441c15000a4142d070642862050442c152900c6029050b4182d0d0b41015000441c11140ac0401040b42c1107044602b050b4100107054002d050a411450300c142904114287e000b41401070442c35000a504010a0182c11040a410010d0a4682d040a41c111504c6c151b0440029
|8=>0x10041c11010542c111804400110b0542c41052a800110d0b4882b05004142d0a054201f0d0f4282d150bc88290005414210d0f41c150a0b42811050182c29040b43429050b4287e000b4542f030041429370042c0e0a054a8150d0b400110b05428010d0b4142d040a4283507044002d050a4142d050440029040b4182d04054343d0b0a41c151504c0c01070442801
|9=>0xa14834290100404150d0b40429040b488290d0b400150d0b4102d41054042b0b044002d00054282d050a428150d0a46001050b4342d0b04468030a04434290105c2c110f0041c150b0a47c6a000b41029070543429030b414290b0041c150b0542811150bc0c010a0540c010004428151800400110b0542ca90400428010a04468010d0b428110d0a42815040542c11
|10=>0xa0b42c011a0042811050142c0104004102d050b414a9040042c010b044282d070440029040b468620b05428110f0041c110b0a42c35040042c6e000a40cef050a404030b044342d070440401040b414aa0400428010a044142d060a4342905044042b070442c110b054146d0a0041411800dc2401070641411043740c2f050a434291804c2c1504054287e000b4002d
|11=>0x30042815040740c03050a42c0d140301429010042c11000a4342d040b41029250b46803040a4ec290100c2c111f054002d040542c11051147c2b0a0d4002d040a46029050b46011040a42c29050b4342907054287e000b444110a1f8002d0d0b41411000a4102d0b05414110d0f42c29180041c11050b50401010ac2c11030041c110a0442815030441401000442815
|12=>0xa004141d030bc14291600c0429040b41c15010042c11052a810011504c0c010a054342d030b41029050442815070441429010a4102d0b0d41c150b0542811050446c151b04400290a05460680a0442c15041e86001050b410290a0d42c110d0a46003050b414ca1a004281184054606a0a0442c15060b43429050442c350500428010a0546c19050440029150bc2c35
|13=>0xb0a42c15040f4282d050a4342d070440029040b40c7f000b414290607414110b0546c2d0a0041c150b03800110a0541411040a42c29050b40c010d0a400110a0542c0107064280105044100d0a0041401050a468030d0b4281141004042b040b4101d00054342d0b1580c010a054181d0b04414110a0545413030041429030040c1100044281507044102d0a1f8002d
|14=>0x50b4362e090b41c19040540c010a054342d0704414290f0441c150b0a4542f220a40015380d4040c0a0542c110a054342d000442c15340b4a81504004182d0d0a414114a0ac2851010042c110a0d42c0104054343d05004282d61000d82918044101d0a0d42c11030b41c150300414294105428060b0442c110a1f4002d040a4101d0100400150b0448813050041c11
|15=>0x40b43429070442c110a0543c350a0b400150b045e0110807c343d0a0b434290a0541c11010542c115f0bc606d000a4142d0b0540c010a0b41429150bc342d220a4502b01004102d0105400150b0442437070641411050a410010b0042c110004458170f0442c290a044101d180a4142d051a41015050a46803040a4a82d00044282d040543429030b414292904c6029
|16=>0xb41c15000a41015160543c110b0a57002181a028110b054100d6100c60690a0442c15040b4342d2a0a4001105074342d0300414293600c60110b0542c1507064342d05044e0010103028150b044a81504004482d0d0a46001050b4482d0d0a41029040b4002907064342d04054142d070541029040b4100d040b40c2d050a42c2907054102d040a42805140ac0401
|17=>0x1a05c28010a04414110004428150d0b488290005414ca1a00410290d0b414110b0540c7d000b414295800460130b05428151a004281107044002d0a0b418010504414290a0442c110b0558400181a428110b054182d0d0b410151f0a42c016100c5c2d1a054d801060b41411000b41015000a42c290706410150d0f4282d0103014290b0a4102d181a428110b0542c29
|18=>0xa414690a0b410291f0a42c01050446c130705400290706428010504414011f04c002d040746029050b42841052a80011040b4141d00044502b2a0b400110a00404010b0443c350b0a4142d0b0a4001504054101d010ac102d070540c110a0541c110a1f8002d2a0b410010a0b41c15010042c11320bc6801040a41c110b04428150b1a810150a044142d1a0b41029
|19=>0x40b46029000a4142d0a6d4a82f00044142d1a00c281105004002d040a46029050b40401040b468151a00428110d0a468150a044343d07054282d0a04400110b0541c150300414290b004a829000440029050442815050040c110a0542815042280015180040029050b428151800c2c150a1f4002d040a41001010a4102d0a06410150b044142d000a4102d070442c35
|20=>0x50b400150b044282d000542c1108054343d0a0b410dd030bc14290a0440c2d050a4d829180442c151b0546c11000a460110b0541c150b0542c11070542c29040b414010a0d4002d0100c2c29040b40401040542c110a004002d050a41c150b0042c110b03400110a054a817050740011040b46001050b47c130b0042c15010a40029040b43c01070442c29070540029
|21=>0x5428110d0a460130b0540015000b414290a0d460010b054142d040542c110f05414010b0a4342d000542c11050442c29040b40417040b410290b1580c010a054282d01004102d0304c1401050a43c8a050042c290f0541c150a0b4040e0a05410010b1b80029032ac00110a0541c150b0d42c11260a460030b0540429010542c11040b40c010a05410290b0a4142d
|22=>0xb0a414aa00044201f0d0f4282d0a0442c110b0543ca904004282d2904c6029050b42401070641411070540403040b42801000b4282d060b43429050447c150b0042c11041e46001050b42c0d050442815070442c350b04410010a00428110a0040011050441401070442c290a044342d070541c110b0042c111a1882c150a0442c0e00044281504054343d0a0b4101d
|23=>0xb0541c190504414aa00044342d040a40c010a05468010a0443429050440c110a0540011000a42c29050442c01050442c350b0447c13000b460110b054882d00054101d000542c29040b434290005428010a05404170b044342d070540029040b460690a0442c150103028150b044140104004282d000b41c15000a4d803180442c150f00410010a0b41c15040b41029
|24=>0x14110705400290b0543c010a0b400110504410010005428110b05404030b0442c11
|_=>0
def oO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x138821604020000000000003e2000000001e1000000000e100000000000000001b1034200000c10000000000000b880000000049408880000000000008080000000000005300000000000000000000000000002a8000
|5,1=>0xb481428000
|6,0=>0x7c400001dd43a180000000000000006f500001a943410000000019c433086240bc817082d100000b22160429a80000000000000000000a06000025a800000001194000000000001090000000000000000000000007e60f480000000074600001b980000686000019882f4
|6,1=>0x2fc45d2800000002dcc0000000000000000000000168600005988000160600000000ae200002a545318a33000000000000000000000000000000142400000000000138a00004d88000000026844c889450000244c46a00000000228c0000000000000004398834000000000000000000000000000803
|6,2=>0x92980002428471400000000000464c8b191150000000000010e3000042cc0001065202a3f147c9800000003e04000000000003cd478180001da600000000e85000000007220000000000007020df1000000000000000000037846d200001aaa000068a0000198a32c40000ca1000031cc6218c04
|6,3=>0x5a5000016452c62579400000002b2a0000aa295312a420000000151100000000000000000000000a62947500000000000142528044ed4000137426864cc498180000000000097892d200004a509408000
|7,0=>0x43e8870d0c9a1540000845106a209440a8808cff21fa400007d90f921ee43d4879cc00000003c8678c4efa00003b6875d0ea19d1339a80000e519c9138a87104e021bf137686e0cda2000036266b500001a9434a86850cea199432c6649000018e43166620cc29981430025f1000017842e885c4cb6a0000
|7,1=>0x5906b1116022bc40000ae115b8ab3455e8ab0c0002a9354a8000150a29d45328a55148a00000000a38d45228735086a0c400028120000a0053e9a79400009d8d3a127134da89a5132a00004c4697cd2e1a5844a880001289a4e3496691d1221800048088f10000239346c60000000232445c88acd13a2234
|7,2=>0xdfd1bda00006ee8dd0db89b6f20000dad1b3a36340000d7d1ada35836aa6d4c800034f46968d20da2234046788ce4d9b1b3426626cc0596232846488000190231c46326c58d899b1036188c24d82a30235fc8becd7d0af645e480001779aec3000000017422e445c26b7500002d945ac6b4916722cb3
|7,3=>0x83a906ca0ba413481e902d203a40347fe8fed00003f740000fcd1f90bee47d48f9900003e337c060001ee9bda30000f591ea8bd2379c8f3440003c9478c6f091df9800077680001dba3b340000ec0dd62000075080001d29ba230000e790000000073840001cc2395300000001c91800071c8e2cdc3a3834
|7,4=>0x46328be8000000045b48b0600022b145330001140e262448400000000000000088880002209c3d487830e4c000435400010d0618242c485080002129c214
|8,0=>0xa407474e8d1d173a287444e871d0b3a107414e811cff39f873e4e7b1cf339e253bca761ce939cc738ce701cdd39b4735ce6a1cd1399c732ce641cc5398472fce5e1cb9396c72cce581cad3954729ce521ca1393c726ce4c1c953924723ce461c89390c720ce401c7d38f471dce3a1c7138dc71ace341c653
|8,1=>0xba4773cee61dc93b8c770cee01dbd3b7476dceda1db13b5c76aced41da53b44767cece1d993b2c764cec81d8d3b14761cec21d813afc75ecebc1d753ae475bceb61d693acc758ceb01d5d3ab4755ceaa95523a9e7530ea49d463a867500e9e9d3a3a6e74d0e989d2e3a5674a4a931d233
|9,0=>0x1824b0396052c065804aff95fd2bf657e4afb95f52be657c4af795ed2bd657a4af395e52bc65784aef95dd2bb65764aeb95d52
|10,0=>0xc1c38347060e0b1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0xca00000000005d800000000027820000000013310000000005a00000000002c000000000010200000000008000000000002000000000000dc000000000060000000000028000000000012000000000008400000000004000000000001f00000000000e80000000000600000000000280000000000110000000000080000000000034000000000018000000000008000000000003800000000001040000000000800000000000200000000000080000000000038000000000002000000000000
|1=>0x402000000000200400000000100000000000077410000000039e4800000001cf0400000000c09c000000003fc1000000001df0000000000ef04000000006c020000000033c10000000019a0800000000cd000000000060820000000029910000000013e88000000009c000000000047a00000000023c00000000011888000000008c000000000044000000000021800000000010a000000000082800000000041000000000020500000000010200000000008040000000004000000000001c01
|2=>0x211e0000000010080000000008008000000004000000000001a0f080000000c15000000000574880000000237410000000119e08000000088e40000000043e02000000020190000000010020000000008000000000003e79200000001800000000000abf080000000487800000000241000000000120000000000082000000000040a000000000204c00000000101a0000000008040000000004008000000002000000000000bbc5000000004c000000000022800000000010300000000008080
|3=>0x85de4800000042cf140000002067820000001024000000000808a08000000402200000000200200000000100080000000080000000000029cf040000001467220000000a3381000000050020000000022e3600000001101100000000833d50000000419e88000000208000000000102f300000000803810000000400800000000200300000000100000000000068094000000031c4880000001841000000000c132200000006008000000002b32080000001248200000000876820000000433c9
|4=>0x180040000000094080000000048e6820000002436010000001203a00000000901700000000480400000000217741000000108100000000083cf240000004167b2000000208a000000001039e0800000080fd04000000406f820000002035c10000001019e4800000080cf0400000040120000000020048000000010008000000008002000000004000000000001820000000000a1ba0800000050cf040000002838020000001305400000000919a08000000489d0000000024020000000011e188
|5=>0x10009620000008004b0000000400030000000200012000000100002000000040c0504000001818292000000a133c10000005082f08000002840ea00000014027120000009503410000004619e8800000220cf440000010a469200000081c04900000040d9a28000002060c2000000102c68200000080634e0000004000020000000e0cb440000006c0000000000343341000000185de28000000c2cc3000000060e782000000306141000000181de08000000c0cf04000000603e02000000300ac0
|6=>0x2011000000001008010000000800e7c20000040033e10000020018c00000010004fa400000800200000000400020000000200002000000100000800000050a03820000028135e10000014099e0800000881cb040000044005000000022001c00000011000c0000000860e2040000043067a20000021833c50000010c19608000008608a000000043022c20000021801c00000010c00c000000082850840000041427c20000020813e500000100a962800000800ef040000040075c20000020033e1
|7=>0x100819e080000800dc7140000400448800000200033c1000010000050000006007842000002103c68a00000810bb480000040859e7000002007cf3c00000d026fc20000060213e10000030109b08000018054f8400000c006fc20000060035e1000003001a508000012288a040000090267d20000042431a80000021019f0800001080c7040000081467820000040a03400000020500e000000102805000000081050000000040820000000020219c080000100d07840000080477020000040233e1
|8=>0x800419e8800040020694400020009e728000100023b91000080011940800040001cf040002000077a20001000034f10000800019e8800040000cf04000200004b8200010000010000004008b0a080001800004000000840823100000402405c0000020120060000010088d9040000804466820000400404c00000200002500000100000c0000008000004200004000000100001009b8e080000804d0784000040264480000020123f410000100913200000080485f84000040242f820000201213c1
|9=>0x2000218e300009001001000004000d678a00020006b244000100031de0800080018ed040004000c7302000200062a400001000314c0000080009ef04000400046782000200000380000100000000000041010d1840002080867e20001040433c10000820211400000410108500000208080280000104003b910000820019f88000410000700000204406b820001022031e10000811002e00000408800b000002044003800001020430e400008010396880004008014000002004004000001000e0011
|10=>0x1000000a033c94000015019f09000002844f0470002180c78204400000314c02060420d9e780c3000014d3806180000679c00801091e3c90040006031e08020002018f04008010832698002418c062010009300019e08004980000400002080000680001000a10341000800181de0800400000cf440020000067820010000002100006041259e60001063078d3000081180c48200040800bbcc
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>2
|5,0=>0x5c1200000000000000000000000000000000000000000000620018000000018000003000002e0000000000401800a000000000800000380600000000800000007200000000000000002600
|6,0=>0x117a000011c000000000000010800063d090000018000c41611000007a000000000453480000003c000ee000000c08710002c0a00000880000000000a0b00000000000000002100000000000114008a001742200000000009002b82e000000cee252f0602e00291497400000000000088012e000018800000002400000000000000885c0000108000a00088000853
|6,1=>0x50004a292b000002a801f4043b800000400000000000000d0b00000000430cb648a79108104200000000817001e00800000000e00119ec000000084183500000000800020001f129980a000000c00000004c10000880000ab000002800000000a460000000000012c14000a80116005c9dc000300020108b
|7,0=>0x8bb8cb3200280b91e5b82000116d80012b58dcf2900000396980804010001800171770a00085ac086331e22002013022fe24000e6df4449422002c850007a05800006da6b5ea50e5f378427200098921b531ae1e410033e0a4d8988400008914a29335a0900a110a80022778611802897c9ae0c0005b4400f332491c4b10883c013f1fa64171801c74008c900459200
|7,1=>0x1985d7b4306a904e3c842bc002900550068d0339c00d8088013e0500040a4082d0100139913f41000a080046630014c64002080016080042400000c0004a0500000840004821df21001b138005b0850218001510adf00034ce110885c001d56b9050d52d8441617370f9049e40000548305a50420503101b4056b814061c760002211000019cbf3e28400c308869f00b
|7,2=>0x1754800003404000300b0002c3d420000000002c000104f02020003300010672d350001750
|8,0=>0xa595c56f2a2bc13b15a9aa216fcaaa4de2a76551a095898cb05e51ab9f4ad40599f98acc51c052a9286b9a527537c1c0aea2ba59ff491621d542ea8cd6073e155294a98622424cf4690b634cb60a69ea4e8145cbe167dd12693d7b03ced2e70cdce8c8803c2213a153b670376ed3d82848b48da1287b8c2ad3669c9e4d2a5c18536e38e3a0687f5e1f65ed4
|9,0=>0x3c6331f43239454e8b181d330224ee56386123d814766ac922707023876eb
|10,0=>0x1b0e9b87d
|11,0=>0x34
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 49 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_245 10 roots_245 ops++addP pm 1 dom_208 4 roots_208 ops++addP pm 2 dom_244 8 roots_244 ops++addP pm 3 dom_241 8 roots_241 ops++addP pm 4 dom_39 5 roots_39 ops++addP pm 5 dom_178 5 roots_178 ops++addP pm 6 dom_243 9 roots_243 ops++addP pm 7 dom_183 9 roots_183 ops++addP pm 8 dom_246 9 roots_246 ops++addP pm 9 dom_231 9 roots_231 ops++addP pm 10 dom_242 7 roots_242 ops++addP pm 11 dom_103 7 roots_103 ops++addP pm 12 dom_215 10 roots_215 ops++addP pm 13 dom_119 9 roots_119 ops++addP pm 14 dom_199 8 roots_199 ops++addP pm 15 dzo_101_2 5 roots_101 ops++addP pm 16 dzo_210_32 5 roots_210 ops++addP pm 17 dom_230 6 roots_230 ops++addP pm 18 dom_118 6 roots_118 ops++addP pm 19 dom_167 6 roots_167 ops++addP pm 20 dom_227 6 roots_227 ops++addP pm 21 dom_115 6 roots_115 ops++addP pm 22 dzo_214_32 6 roots_214 ops++addP pm 23 dom_87 8 roots_87 ops++addP pm 24 dom_83 5 roots_83 ops++addP pm 25 dom_179 6 roots_179 ops++addP pm 26 dom_182 6 roots_182 ops++addP pm 27 dzo_229_2 6 roots_229 ops++addP pm 28 dzo_211_32 6 roots_211 ops++addP pm 29 dom_226 4 roots_226 ops++addP pm 30 dom_114 4 roots_114 ops++addP pm 31 dom_86 5 roots_86 ops++addP pm 32 dom_55 6 roots_55 ops++addP pm 33 dom_102 4 roots_102 ops++addP pm 34 dzo_117_2 6 roots_117 ops++addP pm 35 dzo_245_2 7 roots_245 ops++addP pm 36 dom_99 4 roots_99 ops++addP pm 37 dzo_213_32 6 roots_213 ops++addP pm 38 dzo_197_2 5 roots_197 ops++addP pm 39 dom_69 4 roots_69 ops++addP pm 40 dom_225 5 roots_225 ops++addP pm 41 dom_228 5 roots_228 ops++addP pm 42 dzo_213_2 6 roots_213 ops++addP pm 43 dom_135 5 roots_135 ops++addP pm 44 dzo_215_32 7 roots_215 ops++addP pm 45 dom_23 5 roots_23 ops++addP pm 46 dom_214 8 roots_214 ops++addP pm 47 dom_151 8 roots_151 ops++addP pm 48 dom_213 9 roots_213 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_39 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_101_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_210_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_214_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_229_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_211_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_117_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_245_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_213_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_197_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_213_2_69 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_135 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_zo_215_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_23 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_213 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_245 10 s (0,roots_245.map (·&&&dom_245)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 2000006 zs symsG zs (hk 2000006 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 2000006 ys h symsG ys (hk 2000006 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 2000006 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 69 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 69 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 235 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 107 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 235 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_256 : ∀ i, 256 ≤ i → i < 289 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 33 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 289 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 124 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 124 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 27 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 2000006 mkCut s i=true:=by
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
def dzo_217_32:=0x303030300000000030303030000000003030303000000000303030300000000
def gzo_217_32:=0x303030300000000030303020000000003030302000000000302030200000000
def gsh_217_32:=0x3030303000000000303030200000000030303020000000003020302
theorem lowS_zo_217_32_208:Lower true dzo_217_32 roots_217 gzo_217_32 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_32) [(dom_217,32)] (by decide +kernel) (lower_slice_b (T:=gsh_217_32) [(0x2020202000000000202020200000000020202020000000002020202,0,1),(0x3000300000000000300030000000000030003000000000003000300,0,8)] (by decide +kernel) lowS_208)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0e00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0e000000000f0f0f0e000000000f0e0f0e
theorem lowS_zo_219_32_208:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,0,2),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8)] (by decide +kernel) lowS_208)
def dzo_216_32:=0x101010100000000010101010000000001010101000000000101010100000000
def gzo_216_32:=0x101010100000000010101000000000001010100000000000100010000000000
def gsh_216_32:=0x1010101000000000101010000000000010101000000000001000100
theorem lowS_zo_216_32_208:Lower true dzo_216_32 roots_216 gzo_216_32 5:=lower_iso_b (d1:=dom_216) (r1:=roots_216) (T1:=gsh_216_32) [(dom_216,32)] (by decide +kernel) (lower_slice_b (T:=gsh_216_32) [(0x1000100000000000100010000000000010001000000000001000100,0,8)] (by decide +kernel) lowS_208)
namespace S_251
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,10),(8,40),(8,72),(8,136),(9,11),(9,25),(9,41),(9,73),(9,137),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,192),(66,67),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,192),(160,161),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|6=>7
|7=>118
|8=>241
|9=>83
|10=>9
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x962b57d5de6746a47b162767623f1c05fb8
|7,0=>0xe9112ce2d7cbb44c487db9074b7758b6813b58c9ac1bcaa94fa4a5ea2bb8a18c3a12b39bca098fb1988af901bc8d0678b5ae8aad0859c2851a18508e8382583708801e17fa6a7e7507ac8875c9575513743de7136d70d756cd436bbe26865a65b5562b185f6835dccd5ce1e5ad19588a7574fe56dde5593f54c6b549e9516685054f4f01d498924972547ee9466e5456ae4442143afd403ea3cde33a7093a5e33977738ac836d0a356dc34e4a33d3b335ce32265306bc2f7522f6812f1c42e48e2c9942a27429dfe298c428d86280fd280ab27df1273a326b702680e23d2822bde221ad21210207a02047a201151ed981b8b91ae7c1733916c6a1606215a7113bfd129d011c9a0fed50f12e0eec00d6dd0b7ef0b419085a606ff606f7f05e0e03a1401234004cf
|8,0=>0x4b2154a9e949e3947ef247b2047a2c46d51466ce451dd43b0f438b8432a4431be4087a3faed3f58f3ddcc3d42b3d2463d0183ca853c4753bdc63b56c394f138fdc380a237c03375cf3735536ef53649f355f135501354af337f73362a32ca132b2e329cf31b5a3143a3112c302132d2852bd312b8a82b27c2b2382aeea29f9c28ee3285e1284cb26b2c25d6f24eac24e0524d9423f3923bcb236c32238c2221f2156320c9a1ed781d8261ceef1c1351b3ed1b3a31b30019b1e19a8518be81881d17a9817985168a31633a1606215fbd1519114fba147ad14383136b3126f41207411ce11198511026100320d2560c5fb0c52f0c3d70b0ca0ade80a0c709e2909acf08f670858c08368078b706da40696e068d1066d7064bc04f0e048d0039560381c0366c032970321602c120244d020ed016c700e8300e42007140057700498
|8,1=>0xe94e8e77a0e2e46d801ed7fa5d272cd1f70cf9d7cd8b1cc482cb554c8ff5c2ce9c235cc1ed1bdfd6b9c9ab5f55b5a27b590cb54d5b3be0ad963ac630a9e45a52c7a4591a426ba27729cfca9c66d9b0cd9ae9d9a4ad96c1e9617b93b2b91ca4902af8c4928bb548a296892f48927b8857c869318688783a1f82917818b1813aa7dddc7d8747c7927bd537ba097b69b7ae38798be78fa0785977763675f047323872f4b727c8716886e4986d1cd6cc936c20e6bb8e6b9b36b91c6b6f66b3f66a2386949968d7f67b7567645656ab65062627016199a60c4160957600d75f6ec5ec395c5085a20259d915939c58499575f35717454a7c52f0e52ef7528fa5224c51f3151e5151a805182550be950b4a50a8b4f41b4d61e4baee4b96b
|9,0=>0xe9f97e7737cc5b1c1f3fbf87eb64c2b4c83b1f52b16e4a131b9b7bb9b7029624d9550994faa9396b8f85a8be808b08a7dbc47d314727c66fdde6ca956c0dd6bef368a73687b3650235ffd55a0b357692563af56395505c24a17f495a44816147e7f4698b460984210d406cd3f42a3ef5e3d0123c15d3b92a3a5cc38cac36461351b53019c2f8c12f6942da7c2d3af2bb012aa75295ee28bfc283a02516b24a752300a1ed891c0961a49d19d7d19398175c11731416f1515d6c13d1810b8a101c00b32d0908f05c10053b60280701154
|10,0=>0xc34df840fe5483653593527d9411753ecf2294df1497e
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f00000f0f000000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0ef0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00505050505050505050505050505050505050505050505050500050005000500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ec0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c505050505050505050505050505050505050404050504040505040405050404f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
|0,1=>0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0ce0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c505040405050404050504040505040405050404050504040505040405050404f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000f000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f000f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f00
|0,2=>0x505050505050505050505050505050505000500050005000500050005000500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f00505050505050505050505050505050504040404040404040404040404040404f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c505050005050500050505000505050005050500050505000505050005050500f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0c0c0f0f0c0c
|0,3=>0x505050505050505050005000500050005050505050505050500050005000500f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0000f0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0000000000000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a505050505050505050505000505050005050505050505050505050005050500303030303030303030303030303030303030303000000000303030300000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0000000000000000f0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e000000000000000050505050505050500000000000000000505050500000000
|0,4=>0xf0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f040404040404040400f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0000f0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00505050505050505050505050505050505050000050500000505000005050000d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0d0d0c0c0d0d0c0c0d0d0c0c0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f00000000000000000000000000000000000000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e505050505050505040404040404040405050505050505050404040404040404505050505050505050505050505050505050505050505050404040404040404000000000000000050505000505050000000000000000000505050005050500505050505050505050504040505040405050505050505050505040405050404f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00005050505050505050505050505050505050505050505050505050505050500000000f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0c
|0,5=>0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f000000000000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00a0a0a0a0a0a0a0a0f0f0f0a0f0f0f0a0a0a0a0a0a0a0a0a0f0f0f0a0f0f0f0af0f05050f0f05050f0f05050f0f05050f0f04040f0f04040f0f04040f0f0404f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0505050505050505040404040404040400000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f00f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0f000f0f0f000000505000005050000050500000505000005000000050000000500000005000000f0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0f0f0a0a0a0aa0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0ac0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0e0e0c0c0e0e0c0c0e0e0c0c0e0e0000f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0c
|0,6=>0xf0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00000f0f0f0f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f00000000000000000000000000000000000050505050505050504040404040404040000000000000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0e0000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a00000000000000000000000000000000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a00000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f05050404050504040f0f0f0f0f0f0f0f0505040405050404505050505050505050505050505050505050505000000000505050500000000505050505050505050505050505050505050505050505050000000000000000
|0,7=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0000000f000000f0f00000f0f00000e0e00000e0e00000f0f00000f0f00000e0e00000e0e0000f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0ef050f050f050f050f050f000f050f000f050f050f050f050f050f000f050f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f000000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f0f0f0f0f0f0f05050500050505000f0f0f0f0f0f0f0f0505050005050500f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0c0c0f0f0c0c0000f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0a505050505050505050500000505000005050505050505050505000005050000a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0a0a0a0f0a0a0a0f0a0a0a0f0a00000000000000000000f0f00000f0f000000000000000000000f0000000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a00f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000
|0,8=>0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a303030303030303030303030303030302020202020202020202020202020202303030303030303030300000303000003030303030303030303000003030000303030303030303030303030303030303030000030300000303000003030000303030303030303030303030303030303030303030303030000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f000000000000000000000000f0f00000f0f000000000000000000000f0f00000000f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050500050005000500c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0c0c0f0f0c0c00000000000000000000000000000000f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0000000000000000505050505050505000000000000000005000500050005000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f000f0f0f00
|_,_=>0
def sP:Nat→Nat
|0=>0x504260c0b001424050422020b00060508020b230014181d0422020b0621050908020b00142005041f0c0b16141c1d04030b000605040c0b1b0006051908020b0006170504020b00060f0509021500141304020b10000612051104020b060f08020b1000060f0e020b0d0006040c020b0a000605090802070006050403020100
|1=>0xb0a0016142d130508020b001413052c08020b00060504021530000605112c020b00140f1809021a1614052c020b2f2a062005040c020b00140f2b020b1000161425200504020b16142d1d2c04020b2a06251c05040c0b00142904020b10001606241c0504020b00061c05040b28001412051104020b1614271804261f021606
|2=>0x1425241d04020b00062405041f020b000605041f0b280006340f0508020b0014210f052c020b2a140f050902370016061805041f0b36160605350804020b0014251d04020b2a14340f1d040215001421052c08020b2a06050804020b0700142e05041e0100160633050402150014130f1d04020b00063205040c0b0014042602
|3=>0x42602150014181d041f0c0b14053504020700161413052c04020b2a1405042602152a3c060e0504020b00142405040c020b00141c1d043a0b00142104020b100016060f052b08020b00060504310c020b0014120504020b160605040322020b000629050804020b00062505041f0c0b000621052c08020b0006270504030200
|4=>0x41e15001439120504020b1606130504020b0014041f020b0a0016060f1808020b00140f1d2c020b2a1405112c08020b2a060e0504020b3600061805040c0b360006180504220c020b062705041e0c00061c0504030c0b00140508020b3d2a062e050422020b00062d130504020b0014251d040c0b00142405041f0c0b000605
|5=>0x20b00141c1d04220b0014271d04030c0200140508020b3f2a14341804021a1614251d0422020b0014181d04221f020b060f0511020b0014331d040c0b001412050804020b161405190402152a0639051104020b00060504031f0c0b00142d0f1d04020b2a142d052c08020b2a1413052b04020b00143e050402370016141c1d
|6=>0x7001614050908021a2a060504024100160605092c0215000605112b04020b0006340f05040215001425240504020b2a14051104021a2a142005041f020b16060f0e04020b0014050403020100161429130504020b00140422020b0a0016141c2005041f0b161434050402370016140f1d090215000605040c0b4000062d0508
|7=>0x60e0504020b001421050804020b2a00144705040c020b0016060504020b460016143b05041f020b0016140504020b450016140504020b440016060504020b400016141c0504221f0b00160605110804021a001421180804020b2a142505041e4300160605351104020b000605092b08020b0014251d041f0c0b001405090802
|8=>0xb00140f0511020b00161421052b04020b001614052c020b4c0016142d0f1d04020b001614250504020b4300161405044a020b0016141d04020b1b001614050908020b2a0014490504020b001614210f0504020b2a00060f050402150b00142d052c08020b00161439051104020b0016141d05090402150014480504020b0016
|9=>0x60504020b3d001614340f1804020b001614530504020b001614271d040c020b00140504261f0c0b001614050451020b00161405041f0b500016140f05020b2f001614051904021500161405092b020b0016140504020b4f0016140f1804020b2a16060504020b4e00140504020b3d2a164d06180504020b001606052b080402
|10=>0x21a152a142e200504020b00161405041e220b00161405040c0b4600161418050422020b161405040c0b400016142d0508020b0016143e2d0504020b001614251c1d04020b0016140504020b57001606050402550b0016142e05041f0c0b0016061c050402150b0014050402540b0016141c0504030b0016060f1804020b0016
|11=>0xb40001614252e0504020b001614180504020b461614052c04020b100016060504021a1500143305041f0b0016060504020b2800140f1804021a0b16140504020b5a00161425050426020b0016061c05041e0b0016140f05020b3f001614580504020b0016140504020b430016141d05041e021500140508020b3f0016140504
|12=>0x1405110804020b2a0014130f0504020b00161405043126020b0016140f0504020b370016062d052c04020b0016140f0e04020b001614341d04020b0016061c05040c0b000605040c0b3600143e0504020b00161405041f02150b2a14390504020b0016145b0504020b0016140504020b010016141c0504260b00161405041e
|13=>0x402156100140504020b100016141c1d041f0b0016142d0504020b2a161405112b04020b00161405045f020b0016145e0504020b0016145c0504020b001614250504020b2a1614340f05040215001614050904024b001614470504020b00161405041e1f0b2a1614251d041f020b00161429210504020b0016140f1d04020b2a
|14=>0xb0d0016060504020b3f001614270504261f020016141c1d04020b2a0014050468020b001606180504020b0d0016141d050422020b0006250504020b0016060504020b6700161405092c0215001665060504020b001425240504020b001614051104021a001614630504020b00160605041e1f0b0016140504020b6200160605
|15=>0x64020b160605040c021a0b0014050908021a0016140f04020b520016060504020b6d0016141d04020b2300161405092b08020b00166b060504020b001614052c020b230016140f0559020b001606051104020b00140f051108020b00160605041f0c0b00140504020b4c2a00142e05041f0b0016140504020b6a0016060f0502
|16=>0x20b00140504020b7500161405090402740016142d0f0508020b00160621050804020b0014050402730b00161405351104020b0016140504020b720016140f0509021a0016141d0504020b2800140509040271001614240504020b001614271d041e0200161405041e640b00166f0504020b0016141805041f0c0b1614180504
|17=>0x330504020b0016066c050402150b001421180804020b0016140504311f020b00161439050804020b001614181d04020b2a061805040c020b00060504020b300016142505041e0b0016142e0504020b010016060504030c020b0014760504020b0016143b05040c020b0016141c0504220c0b0016141805041e1f0b1606050908
|18=>0x5041f0c0b0014050804020b100016140f052b2c020b001614292d0504020b00167b6c0504020b00161429052c04020b001614790504020b001614472e0504020b0016060f052c020b001614340f1d04020b00161405041f020b781614340f052c020b0016143e0f0504020b001614210f1804020b0016140504020b77001606
|19=>0x20b2a1614290504020b00161421051104020b00161421052c020b0016143305040c0b0016062d0f0504020b001642060504020b001614271804021a1614340508020b0016143e340504020b001614052c08020b2a1405110804021a0016140504020b7d001614057c04020b00161405041e0b50001606050904021a0016141d
|20=>0x5110402150b001418050904021a161405043122020b00161421050908020b0016141c1d0402150b0014800504020b0016140504020b7f001614170504020b0016140504020b7e0016666c0504020b0016062705040c020b001425050422020b001606050426020b00161405041e221f0b00161405041e1f15001614251c0504
|21=>0x20b8700161405090402690016140504020b86001614050804020b07001614051904020b2a16140504020b85001614840504020b0016143205040c0b001614340504021a00161418050426020b1614830504020b0016141c05041f0b2a1614241c0504020b0016141c05040b280016141c1d041e0b0016140504020b82001606
|22=>0x1614181d04020b0016140504020b500016145d1d04020b001606340f0504020b0016141c0504030c0b00161405042622020b0016140504260215001606050904021500142505041e1f0b00161405041e3a0b00161418050804020b2a143b2e0504020b0016140f8804020b0016141c0504640b0016141d050403020b00060504
|23=>0x20b001614055904020b0016140f1d04020b00161405110804020b0016140f052c020b001614330504020b001606050904020b001614052c08020b0016060504020b0d00161425180504020b0016140504221f020b0016145d0504020b0016140504020b008916142e05040c020b0016147a0504020b0016141805041e020b00
|24=>0x14050426020b001614880504020b001614211d0504020b00161405110402150b0016140504020b4c0016142d0f0504020b0016140504020b1b0016141c1d04020b0016140504020b8c001614271d04020b0016140504020b8b0016140504020b8a001614050904021a001614050403020b0016140504020b4b0016142705040c
|25=>0x2a001614320504020b0016140504020b74001614052b2c04020b0016141d050904020b00161405041e0c0b0016148d0504020b001614050402710b001614052c0402150b001606052c04020b0016140f0504020b2a001614251c0504020b00161427052c04020b00160605040c020b00142e0504020b001614058104020b0016
|26=>0x20b61001606180504020b0016140504020b230016140504220c020b0016140f0508020b00166e060504020b001614050402150b2a001418050804020b0016060504021a0b00161405090402150016141d05041e020b001614052b04020b2a0016060504020b56001614050804020b2a00140f0504021a0b0016141c0504020b
|27=>0xb00140f1804020b0016140504021a150016140504020b28001614270504021a0016140504020b69001614050422020b0016141d0504020b2a001405092c020b0016140f050402150b0016140e0504020b0016060f0504020b001614340f0504020b00161427050804020b001614180504021a0b163c060504020b0016060504
|28=>0x140504020b001614050904020b0016141d0504020b001614050402150b0016060504020b0016141c0504020b0016140f0504020b001614050804020b001614180504020b0016140504021a0b001614250504020b00161405041e1f0b001666060504020b00160605040215
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x2a7023701c7015700e700770007
|7,0=>0x211820a720281fb71f471ec81e481dd71d581cd81c671be81b681ae81a7719f8197818f8187818071788170816971618159815181498141813a7132812a8122811a8113710b810470fc80f480ec80e570de70d770d070c880c080b880b080a880a08098809170898081807a7072806b7064705c8054804d7046703f703870317
|7,1=>0x3ad83a5839d8395838d8385837d8376736f736873608358835083497341833a7332832a8322831a8312830b730472fd72f672ee82e772e072d882d082c972c272ba82b372ab82a3829b8293828b8283827c7274826d7265825e7257724f8247823f823782307228822172198
|8,0=>0x5bc85b395ab85a3859b8593858b8583857c7573956b8563855b8553854b85429539953185298520951885108508850084f884ef94e784df84d694ce84c684be84b684ae84a6849e8497748f8486947e8476846d9465845c9453944b8443843b8433842a9422841994109408840083f973f093e793df83d693ce83c683be83b59
|8,1=>0x7c387bb87b387ac77a3979c7794878c8784877c8774876b9763875b8752974a8742873a8732872b7722971a8712870a870286fb76f386eb86e386da96d286ca86c286ba86b196a986a1869986909687967f8676966d9664965b9652964a8642863b7634762c8624861c8614860c860485fc85f395eb85e295db75d385cc75c48
|8,2=>0x9d299ca89c379bb89b299ab79a2999a8992898a8982897a89719968995f9957894e9946893d9935892c9924891b99129909990188f988f188e898df98d698cf78c788bf88b788ae98a6889e8895988c9884887d7875886d8864985c8854884b9843883b8833882b8823881b8813880c780487fc87f487ec87e487dc87d487cb9
|8,3=>0xb678b5e9b559b4c9b448b3d7b349b2c8b248b1b9b138b0b8b038afb8af38aeb8ae29ada8ad28aca8ac28aba8ab28aaa8aa28a999a918a898a818a798a718a689a5f9a578a4f8a478a3f8a378a2f8a278a1e9a168a0d9a0589fc99f489eb99e389db8
|9,0=>0xd7b8d738d6b8d629d5a8d528d4a8d419d398d318d289d1f9d178d0f8d069cfd9cf58ced8ce49cdb9cd38ccb8cc38cba9cb28ca99ca09c979c907c888c808c788c708c679c5e9c568c4d9c458c3d8c358c2d8c258c1d8c158c0d8c058bfc9bf48bec8be39bdb8bd38bcb8bc38bbb8bb29ba99ba18b998b909b888b7f9b778b6f8
|9,1=>0xe158e0d8e058dfe7df68dee8de68dde8dd68dce8dc68dbe8db59dad8da58d9c9d939d8b8d838
|10,0=>0xe5c8e548e4c8e457e3d8e358e2d8e258e1d8
|11,0=>0xe647
|_,_=>0
def wAt:=mkWire dB 142 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x5164b015040040859001c4081514164ac152b05ca81100164945b001c450590502450590c0bc08591f0b40009000542c1502164007914164082d1f164945b1f05408011416410590f0bc10151f1640801050041459141642015040b410590c05408591e164145902054082d02164702f0205450591a04410590b00450591416438111816c0015040b41015141642c59
|1=>0x200414011c00414590205400590b16414590f0b4101500164142104004105914164ac2f0800410591d024145914164089d0b0542c590f0041015141640072020540859053189859001e4b45b0f00410152d16c14b104004186b141642c010b1642459141641001040b4102d0504414010b004001100164202f0416400ba1416430152c1641001001c400ba1c1640815
|2=>0x1e42c59020b400591816c001514164ec5b2e00430150216408150516400320216414212b05c200104164141114164200104164e40304384742d05164300114164302d021645059041640859141647c15020045059050841001041642c150215450590b164945b1f05408012516c50591f054080114164302f021641059040545059001643c5904054003d05044180b
|3=>0x4054001514164005904054100105164100100164202d04164605b0602c14011416408590602c1401141645059000c4001502164082d021642c1514164140914164302d021640059052c810010416400311416430150216450592d16c3c0104054147d021640801051647c15020047c2d0200450590b164085902004140105164ac2d2b0bca81100164b45b2c0541001
|4=>0x4164140104274002d0b0547c591f0540801051647c59020041459041541015141642c591e0541459020b408593900c9c21050b40059041a42c010b1641055141642c590200450590c0b408590f004101500164105900164b01504004a45b2b054a81100164b42f2d0b43c01040541459020b408150b16410e11d0b4145914164b45b0f004101505318882d1f1641059
|5=>0x50042c59141641001040b4002114164202d041643c2d0405450590b164945b1f05408010916400590b004102d3b00c14891f16408011816c10150005450590c0b4b82f0c05408592d164b45b0f00410151c16408150f0b4b42f0f0041015050442c59040b414591416408591f05c08011804410590005450590502414592a02400590b054302d0216400592c0bc1001
|6=>0x40041059080b410590b164102d051643cab0405400591816c14011416400590508410592e0b43015021647c2f020045059052247c5902004882f2a02400590f1ac14110b0047c17020045059050247c5902004202d041642c011416414210500410591f054080114164202d04164102d141642001041647c150200414590800410590b0040059040b41059420bc1861
|7=>0x20043017021641015080bc1059041a42c010b164b05904004102d28004302f0216410150005400590415850590b164b017000440059060241401141645059080041059091641411040b420150800410590508810010416414590f0041015250bc7c1502004092d1d0bc14591c0bc1409051640059040b410590021874110516400590f16410150405450590b16414b1
|8=>0xb0042c592e00c7409051647c5900024082d021647c2f02004a809000540059021647c170200414b10400410590f0041015051647001020549c22050b410590b56418171416408010c05408590205450590b1642d410c05c08590c0b40815021641015000545059052c810011416414010f0b410151c2ac0815001640859050b41459021647c2d0200409491505c2c59
|9=>0x20042c590016410e11d0b4145905284302f02164b82f1d0241459001e40815020b4147e00024082d1c1647001020547c2f000540801052b8b0590400450590b0042c59051e40009020b450590c0bc08590504414010b00518591f0bc08011f0b47c1502004505902054082d2c0bc10010405415652c16c1001250bc7c1502004082d0b16414592c0bc1001041640059
|10=>0x8004105902604a82f0016574590f00c10155d0b43c030405470010205400590b1643c2d04054742f040b414591c15408150b164005900024082d1f054080105164741105164145904054005900164202d04164b45b0f0041015261640079020b4b42f0f0041015052c410011416410151816c0015051641425040b4505902054085902164180b14164641509004102d
|11=>0x1f15c08010b16418130405450592c0bc1001141642c151f0b408010516408150016409a51500c2c590604c00151416414592a0240059180241401141659817060b45059040b410010b165985b060b450592516c7c150200410550b0042c59640547c5b02004505900024082d1b004702f02054182f141642c592b05ca81100164145902054080118044001500164202d
|12=>0x2164102d2a0b400592516c7c150200414590b054082d1f16c0009020b451c11d04c14590002400150216400151f16c080114164002d0216410590b004102d0405454170b165b8170600450590f0bc141105164102d0800410596c0541803141643c2f0400410152c16c1001040541055141642c5905044202d041640859020045059001641422041647059020540801
|13=>0x220b47c59020049c21050b41059001641401051640859050045059061ac2c0114164147d00024082d2e0bc74090516450590c0b408593a054003202164b8010c0540859000c4081502164140100024082d041645059040b44417080b41059180bc1401040b410590f0041015141641421041642d31050881059080b4105918088140104164002d05044102d05164302f
|14=>0x5038302d0216411d1180bc0015020b43017021642c0114164102d02164080105164ac170800410592c1641001040543c010405418150600c50592c1d4100105165e82d0f16c10151d02414590504410011416414590f0b4101500024a817001643c2d0400410152d0b43c010405400150f1641015230043c2f0405450591e054082d0600c50590b1641421050041059
|15=>0x5164f4592c05c10010e044605b00054149a001e4082d060b418031416408590b0545059051f47c5902004007914164082d1f1640009020b42c5900024082d1c004081500164b07504004145905084202d0416414210400410591c0b408150216450590f0041015061841401141641401050b42c0127044142d0416400d105094102d001641001041642c01080b41059
|16=>0x618c14011416454030b164102d50004301702164ac2f080041059001642401040b4fc592c0bc100181024740305164007202054085904274002d0b0541401001e4082d3416c1425040b408010205400592516c700102054302f020540859051640815020b468220b00410591416410550b16414010b004102d2a024005908054102d041641459020542c59810447403
|17=>0x1e054082d14164102d0400410590604c50591802414011f16408010f00c10152a02c00590c05408590f16c101500054082d0500414590c05c0859051643c03040543c2d0405450590c0b40815021647c2d1f1640801021a42c010b164102d141642c59051f40009020b43003020b408590416400150016474090516414a90405400591f16c08150200408550b1641459
|18=>0x40b41459020b40859051a42c012a0b40059040042c590400450590405400591c0040815000442c151416408591d02414591d00c1459001e4082d1d00414591d0441459041542c590508810590f00410151c0bc0815050241459021582c59050b414591802c14011d02c14590b004102d0c0b408591d0bc14590b05408592c16c1001050441459080b41059040041015
|19=>0xc0bc0859050b42c011500c2c592a024005900164145904004102d040542c591816c14010405450590f0b41015050b41059050042c01060445059060bc50590500450590f0bc1015000c408590504410590600450590b16400590500410590b00450590b164102d020b414592a04400590605c5059041640059050442c010205400591c00c0815180bc14012c1641001
|20=>0x102d051642c59141640815040541059050042c011f054080100024082d060b45059141642c590500410150b0042c59
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x1aa834506790cb418e830d06018bc417262d5058a0ad41528000052a0a1413e426d04ba09341206234c44a0863106620483f180000f481d9039206e40d841a1033106240be6170c2c985540a28135024a0463088410101e9839406a80c8c17200000548099011201e4034805900a10104018802100220004
|7,1=>0xcba1943324463ccc5a188330c46090bf997b42ee85cd0b8196c42d085910b0215c400005688ab2152429c85290a32143327e84ed09ba134326084b109499254244647908d99174226843d085a10832088404c7ea0f941ea83c5076a0e941ca838506ea0d94
|8,0=>0x4ac694cd281a4d3494691cd221a41347c68ecd1c1a35346468bcd161a2a244e6890d109a1e34366860d0a9a12341e6830d049a0634066800cfe99fa33ee67d0cf899ee33d667a0cf299e233be6770cec99d633a66740ce699ca338e6710ce099be337846e4cdb19b3336066b4cd519a733486684ccf199b3
|8,1=>0x62a6c48d879b0c36126c18d819b0035fa6be8d7b9af435e26bb8d759ae835ca6b88d6f9adc35b26b58d699ad0359a6b28d639ac435826af8d5d9ab8356a6ac8d579aac35526a98d519aa1253c6a6cd4c1a9535246a3cd461a89350c6a0cd401a7d34f469dcd3a1a7134dc69acd341a6534c4697cd2e1a593
|8,2=>0x7a46f3cde61bc9378c6f0cde01bbd37746edcdda1bb1375c6eacdd493a637466e80dcf139b37306e54dc91b8f37186e24dc31b8337006df4dbd1b7736e86dc4db71b6b36d06d94db11b5f36b86d64dab1b5336a06d34da51b48268a6d08d9f9b3c36726cd8d999b30365a6ca8d939b2436426c78d8d9b183
|8,3=>0x46338c07174e2d1c5738a87144e271c4b38925118e219c40387a70e8e1b9c34386270b8e159c28384a7088e0f9c1c38327058e099c10381a7028e04140538046ffcdfe1bf937ec6fccdf81bed37d46f9cdf21be137bc6f6cdec1bd53
|9,0=>0x9c85388a7014de29b85368a6c14d629a85348a6814ce29985328a6414c629885308a6014be297852e8a5c14b6296852c8a5814ae295852a8a5414a629485288a50149e29385268a4c149629285248a48148e29185228a44148629085208a40147e28f851e8a3c147628e851c8a38146e28d851a8a3414662
|9,1=>0x1428a8415062a085408a8014fe29f853e8a7c14f629e853c8a7814ee29d853a8a7414e62
|10,0=>0x5141a2634486888d101a1e34386868d0c1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 15
def pmP:Nat→Nat
|0=>0x80000000000001cc150000000007e0a8000000001c084000000000e00a000000000200040000000004faa000000000240000000000010500000000000808000000000040020000000002000000000000096080000000003f00000000000140000000000007d000000000003420000000000101000000000005300000000000200000000000005d00000000000288000000000012000000000000840000000000040000000000000f80000000000048000000000001000000000000048000000000001000000000000020000000000000
|1=>0x22a82a80000000d4c15400000006265aa0000000313075000000018982a80000000c0cb5c00000006024be000000021401000000000e906880000000708b54000000032698000000001932f500000000c987a80000000648bd40000000320160000000018705500000000c196a8000000060100000000002365aa00000001132d5000000008596a8000000040cb7400000002065ae00000001032d500000000813ea80000000408b5c00000002045aa0000000102080000000008100800000000405b4800000002008000000000100001
|2=>0x88196a80000004408b5400000022025f600000011012f100000008803ea80000004401000000000220055400000011002a2000000088001f00000004400000000000200057400000010002b2000000080004100000002418b5400000012084aa000000080f000000000040080000000002000200000000100000000000007c32d500000003e182a80000001f041140000000d861aa00000006330d400000002af82a8000000147cb540000000a3e0aa000000051c014000000028996a8000000144cb140000000a06faa00000004c5021
|3=>0x808196a80000040000014000001920e5aa000000a826ad5000000488396a80000024414954000001120e5aa00000089062d5000000438193a8000002170c3d40000010a0e4ea00000085032f5000000418197a80000020908000000001038e0ea000000814b2d5000000408316a80000020408bd400000100900080000008001018000000288196a80000014005f540000008606faa00000043032d50000002081bea8000001040cb54000000800810400000031022ff000000181292a00000004c0001000000022065ba00000011032d7
|4=>0x8008000000000400201250000011920e5aa00000889072d5000004248396a8000020260835400001002004200000080010010000004000014800000200000a100000100000124000008000008600000400000020000018200020000000c100000200000600252c600000280819ea8000014000061000000a00002080000050000101000002280096a8000011040481c000008800060000000381032dd000001c00080c0000008040cb5c00000402065aa0000020025257000001000014200000080000870000003040240000000111032d5
|5=>0x10008020000000800014b140000301a0618a00001809070c500000c00098280000060004434000003000000200000104d030c5000008230104a000004108000500000201a0e58a00001005032d500000802819628000040120db540000200806baa00001004032d500000801018ea80000400709b540000200306daa00001001834d100000800c1a200000040060c3440000200304920000010018248000000800c1208000004006053000000200300900000010018041000000800c00000000040040d34400002002065aa0000100102490
|6=>0x20000136a8000100000900000008000040400000400000400000020000011400001000000220000080000001200002c01022d7000014108116b80000a00400248000050020010c00002411032d5000012088016a8000090241cb5400004806065aa00002401032d7000012008116a80000900400bc400004800005e400002042012d50000101880a680000080848cb540000402204daa00002011016d1000010088034800000804401a000000402200c20000020110049000001000829628000080040cb5400004002025a60000200100690
|7=>0x2800c13ea8000140044d3540000a002261ea00005000114600000244481bfa8000122240cbd400009022065aa00004811016d100002408809788000120240cb5c00009012045aa00004801832d500002400c18780000120040dbd400009002045aa00004801016f50000240080b690000102440cbd400008122045ee00004081c32f50000204081bfa8000102040cbd400008102045ea00004011037d50000200081bea8000100040db5c00008002065ba00004001027d5000020008136a80001000408bd400008002044ea0000400100008
|8=>0x200000296180010000010a180006000066188000240000008000010c02899628000860044cb5400043002261a200021801130d000010c008916a80008600440240000430022010800021001130d500010800898688000840041c31400042002065aa00020001132d5000100008196a8000800040804000040000001080002000000001000060408116a80003004005b5c00014842065aa0000a421022d5000050188096a8000200c40cb540001002202daa00006c09032d7000034080083000001a02408b5c0000b003061aa00005001830f5
|9=>0x201008292b80010080410058000804000850c0004019301275000200a90096a80010044c08b5400080226024aa0004011300204000200890014200010044800250000801524f5aa000400a9062d7000200480283a8001002241cb54000801120c5ae0004008107275000200408316a8001002040cbd4000800a4027aa00040050032d50002002800aaa8001001048cb5400080082065ae00040041032d500020020021430001001000df54000800404e4a80004001300214000200090010200010004000010000800040040800040001022d5
|10=>0xc0000e996a80060000448b54002100024000200100005e32d500080000000008002840004c34000120000665aa00081045232d500040802908620002040048cb5400100102ce5aa00080045270c000040003f196a80020001d8c1400010000a3c5aa00080000d20d0000400005382a0001200848cb5c00090042465aa00042801032d7000212208096280010910404904000848424218800042401072d5000212008196a8001021241cb54000810800208600040809012d700020200139620001008809cb5c000804020c5ae00040201052c7
|11=>0x40000509396a810080024240100804001012008040200010200402000826838628100041140cb540800208a0010804001044430d50200082201aea8100000040cb540800000004028022800210329500e840000116a801c201040c21400d001504e5aa00680061232950034003010840801a000848cb5400d000424652a00680021032d5002840009114a8014200040cb5400a100020652a0040002122ad50018000000008000a000840da54004100020042200184001136d5000c0802919628006040060db5400302002265aa00181001032d5
|12=>0x802840009116aa012000040804080e1000244d2220508001232950c0000649396a8600002249cb5430000082465aa10780000122d5080400209996a84020000cccb5410c10022004aa08608001022d5
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0xca0a0113928a301516bb43044853f1f0a84034d90001cfd33ad32d74385f4b446b942128194a36070b4c700a3080070985215038f056ce982406d9a0910a983f547e24442b8088546a034a93c410d6e290161d170623b222980ab64d55988a893015483f5001158ad6f484ad1416020057ea56c8603c005b55e18635d8180e3fa7d242525
|8,0=>0xba22da7429f584443350e0594b7799becb18b15a6917354d01436317dc451006420de261402b248e1382f54eda7bcf5817e07b14b73cafe111ebc440b05178580915e99c3926b26a88dd6b8cc678a0eac34e85e37128cc4d908d540a6da31aa8b48f05844dc6c3cbc94a2839a5d3220f83e33b14d79f83582c607388614415162fec443cc0be192a9caacdd8797ec116
|8,1=>0x5c91912f97b9aa7884ef8e3c15445b34be2096a5b08dc379dddcff01500f8ec299a49afa57389b99e27bb5cb050eac4556aa872a08ba4b63620d339474124e2b7190e54fd4bb59c1896da00db079c26a6c892c97ea7702a14102fbb25c16405a88b1bd1658d390adf621910c9214cb07746141dd670b7f28b072928dacf4d5
|9,0=>0x2b5696ac33a0fa2c341be34faa39ec4f069d0e8cf68b739cbf173062d38e6c2cc8e902b63d8d6f41b38db12e219a536d284be55cd1af0d0dd7a793b66229648bdd87839b91d328233887acf77505a84ca6b4300ff8b97dea322f905d62c
|10,0=>0x120751e44a362f099ce66
|11,0=>0x25
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 53 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_219 10 roots_219 ops++addP pm 1 dom_115 6 roots_115 ops++addP pm 2 dom_250 9 roots_250 ops++addP pm 3 dom_99 4 roots_99 ops++addP pm 4 dom_235 9 roots_235 ops++addP pm 5 dom_107 6 roots_107 ops++addP pm 6 dom_241 8 roots_241 ops++addP pm 7 dom_187 9 roots_187 ops++addP pm 8 dom_170 5 roots_170 ops++addP pm 9 dom_243 9 roots_243 ops++addP pm 10 dom_171 6 roots_171 ops++addP pm 11 dom_211 8 roots_211 ops++addP pm 12 dom_42 4 roots_42 ops++addP pm 13 dom_249 9 roots_249 ops++addP pm 14 dom_122 6 roots_122 ops++addP pm 15 dom_120 4 roots_120 ops++addP pm 16 dom_121 6 roots_121 ops++addP pm 17 dzo_218_32 6 roots_218 ops++addP pm 18 dom_232 5 roots_232 ops++addP pm 19 dom_233 6 roots_233 ops++addP pm 20 dom_123 9 roots_123 ops++addP pm 21 dom_234 7 roots_234 ops++addP pm 22 dom_248 7 roots_248 ops++addP pm 23 dom_58 5 roots_58 ops++addP pm 24 dom_227 6 roots_227 ops++addP pm 25 dom_83 5 roots_83 ops++addP pm 26 dom_186 7 roots_186 ops++addP pm 27 dom_106 5 roots_106 ops++addP pm 28 dom_226 4 roots_226 ops++addP pm 29 dom_114 4 roots_114 ops++addP pm 30 dom_178 5 roots_178 ops++addP pm 31 dom_59 6 roots_59 ops++addP pm 32 dom_185 6 roots_185 ops++addP pm 33 dom_179 6 roots_179 ops++addP pm 34 dom_43 5 roots_43 ops++addP pm 35 dzo_211_32 6 roots_211 ops++addP pm 36 dom_216 5 roots_216 ops++addP pm 37 dom_57 4 roots_57 ops++addP pm 38 dom_242 7 roots_242 ops++addP pm 39 dom_89 5 roots_89 ops++addP pm 40 dzo_217_32 6 roots_217 ops++addP pm 41 dom_91 6 roots_91 ops++addP pm 42 dzo_219_32 7 roots_219 ops++addP pm 43 dom_202 5 roots_202 ops++addP pm 44 dom_218 6 roots_218 ops++addP pm 45 dom_75 4 roots_75 ops++addP pm 46 dom_184 4 roots_184 ops++addP pm 47 dzo_210_32 5 roots_210 ops++addP pm 48 dzo_216_32 5 roots_216 ops++addP pm 49 dom_139 5 roots_139 ops++addP pm 50 dom_203 7 roots_203 ops++addP pm 51 dom_217 8 roots_217 ops++addP pm 52 dom_155 7 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_218_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_211_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_217_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_219_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_210_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_zo_216_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h52;exact cpcs (by decide +kernel) lowS_155 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_219 10 s (0,roots_219.map (·&&&dom_219)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_219 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 118 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 118 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 241 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 113 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 241 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 83 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 83 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 9 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_251 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_239:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 12:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_191
def isoMvS_253:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_247
def isoMvS_254:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_251
namespace S_255
def pG:List (Nat×Nat):=[(1,5),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,34),(2,130),(3,7),(3,11),(3,19),(3,35),(3,67),(3,131),(4,5),(4,20),(4,36),(4,68),(4,132),(6,7),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(8,136),(9,11),(9,13),(9,25),(9,41),(9,73),(9,137),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,36),(32,40),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffff
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
|0=>0xff00
|_=>0
def pmB:Nat→Nat→Nat
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_191 12 roots_191 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_239 12 roots_239 ops++addP pm 6 dom_223 12 roots_223 ops++addP pm 7 dom_127 12 roots_127 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_127 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [2, 0] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.or, inputs := [3, 8] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [10, 1] }, { op := GateOp.and, inputs := [2, 0] }, { op := GateOp.and, inputs := [9, 12] }, { op := GateOp.and, inputs := [11, 13] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52946_aux

theorem PEqualNP.Outside.L_meta_52946 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52946_aux.main
