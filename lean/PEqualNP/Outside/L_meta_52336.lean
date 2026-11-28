import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52336_aux
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

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeeeeeeeaa00aa00eeeeeeeeaa00aa00eeeeeeeeaa00aa00eeeeeeeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_49 : Nat := 0x3000300030003
def goal_49 : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000
def roots_49 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_50 : Nat := 0x5000500050005
def goal_50 : Nat := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def roots_50 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffffaaaaaaaaaa00ffffaaaaaaaaaa00ffffaaaaaaaaaa00ffffaaaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfafafafafafafafaaa00aa00aa00aa00fafafafafafafafaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafaaaaa0000aaaa0000fffffafafffffafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffff0f0fffff0f0cccc0000cccc0000fffff0f0fffff0f0cccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffafafffffafaeeee0000eeee0000fffffafafffffafaeeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffaaaaffffaaaaeeeeaa00eeeeaa00ffffaaaaffffaaaaeeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffafafffffafaaaaaaa00aaaaaa00fffffafafffffafaaaaaaa00aaaaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffafafffffafaeeeeaa00eeeeaa00fffffafafffffafaeeeeaa00eeeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_97 : Nat := 0x3000000030000000300000003
def goal_97 : Nat := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfffffffff0f0f0f0cccccccc00000000fffffffff0f0f0f0cccccccc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfffffffffafafafaeeeeeeee00000000fffffffffafafafaeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffffffffaaaaaaaaeeeeeeeeaa00aa00ffffffffaaaaaaaaeeeeeeeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffffffffafafafaaaaaaaaaaa00aa00fffffffffafafafaaaaaaaaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffffffffafafafaeeeeeeeeaa00aa00fffffffffafafafaeeeeeeeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_112 : Nat := 0x10001000100010001000100010001
def goal_112 : Nat := 0xffffffffffff0000ffff000000000000ffffffffffff0000ffff000000000000
def roots_112 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffffffffffaaaaffffaaaaaaaa0000ffffffffffffaaaaffffaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffffffffff0000ffffcccccccc0000ffffffffffff0000ffffcccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffffffffffaaaaffffeeeeeeee0000ffffffffffffaaaaffffeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffffffffffff0f0ffff000000000000fffffffffffff0f0ffff000000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffffffffffafaffffaaaaaaaa0000fffffffffffffafaffffaaaaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffffffffff0f0ffffcccccccc0000fffffffffffff0f0ffffcccccccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffffffffffafaffffeeeeeeee0000fffffffffffffafaffffeeeeeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffffffffaaaaffffaaaaaaaaaa00ffffffffffffaaaaffffaaaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffffffffaaaaffffeeeeeeeeaa00ffffffffffffaaaaffffeeeeeeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffffffffafaffffaaaaaaaaaa00fffffffffffffafaffffaaaaaaaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffffffffafaffffeeeeeeeeaa00fffffffffffffafaffffeeeeeeeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefeeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffccccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeeeeeeeeeaa00aa00eeeeeeeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffccccccccc00000000cccccccc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffccccffffcccccccc0000ffffcccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeeeee0000ffffeeeeeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaffffaaaaaaaaaa00ffffaaaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffccffffcccccccc0000ffffcccccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffeeffffffffffffffeeffffeeeeeeeeaa00ffffeeeeeeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0ffff000000000000ffff000000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcffffcccccccc0000ffffcccccccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffefffffffffffffffeffffeeeeeeeeaa00ffffeeeeeeeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffafafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcf0f0f0f0f0f0f0f00000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffefafafafafafafafaaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffff0000ffff0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffaaaaffffaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffff0f0fffff0f0cccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffafafffffafaeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffaaaaffffaaaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffff0000ffff0000cccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffffaaaaffffaaaaeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffff0f0fffff0f00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffafffffafafffffafaaaaaaa00aaaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffff0f0fffff0f0cccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffefffffffefffffafafffffafaeeeeaa00eeeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffccccccccffffffff00000000cccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffff0f0f0f0cccccccc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffffffff00000000cccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffffffff0f0f0f00000000000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfffffffff0f0f0f0cccccccc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffefffefffffffffafafafaeeeeeeeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffffffffff0000ffffcccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffffffffffaaaaffffeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0ffff000000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffffffffff0f0ffffcccccccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffffffffffafaffffeeeeeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffffffffffff0000ffff000000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffffffffffffaaaaffffaaaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffffffffff0000ffffcccccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffeeffffffffffffaaaaffffeeeeeeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffffffffffff0f0ffff000000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffffffffffffafaffffaaaaaaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffffcfffffffffffff0f0ffffcccccccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffefffffffffffffafaffffeeeeeeeeaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_49
def pG:List (Nat×Nat):=[(1,17),(1,33),(16,17),(16,48),(32,33),(32,48)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3f
def xsM:=roots_49.map (·&&&dom_49)
def gM:=goal_49&&&dom_49
def NN:Nat→Nat
|2=>1
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0x9035d
|3,0=>0x9035d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x3000300000000c0000000c0002000200020002
|_,_=>0
def sP:Nat→Nat
|0=>0x924
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wAt:=mkWire dB 3 50 0x3ffffffffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_49 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_49 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_49==dom_49)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_49 gM v ys):RunD true dom_49 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_49 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_49 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_49 gM s xsM):False:=by
  have hmin:2≤s:=by have hl:=run_len h;change 3≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_49 roots_49 goal_49 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_49
theorem lowS_49:Lower true dom_49 roots_49 goal_49 4:=S_49.noCircuit
def isoMvS_50:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_50:Lower true dom_50 roots_50 goal_50 4:=lower_iso_b isoMvS_50 (by decide +kernel) lowS_49
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_49
def isoMvS_97:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_97:Lower true dom_97 roots_97 goal_97 4:=lower_iso_b isoMvS_97 (by decide +kernel) lowS_49
def isoMvS_112:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_112:Lower true dom_112 roots_112 goal_112 4:=lower_iso_b isoMvS_112 (by decide +kernel) lowS_49
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_49
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
theorem lowS_51:Lower true dom_51 roots_51 goal_51 5:=lower_slice_b [(0xa000a000a000a,16,17)] (by decide +kernel) lowS_50
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_slice_b [(0x300030003000300,1,9)] (by decide +kernel) lowS_49
namespace S_113
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(16,17),(16,48),(16,80),(32,33),(32,48),(32,96),(64,65),(64,80),(64,96)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_113.map (·&&&dom_113)
def gM:=goal_113&&&dom_113
def NN:Nat→Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3038a2a5ec23a7c
|4,0=>0x3108e2ea67282dc21e4c1a11819e2b12752
|5,0=>0xd931d8123f06abc
|6,0=>0xd931d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc000800000000000c000b0003000300020003000300030002c000c000c000c000c000c000000000003000000030000000300000000c000c000c0000000c000c000c000100010001000100010001000100008000800080008000800080008000b0002000300020003000200030002c000c000c000c000c0000000c00030003000300030002000200020002c000c00000000000c000c000000030000000300000003000000030000800080008000800080008000800030003000300030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x327032703247093270327d0c32709b270b3247327a09367093570328036543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def wAt:=mkWire dB 14 114 0x3ffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x7048d234c1305c1274c92048d07409
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x200
|4,0=>0x8262004222
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfca7530
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>8
|4,0=>0x4415
|5,0=>0xf6
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_112 4 roots_112 ops++addP pm 1 dom_97 4 roots_97 ops++addP pm 2 dom_81 4 roots_81 ops++addP pm 3 dom_49 4 roots_49 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_113 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_112 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_97 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_49 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_112 4 s (0,roots_112.map (·&&&dom_112)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_113 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_112 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_113==dom_113)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_113 gM v ys):RunD true dom_113 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_113 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_113 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_113 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_113 roots_113 goal_113 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_113
theorem lowS_113:Lower true dom_113 roots_113 goal_113 7:=S_113.noCircuit
def isoMvS_43:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_43:Lower true dom_43 roots_43 goal_43 4:=lower_iso_b isoMvS_43 (by decide +kernel) lowS_27
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 4:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_27
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_57
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 4:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_27
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_27
def isoMvS_114:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 5:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_51
def isoMvS_116:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_57
def isoMvS_139:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_139:Lower true dom_139 roots_139 goal_139 5:=lower_iso_b isoMvS_139 (by decide +kernel) lowS_57
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_57
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_51
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_57
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_57
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_51
def isoMvS_154:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_154:Lower true dom_154 roots_154 goal_154 5:=lower_iso_b isoMvS_154 (by decide +kernel) lowS_57
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_51
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 7:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_113
def isoMvS_195:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 4:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_27
def isoMvS_198:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_198:Lower true dom_198 roots_198 goal_198 4:=lower_iso_b isoMvS_198 (by decide +kernel) lowS_27
def isoMvS_201:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_57
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 4:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_27
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_51
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_57
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_27
def isoMvS_226:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 5:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_57
def dzo_51_8:=0xf000f000f000f00
def gzo_51_8:=0xf000e000e000a00
def gsh_51_8:=0xf000e000e000a
theorem lowS_zo_51_8_50:Lower true dzo_51_8 roots_51 gzo_51_8 5:=lower_iso_b (d1:=dom_51) (r1:=roots_51) (T1:=gsh_51_8) [(dom_51,8)] (by decide +kernel) (lower_slice_b (T:=gsh_51_8) [(0xa000a000a000a,0,1)] (by decide +kernel) lowS_50)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(10,11),(10,26),(10,42),(16,17),(16,18),(16,48),(24,25),(24,26),(24,56),(32,33),(32,34),(32,48),(40,41),(40,42),(40,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x7c3b0
|5,0=>0xbc850
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0000c0c0c0c0c0c0c0cf0f0f0f00000000f0f00000f0f0000f000f000f000f00a0a0a0a0a0a0a0a303030303030000
|_,_=>0
def sP:Nat→Nat
|0=>0x8d53a354c688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x8d
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
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dzo_51_8 5 roots_51 ops++addP pm 2 dom_51 5 roots_51 ops++addP pm 3 dom_43 4 roots_43 ops++addP pm 4 dom_50 4 roots_50 ops++addP pm 5 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_51_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_59 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_59 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_59 roots_59 goal_59 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_59
theorem lowS_59:Lower true dom_59 roots_59 goal_59 7:=S_59.noCircuit
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xcc00cc0000000000cc00cc,16,18)] (by decide +kernel) lowS_85
theorem lowS_115:Lower true dom_115 roots_115 goal_115 8:=lower_slice_b [(0xc000c000c000c000c000c000c000c,16,18)] (by decide +kernel) lowS_113
theorem lowS_117:Lower true dom_117 roots_117 goal_117 8:=lower_slice_b [(0x300030003000300030003000300030,64,68)] (by decide +kernel) lowS_113
theorem lowS_143:Lower true dom_143 roots_143 goal_143 6:=lower_slice_b [(0xcccc0000000000000000000000000000cccc,128,130)] (by decide +kernel) lowS_141
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,16,17)] (by decide +kernel) lowS_150
namespace S_155
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,18),(2,130),(3,11),(3,19),(3,131),(8,9),(8,136),(10,11),(10,26),(10,138),(16,17),(16,18),(16,144),(24,25),(24,26),(24,152),(128,129),(128,130),(128,136),(128,144)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_179:Lower true dom_179 roots_179 goal_179 8:=lower_slice_b [(0xa000a000a000a0000000000000000000a000a000a000a,16,17)] (by decide +kernel) lowS_178
theorem lowS_199:Lower true dom_199 roots_199 goal_199 5:=lower_slice_b [(0xaa00000000000000aa00000000000000aa00000000000000aa,64,65)] (by decide +kernel) lowS_198
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_slice_b [(0x3030000000000000303000000000000030300000000000003030,64,68)] (by decide +kernel) lowS_201
theorem lowS_206:Lower true dom_206 roots_206 goal_206 5:=lower_slice_b [(0x4444000000000000444400000000000044440000000000004444,128,130)] (by decide +kernel) lowS_204
theorem lowS_213:Lower true dom_213 roots_213 goal_213 6:=lower_slice_b [(0x300030000000000030003000000000003000300000000000300030,64,68)] (by decide +kernel) lowS_209
def isoMvS_91:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_87
def isoMvS_93:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_93:Lower true dom_93 roots_93 goal_93 6:=lower_iso_b isoMvS_93 (by decide +kernel) lowS_87
def isoMvS_103:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 6:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_87
def isoMvS_107:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 6:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_87
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_87
def isoMvS_118:List (Nat×Nat):=[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 8:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_117
def isoMvS_157:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_151
def isoMvS_158:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_158:Lower true dom_158 roots_158 goal_158 6:=lower_iso_b isoMvS_158 (by decide +kernel) lowS_143
def isoMvS_171:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 7:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_155
def isoMvS_174:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_143
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_115
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 8:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_117
def isoMvS_188:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_188:Lower true dom_188 roots_188 goal_188 6:=lower_iso_b isoMvS_188 (by decide +kernel) lowS_143
def isoMvS_203:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_87
def isoMvS_211:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_155
def isoMvS_214:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_205
def isoMvS_217:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_155
def isoMvS_218:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 6:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_87
def isoMvS_220:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 5:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_199
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_155
def isoMvS_230:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_205
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_87
def isoMvS_236:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 5:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_199
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 8:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_179
def isoMvS_242:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 8:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_115
def isoMvS_244:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 6:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_213
def isoMvS_248:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_59
def dzo_77_2:=0xcccc000000000000cccc
def gzo_77_2:=0xc8c80000000000008800
def gsh_77_2:=0x32320000000000002200
theorem lowS_zo_77_2_77:Lower true dzo_77_2 roots_77 gzo_77_2 4:=lower_iso_b (d1:=dom_77) (r1:=roots_77) (T1:=gsh_77_2) [(dom_77,2)] (by decide +kernel) (lower_slice_b (T:=gsh_77_2) [] (by decide +kernel) lowS_77)
def dzo_27_4:=0xf0f0f0f0
def gzo_27_4:=0xe0e0a000
def gsh_27_4:=0xe0e0a00
theorem lowS_zo_27_4_27:Lower true dzo_27_4 roots_27 gzo_27_4 4:=lower_iso_b (d1:=dom_27) (r1:=roots_27) (T1:=gsh_27_4) [(dom_27,4)] (by decide +kernel) (lower_slice_b (T:=gsh_27_4) [] (by decide +kernel) lowS_27)
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccc8c800000000cccc8800
def gsh_93_2:=0x333332320000000033332200
theorem lowS_zo_93_2_77:Lower true dzo_93_2 roots_93 gzo_93_2 5:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x333300000000000033330000,0,16)] (by decide +kernel) lowS_77)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0f000000000e0e0a000
def gsh_91_4:=0xf0f0f0f000000000e0e0a00
theorem lowS_zo_91_4_27:Lower true dzo_91_4 roots_91 gzo_91_4 5:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [(0xf0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_27)
namespace S_95
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(3,11),(3,19),(3,67),(4,68),(5,13),(5,21),(5,69),(6,22),(6,70),(7,15),(7,23),(7,71),(8,9),(10,11),(10,26),(12,13),(12,76),(14,15),(14,30),(14,78),(16,17),(16,18),(16,80),(20,21),(20,22),(20,84),(24,25),(24,26),(24,88),(28,29),(28,30),(28,92),(64,65),(64,68),(64,80),(66,67),(66,70),(66,82),(72,73),(72,76),(72,88),(74,75),(74,78),(74,90)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffff
def xsM:=roots_95.map (·&&&dom_95)
def gM:=goal_95&&&dom_95
def NN:Nat→Nat
|4=>2
|5=>5
|6=>3
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb711c164e2
|5,0=>0x3ea0233471152e6106140b2c9
|6,0=>0x510b62bb092a996
|7,0=>0xc3264
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ccccccccffffffff00000000ffff000000aa00aa0000000000aa00aa555555550000000044444444afafafaf00000000aaaaaaaaffffff0000000000ffffff000f0f0f0f0000000000000000ffffffff00000000ffffff00f0f0f0f000000000f0f0f0f0cccccccc00000000ccccccccaaaaaaaa00000000aaaaaa00ffff000000000000ffff0000ff00ff0000000000ff00ff00aaaaaaaa00000000aaaaaaaa3f3f0f0f0000000033330000ffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x437620436209437f20e437620462d094372c0436b20a462098476204765043210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2a805
|5,0=>0x22638c598830a6
|6,0=>0xd597b287
|7,0=>0x3b6
|_,_=>0
def wAt:=mkWire dB 16 96 0xffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c260501
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x21441
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 6
def pmP:Nat→Nat
|0=>0x2755c4ff0fc00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xd1
|7,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 6 roots_93 ops++addP pm 1 dzo_77_2 4 roots_77 ops++addP pm 2 dom_77 4 roots_77 ops++addP pm 3 dzo_27_4 4 roots_27 ops++addP pm 4 dom_91 6 roots_91 ops++addP pm 5 dom_87 6 roots_87 ops++addP pm 6 dom_27 4 roots_27 ops++addP pm 7 dzo_93_2 5 roots_93 ops++addP pm 8 dzo_91_4 5 roots_91 ops++addP pm 9 dom_86 4 roots_86 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_95 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_77_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_91_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_93 6 s (0,roots_93.map (·&&&dom_93)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_95 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_93 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_95==dom_95)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_95 gM v ys):RunD true dom_95 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_95 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_95 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_95 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_95 roots_95 goal_95 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_95
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=S_95.noCircuit
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=lower_slice_b [(0x30303030303030303030303030303030,64,68)] (by decide +kernel) lowS_121
def dzo_155_4:=0xf0f0f0f0000000000000000000000000f0f0f0f0
def gzo_155_4:=0xf0f0f0f0000000000000000000000000e0e0a000
def gsh_155_4:=0xf0f0f0f0000000000000000000000000e0e0a00
theorem lowS_zo_155_4_27:Lower true dzo_155_4 roots_155 gzo_155_4 5:=lower_iso_b (d1:=dom_155) (r1:=roots_155) (T1:=gsh_155_4) [(dom_155,4)] (by decide +kernel) (lower_slice_b (T:=gsh_155_4) [(0xf0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
namespace S_159
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,129),(2,18),(2,130),(3,11),(3,19),(3,131),(4,132),(5,13),(5,21),(5,133),(6,22),(6,134),(7,15),(7,23),(7,135),(8,9),(8,136),(10,11),(10,26),(10,138),(12,13),(12,140),(14,15),(14,30),(14,142),(16,17),(16,18),(16,144),(20,21),(20,22),(20,148),(24,25),(24,26),(24,152),(28,29),(28,30),(28,156),(128,129),(128,130),(128,132),(128,136),(128,144)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_159.map (·&&&dom_159)
def gM:=goal_159&&&dom_159
def NN:Nat→Nat
|3=>10
|4=>54
|5=>113
|6=>61
|7=>11
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xb417e8c4fd866fe806c0675085126a507ae3b8d519f0e044c6
|4,0=>0xee449dc156ca80abe12fbbca7b4c6db23c2b2210ae9faac5dfa75da9ed459c225924618903a84c1184146831688055575d3f705f25e2ee53cf351bc050bed5090b4f0a74c8114b29f46d0c46bfe466d744a453e7a93b5863ad5d3a26d38da8382b83279525a682244f20bde1ca8e1b893165ea15afa1395a12e6a1098a0a7ad07b1d05c0b00dab
|5,0=>0xfe7d1f9432e75ffe517ce49f3dd0adcfcccc4e4ac435abb11fb2b6bafc4ca8bf7a7f30a4bb8a46e19dabe9b26899544918f69179a8f6d28bc3e89f0f86f3881f8880c747e3797db4b7bdd87ac7a7281d6f4376c98f6c46a655c162dbf628b2626376213961fb461cd75ea7b5e2b55d7c55ae3f5a27457ceb5711b562c3550415401f52ab14f5e04e40e4aefc491444758f47252447b9443f34372142599415c5411c5408373d22c3ab4f3a0ba3a05f38986384e934b3d2e6f12a4192962725cd72459f227db227be2272520b7a208d81dea11dd451dbf71d5111bf9e1b9581b8b5169871689c14a4f1490411f9311e131157010fbc0e1e00cd540b9080b0310a3c208732083830656c05d7005618055ee055be04d6a00a5e00612
|6,0=>0xf6268ec7bfe2c58e1ac1dbc60d2c51d07f9c3fa4c3baec395ebf9c8b0738afe78abb08a4bc69c67b8c14e8b14e8941f872a386b5d82887805b575268740b57093f62b5461dc24ff364e8624dd724c57046bea45f123fffa3f420398fc36f2135dba3341d32c94314a62a91529f8e294da2603c25d5b240aa23aaf1ddd91d3b11bfea1bae71491113e21113230a63d07db80789302e4500512
|7,0=>0xf177edb423cbab5ca63593d95855fd8424574778738813e1a2289ea
|8,0=>0x932a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfffffefe000000000000000000000000ffff0000ffffffff000000000000000000000000ff00ff00fffffffa000000000000000000000000aaaaaaaaffffafaf000000000000000000000000ffffaaaaeeeeeeee000000000000000000000000eeeeeeeeffffffff00000000000000000000000000000000fffff0f0000000000000000000000000fffff0f0ff00ff00000000000000000000000000ff00ff00fffefffe000000000000000000000000ff00ff00ffffff00000000000000000000000000ffffff00f0f0f0f0000000000000000000000000f0f0f0f0eeeeeeee000000000000000000000000eeee0000ffff0000000000000000000000000000ffff0000fffffffa000000000000000000000000ff00ff00cccccccc000000000000000000000000ccccccccffffffff000000000000000000000000aaaaaaaa
|0,1=>0xfffffffc000000000000000000000000cccccccc00af00af00000000000000000000000000af00aafefefefe000000000000000000000000fefefefe0000fefe0000000000000000000000000000fefeffeeffee000000000000000000000000ff00ff00afafafaf000000000000000000000000aaaaaaaa00ab00ab00000000000000000000000000aa00aaffffaaaa000000000000000000000000ffffaaaaffffff00000000000000000000000000aaaaaa00ffffffaa000000000000000000000000aaaaaaaafffffff000000000000000000000000000000000000000ff000000000000000000000000ffffff00ffff0505000000000000000000000000ffff0000ffffffff000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000aaaaaaaaffffffff000000000000000000000000ffff0000
|0,2=>0xffffffff000000000000000000000000ffffff00aaaaaaaa000000000000000000000000aaaaaa00fefefefe0000000000000000000000000000000000ef00ef00000000000000000000000000ee00ee3333030300000000000000000000000033330300afafafaf000000000000000000000000afafaaaafffffafa000000000000000000000000fffffafafffffafa000000000000000000000000000000004545454500000000000000000000000044444444ffff00af000000000000000000000000ffff00aaffff0f0f000000000000000000000000ffff0000fffffff0000000000000000000000000fffffff000000000000000000000000000000000ffffff00333301010000000000000000000000003333000011110101000000000000000000000000111100000f0f0f0f00000000000000000000000000000000
|0,3=>0xeeee0000000000000000000000000000eeee5555050500000000000000000000000055550000f5f5f5f0000000000000000000000000f5f5f5f0ffff0f0f000000000000000000000000ffff0f001111111100000000000000000000000011110000ffffffaa000000000000000000000000ff00ff0000000000000000000000000000000000eeeeeeeeffffffff000000000000000000000000ffffaaaaabababab000000000000000000000000aaaaaaaa333303030000000000000000000000003333000000ff00af00000000000000000000000000ff00aa00000000000000000000000000000000ffffaaaaffffeeee000000000000000000000000ccccccccfefefefe000000000000000000000000aaaaaaaa0000afaf0000000000000000000000000000aaaa0000efef0000000000000000000000000000eeee
|0,4=>0x1010101000000000000000000000000000000000f0f0f0f0000000000000000000000000a0a0a0affff00ff000000000000000000000000ffff00aaffffffff000000000000000000000000ccccccccfcfcfcfc000000000000000000000000fcfcfcfc00af00af00000000000000000000000000aa00aa050505050000000000000000000000000000000000ff00ff00000000000000000000000000aa00aa000f000f000000000000000000000000000a000afefefefe000000000000000000000000f0f0f0f0fff0fff0000000000000000000000000fff0fff00000ffff0000000000000000000000000000ff00aaaaffff000000000000000000000000aaaaaaaacfcfcfcf000000000000000000000000cecececef0f0f0f0000000000000000000000000fefefefefafafafa000000000000000000000000fafafafa
|0,5=>0xffffff0000000000000000000000000000000000ffffaaaa000000000000000000000000000000000000050500000000000000000000000000000000f0f0f0f0000000000000000000000000fffffafa000f000f000000000000000000000000000f000000ff000f00000000000000000000000000ff0000ffff000f000000000000000000000000ffff000033331111000000000000000000000000333300001111111100000000000000000000000000000000ffffff00000000000000000000000000ffff00003333333300000000000000000000000033333300333333330000000000000000000000003333000000bb00bb00000000000000000000000000aa00aa03030303000000000000000000000000000000000000ffff0000000000000000000000000000eeeeeeeeeeee00000000000000000000000000000000
|0,6=>0xfffffffa000000000000000000000000fffffffa0000ffff0000000000000000000000000000aaaaff0fff0f000000000000000000000000ff00ff00fffffafa000000000000000000000000f0f0f0f0ffffff0f000000000000000000000000ffffff0055555555000000000000000000000000000000000f0f0f0f0000000000000000000000000c0c0c0c00ff00ff00000000000000000000000000000000ffff00ff000000000000000000000000ffff0000efefefef000000000000000000000000eeeeeeee555555550000000000000000000000004444444433333333000000000000000000000000333322220505050500000000000000000000000004040404fffffff0000000000000000000000000f0f0f0f011110000000000000000000000000000ffff00000f0f0f0f0000000000000000000000000f0f0f00
|0,7=>0xff000000000000000000000000000000003333333300000000000000000000000000000000bbbbbbbb000000000000000000000000aaaaaaaa4444444400000000000000000000000044444444ffffeeee000000000000000000000000ffffeeee0000ffff00000000000000000000000000000000ff00ffff000000000000000000000000ff00ff0000ff00ff00000000000000000000000000ff000055555555000000000000000000000000555500000f0f0f0f0000000000000000000000000f0f0a0a0000ff0f0000000000000000000000000000ff00ffff0f0f000000000000000000000000ffff0a0a0505050500000000000000000000000005050000f0f0f0f0000000000000000000000000fffffff0ff00ff0f000000000000000000000000ff00ff00ffffffaa000000000000000000000000ffffffaa
|0,8=>0xff000000000000000000000000000000ff00000f000f000000000000000000000000000000000000555500000000000000000000000000000000ffff5555000000000000000000000000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x10d0a06031f110a03081f110a0301111e0a06181d0b0a18080b1c0a031b05010006030b1a0a030111190a0610050116100805011606100111151008011115180501170a030e050116030e0111151403050111061301110a0f0812110610010d0f080100030e010d03070b00060c0b0a09080400030701000605040003020100
|1=>0xa03080b320a030b112c0a03080b310a080111300a090804110a2f030501162403012e0a030812112d0610050b000301112c0a0308112b0a03080b2a0a0629180b0a100801112803080b270a260301110a031b050b0003050b170a1825080b0a2423100111030811220a1005011117030811210a06180b0a200603010d0a0308
|2=>0x110a0308410b110a100308400100340308050b0a06031d0b110a09080b113f0a030801113e0a06033d01110a3c030801110a030805113b0a03080b111c0a033a0501110a03081d39110a0638050b0a03080b370a062511360a2910080100030111350a080b11300a0634050b0a1008053311060b111c0a0910080b000c03080b
|3=>0x301114e480a03080512115025030811360a0308050b005006030b110a20061005010011181008050b0a030801110a4f03080b1a0a03080b004e0a034b0111480a4d030501110a03084b12110a03084b0b000a030811360a200301114a0a060301110a4903011148470a0308460b110a03450111440a0308050b430a03084201
|4=>0x5a0a03081d4c110a380308050b0a03084011540a1808050b3f0a59030801110a03080511580a03080539115703081d01000a242f0301110a06030511550a06560501110a03080511550a030811540a20180308011a0a060305012e0a0308050b390003050111530a2503080b110a03080b110a520603050b000a08050111510a
|5=>0x6601110a06034001000a0308050b650a03080511640a03080111630a03086201110a6108050b110a06030111600a03080111600a0903080b000a030e0501115f03080501005e13030801110a030801110a5d031b0501110a062501110a205c030801110a0c030801110a08050b11510a030801115b0a03080b110a4f03080111
|6=>0x3080504110a03710801110a03080b011a0a6f060301110a1803080b0a201810080501000308050b6e0a060301114e0a06036d01110a030801110a2d03080b000a20031b050b110a03086c01110a6b060301110a1803081d0b0a06100501116a03080b11690a06670501110a29030801000a03081d0b000a10080501115f0308
|7=>0x30801110a490308050111650a29030801110a03081d0b110a0903080100110a100308050b110a23030501116803400100480a03080111760a03080111750a74030801110a0618050b0a06050b113f0a06030501160a03080501160a03050b00480a03080b110a2d03080111730a03084b39110a291803080b0a72030801110a
|8=>0x30801110a200308053901110a036d0801110a20180308050b0a7b0308050b110a03084c0111690a03050111480a03080100110a2006030501110a6a0308050b113f0a1003450801110a0379080501110a0308050b000a0308050111780a03080b110a200308050111770a1003080511540a06030501110a5f03080501110a5f
|9=>0x801114e0a036d0801110a06030501110a6803081d0b01110a8003080501110a0610080501110a06030e0501110a100308050100110308011a110a200308050b39110a03084001000a2918030801110a06030501110a7f03080501110a7f030805017d110a03080111690a0308117c0a201803080501000a0308050100117a18
|10=>0x7e0308050b01110a03080501110a6a0903080b110a3803080501110a030801110a8203080501110a8103081d01110a030e0801110a20030805120b110a0308011a110a03450e01110a03080100114e0a0603050b110a3403080501110a03084b0b110a09030e0801110a0308051201110a03080b01110a2003080501110a5e03
|11=>0x3080501110a030801110a201803080501110a0308050100110a09030801110a06030501110a03050111830a03084b01110a030e080501110a03080501110a
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x1220204038806100a20104018802100220004
|4,0=>0x98a92c524ea48948ea9185226a439484a90451fea3e947aa8f051d6a399470a8dc51aea349466a8c85186a2f945ca8b4515ea2a9452a8a05136a259448a88c510ea20943ea87850e6a1b9434a86450bea16942aa8505096a119420a83c506ea0c9416a8285
|5,0=>0x55ccaa1951329c652cca41945328464fcc9e1939326c64ccc98192d3254649cc921921323c646cc8c19153224643cc861909320c640cc8018fd31f463dcc7a18f131dc63acc7418e5a9c5637ec6e58d9b1ad634ec6894ce31966320c6298c2317e62f0c5c98b6316662c0c5698aa314e6290c50989e31366
|5,1=>0x3d3679acf1d9e0b3bb676caec19d533a4673cce619c9338c670cce019bd337466dccda19b1335c66accd419a53344667ccce1999332c664ccc8198d3314661ccc2198132fc65eccbc197532e465bccb6196932cc658ccb0195d32b46
|6,0=>0x56b6ac8f579aabbd516a94f50de9eb5376a60f4a9a91bd1d6a2cf43de843d0179f6d3d5a773ce779c0f365e693ccb7988f2f5e5bb4b07952f289e4dbc95691ed221e40bc7a78e6f1b1e33345f78b0f149a25bc44787af0d9e17bc296844f071a0abc0e780ef001dfd33f377dacf9d9f03bd97
|7,0=>0x16cdad63da57b3ed665ac9b58d6b0cf5fdebc3d717
|8,0=>0x5b96
|_,_=>0
def wAt:=mkWire dB 132 160 0xffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xb03c200d110a404451d0a00445100b1c015080340c29110a40c021d0a0142a031142c15011140da1110a4142d110a4200d050346028050a80429030044429110a4182908034142a050084531010a4442905014206a050a80c3a030a82c2b030a4142d01114200d030b804450611c0c760b0540445030044429030a44429031d8200d290a0180003114142d01114200d
|1=>0x3114182a08034182a0803445f9010a93017010a40447050a84429030a8142a0b0ac0445050a80445031142c0d011153017010a42002110a4142a03084442a0b03c0445030a41421087a40c2a110a40445081080c29050a80445111080c29011080c29060a0200d060a0200d056a84532010a42445050342c15011144429050340c29011142002110a40c4501114200d
|2=>0x50a80c45110a4140d08034200f050142029010a80445110a804450503460290311415a2080a8602a03114142d01114142a0b0a4044511204142a08054202905008442901114200d180ac0c45050140445030542029114c40429050a86028031141402110a42081050a8202a08034142d011140da9110a80c29080340c21080a40c29110a4142a0b0ac0445110a46015
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0xa2000000082000000000000062000000000000000000000000000000000000000000000051000000000041000000000000000000000000000000000004000000000000000000000000000000000000000
|5,0=>0x2710000000000000000002612420000000000000002312120000000000000000000000000000000000000000000000000000000000002011f10000001d21b20001920000000001811710001611510001231020000f10000000c3000000
|5,1=>0x4320000000004033e20000003c23a20000000000003910000003720003523410000003313210000000002f30000002e12d12c10000002a2000000000000000000000291000281000
|6,0=>0xb32b12af2ad2ab2aa1a82a62a42a22a029e29c29a29829719529329128f28d28b28928728528418228117f27d27b27927727527417317217026f16d26b26926726616426226025e25c25a25825625425225024f14d24b2492472452
|7,0=>0xbf1be1bd1bc1bb1ba1b91b81b71b61b51
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 12
def pmP:Nat→Nat
|0=>0x4690409040804070401040002090200010000800061006000490041004000300024002100200019001800140010000900080006000500040003000200010000
|1=>0x42012ef92eeb2988280224222421240022c120412004200114000ee90ea90e790e690e490e390e2b0e290e210e0908a908810800067d06610615060906010600
|2=>0xcee9c8a1c421a46e880084206ec96e296da164254ea94e294da0490044244421
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0xa000018000000048000000000000000000000000001000000680000000000000000000580000000000000000000000
|5,0=>0xa0000052600004c04000080088000cc01d1a0000a1e00000160001604340000a0000000000001a00d00000088000000000010a00000000012040000000000000000000000000000000000068d00009100068000005c68012d400b0600b800030000
|6,0=>0x2c2b0c0a5843a6c780a40b0765501f73384236c9c41d948631c0205cb7481dc1a372d5937e6e09e44f1a2a02a891926a209b98b5d1e
|7,0=>0x13d7c47ab98be8b257c8
|8,0=>0x32
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 16 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_155 7 roots_155 ops++addP pm 1 dom_139 5 roots_139 ops++addP pm 2 dom_154 5 roots_154 ops++addP pm 3 dom_143 6 roots_143 ops++addP pm 4 dom_153 5 roots_153 ops++addP pm 5 dom_150 5 roots_150 ops++addP pm 6 dom_141 5 roots_141 ops++addP pm 7 dom_149 5 roots_149 ops++addP pm 8 dom_147 5 roots_147 ops++addP pm 9 dom_157 6 roots_157 ops++addP pm 10 dom_158 6 roots_158 ops++addP pm 11 dom_151 6 roots_151 ops++addP pm 12 dom_146 4 roots_146 ops++addP pm 13 dzo_27_4 4 roots_27 ops++addP pm 14 dom_27 4 roots_27 ops++addP pm 15 dzo_155_4 5 roots_155 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_159 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_155 7 s (0,roots_155.map (·&&&dom_155)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_159 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_155 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_159==dom_159)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_159 gM v ys):RunD true dom_159 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_159 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 10 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 54 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 54 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 113 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 113 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 61 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 61 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 11 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_159 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_159 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_159 roots_159 goal_159 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_159
theorem lowS_159:Lower true dom_159 roots_159 goal_159 9:=S_159.noCircuit
def dzo_179_8:=0xf000f000f000f0000000000000000000f000f000f000f00
def gzo_179_8:=0xf000f000f000f0000000000000000000f000e000e000a00
def gsh_179_8:=0xf000f000f000f0000000000000000000f000e000e000a
theorem lowS_zo_179_8_50:Lower true dzo_179_8 roots_179 gzo_179_8 6:=lower_iso_b (d1:=dom_179) (r1:=roots_179) (T1:=gsh_179_8) [(dom_179,8)] (by decide +kernel) (lower_slice_b (T:=gsh_179_8) [(0xa000a000a000a0000000000000000000a000a000a000a,0,1),(0xf000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_50)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,131),(8,9),(8,136),(10,11),(10,26),(10,42),(10,138),(16,17),(16,18),(16,48),(16,144),(24,25),(24,26),(24,56),(24,152),(32,33),(32,34),(32,48),(32,160),(40,41),(40,42),(40,56),(40,168),(128,129),(128,130),(128,136),(128,144),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x57db326e37
|6,0=>0xfca08fba6ad6a73b5db2b2f6b67c633ccd50ffc1
|7,0=>0x9d20d8e86c8df7462ba75aa072f8101e10012f8f0aea0
|8,0=>0xc2d55770fe1d969
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0000000000000000000000000f0f0000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f0000000000f0f0f000000000000000000000000000f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000f0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0000000000000000000000000f0f0f0f00000000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f00000f0f000000000000000000000f0f00000f0f0000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a30303030303030300000000000000000303030303030000f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xe362093a62f09362d0543620c93a620b43a62059736208936204973a62c493a620b47a62c93a21093a210843620c54362049e7629762d0973a21084762543210
|1=>0x93a620b93a620973a6209
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x65006
|6,0=>0x3863172b62561e71861260b7
|7,0=>0x7476e66866175a75374d64673e8
|8,0=>0x8878177b6
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x24d304e9978c19e8e99a641974c1396419a4c1ba64d904c134641304e59065d3071b974c1ba4e59066934641904e9307a73a4c1c6e5dba4c139641
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x5cd5248cf330c9318c42
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0xeb9f1cf2e16f7ab9b1cd0606f72b993ec8e64611fd8bfc4fe0fb010004001e000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x20
|6,0=>0x7090569c83
|7,0=>0xb54272619f1
|8,0=>0x396a
|9,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_186 8 roots_186 ops++addP pm 1 dom_59 7 roots_59 ops++addP pm 2 dom_147 5 roots_147 ops++addP pm 3 dom_163 5 roots_163 ops++addP pm 4 dom_185 8 roots_185 ops++addP pm 5 dom_171 7 roots_171 ops++addP pm 6 dom_155 7 roots_155 ops++addP pm 7 dzo_179_8 6 roots_179 ops++addP pm 8 dom_43 4 roots_43 ops++addP pm 9 dzo_51_8 5 roots_51 ops++addP pm 10 dom_179 8 roots_179 ops++addP pm 11 dom_139 5 roots_139 ops++addP pm 12 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_179_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_51_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_186 8 s (0,roots_186.map (·&&&dom_186)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_186 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_187 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_190:Lower true dom_190 roots_190 goal_190 9:=lower_slice_b [(0x505050505050505000000000000000005050505050505050,128,132)] (by decide +kernel) lowS_186
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000cccc000000000000c8c80000000000008800
def gsh_205_2:=0x3333000000000000333300000000000032320000000000002200
theorem lowS_zo_205_2_77:Lower true dzo_205_2 roots_205 gzo_205_2 5:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (lower_slice_b (T:=gsh_205_2) [(0x3333000000000000333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_77)
namespace S_207
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,130),(3,11),(3,67),(3,131),(4,68),(4,132),(5,13),(5,69),(5,133),(6,70),(6,134),(7,15),(7,71),(7,135),(8,9),(8,136),(10,11),(10,138),(12,13),(12,76),(12,140),(14,15),(14,78),(14,142),(64,65),(64,68),(66,67),(66,70),(66,194),(72,73),(72,76),(72,200),(74,75),(74,78),(74,202),(128,129),(128,130),(128,132),(128,136),(192,193),(192,194),(192,196),(192,200)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_207.map (·&&&dom_207)
def gM:=goal_207&&&dom_207
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>7
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x8a2d5
|4,0=>0xc25eabc6517027e1cc01
|5,0=>0xad574a25faa1ad0a133090fc16417f4f7643931c1bf3e135b1
|6,0=>0xb967d982ee8de291d42c188020776d03c4d
|7,0=>0x83b1d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xfafa0000000000000000000000000000fafa00ff00000000000000ff00000000000000aa00000000000000aa3333000000000000333300000000000000000000000000000000ff33000000000000ff33000000000000ff00000000000000ff00bbbb000000000000bbbb000000000000aaaa000000000000aaaafafa000000000000fafa000000000000fafa000000000000fafaffff000000000000ffff000000000000ffff0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0aaaa000000000000aaaa000000000000aaaa000000000000aaaa00bb00000000000000bb00000000000000aa00000000000000aaffff0000000000000000000000000000ffff0000000000000000ffff000000000000ffff00000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000ff00cccc000000000000cccc000000000000cccc000000000000ccccffff000000000000ffff000000000000aaaa000000000000aaaafafa000000000000fafa000000000000fafa0000000000000000
|0,1=>0xffff000000000000ffff000000000000ff00000000000000ff00eeee000000000000eeee000000000000eeee000000000000eeeeffcc000000000000ffcc000000000000ffcc000000000000ffcc0f0f0000000000000f0f0000000000000f0f0000000000000000fefe000000000000fefe000000000000fefe000000000000fefe
|_,_=>0
def sP:Nat→Nat
|0=>0xa0d0239483508e520d023a48344ce520d0209ca41a0e52364341ca4188e98906a11d241a1672907051ca41a9e2391023b8a41a0413a46a104a41a8e52358341ca41a96520c470106a10528398a418820
|1=>0x6811ca4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x1350e5095045
|5,0=>0x4e64864263c63663062a62461e6186
|6,0=>0x7977366d66766075a6546
|7,0=>0x806
|_,_=>0
def wAt:=mkWire dB 21 208 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x19141d29111d39111218950941d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x2000000000000
|6,0=>0x81716151413121
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xd9afbdd5aab40e724c682503001001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3002100
|6,0=>0x485b76a
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 11 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_205 6 roots_205 ops++addP pm 1 dom_198 4 roots_198 ops++addP pm 2 dzo_77_2 4 roots_77 ops++addP pm 3 dom_143 6 roots_143 ops++addP pm 4 dom_201 5 roots_201 ops++addP pm 5 dom_199 5 roots_199 ops++addP pm 6 dzo_205_2 5 roots_205 ops++addP pm 7 dom_203 6 roots_203 ops++addP pm 8 dom_77 4 roots_77 ops++addP pm 9 dom_206 5 roots_206 ops++addP pm 10 dom_204 4 roots_204 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_207 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_77_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_205_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_204 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_205 6 s (0,roots_205.map (·&&&dom_205)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_207 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_205 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_207 gM v ys):RunD true dom_207 gM v (ori ys):=h
def Z (s:Nat):=barP dom_207 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_207 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 5=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_207 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_207 roots_207 goal_207 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_207
theorem lowS_207:Lower true dom_207 roots_207 goal_207 8:=S_207.noCircuit
theorem lowS_215:Lower true dom_215 roots_215 goal_215 8:=lower_slice_b [(0xf000f00000000000f000f00000000000f000f00000000000f000f0,64,68)] (by decide +kernel) lowS_211
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,136),(10,11),(10,26),(10,138),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,88),(24,152),(64,65),(64,80),(66,67),(66,82),(66,194),(72,73),(72,88),(72,200),(74,75),(74,90),(74,202),(128,129),(128,130),(128,136),(128,144),(192,193),(192,194),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|3=>1
|4=>6
|5=>13
|6=>9
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xb8c7d
|4,0=>0x8ebbd4b27b452f73164b2998023526
|5,0=>0x82ee4820086c393553bc3bf253961e2da19288f614b791135410b450758b02594
|6,0=>0xab65598d8c61d8f3cc302711e1a91e15f330ca8704e6c
|7,0=>0x4c5010af55
|8,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00f0f0a0a000000000f0f0a0a000000000f0f0a0a00000000000000005050505000000000505050500000000050500000000000005050000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000f000f00000000000f000f00000000000a000a00000000000a000af0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0ac0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0ae0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0ef0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|0,1=>0x3030303000000000303030300000000030300000000000003030000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a0000000000000000f0f0a0a0000000000000000000000000f0f0a0a00f000f00000000000f000f00000000000f000a00000000000f000a000000f000000000000000f000000000000000a000000000000000ae0e0e0e000000000e0e0e0e000000000e0e0000000000000e0e00003030303000000000303030300000000030303030000000003030000b0b0b0b000000000b0b0b0b000000000b0b0a0a000000000b0b0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x69c8f1a8e6239ea684ce78c47239ea3928e7a8e49b9ea6c88e7a0ad399c33916e78d41201ea6922078d07201ea6c08e7a9a13014731120194e6238623900569c8c19c8b0282648068398032848018820
|1=>0x14d391cf429a7239ea6848e7894d391cf2a9a4bb9ea69c8b73c6a091cf415a7239ea69ec403eaa
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x1d51851350e5095045
|5,0=>0x6966365d65765164b64563f63963362e5286226
|6,0=>0xa479d79679068978277c67576f6
|7,0=>0xb17ab6
|8,0=>0xb86
|_,_=>0
def wAt:=mkWire dB 24 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x22939143d22929f7a92937a96a939153d51101173d43b2296a923d39123d51923d09453d23d53d79173d391
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x7200000a4320000000000000c0000
|6,0=>0x192b954a6512793496492
|7,0=>0x383b1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xefeb6f422f291a0f0806050100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x4001300000400
|6,0=>0x72189653b
|7,0=>0xac
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 7 roots_217 ops++addP pm 1 dom_218 6 roots_218 ops++addP pm 2 dom_203 6 roots_203 ops++addP pm 3 dom_211 7 roots_211 ops++addP pm 4 dom_154 5 roots_154 ops++addP pm 5 dom_155 7 roots_155 ops++addP pm 6 dom_91 6 roots_91 ops++addP pm 7 dom_216 4 roots_216 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_216 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 7 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_219 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_219 roots_219 goal_219 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_219
theorem lowS_219:Lower true dom_219 roots_219 goal_219 9:=S_219.noCircuit
namespace S_243
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,67),(3,131),(16,17),(16,18),(16,48),(16,80),(16,144),(32,33),(32,34),(32,48),(32,96),(32,160),(64,65),(64,80),(64,96),(66,67),(66,82),(66,98),(66,194),(128,129),(128,130),(128,144),(128,160),(192,193),(192,194),(192,208),(192,224)]
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
|8,0=>0x655b0
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f0000000f000f000f0000000f000f000f0000000f000f000f0000f000f00000000000f000f00000000000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x58d11ac688
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
|0=>0xb1
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
addP pm 0 dom_242 8 roots_242 ops++addP pm 1 dom_179 8 roots_179 ops++addP pm 2 dom_115 8 roots_115 ops++addP pm 3 dom_241 8 roots_241 ops++addP pm 4 dom_227 7 roots_227 ops++addP pm 5 dom_211 7 roots_211 ops
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
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
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
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_slice_b [(0x50005000500050005000500050005000500050005000500050005000500050,64,68)] (by decide +kernel) lowS_242
theorem lowS_252:Lower true dom_252 roots_252 goal_252 8:=lower_slice_b [(0x1010101010101010101010101010101010101010101010101010101010101010,64,68)] (by decide +kernel) lowS_248
def isoMvS_111:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_iso_b isoMvS_111 (by decide +kernel) lowS_95
def isoMvS_123:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_123:Lower true dom_123 roots_123 goal_123 9:=lower_iso_b isoMvS_123 (by decide +kernel) lowS_119
def isoMvS_221:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 8:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_215
def isoMvS_222:List (Nat×Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 8:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_207
def isoMvS_238:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 8:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_207
def isoMvS_249:List (Nat×Nat):=[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_187
def isoMvS_250:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 9:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_119
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500550050005500440044000000
def gsh_118_8:=0x550055005500500055004400440000
theorem lowS_zo_118_8_118:Lower true dzo_118_8 roots_118 gzo_118_8 7:=lower_iso_b (d1:=dom_118) (r1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (lower_slice_b (T:=gsh_118_8) [] (by decide +kernel) lowS_118)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0e0e0e0e0a000
def gsh_59_4:=0xf0f0e0e0e0e0a00
theorem lowS_zo_59_4_59:Lower true dzo_59_4 roots_59 gzo_59_4 7:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [] (by decide +kernel) lowS_59)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030202020202000
def gsh_121_4:=0x3030303030303030303020202020200
theorem lowS_zo_121_4_57:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_57)
def dzo_115_12:=0xf000f000f000f000f000f000f000f000
def gzo_115_12:=0xf000f000f000f000f000e000e000a000
def gsh_115_12:=0xf000f000f000f000f000e000e000a
theorem lowS_zo_115_12_50:Lower true dzo_115_12 roots_115 gzo_115_12 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_12) [(dom_115,12)] (by decide +kernel) (lower_slice_b (T:=gsh_115_12) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f000f000f0000000000000000,0,64)] (by decide +kernel) lowS_50)
def dzo_114_4:=0x500050005000500050005000500050
def gzo_114_4:=0x500050005000500050004000400000
def gsh_114_4:=0x50005000500050005000400040000
theorem lowS_zo_114_4_50:Lower true dzo_114_4 roots_114 gzo_114_4 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_4) [(dom_114,4)] (by decide +kernel) (lower_slice_b (T:=gsh_114_4) [(0x50005000500050000000000000000,0,64)] (by decide +kernel) lowS_50)
def dzo_115_4:=0xf000f000f000f000f000f000f000f0
def gzo_115_4:=0xf000f000f000f000f000e000e00000
def gsh_115_4:=0xf000f000f000f000f000e000e0000
theorem lowS_zo_115_4_51:Lower true dzo_115_4 roots_115 gzo_115_4 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (lower_slice_b (T:=gsh_115_4) [(0xf000f000f000f0000000000000000,0,64)] (by decide +kernel) lowS_51)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300330032003300220022002200
def gsh_117_8:=0x330033003300320033002200220022
theorem lowS_zo_117_8_116:Lower true dzo_117_8 roots_117 gzo_117_8 6:=lower_iso_b (d1:=dom_117) (r1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (lower_slice_b (T:=gsh_117_8) [(0x220022002200220022002200220022,0,1)] (by decide +kernel) lowS_116)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0e0e0e0e0a000
def gsh_123_4:=0xf0f0f0f0f0f0f0f0f0f0e0e0e0e0a00
theorem lowS_zo_123_4_59:Lower true dzo_123_4 roots_123 gzo_123_4 8:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_59)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000e0e00000a000
def gsh_107_4:=0xf0f00000f0f00000e0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 5:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000c8c80000cccc00008800
def gsh_109_2:=0x3333000032320000333300002200
theorem lowS_zo_109_2_77:Lower true dzo_109_2 roots_109 gzo_109_2 5:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_77)
def dzo_119_8:=0xff00ff00ff00ff00ff00ff00ff00ff00
def gzo_119_8:=0xff00ff00ff00fa00ff00ee00ee00aa00
def gsh_119_8:=0xff00ff00ff00fa00ff00ee00ee00aa
theorem lowS_zo_119_8_118:Lower true dzo_119_8 roots_119 gzo_119_8 8:=lower_iso_b (d1:=dom_119) (r1:=roots_119) (T1:=gsh_119_8) [(dom_119,8)] (by decide +kernel) (lower_slice_b (T:=gsh_119_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa,0,1)] (by decide +kernel) lowS_118)
def dzo_87_8:=0xff00ff0000000000ff00ff00
def gzo_87_8:=0xff00fa0000000000ee00aa00
def gsh_87_8:=0xff00fa0000000000ee00aa
theorem lowS_zo_87_8_86:Lower true dzo_87_8 roots_87 gzo_87_8 5:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_8) [(dom_87,8)] (by decide +kernel) (lower_slice_b (T:=gsh_87_8) [(0xaa00aa0000000000aa00aa,0,1)] (by decide +kernel) lowS_86)
def dzo_103_8:=0xff000000ff000000ff000000ff00
def gzo_103_8:=0xff000000fa000000ee000000aa00
def gsh_103_8:=0xff000000fa000000ee000000aa
theorem lowS_zo_103_8_102:Lower true dzo_103_8 roots_103 gzo_103_8 5:=lower_iso_b (d1:=dom_103) (r1:=roots_103) (T1:=gsh_103_8) [(dom_103,8)] (by decide +kernel) (lower_slice_b (T:=gsh_103_8) [(0xaa000000aa000000aa000000aa,0,1)] (by decide +kernel) lowS_102)
def dzo_125_2:=0xcccccccccccccccccccccccccccccccc
def gzo_125_2:=0xccccccccccccc8c8cccccccccccc8800
def gsh_125_2:=0x33333333333332323333333333332200
theorem lowS_zo_125_2_77:Lower true dzo_125_2 roots_125 gzo_125_2 6:=lower_iso_b (d1:=dom_125) (r1:=roots_125) (T1:=gsh_125_2) [(dom_125,2)] (by decide +kernel) (lower_slice_b (T:=gsh_125_2) [(0x33330000333300003333000033330000,0,16),(0x33333333000000003333333300000000,0,32)] (by decide +kernel) lowS_77)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(10,11),(10,26),(10,42),(12,13),(12,76),(14,15),(14,30),(14,46),(14,78),(16,17),(16,18),(16,48),(16,80),(20,21),(20,22),(20,52),(20,84),(24,25),(24,26),(24,56),(24,88),(28,29),(28,30),(28,60),(28,92),(32,33),(32,34),(32,48),(32,96),(36,37),(36,38),(36,52),(36,100),(40,41),(40,42),(40,56),(40,104),(44,45),(44,46),(44,60),(44,108),(64,65),(64,68),(64,80),(64,96),(66,67),(66,70),(66,82),(66,98),(72,73),(72,76),(72,88),(72,104),(74,75),(74,78),(74,90),(74,106)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|4=>8
|5=>57
|6=>136
|7=>113
|8=>41
|9=>7
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc60da53a1344730400011b8b2186211119006286
|5,0=>0xe8dbbe1beec2b8ebaa92b7dadb09dfaf6fca8ccea20769ddfb8f512842827fc5c7c9bb7a5cd7054c6f8f5672ca6653b662045ad18569165636652d2f4e1bc4d3fd49c2e4633f4383342a0d405d73bf8a3b4a33a7bd3a4a13943f3630a35f033461d323b72f7c6232331eb471e9031e6201c2631b8b217117165cd1579014e4014c640e2ae0baf60766d0712503c04
|6,0=>0x997039599f9596a8dd6d8a34d88cdb8812487e81866f6852ff83b83828c57dc1e7c2d677ea6776e17762e76ba9768247370372b70724ef707d46f8f56da9d6cfd56bd046ab1963e7362719600375bb755916758f9457e7a5751d5518d53c9f531a453135517d94d97f4cdf94b8ce4afad4a71b497db497ad494a746e9a418a4407fc3e9a03e38b3cda43be473bd923b0b73917338f4c38f2f38dce3875b3822237bff37a5135d903490934077326ae301772ca812aa062917027ad526fb1261512539d24e27247fe243272322b21ae32171a216df1f5691d09a1c22a1c0921ba551b90a197f2191c1190651791816d5e1623a15928152eb13cbe134b212f28123700fd810fa5b0ef7c0eae80dd790d4560d1d20c2500a5550a06f0a00d07c47066ae05c8f049f10448c0432f03df50397602dff02702026b1021bd01c8f00873
|6,1=>0xe27d2cc660c04a6b83c9b6b0aac8c0a4705a0ecf
|7,0=>0xf65c1f100aed928b62fdb5f79ab19faac14a8b26a2a1d92d608ebbe8e4b38ca6b877cf841d97726e734e172b497266c70122700d56cb9666bfd6404a5e04c5d05a5b34459c3e588d55854f515c6503014ecca4e5c14c93a48b9a47fe540dfe4090d3f9c93f34b3f2d03eed83ee943e4eb3d2e13cf64374ff36f1d35d773546033ac6312122fdb02fcb22cfd52c0582b8c12906d266cd26113247752449a238e82203d2123e21221207a51eb161d3691c6da1c6c91a75819f9319e0718e4d18327164f5164e61606715e1015d9014dfe13c8912f0a1269f123e4114a2112e10fc2d0f9960dc6e0db150d1df0d1370cf570ccf70c22a0a85309f930926508e9208c5707e5c073c70721c054a0050a50507004b4803f6801a3b014c3
|8,0=>0xf80d3bcd97b5c4bb5859a24cba0fec8f7518a22c883e68837d61f425ef43527985137d4789646f5d4633a43da4431fe3c55e3c0ea395fb26280241f0224dc222f22150d212c91edcb1cabb194ba18965155f2109fd0bb3f0a2af0a10408f0c045fa037ed0127a
|9,0=>0x950798d3bf5efe35254f3b65b334ec2537d
|10,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa2aaa2aaa2aaa0aaa22aa22aa22aa003f3f3f3f3f3f0f0f3333333333330000ffffffffffffffffffffffff00000000ffffaaaaffffaaaaffffaaaaffffaaaaefefefefefef0f0feeeeeeeeeeee0000ffffffffffffffff0000000000000000fffffffffafafafafffffffffafafafaffffffffaaaaaaaaffffffffaaaaaaaaffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffeeeeeeeeeeee0000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffaaaaeeeeeeeeeeeeaaaa00aa00aa00aa00aa00aa00aa00aa00aa
|0,1=>0xaaaaaaaaaaaaaaaaaa22aa22aa22aa0033333333333300003333333333330000ffffffffffff0000ffffffffffff0000ffffffff0faf0fafffffffff00aa00aaffff0f0fffff0f0fffff0000ffff0000cccccccccccccccccccccccccccccccc00000000ffff00aa00000000ffff00aa00000000ffffffff00000000ffffff00ffffffff00aa00aaffffffff00aa00aaffffffffffffffffcccccccccccccccc0000ffff0000ffff0000ffff00000000ffffffffffffff00ffffffffffffff00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa3fbf3fbf3fbf0faf33bb33bb33bb00aaffffffffffff0000eeeeeeeeeeee00000f0f0f0f0f0f0f0f0e0e0e0e0e0e0000
|0,2=>0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00000000fffffafa00000000fffffafa3f3f3f3f3f3f2f2f3333333333332222ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00ffffffffffffaaaaffffffffffffaaaaffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000ffffffffffff0000cccccccccccc0000fffffafafffffafafffffafafffffafaeeeeeeeeeeee0000eeeeeeeeeeee00000000ffff000000aa0000ffff000000aaffffffff0f0f0f0fffffffff00000000ffff00aaffff00aaffff00aaffff00aaffffffffffff00aaffffffffffff00aa
|0,3=>0xffffaaaaffffaaaaffffaaaa00000000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffff3333333333330000ffffffffffffffff00aa00aa00aa00aa00000000ffffff0f00000000ffffff00ffffafafffffafafffffaaaaffffaaaa0f0f0f0f0f0f0f0f000000000000000000aaffff00aa0faf00aaffff00aa00aafffffffffffff0fa0000000000000000ffffffffffff0f0fffffffffffff0000aaaaaaaaaaaaaa0aaaaaaaaaaaaaaa00ffffeeeeffffeeeeffffeeeeccccccccffffffffaaaaaaaaffff0000aaaa00000000ffff00000faf0000ffff000000aaffffffffffff0fafffffffffffff00aaffffffffffff00aacceecceeccee00aa
|0,4=>0xff33ff33ff33ff0033333333333322223333333333332222ff3fff3fff3fff0fff33ff33ff33ff000faf0faf0faf0faf00aa00aa00aa00aabfbfbfbfbfbfafafbbbbbbbbbbbbaaaa0000ffff0000ffff0000ffff0000ff0051515151515150505151515151515050f3f3f3f3f3f3f0f0f3f3f3f3f3f3f0f033bb33bb33bb00aa33bb33bb33bb00aa55555555555550505555555555555050fffffffffffffafa00000000000000000000ffff0000ff0f0000ffff0000ff00bbbbbbbbbbbbaaaabbbbbbbbbbbbaaaafbfbfbfbfbfbfafa00000000000000001f1f1f1f1f1f0f0f111111111111000015151515151505051111111111110000
|0,5=>0xffffffffffffff00ffffffffffffffffffffff00ffffff000000ffff0000aaaa0000ffff0000aaaaffffffffffffffffbbbbbbbbbbbbaaaaffffffffffffffffffffffffff00ff00333333333333002233333333333300220000000000000000ffffaaaaffffaaaa00aa00aaffffffff00aa00aaffff00aaffffffffff0fff0fffffffffff00ff000000000000000000ffffffffffff00aa5555555555550000555555555555000011111111111111111111111111110000ffffffffffffffffffff00aaffff00aafffffffffffff0f0fffffffffffff0f000000000ffff0f0f00000000ffff00000000ffff00000f0f0000ffff00000000
|0,6=>0xffffffffffffffff0000ffff000000aa0000000000000000eeeeeeeeeeeeeeee00000000ffffffff00000000ffff00aaafafafafafafafafaaaaaaaaaaaaaaaa00000000555505050000000055550000ffffffffffffffff333333333333222233333333333333333333333333330000fffff0f0fffff0f0fffff0f0fffff0f000000000555550500000000055555050fffffffffffff0fafffffffffffff0fa00000000ffffaaaa00000000ffffaaaaffffffffffffffffffffffffaaaaaaaa00000000ff55f05000000000ff55f05000000000ffffffff00000000ffff000033331111333311113333111133330000fffffffffffffafafffffffffffffafa
|0,7=>0xffffffffffffffffffffaaaaffffaaaaffffffffffffffffff00ff00ff00ff00ffffffffffffffff55555555555500000000000000000000bbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaabbbbbbbbbbbbaaaa00000000000000001111111111110000ffff0000ffff0000ffffffffffff00aafbfbfbfbfbfbfafafbfbfbfbfbfbfafa00aa00aa00aa00aaffffffffffff00aa000000000000ffff000000000000ff00ccccccccccccffffcc00cc00cc00ff0055555555555555554444444444444444ffffffffffffafafffffffffffffaaaa00000000000000003333333333330000333333333333333333333333333322220000000000000000ffff00aaffff00aa
|0,8=>0xff00ff00ffffffffff00ff00ffffff00ffffff0fffffff0fffffff00ffffff0000000000fafafafa00000000fafafafafafafafafafafafafafafafafafafafaffff0000fffffafaffff0000fffffafa00000000555555550000000055550000ffffffff00000000ffffffffffffaaaaaaaaffffaaaaffffaaaaffffaaaaaaaa555555555555555555550000555500000000ffff0000ffff0000ffff0000aaaaffffffffff00ff00ffffffffff00ff0000000000000000000000ffff0000ff0055550505555505055555000055550000ffffffffffffffffffffffffccccccccffffeeeeffffeeeeffffeeeeffffeeee0000000000000000ffffeeeeffffeeee
|0,9=>0xffff0000ff000000ffff0000ff000000000000000000ffffffffffffaaaa0000000000000000ffffffffffff0000ff00ff00ff00ff00ffffffffffffff00ffffffffffffffffffffffffffffaaaaff33ff33ff33ff00ff33ff33ff33ff00ffffffffffffffffffffffff00aa00aa000000000000fafa000000000000fafa00000000fffff0f000000000fffff0f0ffffffffafafafafffffffffaaaaaaaa0000ffff0000f0f00000ffff0000f0f0fffffffff0f0f0f0fffffffff0f0f0f0aaaaffffaaaafafaaaaaffffaaaafafa0000000000000000555555555555000011111111111100001111111111110000ffffff00ffffff00ffffff00ffffff00
|0,10=>0xfafa0000fafa0000fafa0000fafaffffffffffffffffffffccccffffcccc0000000000000000ffffffffff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x4030602281d080306022804070201000a08070602270a0d0706020104250c06240a0d07021613231d22211a130a20041b1a130a0407021f1e0a1d1c071a130a041b1a13190a0d0702161318170702161315140407130e0a040713120a0803060211040c06051004070f0e0a0d07060201040c060b0a09080706050403020100
|1=>0xa080706022815360807062f0a1d083a061a0a200d03021a13040c06240a3904071a13380a1704071a13373604071a350a1d340602130a0d0c3306021a04071a13320a2b040702162a3104071a130a04070230130a0403060211131d0d21021613040c0602050a1d0c062f2e0a040706132d0a04030702162a0407130e000a29
|2=>0x3e133d040706134e4504074d130e0a0407131e4c0a0407064b130a2b040216134a04070643490a04070605131004074813470a04070643460a2b0421021613040706131e452b080c0602161d221a13440a04070643134204070613410a22071a133b0a04070602010a04070613400a1d3f06021a3e040702133d3c36071a133b
|3=>0x560407021a130a2207061a13550a0d07021a13180a2b0407021613001707021a13150a04211b1a130a0407021a2a0a04070213471e0a0407060213540a0d045307021a131d040306022813521d17071a130a0407062f13510a04071a1300500a04074f02131e0a08220c07061a0a1d0d0c060216130407060227130a04070602
|4=>0x1a133c2b045e0702161304070602285d0a2c040702131e0a0d0306021a1355040706025c130a040702161300150407131e000a391d0807062f0a391d5b0d03021a13040c061a13510a170d0702161304210702135a0a290d0706022f0a1d085906021a0a0407021a13580a36040706131e0a080d0c0306021a1d5722071a130a
|5=>0x421071a130a1d5b0d070216130407021a133c15040306021a3e6564040c0306021a080403070602281d080c061a0a391d0407061a13451704071a13630a080d0c07060216040c06022f620a1d07021a13180a0407060213610a20040702135a0a60080407062f0a220421071a130a5f1d0d07021a1304070213470a2b040702
|6=>0xa0d04210702161304070602136a0a360407062f130a040c07062f2e0a29041b061a130a1c1704071a130a1d081b061a130a04070643130a391d043a061a130a14040702133d0a662004071a130a1d640c06021a0a2c04070213690a2907061a132e0a040748131e000a040307021a2a0a2b040706022813080407062f670a66
|7=>0x43130a0407021372000a0407060213710a1d0d021a134a0a1d0470021a130a0407060211130a0407021a136f0a040706026e5d0a36040c061a130a2b040c06021a3e5b04070213690a04070613461e0a0407021a136d0a0434070602130a1d0807061a6c0a0d0403021a134a0407061a136b0a1d04211a130a392b0407021a2a
|8=>0xa1d041b06131e0a043f0306021a13043a0c07062f0a040702131e3c0a290d0306021a131d080c0602160a04070602010a141d0d03021a13043f0706021a3e2004071a130a3929040706026e0a08070602240a080d07060228040702131e760a04070275131e0a1d0d0706021374730407061a130a1d04071a134c0a04070648
|9=>0x6021a3e0407060205130a040c060216136204070602137a0a790407021a130a1c04071a130a1d04210216130a0407067843130a1d3f06021a130a1d080c06021e0a2204071a13440a770407021a130a5f2b0407021a131d04070213470a520407131e000a2c2b04070216135f040307021a13365704071a130a2b080706022f
|10=>0xd040c07060216131d0407021a133c0a047f030706021613080d0706021613040c0706026e0a1d0d0c06021a130a04077e02131e0a0407061a13510a1d04030602131e0a040706021a137d0a2204071a13000a040706027c130a143604071a130a040706134e0a3904070624130a3904070678131e0a040706027b130a1d0803
|11=>0x7061a13650a391d0406021a13870a040706021a13860a0407021a13840a040307021a133c1d04070602133d0a1d040702131e000a045e0307021613040706023e131e0a0407061a13830a2b0407021a13000a820407021613000a0407060226130a1d040c061a130a390407021a134a0a5f0407021a130a04800706022f130a
|12=>0x49007021613600407061a130a2b045e07021a130a1d0407060228130a5b0d040307021a1304078f021a130a048e1b071a130a170468071a130a60290407061a130a0804590706021a0a048b07061a130a040706021a138a0a170d07021a130a89040706021a130a0407060213690a040706021a88130a521d04071a13000a04
|13=>0x7068c131e0a1d040306022f130a2b04070602131e0a0d0706021a13550a1d1707021a130a1d5b0d07021a130a08040c07061a0a39040706022f650a040706021a13920a080d0c0706021a0a1404071a130a39040307060228130407060213910a0d0407021613002908040706022f0a1d040c06022f0a36041b07061a130a0d
|14=>0x134e0a040306021a13650a990407021a130a040307060213690a96080407061a130a08041b07061a130a040706021a3e650a040c0306021a3e1d0407061a13980a04071a1300970a64040c0706021a0a040307021a13840a360407061a130a1d040c06021a3e0a96220407061a130a0407061a93130a0407061a13550a391d04
|15=>0x130a9e040706021a130a1404070216130a5f1d0407021a130a2b040c06021a130a040706131e0a39201d0407021a130a040706021613650a2b040706022f130a2b0407060216130d0407021a134a0a9c0407021a130a9b040706021a130a220407062f130a1d040706026e130a0407062f13950a04079a02131e0a2904070602
|16=>0xa04071a134c0a142b0407021a130a1d080c06021a0a2b040706021a3e130804030706021a3e1d04071a13000a3904070602133d0a1d640706021a130a04070602133d1e0a043f0706021a130a0407021a13760a145204071a130a14040702131e0a601d0407061a130a08040c070602160a2c040307021a130a521d040c061a
|17=>0x13000a29040706021a130a1d080706021a130a940490071a130a141d0407021a130a8504070216130aa00407021a130a04590706021a130a045e0307021a130a0d040c0706021a130a047f030706021a130a080d0706021a130a94040c07061a130a0407021a139f0a040706021a135d0a040307021a13000a1d040702161300
|18=>0xa291d040706021a130a1d0407068c1a130a1d04070602131e0a220407061a130a04030706022f130a1d0407060216130a9d040706021a130a0407060213740a04071a13000a390407061a13a20a08040706021a3e0a1d0407021a13000a090407061a130a08040706022f0a04a107060216130a64040706021a130a9404071a
|19=>0x40706021a130a0407061a130a391d040706021a130a850407021a130a04030706021a130a040706021a3e130a04077e021a130a040706022f130a04070602131e0a08040c0706021a0a140407021a130a0407060228130a1d040706021a3e130a0407021a133c0a0407021613000a2b04030706021a130a04070602281613
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x23501e50195014500f500a500550005
|5,0=>0x1776171616b6165615f61596153614d61476141613b6135612f61296123611d61176111610b610560ff60f960f360ed60e760e160db60d560cf60c960c360bd60b760b160ab60a5609f60996093608d60876081607b6075606f60696064505e60586052604c60466040603a6034602e60286
|6,0=>0x332732b7324731d7316730f7308730172fa72f372ec72e572de72d772d072c972c272bb72b472ad72a6729f72987291728a7284627d7276726f72687261725a7253724c7245723e72377231622a7223721c7215720e7207720071f971f271eb71e471dd71d761d161ca71c371bc71b571ae71a771a071997192718b7184717d7
|6,1=>0x4ee74e774e074da64d374cc74c574be74b774b074a974a2749b7494748d7486747f74787471746a7463745c7455744f64487441743a7433742d6427642074197412740b740473fd73f673ef73e873e173da73d373cc73c573be73b773b073a973a2739b7394738d7386737f73787371736a7363735c7355734e7347734073397
|6,2=>0x526751f75187511750a750374fc74f57
|7,0=>0x70a770286fa86f286ea86e286db76d386cb86c476bc86b486ad76a6769f7698769086897681867a7673766b8663865b8654764d7646763e8636862f76278620761886117609860185f985f185e985e275db75d385cb85c475bc85b575ad85a5859e7596858f758875808578857085688561755a7552854b7544753c8534852d7
|7,1=>0x87f88796871886a7862885a8852884b7843883b8833882c7825781e7816880e880687fe87f687ef77e787df87d877d087c887c087b977b187aa77a2879b7793878c7785777d8775876e7766875e8756874e8747773f8738773087288721771987118
|8,0=>0x9bd79b589ae79a7799e999779907987997f8976996e8966895f7957894f8947894079397932792a8922891b7914790c890488fd78f588ed88e678de88d778d078c888c088b798ae98a6889e8897788f88878
|9,0=>0x9f179e989e279da89d289cb79c47
|10,0=>0x9f87
|_,_=>0
def wAt:=mkWire dB 163 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x70443419070441c29040a410291a0a4100106138101d04074802b17074100106138184e0d074102907004184e07394082a2c130ac191d0a4101d1e004746b06138101d03004184e1a3e4101d0613810e5020a8746b04074384f1e394746b020a8101d2c130ac190d07410291a0a490290713474bc04074684d1a0a4b04c2b064100d070a4984d040a47458070446829
|1=>0x75b834192c130ac191d0a4101d07004184e1a13410960c0241c4d1e0a4101d080a4104d1d0a4101d2c130ac19040341c29086881c09070443419040c81c4d043e4284d1a3e4104d070a4082a04074104d07135802829024744d0407410291a0a40c13070a4684d290241c2104134502b1d0641c111e004746b06138101d030646829040341c2904074744f04074082a
|2=>0x41341c4d0757878011d1ac184e04074184e04074ac190d07410291a0a4ac1904034341d040a434300713410290c394082a1d134101d04074104d0713468292613474580407468291d064101d040a41c290d0c01c4d040a4104d1d2f01c111a134584d040a4104d1a0a4101d07044584f00394082a06138101d075b874a01a3e44c290d07410295213c101d020a81c11
|3=>0x1a0a41c4d020a8101d5b07c3419040a4502b1d064101d810ac1cbd1a1341029071346829000a4184e040740c4d070a46829040a4104d1a0a4bc2b07134684d1d1ac1829040746c1307394082a1d1ac1c290407554291d13c101d0613810e5020a8290e1e134746b04074082a1d2f0101d0704490291d2f0101d1a13488010613810e5020a834300713410291d1ac101d
|4=>0x6138a4091d134101d0c0ac1c4d078d4123202134200e070a4104d040a410010613811650c0ac1c4d2b1ac742904074544d070d810291d024184e04074082a040c81c4d0313c1c296407c10f9130a6140f070a41019070a428010613878291d1ac101d1d1ac184e040746829030641c291d1ac4c29040746c4f07394082a1d0a4184e04074184e0416468291d160101d
|5=>0x1d1ac101d1d13c1c11040741001061381c110d0641029020a8104d07134684d040c81c4d1d3ec4c290407410291d064082a04074bc29070a4684d1e13c746b04074184e040a468291a1341c2104134684d07134101d1b0441ce5020a86829040a41c1929024744d040740c19040341c291a3e44c29040743419070a4102906624100e070a46c1907394082a070241001
|6=>0x4394082a04074bc2b1a134684d9407c1009061e4746b04074a46b1d134101d040c81c4d170a4100106138ac6b040341c2908394104d020a8104d07394082a040c81c4d130a41c4d070a4763202134101d06139a0130702410f90a136140f070a410192207410e5020a8101d2213410e5020aa544d9407c10091d13c082a04074746b02134101d040741c291a1347429
|7=>0x130a478291d1ac101d0d0c01c4d040a475fa060a4101d1d02474190407474191d1ac101d29024744d04074104d0713468292b064100d070a4740907134101d290ac744d0407468291d064101d140ac741904074341d040a4746b020a8101d1d004184e040741032071346829040341c291a134341d040a46829075b83419040a674191d0ac101d1d3e44c2904074684d
|8=>0x4074200904134104d1a1341c591a0a410f9130a4184e04024744d04074104d0704410090706474190407410191a0a6142b04064302b071340c19070a41c4d040a40c4d070a4104d040a41c4d04026141f040641c22041341c2906138682906138101d00394184e020a874191d0a4101d04074104d07134742904074104d070a4082a06138101d1e0a4746b0407410f9
|9=>0x20a8101d040641c29130a418291a134746b04074104d07134741904074bc291a1344c2904074280106138184e1a0a4100d070a4584d1a0a4744d04074084d04074746b0407410e5020a81c291a134101d1a0a4742b04074584f1a0a4184e020a81e3202134104d0a134184e
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x51400000000000000000000000000000000000000000000000000f5000000000000000294000000005500000000000000000000500000000000000000000000000000000000
|6,0=>0x7021b8800000006a400006820000662000064218885f316d0574000055214c8000000000013d0000130c48400004440000431104800000000000fc83b40000374000000000000000d840000d4431400000000b8c0000a90264089000008081e20744000000000006c80000000192
|6,1=>0xc540000000308cbe42f440000000b942dc8b342c480002bc80002b0caa20000a822910a0427109930000000255091424040002388000229000000000002244000218c00000000002108000208800000008021f8800000007a41e080000000744000000000000000000722
|6,2=>0x34500000000ce300000003344c94
|7,0=>0x628d873610d8135f8d7c25e4d7635ccd7035b4d6c15a4d66358cd603574d5a355cd543544d4e352cd483514d4234fcd3c34e893734d0d3134b8d2b34a0d253488d202474d1a345cd143444d0e342cd083414d0233fccfc33e4cf633cccf033b4cea339cce430000e13378cdb3360cd53
|7,1=>0x2143844e0e382ce09281ca043804dff27f0df937d8df337c0ded37a8de73790de13778ddb37649d6374cdd03734dca371cdc43704dbe36ecdb836d4db236c09ad36a8da73690da2267cd9c3664d972650d91364058d3
|8,0=>0x2672994a632984a5f2974a5b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b28e4a3728d4a3328c4a2f28b4a2b28a4a272894a232884a1f2874a1b2864a172
|9,0=>0x26f19b866d19b066b19a86691
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x1320000000008800000000040000000000120000000000500000000001d0000000000c80000000005900000000024000000000110000000000800000000003f0000000001f0000000000f400000000078000000000370000000001a8000000000a00000000004a00000000024000000000100000000000740000000003800000000018000000000080000000000280000000001000000000005000000000020000000000080000000000200000000000
|1=>0x32228000000181f00000000c002000000060000000000283f00000001117400000008888000000044080000000201e0000000100a000000008048000000040080000000127a8000000091dc000000048e800000002422000000011b00000000081000000000405000000002022000000010100000000052f8000000028ba00000000800000000003ba000000001d80000000008fc00000000458000000002240000000011000000000081000000000400
|2=>0x200002c800010000064000080000300000200647d0000100303e8000080100f000004000010000020000000000080323c8000040001640000200003000000802275000004003300000010000000000040000000000100000000000400000000001000000000004c8f20000002000000000008004000000039004000000100820000000800000000003a2e80000001c1f00000000ccfa0000000657d0000000327e8000000191f40000000c8f800000006455
|3=>0x8000323e8004000191f00020000c8ea0010000646d0008000322e8004000191540020000c89a00100002064000800000228004000000940010000e8fa000800070fe0004000322a800200011170001000048e8000800020340003000325e000070000164000300048aa000180004110000800302c800040009144000180208300000c0064550000400a00c0000140191f40000800c8fa00004006479000020032388000100191540000800c83a00004002454
|4=>0x80000103280240008011401000048814006400004770032000023a8014020195f400a0000c3fa004000064750018040332f800c004111300054000c9ee002000064770010000322a800800009080004000040ea002000000b40010000003a000800000074003000088ba001200064fd0008a04302e8004100191f40020800c8ea001040064690008200322a8004100191340020800c82a001040000410008000332e8004000193f40020000c9ea001000064b5
|5=>0x1800200064f540050003a7fa0028001d3f5000000000f842100000045208800000320804100391543040000c8ba1820000405f0c10000002e860000011174280000008bc1040200407c08140002a2f0400000191f4104000088ba0804200647d0402000321e82008001d1741000400c87a0800000645d0200000021200c0000190d40420000c84a021000044450088000333e8044000191d40220000c8da01100006065
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x7000000000000000000000000000004000000000900000c00000000021a00000000000000000000
|6,0=>0x200004a000022234f0000164e040b0006002e4b002b2331533c0000292a51001b00490000001d001500000034004e0000051c00000d0b000055004800000050001550000019004b001c000b150e231848050600000008001e39000400520b000000052600350002000028004f03000001003d3f03000b0b4c0000000502020b
|6,1=>0x300000100005809
|7,0=>0x78b6103a360e847115704244889656231f9d127c543460b813139c277f12613b658d8e2ba68f69242d5b6e8917b76d59674d5e5f30902ca42f23b1120586747280b3af6c82630f3e267f8b890a215711a51232119e5d201145a0917799376b76a733387ca1b9259f5a6f46007e6a921485
|8,0=>0x73b279bb5ca2819bbab4659368759594438766a97a64aabcac89b5ad8a978ca3ae9a41b0ab6583a87d
|9,0=>0x62937b985c7f47
|10,0=>0x40
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 9 roots_125 ops++addP pm 1 dzo_77_2 4 roots_77 ops++addP pm 2 dom_123 9 roots_123 ops++addP pm 3 dzo_118_8 7 roots_118 ops++addP pm 4 dom_119 9 roots_119 ops++addP pm 5 dzo_59_4 7 roots_59 ops++addP pm 6 dom_111 8 roots_111 ops++addP pm 7 dom_57 5 roots_57 ops++addP pm 8 dom_51 5 roots_51 ops++addP pm 9 dom_87 6 roots_87 ops++addP pm 10 dom_95 8 roots_95 ops++addP pm 11 dzo_121_4 6 roots_121 ops++addP pm 12 dom_116 5 roots_116 ops++addP pm 13 dom_59 7 roots_59 ops++addP pm 14 dom_118 7 roots_118 ops++addP pm 15 dzo_115_12 6 roots_115 ops++addP pm 16 dzo_114_4 5 roots_114 ops++addP pm 17 dom_91 6 roots_91 ops++addP pm 18 dom_121 8 roots_121 ops++addP pm 19 dzo_115_4 6 roots_115 ops++addP pm 20 dom_117 8 roots_117 ops++addP pm 21 dzo_117_8 6 roots_117 ops++addP pm 22 dom_49 4 roots_49 ops++addP pm 23 dom_103 6 roots_103 ops++addP pm 24 dom_114 5 roots_114 ops++addP pm 25 dom_50 4 roots_50 ops++addP pm 26 dzo_123_4 8 roots_123 ops++addP pm 27 dzo_91_4 5 roots_91 ops++addP pm 28 dzo_107_4 5 roots_107 ops++addP pm 29 dzo_93_2 5 roots_93 ops++addP pm 30 dom_27 4 roots_27 ops++addP pm 31 dzo_109_2 5 roots_109 ops++addP pm 32 dzo_119_8 8 roots_119 ops++addP pm 33 dom_77 4 roots_77 ops++addP pm 34 dom_43 4 roots_43 ops++addP pm 35 dom_107 6 roots_107 ops++addP pm 36 dzo_51_8 5 roots_51 ops++addP pm 37 dzo_87_8 5 roots_87 ops++addP pm 38 dom_93 6 roots_93 ops++addP pm 39 dom_86 4 roots_86 ops++addP pm 40 dom_102 4 roots_102 ops++addP pm 41 dom_115 8 roots_115 ops++addP pm 42 dzo_103_8 5 roots_103 ops++addP pm 43 dzo_125_2 6 roots_125 ops++addP pm 44 dom_109 6 roots_109 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_77_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_118_8_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_59_4_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_121_4_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_115_12_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_114_4_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_115_4_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_117_8_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_49 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_123_4_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_91_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_109_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_119_8_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_51_8_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_103_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_zo_125_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_109 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 9 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 57 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 57 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 136 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 136 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 113 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 113 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 41 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 41 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 7 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_127 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_127 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_127 roots_127 goal_127 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_127
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=S_127.noCircuit
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,128,132)] (by decide +kernel) lowS_187
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x550050000000000044000000
def gsh_86_8:=0x5500500000000000440000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 4:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (lower_slice_b (T:=gsh_86_8) [] (by decide +kernel) lowS_86)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0a00
theorem lowS_zo_219_4_27:Lower true dzo_219_4 roots_219 gzo_219_4 6:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,0,64),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_27)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000550050000000000044000000
def gsh_214_8:=0x550055000000000055005500000000005500500000000000440000
theorem lowS_zo_214_8_86:Lower true dzo_214_8 roots_214 gzo_214_8 5:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (lower_slice_b (T:=gsh_214_8) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00fa0000000000ee00aa00
def gsh_215_8:=0xff00ff0000000000ff00ff0000000000ff00fa0000000000ee00aa
theorem lowS_zo_215_8_86:Lower true dzo_215_8 roots_215 gzo_215_8 6:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_86)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000cccccccc00000000ccccc8c800000000cccc8800
def gsh_221_2:=0x33333333000000003333333300000000333332320000000033332200
theorem lowS_zo_221_2_77:Lower true dzo_221_2 roots_221 gzo_221_2 6:=lower_iso_b (d1:=dom_221) (r1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (lower_slice_b (T:=gsh_221_2) [(0x33330000000000003333000000000000333300000000000033330000,0,16),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_77)
namespace S_223
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,130),(3,11),(3,19),(3,67),(3,131),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(6,22),(6,70),(6,134),(7,15),(7,23),(7,71),(7,135),(8,9),(8,136),(10,11),(10,26),(10,138),(12,13),(12,76),(12,140),(14,15),(14,30),(14,78),(14,142),(16,17),(16,18),(16,80),(16,144),(20,21),(20,22),(20,84),(20,148),(24,25),(24,26),(24,88),(24,152),(28,29),(28,30),(28,92),(28,156),(64,65),(64,68),(64,80),(66,67),(66,70),(66,82),(66,194),(72,73),(72,76),(72,88),(72,200),(74,75),(74,78),(74,90),(74,202),(128,129),(128,130),(128,132),(128,136),(128,144),(192,193),(192,194),(192,196),(192,200),(192,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffff
def xsM:=roots_223.map (·&&&dom_223)
def gM:=goal_223&&&dom_223
def NN:Nat→Nat
|2=>1
|3=>11
|4=>39
|5=>124
|6=>233
|7=>177
|8=>78
|9=>10
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|2,0=>0x141ad
|3,0=>0xc29cda2e44782fe44bd6386b11ab851541c0ef730a3df0338c00186
|4,0=>0xdcc7fd7249d69f3c6701c1aafbc071bac2ba249da08e294c3f8e44b7a298707a16fd936ba706b54d6954166e565797754b5f4fb054758045e6e45ab43ae333ae0b371c22ef4f2755a2609e24e5517a851776015b64138e70539703eea03156025e1
|5,0=>0xf03cce811ae18a7d68a2cf95eca9a1c9044c6701c37efc2868b703eb6588b6155b322bafc0eaf741ac7d8aae42a9d19a9ad3a6489a2c9da22999fab49f3c79c6399bc3b98eaa94298941cb92ffe912ae910de8dcbc8c3ed891018774a8206180c9e808797d7197b1a879eb975fda72a9d6ca976b5c76a5436a3916752b66e5666d6a6521163896626255b33c5a9a35a59a59827587d555a235584854a8053858530af52bee4e99f4e78b4c0024982b447764388042dc24105240f293be353bbdc3979c3937b3934c364a734f8d331682ff3a2fc042f5462f0b02f06d2ce992cc2e2c9e42bc102ad842a567298e728b7326cb826361260ce201d21ef5a1d04c1925117a85172c416c5012eac1275c102020fa5e0f0fe0c5550c0910a8a90a6bc0880f0865d0808e058b804f09049f00452602973023a1
|6,0=>0x566d155e5055a23551df545d7531ae51754504414f4634e1374c4bd4a82049b2a4946648c5a479d147318458aa449b243503430b34303742c6b40a453fa693fa283f2fa3ea633e91f3e4a93c4933bc563a16439cbd39afa3913e38df538d2438b0f37f62379a73730736f7f353b93447c3323932a943235030b9d30539304cd2fe6d2fdb62f6072dac52b57c2aea1294ff294c22908f289d32896a287db281cc27d9b26a972694a25c7324b46249bb23d99239a122e0122898225e0224512232021b3320e76202e61f2ef1ef3f1ea751da991c51f1bc421b70f1ad491acf61a96e1a8a3187ca173ad1607115d8415cac1335e128ea11df511492108ee107310f3210eebf0ec050e7570e5240db3f0da9a0d4a90c90b09f0107ef007c4c0724c06d6105e9b05e0705a6d056f6052fc0455703d630373a025610228b01dbf00b4e
|6,1=>0xf6564f0a30f03cce98c9e8b49ddaaddbd9adaf42dab9ada82ad96c5d93a0d2b45cf4fdcdfa5cd5d9cb157c869dc866ec7e10c3396c243dbe7d5be38fbc3d6bc1bbb9f71b84fcb77c8b5fdab5d6ab41a2b383ab150db13d5ad627acfd3a912ea8573a255ca08159c5849c1c29bfa19b1559a1d697995973b09619b9589c93f7293621921368dc2c8cbda8cbbf8b1188b0c68aca58ac7f89fbe88b9988a9d8828c87f2c878bd86f94868b784a0a84980845a580a5e807217fdd07f1be7e2267dbe77ab9079896788787532e750e673e6d7306f7300a715766ec586dda36d7516b1cc6a8ac6756d6585d653e1638b8634b55ff5d5ee2f5d24a5bb9b5aab359f7959cc3586d558622
|7,0=>0x898598274e824537e4867e2237dbcc7ae297abac7a99777bee7765f774b8760ee75c22737a6736ff7008a6cc2b675d6666eb6595963d8862dbc6280d618bf6178b5d2c75c3cf56fc556a25546eb53bb5536e95204d51d63511bf50a3d504754fec74e9d24d1c84c71b4b6f84b1474781e476574656f464cd461fa4508c43fb9438614300a42dd242b5c4106e40e3b404df3f9803f5913ee683cfd43c4f63a2a0399173913e387513782c36f72352ac34f5332c1531c603065f2e93c2e7752e6522e5042de162b4e4291ce28a9d2896a27c81278c5275362749226a9025a6b254bd249bb20f3420d471ebf01deea1dcce1cdd81c1101a84f1a43a19fc718f0b1877f17dbf1726616bcd1695113b90138571239610aab103e70f45d0daca0a72c08e7e08dd50898b054c7051640432d0429e0318f0239101afe019de01143008ad
|7,1=>0xec7aaec3c5e4852e1b17e1a2ce15dce1194e100edf170df079dc8acd648bd3758d23d5d1a38d0c78cac88bfdb2bbfc2bade8ba6a4b8e97b41d5b1887b031eb0198ac304ab16daa6b1a6dbda6be1a5f01a43c4a271da1117a0b58a07b49cd26997e6985b294e2d9496193bc88f3af8eb5d8d68d8bd0d8ba8e8a71f
|8,0=>0xeb110e7a9be1d8ad66aed557bc9b19c71febf4c3b7f76b7c28b6248b06b1abff3a368da2cf79ce4f9818d971db94bc2949349448693d6693160907928f4038c5e2855f08543984913846fe81f947f0917ba5c78919757537051a6f5f868abe66fc9647d661341587c05742c4ae154a82d4757e3f6713f013386a3373803503d3351833356328042fff02e77f2e12b2d8b927a062704222e201c0f51b02f191fd18f0b18d59178f016a2a159e11461711fd80c8e30a550071d80601305aff0446300af2
|9,0=>0xe9ab7c1cdd7474a5bfd6561234791a45147259c124e651f14a
|10,0=>0x1730e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff0000fffffefe00000000fffffefe00000000fffffefe00000000eeeeeeeeffffffff00000000ffffffff00000000ffff000000000000ffff0000fafafafa00000000fafafafa00000000fafafafa00000000fafafafaffffffcc00000000ffffffcc00000000eeeeaa0000000000eeeeaa00ffffffff000000000000000000000000ffffffff0000000000000000ffffff0000000000ffffff0000000000ffffaa0000000000ffffaa00ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaafffffafa00000000fffffafa00000000fffffafa0000000000000000fffffafa00000000fffffafa00000000fffffafa00000000ffff0000cccccccc00000000cccccccc00000000cccccccc00000000ccccccccfffffffa00000000fffffffa00000000fffffffa00000000aaaaaa00ffffffff00000000ffffffff00000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00fffffefe00000000fffffefe00000000fffffefe00000000eeee0000ffffffff00000000ffffffff00000000fffffafa00000000aaaaaaaa
|0,1=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffee00000000ffffffee00000000ffffaaaa00000000eeeeaaaaffffffff00000000ffffffff00000000ffffffff0000000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffffffff00000000ffffffff00000000ffffaaaa00000000ffffaaaaeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeeefefefefe00000000fefefefe00000000fefefafa00000000fefefafaffffff0000000000ffffff0000000000eeeeaa0000000000eeeeaa00eeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeee0000fffffafa00000000fffffafa00000000fffffafa00000000aaaaaaaaeeeeeeee00000000eeeeeeee00000000eeeeaaaa00000000eeeeaaaafffffefe00000000fffffefe00000000fffffafa0000000000000000ffffff0000000000ffffff0000000000ffffff0000000000aaaaaa00fafafafa00000000fafafafa00000000fafafafa0000000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000fffffffa00000000fffffffa00000000fffffafa00000000aa00aa00
|0,2=>0xffffffff00000000ffffffff00000000fffffafa00000000ffff000033333333000000003333333300000000333333330000000033330000fffff0f000000000fffff0f000000000fffff0f00000000000000000ffeeffee00000000ffeeffee00000000eeeeaa0000000000eeeeaa00fffffffa00000000fffffffa00000000fffffafa00000000fffffafaffffffff00000000ffffffff00000000ffffaa0000000000ffffaa00ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaaffffffff00000000ffffffff00000000eeeeaaaa00000000eeeeaaaacccccccc00000000cccccccc00000000cccc000000000000cccc0000ffffff0000000000ffffff0000000000aaaaaa0000000000aaaaaa00ffffffcc00000000ffffffcc00000000ffff000000000000cccc0000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000033333333000000003333333300000000333300000000000033330000ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa00000f0f0000000000000f0f0000000000000f0f0000000000000000
|0,3=>0xafafafaf00000000afafafaf00000000afafafaf00000000aaaaaaaaffffbb0000000000ffffbb0000000000ffffaa0000000000ffffaa00bbbbbbbb00000000bbbbbbbb00000000bbbbaaaa00000000bbbbaaaa11111111000000001111111100000000111111110000000011110000fffff0f000000000fffff0f000000000fffff0f000000000fffff0f0aaaaafaf00000000aaaaafaf00000000aaaaafaf00000000aaaaaaaa000005050000000000000505000000000000050500000000000000000000ff00000000000000ff00000000000000ff00000000000000ff00ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aa00110011000000000011001100000000001100110000000000ff00ff000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0afffffff000000000fffffff000000000fffffaf000000000fffffaf000000000000000000000000000000000ffffff0000000000ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ccccccccfffffafa00000000fffffafa00000000fffffafa00000000fffffafafffffffa00000000fffffffa00000000fffffffa00000000ffffff00
|0,4=>0x5555505000000000555550500000000055555050000000005555505005050505000000000505050500000000050505050000000005050000eeeeaaee00000000eeeeaaee00000000eeeeaaaa00000000eeeeaaaa3333333300000000333333330000000033332222000000003333222205050505000000000505050500000000050505050000000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffaa000000ffff000000000000ffff000000000000ffff0000000000000000ff00ff0000000000ff00ff0000000000ff00aa0000000000ff00aa0005050505000000000505050500000000050505050000000004040404fffffafa00000000fffffafa00000000fffffafa00000000f0f0f0f0ffffffaa00000000ffffffaa00000000ffffaaaa00000000ffffaaaa00ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aaffeeffee00000000ffeeffee00000000ffeeffee00000000ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffff00ff00000000ffff00ff00000000ffff00aa00000000ffff00aa0000000000000000fffffafa000000000000000000000000fffffafa
|0,5=>0x5555555500000000555555550000000055555555000000004444444400ff00ff0000000000ff00ff0000000000ff00aa0000000000ff00aa0000ffff000000000000ffff000000000000aaaa000000000000aaaafafafafa00000000fafafafa00000000fafafafa00000000fafa000000000f0f0000000000000f0f0000000000000f0f00000000ffff00000000afaf000000000000afaf000000000000afaf000000000000aaaaf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000fefefefeff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aa00fffff0f000000000fffff0f000000000fffff0f000000000aaaaa0a000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aafafafafa00000000fafafafa00000000fafafafa00000000c8c8c8c8ffffffcc00000000ffffffcc00000000ffffffcc00000000ccccccccffffffaa00000000ffffffaa00000000ffffffaa00000000ff00ff00ffffaaaa00000000ffffaaaa00000000ffffaaaa000000000000000033331111000000003333111100000000333311110000000033330000eeeeeeee00000000eeeeeeee00000000eeee000000000000eeee0000
|0,6=>0xffff000000000000ffff000000000000ffff000000000000aaaa55555555000000005555555500000000555550500000000055555050000055000000000000005500000000000000550000000000ff00ff00555555550000000055555555000000005555555500000000000000000000fafa000000000000fafa000000000000fafa000000000000fafaffffffff00000000ffffffff00000000ffffff0000000000ffffff00ffffffff00000000ffffffff000000000000000000000000eeeeeeee00bb00bb0000000000bb00bb0000000000bb00aa0000000000bb00aaffff00ff00000000ffff00ff00000000ffff00ff00000000ffff00aaeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeaaaacccc444400000000cccc444400000000cccc444400000000cccc000000000000000000000000000000000000ffffffff00000000eeeeeeee0000000000000000fffffffa000000000000000000000000fffffffa00000000000000000000000000000000ffffaaaa00000000ffffaaaaffff0f0f00000000ffff0f0f00000000ffff0f0f00000000ffff000033330303000000003333030300000000333303030000000033330000
|0,7=>0xff00000000000000ff00000000000000fa00000000000000fa0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00bb00bb0000000000bb00bb0000000000bb00aa0000000000bb00aa00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000fffffff0ffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaacccccccc00000000cccccccc00000000cccccccc00000000cccc00000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000fffffafa00000000000000000000000000000000eeeeeeee00000000eeeeeeee4444444400000000444444440000000044444444000000004444444455555555000000005555555500000000555555550000000055555500cccccccc00000000cccccccc00000000cccc888800000000cccc8888ffffcccc00000000ffffcccc00000000ffffcccc00000000ffffccccffffffff00000000ffffffff00000000cccccccc00000000cccccccc0000ffee000000000000ffee000000000000ffee000000000000ffeeeeeeeeee00000000eeeeeeee00000000eeeeeeee0000000000000000
|0,8=>0xffffffff00000000ffffaaaa000000cc00000000000000cc00000000000000cc00000000cccccccc00ff00ff0000000000ff00ff0000000055ff00aa0000000055ff00aaff00ff0000000000ff00ff0000000000ff00ff0000000000ff00aa0033333333000000003333333300000000333333330000000033333300ffffffff00000000ffffffff00000000fffff0f000000000fffff0f0ffff555500000000ffff555500000000ffff555500000000ffff0000bbbbbbbb00000000bbbbbbbb00000000bbbbbbbb00000000bbbb0000bbbbbbbb00000000bbbbbbbb00000000bbbbbaba00000000bbbbbabadddddddd00000000dddddddd00000000dddddddd00000000ccccccccafafafaf00000000afafafaf00000000afafafaf00000000aeaeaeae0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00aa0000ff00000000000000ff00000000000000ff00000000000000aa00cccc0c0c00000000cccc0c0c00000000cccc0c0c00000000cccc0000
|0,9=>0xff00ffff00000000ff00ffff00000000ff00ffff00000000ff00ff000000ff00000000000000ff00000000000000aa00000000000000aa00ffffafaf00000000ffffafaf00000000ffffafaf00000000ffffaaaaffffff0000000000ffffff0000000000ffffff000000000000000000ffff000000000000ffff000000000000ffff000000000000eeee000000aa00ff0000000000aa00ff0000000000aa00ff0000000000aa00aa0f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0af0f0f0f000000000f0f0f0f000000000fffffafa00000000fffffafa0000000000000000f0f0f0f0000000000000000000000000fffffafa3333003300000000333300330000000033330033000000003333000000005555000000000000555500000000000055550000000000000000ffff0f0f00000000ffff0f0f00000000ffff0f0f00000000ffff0a0affffffff00000000ffffffff000000000000000000000000ffffaaaa000000000000000000000000000000000000000000000000ffffff00eeeeeeee00000000eeeeeeee00000000eeeee0e000000000eeeee0e033330033000000003333003300000000333300220000000033330022
|0,10=>0xcfcfcfcf00000000cfcfcfcf00000000cfcfcfcf00000000cccccccc33333333000000003333333300000000333333330000000022222222fffffffa00000000fffffffa00000000fffffffa00000000fffffffa33333333000000003333333300000000333333330000000000000000bbbbbbbb00000000bbbbbbbb00000000bbbbbbbb00000000aaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffff003333333300000000333333330000000032323232000000003232323255555500000000005555550000000000555555000000000055555500fefefefe00000000fefefefe00000000fefefefe00000000fefefefeffffffff00000000ffffffff00000000fafafafa00000000fafafafa00ff00ff0000000000ff00ff0000000000fa00fa0000000000fa00faff33ff3300000000ff33ff3300000000ff33ff0000000000ff33ff00ffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaaffeeffee00000000ffeeffee00000000ffeeffee00000000ffeeffee0000eeee000000000000eeee000000000000eeee000000000000eeee000000ff00000000000000ff00000000000000aa00000000000000aa
|0,11=>0xcccccccc00000000cccccccc00000000cccccc0000000000cccccc00ffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffccffffffff00000000ffffffff00000000ffffffff00000000ffffaaaaffffffff00000000ffffffff00000000eeeeeeee00000000eeeeeeee00ff00ff0000000000ff00ff0000000000ee00ee0000000000ee00ee33333232000000003333323200000000333332320000000033333232333333330000000033333333000000003333330000000000333333000000ffff000000000000ffff000000000000ffff000000000000ff000000ffff000000000000ffff000000000000fafa000000000000fafa4444ff44000000004444ff44000000004444ff44000000004444ff4400ff00ff0000000000ff00ff0000000000ff00ff0000000000000000000000000000000000000000000000000000000000000000eeeeeeee55555555000000005555555500000000555555550000000055550000ffff00ff00000000ffff00ff00000000aaaa00aa00000000aaaa00aa00ff00fa0000000000ff00fa0000000000ff00fa0000000000ff00faffffffee00000000ffffffee00000000ffffffee00000000ffffffee
|0,12=>0xfffffff000000000fffffff000000000fffffff000000000fffffff0ffffffcc00000000ffffffcc00000000ffffffcc00000000ffffffcc333333330000000033333333000000002222222200000000222222223333330000000000333333000000000033333300000000003333330000ee00ee0000000000ee00ee0000000000ee00ee0000000000ee00eeffffffff00000000ffffffff00000000ffffcccc00000000ffffccccffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffaa33332222000000003333222200000000333322220000000033332222f3f3f2f200000000f3f3f2f200000000f3f3f2f200000000f3f3f2f2000000000000000000000000000000000000000000000000ffffaaaa
|_,_=>0
def sP:Nat→Nat
|0=>0xa0d021a161d0d022724070d1f15180a091a081d231c0d19280a1c0d19151d0d020e161d0f020508070f020516030d0c27260a1c1f25241d1c0d0c151d1c1b1a1d230d0216221d1c0d0521120d02151d201c1f1e1d1c1b1a070d19180a021716030d0215140d051312110508100f020e000d0c0b0a0905080706050403020100
|1=>0x351d34090508241d1c330d1f150a310d02151d1c1b0524070d0c05131d11020508070f020500162b0905081d1c060521031c291a070306023205081c311b1a1d0f020516083006052103302f05241d0f02162e030217242d03111f2c080a0d02242207060205081d2b2a05080a1c1b1f151d0d1f15260a1c290508070d0c2622
|2=>0x290d02053f1d3e1f3d240a0311021f083c1d0f02051603291f05131d03310f0205081d090d1f05241d1102052107030f021a242d033b091a080a031c1b1f1a1d0611020521030d02053a241d1c0d24221d23060d0205241d0d0205241d3911020c082e1d111a08381d231b111f1a371d11361f1a081d1c291a1d23031c0d0524
|3=>0x81d1c111a081d233b111a08441d1c0605241d031c311b1a0a034a0d1f05241d0602320524030d021f151d491b11481f1a1d11020508471d11024605081d310d0227241d452a1f05080a310f020521030d0224221d2d111f15440a03290d021f151d1b110205240711431f05081d0d420205242d41111f1a081d1c3140291a03
|4=>0x905080a0311021a081d2d3b0d1a08440a110205240703111f5008440a0d1102052112091f244c0a030d02244f221d110c05131d0311021f17081d110205084e1d3b4a05241d031c29053f1d033b0d4805241d111f4d440a031c1b1f244c1d110508371d4b091f1a081d310d0227080a1b091f1a0a031c1b05241d231c312905
|5=>0x5241d3b0d02151d1c0d1f54241d0d0224221d200d110219280a09110c05081d310d02150a030d020516241d11531f05081d1c0d0c27080a34091a080a03090508241d23310d0208220a1c1105081d122f060205241d060205081d0d021f0521520d11020c151d1c0d0c27241d1b111f1a441d310d0224221d11021f08511d2b
|6=>0x20c084c1d11021a081d203b0d0524581d1c0d1f15080a110508381d4b1c2905081d231b11021f151d0f020524570311020e161d030d1f2724260a111a08371d233b0d0215080a1c0d1f15241d2911020508071c31291a1d032a090c05080a3b0f021a081d1c0d053f241d45091f05081d11052156120311020555081d0d531f
|7=>0x5211d03110205245d1d230d11020c150a03111f27245e0a031c0d0c05241d1c0d0c27240a031b111f1a440a03110205161d032a091f1a080a1c1b291f1a1d1c290524070311021a5d1d2311025c05081d1c311b05241d11020508070f5b020524030d021a241d200d0205245a1d1102591a081d0d0c05260a3b0d023d241d11
|8=>0x5241d633b11020524031c621f1a0a031c291f1a1d03290d0205241d233b11050824371d61110224601d031c11053f241d030d111f0524581d110c0521381d0331290d021a0a030d110c0508370a11021f05085f1d29111f0508441d111f1a08441d3b0d0224221d09111f0508241d110524561d230311531f05241d03311102
|9=>0x2a091f0508240a09110c05080a0311020555241d0311021f1a69241d3b0d020824220a311b110205241d110224601d2303111f244c440a030d110219150a03111f0524680a0367111f05241d031c1b291f05241d0d11021f3d241d11021f66241d03111f1a08381d1c0d0c05080a0d11020c05211d11021f65241d0311021f64
|10=>0x245e0a033b020524710a033b0d02150a031b11021f24221d11020c24220a0311021f05081d700d111f0524561d0d021f05246f1d3b110205246e1d116d1f05241d03111f0508371d6c3b0f021a241d036111020508241d11020c3205081d1b11021f1a081d29021f500a03110205216b1d031b111f05245e1d6a3b0d0205241d
|11=>0x1d03110c05260a03111f1a7708370a11050824441d231c0d0c24220a033b0d050824370a110224761d200345091f05080a030d110227241d23110205081d1211021f05751d031c0d1f0824220a111f7424440a03290d1f0508440a3b110524581d0311021f150a03730d020c72240a29110205240703090d1f0508240a311105
|12=>0x30f0205242d030d1f0524260a11050824381d237c110205241d031c0d1f15240a031b111f0524371d117b0205081d2341111f05240a031c2905241d23033b0d0224761d3b0d020521241d11021f08244c1d11027a24791d0311021a05081d2378110205241d030f11021f05086c1c0d1f150a03110205245a1d03110c052158
|13=>0x20c084c0a03110c05247f0a03110205247e1d03110c0521561d0311021f6905241d11021f7408241d3b0d021a241d1c0d1f0521241d1102591a241d031b11021f150a031c1b1f05241d1c111f1a081d1c1b1f27240a03111f1a0508441d111f3d7d240a033b110524561d030d110205241d4b29111f1a5e0a0311021a241d20
|14=>0x5241d1c0d1f3d240a0311020c74080a03110280241d23030d111f1a08370a0d11020524841d3111830205080a11025c05241d03111f0524821d0331110508440a03111f0524811d030d11020524351d110205240703110c0508371d1c314029052403111f3d24680a033b0d023d240a0361110280241d0311052435381d0311
|15=>0x1d1c0d05241d23290d021f27241d290f021f052103091f0508241d1102242e791d033b117b0205081d8911021f05081d110508446b0a0311021f88241d033b110287240a0361110224761d031c110508241d2311021f8605081d3b11050824441d1c311b05240a0311020585241d031c0d1f1a080a290f021f05081d1b11481f
|16=>0x205081d1c111f8e241d03111f05248d0a031b111f1a5e0a03290d021f27080a1102053a241d03118c1f05241d0311431f1a241d033b0d7b0205241d06110205241d03110205241d39030f021f052452033b0905240a031c330d1f24220a1c110524351d031c1b291f1a0a03111f0508441d6c11021f248b1d038a3b11021a24
|17=>0x111f244c5e0a031c0d0c7205240a110205081d4b94110205241d03291102053f1d039311021f05241d1c920d1f05241d111a24381d23033b0d7b0205080a3b110291240a03111f2490440a03111f7d24220a033b1b0d0205241d11020508241d2d3b0d050824440a8f11021f05241d111f0508381d6c1b110205241d23312911
|18=>0x98971102052403290f021f1a1d0311020524471d031c111f05081d6c11024605241d03110219150a0331110205081d11021f24961d0311431f05241d0311021f05081d950f11020c0521031c291f05081d111f74245e0a03090d1f05240a031c1b1f1a0a0331290d0205080a111f1a08371d11021f243c1d0311420205242d03
|19=>0x110205161d031c31291a0a0311021a241d2d03110205244e1d03021f9b05241d03111f0524131d03111f05249a1d03310d0205080a11021f1a5d1d11020524991d0311027a241d23031c0d1f05241d6c11021f05081d521b11481f1a0a03310d0227240a031c312905241d031c111a241d2303290d021f150a030d0205244f1d
|20=>0x311021f05245d1d3b1183020508240a0f11021f242e1d033b11050824440a033b021a24a10a03111f0524a00a032911021f05081d1102052124351d0311021f1a081d3b117b0205241d038911021f05241d03291183021f1a0a031b11481f05240a03119f021f05241d03111f05249e0a039d110205241d031c0d1f05241d9c
|21=>0x11020524791d038a3b11021a240a0311a4021f24220a03111f0524381d6c033129110205241d03111f0524440a031c110c7205240a03290d021f27240a03110205241d2d0311021f244c0a033b11a20205240a031c92111f05241d03091f0508240a033b117b0205080a0311021f0508241d493b0d027205240a111f0524561d
|22=>0x9c03110205241d4b033129110205080a0311023205241d230311021f150a031c11a70c05240a0311021f74240a030f11021f0508241d290d021f05080a110c0524a50a0311021f05212449033b0d7b0205240a0311020c24220a0311021f3d24220a0373111f0524440a031c0d1f7205240a0d021f05241d491c312905240a03
|23=>0x30f11021f05212403111f050824441d11021f05ab241d0341111f05240a03aa11021f05241d030d11021f27241d11020c0524a90a031c110205241d23031b111f0524440a031b11021f244c0a031c291f05a80a033b1b0d0205240a0311020508241d2311020c05a80a0311021f15240a030f11020c05241d0311021f05241d
|24=>0x1d03111f1a08370a0311020524841d03290d021f24220a03111f050824381d11021f05241d95031102af05241d2303117b021f05081d1c621f05240a030d11481f05240a031c291f05241d0311021f1a05081d98110205240a037311021f0508241d11021f0524ae1d03110205244f1d031c1b0d1f05240a03ad3b110205240a
|25=>0xa0311021f0524b31d0331110205080a031b11021f0508241d0d11020c05241d0d11020c27240a03111f0524b20a031c291f05080a032911021f05211d033b0f0205241d03110c0508440a033111020524b10a036a11021f24220a03110c0524381d030d11021f2708240a1c111f05241d6c03b011021f05240a033111020524
|26=>0x240a031c111f0508241d3b0d0205241d3b0d0227240a030f11021f24761d0329111f05245e0a030d11021f05241db51c111f05241d9c031b2911021f05241d3b117b8305240a0311021fb405241d031c291f1a0a030d11020c05080a730d021f0508240a0d0205244f0a0311020c0524220a0311021f05241d5203110c050838
|27=>0x24b90a0311021f0524b81d0311020c0524b70a031c110c05080a0311021f1a77080a0d11021f15240a0329110205241d230311021a241d2303111f24b60a030f11021f1a241d031c110c05241d03403b11020524036a0d11021f05241d0d11021f0824220a110224761d230311020521241d230311021f1a5d0a034111021f05
|28=>0x20c3205241d038a3b110205241d61110205241d03bd11021f05241d03117b831f05080a291183021f05080a3140291102052403111f1a08440a03111f1a24bb0a03111f1a24381d031c291f1a050a031c0d0c05240a0311020c0524ba0a031c0d1f0508240a0d1142021f05241d1b11021f05241d1b11021f27240a0311021f
|29=>0x1f05241d031c29021f1a050a0311021f7a241d0311021f08244c0a03314011020524031c111f1a241d0361110205241d23031c111fbf240a033111be0205240a0373110205241d23036a3b0d0205240a03111f052124581d03111f0524260a03311b110205240a031c1b291f05240a030d11021f3d240a03111f1a08380a0311
|30=>0xa031c11020c05240a0311021f05241d6c033b110224760a033b11020508240a03c31c111f05240a031b2911021f05240a030d11021f24220a031c111f05241d033b110524370a031102c105240a033b11a30205240a033111027205240a031c1b1f05240a031c111f1a080a03111f1a0508440a0311830205244f0a03c01102
|31=>0x5241d0373117b021f05240a032911021f7205240a033311021f05240a0311021f1a72240a031c111f1a240a037311021f72240a031c0d1f05240a036a0d11021f05240a0311021f1a77240a033b11021a240a03111f0524440a031c111f24760a032911be021f05240a0311be021f1a240a031c111f0508240a033b0d020524
|32=>0x1f1a24a10a031c117b1f05240a031c111f1a05240a031c0d021f05240a033b117b0205240a0311021f0524440a033111020c05240a038a3b110205240a0311021f05241dac0311020c05241d031c11021f05241d0311021f0508241d0d11021f24760a031183021f1a240a03111f1a0524380a031b11021f05240a0311021f32
|33=>0x830205240a0311021f0524c20a031b0d11021f05240a0311021f0524c60a033b11027205240a030d117b021f05240a0311021f1a24c50a0311021f24761d0311021f0521241d0311021fbc1a240a03c411021f05240a03111f050824370a0311021f27240a033b11be0205240a030d11021f7205240a3129110205240a031102
|34=>0x37311021f05241d03c311021f05240a03c811021f05240a03110205241d230311a2021f1a240a0311021f0524c70a0311021fbc05240a0311021f05245d0a032911021f05080a031c11021f1a05240a0331110205240a031c291f05240a0311021f0524a10a03110205244f0a036211021f05240a032911021f05241d033b11
|35=>0x11021f05240a032911021f05240a0311021f05241d030d11021f05240a0311021f7205240a031c111f05240a033b110205240a0311be021f05240a0311021f1a05240a03111f0524380a037311021f05240a030d11021f0508240a111f2476380a03117b021f05080a031c29021f05240a03c93b110205240a
|_=>0
def sO:Nat→Nat→Nat
|2,0=>3
|3,0=>0xad004e8023400fa006d002e80134007a002d000e80034
|4,0=>0x3b541d0a0e3506f2836541a8a0cf5065283154180a0bb505b282c54158a0a75051282754130a0935047282254108a07f503d281d540e0a06b50332818540b8a0575029281354090a043501f280e54068a02f5
|5,0=>0x134b098d84bac2576128b092d848ac23f611cb08cd845ac2276110b086d842ca21061053081183fcc1f860f9307b183ccc1e060ed30751839cc1c860e1306f1836cc1b060d530691833cc19860c930631830cc18060bd305d182dcc16950b1b057582aec15160a5b05158280a13a609a304b98250c122608e304598220c10a6082303f981f0c0f26
|5,1=>0x1e6b0f1d8782c3bb61dab0ebd8752c3a451cf30e618724c38c61c3a8e0586f6c37561b7b0da586c6c35d61abb0d458696c345619fb0ce58666c32d6193b0c858636c3156187b0c258606c2fd617c28bc985d8c2e6617030b6985a8c2ce616430b098578c2b6615830aa9854aa29f614cb0a4d851ac2876140b09ed84eac26f6
|6,0=>0x2c1b95f1caeae56f62b439585cab4e55372a639515ca7ce5377298394a5ca44e51b728ab1439ca0ee500727cb93c9c9d6e4e4726eb9359c99ee4c87260b92e9c966e4ac7252b9279c930c4926245b9211c8fae4767238311a988c6e45c722ab9139c88ee440721cb90c9c856e424720f310618822e40a7201b8ff1c7eae3ee71f3b8f8587b4e3d37
|6,1=>0x39bb9cc1ce54c724638eb9c59ce1ee7087380b9be9cde6e6ec7372b9b79cdaee6d1636539b0dcd78e6b6635831aa5cd44e69b734a39a35cd0ce67f733cb19cd8cd8e665732f3995dcca0e6497321398f18c6ae62e7313b9881cc32e612730631815cbfce5f862f8b97a9cbc6e5dc72eab9739cb8ee5c162dd396cdcb58e5a572cf396618b22e58a7
|6,2=>0x4793a3b191cae8de746bba341d192e8c2745dba2d1d15ae8a6744fba261d122e88a7441ba1f1d0eae86e7433ba181d0b2e8527425ba111d07ae8367417ba0a59044e81b740a3a035d00ce7ff73fcb1fc9cfd6e7e563ef39f5dcfa0e7c973e139eedcf68e7ad73d339e7dcf30e79173c5b1e11cefae77673b7b9da1cec2e75a73a9b9d31ce8ae73e7
|6,3=>0xa0775003a7e993e8c9ed74f33a77dd3b0e9d174e5b2715937ce9b774d83a6a5d344e99b74ca3a635d30ce98064bcba5c9d2d6e96474aeba55d92a2c94a74a1ba4f1d26ae92f64943a485d236c91474873241dd200e8f97
|7,0=>0x5f442f85d7b30bd275e542f0a17750bb285d5bae8e1738eb9575c73ae1a16fd0b7775b7c2d9e16c2cb5985a93ad2a1686eb3c759a42cb2164aeb1d858ac2c39d60eeb00757cbabc615d30ae1856cc2b49d5950ac2855dbaad1d5590aa4854ebaa56151b0a86753fba9e1d4e10a68853042965d4a4ea4b7521c28f5946b0a2d8512c2876142b0a0e7
|7,1=>0x6e3bb7059b730db276d5bb68e1b370d9476c643615dafb0d7676b8335a5dac30d5986a8c35261a830d398698c34ad9a48ed1c868abb4361a0b0cfe767b433bdd9cf0ce0766c43345d994ecc2865dbb2d1d9590ca4864ebb256191b0c85863f3b1ddd8e0ec688630bb16618a30c4a7621bb0ee1868ec2d76133b07a182d0c0f7603c2ffe17ef0bf07
|7,2=>0xf387798bbca61e430f1a7789bbc2e1e070efb8779c3bb1ddc90edd776b3bb3a1d8eeebf875bc3abe1d4f0ea0774c43a421d110e81773cc39c9dcd6ee63872e3b9521c990e45771f3b8dddc60ee297710c3869dc250e0b7701c37f1dbe90dec86f2bb779dbad0dce8
|8,0=>0x897cc4a1e242f11988893c42a220510fa8879443a661c310d988684c3222182f0b98858c42a62143109a78494422a2105107a8839441aa20c5105a88294412a2085103a8819bc0ae2048f01c880a4403220090ffc87f9cbfaa5fc50fda87e9bbf2e1f88efbb97d9c3eb1df4aef9e77cacbe361f0b0f7e77bb43dba1eceef5f87abc3d3a5e8d0f3f7
|8,1=>0x233d119778c7c461e22ff117788b7c459e22c0f15888a844522228111388
|9,0=>0x23d511e378edc474e2398f1c578dec46d6235cf1a68
|10,0=>0x11f27
|_,_=>0
def wAt:=mkWire dB 202 224 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2403444750a034280d0a034ec7411034280d1f114180d1112430741f24444490c1d0900d0a0347c9124034ec740a03414910a03444dd08020901524034202508114900d291d044910a034240d0924444dd08020a40d311d0a47d0a03490b53b1d07c45111d4280d240d4442124034280d0524408451112430741f24490750a03444490c1d0280d110347c91110849045
|1=>0xa034a40f1124414910211444910a03414910211584171f1d80847241d4280d02080900d110347c9102088280d24054900d0a034447d11034280d11374200824034a47d2724414341f244280d11024440d2903444910a034149102114900d311d0280d3b2447c451c0807c91240344409110349045050d0440d1f11408450a034909d0d050440d0903444dd080209015
|2=>0x11034c474291f444910a034440d113742008240349c911f11434141103468740a034280d0524444750a034907d24034280d0a03490152403468341103490450524430470a034447d11034280d0903444dd08020907d11374200824034a47d0a034a40d6105c448d1f1d8547d2427434140a034a40d1124408450a034084724054900d1f244900d11024440d110349075
|3=>0x11084440d0a0347c45241d4280d11024440d24114280d29034449102114900d0a03414910211490353b1d07c45111d4280d1c080900d11024440d11024909d0d050440d08114280d110347c451f114440d0a034909d0d0504409110348408241d4280d1c080900d021147c910924444dd08020307424034280d1f244440d0802c900d1a1b0a40d241141491241f4140d
|4=>0x2403408200a034901524034280d1c1dc280d11024440d0a034440d1f114ec740a034900d1f114280d240343414110347c4511034280d1112430740a0347c91291d0280d1f114dc4508020900d05244a40d11244084505244280d11024440d111d490750a034dc450a03420082403444750a0342045311d0280d3b2447c45241f4280d08020900d310ac840b241d4280d
|5=>0x249444760a03409740811c900d242d4ec740a0347c45291f444910524408453b1d0280d05244443124034440d1f244280d0811c90152403490760a034440911034900d291d044910a03490450a0349c9124114341411034280d110347c4505244a47411244280d1f1549c910d050440d0a034ec9124034900d0a034449102114349105244a40d11244084511034a47d
|6=>0xd050440d3b1d0280d1f1146c170d244440d7b05408911c1dc08450a03444dd08020900d02244900d1f114900d111d8280d05034440d1f1140886241d4280d11088900d0a034080d240347c45050f844750a0340822240347c45111a814911f11445120802c900d11244900d0a0347c86241d4280d0a0349015240347c450a03445b1241d8280d240549045020342045
|7=>0x242387c760a034a47d24114900d1f1d8280d2724434141103408451f2446c140d244440d2403444750a034440d24114900da602c300d1f24444760a034447d110341436110347c910d05c440d0802c900d05034440911034440d111d8280d291f44491021147c3e111d4280d052447c450d05c440d1102890760a034a47d11244280da302c20092403408451f2449045
|8=>0x1124408451b02034910a034449102114280d240341491621f4a40f11244900d05114280d0a034ec931f114440911034eded022447c45111d490750a034280d0802c900d24ac414760a03445110802c900d020f444750a034280d0d050440d1f1d8280d0d244440d1c24c449102114440d1f114900d1f1d8280d241f49072021149c910d050440d241f4280d1c1d0280d
|9=>0x111d4280d3b244900d1f114900d0a034280d110347c91050d07c910838c900d0211c900d112440845241d4280d1f11444750a034907d0802c900d3102c30451f244440d0a0347c910211c900d0d050440d1102490760a034280d3b2447c45080209015240347d0a021d4280d11244341711034280d240340847291d844910a034148d1f1d8280d0a034900924034a40f
|10=>0x310acec911f114083511034280d2403434171103414931f1d8280d1f1d8280d0811c90152403445110802c900d11024900d0a034440d0a0347c451f1143414110349016111d4280d1b02ca40d24114440d021d8280d0a034a40d112447c4524024080d1a1dc280d05244449105244084524034440d1f244900d11034ec931f114a47411244280d240347c910211c903e
|11=>0x24114c42b291f444910802c9015240340af21a034149124054280d0211c084511244149102114440d1f24430451f244900d11024440d1103408750a034442124034280d240d415aa1c03408454211c08750a03698470c0347c912403408451f244680f24054900d2427434141103444911f1d8280d052447c760a035d8e10524c08472405444750a034280d021147c91
|12=>0x2403414913b24c7c45291dc44910a0341491241140845050f044750a0346c1708114c42b3b2447c450a034149102114448d1f1d8280d056a0700d02114a47d112447c760a034440d1f1140884241d4280d1c080084524034a47d29034a40d11244084524224341711034084724054900d1f244280d3b034280d1f114448d1f1d8280d1121490750a034080d24024900d
|13=>0xa034089105114449105034700f02114140d05244149102114441505034440911034340911034680f0524414911f114200b2403408450524c081511244081505244084524034440d1f11408451f24490760a0347c450524c900d1f114709102114a40d1124434171103408450a0340820240347c451fc24a41711244ec911f114a40d11244084524034149102114200b
|14=>0x1f114a41711244349111034147202114140d1f114089111034680b05244280d0524c90750a034680d0524434151103420082403434141103408151f114140d11034a47d11244684705244900902114440905244440d0211408911f114200b2403430451f244ec0d1f11414760a034280d1f244280d02114900d0a034440d0524c90150203414910211c3491110341475
|15=>0x44910a034440d0503408451f114081505244084705114900d1103414930211c900924034904502114ec091f11414450a0349071021141471021147c760a034680905244201724034680d05244204724034904524034440905244ec911f114449102114446a05244ec931f114a40f1124444910a034080d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x4000000000000000000000000000000000000000000000000000000000000000000
|5,0=>0x9540000904000000000000000000000000000000008c400007d000006d00000000000000017400000000000000000000000001250000000044400000000000314075000000000940000000000004400000000000000000
|5,1=>0x15d400000000000000525000000000000001354000000000000000000000000130400000000000000493111400000004130f50000000000000000000f0400000000000ec40000dd00000000000000000000003340b940000000000000000000000000a90000
|6,0=>0x2dd00000000b3400000002c480000000b0100000002b4c0002a8ca7328d0a1200009e326cc97400000000000943244c000238c00000008a4000000021908241fcc00000000001ed077400000001d48000000072300006e400000001a9067318d0000000062100005f300005c30000000
|6,1=>0x421104440c4000000000000000000000000400c0003fc4fc33e100003dc4f343bd0ee10000000000000000000003a90e6400000003890e1100000000000de336cc0000000000000000035d0000350cd04000000000000000000cd30000c9400000000000c630000c242fccbb4
|6,2=>0x13a1000000000013640000000000000000013334bd0000000000000012e1000000000012b300000000001283491000048891e4000000046900000001191458c00044cd0f400000000000000000000000000000000000000000000010d243040000000000000000000000000000000
|6,3=>0x17645c916f3000000000000005ad1674000000058d15f457840005744000565156300015510000000548d4e452cc00000000000001474000146150913f34ed00000000000
|7,0=>0x87ce1c3864e1630002142000212283ce0d2828e073810e0228009fd37e8df827d4df327c0ded37a8de737949e32780dde27709d93758dd33740dce27309c93718dc337049be36ecdb836d89b336c0dad36a8da73690da13678d9b3660d953648d8f3630d89361c9843604d8015f4d7a3
|7,1=>0xb24ec63b0cec03af4eba3adceb43ac8aaf3ab0ea93a98ea33a80e9d3a68c000a5ce943a44e8e3a2ce8a1a1cc000a10e8139f8e7b39e4a7639d0a7139b8e6c29a4e66398ce62197ce5c3964c000958e533940e4d3928e473910e4138f8e3c28e4e3638cce30300022d38aca283894e223
|7,2=>0x34c3d24c000d1cb443d04f3e3cf0b393cd8f333cc4b2e3cacf283c94f232c84b1f2c70f193c5cb143c44f0e3c30b093c18f033c00eff1bf0ef93bd8ef33bc0eed3bacae83b94ee23b846de3b6ced83b54ed23b3cecc3
|8,0=>0xf34bcb2f24bc72f14bc32f04bbf2ef4bbb2ee4bb72ed4bb32ec4baf2eb4bab2ea4ba72e94ba32e84b9f2e74b9b2e64b972e54b932e44b8f2e34b8b2e24b872e14b832e04b7f2df4b7b2de4b772dd4b732dc4b6f2db4b6b2da4b672d94b632d84b5f2d74b5b2d64b572d54b532d44b4f2
|8,1=>0xfa4be72f94be32f84bdf2f74bdb2f64bd72f54bd32f44bcf2
|9,0=>0xfd07f31fc87f11fc07ef1fb87ed1fb07eb1
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x80800000000400000000001e8000000000e50000000007200000000038400000000140000000000890000000004200000000020800000000100000000000750000000003a000000000194000000000c200000000050000000000220000000000e00000000004a0000000002100000000010000000000060000000000280000000000d000000000048000000000200000000000a00000000004000000000018000000000080000000000200000000000
|1=>0x86000000000410000000002040000000010000000000065280000000208000000000c00000000004e4000000002500000000010100000000080200000000400000000001c2000000000c00000000005fe000000002e500000000170800000000a00000000004de00000000269000000001338000000009940000000048000000000200000000000e28000000006100000000029a00000000144000000000a08000000004240000000021000000000104
|2=>0x20004800000100010000000800000000002208d0000001104080000008328400000040608000000202a40000001008680000008041000000022002000000108050000000804000000004000400000020000000000080e10000000400a0000000200400000000c080000000048e40000000218200000001001000000008000000000024e10000000124000000000901400000004502000000020850000000100280000000800400000004000000000018a0
|3=>0x5167080000023039c0000010c0c000000084404000000421f3800000210390000001009ca00000080000000000301f3800000180bb4000000c0004000000482ed0000002417380000010439400000082018000000403e7000000201f2800000100f8c000000805de000000402e700000020172800000100a9c000000804da000000401e10000002007a8000001003bc000000801ca000000400e3000000200448000001001b40000008008000000040020
|4=>0x22057380000100a384000008041420000040086500000200000000000a001140000050000a000002400ed000001200368000008420100000042000000000200000000000b0172800000580394000002a15ca00000140ee5000000a01778000005003d4000002801ca00000140089000000900f68000004806b4000002401ca000001200cd00000088002800000400620000002000ca0000010000500000080001000000400000000001885ce000000c42e5
|5=>0x10000000000040801000000200000000000ac82f500000500060000002580fb4000012401da000008c82b5000004300be800002120bd40000108054a0000082018c00000410086000002080410000010102ba00000808159000004040000000020005a0000010000c2000007416e700000380076000001a0039000000d000c0000006018a10000030043200000180120000000c00000000005004e5000002723f3800001390f9c000009c05ca000004848e5
|6=>0x12020173800090000000000400805ce000200000ed0000a03017380004000180000020000442000090c42e500004842270800021b04b9400010d805ca000086804e40000418003280002000420000010000000000041602ed00002030773800010180b9c000080c058e000040004060000200010200001000001400008000008000021603e5000010b01728000085803b4000042805ce00002040480000010100fe8000080010000000400010400002000001
|7=>0x220000000001002020194008009805ce004000600420018102017a800c08100b9400440000408002020400860010102003380080810011c004001805ca001820402f7000604a017a800300d04bd40018068014a000c0100035000410a0173800200180008000842c05fa000408482f50002041007e800100d003f4000802905da000400402f500020020173800100100b94000800805c2000400400e100020020041000100100200000800001ca00040000065
|8=>0x8400062173840000100b9c200000005ce10000000000044100201f3822000310b9c110001085c4088000002e304400000170822000000814100000805ce040100002000200000010000800850118c040040801020200000048100c00050152804010020194013000805ee008408482f500420034172802100120bd401080090408008008602f500400414172802000320b94010000904000080000026500400000002001c00100194009040c0184004440402e5
|9=>0x3000109885ca508040402e528400020173922000500b94910000805ce480200002e120c00030172904100520b94820080905ca410000602e710000340052080001800294212c00805ce10840040205
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x10000000000000000000000000000000000000000000
|5,0=>0x200000d00037000000000098000000000000000010d00000000103e000002402000000000002480000001e0009400000000000000e88000000000c000000002000000000000000000000000000000f0005800010000000000009c00000000400008001e00000000004000000c0000000004d00000040000000443e000003200000000400000000000
|6,0=>0xd070713c00000000000000002900004594200004574600800000026c0c003e85000001180800000012c6c1e00000003434000aa1d0000000000004000a8000780017001405c0f0b800007e0f0019282003440000210007286282540c75048fc00000f01016000a800001f0f000c60e1a80000005684400002080000555785c00062f8c81000001440015002100006
|6,1=>0x5f9316a010000000005486000000281404003c0001e7c001040000008694c00000006807000095c173480000000029400000030000000000000560680000000025000000305c0000000107e000a84800005800000bd008002e2d0000068000000000001a0009c0010810041e0000000c2000d00000
|7,0=>0x15474b68d913f04c2b4b371c6c6519ec8a08622fc4a0f6543156de3d000389821aa90ca40a871d6533fa5cc11c3905c1a006a1a6242433031b2f67f05924cd0db2c0079598f42e6266384066e001741432782c938f13991d82a75dc50c9131811112d31b01039031445cb4b8242f8ba0d4d380500f500702ac018984771942970bc452f43dc2882a34008467120e2065
|7,1=>0x652c00050b7748a4ba01828bc412335a75ca28143b90e6727ac066746d35d3c01813fd3269821ae0e8e1430e228a0139222d2754384e0f
|8,0=>0x1166a7bbce5adf7dc853f2c674a4ecb984b55d927402d926fd842d21b1a7c498d8919546cda6c8fc6179277d42ddef573b59b0cf563151e70801b174db7cc59e929854a1910192c19cce8904addaa27924102a17dac4dec7
|9,0=>0x16c6c3bc54d6808f490d8dd
|10,0=>0x6b
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 45 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_219 9 roots_219 ops++addP pm 1 dom_85 5 roots_85 ops++addP pm 2 dom_222 8 roots_222 ops++addP pm 3 dom_86 4 roots_86 ops++addP pm 4 dom_198 4 roots_198 ops++addP pm 5 dom_159 9 roots_159 ops++addP pm 6 dom_95 8 roots_95 ops++addP pm 7 dom_207 8 roots_207 ops++addP pm 8 dom_77 4 roots_77 ops++addP pm 9 dom_221 8 roots_221 ops++addP pm 10 dzo_27_4 4 roots_27 ops++addP pm 11 dom_27 4 roots_27 ops++addP pm 12 dom_210 5 roots_210 ops++addP pm 13 dom_143 6 roots_143 ops++addP pm 14 dom_201 5 roots_201 ops++addP pm 15 dom_204 4 roots_204 ops++addP pm 16 dom_158 6 roots_158 ops++addP pm 17 dzo_77_2 4 roots_77 ops++addP pm 18 dom_215 8 roots_215 ops++addP pm 19 dom_203 6 roots_203 ops++addP pm 20 dzo_86_8 4 roots_86 ops++addP pm 21 dom_218 6 roots_218 ops++addP pm 22 dzo_91_4 5 roots_91 ops++addP pm 23 dom_206 5 roots_206 ops++addP pm 24 dom_91 6 roots_91 ops++addP pm 25 dzo_87_8 5 roots_87 ops++addP pm 26 dzo_93_2 5 roots_93 ops++addP pm 27 dzo_219_4 6 roots_219 ops++addP pm 28 dom_157 6 roots_157 ops++addP pm 29 dom_205 6 roots_205 ops++addP pm 30 dzo_214_8 5 roots_214 ops++addP pm 31 dom_199 5 roots_199 ops++addP pm 32 dzo_215_8 6 roots_215 ops++addP pm 33 dom_214 6 roots_214 ops++addP pm 34 dom_87 6 roots_87 ops++addP pm 35 dzo_205_2 5 roots_205 ops++addP pm 36 dom_220 5 roots_220 ops++addP pm 37 dom_151 6 roots_151 ops++addP pm 38 dom_217 7 roots_217 ops++addP pm 39 dom_93 6 roots_93 ops++addP pm 40 dom_213 6 roots_213 ops++addP pm 41 dzo_155_4 5 roots_155 ops++addP pm 42 dzo_221_2 6 roots_221 ops++addP pm 43 dom_195 4 roots_195 ops++addP pm 44 dom_211 7 roots_211 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_223 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_27_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_77_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_91_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_87_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_219_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_215_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_205_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_zo_155_4_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_zo_221_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_211 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_219 9 s (0,roots_219.map (·&&&dom_219)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_223 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_219 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_223==dom_223)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_223 gM v ys):RunD true dom_223 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_223 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 11 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 39 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 39 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 124 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 124 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 233 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 105 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 233 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 177 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 49 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 177 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 78 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 78 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 10 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_223 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z2 i (Nat.zero_le i) hi
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_223 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_223 roots_223 goal_223 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_223
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=S_223.noCircuit
theorem lowS_247:Lower true dom_247 roots_247 goal_247 11:=lower_slice_b [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,64,68)] (by decide +kernel) lowS_243
theorem lowS_251:Lower true dom_251 roots_251 goal_251 11:=lower_slice_b [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,16,18)] (by decide +kernel) lowS_249
theorem lowS_253:Lower true dom_253 roots_253 goal_253 11:=lower_slice_b [(0x3030303030303030303030303030303030303030303030303030303030303030,64,68)] (by decide +kernel) lowS_249
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005500550050005500440044000000
def gsh_246_8:=0x55005500550055005500550055005500550055005500500055004400440000
theorem lowS_zo_246_8_118:Lower true dzo_246_8 roots_246 gzo_246_8 8:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_118)
def dzo_50_4:=0x50005000500050
def gzo_50_4:=0x50004000400000
def gsh_50_4:=0x5000400040000
theorem lowS_zo_50_4_50:Lower true dzo_50_4 roots_50 gzo_50_4 4:=lower_iso_b (d1:=dom_50) (r1:=roots_50) (T1:=gsh_50_4) [(dom_50,4)] (by decide +kernel) (lower_slice_b (T:=gsh_50_4) [] (by decide +kernel) lowS_50)
def dzo_242_12:=0x5000500050005000500050005000500050005000500050005000500050005000
def gzo_242_12:=0x5000500050005000500050005000500050005000500050005000400040000000
def gsh_242_12:=0x5000500050005000500050005000500050005000500050005000400040000
theorem lowS_zo_242_12_50:Lower true dzo_242_12 roots_242 gzo_242_12 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_12) [(dom_242,12)] (by decide +kernel) (lower_slice_b (T:=gsh_242_12) [(0x5000500050005000000000000000000050005000500050000000000000000,0,64),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_50)
def dzo_242_4:=0x50005000500050005000500050005000500050005000500050005000500050
def gzo_242_4:=0x50005000500050005000500050005000500050005000500050004000400000
def gsh_242_4:=0x5000500050005000500050005000500050005000500050005000400040000
theorem lowS_zo_242_4_50:Lower true dzo_242_4 roots_242 gzo_242_4 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_4) [(dom_242,4)] (by decide +kernel) (lower_slice_b (T:=gsh_242_4) [(0x5000500050005000000000000000000050005000500050000000000000000,0,64),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_50)
def dzo_244_8:=0x1100110011001100110011001100110011001100110011001100110011001100
def gzo_244_8:=0x1100110011001100110011001100110011001100110010001100000000000000
def gsh_244_8:=0x11001100110011001100110011001100110011001100100011000000000000
theorem lowS_zo_244_8_116:Lower true dzo_244_8 roots_244 gzo_244_8 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_8) [(dom_244,8)] (by decide +kernel) (lower_slice_b (T:=gsh_244_8) [(0x11001100110011001100110011001100000000000000000000000000000000,0,128)] (by decide +kernel) lowS_116)
def dzo_230_8:=0x550000005500000055000000550000005500000055000000550000005500
def gzo_230_8:=0x550000005500000055000000550000005500000050000000440000000000
def gsh_230_8:=0x5500000055000000550000005500000055000000500000004400000000
theorem lowS_zo_230_8_102:Lower true dzo_230_8 roots_230 gzo_230_8 5:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_8) [(dom_230,8)] (by decide +kernel) (lower_slice_b (T:=gsh_230_8) [(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_102)
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,34),(2,130),(4,68),(4,132),(6,22),(6,38),(6,70),(6,134),(8,136),(10,26),(10,42),(10,138),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,48),(16,80),(16,144),(20,22),(20,52),(20,84),(20,148),(24,26),(24,56),(24,88),(24,152),(28,30),(28,60),(28,92),(28,156),(32,34),(32,48),(32,96),(32,160),(36,38),(36,52),(36,100),(36,164),(40,42),(40,56),(40,104),(40,168),(44,46),(44,60),(44,108),(44,172),(64,68),(64,80),(64,96),(66,70),(66,82),(66,98),(66,194),(72,76),(72,88),(72,104),(72,200),(74,78),(74,90),(74,106),(74,202),(128,130),(128,132),(128,136),(128,144),(128,160),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|4=>1
|5=>24
|6=>124
|7=>137
|8=>53
|9=>9
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x1f033
|5,0=>0xdf544c8ea8c227fb532ba827ea7e32967f9868b2858eb82d016c2915f546434623141d279a32171b1b778189ba17cca148ca0e7950d06d061920293e
|6,0=>0xfb799f8429e1ba6ceca6c9d2fc7cebc5de7c4e20c3620c2e4fbe34fbce39bbf52b264ab1b64ac5ccabd29a9426a4ab3a44f5a04bc9df089a33199a2099720987f0976ab8d2a58cf63893b98838f878e8873688570384b2184202828e98236f8228d814b47fa367a891787757801c75e76753757438e7390e6f9f86e46c6d6fa6a3a86a24869975686896834367f5b6540a62ff15fe5c5eca15e52f5dee75c6cf5a17759ae15720155ad5555725378753318527824ebd04eb534c39a4761346e4d468b04503a44d5940e023fc873def63cf043c47b3c0e83a9333a4c23a2413962d387fc38490384853500433c9f32ae531ffb2e69e2c58a28b5d284282583a24caa23ce31f4e01ec441e7a11c8b11c1e61b778191cb14f641394c0fb200ef6b0e8570d9b00d1160a89c0a6cd092b608c5d0397301371
|7,0=>0xc916ec1882bfa78bec45bbd83b893ab465bb2d7db158caf56aaee34ac06dab1a0a8e05a5896a4982a20b7a1d529e9c59d8b29d2d399b919889c978d59500a91f388c13c882bb8551e845468309382ba982019810528022b8015f7e7de7e0267da82796107798075fcb6ee2f6b7496b62f6b3696993767f5b67c566633a64f26626905f92a5e92e5d25f5d14d5baf25b65e5a84259e1d59c31584df50d0a4e4a24a5b949a2347c2f463b0444da4421b43f7943c1642880410283fb0d3e8b43e6563c3303acce3a98635ce4314e231434308ce300462ff092f4122d8da29ed729cb629c7c27fd125ce02575c2444b2382b2350221771205472036d1f9cc1c5e41a68818fa717807177fd1710215d6a1522414c6e14c1513b5212efe112391046c0f9b90f25e0f1410d9c70c8ab0b8d009b340867a07edd06dc1063860196e012ab
|7,1=>0xfe888f580fe8939e3b36df9f1dc7bbd5a2bcc219ca982
|8,0=>0xfe6ddf6f00ef099d8816b8b7ab0326afcd0a6d2ca4f9e9bc2399e6a98a538ee2f8de658ae937fb287f910782bf74d5074b6c7480773e23705ac6dcc36902167abf5acf6558dc52d93520635123c490c147fab459db4359a40d043cfa2331b72c0602996e286c927cf120f5720ef41dea81dc0b1b2ba163cb14f60104e2101780390f02009
|9,0=>0xe067ddc29bd1192b4c18853a07d51a5df842224d0a6d4
|10,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a155540155555401555554015555540155555400015554000155540001555400022222222222200222222222222220022222222222222000022222222222200005555555555555050555555555555505055555555555550505555555555555050aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000014141414141414141414141414141414141414141414141414141414141414142aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaaaaa800000005555555555555555000000000000000055555555555555550000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000015555555555540001555555555554000155555555555400015555555555540002aaaaaaaaaaaa8282aaaaaaaaaaaa8282aaaaaaaaaaaa82800000000000000005555555555555555555555555555555555555555000000005555555500000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000154015401540154015401540154015401540154015401540154015401540154022222222222222222222222222222222222222222222222222222222222222225151515151515050515151515151505051515151515150500000000000000000
|0,1=>0xaaaa000088aa0000aaaa000088aa0000aaaa000088880000aaaa000088895555555555540155555555555554015555555555555400015555555555540002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaa8000555555554444444455555555444444445555555544444444555555554444444422222222222222222222222222222222222222222222000022222222222200000000000155541414000000015554141400000001555414140000000155540002aaaaaaaa22aa22aaaaaaaaaa22aa22aaaaaaaaaa22222222aaaaaaaa2222222555544445555444455554444555544445555444455554444555544445555444488888888888888888888888888888888888888888888000088888888888800000000000155551110000000015555111000000001555511100000000155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80002aaa80002aaa80005151515151515050515151515151505051515151515150505151515151515050aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a00154015555551154015401555555115400000001555511100000000155551112aaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa80002aaa80001111111111110011111111111111001111111111111100001111111111110000
|0,2=>0xaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0aaaaaaaaaaaaa000000015554000155540001555400015554000155540001111000015554000111100002aaa80002aaa80002aaa80002aaa80002aaa8000000000002aaa800000005555555500550055555555550055005555555555000000005555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222222200002222222222220001555555555555555555555555555555540001555400011110000155540001111000000002aaaa22a800000002aaaa22a800000002aaaa222000000002aaaa222111100111111001111110011111100111111000011110000111100001111000000aa00aa00aa00aa00aa00aa00aa00aa00000000000000000000000000000001555511555555115555551155555511555555111155551111555511115555111088888888888888888888888888888888888888880000000088888888000000000000000555500550000000055550055000000005555000000000000555500002222222222220000222222222222000022222222222200002222222222220001555555555555555555555555555555551111111111111111111111111111111222aa22aa22aa22aa22aa22aa22aa22aa22222222222222222222222222222220000555500004444000055550000444400005555000044440000555500004444
|0,3=>0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa00000000155555554000000015555555400000001555555540000000155540002aaaaaaaaaaaa2222aaaaaaaaaaaa2222aaaaaaaaaaaa2222aaaaaaaaaaaa2220055555500554455005555550055445500005555000044440000555500004444aaa2aaa2aaa2aaa0aaa2aaa2aaa2aaa0aaa2aaa2aaa2aaa0aaa2aaa2aaa2aaa11111111155551155111111115555115511111111555511111111111155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa2222aaaa2225555555555555555555555555555555555555555555555555555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa00000000000000000001454545454545414000000000000000014545454545454142aaaaaaa800000002aaaaaaa800000002aaaaaaa800000002aaaa22200000000050505050505050505050505050505050505050505050505000000000000000022222222222222222222222222222222222222222222222222222222222200000000000155554140000000015555414000000001555541400000000155554142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222222222222225555555555555555555555555555555555555555444444445555555544444444
|0,4=>0xaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa8888aaaaaaaaaaaa88880000000000000000000000000000000155555555555555555555111155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000002aaaaaaaa2222222555555555555555555555555555555550000000000000000555555555555000000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa0000000088888888000044440000004400004444000000440000444400000000000044440000000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaa8000444444444444444444444444444444444444444444444444444444444444000022aa22aa22aa00aa22aa22aa22aa00aa2222222222220000222222222222000155555555551155115555555555115511555555555511551155555555551155100002aaa80002aa200002aaa80002aa200002aaa80002aa200002aaa80002aa2555511115555001155551111555500115555111155550000555511115555000000000000aaaaaaaa00000000aaaaaaaa00000000aaaa000000000000aaaa000155555554141414155555555414141415555555541414141555555554000000000002aaa8000282800002aaa8000282800002aaa8000282800002aaa800028280000000055555555000000005555555500000000555555550000000055554444
|0,5=>0xaaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa0aaaaaaaaaaa0aaa00000000044444400000000004444440000000000444444000000000044444402aaaaaaaaaaaaaa22aaaaaaaaaaaaaa22aaaaaaaaaaaaaa22aaaaaaaaaaaaaa20000000000000000000000000000000000000000000000005555555544444444aaaaaa88aaaaaa88aaaaaa88aaaaaa88aaaaaa88aaaaaa88aaaaaa88aaaaaa8800000001555555100000000155555510000000015555551000000001555555100002aaa8000002a80002aaa8000002a80002aaa8000000000002aaa800000005555111155551111555511115555111155551111555500005555111155550000aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa004444440044444400444444004444440044444400444444004444440044444400000088880000888800008888000088880000888800000000000088880000000111111110011001111111111001100111111111100000000111111110000000000000000000000000000000000000000aaaaaaaaaaaa0000aaaaaaaaaaaa00014141414141414141414141414141414155555555555541415555555555554142aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa802aaaaaaaaaaaaa801111111111111100111111111111110011111111111111001111111111111100
|0,6=>0xaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa15555555555555555555555555555555555555555555555555555555555540002a802aaaaa802aa22a802aaaaa802aa22a802aaaaa802aa22a802aaaaa802aa2551155115511550055115511551155005511551155115500551155115511550000000000aaaaaaaa00000000aaaaaaaa00000000aaaa888800000000aaaa88880000000000000000000000000000000000000000000000015555555555540000000000000002aa20000000000002aa20000000000002aa20000000000002aa25555555555555555555555555555555555555555555555555555555544444444aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa888800000000aaaa888800000000000000015555555555554140000000000000000155555555555541422222aaaa2222aaaa2222aaaa2222aaaa2222aaaa222222222222aaaa22222225555555555555555555555555555555555555555555544445555555555554444222222222222222222222222222222222222000022220000222200002222000155555554000155115555555400015511555555540001551155555554000155100002aa200002aa200002aa200002aa200002aa200002aa200002aa200002aa25544554455445544554455445544554455445544554455445544554455445544
|0,7=>0x44444444440044004444444444004400444444444400440044444444440044000002aaa80002a8000002aaa80002a8000002aaa80002a8000002aaa80002a800000000000000000000000000000000055555555444444445555555544444444aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00000000015555540000000001555554000000000155555400000000015555540222222222aaaaaa2222222222aaaaaa2222222222aaaaaa2222222222aaaaaa21111111111111111111111111111111111111111111111111111000011110000
|_,_=>0
def sP:Nat→Nat
|0=>0x40429d120c1010a1078202805891e04f880e78e18142039d386010a162471402203891e5411b16304832020384060809a1618c9814203842a08a01104c203045c58906288080e4c7012c203892a08a01164c18124203860844101162478e20203891e386880e1820304042840608080
|1=>0x42912d102418a20203892a085012c2c98906054080e24182140558b382479504884090608a01161c48f04055080e2418a02a44070c2450150203891e98701101c31504280a51024c0a02904071810182022c4830404d0b0e10a821405188120c101001c20f0489008123d0a0101c495
|2=>0x682418214cc5871254182146c5891c059080e70203042988b0cc0c0214203861298501101c30906288080e744830428d8b3810c15042842f120c101161c20304280a3167020f060808b3c7018a022039d380c10a022c606080c10116101822804407123c1015c2039c1260a82142ce03
|3=>0x4405908120c501782038906eca01101ce04720c10a1018e15042808b120c53a022039c083c182442048f72541011674e030429108120c1015a2da1c123c1a1101c3386e085010e3048e02203891e5411b101c4830451b010e4c4a606044076a0c10a022c3892a085222c204982a0808b
|4=>0x3a24182022da06385410a442048f040500b0e24182146c4073c2418a20203bd085410a0220203040608b0608501802c39e120c50d101c4bf1e050080e2470a028c407080c10a02f859c123c701101c6092a091011074e1804284073a24795040458c0c24701101de892a085011624a82
|5=>0x902c3891c28096101c48342059080e4c2182a080886024795040442c120c50d101c48314048080e2418a031c40738b078302203841e080a0101c48f0314407131018a02203bd125410a4420f091e380880e18237042808b126010a030c5c21254182022c4831484b080e2419402203a7
|6=>0x608d880e4c218060808b3224c0314203bd120c521101c31c300850b0f34483042808b0c11c82140444c120c10a022c20304280cb1618e031484407120c5019420386125410116d0209060851716247824480407582418a202039c126070a101c60906840880f24483042808b120c10a
|7=>0x101818214052880e2418a03404070c70c0a101d38c0c10a8202206042a080880c24882022c3891e54117101e78906280880e30f090604407187448304045891e050080e9c30906080850ef448e14044071338182140459d120c10a2e2c31c1c280880e247950405288120c1010a1c609
|8=>0x300c10a022c4d80608501101ce09300c10a161c9890606b080e25c95060850116241821404b0b0e1848e1404407120c10a0354407382418a422038412e4182140441c12e4182142038906280d4101e90906080880e24a830428d880e1048f0609101107048f06091080e744830429101
|9=>0x1c0c501101ce891e54101101c60906044074e7021806085080ef449504280880e744950608501162418a0364407120c101822c38906059080e9e88c120c0880e241821405f0b0e25303140440726247030220386385410a022039d126010a022039c080c10a442048f7254101101c209
|10=>0x1404587126010a030c407ba2418a022038c0c24181101d384120c10116d0209300c10a44204830429116101dc092a0c10a022c498060808b681c20304060880e184b7042808b0e24a830429881162418214880c31170483042808b0e184950429101102478e022038906280da101ce09
|11=>0x101c3090629081101c48304280cb161c48304280ad1624c15042808b182418244044077a241821404587120c12202c840738b018a022038906280de101c48304500880e1018214050080e247950488088120c50146203a72624c150404407382478302203a73c2470314044070c70182
|12=>0xe7049806284074e2418a02584074ef448304291080e1048304280e3104c498060808b0e24182146c4078424182022c3e2120c501101c98906840880e4c4b906080880e18e0304291080e4c4830384407120f00a4620384120c10a2e20384123ca820222f931260181101c3097208501
|13=>0xb60c0880e744830428b880e24c03042988b0fa8483042808b0e1848304045b40e2418a03a44070824783040459e120c501101ce89060850117a0483042808b0e2418214073880e184830428d880e33306120c1010e2418215940880e4c21806080880f9048304280880e64e090628088
|14=>0x6085010e25b8304298810fb8483042808b0e241ed1404407120f60a02203891e0c1014a203bd120c501101d386125410a022c6092a080880e30483c004407120c10a03ac407123c101402038907800b2101c31c06280880e9cf06120c501101ce86120c10a022c61d120c101101c989
|15=>0x146c407120c10a2e203890608501462c3890608501562038c0c24182022c389062b881101c31c30085080e241821404d880e70215060850110304830404587125410a028c407120c10a03c0587123ca82022f78c0c24181101c6061254101101c3042a08501106560906280880ee04b7
|16=>0x140440726241824404407120c10a6204587120c10a02b44070824a8304280880c2418214880880e24c1504280880e2418214051880fcc48f06044073824783040440712dc182140458718184830404407382418a02203a71254182148808812e4c0304280880e4c48302203a73a24182
|17=>0xe18e0304280880e26d831404407120c10116d0389300c10a442039d0c241821404407a6241821404407120c1018220384123c1820220384120c10a022ce890608501101ce09300c10a101c4980608501161c4830428096101c48314840880e25c8304280880e2418a0384407136cc03
|18=>0x608501101d804120c10a02203f3126018a0220393120c101161d60906280880e18483042808b0e2418a03d8407be4c48302203891e54101101c4831407a880e704950608501101de890608501101c98907800880e2418214052880fd048304280880e1849504280880e18483c028088
|19=>0x241821404407120c501101d393120c101101c3090608501101c4d706280880e24182140458712601821404407120f00a0220384120c10a02203890608522022038c120c101101c30906280880e9e886120c501101e88906280880e74209
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x8e60886082607d50776071606b6065605f60596053604d60476041603b6035602f60296023601d60176011600b60056
|6,0=>0x2497242723b7234722d7226721f72187211720a720371fc71f571ee71e771e071d971d271cb71c471bd71b671af71a961a2719b7194718d7186717f71787171716b6164715d7156714f71487141713a7133712c7125711e711771107109710270fb70f560ee70e770e070d970d270cb70c470bd70b670af70a870a2609b70947
|6,1=>0x3e973e273dc63d573ce73c773c073b973b273ab73a4739d7396738f73887382637b7374736d7366735f73587351734a7343733c7335732e7327732073197312730b730472fd72f672ef72e872e172da72d372cc72c572be72b862b172aa72a3729c7295728e7287728072797272726b7264725d725672506
|7,0=>0x5d085c885c175ba75b375ab85a4759c8594858c8584857c8574856d7565855e7556854e8546853e8537752f8527851f8517850f8509650274fa84f284eb74e384db84d384cc74c574be74b774af84a874a174998491848a7482847a8472846a8463745b8453844c7444843d7435842d8426741f7417840f840783ff83f783f07
|7,1=>0x7b877b087a887a2679a8792878b7783877b8773876b8764775d7755874d8746773f7738773087297722771a8712870a870286fb76f386eb86e386db86d476cd76c676bf76b786af86a7869f8697868f8687867f8677866f8667865f8657865076497642763b7633862b8624761d7615860e760685fe85f685ee85e775e075d88
|7,2=>0x7fc87f577ed87e587dd87d677cf77c787bf8
|8,0=>0x99a7992898a8983797a997199698962795b7953894c7945793e7937792e9926891f7917890f890788ff88f788f078e978e188d898d088c978c188ba78b288aa88a2889a8893788b8884787c8874886c8864885c8853984b8843883c7834882c8824881c8814880b98047
|9,0=>0x9dd79d679ce89c779c079b889b179a989a18
|10,0=>0x9e47
|_,_=>0
def wAt:=mkWire dB 119 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x12620605142e06053a072a25069d041e1e270629022d121d1205101d381d12053c070c9d120d041e0c07062506291205121d0c290625101d3c07580d129d041e126206050c07120d120506291c07069d041e0629069d041e121d0c290625101d0c07120d061d182c0c29120d101d0c1d182c0c29101d182c121d0c290625101d
|1=>0x5807129d041e0c05120d0629069d041e0625062d101d12d1142e06250c05120d101d121d260f12290672120512de062d0629069d041e0c29120d080d121d06292a25061d101d041e12610605123e06290451148d0c07120d301d060512050629121d021d0629101d2a05061d0c1d0625120d122d062d101d069d0c29120d041e
|2=>0x6290c1d120d0807121da2070c09120d120d1205041e0c29120d061d121d0c29120d061d121d0c290c9d041e0c1d0c29101d182c0c29120d101d3a040c1d120d101d182c0c29120d101d101d0605121d1229101d120d1205301d060512c6022d0625142e3a04080d121d101d060512291289021d0c07120d071a062938091205
|3=>0xc09120d12de062d101d1c05069d041e1229069d041e0c1d120d1205121d021d06292a05061d101d121d060506950807121d101d12050605ae0712290609101d2a05061d101d126206050625069d041e3012121d0605029d1205041e0689021d301d06055807129d041ea6290c1f120d3a072a25061d0629121d021d021d1205
|4=>0x61d7a090c05120d0c29120d041e142e121d101d060512620605061d122d101d142e0605101d121d260f1229120d062d101d061d022d101d1256061d382f1205101d120d0629069d041e136e300906051205069d041e1255061d06290c29120d041e0c05120d2a25061d101d580f129d041e101d260f1229041e1e2706290c29
|5=>0x4050c07120d3a04080d121d121d061d06292609060512290689021d120d029d041e12c6022d101d101d080f121d061d0605101d0c29120d021d101d0c05120d021d1e2706291205129d041eae7312050609148d0c07120d06721205021d061d06290c07120d041e061d0605122906291205041e069d041e12050625101d2a27
|6=>0x121d0629101d580d129d041e0c1d120d101d12c5022d101d2c1d126206053a070c1d120d18230c29120d02b5080f121d0605121d12290c89120d021d389d1205041e06051205041e126206050c05120d2a07061d06051229101d3a070c1d120d12d1142e101d1385078204051229029d041e12290689021d0625078204051229
|7=>0x22d101d12dd062d101d048106721205048d0c07120d06290807121d0c05120d061d120d101d0c29061d120d0c29120d040512e60689021d06290672120504051e270629120d1205041e0c9d120d041e0c1d120d101d0c290c1d120d1229300906053a040c1d120d0605022d101d0c2f120d101d142e120d101d0d82120d0405
|8=>0x629062d101d0c29120d1205041e061d021d301d06051229041e3a070c1d120d3a040c1d120d0c07120d101d461d0c07120d0c29120d101d03c9135e0609120d120506053a070c1d120d12050c29120d101d0c07120d6e07062d101d101d061d062918090c29120d0c29061d120d120d061d121d129d041e122d062d101d062d
|9=>0x12050c05120d040512290807121d381f1205061d120d120d04051205062530090605142e101d0605021d0c1d120d0c1f120d260f1229121d0629121d101d0c1d120d120506050605101d12620605029d041e0689021d07820405300906051229021d022d101d080f121d061d121d120d021d061d06050c07120d062912091205
|10=>0x41e1229120d0609101d06050405121d021d260d1229120d041e0c09120d0c09120d080d121d0805121d060512091229101d129d041e120d101de607120926091229061d062907ce1209061d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x950150000000000000000000000000000000000000000000000000000000000000000005
|6,0=>0x1a880001a0865318c861217505c116885820000544148800000004e4129048200000001110404000000000000000f883c200003a20d903240c080000b1000000000000a882820000000091000000000000000204078800007081a200000000000173050c000000010400000e2
|6,1=>0x2d4cb142b5000000000002a8ca730000a34000000027d000000009b400009740000000250c0002488000240800000008e22290000000000000000000000000000088221880000000842000000020107d31ec87831d4c0001cc800000000001c8400000000001c086c4
|7,0=>0x580d5d3568d573550d52253cd4c3524d46351094134fc93c34e4d3634d453324c0d2d34a8d273490d22247cd1e146cd183454d12343cc00043490a341cd043404cfe33eccf833d4c0003cc8f033b4cea339cce43384cde336ccd83354cd233408ce232ccc83314cc232fccbd22ec8b83
|7,1=>0x85ce152848e0f3830e093818e042804dfe37ecdf837d4df237c09ed37a8de73790de13778ddb3760dd53748dcf3730dc93718dc33700dbd36e8db736d0db136b8dab36a0da53688d9f3670d9a2660996264cd903634d8a361cd84360c58035f4d7a35dcd7435c896f35b0d693598d633
|7,2=>0x23038b4e2a389ce243884e1e386ce1a1
|8,0=>0x29b2a64a972a54a932a44a8f2a34a8b2a24a872a14a832a04a7f29f4a7b29e4a7729d4a7329c4a6f29b4a6b29a4a672994a632984a5f2974a5b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b28e4a3728d4a332
|9,0=>0x2a51a906a31a886a11a8069f1a7869d1
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x80d00000080400000054000000047800000044000000043400000042c00000042400000040c00000040400000040000000024e00000020c00000010100000010000000008000000006c00000006000000004d00000004c00000004100000004000000003e00000002c00000002700000002400000002000000001000000000c000000008000000004000000000
|1=>0x557d00000546c00000540c00000447900000404c00000400400000400000000347d00000343d00000240c000002004000002000000001a7f00000167900000157d00000157900000157500000147f00000147900000140400000127c00000107e00000107d00000107100000104c00000102400000100d00000100c000001004000000c45000000860000000822
|2=>0x6937800006177d000061779000061179000059a7e00005947d00005367d000051e7f00005187f00005147f00005103f00004957d00004167900004157500002d37d00002903000002824900001927c00001921c00001107c00001104c000010a4e00001042400001000400000957d00000924d00000917900000903000000834100000800000000746d000006000
|3=>0x12000200010814590010695f9001001171000c0107d000c0104d000c0007d000c0002c00085b45c00085947d00085907c00080345d00080144f00080106f00050006d00040147f00040147d000280500000280400000201579000201531000201471000201071000101c7f00010082d0001008220000e153900008157900008153100008044100007967900006977c
|4=>0x8000d67908000902c08000557d08000547d08000547908000147908000117d08000002c05200557d04004157d04000147d040001475020859c7f01004157d01000157d01000147d010001475008001c7f008000c4f00800082d00800004700404103f00400086f00280347d00280340c00280145d00200547900200345d00200147900200040c001201079001200141
|5=>0x8c000557d80008157d80000157d5000082d128200547928000447920200447920040242c20004d47920000547d2000004391000417fd1000005a0080c0504d080c0147d080c0006c08080107d
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x90a00000000000000000000000000000000000003
|6,0=>0x1b0f4d0000000a0a002700000200002a001700001b0005001e0000480300000000000000003a0a00001100001a0a2305200001000000400000002314000010001e15011508420101000405000018171500002150000000000101000144070a000b003900010100001300000000280100013a000000051500004a0001
|7,0=>0x5b230393ad9e296d21221f31310311724e6003a6471b807a3b52038b1f4b905781791f030d4f033d036e0e11230619298a8f65083492990875a405628c71731703176b951c2377122c1d7f1b152f43553a2389172b668d161f357d2f1b985f39237869334551677e5c39153782190c0e9636037c036306056a4c0c4926160a2f
|7,1=>0x172d252446943c033a
|8,0=>0x6130b02fa1a93f586c2eafa576ae3eac5e6fa7a09dab2f5684a39c325a70a2aa2e8364889197598e6f7b41869a54a8689f3074875d
|9,0=>0x30539b312e85316f38
|10,0=>0x2d
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 36 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 9 roots_250 ops++addP pm 1 dom_50 4 roots_50 ops++addP pm 2 dzo_118_8 7 roots_118 ops++addP pm 3 dom_246 9 roots_246 ops++addP pm 4 dom_190 9 roots_190 ops++addP pm 5 dom_222 8 roots_222 ops++addP pm 6 dom_238 8 roots_238 ops++addP pm 7 dom_242 8 roots_242 ops++addP pm 8 dzo_246_8 8 roots_246 ops++addP pm 9 dom_218 6 roots_218 ops++addP pm 10 dom_252 8 roots_252 ops++addP pm 11 dzo_50_4 4 roots_50 ops++addP pm 12 dom_118 7 roots_118 ops++addP pm 13 dom_116 5 roots_116 ops++addP pm 14 dom_204 4 roots_204 ops++addP pm 15 dom_234 6 roots_234 ops++addP pm 16 dzo_114_4 5 roots_114 ops++addP pm 17 dzo_242_12 6 roots_242 ops++addP pm 18 dzo_242_4 6 roots_242 ops++addP pm 19 dzo_244_8 6 roots_244 ops++addP pm 20 dom_174 6 roots_174 ops++addP pm 21 dzo_214_8 5 roots_214 ops++addP pm 22 dom_86 4 roots_86 ops++addP pm 23 dom_102 4 roots_102 ops++addP pm 24 dzo_230_8 5 roots_230 ops++addP pm 25 dom_236 5 roots_236 ops++addP pm 26 dom_158 6 roots_158 ops++addP pm 27 dom_188 6 roots_188 ops++addP pm 28 dom_244 6 roots_244 ops++addP pm 29 dom_186 8 roots_186 ops++addP pm 30 dom_230 6 roots_230 ops++addP pm 31 dom_206 5 roots_206 ops++addP pm 32 dom_210 5 roots_210 ops++addP pm 33 dom_220 5 roots_220 ops++addP pm 34 dom_226 5 roots_226 ops++addP pm 35 dom_214 6 roots_214 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_118_8_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_246_8_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_50_4_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_114_4_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_242_12_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_242_4_50 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_244_8_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_230_8_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_214 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 9 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 124 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 124 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 137 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 137 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 53 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 53 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_239:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_iso_b isoMvS_239 (by decide +kernel) lowS_223
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,136),(10,11),(10,26),(10,42),(10,138),(12,13),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,48),(16,80),(16,144),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,33),(32,34),(32,48),(32,96),(32,160),(36,37),(36,38),(36,52),(36,100),(36,164),(40,41),(40,42),(40,56),(40,104),(40,168),(44,45),(44,46),(44,60),(44,108),(44,172),(64,65),(64,68),(64,80),(64,96),(66,67),(66,70),(66,82),(66,98),(66,194),(72,73),(72,76),(72,88),(72,104),(72,200),(74,75),(74,78),(74,90),(74,106),(74,202),(128,129),(128,130),(128,132),(128,136),(128,144),(128,160),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|12=>1
|_=>0
def HT:Nat→Nat→Nat
|12,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xfac688
|_=>0
def sO:Nat→Nat→Nat
|12,0=>8
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
|12,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 11 roots_254 ops++addP pm 1 dom_191 11 roots_191 ops++addP pm 2 dom_127 11 roots_127 ops++addP pm 3 dom_253 11 roots_253 ops++addP pm 4 dom_251 11 roots_251 ops++addP pm 5 dom_247 11 roots_247 ops++addP pm 6 dom_239 11 roots_239 ops++addP pm 7 dom_223 11 roots_223 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 11 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem checked (s:Nat) (hs:s≤12):∀ i<NN s,bar dom_255 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [2, 8] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [0, 10] }, { op := GateOp.or, inputs := [8, 7] }, { op := GateOp.or, inputs := [3, 8] }, { op := GateOp.and, inputs := [9, 14] }, { op := GateOp.and, inputs := [1, 13] }, { op := GateOp.and, inputs := [5, 4] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [15, 16] }, { op := GateOp.or, inputs := [19, 17] }, { op := GateOp.or, inputs := [20, 18] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52336_aux

theorem PEqualNP.Outside.L_meta_52336 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52336_aux.main
