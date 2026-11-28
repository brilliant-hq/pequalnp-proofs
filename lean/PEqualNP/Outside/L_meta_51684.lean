import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51684_aux
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

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefafaeeee0000fefefafaeeee0000fefefafaeeee0000fefefafaeeee0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffaaeeeeaa00ffeeffaaeeeeaa00ffeeffaaeeeeaa00ffeeffaaeeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffaaaaaaa00fffafffaaaaaaa00fffafffaaaaaaa00fffafffaaaaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffaeeeeaa00fffefffaeeeeaa00fffefffaeeeeaa00fffefffaeeeeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccc0000cccc0000ffffffccffffffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeeaa00eeeeaa00ffffffeeffffffeeeeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xffffffccffffffcccccc0000cccc0000ffffffccffffffcccccc0000cccc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xffffffeeffffffeeeeeeaa00eeeeaa00ffffffeeffffffeeeeeeaa00eeeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefeeeeeeeeefafafafa00000000fefefefeeeeeeeeefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccff00ff0000000000ffccffccffccffccff00ff0000000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffaaffaaaa00aa00ffeeffeeffeeffeeffaaffaaaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0ff00ff00fff0fff000000000fff0fff0ff00ff00fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffaffaaffaafffafffaaa00aa00fffafffaffaaffaafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcffccffccfff0fff000000000fffcfffcffccffccfff0fff000000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffeffeeffeefffafffaaa00aa00fffefffeffeeffeefffafffaaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeaaaaeeee0000ffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafaffffaaaafafafafaaaaa0000fffffafaffffaaaafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcffffccccfcfcf0f0cccc0000fffffcfcffffccccfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefeffffeeeefefefafaeeee0000fffffefeffffeeeefefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaaaa00ffffffaaffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccff00cccc0000ffffffccffffffccffccff00cccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffaaeeeeaa00ffffffeeffffffeeffeeffaaeeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0ffffff00fff0fff000000000fffffff0ffffff00fff0fff000000000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffaffffffaafffafffaaaaaaa00fffffffaffffffaafffafffaaaaaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcffffffccfffcfff0cccc0000fffffffcffffffccfffcfff0cccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffeffffffeefffefffaeeeeaa00fffffffeffffffeefffefffaeeeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfefefafafefefafafefefafafefefafaeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffaaffeeffaaffeeffaaffeeffaaeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffafffafffafffafffafffafffafffaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffafffefffafffefffafffefffaeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaa00aa00fffafffaaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeaaaaffffffffeeeeaaaaeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafafafafffffffffafafafafafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffcfcf0f0fffffffffcfcf0f0fcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefafafffffffffefefafafefefafaeeee0000fefefafaeeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccff00ffffffffffccff00ffccff00cccc0000ffccff00cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffaaffffffffffeeffaaffeeffaaeeeeaa00ffeeffaaeeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaaaaaaa00fffafffaaaaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfff0fffffffffffcfff0fffcfff0cccc0000fffcfff0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffafffffffffffefffafffefffaeeeeaa00fffefffaeeeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffafafafafafafafaeeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffccffccffccffcc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ff00ff00ff00ff000000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ffccffccffccffcc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffcccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffeeeeaaaaeeeeaaaaffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffafafafafafafafaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcf0f0fcfcf0f0ffffccccffffcccccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefefafafefefafaffffeeeeffffeeeeeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffccff00ffccff00ffffffccffffffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffeeffaaffeeffaaffffffeeffffffeeeeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffff0fff0fff0fff0ffffff00ffffff000000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffafffafffafffaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffcfff0fffcfff0ffffffccffffffcccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffefffafffefffaffffffeeffffffeeeeeeaa00eeeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffffffffff00000000cccccccccccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafafafafaaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fcfcfcfcccccccccf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffafafafafefefefeeeeeeeeefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffff00ff00ffccffccffccffccff00ff0000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffffaaffaaffeeffeeffeeffeeffaaffaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fff0fff0ff00ff00fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffafffaffaaffaafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffffffffffffffffff0fff0fffcfffcffccffccfff0fff000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffafffafffefffeffeeffeefffafffaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffcccc0000ffffccccffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeaaaaffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffff0f0ffff0000f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffafafafafffffafaffffaaaafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcf0f0fffffcfcffffccccfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffefefafafffffefeffffeeeefefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffff00ff00ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffaaffaaffffffaaffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffccff00ffffffccffffffccffccff00cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffaaffffffeeffffffeeffeeffaaeeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffffffffffffffff0fff0fffffff0ffffff00fff0fff000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffafffafffffffaffffffaafffafffaaaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffcfff0fffffffcffffffccfffcfff0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffefffafffffffeffffffeefffefffaeeeeaa00
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
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
def isoMvS_164:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_164:Lower true dom_164 roots_164 goal_164 4:=lower_iso_b isoMvS_164 (by decide +kernel) lowS_41
def isoMvS_168:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_168:Lower true dom_168 roots_168 goal_168 4:=lower_iso_b isoMvS_168 (by decide +kernel) lowS_41
def isoMvS_200:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_41
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
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_slice_b [(0x303000003030,32,36)] (by decide +kernel) lowS_41
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_slice_b [(0xa000a00000000000a000a,16,17)] (by decide +kernel) lowS_82
namespace S_169
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,129),(8,9),(8,40),(8,136),(32,33),(32,40),(32,160),(128,129),(128,136),(128,160)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_169.map (·&&&dom_169)
def gM:=goal_169&&&dom_169
def NN:Nat→Nat
|3=>3
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x3e545373b004d20
|4,0=>0x99e4571e8868f5652c1a50e882ab292893b11cc9
|5,0=>0x532f32aeff22bc0
|6,0=>0x532f3
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0800000000000000000000000000000c0b030000030300000000000000000000030000000300c0c00000c0c000000000000000000000c0800000c0800000000000000000000000000000003020000030200c0000000800000000000000000000000c0000000b030000030000000000000000000000030300000300c0800000c08000000000000000000000c0800000c0b030000020200000000000000000000030300000202c0c00000c0c000000000000000000000c0c00000003030000030300000000000000000000020200000202c0c00000000000000000000000000000c0c00000001010000010100000000000000000000010100000100c0c00000000000000000000000000000c0800000003000000030000000000000000000000030000000300808000008080000000000000000000008080000080b030000030300000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x52105210526105e210521f0a5e10a82105d2105c210521b085260a5910872652403210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x21022004
|4,0=>0x5eaa952aa0536a5948a8c5
|5,0=>0xf91cab45
|6,0=>0x424
|_,_=>0
def wAt:=mkWire dB 16 170 0x3ffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14815240915495514052149501415
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x82620000004222
|5,0=>0xb1a1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfb9630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x98011
|5,0=>0x12d
|6,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_168 4 roots_168 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_41 4 roots_41 ops++addP pm 3 dom_161 4 roots_161 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_169 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_161 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_168 4 s (0,roots_168.map (·&&&dom_168)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_169 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_168 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_169==dom_169)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_169 gM v ys):RunD true dom_169 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_169 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_169 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_169 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_169 roots_169 goal_169 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_169
theorem lowS_169:Lower true dom_169 roots_169 goal_169 7:=S_169.noCircuit
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_27
def isoMvS_53:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53:Lower true dom_53 roots_53 goal_53 4:=lower_iso_b isoMvS_53 (by decide +kernel) lowS_27
def isoMvS_57:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_45
def isoMvS_75:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_iso_b isoMvS_75 (by decide +kernel) lowS_45
def isoMvS_89:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_83
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_45
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_27
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_27
def isoMvS_105:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_83
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_27
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_27
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_45
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 4:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_27
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 5:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_83
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_83
def isoMvS_201:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_169
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_45
def isoMvS_204:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_45
def isoMvS_210:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_45
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_45
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_83
def isoMvS_226:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_27
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_45
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_83
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xcc00cc00cc00cc,16,18)] (by decide +kernel) lowS_53
def dzo_57_2:=0xc0c0c0c0c0c0c0c
def gzo_57_2:=0xc0c0c080c0c0800
def gsh_57_2:=0x303030203030200
theorem lowS_zo_57_2_41:Lower true dzo_57_2 roots_57 gzo_57_2 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_2) [(dom_57,2)] (by decide +kernel) (lower_slice_b (T:=gsh_57_2) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,18),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,17),(16,18),(24,25),(24,26),(24,56),(32,33),(32,40),(34,35),(34,42),(34,50),(48,49),(48,50),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_59.map (·&&&dom_59)
def gM:=goal_59&&&dom_59
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x593ef1f10d
|5,0=>0xa75f10deb70a6f0
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa000a000a000af0a0f0a0f0a0f0af0f0f0f0f000f00f000f000f000f0000000000f0a0f0af0f0f0f00000000f0f00000f0f0000f000f000a000a00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x436104361094386107436103610543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wAt:=mkWire dB 10 60 0xfffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x182
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x400
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xf9c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x25
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_57 5 roots_57 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_57_2 5 roots_57 ops++addP pm 3 dom_41 4 roots_41 ops++addP pm 4 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_57 5 s (0,roots_57.map (·&&&dom_57)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_57 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_59==dom_59)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 gM v ys):RunD true dom_59 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_59 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_slice_b [(0x3030303030303030,32,36)] (by decide +kernel) lowS_57
namespace S_91
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(2,18),(2,66),(3,11),(3,19),(3,67),(8,9),(8,72),(10,11),(10,26),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_91.map (·&&&dom_91)
def gM:=goal_91&&&dom_91
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x9f8ac
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f0000f000f00000000000f000f00c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0af0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 92 0xfffffffffffffffffffffff
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
addP pm 0 dom_90 5 roots_90 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_83 5 roots_83 ops++addP pm 3 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_91 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_90 5 s (0,roots_90.map (·&&&dom_90)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_91 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_90 h
def symsG:List (List (Nat×Nat)):=[[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_91==dom_91)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_91 gM v ys):RunD true dom_91 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_91 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_91 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_91 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_91 roots_91 goal_91 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_91
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=S_91.noCircuit
def dzo_105_2:=0xc0c00000c0c00000c0c00000c0c
def gzo_105_2:=0xc0c00000c0c00000c0800000800
def gsh_105_2:=0x303000003030000030200000200
theorem lowS_zo_105_2_41:Lower true dzo_105_2 roots_105 gzo_105_2 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_2) [(dom_105,2)] (by decide +kernel) (lower_slice_b (T:=gsh_105_2) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,66),(3,11),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,42),(10,74),(32,33),(32,40),(34,35),(34,42),(34,98),(64,65),(64,66),(64,72),(96,97),(96,98),(96,104)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_107.map (·&&&dom_107)
def gM:=goal_107&&&dom_107
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x23449
|5,0=>0xf3574
|6,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0000000000000f0f00000000f0a00000f0a00000f0a00000f0af0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000000f0a0000000000000f0af0f00000f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xd1a1ac684688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 108 0xfffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x89
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
addP pm 0 dom_105 5 roots_105 ops++addP pm 1 dom_106 4 roots_106 ops++addP pm 2 dzo_105_2 5 roots_105 ops++addP pm 3 dom_75 5 roots_75 ops++addP pm 4 dom_41 4 roots_41 ops++addP pm 5 dom_99 4 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_105_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_99 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_105 5 s (0,roots_105.map (·&&&dom_105)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_107 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_105 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_107==dom_107)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_107 gM v ys):RunD true dom_107 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_107 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_107 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_118:Lower true dom_118 roots_118 goal_118 6:=lower_slice_b [(0x500050005000500050005000500050,32,36),(0x550055000000000055005500000000,4,36)] (by decide +kernel) lowS_82
theorem lowS_173:Lower true dom_173 roots_173 goal_173 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030,32,36)] (by decide +kernel) lowS_169
theorem lowS_185:Lower true dom_185 roots_185 goal_185 8:=lower_slice_b [(0x30300000303000000000000000000000303000003030000,1,17)] (by decide +kernel) lowS_169
namespace S_218
def pG:List (Nat×Nat):=[(2,18),(2,66),(8,72),(8,136),(10,26),(10,74),(10,138),(16,18),(16,80),(24,26),(24,88),(24,152),(64,66),(64,72),(64,80),(64,192),(128,136),(128,192),(130,138),(130,146),(130,194),(144,146),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_218.map (·&&&dom_218)
def gM:=goal_218&&&dom_218
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x40879
|4,0=>0x49e6b231121999b0006e
|5,0=>0x5d3b34d28f34ef53460e30fa82fe9115ba713bdb0331302c54
|6,0=>0xc97a573884613541a861
|7,0=>0xc97a5
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a000000000a000a004040404000000000404000000000000040404040000000004040002828282800000000282828280000000028280000000000002828000505050500000000000000000000000005050000000000000000000000000000000000000000000000000000a0a0a0a000000000a0a0a0000000000000000000000000000000001400141400000000140014028282828000000002800280000000000282828280000000028002805040504000000000000000000000000050405040000000000000000a000a00000000000a000a00000000000a000a00000000000a000a0141414100000000010101010000000001414141000000000101010128282828000000000000000000000000282828280000000000000005050505000000000505050500000000000000000000000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0a000141414140000000014001400000000001414140000000000140014020202020000000002020202000000000202020200000000020202025050505000000000505050500000000050505050000000000000000
|0,1=>0x1010101000000000000000000000000010101010000000000000000a0a0a0a000000000a0a0a0a0000000008080808000000000808080800400040000000000000000000000000004000400000000000000028282828000000002828282800000000080808080000000000000000000000000000000505050500000000000000000000000005050000202020200000000020202020000000002020202000000000000000000014140000000000000000000000000000141400000000000000028282828000000002828000000000000282828280000000028280005050505000000000505050500000000050505050000000005050000
|_,_=>0
def sP:Nat→Nat
|0=>0xce12906709483384b824467094833dc2523467080a3384b620ce12d483a1c2520ce12cc91384b224067094834bce128cee290670958458ce128d47094690a083398a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8f2986
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 25 219 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x28728d09129128789128d49329d694
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x61005100000032120001
|6,0=>0x918171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xff7cf078c288180
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3020014605
|6,0=>0x7889
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_216 5 roots_216 ops++addP pm 1 dom_202 5 roots_202 ops++addP pm 2 dom_200 4 roots_200 ops++addP pm 3 dom_82 4 roots_82 ops++addP pm 4 dom_90 5 roots_90 ops++addP pm 5 dom_210 5 roots_210 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_218 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_210 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_216 5 s (0,roots_216.map (·&&&dom_216)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_218 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_216 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccccccccccccccccccccccccccccccc,126)],[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_218==dom_218)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_218 gM v ys):RunD true dom_218 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_218 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_218 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_218 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_218 roots_218 goal_218 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_218
theorem lowS_218:Lower true dom_218 roots_218 goal_218 8:=S_218.noCircuit
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_slice_b [(0x30300000000000003030000000000000303000000000000030300000000,1,33)] (by decide +kernel) lowS_201
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_55
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 5:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_55
def isoMvS_115:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_115:Lower true dom_115 roots_115 goal_115 7:=lower_iso_b isoMvS_115 (by decide +kernel) lowS_107
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_91
def isoMvS_122:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_59
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 5:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_55
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 5:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_55
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 7:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_59
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 6:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_61
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_59
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_107
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 6:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_118
def isoMvS_186:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_186:Lower true dom_186 roots_186 goal_186 6:=lower_iso_b isoMvS_186 (by decide +kernel) lowS_118
def isoMvS_199:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_199:Lower true dom_199 roots_199 goal_199 6:=lower_iso_b isoMvS_199 (by decide +kernel) lowS_61
def isoMvS_203:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_185
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_185
def isoMvS_206:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_61
def isoMvS_211:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_91
def isoMvS_213:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 7:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_107
def isoMvS_214:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 7:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_59
def isoMvS_217:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_173
def isoMvS_220:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 6:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_61
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 7:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_107
def isoMvS_229:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_91
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 7:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_234:List (Nat×Nat):=[(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 7:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_107
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_91
def isoMvS_242:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_59
def isoMvS_244:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_244:Lower true dom_244 roots_244 goal_244 7:=lower_iso_b isoMvS_244 (by decide +kernel) lowS_59
def isoMvS_248:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_107
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_59
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_109
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xcc00cc00cc00cc00cc00cc00cc00cc,16,18)] (by decide +kernel) lowS_117
def dzo_82_32:=0x50005000000000005000500000000
def gzo_82_32:=0x50004000000000004000000000000
def gsh_82_32:=0x500040000000000040000
theorem lowS_zo_82_32_82:Lower true dzo_82_32 roots_82 gzo_82_32 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_32) [(dom_82,32)] (by decide +kernel) (lower_slice_b (T:=gsh_82_32) [] (by decide +kernel) lowS_82)
def dzo_41_2:=0xc0c00000c0c
def gzo_41_2:=0xc0800000800
def gsh_41_2:=0x30200000200
theorem lowS_zo_41_2_41:Lower true dzo_41_2 roots_41 gzo_41_2 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_2) [(dom_41,2)] (by decide +kernel) (lower_slice_b (T:=gsh_41_2) [] (by decide +kernel) lowS_41)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c080c0c0800
def gsh_121_2:=0x3030303030303030303030203030200
theorem lowS_zo_121_2_41:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0e000000000f0e0f0a00000000
def gsh_91_32:=0xf0f0f0e000000000f0e0f0a
theorem lowS_zo_91_32_82:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xa0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00,0,8)] (by decide +kernel) lowS_82)
def dzo_90_32:=0x5050505000000000505050500000000
def gzo_90_32:=0x5050504000000000504050000000000
def gsh_90_32:=0x50505040000000005040500
theorem lowS_zo_90_32_82:Lower true dzo_90_32 roots_90 gzo_90_32 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_32) [(dom_90,32)] (by decide +kernel) (lower_slice_b (T:=gsh_90_32) [(0x50005000000000005000500,0,8)] (by decide +kernel) lowS_82)
def dzo_83_32:=0xf000f00000000000f000f00000000
def gzo_83_32:=0xf000e00000000000e000a00000000
def gsh_83_32:=0xf000e00000000000e000a
theorem lowS_zo_83_32_82:Lower true dzo_83_32 roots_83 gzo_83_32 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (lower_slice_b (T:=gsh_83_32) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,40),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xd738bd2c8463b6825416237e50a36009076
|5,0=>0xc357cbdbaab87eaaff718d6d78bebf5cedc5b8f548b2a4775644a412dd012257a1e86818c1015d0e0c79c02135
|6,0=>0xfd094e2835d08a8c814fae4a2ae413a9b6aa8b0ea878aa4f30995e69706c94367873e4844f57c7b77711f74a5d732456c7e15dcba5d6dd58a1d5362e492d547a7845591443f943d53439b138e9e385873804e2feb02e32a2902c22a3f1c85c18bfa1420913a971274f08b9d049e70231801256
|7,0=>0xfb58fa7d1ba22a39fb9397eaa9582884ca08132c63b3d4e11a4b1f2463ab452944182d3ebb03864336ae034e5d3004b2eccd2c9172b0d92a2e925dc21c1ad1a6ff19f6a1649115edf14c531489e0fa2d0d8d10cc950c13b0bdcd
|8,0=>0xcdd9293d0378ef06900d62b5b5f5a847c6832d0c2881b1cf4b0e7a107721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000000f0e0f0e000000000f0e0f0af0f0a0a0f0f0a0a0f000a000f000a00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af000f000f000f000f000f000f000f0000000000f0a0f0a000000000f0a0f0af0f00000f0f00000f0f00000f0f0000f0f0f000f0f0f000f0f0f000f0f0f00f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0ae0e0e0e0e0e0e0e0e0e0a0a0e0e0a0af0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f000f0f0f000a0a0a000a0a0a00
|0,1=>0xf0f0f000f0f0f000000000000000000f0f0a0a0f0f0a0a00f000a000f000a000f000a000f000af0f0f0f0f0f0f0f0f0f0a0a0f0f0a0af0f0f0f0f0f0f0f0f0f0f0f000000000000f0f00000f0f00000f0000000f00c0c0c0c0c0c0c0c0c0c00000c0c00003030303030303030303000003030000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000f000f000a000a000a000af0f0f0f0f0f0f0f0f0f0f000f0f0f00f0a0f0a000000000f0a0f0a000000000000f0f00000f0f00000f0a00000000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0a0f0f0000f0f0f0f0f0f0f0f0f0a0f0a00000000
|0,2=>0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c00005050000050500000500000005000000f0f00000f0f00000f0a00000f0a0000000000000000505050005050500f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0505050005050500f0f0f0f0f0f0f0f000000000f0a0f0a000000f0000000f0000000a0000000af0f000f0f0f000f0f0f000a0f0f000aa0a0f0f0a0a0f0f0a0a0f0a0a0a0f0a0000f0f00000f0f00000a0a00000a0af0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0000000000000000f0f0f0a0f0f0f0af0f05050f0f05050f0f05000f0f0500f0f0f0f0f000f000f0f0f0f0f000f00
|0,3=>0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f0000000050505000505050005050500050505000000000000000000f0f0f0f0000000040404040404040404040404040404045050505050505050500050005000500f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a00e000e000e000e000e000e000e000e
|_,_=>0
def sP:Nat→Nat
|0=>0x40b04f24b3d82851091c131a10848704c1082c614950b3d81445432c130849404f14424204f0042470401442425cc58825004f1445491c130424b34130420d04f14940b04f4c44870404484013c92c63851083413092c62851081c61440c2040
|1=>0x11f0cb04f14470b04f9051092c194f1522542c13c51150cb04f14448b04c3e412224b04f14940b04f12124b04f1601092cf6056c92d73047c91c13c51080cb04c14421e2c13c51092c131d14421c2c13c56c824204f44940b04f1080c204c489
|2=>0x2c13c014424b04fb0512b24b04f1442472cf60511524b04c3c44891cb04c1092d731614424704f68510848704f1448d22c13c51090813d614424b04fa4524b04fa056dc24b04c3c40cb04c9051092c13e71442470813049892c13c510908b5cc
|3=>0x1232092c13c510824b5cf14424b04fcc512324b04f144c891cb04f1711092ef04f14424b5cfc0510324b5c51092cd04f1442091c130524bbc13ca14424b04fb851032422c130424b04fb451082d93c56d52422c13c424b18f1442030813c5109
|4=>0x3c511c0c92c13c51080cb04f1440c92c13056c92cfd05d4324b04f14424b04f7451092c13f71447092c13c51092c13f61752092c13c51091c204f1442422d73c511224b04c3c48c324b04f14424b3d817524b3f41447092c130f1442091c13c5
|5=>0x24b04f14424b04f1601092c13c51092c130f1711092c13c5d492c13c5e4424b04f14424b5cf15b1092c13c56c92d73c51091cbbc13c52542c13c51092c13e41781092c13c51032422c13c51092c130f9056c92c130f1122472c13c510824b04c
|6=>0x424b04f1442472c13c5e8424b04f1440c92c13c5108
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619545f61658536135847610583b60d582f60a58236
|6,0=>0x6fddb876c5daa768dd9c765998f762598275edd7475b5d66757dd587545d4a750dd3c74d5d2e74a19217469d13743590674018f973c9ceb7391cdd7359ccf73294c372f1cb752c1ca97289c9b7251c8e6
|7,0=>0xb01ab88ac9aab7a91e9c8a5228e6a1a27e89da26f79a1e62696de547935e4678fde3878c5e2a788de1b8855a0f681e20077e21f177a9de3776e1d38731dc66
|8,0=>0xc41f097c09efb7bd5aee7b9dee07b69ad37b35ac67
|9,0=>0x3176
|_,_=>0
def wAt:=mkWire dB 59 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4f453d205c92d24c4932245441c2cf4b49245493214f6317505441c2cf423f05289153c5441504f481724b431724f432f24f493114f44152c5492d25054151070b3d24549152c9593d0520915205492d245483024b48302c954151070b3d205492d0c20b1524f54151070b3d2504915
|1=>0x24c453d2cf4b2520f4b2504f4b2508fcb1520f4b252414b3d045443d2d7813d24f413d0c20b1524f441e2cf4b2505209151054b1564f414824548303c5492d20c5207245481524b491504f4b323c549152c3493da8bc23d2c5483f14a441e2cf441514f493214f4f152c54b3d2cc8b15
|2=>0xb3d101493d24b4b113c5443d105c91104f4415105413d2cf41151070b3d24c853d48449152c5493d24c853d1054f152454b3d3c5492d0c5493d24f4b2524f453d105413f24f44170cbc93d6c9c41524c453d20fcb25105c92d2c54b3d2c5413d2454f150cb493d052891504fc417
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x11000000000001000
|5,0=>0x1a40001910000001811440001221110f20d20000a3082053000023
|6,0=>0x6930006720000000006436225f30005c30005b15925725615330005215024d34c14934724520004234113e33c23a20003733523323212f32e12c22932720002522322121e3
|7,0=>0xb22b02ae2ac2aa2a82a62a42a22a029e29c29a29829629429229028e28c28a28828628428228027e27c27a27827627427227026e26c2
|8,0=>0xbe1bd1bc1bb1000ba1b91b81b71b61b51b41
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x8f000010ac00020000003bd00007080000c800001840000300000055200004f400009680001200000232000046000008200001010000108000020000003c0000025000004000000500000088000010000001400000240000040000005000000800000080000008000000
|1=>0x1006220200c2404018080690b500ccef801795e402723c804d47900909fa00a51f40100128010479001fafa00351f400633e800bd7900178f2002cc640056fc800a5790013afa00264c4004a3c80090b10008022000b1e40012fc80024f900029f200013e400023d8000479
|2=>0x202723ca00c47b201f8f2200300c22a23c8404c01040180606293f40c527681800a502949da05091e408527e808ad790114ef202293f404523c808a019
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x1000000100
|5,0=>0x380040000e1a0008210100050224005
|6,0=>0x4833a000003e65a113800d8120386001c21a984e6430050615107a00390243cf1816cc0832828d3b
|7,0=>0x672d0ac74549b22e59fc980c52c2730e2a478ad7484c89f4790b5b4a9d317c4
|8,0=>0x6f3e0c641414cd4745838
|9,0=>0x20
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_81 4 roots_81 ops++addP pm 2 dzo_82_32 4 roots_82 ops++addP pm 3 dom_107 7 roots_107 ops++addP pm 4 dom_59 7 roots_59 ops++addP pm 5 dom_115 7 roots_115 ops++addP pm 6 dom_91 7 roots_91 ops++addP pm 7 dom_82 4 roots_82 ops++addP pm 8 dzo_41_2 4 roots_41 ops++addP pm 9 dom_41 4 roots_41 ops++addP pm 10 dom_121 7 roots_121 ops++addP pm 11 dzo_121_2 6 roots_121 ops++addP pm 12 dzo_57_2 5 roots_57 ops++addP pm 13 dzo_105_2 5 roots_105 ops++addP pm 14 dzo_91_32 6 roots_91 ops++addP pm 15 dzo_90_32 5 roots_90 ops++addP pm 16 dom_73 4 roots_73 ops++addP pm 17 dom_51 4 roots_51 ops++addP pm 18 dzo_83_32 5 roots_83 ops++addP pm 19 dom_106 4 roots_106 ops++addP pm 20 dom_99 4 roots_99 ops++addP pm 21 dom_57 5 roots_57 ops++addP pm 22 dom_90 5 roots_90 ops++addP pm 23 dom_105 5 roots_105 ops++addP pm 24 dom_89 5 roots_89 ops++addP pm 25 dom_83 5 roots_83 ops++addP pm 26 dom_75 5 roots_75 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_41_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_121_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_57_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_105_2_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_123 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_123 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_123 roots_123 goal_123 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_123
theorem lowS_123:Lower true dom_123 roots_123 goal_123 10:=S_123.noCircuit
def dzo_89_4:=0x303030300000000030303030
def gzo_89_4:=0x303030200000000020202000
def gsh_89_4:=0x30303020000000002020200
theorem lowS_zo_89_4_89:Lower true dzo_89_4 roots_89 gzo_89_4 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_4) [(dom_89,4)] (by decide +kernel) (lower_slice_b (T:=gsh_89_4) [] (by decide +kernel) lowS_89)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030203030303020202000
def gsh_121_4:=0x3030303030303020303030302020200
theorem lowS_zo_121_4_89:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_89)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,36),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,44),(12,76),(16,17),(16,80),(20,21),(20,52),(20,84),(24,25),(24,56),(24,88),(28,29),(28,60),(28,92),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(64,65),(64,72),(64,80),(68,69),(68,76),(68,84),(68,100),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|4=>3
|5=>10
|6=>17
|7=>7
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x883e37cac47003b
|5,0=>0xf0f28843cf73b466ee9b6c6533247c26b5d1bd4310f4a044c1
|6,0=>0xfe5c8db521d76c3ca6a8c218fbafe3894b282b8a7ca296926e5d3c55c34449e74413a63af32239670fd4d
|7,0=>0xcfb04c8781c68b0b324d8e22674b3a0f7ba
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00cc00cc0088008b23232323232323232323232323232320000cccc0000cccc000088880000888800033330000333300000000000022220c0c0c0c000000008c8c8c8c8888888a2222222222222222222222222222222888888888888888888888888000000033332222333322223333222233330000cc00cc00cc00cc00cc00cc00cc00cc033333333000000003333333300000000cccccccccccccccc888888888888888b3333333222222223333333322222222cccc0000cccc0000cccc0000cccc00033223322332233223322332233003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c33333333333333330000000000000000
|0,1=>0x8c8c8c8c888888888c8c8c8c8888888b0303030303030303232323232323232cccccccccccccccccccccccc888888880000000000000003333333322222222444444444444444444444444000000000000000333333330000000022222222cccccccccccccccccccccccc000000000000000000000000000000022222222cccccccc00000000cccccccc888888880000000222222220000000022222222cccccccccccccccc000000008888888800000000000000022222222222222220000cccc0000cccc0000cccc000088883030303000000000303030300000000
|_,_=>0
def sP:Nat→Nat
|0=>0x38559018670ab0030ce155806384aa682a619c2a018e15340619c2a980c33aa50018e1544063aa0d0186153c063b94d018e15300641c2a018620a80619d6a018670952419c2901907094c3104a418820
|1=>0x30ce1500c338554018675400619c2a900c33b94030ce12a81730ce15008619c2a01867ea80619f8a018672aa00d98670a80619dc5500c33854905cc3384aad18670a804b8ce1500c3
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa5055005
|5,0=>0x4563f63963362d62762161b61560f6
|6,0=>0xb96b36ac7a579e79779078978277b77476d76675f75965274b7
|7,0=>0xe77e16da7d46cd7c67bf7
|8,0=>0xee6
|_,_=>0
def wAt:=mkWire dB 30 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x32a3075030a95013013295413070c95033075013155010a9501ba8301301501301329bab301316501baa301196501349503196501a0132a503307
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1e2709a2609625092200102388c2288821884208802
|7,0=>0x261946418c62184601
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 10
def pmP:Nat→Nat
|0=>0xffdfd777715f5745221d110b09060400
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0xbb262a80433323517
|7,0=>0xecdfdae
|8,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_61 6 roots_61 ops++addP pm 2 dom_109 7 roots_109 ops++addP pm 3 dzo_89_4 5 roots_89 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dzo_121_4 6 roots_121 ops++addP pm 6 dom_89 5 roots_89 ops++addP pm 7 dom_124 5 roots_124 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_89_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_121_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_124 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_125 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_125 roots_125 goal_125 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_125
theorem lowS_125:Lower true dom_125 roots_125 goal_125 9:=S_125.noCircuit
theorem lowS_126:Lower true dom_126 roots_126 goal_126 8:=lower_slice_b [(0x50505050505050505050505050505050,32,36)] (by decide +kernel) lowS_122
def dzo_185_2:=0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def gzo_185_2:=0xc0c0c0c0c0c0c0800000000000000000c0c0c080c0c0800
def gsh_185_2:=0x30303030303030200000000000000000303030203030200
theorem lowS_zo_185_2_169:Lower true dzo_185_2 roots_185 gzo_185_2 8:=lower_iso_b (d1:=dom_185) (r1:=roots_185) (T1:=gsh_185_2) [(dom_185,2)] (by decide +kernel) (lower_slice_b (T:=gsh_185_2) [(0x30300000303000000000000000000000303000003030000,0,16)] (by decide +kernel) lowS_169)
namespace S_187
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,129),(2,18),(3,11),(3,19),(3,35),(3,131),(8,9),(8,40),(8,136),(10,11),(10,26),(10,42),(10,138),(16,17),(16,18),(24,25),(24,26),(24,56),(24,152),(32,33),(32,40),(32,160),(34,35),(34,42),(34,50),(34,162),(48,49),(48,50),(48,56),(48,176),(128,129),(128,136),(128,160),(130,131),(130,138),(130,146),(130,162),(144,145),(144,146),(144,152),(144,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_187.map (·&&&dom_187)
def gM:=goal_187&&&dom_187
def NN:Nat→Nat
|4=>3
|5=>24
|6=>55
|7=>20
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x3d10b2b14e1a966
|5,0=>0x8f8bf6eecb6b0ae46f123f1c038e96360fa34b6033d2f322b7312fb2ebee2e8922e63f2b14e2b02e2aeb021b330e7fc0e6950d9d20c20707afe038bf
|6,0=>0xec573d379ed170bae7e49ff068f8bf8ac5d89c488207d72ccd6af58617965eddd5124147a2f458744519f42ab24233f415813f1c03e51f3dede37fed2fbb92ed982e04d2d2bb29e2924ae5242b521b332180e1f1931ec351de0b194a0177e51624815cee1499f13fb613466120ae1170b0f01d0bc990aeee0aab708cf207dcd078000721b0263e0252b
|7,0=>0x8852f870cc5a46052dbc4f67f4519f4500e44f704383834d77308282e55a2b4d120c571705f149440bb7c06c3706719064fc
|8,0=>0x9cc772d78826f6b
|9,0=>0x3dbb0
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0a0a0a0a00000000000000000f000f000a000a00f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0aa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f000f000f000f00f0f0f0f0f000f0000000000000000000a0a0a0a0a000a00f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a000a00f0f00000f0f000000000000000000000f0f00000f0f0000f000f000f0a0f0a00000000000000000f000f000f0a0f0ac0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000f0f0f0f0000000000000000000000000f000f00
|0,1=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0aa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a000a005000500050a050a000000000000000005000500050a050af0a0f0a0f0a0f0a00000000000000000f0a0f0a0f000f00a0f0a0f0a0f0a0f00000000000000000a0f0a0f0a0a0a0a00a000a000a000a0000000000000000000a000a000a000aa0a0a0a0a000a0000000000000000000a0a0a0a0a000a00f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0a0f0a0f0a0f0a00000000000000000f0a0f0a0000000000000000000000000000000000000000f0a0f0a0f0a0f0a00f000f000f000f0000000000000000000a000a000a000a00000000000000000000000000000000f0f0f0f0f0a0f0a5050505050005000000000000000000050505050500050000000000000000000000000000000000f0f0f0f0a0a0a0af000f000f000f0000000000000000000f000f000a000a00f0f0f0f0000000000000000000000000f0f0f0f00000000
|0,2=>0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a00000000f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f000000000000000000000000000000000000f0f0f0f0f000f00a0a0a0a0a0a0a0a00000000000000000a000a000a000a00f0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0a00f000f000a000a0000000000000000000f000f000a000a00f000f000f000f0000000000000000000f000f000a000af0f0f0f0000000000000000000000000f0a0f0a0000000000000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f0a0a0a0a00000000000000000f0f0f0f0a000a00f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0000000000f0a0f0a0000000000000000000000000f0a0f0af0f0f0f000a000a00000000000000000f0f0f0f000a000af0f0f0f0f0f0f0000000000000000000f0f0a0a0f0f0a0000000000a0a0a0a0000000000000000000000000a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00
|0,3=>0xf0f0f0f0505050500000000000000000f000f0005000500f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0a0f0af0f0f0f0000000000000000000000000f0f0f0f0a0a0a0a00000000505050500000000000000000000000005000500f0f0f0f0f0f0f0f0000000000000000000f000f000a000af0f0f0f0f0f0f0f00000000000000000f000f000f0a0f0aa0a0a0a0f0f0f0f00000000000000000a0a0a0a0f0a0f0a5000500050005000000000000000000050005000f000f000000000000a000a000000000000000000000000000a000a00000000000000000000000000000000f0f0f0f000a000a0000000000000000000000000000000000000000a0a0a0af0f0f0f0f0f0f0f0000000000000000000000000a0a0a0a00f000f000f000f0000000000000000000f000f00000000a000a000a000a0000000000000000000a000a000a0a0a0a00000000000000000000000000000000a0a0a0a0a0a0a0af000f000f000f0000000000000000000f0a0f0a0f0a0f0a
|0,4=>0x5050505050505050000000000000000050505050000000050505050505050500000000000000000505050505000500f050f050f050f0500000000000000000f050f050f000f00000000000000000000000000000000000000000000a000af0f0f0f0000000000000000000000000f0f0f0f000a000a0000000000f000f000000000000000000000000000a000a
|_,_=>0
def sP:Nat→Nat
|0=>0x208830214382060404021401c2180438f9008604820e103023c3880430080802010c023a38384381810e201011b34383840c08290085c48214402160428a9420103021434384120808406085001c302090428992201088214402061e0808d1810582141c20904203840c082840608080
|1=>0x1cb4804300850e3e488040c08510086012c1c50390081810a0e4021804a871f20103023438a0d20103021434804042950e201030214a4704502430214388040c085081c1c8042c1810e082c302149c70d0e1048214393040c0850e2094302143880412080a446302060404804220850e
|2=>0x81810a76388043058482144023a0c0850e0e402110428720201030202288040c09c8a1c10302140108e201010a70388040c080b71c508040c085362010302143869f081810a1c343840c0808e1810302144c70c201030214d08040c085321c34804600850e0e4020b0c087105c1810a
|3=>0x1208526201030214393040c0850e20121860428710081810a843a090081810a1c40206042a00e0e3020604045100819f82143880412085241c308040c0809a3e40211042871008181315439590081810a1cf88040c0850e0e10302149073d2010c060438804220850e201030214f0710
|4=>0x1c40206042960e18402060428d0e7a40206042872b0e4020604287201840206042872b1a4020604287072010c06043839008181311c488040c0850e18402060429a8e201030214dc7072440206042870c20104860428687081810a1c402060428f0e2010302151070718103020234604
|5=>0x8040c0850e2010302146870720103021438690081810a1c808040c0850e2010c06040450e0e402090c0850e201030214cc710081810a8a39590081810a
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0xa50154005
|5,0=>0x2618926231886620187a61d186e61a18626171856614184a611543f60e583360b5827608581b605580f6
|6,0=>0x2107825e0367f59f677c19e97789ddb7751dcd7719dbf76e1db176a9da37671d957639d886605d7a75cdd6c7595d5e755dd50752994374f593674bdd287485d1a744dd0c7415cff63e1cf173ad8e47375cd6733dcc87305cba72cdcac7295c9e7
|7,0=>0xa91e9c8a5228d7a19e7f79e1e7089a5e6189662518929e4378f1e3488b5e258879e177
|8,0=>0x2b97ac9eab7
|9,0=>0x2c06
|_,_=>0
def wAt:=mkWire dB 70 188 0xfffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1a290c410e3920291a2b20196a39182a1c4114cf181b1c416219143b3039141908bd1828203924390e3b144112280c290c39563b0e190e1b14410e391441563b1a29561b1a290c4116401229023414390c41303b141912290c39087940281a390c413441141b1c1d144114411c651a280c41303014191c41121c144112291c19
|1=>0x14411441143b0e3b1441182a1c411a2a0c410e3b14411c191c412029201940281a390c41402b1a390c4120391439144120191c191c4120b112280c39402a1a390c41024314391c292029203912870c39304314191c4114413043141920c5143b3e1818291c410e1b1441303b0c293e180e3914410cbf182820391a2a0c41563b
|2=>0x141b14410c411a390c411439141914410c39181b1c41182b1c411a290c4112280c392039141b6241143b0e19144118191c411a290c411419
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xf40000d20000000000000b2000000000000000074043000000000000000000022002
|6,0=>0x6e36b36836530006230005f30005d25a35825625510000000000005235024d30004b24920004630000000004334123e30003c20003a23733433223022d30002a32732522322121f21c30001a2173152132000
|7,0=>0x9729529329128f28d28b28928728528328127f27d27b2792772752732712
|8,0=>0x9b19a1991
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x404f737cbf2f4b72bc9f21470148511003f0f4300bc2a08c2007c1a060150400a020050100300800
|1=>0xf7f52c7daf67d27
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x30050000001c0000000109000000000141
|6,0=>0x170d92c04401001cf0453000000021c80052401800001051001c014d20104f4df6c14071d4007601040
|7,0=>0x9512a185d7127159166a262070e8de
|8,0=>0x1c71d
|9,0=>0x18
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_185 8 roots_185 ops++addP pm 1 dom_155 7 roots_155 ops++addP pm 2 dzo_185_2 8 roots_185 ops++addP pm 3 dom_59 7 roots_59 ops++addP pm 4 dom_179 7 roots_179 ops++addP pm 5 dom_186 6 roots_186 ops++addP pm 6 dom_147 4 roots_147 ops++addP pm 7 dom_169 7 roots_169 ops++addP pm 8 dom_27 4 roots_27 ops++addP pm 9 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_187 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_185_2_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_185 8 s (0,roots_185.map (·&&&dom_185)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_187 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_185 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff00000000ffffffff00000000,96)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_187==dom_187)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_187 gM v ys):RunD true dom_187 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_187 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 55 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_slice_b [(0x303030303030303000000000000000003030303030303030,32,36)] (by decide +kernel) lowS_185
theorem lowS_190:Lower true dom_190 roots_190 goal_190 7:=lower_slice_b [(0x444444444444444400000000000000004444444444444444,16,18),(0x555500005555000000000000000000005555000055550000,2,18)] (by decide +kernel) lowS_172
theorem lowS_207:Lower true dom_207 roots_207 goal_207 9:=lower_slice_b [(0xcccc000000000000cccc000000000000cccc000000000000cccc,64,66)] (by decide +kernel) lowS_205
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,67),(3,131),(8,9),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(16,17),(16,18),(16,80),(24,25),(24,26),(24,88),(24,152),(64,65),(64,66),(64,72),(64,80),(64,192),(128,129),(128,136),(128,192),(130,131),(130,138),(130,146),(130,194),(144,145),(144,146),(144,152),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_219.map (·&&&dom_219)
def gM:=goal_219&&&dom_219
def NN:Nat→Nat
|6=>1
|7=>5
|8=>2
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x3e9dd
|7,0=>0xca9655506332d042e7980aef3
|8,0=>0xa019f2fd77
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f0000f000f00000000000f000f00000000000f000f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5821765821076538217654821065a82107654321765a821765821796543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x2376e14735c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wAt:=mkWire dB 11 220 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1d98661d76601765a1786017660276619875d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff1aff3f7fafc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x5cfc
|8,0=>0x22
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_218 8 roots_218 ops++addP pm 1 dom_211 7 roots_211 ops++addP pm 2 dom_155 7 roots_155 ops++addP pm 3 dom_91 7 roots_91 ops++addP pm 4 dom_217 8 roots_217 ops++addP pm 5 dom_203 8 roots_203 ops++addP pm 6 dom_147 4 roots_147 ops++addP pm 7 dom_83 5 roots_83 ops++addP pm 8 dom_27 4 roots_27 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_27 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 8 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_219==dom_219)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_219 gM v ys):RunD true dom_219 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_219 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_219 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_slice_b [(0x50505050000000005050505000000000505050500000000050505050,128,132)] (by decide +kernel) lowS_218
def dzo_233_2:=0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2:=0xc0c00000c0c00000c0c00000c0800000c0c00000c0c00000c0800000800
def gsh_233_2:=0x30300000303000003030000030200000303000003030000030200000200
theorem lowS_zo_233_2_169:Lower true dzo_233_2 roots_233 gzo_233_2 8:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_2) [(dom_233,2)] (by decide +kernel) (lower_slice_b (T:=gsh_233_2) [(0x30300000303000000000000000000000303000003030000000000000000,0,64)] (by decide +kernel) lowS_169)
namespace S_235
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,66),(3,11),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,42),(10,74),(10,138),(32,33),(32,40),(32,160),(34,35),(34,42),(34,98),(34,162),(64,65),(64,66),(64,72),(64,192),(96,97),(96,98),(96,104),(96,224),(128,129),(128,136),(128,160),(128,192),(130,131),(130,138),(130,162),(130,194)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_235.map (·&&&dom_235)
def gM:=goal_235&&&dom_235
def NN:Nat→Nat
|6=>4
|7=>4
|8=>1
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x67bf3564403d0850d14f
|7,0=>0x5aa7e19020168de1439c
|8,0=>0x2ff10
|9,0=>0xfffda
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x50500000505000005050000050500000500000005000000050000000500f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000000f0f0000000000000f0f0000000000000f0a0000000000000f0af0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x854310865431087543108a549108543b108754931075432108a64916543210543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0x26e35833806
|7,0=>0x60ea5d139a8
|8,0=>0x377
|9,0=>0x3e6
|_,_=>0
def wAt:=mkWire dB 12 236 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x141635410354d63d41954c18798d505410354d8798d5061e63541
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x4998c6603
|7,0=>0x91409c4c2
|8,0=>0x141
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 9
def pmP:Nat→Nat
|0=>0x3ffeeeff5fc7f04c0b01c00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x3421
|7,0=>0x8657
|8,0=>5
|9,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dzo_233_2 8 roots_233 ops++addP pm 2 dom_169 7 roots_169 ops++addP pm 3 dom_227 7 roots_227 ops++addP pm 4 dom_203 8 roots_203 ops++addP pm 5 dom_234 7 roots_234 ops++addP pm 6 dom_107 7 roots_107 ops++addP pm 7 dom_226 4 roots_226 ops++addP pm 8 dom_99 4 roots_99 ops++addP pm 9 dom_106 4 roots_106 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_235 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_233_2_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_106 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_235 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_235==dom_235)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_235 gM v ys):RunD true dom_235 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_235 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
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
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
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
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030200000303000002000
def gsh_105_4:=0x303000003020000030300000200
theorem lowS_zo_105_4_73:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030200000303000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003020000030300000200
theorem lowS_zo_233_4_73:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000000000003030000000000000303000000000000030300000000,0,32),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_73)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,36),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,160),(64,65),(64,72),(64,192),(68,69),(68,76),(68,100),(68,196),(96,97),(96,100),(96,104),(96,224),(128,129),(128,132),(128,136),(128,160),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|5=>2
|6=>8
|7=>9
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x775a337de7
|6,0=>0xca2afc5661ae31d8200f745ae6acd5428be33e7b
|7,0=>0xd4d1baed4b9dfa1869347f085587984bbe33e8e734335
|8,0=>0xc5934c30fb5a879
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc000000cc000000cc000000cc0000008800000088000000880000008b3300000333000003330000033300000333000003330000033300000333000c8000000c8000000c8000000c8000000c8000000c8000000c8000000cb333000033330000333300003333000033220000332200003322000033220000000000000000cccc0000cccc00000000000000000000cc880000cc8b23200003232000032320000323200003232000032320000323200003232cc880000cc880000cc880000cc880000cc880000cc880000cc880000cc8b0300000303000003030000030300000303000003030000030300000303088880000888800008888000088880000888800008888000088880000888b30000003300000033000000330000003300000033000000330000003300cccc0000cccc0000cccc0000cccc0000000000000000000000000000000333300000000000033330000000000003333000000000000333300000000ccc80000ccc80000ccc80000ccc80000ccc80000ccc80000ccc80000cccb33300003333000033330000333300003300000033000000330000003300cccc0000cccc0000cccc0000cccc0000888800008888000088880000888b33300003333000000000000000000003333000033330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x687054c68705467d0546a10543670549681054268170426a7054c2687054687f054b68754e21704cb68754c6a105492810461d054361054b268754b6a1543210
|1=>0x4687054e6705496870542
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x56005
|6,0=>0x3863262b72471e61861260b7
|7,0=>0x7476e66866265b75474d74583e7
|8,0=>0x8968277b7
|9,0=>0x8f6
|_,_=>0
def wAt:=mkWire dB 16 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 12
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2196759527595a6e1d785d5e7619765d575595875952759516dd5c0c9d655d56859527595615e17559d755956a9e175661765d5c0c9d9859d75595
|_=>0
def oO:Nat→Nat→Nat
|5,0=>4
|6,0=>0x5cd43488f330c9318c42
|7,0=>0x2a2a0a6290a22809e2709a2
|8,0=>0x2e1b46c1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 10
def pmP:Nat→Nat
|0=>0x39cfce0e33ddde9cf467633b080fdc7773b399dccec66f2bf139c8ce443200008003c000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>1
|6,0=>0x2344e7a4e3
|7,0=>0x15549738b290
|8,0=>0x21e6
|9,0=>5
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 13 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dom_205 8 roots_205 ops++addP pm 2 dom_109 7 roots_109 ops++addP pm 3 dom_225 5 roots_225 ops++addP pm 4 dom_232 5 roots_232 ops++addP pm 5 dom_173 8 roots_173 ops++addP pm 6 dom_236 7 roots_236 ops++addP pm 7 dom_101 4 roots_101 ops++addP pm 8 dzo_105_4 5 roots_105 ops++addP pm 9 dzo_233_4 6 roots_233 ops++addP pm 10 dom_229 7 roots_229 ops++addP pm 11 dom_228 5 roots_228 ops++addP pm 12 dom_108 4 roots_108 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_105_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_233_4_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_108 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_180_2:=0x4400440044004400000000000000000044004400440044
def gzo_180_2:=0x4400440044004000000000000000000044004000440000
def gsh_180_2:=0x1100110011001000000000000000000011001000110000
theorem lowS_zo_180_2_164:Lower true dzo_180_2 roots_180 gzo_180_2 5:=lower_iso_b (d1:=dom_180) (r1:=roots_180) (T1:=gsh_180_2) [(dom_180,2)] (by decide +kernel) (lower_slice_b (T:=gsh_180_2) [(0x1100000011000000000000000000000011000000110000,0,16)] (by decide +kernel) lowS_164)
def dzo_114_4:=0x500050005000500050005000500050
def gzo_114_4:=0x500050005000400050005000400000
def gsh_114_4:=0x50005000500040005000500040000
theorem lowS_zo_114_4_82:Lower true dzo_114_4 roots_114 gzo_114_4 5:=lower_iso_b (d1:=dom_114) (r1:=roots_114) (T1:=gsh_114_4) [(dom_114,4)] (by decide +kernel) (lower_slice_b (T:=gsh_114_4) [(0x50005000000000005000500000000,0,32)] (by decide +kernel) lowS_82)
def dzo_166_16:=0x5500000055000000000000000000000055000000550000
def gzo_166_16:=0x5500000054000000000000000000000054000000440000
def gsh_166_16:=0x550000005400000000000000000000005400000044
theorem lowS_zo_166_16_164:Lower true dzo_166_16 roots_166 gzo_166_16 5:=lower_iso_b (d1:=dom_166) (r1:=roots_166) (T1:=gsh_166_16) [(dom_166,16)] (by decide +kernel) (lower_slice_b (T:=gsh_166_16) [(0x440000004400000000000000000000004400000044,0,2)] (by decide +kernel) lowS_164)
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054005000000000
def gsh_86_32:=0x5500540000000000540050
theorem lowS_zo_86_32_82:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x5000500000000000500050,0,4)] (by decide +kernel) lowS_82)
def dzo_230_16:=0x55000000550000005500000055000000550000005500000055000000550000
def gzo_230_16:=0x55000000550000005500000054000000550000005500000054000000440000
def gsh_230_16:=0x5500000055000000550000005400000055000000550000005400000044
theorem lowS_zo_230_16_164:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso_b (d1:=dom_230) (r1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (lower_slice_b (T:=gsh_230_16) [(0x4400000044000000440000004400000044000000440000004400000044,0,2),(0x5500000055000000000000000000000055000000550000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_244_2:=0x44004400440044004400440044004400440044004400440044004400440044
def gzo_244_2:=0x44004400440044004400440044004000440044004400440044004000440000
def gsh_244_2:=0x11001100110011001100110011001000110011001100110011001000110000
theorem lowS_zo_244_2_164:Lower true dzo_244_2 roots_244 gzo_244_2 6:=lower_iso_b (d1:=dom_244) (r1:=roots_244) (T1:=gsh_244_2) [(dom_244,2)] (by decide +kernel) (lower_slice_b (T:=gsh_244_2) [(0x11000000110000001100000011000000110000001100000011000000110000,0,16),(0x11001100110011000000000000000000110011001100110000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_242_4:=0x50005000500050005000500050005000500050005000500050005000500050
def gzo_242_4:=0x50005000500050005000500050005000500050005000400050005000400000
def gsh_242_4:=0x5000500050005000500050005000500050005000500040005000500040000
theorem lowS_zo_242_4_82:Lower true dzo_242_4 roots_242 gzo_242_4 6:=lower_iso_b (d1:=dom_242) (r1:=roots_242) (T1:=gsh_242_4) [(dom_242,4)] (by decide +kernel) (lower_slice_b (T:=gsh_242_4) [(0x5000500000000000500050000000000050005000000000005000500000000,0,32),(0x5000500050005000500050005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_228_2:=0x4400000044000000440000004400000044000000440000004400000044
def gzo_228_2:=0x4400000044000000440000004000000044000000440000004000000000
def gsh_228_2:=0x1100000011000000110000001000000011000000110000001000000000
theorem lowS_zo_228_2_164:Lower true dzo_228_2 roots_228 gzo_228_2 5:=lower_iso_b (d1:=dom_228) (r1:=roots_228) (T1:=gsh_228_2) [(dom_228,2)] (by decide +kernel) (lower_slice_b (T:=gsh_228_2) [(0x1100000011000000000000000000000011000000110000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_210_4:=0x500050000000000050005000000000005000500000000000500050
def gzo_210_4:=0x500050000000000050005000000000005000400000000000400000
def gsh_210_4:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_4_82:Lower true dzo_210_4 roots_210 gzo_210_4 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_4) [(dom_210,4)] (by decide +kernel) (lower_slice_b (T:=gsh_210_4) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500550000000000550054000000000054005000000000
def gsh_214_32:=0x550055000000000055005500000000005500540000000000540050
theorem lowS_zo_214_32_82:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso_b (d1:=dom_214) (r1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (lower_slice_b (T:=gsh_214_32) [(0x500050000000000050005000000000005000500000000000500050,0,4),(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_246
def pG:List (Nat×Nat):=[(2,18),(2,66),(4,36),(4,132),(6,22),(6,38),(6,70),(6,134),(16,18),(16,80),(20,22),(20,52),(20,84),(20,148),(32,36),(32,160),(34,38),(34,50),(34,98),(34,162),(48,50),(48,52),(48,112),(48,176),(64,66),(64,80),(64,192),(68,70),(68,84),(68,100),(68,196),(96,98),(96,100),(96,112),(96,224),(128,132),(128,160),(128,192),(130,134),(130,146),(130,162),(130,194),(144,146),(144,148),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_246.map (·&&&dom_246)
def gM:=goal_246&&&dom_246
def NN:Nat→Nat
|4=>1
|5=>3
|6=>9
|7=>18
|8=>10
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x27e61
|5,0=>0x48de732fe91c3fd
|6,0=>0xc483e7e0924b42e3501f1e4331e2b819dd40438d0395e
|7,0=>0xc602dc22b58544a8199064c8c5e0d74c5704a1b741a0c419c32e55e291fa219751480513702112dd0ed0a0de7a
|8,0=>0xc602d9b55a5b9963f43d300172070317b541122d0d67009fc4
|9,0=>0x3f43d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaa00aa00aa00aa008800880088008800aa00aa00aa00aa00880088008800880001540000015400000110000001100000015400000154000001100000011000000002a802a80000000002a802a8000000000000000000000000000000044004400440044004400440044004400440044004400440044004400440044aa00aa00aa00aa00aa000000aa000000aa00aa00aa00aa00aa000000aa000014001400140014001400140014001400000000000000000000000000000002800280028002800280028002800280028002800000000002800280000000011001100110011001100000011000000110011001100110011000000110000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0000000110011001100110011000000110000001100110011001100110000001100000280028002800280028002800280028002800280000000000280028000000055000000550000005500000055000000550000005500000055000000550000aa00aa0088008800aa00aa0088000000a800a80088008800a800a00088000140014001400140014001400140014001400140014001400140014001400142a802a802a802a8000000000000000002a802a802a802a800000000000000055005500550055005500550055005500000000000000000000000000000000
|0,1=>0xaa00aa00aa00aa00aa00aa00aa00aa0022002200220022000000000000000000000000000000015401540000000001540154000000000154015400000000880088008800880000000000000000008800880088008800000000000000051005100510051005000500050005000510051005100510050005000500050aa00aa00aa00aa00aa00aa0000000000aa00aa0000000000aa00aa000000000000000154015400000000000000000000000001540154000000000000000280028002a802a802800280028002800280028002a802a8028002800280028000000000000000000000000000000005500550055005500000000000000000000000000000000aa00aa00aa00aa0000000000000000000000000000000154015401540154000000000000000000000000000000000000000000000002a802a802a802a802a802a802a802a802a802a802a802a800000000000000000000000000000005500550055005500550055005500550000000000000000aa00aa00aa00aa00aa00aa00aa00aa00a000a000a000a000a000a000a000a044004401540154000000000154015400440044004400440000000000000002a802a80280028002a802a80280028002a802a80280028002a802a8028002855000000550000004400000044000000550000005500000044000000440000
|0,2=>0x154015401540154014001400140014001540154015401540140014001400142a002a002a002a002a002a002a002a002a002a002a002a002a002a002a002a55005500550055005500550055005500550055000000000055005500000000aa008800aa008800aa008800aa008800aa008800aa008800aa008800aa0089100110011001100154015401540154000000000000000000000000000000000002a8000002a8000002a8000002a8000000000000000000000000000000044000000440000004400000044000000440044004400440044004400440044
|_,_=>0
def sP:Nat→Nat
|0=>0x8c4010071023017c078408c0401c47023010111c408f30101b10230100711930100710231444708c3810071023155071130880401c44c218100710230148044708c40100708c38100d1c40860402871091810071081410071061410040c2040
|1=>0x71023010111c408c0401c408f30100712608c0401c49423010071023016801c408c0405871023150401c408c5561c408c05d00a1c43050401c44c23cc0404478c408c0404471023017401c408f30100a1c408c0408871023185c7102801007
|2=>0x1c408c0401c408c5410071023010171c408c05d
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x45816c056
|6,0=>0x4e523b905874e337163895c3ce177
|7,0=>0x190ec265d42d19590a484e425211ae87640b1ed8e8e6e633b97e0b2c536
|8,0=>0x21af0677fbbe59e4eeb7723b75dacecf7
|9,0=>0x1146
|_,_=>0
def wAt:=mkWire dB 39 247 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4041023018709301420508c4706040015d0408101040020230182921c0420130144311c2470930182023015d0230181030408c87100843c3015d01301875b00102753018709301475900102691c1985d040c10210f8c05556c1010400c2e1014c2c101443c301443e3014c2c0808405
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x1031c42cc4907200014819003
|7,0=>0x1a9332624bc9692b25249c9292324247c8e91b23245c8a9132
|8,0=>0x1f8be17a2001e0bb1742e45c0b71
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x1901762202c4105412fe7117ce0ae9485d283fe505fc84ab901f712aae2277440ee881550c80a150140e02809ff012fe0255404828087d00aae0085000ff800ff000aa00100000200000
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x40942100446
|7,0=>0x1854e1cfe364b41e35cf777
|8,0=>0x18c82bd3b6a8c
|9,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_244 7 roots_244 ops++addP pm 1 dzo_180_2 5 roots_180 ops++addP pm 2 dom_242 7 roots_242 ops++addP pm 3 dzo_114_4 5 roots_114 ops++addP pm 4 dom_230 7 roots_230 ops++addP pm 5 dzo_166_16 5 roots_166 ops++addP pm 6 dom_214 7 roots_214 ops++addP pm 7 dzo_86_32 5 roots_86 ops++addP pm 8 dom_182 6 roots_182 ops++addP pm 9 dzo_230_16 6 roots_230 ops++addP pm 10 dzo_244_2 6 roots_244 ops++addP pm 11 dom_118 6 roots_118 ops++addP pm 12 dom_164 4 roots_164 ops++addP pm 13 dom_228 5 roots_228 ops++addP pm 14 dzo_242_4 6 roots_242 ops++addP pm 15 dzo_228_2 5 roots_228 ops++addP pm 16 dzo_210_4 5 roots_210 ops++addP pm 17 dzo_214_32 6 roots_214 ops++addP pm 18 dom_210 5 roots_210 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_246 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_180_2_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_114_4_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_166_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_230_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_244_2_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_242_4_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_228_2_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_210_4_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_214_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_210 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_244 7 s (0,roots_244.map (·&&&dom_244)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_246 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_246==dom_246)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_246 gM v ys):RunD true dom_246 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_246 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_246 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_246 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_246 roots_246 goal_246 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_246
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=S_246.noCircuit
def dzo_218_32:=0x505050500000000050505050000000005050505000000000505050500000000
def gzo_218_32:=0x505050500000000050505050000000005050504000000000504050000000000
def gsh_218_32:=0x5050505000000000505050500000000050505040000000005040500
theorem lowS_zo_218_32_82:Lower true dzo_218_32 roots_218 gzo_218_32 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_32) [(dom_218,32)] (by decide +kernel) (lower_slice_b (T:=gsh_218_32) [(0x5000500000000000500050000000000050005000000000005000500,0,8),(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_248_2:=0x404040404040404040404040404040404040404040404040404040404040404
def gzo_248_2:=0x404040404040404040404040404040004040404040404040404040004040000
def gsh_248_2:=0x101010101010101010101010101010001010101010101010101010001010000
theorem lowS_zo_248_2_168:Lower true dzo_248_2 roots_248 gzo_248_2 6:=lower_iso_b (d1:=dom_248) (r1:=roots_248) (T1:=gsh_248_2) [(dom_248,2)] (by decide +kernel) (lower_slice_b (T:=gsh_248_2) [(0x101000001010000010100000101000001010000010100000101000001010000,0,16),(0x101010101010101000000000000000001010101010101010000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_184_2:=0x40404040404040400000000000000000404040404040404
def gzo_184_2:=0x40404040404040000000000000000000404040004040000
def gsh_184_2:=0x10101010101010000000000000000000101010001010000
theorem lowS_zo_184_2_168:Lower true dzo_184_2 roots_184 gzo_184_2 5:=lower_iso_b (d1:=dom_184) (r1:=roots_184) (T1:=gsh_184_2) [(dom_184,2)] (by decide +kernel) (lower_slice_b (T:=gsh_184_2) [(0x10100000101000000000000000000000101000001010000,0,16)] (by decide +kernel) lowS_168)
def dzo_170_16:=0x50500000505000000000000000000000505000005050000
def gzo_170_16:=0x50500000504000000000000000000000504000004040000
def gsh_170_16:=0x5050000050400000000000000000000050400000404
theorem lowS_zo_170_16_168:Lower true dzo_170_16 roots_170 gzo_170_16 5:=lower_iso_b (d1:=dom_170) (r1:=roots_170) (T1:=gsh_170_16) [(dom_170,16)] (by decide +kernel) (lower_slice_b (T:=gsh_170_16) [(0x4040000040400000000000000000000040400000404,0,2)] (by decide +kernel) lowS_168)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500050000000000050004000000000004000000000000
def gsh_210_32:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_32_82:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (lower_slice_b (T:=gsh_210_32) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_232_2:=0x40400000404000004040000040400000404000004040000040400000404
def gzo_232_2:=0x40400000404000004040000040000000404000004040000040000000000
def gsh_232_2:=0x10100000101000001010000010000000101000001010000010000000000
theorem lowS_zo_232_2_168:Lower true dzo_232_2 roots_232 gzo_232_2 5:=lower_iso_b (d1:=dom_232) (r1:=roots_232) (T1:=gsh_232_2) [(dom_232,2)] (by decide +kernel) (lower_slice_b (T:=gsh_232_2) [(0x10100000101000000000000000000000101000001010000000000000000,0,64)] (by decide +kernel) lowS_168)
def dzo_234_16:=0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16:=0x505000005050000050500000504000005050000050500000504000004040000
def gsh_234_16:=0x50500000505000005050000050400000505000005050000050400000404
theorem lowS_zo_234_16_168:Lower true dzo_234_16 roots_234 gzo_234_16 6:=lower_iso_b (d1:=dom_234) (r1:=roots_234) (T1:=gsh_234_16) [(dom_234,16)] (by decide +kernel) (lower_slice_b (T:=gsh_234_16) [(0x40400000404000004040000040400000404000004040000040400000404,0,2),(0x50500000505000000000000000000000505000005050000000000000000,0,64)] (by decide +kernel) lowS_168)
namespace S_250
def pG:List (Nat×Nat):=[(2,18),(2,66),(8,40),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(24,26),(24,56),(24,88),(24,152),(32,40),(32,160),(34,42),(34,50),(34,98),(34,162),(48,50),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(96,98),(96,104),(96,112),(96,224),(128,136),(128,160),(128,192),(130,138),(130,146),(130,162),(130,194),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_250.map (·&&&dom_250)
def gM:=goal_250&&&dom_250
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x95bcf8ad467aba81bd5f
|6,0=>0xddb6fb3717861d77bb81778cc6467451002444af3e24233bfa1f491119d00f5b70aac807785
|7,0=>0xfc02cde685dca689b54e994119134985ac6772f16a2896972c608e8605c55f1485a5ae3f3d73bcf636ac0361a91e4cb182211188a1104e0818a0087a
|8,0=>0xd1842ce3db702a05cbfc4679b391271cf3212b8d
|9,0=>0xef2e1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xa000a0a0a000a0a0a000a000a000a000a000a0a0a000a0a0a000a000a000a014141414141414141414141414141414140014001400140014001400140014028282828282828282828282828282828282828282828282800000000000000050505050505050505050505050505050505050505050505050005000500050020202020a0a0a0a000000000a0a0a0a020202020a020a02000000000a000a0141414140000000014141414000000001414141400000000141414140000000000000000000000000000000000000002828282828282828280028002800280005000500050005000500050005000500050005000500050000000000000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0001010101010101010101000001010000010101010101010101010000010100002800280028002800280028002800280028002800280028002800280028002804040404040404040404040404040404040404040404040404040404040404040000a0a00000a0a000008080000080800000a0a00000a0a000008080000080800000001414141400000000141414140000000014001400000000001400140282828282828282800000000000000002828282828282828000000000000000505050505050505050505050505050500000000000000000000000000000000
|0,1=>0xa0a0a0a020202020a0a0a0a000000000a0a0a0a020202020a0a0a0a000000004040404040404040404000004040000040404040404040404040000040400028282828282828282828000028280000282828282828282828280000282800050405040504050405040504050405040504050405040504050405040504050400000000000000000000000000000000a080a080a080a080a080a080a080a094141414141414141414141400000000141414141414141414141414000000000280028002800280000000000000000002800280028002800000000000000050504040505040405050404050504040505040405050404050504040505040400000000000000000000000000000000a000a0a0a000a0a0a000a000a000a0141414141414141400000000141414141414141414141414000000001400140282800002828000020200000202000002828000028280000202000002020000505050505050505040404040404040405050505050505050404040404040404a0a0a0a0a0a0a0a0a000a000a000a000a0a0a0a0a0a0a0a0a000a000a000a0040404040404040400000000000000000404040404040404000000000000000282828282828282828282828282828282808280828082808280028002800280000050500000505000000000000000000000505000005050000000000000000
|0,2=>0x141414141414141414141414141414141414000014140000141400001414000000000000000000000000000000000000028002800280028000000000000000505050505050505050505050505050505040504050405040504050405040504a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0202020202020202000000000000000000000000000000000000000000000001414141414141414000000000000000282828280028002828282828000000002828282800280028282828280000000505050505050505050505050505050500050005000500050000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xa1d310120060714408100a1d71440402874c914434a1d338434128e1440c100714458100714408148028e1445410071541020402874ce10d28744510100a1ce10d0482873ce10100a1cc2451011c510b0402872440481c51820401440c2040
|1=>0x4c91440401c510204028714404800a1cc1440402874c51220211c510101a1d314404028511504028731314404028714406000a1ce14405000a1d314434101f1c510100a1c578100a74738510100a1db14404028738510d05a1d314401a1c5119
|2=>0xa1c510100a1c510188028738510101a1c510100a1c510140028714434100a7471440402981c510100a9871440402981ce1440402874c510d00a1c510194028790510100a1c51018c0287
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce2e6a731b971caae4f6243905c74e34616b899c3ee187
|7,0=>0x8f445de20f097813bea1e8ced7733b7ddb2cd2766331217aeb5856c29d942c998493a2dd0ac7f6
|8,0=>0xab3d3de92d4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 39 251 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x454a65045ca05045541c101404d0454065045c5011c185050404a491019d131c147051405c0310545010404a050454117281450514d810128e8501013811514045050404501507c4051404a3a1404406140541c1014a3a140450114141013924501101853604050151c18c0314d4101
|1=>0x1031404a051c181011c147111c045011c445050404e061404e111405201101804e0454a3a140453604045350404006
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x80cf100038464cb19512463cc690a30e614819003
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x65e20c7440feb81fd3031aa05f4c0be8816db02da604fc408cd810db021a20210003cd8079900f220064c00c9001800013600248004000071000800004c00088000b000080000c000100000
|1=>0x31ae8e10114a5e28d3449ceb91fd713fae101c419f8832f3
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0x61c030e1434881d008a244
|7,0=>0x88f6a078d6d761175c58b6953a58687d1763
|8,0=>0x65491e6699e6
|9,0=>0x13
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_218 8 roots_218 ops++addP pm 1 dzo_82_32 4 roots_82 ops++addP pm 2 dzo_218_32 6 roots_218 ops++addP pm 3 dom_82 4 roots_82 ops++addP pm 4 dom_242 7 roots_242 ops++addP pm 5 dzo_248_2 6 roots_248 ops++addP pm 6 dom_248 7 roots_248 ops++addP pm 7 dom_122 7 roots_122 ops++addP pm 8 dom_186 6 roots_186 ops++addP pm 9 dzo_184_2 5 roots_184 ops++addP pm 10 dzo_170_16 5 roots_170 ops++addP pm 11 dzo_210_32 5 roots_210 ops++addP pm 12 dom_234 7 roots_234 ops++addP pm 13 dzo_232_2 5 roots_232 ops++addP pm 14 dom_232 5 roots_232 ops++addP pm 15 dom_210 5 roots_210 ops++addP pm 16 dzo_90_32 5 roots_90 ops++addP pm 17 dzo_234_16 6 roots_234 ops++addP pm 18 dom_168 4 roots_168 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_250 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_218_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_248_2_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_184_2_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_170_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_210_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_232_2_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_234_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_168 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_218 8 s (0,roots_218.map (·&&&dom_218)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_250 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_250==dom_250)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_250 gM v ys):RunD true dom_250 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_250 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_250 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_250 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_250 roots_250 goal_250 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_250
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=S_250.noCircuit
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_63
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_119
def isoMvS_215:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_iso_b isoMvS_215 (by decide +kernel) lowS_125
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_189
def isoMvS_231:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_125
def isoMvS_238:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=lower_iso_b isoMvS_238 (by decide +kernel) lowS_125
def isoMvS_243:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 10:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 10:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_123
def isoMvS_249:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccccccccccccccccccccccccccc,126),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 9:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_125
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_123
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,32,36)] (by decide +kernel) lowS_187
theorem lowS_223:Lower true dom_223 roots_223 goal_223 11:=lower_slice_b [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,128,132)] (by decide +kernel) lowS_219
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,64,66)] (by decide +kernel) lowS_237
def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000ee0000
def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000fe000000ee
theorem lowS_zo_231_16_164:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso_b (d1:=dom_231) (r1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (lower_slice_b (T:=gsh_231_16) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc,0,2),(0xff000000ff0000000000000000000000ff000000ff0000000000000000,0,64)] (by decide +kernel) lowS_164)
def dzo_181_2:=0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc
def gzo_181_2:=0xcc00cc00cc00c8000000000000000000cc00c800cc0000
def gsh_181_2:=0x3300330033003200000000000000000033003200330000
theorem lowS_zo_181_2_165:Lower true dzo_181_2 roots_181 gzo_181_2 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_2) [(dom_181,2)] (by decide +kernel) (lower_slice_b (T:=gsh_181_2) [(0x3300000033000000000000000000000033000000330000,0,16)] (by decide +kernel) lowS_165)
def dzo_115_4:=0xf000f000f000f000f000f000f000f0
def gzo_115_4:=0xf000f000f000e000f000f000e00000
def gsh_115_4:=0xf000f000f000e000f000f000e0000
theorem lowS_zo_115_4_83:Lower true dzo_115_4 roots_115 gzo_115_4 6:=lower_iso_b (d1:=dom_115) (r1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (lower_slice_b (T:=gsh_115_4) [(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) lowS_83)
def dzo_167_16:=0xff000000ff0000000000000000000000ff000000ff0000
def gzo_167_16:=0xff000000fe0000000000000000000000fe000000ee0000
def gsh_167_16:=0xff000000fe0000000000000000000000fe000000ee
theorem lowS_zo_167_16_164:Lower true dzo_167_16 roots_167 gzo_167_16 6:=lower_iso_b (d1:=dom_167) (r1:=roots_167) (T1:=gsh_167_16) [(dom_167,16)] (by decide +kernel) (lower_slice_b (T:=gsh_167_16) [(0xaa000000aa0000000000000000000000aa000000aa,0,1),(0xcc000000cc0000000000000000000000cc000000cc,0,2)] (by decide +kernel) lowS_164)
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fa00000000
def gsh_87_32:=0xff00fe0000000000fe00fa
theorem lowS_zo_87_32_82:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_82)
def dzo_165_2:=0xcc000000cc0000000000000000000000cc000000cc
def gzo_165_2:=0xcc000000c80000000000000000000000c800000000
def gsh_165_2:=0x330000003200000000000000000000003200000000
theorem lowS_zo_165_2_165:Lower true dzo_165_2 roots_165 gzo_165_2 5:=lower_iso_b (d1:=dom_165) (r1:=roots_165) (T1:=gsh_165_2) [(dom_165,2)] (by decide +kernel) (lower_slice_b (T:=gsh_165_2) [] (by decide +kernel) lowS_165)
def dzo_83_4:=0xf000f00000000000f000f0
def gzo_83_4:=0xf000e00000000000e00000
def gsh_83_4:=0xf000e00000000000e0000
theorem lowS_zo_83_4_83:Lower true dzo_83_4 roots_83 gzo_83_4 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_4) [(dom_83,4)] (by decide +kernel) (lower_slice_b (T:=gsh_83_4) [] (by decide +kernel) lowS_83)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa
theorem lowS_zo_215_32_82:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_211_4:=0xf000f00000000000f000f00000000000f000f00000000000f000f0
def gzo_211_4:=0xf000f00000000000f000f00000000000f000e00000000000e00000
def gsh_211_4:=0xf000f00000000000f000f00000000000f000e00000000000e0000
theorem lowS_zo_211_4_83:Lower true dzo_211_4 roots_211 gzo_211_4 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_4) [(dom_211,4)] (by decide +kernel) (lower_slice_b (T:=gsh_211_4) [(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_83)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_32_82:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_229_2:=0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc
def gzo_229_2:=0xcc000000cc000000cc000000c8000000cc000000cc000000c800000000
def gsh_229_2:=0x3300000033000000330000003200000033000000330000003200000000
theorem lowS_zo_229_2_165:Lower true dzo_229_2 roots_229 gzo_229_2 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_2) [(dom_229,2)] (by decide +kernel) (lower_slice_b (T:=gsh_229_2) [(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) lowS_165)
def dzo_229_16:=0x33000000330000003300000033000000330000003300000033000000330000
def gzo_229_16:=0x33000000330000003300000032000000330000003300000032000000220000
def gsh_229_16:=0x3300000033000000330000003200000033000000330000003200000022
theorem lowS_zo_229_16_164:Lower true dzo_229_16 roots_229 gzo_229_16 6:=lower_iso_b (d1:=dom_229) (r1:=roots_229) (T1:=gsh_229_16) [(dom_229,16)] (by decide +kernel) (lower_slice_b (T:=gsh_229_16) [(0x2200000022000000220000002200000022000000220000002200000022,0,1),(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) lowS_164)
namespace S_247
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(3,19),(3,35),(3,67),(3,131),(4,36),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(20,148),(32,33),(32,36),(32,160),(34,35),(34,38),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,66),(64,80),(64,192),(68,69),(68,70),(68,84),(68,100),(68,196),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,132),(128,160),(128,192),(130,131),(130,134),(130,146),(130,162),(130,194),(144,145),(144,146),(144,148),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|5=>4
|6=>17
|7=>45
|8=>79
|9=>50
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xdc52ad94bb7d1f2617a8
|6,0=>0xb3a40b09d1a6a2fa64eb93daf8bc817597456163529e34d3153874c32fab26397204c81c2b30da2303290
|7,0=>0xfe62ef3e7bcfa35cedccbef63afae9aac81a1a2c893bc852438299b7f45c7bcdc77ac7718b366ecf5feb4587ca54a5e51ebf4f6904b16548387458393f27f3c1c13a4772b9542b77a28ee52628624bcf218c31aef417a5a171eb1595c133941331d12ca70ad360ab2908dc705e4d00675
|8,0=>0xed1d4eb970e84c1c6bf9c2ee1c1fc3bf694af8d6ad481acab8abb37a5eff9a1eb97807959148fb0b8afe287ab783bf283b7881f17808fd7b3ef76fba767087118168ded6725c62486608d25ebad5ea7d5aae357d5d54c4d4feb24f5594c6a549c61475f5463aa429c44194b3d9793c8fc3c1c13bfa03bb8238e25378c9321262fcab2a7f22a24f2996e2964f23806233e2204ec1fbff1d7001cd251b57019b8a18c0e1703c141ab10a820f7140d92c0bd4a0ab290a1a307b0d0788704e3401def00aa4001d7
|9,0=>0xe031ad91c4c7691b5c68b2322ae51e9fb1d9ac02968ac94e859188990afe896fc86b6985d968218f7b98c718376f03e6c2ad6713a661655ea7d5e70b5d0ec5b6865b2165766c55a5c5420748c35487bd432004194b403353d517360c334a6b32fc53248b30b152b0e82a751277bc14cc7104480f53809ec502040019af
|10,0=>0xf9dd7ae9b59ac0285a0a7fd216aad45fce307a19
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00cc00ff00ff00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa33003300330033003300330033003300330033003300330033000000330000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00aa00aa00aa00aa00ff00aa00ff00aa00aa00aa00aa00aa0f000f000f000f000f000f000f000f000f000f00000000000f000f00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f000f000f0aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa33003300330033003300000033000000330033003300330033000000330000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
|0,1=>0xff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff000000000000000000000000000000000000000000000000ff00ff00ff00ff00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00faff00ff00ff00ff00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00eeff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff000000000000000000ff000000ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00aa00ff00ff00aa00aa00aa00aa00ff00aa00ff00aa00aa00aa00aa00aaff00ff00ff00ff00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00cc00ccff000000ff00ff000000000000000000ff000000ff00000000000000000000ff000000ff00ff00ff000000ff00ff00ff000000ff000000ff000000ff000000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000
|0,2=>0xff00ff00ff000000ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00000000000000000000000000ff00ff00ff00ff0000000000000000330033003300000033000000330000003300330033003300330000003300000f000f000f000f000f000f000f000f000f000f0000000f000f000f0000000000000000000000005500550055005500550055005500550000000000000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000ff000000ff00ff000000000000000000ff000000ff0000ff00ff000000ff00ff00ff0000000000000000000000000000000000000000ff00ff000000ff00ff00ff0000000000ff00ff000000ff00ff00ff000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000ff00ff00f000ff00ff00ff00f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000000000000033000000330000003300000033000000330033003300330033000000330000000000000000000000000000ff00ff000000ff000000ff00000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000
|0,3=>0x330033003300330033000000330033003300330033003300330000003300000f000f00000000000f000f000f000f000f000f00000000000f000f00000000ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000cc00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00cc00cc00ff00cc00cc00000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000033003300330033003300330033003300330033003300330033003300330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00000000000000000000ff00ff00ff00ff00000000000000000000000000000000ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00f000ff00ff00f000f000f000f000ff00f000ff00f000f000f000f000f0ff00ff00ff00ff00ff00ff0000000000ff00ff00ff000000ff00ff000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000
|0,4=>0xff00ff00ff000000ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff000000ff000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000000ff000000ff0000000000000000ff00ff0000000000ff00000000000000ff00ff00ff00ff00ff000000ff00000000ff00ff00ff0000000000ff00ff000000ff000000ff00000000000000000000ff000000ff00000000000000ff000000ff000000ff0000000000000000ff00ff00ff00ff00ff000000ff0000000000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000cc00ff00cc00ff00cc00ff00cc00ff00cc00cc00cc00cc00cc00cc00cc00cc0000ff000000ff000000ff000000ff000000ff00000000000000ff00000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000550055005500550055005500550055005500550055005500550055005500000000000000000000ff00ff00ff00ff000000ff000000ff0000000000000000ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000
|0,5=>0xff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff0000000000ff00ff000000ff0000000000000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000000000000000000000000000000000000000000000000000ff00ff00ff0000000000000000000000000000000000000000ff000000ff000000ff00000000ff00ff00ff00ff00ff000000ff000000ff000000ff000000ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff000000ff00ff00ff000000000000000000000000000000000000000000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000033003300330033003300330033000000330033003300330033003300330000ff00ff00ff00ff00ff00ff00ff000000ff00ff0000000000ff00ff000000000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ff000000ff000000ff00ff00ff00ff00000000000000000000000000000000
|0,6=>0xff000000ff00000000000000000000000000000000cc00cc00cc00cc00cc00ff00cc00ff00cc00cc00cc00cc00cc00cc00cc00cc0000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff00000000000000000000ff00000000000000ff00000000000000000000000000000000cc00cc00cc00ff00cc00cc00cc00ff00cc00cc00cc00cc00cc00cc00cc00cc00000000000000000000000000000000ff00ff00ff00ff00ff000000ff00000000ff000000000000000000000000000000ff000000ff00000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff000000ff00000000000000000000ff00ff00000000000000ff0000000000ff00ff00000000ff000000ff000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00000000000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000
|0,7=>0xff000000ff000000ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff000000ff0000ff00ff0000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff000000000000ff00ff00000000000000000000000000ff00ff0000000000000000f000f000ff00ff00f000f000f000f000f000f000ff00ff00f000f000f000f0ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff00ff00ff00f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff000000ff000000ff00ff0000000000ff000000000000ff00ff00ff000000ff00ff00ff000000000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1618c8a0809107003828a08344880c2820d1208321141010b400070a0874e0614104820e18b8a08244070038d8a08344880c28d041a241060a40203120800a0808587003828a20344881c2880d125470a085010700385101a3c10e0a1068c02005041a3058614104880e182840608080
|1=>0x160148e362820d12083171440203120800e14c020d040400e144069404385041a096801c2820904b00231c6c5041a080801c2820d127c32b302820d040430e1440b09041c00e1410e893e1850450344820c3850448241001c1450404043801c28209041c0231c1420d04040191410682
|2=>0x2e145041a244001c2820d125400e0a10689040138a0835d0200385101a2440e722820d040400e1411c0d120830a0834136003828a083410b00385043a7000e1410682020148e14101010e00733141068202007310834482003850464241001c28209041c0171cc420d120830e1410682
|3=>0x94385041a2410092385161a241009028b0412083801c2820d8c083001410689051000e141068986007181410682161870a08344820d085041a09f801c288041209f001c2820d7a083001410689101870a08341010039e0a083448c0c148041a241003229a8412090001c145041a24106
|4=>0x834482008c70a6a10689040148e0a282511a241001c28209041c0251c282281a241001c288041a2410052385041af41001c2880412083801d3c5041a241001ccc510083448200385041a091001c145041a24100983854b08344820038c0a2c1068904185041a0808600385041a24100
|5=>0x156868904007591410689040070a0834482b0007310834482003828a2058689040070a082412000385101a241171c2820d055800eaa2820d120800ea62820d12083001c982841a241001c282381a241001c145041a24100463988a08344820038541083448200385041a24100263a90a
|6=>0x3628b041a24106002820d12080651c2b1841a241001c2820d12083191410689180070a083448280007620834482003b08a0834482003828a0834482005c70a0834482c02820d120800ebc282511a241061c2820d120ae86003ae0a08344820c0070514d420d120800e1410689056c00e
|7=>0x3888a08344820d805161a24100e0dc5041a241001c2820904803001c605041a24106a8385161a2415f00385041bb81001c2820d120b6001c2820d12083171c2820dd40800e0a2b4841a241001c295041a241001c2820d12080681c2820d040400e682820d280800e1410689059c00e
|8=>0x834482003b7981410689041800e145820d120ba001c28273120800e362820d12083001c28b041a24106006c5350834482003ae0a083448200385041a2417200385041a70f801c2820d1208300ca3828a2c10689041800a083449f0c1451008341010038504e23448200385100834101
|9=>0xc0070a083448201d870a08344828a0070a201068904007341410689040128e222ad0d120800e0a288041a241001c288041a241001c445041a241001c645041a2410600a470aea3448200385041a241001cf05041a24100a83828a2c10689040070a0834482003b5981410689053470a
|10=>0x385041a24106f2385350834482003b318083448200385102c34482003855a083448200385041a241001dc05041a241001defd0a08344820038504f0241001c2820d120a0001c2820d120bb801c282511a241001c2820d120802e1c145041a24106003930a0834482003b30a0834482
|11=>0x1a241001c28b041a241001c2820d120800e8e2820d120800e6860516083448200385041a241063c2a7041a241001c2820d120a6b414c020d120800e1410682020070afa10689040070a08344820c0070514104820e0070a083449f003857c0834482003ab8a083448200385041a2416d
|12=>0x5041a241001d985041a241001c2820d120800e3c2820d12083001c2820d12080251c28804
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x24c03180330006
|6,0=>0x8470fae1d9c37b86870c2e17142ab84e708ee101c1cb8327056e09580f38186
|7,0=>0x1d173930709cddb9b38358e695ccec197631f061e0bfc17782e0e5a5cb1395c62a90535ca3393e8270c4c2094b9218234e44dc85c10471f903d207640e481bcc35dc67c0c78180e2e205840aa6145026dc49c08b8
|8,0=>0x79d0f1dddfc3b78760ee9e5cfc397871f0e21dc0437796df0d9e1b03b5976a30d29da143399666ccae191c31a96232c2258042f975e30ba61713ad995a4eb2dd623abc85672aae151c29a95250a2a141427994e1299e52fc257849d291dd1fc237845d289dd0f4a16841d081a0ff41f683dee79e0f039d88
|8,1=>0x111a61f4436885ef09a60ecc17681d301a1fecbf677deef9e1efc3d69
|9,0=>0x2ed4dd37b971711ede45b57b5b16962cec5967b1d161a2bf45768add159a2af45568a9d151a29f45377a5f149e28fc5178a1d341a27eccf589db139266dccd47997330a65d44b19954f28a24d44919913120623cc47098cf3181e2bcc4f8
|10,0=>0xc37184e305c6038bf717ce2f5c5e38
|11,0=>0x6237
|_,_=>0
def wAt:=mkWire dB 126 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 15
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 8 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x143908013e1a04790039003820271c01080108390a37080114391a7d04791c011c00540308a5141a1c011a9d4c38149508020a37202714390801045d14392c000039083900391a7d127d047900381419045d2c000039083914391a6530380801140108011439045d2c000839044d240008450801143a0801124d24000845143a
|1=>0x8011439045d2c000801083930581401003908396e270a411439080114396a272c0108391a7d127d0479003820270a370801143914d120270801003a144d24000845143a1a4d24000845143a0a372c0014390839145d2c00003908392c001419003908391a65303808011401125d2c00080108395e2708b92202143a0a012027
|2=>0x8391c01131d083a8a01081614396e0b0a41143908016a2708191c010c5f2c0000390839822709012201143a0801663714d1003a126530381c011401045d2c0000390839046530381c01140108013038143914010819363714191c0114392c00003908391439045d2c000839044d24000845143a4c3814951439080212ed2016
|3=>0x2c00083909012201143a24000845143a148d4a390802141a081900392c031439083908020a37143924030845143a141a08011c011265303814010a370801143915414a3a0802080114d1003a9c2709351c0214392c02083920470801143a140100390839202708011c014a45143a080209022201143a2038080108390a371439
|4=>0xa0314392c00143908390c7b00390038be3a144208016a03081900396a2b08190039003920391439080108e6303b140120580801083915312c0208390a4214390801145d2c0008390839143908013637303914012c0008010839ae27086114011521203808011551081a003914951439080230581401083914394a390802145d
|5=>0xa4114390801363714191c01081a1c01140114420801083913bd203a0801da39086214012c000039083913adcc3a1411203b1439080108a5141a1c0124020845143a20270801003a125d2c000839086e30391401141900390839cc181411003909910a02143930381c01140104653038140100f1303a1401145f2c0008396011
|6=>0x801143a30381401141a1c01087b0038303a1401081a003914390839cc3a14111c021401203a08011c011401145a08391a791c0014191c0100390839081914191c01cc1b1411003901c1cc381411127d0479003800390039143908390479003900382027143908010a4014390801143a202708010c7b003900380839cc381411
|7=>0x3b003a0a0314392027080108d1003a00d1003a0a3714390479003809e51402086114010862140114021c012c010839082914010801083908790038cc3814111de71402cc0308291be514022201143a011d083a2c0308392202143a1439003914950802141100390a001439081614390801003a143a08020879003814390801
|8=>0x141100380039080208010839083a003a140108390039003809351c02
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x79400000001950000000051400003d400002940550000005
|7,0=>0xb542c8cae42a90a6428909e400009a4259092423908a421908241f907a400007641c906e41a90000199062417905a4159052400004e41290000119042400003e40e903730cd02f40ad027408d0000
|8,0=>0x5d0d7135b8d6b35a0d653588d5f3570d593558d533540d4d3528d473510d4134f8d3b34e0d3534c8d2f34b852b34a0d253488d1f3470d193458d133440d0d3428d073410d0133f8cfb33e0cf533c8cef33b0ce93398ce33380cdd3368cd73350cd13338ccb3320cc53308cbf32f0cb93
|8,1=>0x19f3670d993658d951648d8f3630d893618d833600d7d35e8d773
|9,0=>0x810a0228009fe27f09fa27e09f627d09f227c09ee27b09ea27a09e627909e227809de27709da27609d627509d227409ce27309ca27209c627109c227009be26f09ba26e09b626d09b226c09ae26b09aa26a09a626909a22
|10,0=>0x83460c182c60a1824608181c6061
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 14
def pmP:Nat→Nat
|0=>0x827e00000104ec00000201f800000400900000080040000008eec00000119d8000001012000000182c0000000fe800000019f800000033b00000006740000000ce000000019400000003040000000438000000086800000010c000000013f0000000252000000042000000001d8000000023000000004400000000600000000080000000008000000000e00000000080000000008000000000
|1=>0x382007600010308ec00020601d80004081280000808076000083b0fc00010661d800018c03f00003180760000110aac00001620c8000010030000001c67600000385ec000006619000000c33f000001867600000308ec000006119800000c1fb000001827e00000304ec00000601f800000c03b00000180020000020cec00000411d8000008218000001027600000200ec00000219f800000433b
|2=>0x10401067e0200030cfc04000611d808000813f01000086440200000cfc040000199008000013b01000000040100030cfc02000609f804000c03f008001067e01000200fc02000221d804000402e008000007c00800b10ec01000619d802000c13b0040008076004000086000600611d800c00c02b00080184760008030cfc00100619d800200c03b000401067e00080208ec00100019d800200013b
|3=>0x100000304ee00000409da00400402b290001027650000200ec400c0e01d842000c03908000180f610000301e412100601f824000c03b041c00847608080300ec10100209f820001423b040001847608000304ec10000219d820000401e040000067008000004e0080004099808200c13b
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x28000580000c003800c5c003
|7,0=>0x1808200876ae403f0e09a0663100ba002c08658000854e9db2d001838070040053210d9a1470300
|8,0=>0x4ec2a64431999fb28143e563bc3f3063e963e0a8dcde0625e8ddf1548b068294709120393294b0976492a79dd23117a4ba7944aae4a41db73a42eb3bc6a88dc142a57d268c
|9,0=>0x2326aaab57260bf5b3a77e1e6ab0d5b03caae757abd5a8cf0af66d35942fdb5143e50a15e53d1552f43db3ab
|10,0=>0xb4a9422a47d02e
|11,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 39 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_245 10 roots_245 ops++addP pm 2 dzo_231_16 7 roots_231 ops++addP pm 3 dom_215 9 roots_215 ops++addP pm 4 dom_243 10 roots_243 ops++addP pm 5 dom_231 9 roots_231 ops++addP pm 6 dzo_181_2 6 roots_181 ops++addP pm 7 dzo_115_4 6 roots_115 ops++addP pm 8 dzo_167_16 6 roots_167 ops++addP pm 9 dzo_87_32 6 roots_87 ops++addP pm 10 dzo_165_2 5 roots_165 ops++addP pm 11 dzo_166_16 5 roots_166 ops++addP pm 12 dzo_230_16 6 roots_230 ops++addP pm 13 dom_182 6 roots_182 ops++addP pm 14 dom_119 8 roots_119 ops++addP pm 15 dom_183 8 roots_183 ops++addP pm 16 dzo_83_4 5 roots_83 ops++addP pm 17 dom_213 7 roots_213 ops++addP pm 18 dzo_83_32 5 roots_83 ops++addP pm 19 dom_181 7 roots_181 ops++addP pm 20 dom_229 7 roots_229 ops++addP pm 21 dom_230 7 roots_230 ops++addP pm 22 dom_55 5 roots_55 ops++addP pm 23 dzo_86_32 5 roots_86 ops++addP pm 24 dom_118 6 roots_118 ops++addP pm 25 dzo_215_32 7 roots_215 ops++addP pm 26 dzo_211_4 6 roots_211 ops++addP pm 27 dzo_211_32 6 roots_211 ops++addP pm 28 dom_151 5 roots_151 ops++addP pm 29 dom_117 7 roots_117 ops++addP pm 30 dom_165 5 roots_165 ops++addP pm 31 dom_199 6 roots_199 ops++addP pm 32 dom_103 5 roots_103 ops++addP pm 33 dom_83 5 roots_83 ops++addP pm 34 dzo_229_2 6 roots_229 ops++addP pm 35 dom_214 7 roots_214 ops++addP pm 36 dzo_229_16 6 roots_229 ops++addP pm 37 dom_227 7 roots_227 ops++addP pm 38 dom_179 7 roots_179 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_231_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_181_2_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_115_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_167_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_165_2_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_166_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_230_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_83_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_215_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_211_4_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_211_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_229_2_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_229_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_179 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 79 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 79 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 50 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(34,35),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,192),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,136),(128,160),(128,192),(130,131),(130,138),(130,146),(130,162),(130,194),(144,145),(144,146),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ac688
|_=>0
def sO:Nat→Nat→Nat
|11,0=>7
|_,_=>0
def wAt:=mkWire dB 7 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_187 10 roots_187 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_235 10 roots_235 ops++addP pm 5 dom_219 10 roots_219 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_219 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
  · simp [NN] at hi
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
def dzo_172_16:=0x111100001111000000000000000000001111000011110000
def gzo_172_16:=0x111100001110000000000000000000001110000000000000
def gsh_172_16:=0x11110000111000000000000000000000111000000000
theorem lowS_zo_172_16_172:Lower true dzo_172_16 roots_172 gzo_172_16 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_16) [(dom_172,16)] (by decide +kernel) (lower_slice_b (T:=gsh_172_16) [] (by decide +kernel) lowS_172)
def dzo_217_4:=0x30303030000000003030303000000000303030300000000030303030
def gzo_217_4:=0x30303030000000003030303000000000303030200000000020202000
def gsh_217_4:=0x3030303000000000303030300000000030303020000000002020200
theorem lowS_zo_217_4_89:Lower true dzo_217_4 roots_217 gzo_217_4 6:=lower_iso_b (d1:=dom_217) (r1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (lower_slice_b (T:=gsh_217_4) [(0x3030303000000000303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_89)
def dzo_236_16:=0x1111000011110000111100001111000011110000111100001111000011110000
def gzo_236_16:=0x1111000011110000111100001110000011110000111100001110000000000000
def gsh_236_16:=0x111100001111000011110000111000001111000011110000111000000000
theorem lowS_zo_236_16_172:Lower true dzo_236_16 roots_236 gzo_236_16 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_16) [(dom_236,16)] (by decide +kernel) (lower_slice_b (T:=gsh_236_16) [(0x111100001111000000000000000000001111000011110000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_173_16:=0x333300003333000000000000000000003333000033330000
def gzo_173_16:=0x333300003332000000000000000000003332000022220000
def gsh_173_16:=0x33330000333200000000000000000000333200002222
theorem lowS_zo_173_16_172:Lower true dzo_173_16 roots_173 gzo_173_16 6:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_16) [(dom_173,16)] (by decide +kernel) (lower_slice_b (T:=gsh_173_16) [(0x22220000222200000000000000000000222200002222,0,1)] (by decide +kernel) lowS_172)
def dzo_237_16:=0x3333000033330000333300003333000033330000333300003333000033330000
def gzo_237_16:=0x3333000033330000333300003332000033330000333300003332000022220000
def gsh_237_16:=0x333300003333000033330000333200003333000033330000333200002222
theorem lowS_zo_237_16_172:Lower true dzo_237_16 roots_237 gzo_237_16 7:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_16) [(dom_237,16)] (by decide +kernel) (lower_slice_b (T:=gsh_237_16) [(0x222200002222000022220000222200002222000022220000222200002222,0,1),(0x333300003333000000000000000000003333000033330000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030
def gzo_249_4:=0x3030303030303030303030303030303030303030303030203030303020202000
def gsh_249_4:=0x303030303030303030303030303030303030303030303020303030302020200
theorem lowS_zo_249_4_89:Lower true dzo_249_4 roots_249 gzo_249_4 7:=lower_iso_b (d1:=dom_249) (r1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (lower_slice_b (T:=gsh_249_4) [(0x303030300000000030303030000000003030303000000000303030300000000,0,32),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_89)
namespace S_253
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(16,17),(16,80),(20,21),(20,52),(20,84),(20,148),(24,25),(24,56),(24,88),(24,152),(28,29),(28,60),(28,92),(28,156),(32,33),(32,36),(32,40),(32,160),(48,49),(48,52),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,192),(68,69),(68,76),(68,84),(68,100),(68,196),(96,97),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,160),(128,192),(144,145),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_253.map (·&&&dom_253)
def gM:=goal_253&&&dom_253
def NN:Nat→Nat
|3=>2
|4=>10
|5=>34
|6=>135
|7=>234
|8=>138
|9=>34
|10=>5
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xb4b128d515
|4,0=>0xb5e2e3df0036318300f628e1022b921eb1d154511256100ced
|5,0=>0xfdc6dd6670c4b9ab903c87c19823c877e6258916559b953755523894e6d34b0a3471ca4624d44e253d0df3906a38ce938bfb35df92f99e2ed6d27d3422f801feff1fbcd18bf91495d139811216d0cad40b1d101a81
|6,0=>0xddea1d7152c6025c41a3c0e7cbe70ebe64dba91eb78beaf993af2fdae96fa658c9c8859bc089b177999a9973ab965e7948f59112d8f3b18a6a48760c86acd84d8282e0e806407cf4f7ce7a7b5e67ad3878d7a7895e77c4c77b8e76b3375c697499073e6571a26709666ff4d6dc086b8306aab869daf6945d684e066901658ff65176644c262b16629a2617175ff905bebe5b6bc5af7c5a6565808c576d85323652b544fa41489a046895465ea4614946078452f041e60407c53f5643f3043f1123d00a3b43a3936d3846037b8137a30342f531d862ff652f9212ed672ec2b2d80f2d4642732f256d924e0024a9823d8223c3f22ca2201b51ff001f1561d21d1ad9a1a7301a01f19f41181ba1811d17bd81512c14b3910ed610d6c0f7df0e6ac0e2660d6600d1b40bd6a09e5b091950510a0390d0349b02fba022100187f017cb
|6,1=>0xfdaa8fb891f8903f416cf3e48e34f0e0cea
|7,0=>0x571e45656b55269530ab52f1d523625128750bb850ad94f37e4ed994e5b74db874da524c95e4c54d4ae4747e624754945faf45a7844a19446b34391341bde4199a41850416784144c412de4107c3ddfe3ce093c90a3c6553b33d3a7f83a44d38df938849380e53737e36e1536d14352ad34b323397931947311ba30cf42f6a72e3b12e2742d19e2b2eb2acea2ac902a81c296832952328ba4288062766f26b7d256d924cd62437e237b72211521ec11f8441debf1dbfa1d6ee1b6331b4761ab0e1aa451a1dd1a19d19a64198a7195f21911117e75174b6161a115d4013efc132d012e6411f58119da10bcc10ae8108f61042c0fba90e8680d9d90d7f00d4b10cc980cb800c6580c1d20b24c09cb009725091db090980864207f5807359068dc063d0061cb0613005ffc0583c03708028af018800130e0115500f8900d870032f
|7,1=>0xe5fb7e3e19dd890dc17cd7abad0a75cda15cb8e1cb636c41aac2cc9c2158c2056bf2bfbca0bbc97cbc6c9b8b00b6ccfb5f1fb584bb5765b3d37b2fbfb17d3acd00abd82abc01a8bf1a7284a4ad9a4394a37f49d7059cc249b6e59963194f42945f5934d4923ac8f1ac8eed18e1688df768cc8a8b51b8a1ec885e687b7d860a484c3583b1c839aa8344882c45828cd82215821fd815d380f0c80e4e8077a7fcf77fbb17ea0f7d68f7b06f7a619793aa78af9784a2750e37312c72d4972b547215f718156cf796b6616b0c66960b653c8652f664f8464d7b64bfc645d363fcc636fa6272d625186221a5f29d5ed9a5dc025d6805cee75cda95c7475c7415c1cf5b1f65a95d5a7d75a6b0
|8,0=>0xb9595b5beab5514b1c7eabc01aa74ca962ba4bca9e73d9e5449c1959ad8c99c7398a249776494b6693deb8f32d892838651d863937e7fe7da8f7bd287b51f7b44d7aed2780e076f4176d5376c94765f475df2719bc701676cfb66c4df696df69334675d766d0f65a4f654d5649ab6373d63554626a45f01b5dc5c5dba15ab705a3e25843557e30542155311652e1d52a615031a4ffe74f96d4e4354963e477cf46e0042d11409623c8743901338f45381d4352e63451f3278531fb7315cd2c55b2b4572acea2a7782a6d729fbd29a952928e2845f26a4d235842318a22ec0227af21bc11fe4d1da421d02d1c5311b2281acc01a49a18d13172ac160a415ab1153f91502b139f4133b9131b412fe511cd6111320ba6b0b5af0b1e50ad2e0acb80a2070966e08635082a50743406c94057b604f1204bfd0477203677026db003fd
|8,1=>0xf9e74e4aa3e42e9e391fe2b3ae178ddc6add1d49c4f12bed48
|9,0=>0xce262c2bd3bec67b3d489ceee906b48c74b87b138562f832e68310d820337989472a385e1b5556a1506e44e32b4c32a4b43d483f14412a43bc43e5b6305f12d25d2cd6829dfc2645113b7109fd008717061f501ee0
|10,0=>0xdebf9d4dbe79b4e3f6993343a
|11,0=>0x1e31b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8cb333333333333333333333333333333333333333222222223333333322222222cccccccccccccccccccccccccccccccccccc0000cccc0000cccc0000cccc0003030303030303030303030303030303030303030303030303030303030303030cccccccccccccccccccccccccccccccc00000000000000000000000000000003333333300000000333333330000000033333333000000003333333300000000888888888888888888888888888888888888888888888888888888888888888b333000033330000333300003333000033330000333300003333000033330000cccccccccccccccccccccccccc00cc00cc88cc88cc88cc88cc88cc88cc00cc00303030303030303030303030303030303030303000000000303030300000000cccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000003333333333333333222222222222222233333333333333332222222222222222cccccccc88888888cccccccc88888888cccccccc88888888cccccccc8888888b333333333333333333333333333330033333322333333223333332233333300ccccccccccccccccccccccccccc0ccc0ccc8ccc8ccc8ccc8ccc8ccc8ccc0ccc3333333333333333333333333333333333333333333333330000000000000000
|0,1=>0xc000c000c000c000c000c000c000c000c000c000c000c000c000c00080008000003300000033000000330000003300000033000000330000003300000022cccccccccccccccc8888888888888888cccc0000cccc00008888000088880000303030303030303030303030303030303030303020202020303030302020202cccccccccccccccccccccccc00000000888888888888888888888888000000000030003000300030003000300030003000300030033003300030003002200220000cccc0000cccc00008888000088880000cccc0000cccc000088880000888b2323232323232323232323232323232323232323232323232323232000000000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc000088880000888b300330033003300330033003300330033003300330033003300330033003300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c800000000c8c8c8c800000003333333333333333333333330000000033333333333333333333333300000000ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8cc00cc00ccc8ccc8cc00cc03333333333333333333333333333333333333333333333332222222222222222cccccccccccccccccccccccccccccccc8888888888888888888888888888888b333333333333333000000000000000033333333333333330000000000000000
|0,2=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000333333333333333333333333333333330000333300003333000033330000222200000000cccccccc00000000cccccccc00000000cccccccc000000008888888b3333333333333333333333333333333333333333333333333333333222222220c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0808080800033330000333300003333000033330000333300003333000033330000222200000000000000000000000000000000cccccccccccccccccccccccc8888888800000000000000033333333333333330000000000000000333333332222222200000000cccccccc00000000cccccccc0000000088888888000000008888888b333333333333333333333333030303032323232323232323232323230303030000000000000000000000000000000000000cccc0000cccc0000cccc0000888810101010101010101010101010101010101010101010101010101010000000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00880088000000000000000000000003232323210101010101010101010101032323232000000000000000000000000cccccccc44444444444444440000000088888888000333300003333000000000000333300003333000033330000000000002222
|0,3=>0x444444444444444400000000888888880000000088888888033003300330033003300330033003300330033000000330033003300000022cccccccccccccccccc88cc88cc88cc88cccccc00cccccc00cc88cc00cc88cc003030303030303030303030303030303030303033333333303030303222222220c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c0c0000080b333333333333333000000003333333333333333333333330000000022222222cccccccccccccccccccccccccccc0000cccc8888cccc8888cccc8888cccc00000000000000000000000000033333333000000000000000000000000222222228c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c888888888c8c8c8c888888891111111111111110101010101010101111111111111111101010101000000004444444444444444444444444444444444444444444444444444444400000003333333333333333333333332222222233333333333333333333333322222222cccccccccccccccccccccccc88888888cccc0000cccc0000cccc0000888800033333333111111113333333311111111333333331111111133333333000000000000cccc0000cccc0000cccc000088880000cccc0000cccc0000cccc0000888b333333333333333333333333333333333333333333333333333333300000000
|0,4=>0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8888888b3333333333333333333333333333333111111111111111111111111000000000000000000000000cccccccc888888880000000000000000cccccccc8888888b33333333333333322222222222222223333333300000000222222220000000000000000cccccccc000000008888888800000000cccccccc000000008888888b0303030333333333030303032323232303030303333333330303030323232320000000000000000000000000000000044444444444444444444444400000000000000000000000000000003333333311110000111100001111000033330000000000004444444400000000444444440000000000000000888888888888888a222222222222222222222222222222233333333333333333333333322222222cccccccc88888888cccccccc88888888cccccccc8888888800000000000000003030303000000000303030303030303030303030000000003030303020202020000000000000000cccccccccccccccc00000000000000008888888888888888000000033333333000000003333333300000000333333330000000000000000cccccccccccccccccccccccccccccccc0000cccc0000cccc000088880000888b333333300000000333333333333333333333333000000003333333322222222
|0,5=>0xcccc0000cccc0000cccc4444cccc4444cccc0000cccc0000cccc4444cccc00022222222333333332222222233333333222222223333333322222222222222224444444444444444444444444444444444444444444444440000000000000000303030301010101030303030101010103030303010101010303030300000000cccccccccccccccccccccccccccccccccccccccc0000cccccccccccc0000888800022220000222200002222000022220000333300003333000033330000222200000000000000008c8c8c8c8c8c8c8c00000000000000008c8c8c8c8888888b333333300003333333333330000222233333333000033333333333300002222000000004444444400000000444444440000000044444444000000000000000000000003333333300000000333333330000000000003333000000000000222200000000000000000000000000000000cccccccccccccccccccccccc00000000000000000000000333333333333333300000000000000003333333300000000cccc0000cccc0000cccccccccccccccccccc0000cccc0000cccccccccccc00000000000000000001111111111111111000000000000000011111111000000008888888888888888cccccccccccccccc8888888888888888cccccccc8888888b030303030303030202020202020202030303030333333332020202022222222
|0,6=>0xcccccccc00000000cccccccc00000000cccc888800000000cccc888b333333333333333111111111111111133333333333333331111111100000000cccccccccccccccccccccccccccccccc0000000000000000cccccccc888888891111111111111111111111111111111111111110000000011111111000000000404040404040404040404040404040404040404000000000404040400000003333333333333333333333333333333300000000333333330000000022222222ccccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8c8c8c800033330000333300003232000032320000333300003333000032320000323200000000000000000000000000000000cccccccc88888888cccccccc88888889111111111111111111111110000000011111111111111111111111100000000cccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8888888b3333333000000003333333300000000333333333333333333333333222222220000000000000000000000000000000000000000cccccccc00000000888888880000000000000000000000000000000333333330000333333333333000022220000000000000000cccccccccccccccc00000000000000000000888800008888000000000000000000000000000000000000000000000003333333322222222
|0,7=>0x333333333232323233333333323232323333333332323232333333333232323200000000000000000000000000000000cccccccccccccccc888888888888888b333333333333333333333333333333333332222333322223333222233332222
|_,_=>0
def sP:Nat→Nat
|0=>0x1c50b0c22745162274e100a20b0436185082648890062038c00284093440583041c610165041322407141a58792141c604322c2880e3c8900634b180040513225c814104c911062008700386871e407080e3c00e1a1c6040a0838c0828101082c5020224005101c2060a080840608080
|1=>0x1810883101c6110028696229080a1a3c8a32028696228880a10587a116144010e248032c3d01016286871e44803100439016386961e6c80a101c79100384161e6c005101c6041c2038f202c70d2c3021b1c3438c12402820e304901c2038c082c5093e7880b1c2038c1200502022480b
|2=>0x1434b0412bc02906144161e4070a2c3089d2028b095ec480b1420b0422bc00314587ae202ca0d2c309095a28b0f22a880b1434b1212ac80a2c24e2a202d4a81420b0c1228609467880b1434b0f249c80a1a59311124050d2c2520020144164c2480a1058792362c51618444a52014407
|3=>0x224050818251901628609465c80b6829996184480a1059bb6202da0a665860900286961849a901c20b0f5a405851058604226c7141a586121228b090ca880b282999618448140a58604226548a2c304ae20505332c304800a2038c222480a1a5890938401882c60010160d9082c3c80b
|4=>0x6828b0c22c402c1434b0f22401882c308b8002869618484b8062038c202c5082c25e10160c5082c9080b5028696182400a2c25d99202ca0a1a58792220c4161ee880b06e4b0c2240594104c49016286961e456901458604366458a1a58609700018a103d19016144161e44d901420b18
|5=>0x7e4050d0e308892014407182480e14587b1202ca082c54890142038c222400e1058604362c1a82820b0f16384161824d8014204af464058e101c609202c50c12f8c901628b095e5c80b602841608443036020b24202c18d2c308b82029e8c224018d2c308ba2029e8c12001882c30d80
|6=>0x12ad890160d80d2c3c0101420b11131002810586095a2c2882c3c8b8210050d2c3c8901420b0f226c00a1a586116a405161810899840c5161ea880b14304a3544058a2c25dc1202c2882c3021b1c20b0f3640585105860422e0196182501016145161e44b908028696181088a1058611
|7=>0x202c7141058791000ca082c9080b1420b0c231c80e2834b0c08445082c304a11628609466480b06506961e0050d2c6048020286097d0480b1420b04227000a1058c11004050d2c444c4211850d2c308901420b376a4058314586114a4050d18484a32050416184628a1a587913640516
|8=>0x1420b0c6a405161e9d010160d8082c443101420b4a220050d18444a32028b09385c80b6028416084578a665860900286961e45c10502869618108831a586115a405161e5d39016c05082c452101c20b0f74405a81420b0c6a2c5392c3021116286961e464901458611132080a041c609
|9=>0x28284161e4400a2c304ae202da0e1420b0f202c51618444a0202da0a2c30899202da0a2c30499002c2882c304b8202c2882c304ba202c70a1a5861212405161824cad202d4301420b0c122c5392c304901628b0956a880b2820b0c23301882c3089b003850d2c3c9106028b0c0844ca9
|10=>0x18108900628b0c22c480b28286961e4480a10584b548405a91420b0c08240141434b0f1200a0a105a789202c5082c26806202c5082d3c480202c5082c261c4202c5082c308899c40a0a2c30909322e00a1058612122c7082c24327202d4851420b0c1242685105861120144161e45390
|11=>0x2c25200202ca082c304cc17445082c3021016284161e448420620b0c226c80b282841612ac80b2820b0c12b400b1c0ca082c3c80b0a28b090c6480b1420b09560080b5828b0c126480b0620b0c229c0101434b0c24253906028b0c0824c8b2814b0c12c480b1420b0c2424d8b5228416
|12=>0x205041618484ad160d9082c30490162841624255901628b0c1266b1016a4185105860920d05082c25590160ea882c3c80b2828416129080b1434b0f24448030a20b0c230c834145860982405d30658609202c51618444aa202c5082c3c927202da052c304b1202c5082c98889202c508
|13=>0x182609016b070a105879016284162424e101638416182569016b0416182569016284161825c1016284160825780162841618465801458609b4405b014586092e405a91458609624058a1059bd912405a8281441618245d80a58609324058a10304a3202c5082c25a86202c1b01058611
|14=>0x1420b0f202e0141058609202c18a10304a3202c2882c3088936405082c30935202c28a2c304aa202c2882c302114e40a0a6658609202c194105849c202ca052c30209322c7141058612122da0a1058635202c1b0105879016c85082c26e1016c050818251901628b0f2444b90176c516
|15=>0x12ac80b0628416197880b582841612ac80b1420b0f22b480b282869618488891420b09b84058a1058c09202da0a105860422001941058635202c1882c304b8202c516181089900384161e9c80b0620b0c12e880b6829996182480b6814416184480a2c24319202c50d2c308895a401a8
|16=>0x620b0f4e4058a105861212e0594145860962005b40614416184482c1420b0938405851420b04221880a1a587914e414141420b0c122c50d2c304c30028b0c128080b5028416182400b28284161e4888b0628b0c225c80b1458604230cc8b58286961844490680c5161ec480b1c28416
|17=>0x202da030a20b0f202d4831420b0c22401882c30d9016385082c31a9016d05161845890162af96182480b582841618d480b6828b0c12c400b60284161811a8b0620b0c22e080b0620b0c22e880b1458609748080b1420b0c22422b4502841618245b01420b0c22d48030a20b0c244480e
|18=>0x6028416184480510586095a405851458611125c82906284161e4058e145860962405b414586095c405ac145860962405831434b0f004050d2c4449c200c50d2c308c320c05082c10486178050d2c304802028b0c130cb8016a4a05105860920c028a10586042228b0c12a880b14f4609
|19=>0x2c304c1202c51618252901628b0c227481414206094640585105861112e080a2c3049d005050d2c304dd06c0a082c308908028696184449006c041618440102828b0c0844c8b8028416181088b1c284161e44010142038c222480b2820b15124058a2c30909865c58e1434b0c0844834
|20=>0x130458360504161e4058a103090946405832820b0c2200a0a1a58612120d8082c3c01016a45082c304802028b0c0824cc216d050d2c3089080284161e4480b1420b0c22d480b1434b0c2224d9006c069618240100a20b0c126c8461458609b4405d31458611124050d2c302114e42c0a
|21=>0x1420b0c1201a031434b0f202f10a2c30499202d60a1058609202c50d2c3088992407141058604222c51618104c1c22c71410586111200a0a2c309092e2da031434b0c22405082c60480202c5161824bad202da140a20b0c2240a082c304c5160ca0d2c304801434b095e008141458604
|22=>0x162869618444b820c05082c2559016502882c3c8900a20b09cc1880b142038c124058a105b2890c4058a2c304aa004058a2c304974e4058a10587ba4e405e40a20b0c124058e50284161e4058a1058486c6405b41420b095e405940a20b0c08456031420b0f202d60a10304a3202da29
|23=>0x1058604122c5082c309095a405ac1420b0c120080b60505082c3088920c05082c30209002e98a2c3049016c05082c308890041a141434b0c124058a103020946405b42828696184480a1058611984050818444a3202c5082c3c8c300a05082c30211160c416184569016c05082c25210
|24=>0x2c308894e40a0a10586111201a0e1420b0c12405b01420b0f120080b58d05082c30490179ca082c3049016c85082c3049017005082c304c3202c7141058609202c70a105888938405940a20b090c405a80a28416182480b0a20b0c139880b1420b0c132480b58505082c3049016c0a0a
|25=>0x2f00a1058609202c7032820b0c124058a2c30497202c5082cdc486202ca0a1a58604122c5082c5449016d02882c30209202ca0a1a58611124028a2c30209324058e1420b0c242480b2828416181088b06c02882c3049016b05082c30909202c5161e27410162841618104d2202c288
|26=>0x155041618444901420b0f244480b0a2841622243101420b09d64058a1058609704058a10586097440583aa20b0c12405a91420b0c082480b28286961e2480b1420b0c13a880b1434b0c24444901420b0c242539016382882c304a7202c5082c30889210a6851058609202ca0a1058789
|27=>0x5a4058a10584af202ec0a2c30499202c5082c304ee202c7082c304a7202c1a81420b0c12405831434b0f202c5082c304cb002da0a2c304b1202c1b01058609202f68a1058609202ca0a2c304b1202ca082c304ec202c18a1a58611202869618261905028416182480b1420b0f124210b
|28=>0x182618016505082c30904122c50d2c30490ba381882c304a7202d60a105861112405b41420b0c084480b1458604126400b1434b0c22253902828416184888916d02882c3049016145161824c9016d018a2c304b1202c70a105849c202c5082c304d2202c50d2c304e6202c5082c30889
|29=>0x120080b8c28416182480b1420b0c124228b14586092e0080b60284161825a90160c50d2c304802028b0c08260901628696184849006284161844010602869618240105828416181049016a45082c30490163818a105849c202c70a1058486202c5082c3c8a7202c28a10587912028416
|30=>0x36405836020b0c120080b1420b0c084539016145082c3021121005082c30889202c2882c304a7202da301420b0c124058e1420b0c084480b28284161825c1016385082c3088900414831420b0c12405941434b0c120050d2c304ef202c5082c4449c202c18a105861186405e01420b0c
|31=>0x162841618108802814416181048b52505082c30490162841618444c9202c7301420b0c124058e06284161e4058a2c304c1202c50d2c3c8905828416182480b0650416182400b1420b095e0080b6828696182480b6828416184480b68505161825890160d8141058609202c5082c30889
|32=>0x28284161844490162841619c44901628416182659016c05082c30490160c5082c3c80baa28416182480b0614416182480b28284161e2480b1420b0f120080b1420b0c222619016284161826610162841618444c300284161824d9016c05082c24310162869618104801420b0c2225c10
|33=>0x2c304901628b0c126480b6028416182401016145082c3c4901628416182485d16145082c30889202b80d2c3049017c85082c3c49016502882c30490160c5082c3089017345082c304901628416182619016284161848209202da0a1058604124058a2c30209324058a1058612222480b
|34=>0x28416182480b1420b0c082480b1420b0c222480b2828416182480b1434b0c12405831420b0c124058a1a58789202c7031420b0c124058a1a58611124028a1058604124058a105b48f12405832820b0c12405831420b0c120080b1420b0c242480b6050508
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x880004
|4,0=>0x6aa0305015a80994042a01c500ba8049401aa0085
|5,0=>0x1fac0f76078b03ad81cac0df606cb034d819ac0c76060b02ed816ac0b0505530291813cc098604930231810cc080603d301d180dcc0686031a817580aec0525026301198080c03a6
|6,0=>0x159b8ab1c54ae29e714bb8a494516e2865140309e5c4e4e26b71323897984aee2507124b8909c476e2347116b889d8440e21971093882dc408e1fe60fbb87c1c3d2e1e270edb8751c39ae1c670dfb86e1c362e1aa70d1b8671c32ae18e70c3b8601c2f2e17270b5b8591c2bae15670a7b8521c282e13a7099b84b1c24ae11e708bb84458214e1037
|6,1=>0x2363919988bee4587228b912d8888e43d721b390bdc850e421720d3904dc818e40571ff38fddc7e0e3e971f138f6dc7a8e3ce61e3b8f01c772e3b271d5b8e91c73ae39671c7b8e258704e37b71ba38db5c6cce35f71ac38d45c694e343719e38cd5c65ce3286190b8c69c626e30c7182b8bf9c5eee2f1617538b9185bae2d67167b8b21c582e2ba7
|6,2=>0x1271c92cc48f724439205c8f4e4737
|7,0=>0x34739a1a0cfee6778337c199e0cbf06578327c1921cc8106397318c18a60c44e61a83094182a0c0505fa82f9b97ae0bc8e5dc82ea417320b8905bc82da416b20b49059c82ca416320b09057c82ba415b5cacb055d82ab3953a0a8d053e829b414ba0a4d051e828b4143a0a0ee500727cb93c9c9d504e2826d4134a099504c2825d412ca095504a37
|7,1=>0x440c21e610e308698430c216610a3084a7421420edd068e82c8412420721029080c840241ff20fe907ec83f241f720faae7ce73e341efa0f6d07af73d439e820f31079173c539e0a0ef5077283b541d8a0eb5075283a541d0a0e750732839541c8a0e36e7138385c1c0e0df706f38375c1b8e0db706d38365c1b11cd7ae6b58356c1a960d3b06958
|7,2=>0x536c2999d4beea578527c291e1480ea388518428a214410a197508c2829d40509fa84f9ba7b593cb09dd84ebb2741d39109c084dc426c2135109a084cc42645d313098184bcc25c612d3096184acc254612930942749dba4ce12570923848dc244e12170904747f323da11dd08e7746fc235e11a0e8c88460422e2116108a8845042265d12308898
|7,3=>0x176b0bad85d33ae7a172eeb8f85c3c2dfe16ef0b6f85b43ad8216b2eb5185a4c2d0616730b318594c2c8616330b12758542c0a15f50af2857542b8a15b50ad2856542b0a15750ab2855542a8a15350a9375463aa15d4fb0a758
|8,0=>0x6e3436fa1b6d0dae86d34367a1b2eed9076c4436021af10d7086b443585dab30d5186a4c35025a710d3086944347e5a2d2d0e8683433fa19ed0ced96733b37a19ad0ccf76634b2fa196b2cac96524326e59252c8b76414b1ea18e50c6996304b15e589f0c47861f4b0da185b2c25860e4b05218190c0395fd4afc657d12bdf95eb4af3dd78d2bbd9
|8,1=>0x7eacbf361f8cefc067dc43ec21f510fa087cc43e3e5f0d2f7d97ba4bdae5ec70f5a97a943d265e812f3797974bc965e3cef16878743c165df92ef4877643b921db72ed38765c3b11dd790eb48755cba8e1d352e92874543a0ddcf70e729735bb98a5cb32e509724439021c6f2e2f8713c387a5c2d0e0e8703437f65becedee86f34377a1bab2dce7
|8,2=>0x204f101f880bc403e2010efff97fc3bfc21fcf2fde9
|9,0=>0x227cf13598973c496623b111588864c41221f730f47875cc38e21b710d38865c430e217710b38855c428e213530919844c420260ef306f8833c417e20b0f0508824441022071102f9
|10,0=>0x116488ae44552229af1458
|11,0=>0x116c7
|_,_=>0
def wAt:=mkWire dB 115 254 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x14490025202d102d182514462241122d2844186d142d28441441122d18252844122d1825102d284416251241142d2c6d28441441122d22290834102d20292025162520452c55122d0a3c162918252c6d2844122d202d144114252c550a3c18251441142d122d1825102d144514412241122d144120452c55122d0a3c16291825
|1=>0x1625224114411825122d102d28442c5514410a3c162918250823284420292844202916251825122d603c0a4116291825102d144514412241122d122d6834102d28251629142d2c6d2844122d1c3314452241122d603c1825142500290602202d60331a10102d202522291625122d60330029202d144a12012029202d22295833
|2=>0x142d28441441122d182528441625122d142d2c6d28441441122d6823160d064114250a3c18251441142d122d202d2c6d2844122d2c6d28442029222918160a41142d282d14412c75162508341241102d14462c75202d08341241102d2844122d202d14411425682328252029284514411825122d102d122d14252c6d28442029
|3=>0x1816142d202d9631082b2025162560330a41142d68342825102d2029202d0a41142d284414412229202d162518252229102d2029202516251441202d102d18251425183a202d22291625224328471441585b14490025202d122d14410600202d1425284414411825122d102d22438629102d2243122d28442029162518251241
|4=>0x142d582f08152025142d122d142d0643142518251629222b16252029202d1625182516c56823064114251825160d064114257423209d222b101208292025141110122025502b203a0a25142d1445102d2241122d1c4320150a25142d106d284420291625122d14410a10142d2025144522411825122d102d2015162908232015
|5=>0x142d202558336025002924291012082d2025202d222b102d14462241122d1401202d10126823162928252029284414412241122d682f08292025162568230641142514411825122d102d60270029202d682f141120251825102d2029202d5e256033282d12bd60330029922d28471441122d20291012082d20251c2b18160a25
|6=>0x282f14416a336027282d22411825122d102d142d14252243122d1411322d10122025142511512016142d582320392229182514462241122d682306411425186d284414416a336027002914410a10142d2025134908162025142d002b202d16251825142528442029162558336025282d0025202d160d1825144114250a331012
|7=>0x29202d202d082b202516258c23aa25282f1441140124230025202d682f064114250c251816142d1441203a0a25142d14651012142d2025585b0a11142d2025602718162015142d122d282d144114251441144a0025202dae290602202d1425583314490025202d322d10122025682f064114255833682d0641142514251825
|8=>0x25202d582308152025142d222b20256834102d28251c33062d1441142510121441142d2025144514412241122d28256027282d1441282d18251441142515750027202d585b60250029202d1825104a2241122d1505322d1012202520391825062d14252241183a22291625582b2039062d14251449144a0025202d12416033
|9=>0x20251825144a2241122d102d14412241122d643315750027202d603c0a4116291825202d082920251625282d14411c53062d1441202d0823202516251c2b1825062d14250829142d0829202516250a331012142d2025102d144a2241122d18251c43062d14257029284620291625585b682d064128441441142d122d58271449
|10=>0x25202d202d682328252029200d1425142d122d183a2039062d14251241222b102d1625182558436025282d1441102d24430025202d10ea209d222b1625584360250029202d182514412241122d1425104a2241122d2046082316251449102d2241122d18256823064114252039062d1425ae250602202d142558330a11142d
|11=>0x142d2c7508341241102d200d142d18251425682f064114251425284420291625602720150a25142d682308292025114908162025142d602760250029202d68232825202960270029202d284620291625222b209d222b1625122d0600202d14255843682d0641142560270a41142d1425142d2241122d1c2b062d182514255a43
|12=>0x242322432241122d102d202522291625122d2825282d1441582b08152025142d2423142d2241122d682f1825064114256823160d06411425622d6823064114256823682d06411425202d102d18251425102d183a22291625102d14252243122d18160a41142d244324230025202d2825202920250a41142d122d582308152025
|13=>0x142d28441441122daa25282f1441a8210a43142d122d222b1241122d102d322d1465101220255223682f06411425162508341241102d585b6025282d28461441122d202d08341241102d1202102d2029202d122d282d14418629102d2243122d14250029202d22432229202d162518252c6d28441441122d14410a3c16291825
|14=>0x1825002916252825202914410600202d14251425102d2029202d102d60330029202d1441322d10122025182514411425585b14490025202d122d202d144114251201102d2029202d182514250029202d582f60250029202d102d082920251625862918252243122d582720392229162528441441122d102d102d14250029202d
|15=>0x582360250029209d222b16251825c6290a12142d20251825203a062d142560332825282d1441142d2029202516251c41062d18251425585b0a11142d2025682f28252029102d18251425b02f10122025094908162025142d14452029202516258243322d10122025202d2029222916252029104a0025202d1425122d102d603c
|16=>0x122d282d144112410029202d11512016142d122d0029202d102d28252029585b0a11142d2025102d162528252029122d0a10142d2025585b144922412046202d162518251c4322291625144a2241122d0029202d102d28461441122d60250029202d18251441142d122d0a33282720292c6d28441441122d081918162025142d
|17=>0x142d14490025202d11a6203d182508162025142d1629222b162516252029202d160d0641142518250029202d682d06411425062f1441142515750027202d150d2243122d062d14411425183a2229162520291816142d203a0a25142d16292827202928471441122d6025282d14411241282d1441144a0025202d60250029202d
|18=>0x14411425682f1411202514411825102d962d14122025102d2241122d14462241122d1c2b0a25142d1625002b202d142d0643142518252029202d000e1425202d062d14411425104a0025202d0c251816142d20291241102d0a3c1629182508292025142d1441122d102d1012142d202514452241122d20292025162514252015
|19=>0x14651012202521b10a27142d222b222916251c43062d1425102d18251425202d14122025682306411425282d144114259a2d0643142568232825202920290a27142d1425122d102d2243122d102d203a062d14251825002b202d0a43142d122d18252241122d0a33142d122d19b20a27142d150e2243122d209d222b1625282f
|20=>0x14251c33062d142518160a25142d1825222b162516291625182524430025202d1441082d20250027102d202d1c2b062d142514492241122d082920251625202d10122025102d222b162514412241122d08292025142d1012142d2025682306411425183a062d142508162025142d102d28272029144a2241122d60330029202d
|21=>0x122d1c2b0a25142d2825282d14412025222916252846122d202d22291625682f06411425102d2029202d15c21a25102d183a2229162514252243122d000e1425aa25282f14410600202d142524230025202d60270029202d1425102d202d322d10122025102d0025202d122d202d1425102d0029202d0a11142d2025682f0641
|22=>0x2025102d202d28461441122d202d202516251441142d2025682f282520292847144120150a25142d062d18251425322d101220251825122d102d0a11142d2025202d1441142560330029202d08291241102d082920251625682328252029282d1441142528441441122d14250029202d2025222b1625122d142d2025150d2243
|23=>0x282d1441101220250029202d162918250027202d142d122d1a25102d1e291825142d1441122d1425064314252243122d082d202514112025101220252241122d1441122d082f2025141220250029202d18251425282f1441142d1425202918251825202d2243122d0a10142d2025202d2243122d28441441122d18162015142d
|24=>0x2025122d1441102d14251825102d062d1425122d102d142d2025203d182514411425202d14250025202d
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x7000000000000000000000000000000
|5,0=>0x5680000000025600000000000000000000000000000003ec00000000196026c000000000d600ec00000000000
|6,0=>0x4f989d2000026144b8892511aa228c42a884100001fd40000000000000003d280000f221d1400007130000000036a06850000000000000000000000000000000c6a00002fa05e1000000002d205640a4814082788000094a00002320000084810441ea0000000000001c2837100000c941798000
|6,1=>0x1fc63e5400000001ec63c54000000000000000779000000003b84000000000003a5400000001c8a00000000df5000000006da00001b42360800000001a8833d4652800000003244000000018a830500000000000000000000bc517262e040000000000000000000b3515e82a945320000000000000000a24
|6,2=>0x84a8000208a404c0000000
|7,0=>0x3c087710ec21d443a087310e499c6338486f90dd99b7436686bd0d5a1a833488684ccf199b332e864d0c7a18b431066188c1217e42f665dd0ba917142dc65a90b3216332be856d0ac195532a28538c00014b3000051d0a1a000027e84ed09ba133425e84ad093a12432426478c8d2000022c8000089210e4
|7,1=>0x58a8b0515f1aba456c8ac91588aad45528a95150a29d45328a551491a8e45148a1cd41a27f44f689dd139a26f44d689a49331a6244bc800012e8a5944aa8945126a249448c690911f223a447048d4d18a22d44528895110a21e34348859109220e44148819101200003fc87e90fb21f243de67b0cf421e44
|7,2=>0x7488e811ce2398472880001c8238c47108e111c0237c46f26dd51b8a36d46d28d951b11b5f36b68d5d1aa1b50469a60001a60b4846888d0119e233846688cc1196232846488c8118e231846288c41186980006128c1c981a2ff45f68bdd17a1af045d88ba4d72a2e145bc6b6cd6c1ad715a86b4116622c93
|7,3=>0x216a429484a9088e0f241b38307058a09240f38169020e02240047fa60001fca3f547e280001f6a3e947ca8f851ef1bdb37b06f5100003d047988f211e223c1377c60001dd9bb747668ebd1d5a3a83
|8,0=>0x9dc73ace741ce539c4737ce6e1cd939ac734ce681ccd3994731ce621cc1397c72ece5c1cb5396472bce561ca9394c728ce501c9d3934725ce4a1c91391c722ce441c85390471fce3e1c7938ec71cce381c6d38d4719ce321c6138bc716ce2c1c5538a4713ce261c49388c710ce201c3d387470dce1a1c313
|8,1=>0xb5876a4ed31da33b407674ecd1d973b287644ec71d8b3b107614ec11d7f3af875e4ebb1d742ae275b8eb59d683aca7588eb0155d3ab4755ceaa1d513a9c752cea41d453a8474fce9e1d393a6c74cce981d2d3a54749ce921d213a3c746ce8c1d153a24743ce861d093a0c740ce801cfd39f473dce7a1cf13
|8,2=>0x2e49dc63b867700ede9dba3b6e76d0ed89daf2
|9,0=>0x307160c2c145820b0316042c045800aff15fc2bf457e0afb15f42be457c0af715ec2bd457a0af315e42bc45780aef15dc2bb45760aeb15d42ba45740ae715cc2
|10,0=>0x6141c2638487088e101
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 15
def pmP:Nat→Nat
|0=>0x51800000028000000011a00000008c0000000458000000220000000108000000082000000040800000020000000008000000002c00000001580000000a4000000050000000024000000011000000008000000003c00000000f0000000068000000030000000014000000009000000004000000001800000000a0000000040000000018000000008000000002000000000
|1=>0x2d7800000122000000090a00000040d000000204800000100000000075e00000038500000018080000007bc00000035e0000001ad0000000d600000006a40000003460000001a20000000d080000006800000002de000000148000000091800000041c00000020a000000103000000081000000040000000017c0000000af00000005600000002ac00000014e0000000a4
|2=>0xe8180000066bc00000334e0000018ae000000ad780000052000000028180000011af0000008c5800000461c0000023060000010ac0000008400000004080000002000000000daf00000050200000026bc000001356000000981000000447800000222000000110c000000880000000412000000208000000101c00000080a0000004030000002010000001006000000800
|3=>0x80042000040001800012035a000090103000040a1000002036bc000100b5e0000801ad000040085800020040c00010011a000080080000040000800020000000008000000002000000000881000000426bc0000210100000105830000080d4800004040c00002010400001008000000801200000400800000200100000100000000070068000020e3c00000415a000001daf
|4=>0x2000d78001000604000800216000400009000200004000100000000064410a0001814a90000c0a060000480e3c00022135e0001108a6000080bd780004056bc000202b160001014a9000080a53800040529400020294800010148d000080a46000040520400020235e000100d8d0000804d7800040223800020111800010080900008040080004012040002009000001001af
|5=>0x40004000014046bc000a022020005001af0002800c7800120121400082335e0004118ae000208c4200010460b800082215c00041080800020801000010066bc0008032560004018ae000200c53000100622800080310c0004011af0002008d5800100408000080115c0004008840002002d780010012a400080094200040048d00020024280010010b4000800842000400401
|6=>0x20080d78010004ebc00800135e0040003af0020000d780100006b4008000342004000020002000000000a4056b8004a0029c00240116e0012002f780090016bc0048003de00218032f0010c00d780084047bc0042003de00210016e001040af500082006bc004002a5e0020011ef0010003d380080016bc004000b4e00200056e0008000000002001600001000800000800102
|7=>0x80402d380401007bc02001005801000100a0080002d280400006bc0200003560100000ac00800004000400000b002000004001000000a0080000028031000ebc0100000400064003ef0030801f78018000fbc00c00069800510038f0028800c68011046ebc00882335e004410b2d0020808c78010402e3c00820135e0041009ab0020804c7801040220800820075e0040111af
|8=>0x24040003dea800401ef5014000f7a0080006bca0200075e5000003af2020000d78810000fbc404180bde2020805ef1000800f78420404ebc20822175e104011baf0800480d782010020a808000020203400038f0180800c080601006bc03000075e014100baf00a0804c78043001030020800b4601040052300820024680404027bc02020135e0101001ab
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x2000000000000000000
|5,0=>0x2000000300000000000000000000800000901800000d060000000
|6,0=>0xb09800000b0e00000000002a000019000000002000000400000280000034001d30c00000127866001d0e8000060844000000000005602144000000000001b008b40800000000016000002c150018c80992b838f8510004c0000000000c0032094004800000202c000000000000000000060000840000000e02039c4e000028003400011900400000001272003080e00
|6,1=>0x9800060580000
|7,0=>0x43284086758300750a02c2c5e082191c946a221cc2e28211f860365c0582c4d82001aeb1171fc14050b05002057a8107c410600596010091052770100402000f22064010101c10d80fafd22060b808085201350090711bc4f06804838e8072e85daa1c020114c0503c35eef40b04834b333bb4026f7781000070005c9e005001576fb663642648231182200060000232
|7,1=>0x30a81a059f29b21054400162038482732800120505800045f3b0a0a46d021f0009c710ec86b40380154ab73b40927b012f5c65904001d1060b8d1025b011f5fa103598808524b3acb43d4090134a40e0d9063c1001432450083c6eee63bd97e0042039043130c388cac399985e013314ca640010d00281
|8,0=>0x3ab4db7161aaf99eea592b5203545be0a1037f8854404521722518633e00e581ab9514e172b997893360d54ad37f456009476294aab6724250cb26d2b9a43f6f21595173cc1446f04aba5249f7016de50c1ab34f50262b19f4fa562d5dc6e843f174bc5e3393ea66fc6a203657b70960c2f260551d34bed12224b8ad588079a9d46c90e96cb02a478193a8d4743d18b7
|8,1=>0x6b002c35a2254439815216
|9,0=>0x22ca76e14236ac5e21d24db49451003f8cc70b69f4fbe92ab96ec04b04e37249a25853b2226fa
|10,0=>0x4e1a960729f
|11,0=>0x35
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 37 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_249 10 roots_249 ops++addP pm 1 dom_237 10 roots_237 ops++addP pm 2 dom_221 9 roots_221 ops++addP pm 3 dom_189 9 roots_189 ops++addP pm 4 dom_81 4 roots_81 ops++addP pm 5 dom_125 9 roots_125 ops++addP pm 6 dom_248 7 roots_248 ops++addP pm 7 dom_252 9 roots_252 ops++addP pm 8 dom_245 10 roots_245 ops++addP pm 9 dom_109 7 roots_109 ops++addP pm 10 dom_89 5 roots_89 ops++addP pm 11 dom_172 5 roots_172 ops++addP pm 12 dom_157 6 roots_157 ops++addP pm 13 dom_164 4 roots_164 ops++addP pm 14 dom_181 7 roots_181 ops++addP pm 15 dom_108 4 roots_108 ops++addP pm 16 dzo_172_16 5 roots_172 ops++addP pm 17 dom_45 5 roots_45 ops++addP pm 18 dom_217 8 roots_217 ops++addP pm 19 dzo_89_4 5 roots_89 ops++addP pm 20 dom_61 6 roots_61 ops++addP pm 21 dom_244 7 roots_244 ops++addP pm 22 dom_220 6 roots_220 ops++addP pm 23 dom_185 8 roots_185 ops++addP pm 24 dom_236 7 roots_236 ops++addP pm 25 dzo_217_4 6 roots_217 ops++addP pm 26 dzo_236_16 6 roots_236 ops++addP pm 27 dom_205 8 roots_205 ops++addP pm 28 dom_124 5 roots_124 ops++addP pm 29 dom_173 8 roots_173 ops++addP pm 30 dom_73 4 roots_73 ops++addP pm 31 dom_216 5 roots_216 ops++addP pm 32 dzo_173_16 6 roots_173 ops++addP pm 33 dzo_121_4 6 roots_121 ops++addP pm 34 dzo_237_16 7 roots_237 ops++addP pm 35 dzo_249_4 7 roots_249 ops++addP pm 36 dzo_233_4 6 roots_233 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_253 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_172_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_89_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_217_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_236_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_173_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_121_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_zo_237_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_249_4_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_zo_233_4_73 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_249 10 s (0,roots_249.map (·&&&dom_249)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_253 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_249 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_253==dom_253)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_253 gM v ys):RunD true dom_253 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_253 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 34 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 34 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 135 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 135 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 234 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 106 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 234 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 138 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 138 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 34 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 34 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 5 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_253 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555550000000055555554000000005554555000000000
def gsh_222_32:=0x55555555000000005555555500000000555555540000000055545550
theorem lowS_zo_222_32_82:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55005500000000005500550000000000550055000000000055005500,0,8),(0x55555555000000005555555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_188_2:=0x444444444444444400000000000000004444444444444444
def gzo_188_2:=0x444444444444444000000000000000004444444044440000
def gsh_188_2:=0x111111111111111000000000000000001111111011110000
theorem lowS_zo_188_2_172:Lower true dzo_188_2 roots_188 gzo_188_2 6:=lower_iso_b (d1:=dom_188) (r1:=roots_188) (T1:=gsh_188_2) [(dom_188,2)] (by decide +kernel) (lower_slice_b (T:=gsh_188_2) [(0x111100001111000000000000000000001111000011110000,0,16)] (by decide +kernel) lowS_172)
def dzo_174_16:=0x555500005555000000000000000000005555000055550000
def gzo_174_16:=0x555500005554000000000000000000005554000044440000
def gsh_174_16:=0x55550000555400000000000000000000555400004444
theorem lowS_zo_174_16_172:Lower true dzo_174_16 roots_174 gzo_174_16 6:=lower_iso_b (d1:=dom_174) (r1:=roots_174) (T1:=gsh_174_16) [(dom_174,16)] (by decide +kernel) (lower_slice_b (T:=gsh_174_16) [(0x44440000444400000000000000000000444400004444,0,2)] (by decide +kernel) lowS_172)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554555000000000
def gsh_94_32:=0x555555540000000055545550
theorem lowS_zo_94_32_82:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x505050500000000050505050,0,4),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_82)
def dzo_122_4:=0x50505050505050505050505050505050
def gzo_122_4:=0x50505050505050405050505040400000
def gsh_122_4:=0x5050505050505040505050504040000
theorem lowS_zo_122_4_90:Lower true dzo_122_4 roots_122 gzo_122_4 6:=lower_iso_b (d1:=dom_122) (r1:=roots_122) (T1:=gsh_122_4) [(dom_122,4)] (by decide +kernel) (lower_slice_b (T:=gsh_122_4) [(0x5050505000000000505050500000000,0,32)] (by decide +kernel) lowS_90)
def dzo_90_4:=0x505050500000000050505050
def gzo_90_4:=0x505050400000000040400000
def gsh_90_4:=0x50505040000000004040000
theorem lowS_zo_90_4_90:Lower true dzo_90_4 roots_90 gzo_90_4 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_4) [(dom_90,4)] (by decide +kernel) (lower_slice_b (T:=gsh_90_4) [] (by decide +kernel) lowS_90)
def dzo_252_2:=0x4444444444444444444444444444444444444444444444444444444444444444
def gzo_252_2:=0x4444444444444444444444444444444044444444444444444444444044440000
def gsh_252_2:=0x1111111111111111111111111111111011111111111111111111111011110000
theorem lowS_zo_252_2_172:Lower true dzo_252_2 roots_252 gzo_252_2 7:=lower_iso_b (d1:=dom_252) (r1:=roots_252) (T1:=gsh_252_2) [(dom_252,2)] (by decide +kernel) (lower_slice_b (T:=gsh_252_2) [(0x1111000011110000111100001111000011110000111100001111000011110000,0,16),(0x1111111111111111000000000000000011111111111111110000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_236_2:=0x444400004444000044440000444400004444000044440000444400004444
def gzo_236_2:=0x444400004444000044440000444000004444000044440000444000000000
def gsh_236_2:=0x111100001111000011110000111000001111000011110000111000000000
theorem lowS_zo_236_2_172:Lower true dzo_236_2 roots_236 gzo_236_2 6:=lower_iso_b (d1:=dom_236) (r1:=roots_236) (T1:=gsh_236_2) [(dom_236,2)] (by decide +kernel) (lower_slice_b (T:=gsh_236_2) [(0x111100001111000000000000000000001111000011110000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005554000055550000555500005554000044440000
def gsh_238_16:=0x555500005555000055550000555400005555000055550000555400004444
theorem lowS_zo_238_16_172:Lower true dzo_238_16 roots_238 gzo_238_16 7:=lower_iso_b (d1:=dom_238) (r1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (lower_slice_b (T:=gsh_238_16) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x555500005555000000000000000000005555000055550000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_172_2:=0x44440000444400000000000000000000444400004444
def gzo_172_2:=0x44440000444000000000000000000000444000000000
def gsh_172_2:=0x11110000111000000000000000000000111000000000
theorem lowS_zo_172_2_172:Lower true dzo_172_2 roots_172 gzo_172_2 5:=lower_iso_b (d1:=dom_172) (r1:=roots_172) (T1:=gsh_172_2) [(dom_172,2)] (by decide +kernel) (lower_slice_b (T:=gsh_172_2) [] (by decide +kernel) lowS_172)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000505050400000000040400000
def gsh_218_4:=0x5050505000000000505050500000000050505040000000004040000
theorem lowS_zo_218_4_90:Lower true dzo_218_4 roots_218 gzo_218_4 6:=lower_iso_b (d1:=dom_218) (r1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (lower_slice_b (T:=gsh_218_4) [(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_90)
namespace S_254
def pG:List (Nat×Nat):=[(2,18),(2,66),(4,36),(4,132),(6,22),(6,38),(6,70),(6,134),(8,40),(8,72),(8,136),(10,26),(10,42),(10,74),(10,138),(12,44),(12,76),(12,140),(14,30),(14,46),(14,78),(14,142),(16,18),(16,80),(20,22),(20,52),(20,84),(20,148),(24,26),(24,56),(24,88),(24,152),(28,30),(28,60),(28,92),(28,156),(32,36),(32,40),(32,160),(34,38),(34,42),(34,50),(34,98),(34,162),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,72),(64,80),(64,192),(68,70),(68,76),(68,84),(68,100),(68,196),(96,98),(96,100),(96,104),(96,112),(96,224),(128,132),(128,136),(128,160),(128,192),(130,134),(130,138),(130,146),(130,162),(130,194),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|5=>16
|6=>72
|7=>187
|8=>264
|9=>138
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xf76b2a02149c27a8c5a18c4b76d5e66857b67ec46740a5d90d3392d2c6cf1fcba1895313e7e09e53
|6,0=>0xebb4de46dfdcb44daf74d15d4c83ccc6ed0c565cb7bc3b1b14ad60fa9791a7cefa73c6976ed86a858576b851667cd1a7aab877df872032703fe694366810d66ccc65b0d631b05f0e65e3bf5c78b584345827c569b852a1a51b50515d950f094f53d4e1fd4dda44c9c84c7c34bd0941adb410213a91c3a399380ae35b43308a23005b2daf72d3ae2ae0627d252726b270431e7611996f1736a148d813d680eb7f0e16a0c45909e4209b410952c0938809310075d3
|7,0=>0x819f17e9ef7e9657d4787c43e7b65f7997b779d876f1e75624739a771ceb6f9cc6dd6b6cd916c65e6a6dc6950b68c66688b9681fb678d766e79660be63ce4639fe63663604965eb985e1ee5e1555d9b85c2b15a6a95a6895a140589eb583e45822c54712516d8509f44be6c49386478e5470a5449f4446264362d41daa41adb4100240f26408064018a3f1363e8ed3d9713be7f384fa383093792b373193692235e6835d6134401302c12de682ca8d2c6312b2d02af272abad2a25229980299472951b2861e272b7271dd268fd268e0222a6219d2210d7205e81f5f71e88a1dfcf1da201c64e1b7b31b7861b3d0189be16ec9154801460f1404712c8a1287b121cc11afe116fc115a8104fa0f03a0d6ab0c9750acf20a27d07b13073d4070c606afa0691a05b23044d0044c20373c0337f030f802f1c02c6d01e79018cf0118b
|7,1=>0xfc79efc33af9241f5100ef385eb317e5f42e47bbe3079d4ae2d3a75d0afbcf34ccbe71cbc5dcbc12c8f5ac5813c45b6c2559c1cc5bf7a7bc951ba090b8d6eb8b14b7376b710cb64fdb5414b51b4b48ddb48c9b3477b0e40afe65ae7bcac05ea7f2fa767ba4f7ea07e59fe8a9f3d09bca598fae987869613d95e21957a6948ac92b7d8d5ee89a438708e854ec852fd82cfd823a9
|8,0=>0x543b2521e65127e50bff4fbf74ef714ef6a4e4a24e3a84d8764bd2e4bc994bb394b78a4b3934b0b6492d34898d478e54759f471994580e4462a42e9941ee441eda4100240c92407503f3783e65d3d7ad3bc3639d46399e33900b38fb4381183591e33e483312032e483267031ca731b66316452f8722eff62e5be2e24d2d61f2d38f2ce252c49b2b23f2a8932a3e329b182870c280c327a192779a272b726c47266e62487e245712443523b0a2387c2318f215ae21478206921fdbf1f5881f42d1eab71e4f31ddd61bc681b87017ac116ac816519163e81617f15b3a1511214c15149ce12c5f12bd61272612506124fb116f30f5070f25e0e5610cd760c0690bf370bb390a9600a9420a8460a49e0a00009baf0836f080ab077a70722406f0606ce706b440627705fe4054cd0504a04df6040d001dde01d0601ce7019ab01537
|8,1=>0xee187eafdae9464e84e1e707be5ee1e4851e034cdeb1dde2fadc9a2d8808d7d04d39a6d1ab9d140ecb97fc8481c8120c638ec5d3ec3c4dc2667c1e0cbfeebbef45bde13bdb82bc6e2bbb8bbb6f7b7101b6048b579ab35bfb3278b1d2fb19c7b0b29ad5deaaf5ea9145a8642a809aa6900a4ccca3124a30b3a13b2a08f29f9ae9e9c59cd409b22998af897cad97a7e965409546f939dc9274391c1c9147090d299096a8e1738a9e088e6787fb68604185fa68553b8507784ac782ceb817d880f9d80d1e7fc8c7fa527f3a27e9977e9657d7fd77ef677ab677a067798076221758ef74dfe7478c72f417248c71ca970afc7018d6eef36e0136d3326c28b6bca56b00b6adc86a87565f9c64ab363b3762f9e62cd36252e61ffc61639604965fc515f4465eb985ded55b0265af4c5a95f597d758e3e585ad577535663b55b5755a84
|8,2=>0xfc33afb99bf9cfbf8947f3f5df24aaf1cd2ee8ac
|9,0=>0xdc5c1daa7dda902d71ffd593bccee2ca726c74aac690fc638ec5d3ec50d5c1ebcbbf3eb87bfb3f32b30c8aadf3a7bc9a5b9fa5351a0f2ca0dd99da0a9c7929bb189b9d09a022959cf958548ce798c1cf8a9a48894986ce086041854cd8369c7fb287ae8879c4878790763a974b6c73e2372f41723ce720126dee66dd176c32e6beba69ece6594564b8f60eff5b1cb5acf6585ad5739256d6956bb9569d15503154eb654e795356250c20500544d0304c8784b93a4b78a4a08949690489e84362040d043fef23d82d3d4323d41e3cfd43c4753b7e638d90384db3662f33e4b338eb31e4a2f2ea2d67c2d5cf2ab44286c9266e62528c21468212b720f571f3011dea81b2a019edb1965f18eaf181ab17bb715e8815b0313ad410944101780dd770d4c00c0080b0650a68e0a36b099df0673d0662e05515043670274d0155b003a0
|9,1=>0xfc636fc33afa3ebf9222f37ffe8b2ee5cefe4e58ddce7dccec
|10,0=>0xd1192ca50cc5d3e8a5a08a4257d51a758d07553b4b78a46dd43e2612224d0a6d404bea
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a155540001555400011110000111100001555400015554000111100001111000000002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002222000022225555555555555555555555555555555555555555555555550000000000000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015555555555555555555400015554000155555555555555555554000155540002a802a802a802a802a802a802a802a802a802a802a802a802a802a802a802a8055555555555555554444444444444444555544445555444444444444444444440a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a000000015555555555555555555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000005555555555555555555555555500550055005500550055005500550055005500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a111111111111111111111111111111111111111111111111111111111111111100002aaa80002aaa800022220000222200002aaa80002aaa80002222000022225555555555555555000000000000000055555555555555550000000000000000
|0,1=>0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000002200aa00aa000000015555555554455445555555555401540154015401540154015401540154015402aaaaaaaaaaaaaaaaaaaaaaa80000000000000000000000000000000000000000000444400004444000044440000444400005555000055550000444400004444aaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa8888aaaa8888aaaa0000aaaa000111111111111111111110000111100001111111111111111111100001111000000002aaa80002aaa800000000000000000002aaa80002aaa80000000000000005555555555005511555555555500550055005500550055005500550055005500aaaaaaaaa0a0a2a2aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a11111111111111111111111111111111111111111111111111110000111100002aaaaaaaaaaaaaaaaa802a802a802a802aa22aa22aa22aa22a802a802a802a800505050505050505050505050505050505050505050505050505050500000000aaaaaaaaaaaaaaaaaaaaaaaa88880000888888888888888888880000888800004444444444444444444400004444000044444444444444444444000044440002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80000000000000000000005500550055005500110011001100110055005500000000
|0,2=>0xaaaa8888aaaaaaaaaaaa0000aaaa0000aaaa8888aaaa8888aaaa0000aaaa000155555555555555540000000000000001555400015554000000000000000000002828282800000000282828282828282828282828000000002828282800000000000000000000000555555555555555511111111111111115555555500000000222222222222222222222222222222222222222222222222222200002222000001540154015401540154015401540154015401540154015401540154000000008888888888888888888888888888888888888888888888880000000000000005555444455554444555544445555444455554444555544445555444455554444aaaaaaaa0000aaaaaaaaaaaa00000000000000000000000000000000000000015555555400015555555555540000000155555554000155555555555400000002aaaaaaaaa802aaaaaaaaaaaaa802a802a802a802a802a802a802a802a802a804444000044440000444400004444000044444444444444444444000044440000aaaaaaaaaaaaaaaa0000000000000000888888888888888800000000000000015555555555555555555555555555555511111111111111111111111111111112aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000005555555555555555444444444444444455555555555555554444444444444444
|0,3=>0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaa00aaaaaa00aa00aa00aa00aa000000000155555554000000015555555400000001555555540000000000000000008800880088008802a802a802a802a8008800880088008802a802a800000001111111155555555000000005555555511111111111111110000000000000000aaaaaaaaa0a0aaaaaaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a15555555400004445555555540000000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80005555555511111111555555550000000000000000000000000000000000000000aaaaaaaa22222222aaaaaaaa00000000aaaaaaaa22222222aaaaaaaa000000004444444444444444000000000000000044444444444444440000000000000002aaaaaaaa8a8a8a8aaaaaaaaa8282828282828282828282828282828282828285555555555555555555555555555555555555555555555555555555500000000000000000000000000000000aaaaaaaa0000aaaa0000aaaa0000000000000001111111115555555400000000000000011111111111111110000000000000000222222222aaaaaaaa22222222aaaaaaaa22222222222222222222222222222220000000055555555000000005555555500000000000000000000000000000000
|0,4=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888888888888889555400015554000155540001555400015554000155540001111000011110000000000000000000000002aaa80002aaa800000000000000000002aaa8000000044444444444444444444555544445555444444444444444444445555444444440a0a0a0a080808080a0a0a0a0a0a0a0a0a0a0a0a080808080a0a0a0a000000015555555555555555555555555555555444444444444444440000000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80005555555555555555550055005500550055005500550055005500550055005500aaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000015555555555555555554155415541554155415541554155415541554155415540000000000000000002a802a802a802a802a802a802a802a8000000000000000050505050505050505050505050505050505050500000101050505050000000000000000000000008888888888888888000088880000888888888888888888881414141414141010141414141414141414141414000000001414141400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80002aaa80000000000000005555555555555555555555555555555555550000555500005555000055550000
|0,5=>0xaaaa0000888800008888000088880000aaaa0000aaaa0000888800008888000000000000000000000000000000000001555555555555555555555554000000022222aaaa2222aaaa22222222222222222222aaaa2222aaaa2222222222222220000000000000000555555555555555500000000000000004444444444444444aaaaaaaaaaaaaaaaaaaaaaaa000000000000aaaa0000aaaa000000000000000155555555111155555555555511111111111111111111111111111111111111100000000000000002aaaaaaaaaaaaaaa80000000000000002aaaaaaa800000001111111111111111555555555555555511111111111111115555555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaa000000000154015401540154015401540154015401540154004400440154015400000000000000000000000000000002aaaaaaa800000000000000000000000000000005555444455554444555555555555555555554444000000005555555500000000aaaaaaaaaaaaaaaaaaaa8888aaaa8888aaaaaaaaaaaaaaaaaaaa8888aaaa888955555555555555540000000155555555555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaa800000000000000000000000000000005555555500000000555555555555555555555555000000005555555500000000
|0,6=>0xaaaaaaaaaaaa0000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa0000000155540001555400015555555555555554000000000000000000000000000000002828282828280000282828282828282828282828000000002828282800000005555555555555555505050505050505054545454545454545050505050505050aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa88888888aaaaaaaa00000001555555540000444555555554000000015555555400004445555555540000000000008888000088880000000000000000000088880000888800000000000000000000000000000000000000055555555555555555555555500000000000000000000000000000000000000000000000000000000aaaaaaaa00000000aaaa000141414141414141414141414141414141414141415555555541414141555541400000000000000002aaaaaaaaaaaaaaa88888888888888888000000000000000000000005555444400000000555555550000000000000000000000000000000088888888888888888888000088880000888888888888888888880000888888880001555400015554000155540001555400015554000155540000000000000002aaaaaaaa222222222222222222222222aaaaaaaaaaaaaaaa2222222222222225555555500000000000000000000000055555555555555550000000000000000
|0,7=>0x88888888888888888888888888888888aaaaaaaaaaaaaaaa88888888888888895555555555555555555555551111111111111111111111111111111111111112aaaaaaaaaaa80002aaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa8000111111111111000011110000111100001111111111111111111100001111000022222222222222222222222222222222222200002222000022220000222200015555555555555555555400015555555555555555555555555554000155540002aaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaa80002aaa80002aaa8000111111111111111111110000111111111111111111111111111100001111000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000aa00aa00aa00000001555400015554000155555555555555555554000155540001555555540000000028282828282828282828282828282828282828280808080828282828000000055555555555555555555555555555555555555550000555555555555000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a0a0a000000000000000000000000000000000000000155555554444444455555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222220505050505050505050505050505050505050505050505050505050504040404
|0,8=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaa0000aaaa000044440000444400004444000044440000444444444444444444440000444400000000000000000002aaaaaaaaaaaaaaa80002aaa80002aaa80000000000000000000000000000000000000000000000055555555555555555555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaa88881414141414141414141414141414141414141414141410101414141414141012aaaaaaa80002aaaaaaaaaaa800000002aaaaaaa800000002aaaaaaa800000000000000000000000000000000000000055555555000011115555555500000000aaaa0000aaaaaaaa0000000000000000aaaa0000aaaa000000000000000000004444444444444444444444444444444444444444444444444444444444440002aaaaaaaaaaaaaaaa22222222aaaaaaaaaaaaaaaaaaaaaaaa2222222222222225555000055550000444400005555000055550000555500004444000044440000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000015401540154015401540154015401540154015401540154015401540154000000000000000000000000000000000002aaaaaaaaaaaaaaa80000000000000004444000044440000444400004444000055550000555500004444000044440000
|0,9=>0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaa00000000000000000000000000000000000000015555555400000000000000015555555555555554000000008888000000000002aaa80002aaa800008888000088880002aaa80002aaa80000000555555555555000000005555555500005555000055550000000000000000888888888888888888888888888888888888888888888888888888888888000155540001555555555554000155555555555400015555555555540001555400000000000000000002aaa80002aaaaaaa80000000000000002aaa80002aaa80000000555500005555000000005555555500005555000055550000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00002222aaaaaaaa000000011111111111111111555555555555555511111111111111100000000000000002aaaaaaaa22222222aaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaa800000000000000055555555000000005555555500000000000011110000000000000000aaaaaa00aaaaaaaaaa00aa00aa00aa00aaaaaa00aaaaaa00aa00aa00aa00aa00000000000000000000000000000000000000000044444444000000000000000282828282828282828282828282828282828282828a8a8a8a8282828282828280000000000000000000000000000000000005555000055550000000000000000
|0,10=>0xaaaa0000aaaa000000000000000000000000000000000000000000000001555400000000000155555554000000015555555400000001555555540000000088888888888888888888888888888888888888888888888888888888000000055555555000000005555555500000000555555550000555555555555000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaa0000aaaa00015555555555540001555555555554000155555555555400015555555555540002aaaaaaaaaaa80002aaaaaaaaaaa800000000000000000000000000000000000111111110000000000000000000000001111111111111111000000000000000000000000aaaa000000000000aaaaaaaa000000000000000000000000000000015555555555555555555555555555555555551111555511115555111155551112aaaa2222aaaa2222aaaaaaaaaaaaaaa800000000000000000000000000000005555555555554444555555555555555555555555000000005555555500000000a8a8a8a8aaaaaaaaa0a0a0a0a0a0a0a0a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a000000001111000000000000155540001555400015554000155540001555400000000888aaaaaaaa800000002aaaaaaa800008888000088880000000000000005555555555555555555555550000000044444444444444444444444400000000
|0,11=>0xaaaaaaaaaaaaaaaaaaaaaaaa88888888aaaaaaaaaaaaaaaa00000000000000015555555555555554444444444444444555555555555555544444444400000002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa800000000000000000001111111111111111111111111111111111111111000000001111111100000000aaaa2222aaaa2222aaaa2222aaaa2222aaaa2222aaaa0000aaaa2222aaaa0000000000015555555400000000000000000000000000000000000000000000000000000002aaaaaaa8000000000000000000000002aaaaaaa800000000000000055550000000000005555000055550000555500005555000055550000555500000000000000000000aaaa0000aaaa00002222000022220000aaaa0000aaaa00000000444400004444000044440000444400004444000000000000444400000000888888888888888800000000888888888888888888888888000000000000000555555551111111155555555111111115555555511111111555555550000000000000000000000000000000000000000aaaaaaaa0000aaaaaaaaaaaa000000015555555555540000000000000000000155555555555400000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000444444445555555500000000000000004444444444444444
|0,12=>0xaaaa0000aaaa0000aaaa000000015555555555555555555400015554000000000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaa800000002aaaaaaa800000000000000000000000555555555555555555555555555555550000000000000000000000002222222200000000222222220000000000000000000000000000000155540001111000015554000111100001555400015554000155540001555400022222aaaa2222aaaa2222aaaa2222aaaa22222222222222222222222222222220000111100001111000011110000111100000000000000000000000000000000aaaaaaaa00002222aaaaaaaa00002222aaaaaaaa00000000aaaaaaaa000000011111111111111111555555555555555511111110000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaa22222222aaaaaaaaaaaaaaaaaaaaaaaa22222225555000055550000555500004444000055550000555500005555000044440000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00011111111111111111111111115555555511111111111111111111111111111112aaaaaaaa22222222aaaaaaaa2222222000000000000000000000000000000005555555544444444555555554444444455555555444444445555555544444444
|0,13=>0x888888888888aaaa888888888888aaaa8888888888888888888888888888888800000001555555540000000155555554000000004444444400000000000000000002aaa80002aaa8000000000002aaa80002aaa80002aaa80000000000000000000000000000000000000000000000000000000555555550000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a1555400015555555555540001555555555554000155551111555400015555111000000002aaaaaaa8000000022222222000000002aaaaaaa80000000222222225555555555555555555555555555555500000000555555550000000044444444a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0000000015555555400000001555555540000000000015554000000000000000000000002aaaaaaa800000002aaaaaaa800000002222222200000000222222225555555555555555000000005555555555555555555555550000000044444444000000000000000000000000aaaaaaaa0000000000000000000000008888888955540001555400015555555555555555555400000000000155555554000000000000000000000000000000000000000000000002aaaaaaa80000000222222224444444455555555444444444444444444444444444444444444444444444444
|0,14=>0xaa00aaaaaa00aaaaaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000001555400015554000000000000000000015554000000000000000000000000000000000000000000000000000000000000000000000002aaaaaaaa22222224444444444444444555555555555555544444444444444445555555544444444aaaaaaaa00000000aaaaaaaaaaaaaaaa000000000000000000000000000000015555555555555555555400015554000155540001555400015554000155540002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaaaaaa80002aaaaaaa800000000000000055555555000000005555555500000000555555550000000055550000000000008888888800000000aaaaaaaa000000000000000000000000000000015555555400000001555400000000000155555555555555555554000155540000888888888888888888888888888888880000000000000000000000000000000555511115555111155551111555511115555000055550000555500005555000000000000000000002222222222222222000000000000000000000000000000015555555400000001555555544444444555555554000000015555555400000002aaaaaaa800000002aaaaaaa88888888800000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000
|0,15=>0xaaaa0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000aaaa00000000000000011111111155555555111111115555555511111111555555551111111111111112aaa8888aaaa8888aaaa80002aaa80002aaa8888aaaa8888aaaa80002aaa80005555555555555555555555555555000055550000555500005555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaaaaaaaaaaaaaaaaaa00004444444444444444444444444444000044444444444444444444444444440002aaa80002aaa800000000000000000002aaa80002aaaaaaa8000000000000000515151515151515150505050505050505050505050505050505050505050505022222222222222220000000000000000000000000000000000000000000000015555555555555555111111111111111111111111111111111111111111111112a802a802aaaaaaaaa802a802a802a802a802a802a802a802a802a802a802a8055555555555555554444444444444444000000000000000000000000000000008888888888888888aaaaaaaaaaaaaaaa0000000000000000000000000000000155555555111111115555555555555555555555540000000155555554000000000000000000000002aaaaaaa8000000000002aaa800000002aaaaaaa800000000000555500005555000055550000555500005555000000000000555500000000
|1,0=>0xaaaa2222aaaa2222aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000000000000001555400000000000000000000000088888888000000000000000000000000888888880000000000000005050505051515151505050505050505050505050515151515050505050505050000000000000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000111100001111000015554000155540001555400015554000155540001555400000002aaa80002aaa80002aaa8000000000002aaa80002aaa80002aaa800000005555555555555555555555555555555500005555000055550000555500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa00001414141414141414141414141414141414141414141400001414141414140002aaaaaaaaaaaaaaaa2222222222222222aaaaaaa80000000222222220000000000000000000000000000555500005555000000000000000000000000000000008888888888888888888800008888000088888888888888888888888888888889555555540001555555555554000155555555555400015555555555540000000000000002aaaaaaa800000002aaaaaaa800000002aaaa222000000002aaaa2225555555544444444000000000000000055555555444444440000000000000000
|1,1=>0x2222222222220000222222222222000022222222222200002222222222220001555555555555555555555555555555540000000155555554000000000000000000000002aaaaaaa800000002aaaaaaa800000002aaa8000000000002aaa800000000000000055550000000000000000000000000000555500000000000000000000aaaa0000aaaa0000aaaa0000aaaa0000000000000000000000000000000111100001111000011110000111100001111111111111111111111111111111100002aaa80002aaa80002aaa80002aaa80002222000022220000222200002222444444445555555544444444444444444444444455555555444444444444444400000000000000000000000000000000222222222222222200000000000000014141414155555555414141414141414141414141414141414141414141414140000222200002aaa8000222200002aaa800022220000222200002222000022225555444455555555555544445555555555554444555544445555444455554444aaaa0000aaaa0000aaaa2222aaaa2222aaaa0000aaaa0000aaaa0000aaaa00015555555555555555555555555555555400004444000044440000000000000002aaaaaaaaaaaaaaaaaaaaaaa800000002aaaaaaa800000002aaaaaaa800000005555555555555555555500005555000055555555555500005555000055550000
|1,2=>0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015555555555555555414141414141414141414141414141414141414141414142aaaaaaa88888888aaaaaaaa88888888aaaaaaaa800000002aaaaaaa800000000000000000000000555555555555000000000000000000005555555555550000aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaaaaaa8889111111111111111000000000000000015555555555555554000000000000000000000000000000000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa80005555555555555555000055550000555555555555555555550000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888aaaaaaaa888888880000000000000001555400015554000155540001555400015554000155540002aaaaaaa800000002aaaaaaa800000002aaaaaaaaaaaaaaaaaaaaaaa800000005555000055550000555555555555555555550000555500005555000055550000
|_,_=>0
def sP:Nat→Nat
|0=>0x1868001d0582404070e0000c0b088242c1400018161b048080e000302c121a0380032060284430030100016110200c240c028100602070001604018081c0c028441217010000a110480c26000584408030b03016110a8080e0c058442a020a03016110480c260c02844120f09000161101808200c028241e02070001604018081a0c058281208038180a04018080200
|1=>0x58240602068303a0b088241e1a0001816110200c040c1482c22090184c000605824040e0a0000c0514044120f010001611048080e0c1182c2209010501823028240602008003a050889406020002c12220701c0006058240602008303a0b088244807000180a0b0885406020601422040188004000584406020f8000c0b088780602060001611048580e00030142209
|2=>0x10380006058440803010306c0b0880c042a0608c0a11048d404001a02c221501808180b088240602060cc162f0480c4006058281202038b80c0b048081c2d00018162c0882406020602c120f010040006058441217010000c0b088245607000181611048ac28000302c22090901c00060584412120a0000c050586c12031001816110185854000302c22150101c0006
|3=>0x88100602001040a280881006020002c50110200c040c058447e03010307c0b088240616060741611018087a000302c2203158a8000605824060e000f00c0505044120f0100016110184854000302c220401848000602844123b010003205088100602000d80a110480c04001d02c72110200c040c058441212168000c05088780602000d816030103854000302c0803
|4=>0x18089c000302c220901808004a1c02c220901930000605844060215000520605828220901808181d05844120301000941d02844120f010006c0b0504408030103016110480896000302c221e01808004a058a014091001c0c0b248441203010301611230081845058441202220000c0b0886006020001816110490c0e000302c2209011080006058240602070303a0b
|5=>0x584412032d0000c0b050240407000640c0b08824061a000f80c21058240602070300c0b2c0441203010000c0b0880c0456000181609018081c00031541639088240407000181654088240602000181609018680019030c016390882404140001816530882404070001816110480c345200018a00b088240612000180a110480c04001c01416090101c0200030141609
|6=>0x10000c64058441203318000c21028240602070000c0b088240602061883a0b08824061200018aa0b08824042d000d80c34058240602070000c0b088246a020001816110200c040c0002c12030117c00060584412020380082062f02c12030103800061a02c220901808182305844125d0101c00060584412022e01c000605844120301000b60602828220901808001d
|7=>0x480c0401000f80c0b0880c042a000d80c0b051001202038000c0b088247602000640c050584412031008c0c0b088100602000d80c0b088240602000f00c0b08824060200018745e058441203090000c0b088240602061a0000b08824cc02000181609018080252000181609018c41c000308416110480c240c0302c221e0180800360302c2209018081865058441203
|8=>0x368003206058441203010305c3e058447e0301030162808824041400018160a088241e020001816390880c042a00018680b08824062b00018161104888040706000161104888041406000420b0480c044e0601816110480c040c000e04205088240612000181609010380e000302c22093600818061a02c22090184800061082c2209018ac1806358441203010300c0b
|9=>0x50441212038000c0b0880c0477000640c0b140281202038000c0b0480c040d000f80c05058240602008000c0b08854060206018167608824060200018161104808ea0025018161104808e6000c818680b0480c044e000181611048480e000302c22090184800061814016110480c3400031c816110480c04002502c2209011c00006058441202038d83206058441202
|10=>0x282c12030103400060282c120301200000605824061a001040c0b08824fe02038000c6b0882406020001816110480cfc000317816110480c04002082c2209019f000060282c22090190c0006058448c48010300a0b088240602060b8162808824042d00018161104808f6070001816590480c040e00018160a0480c10060582440020701c00060584412033c0000c0b
|11=>0x18081c00030741611048080e0c00204161104808280c0020416110480c040c1b0740a0b088fc060200018e40b08824060206000160a0882440020381816110480d0c000302c12030121000060596422090184800060584412023a8000c0b140440602150000c0b0880c048200018161101808ee00208180a110483c0400058a02204018080006058440622010a81800
|12=>0x30141609010380e000302c22090101c00900301416110480d1c000302c22090184800060e82c220901808188d0301422090180800361c02c14110480828000301422090180800360e82c72110480c040c0e82d1811048080e000302c2209012280006058441202038005c06448441203010000c05058a01409018800c88058441203010000c0b050240602438181609
|13=>0x200c04000301416090186800190325416110480c04000302c22090180800940302c120301210a4000302c22090780800360302c2203010a818004082c1411048085a000302c2248018081845058452603010000c0b088240407001880c0b088240414001880c0b0887806020001816110480c2c001f0181611048080e010001816110480cf05200018161104a440400
|14=>0x3800160a0882404071b0180a0b0480c440e000180a280882406020007416110480c04a006278220901808000605a741203010000c0b050240602002700c0b08824069b0001816114c824060206018161104808da000302c2209018080098031a80a110480c04000302c14110180854000325c16110480c040003014161b0480c04000302c50110480c040c0e82c1411
|15=>0x10003a72058441203010000c0b530441202038000c0b088240602290000c0b088240414000d80ca4058441203010000c0b088240407001a40c0b14044120f010000c0b088240602061a00a110200c04000584412a3010000c0b0881006020602d4409018080006058a01409018800c300584412033f030000b1782406020001816110480c0400508181640088244402
|16=>0x88244002038000c0b088240602568000c0b088240407002040c0b0882406020608c0cac058441203010000c0b08824060206001023e0584556090180818060282c220901808f600030d016110480c9e0200018165308824060200018600b200240602002a40a0b0480c4002070000c0b088240602268000c0b088240602002a00c0b088240602000640ca7028441203
|17=>0x302c2209019740400030c00a0b08824067f010000c0b0882406025b0000c0b050240602000640c300584412030114800b50302c223f01808000605828220901808a4000322416110480c0400032d016110480c040c00019660b088240602000640c0b088240602002c40c0b088240602580000c2105844120311008180b0480c040d060000cae088240602000180a0b
|18=>0x480c04bf000180a0b050441203100080c21058a022090180818060590022090101c0006058441203012f800060590022090180818001f02c22090180800bd0302c500a0480c400605828220901808003e0302d76110480c04000302c22090180800065282c50110480c04000315416110480c04ad060000c0b5c02406020001816110480c24000314416b70480c0400
|19=>0x2c8441203010006c06059e822090180800066382c22090180800061a02c50110480c04000301416110480c040c0020416110480c04004b01816110480c040c002f40c340584412031100818002b82c22090180800360302d8c110480c04000302d88090180800066182c22090180800060584412036100800061302c2209018080041031781628088240602000181611
|20=>0x4b0180a0b460441203010000c0b0882406d0000181609018081c00030c016110480c04cf0001816112312004000302c220901a3800060282c220901808002e0301416110480c34000333416110480c04000302c22090780800061082c22090180800410302c22090180998001081450110480c04000302c220901808003c0302d9409018080006058441203648000c0b
|21=>0x480c04000302c220901809b0000302c22096b8090206058a022090101c00060282c22090188044000302c22090180800d60302c220901809a8000301416400882406020600016110480c040c6600016110480c040c0007416110480c04d30001816d2088240602000640c0b088240602688000c0b08824060200270320605844120301000c43e0302c2209018081800
|22=>0x282c1203010040006058441203010006c061c02c22090180800067082c2209018080036030740a0b088240602008000c0b0882406226c8000c21058240602070000c0b0882406df0001816110480c2400030c016110480c0400253780c0505844120301001200605844120301001ba06058441203010d832061802c22096d80800063a02c22090180800410302db411
|23=>0x1816112400c040c0582822090184800061802c220901809d0000302c22090180800067382c22090186800062882dcc110480c04000302c22090185800060586c1203010000c0505844120301000c40605b90120301030000b0480c34000c81816110480c04004081816280502406020001860210584412030103102e2058441203010000c50058282209018080006
|24=>0x180800060582822090180800062abb416110480c04000302c2209019f80006058240622070000c0b0882406027403000067602c22090180800060584412031000094060584412030b0300006058441203120000c0b088240602001040c0b0480c4002070000c3005844120301205d621058441203090000c0b750240602060006e0508824060200019d20b088240602
|25=>0x183c816110480c0400033c42209018080006058441203010304605058441203100006c06108441203013c000062f02c14110480c0400033b416110480c040c00018167a088240602290000c210582822090180818060596450110480c04000302c22ef01808000605844120301001dc061a02c22090180818004082c22093600800060282c22090101c0036031ac2209
|26=>0x3101912110480c04000302c12030103818000302c22090180998810282c80110480c44020002c22090180800f90322c16110480c04000302c22097c00800060584412020a0000c05058282209018086c061081414110480c04000302c220901bd8000605845ea03010000c050582406200100400061a02c14110480c04000302c22090188800f4058282209018800406
|27=>0x180800620302c22090180800361f01816110480c04007f81816110480c24000302c1411048080e000302c220901bf80400030dc16110480c040c000181628088240602000183a6f0584412030100032060584412020383000060282dfa110480c04000302c22090105018000302c220901808a4001b01816fc0882406020001816110480df4000308416110480c040c
|28=>0x480c049f0302c22090180a02000315c16110480c04000301416110480c040034818167d0882406020001816110480c040100018600b08824042d000181639088240602000f80c0b0502406021701816110480c40310001816110480c04a00001816112400c040c0002c22090184818000302c2209018ac00060584412037f00818000308422090180a00061a02c2209
|29=>0x10300c05058e422090180800060584406021503000060282ca6110480c04000302cb20a0882406020001816110480a0c000301416280882406200001816110480c0400438180a0b530441203010000c0b088240602828000c0b0880c042a0001816110200c04000301416115582406020001816110480e06000340816110480c0400030141628088240407000184211
|30=>0x1808003e034442209018080006058441203010300006058441203010000c3805c40220901808000605c3c1203010000c05058441203010008206058a0220901808a4000302c220901808010e0302c22098600800062802c22090180800360302e16090180800060584412030100032d60302e14090180800060584412030142000063882c22090180800060584412d7
|31=>0x88240602000d80c0b08824060266084163908824060206018680b088240602000d80c210882406020027c0c5e058441203010006c0605c4c1203010000c6a058441203010000c21058441203010306c061b81422090180800360302c220901808003603154160a088240602000183a0b088240602004480c5e05844120301030000b050441203010d80c30058a02209
|32=>0x480c04001f01816110480c40001b01816110480c0400032e816110480e30020001816110480c04008b81816110480c045200018a00b140441203010000c0b088240407000d80c0b088262c0200018161104b5c040c0001816110480c040c6602c220901808181d05844120301000d2061802c22090180a2a000301416110480c04360c8181714088240602000184205
|33=>0x1b01816110480c0400031b816110480c04001481816110480c4402060000caa108441203010000c0b088240602060007c060590022090188804001082c22090180800360302c14110480c04360302c220901808011c0302c220901c6800060590022090180800e5058240620010040006058a022090180800062882c22090180a32000309816110480c04000c8181611
|34=>0x480c040c0001816110480c040030018420b200441203010000c0b088240602780000c0b0882406c90001816110480c04000332016112400c04000302c220901808180014819540b088240622010000c0b08824060200019e80b0882406028f8000c21058441203010010206058441203010023c0605bf422090180800060590022090180a3a000302c220901808004a
|35=>0x100000c0b530441203010000c0b08824060206002362105844120301424000605c881203010000c0b08824060200019c00b08824060200204a20b0882406020008c0c0b08aac1203010000c50058441203010000c0b140441203010000c309082c2209018080006058441203010000caf05844120301000d2060282c14110480c04000302e40110480c0400030141611
|36=>0x882406020600102060582822090180800062882c22090180818b90308416110480c040c0302c22090180800068244416110480c04000302c22090180a48000302c22090180800062a88416280882406020001816400882406020014416390882406020001816110480c04004081816530882406020001816110480c040c000d80d23058441203010000c0b140441203
|37=>0x1bd80006058240602070000c050584412031100800060582880090180800060584412030142400061a02c22090180818000302c22090180801260302c2209018080036033cdf60b08824060200018420508824060200018680b08824060200018bc0b0882406020001a4a0b0882406020001816110480c04002081816110480c04d9000181639088240602060000c0b
|38=>0x180818000302cf2110480c04000302c22090180801000302c220901b2404000302c50110480c040c0001a500b0882406020001816110480c24000302c14110480c0400030c016110480c04360c81a4e0b0882406020001816110480c4402060006e0b0882406020001816110480c051d000181611048080e00032a816400480c0400032a980110480c04000302c2209
|39=>0x584412d70100172060582822090188004060282c22090180800810302c80110480c44020001816110480cfe02000180a0b088240602000d80c0b0882406020611c16590882406020001816110480c0400033ac16110480c04004f818160901880040e0001a520b0882406020001816110480c040003304420b050441203010000c0b0882406020600172061082c2209
|40=>0x882404070001816110480c040100019540b088240602060000c0b08824060240ae40c21058441203012040c0b0882406f6010000c0b050441203010300006108441203010017206058441203010006c0628c8416110480c040040818168c0882406020001a22110480c04000302c22090180818000302c2209950080006058441203010000c1d058441203010300081
|41=>0x8824060200018600b088240602000188e0b088240602002040c0b08824060200018a20b088240602000d80c05058441203010000c0b088240622010000c0b08824060200019ca0b0882406024094416110480c04520001816110480c04006e01816110480c04001b018612b08824060200018161104b5c04000302c2209018081800238141628088240602000180a0b
|42=>0x58441203010000caa058441203010000c0b050441203010000c0b088240602060000c0b088240602002e40c21058441203010000c0b140441203010000c0b
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d30151809cc0486021300f1806cc030601530091803cc018600930031800cc0006
|6,0=>0x10b3883dc410e20170fd387cdc3d8e1e570ef3875dc3a0e1c970e1386edc368e1ad70d33867dc330e19170c53860dc2f8e17570b7385a182c2e15a70aa30535c28ce13f709c384c5c254e123708e38455c21ce1077080383e5c1e4e0eb707238375c1ace0cf706438305c176c0b47056b8299c13ee0987048b8229c106e07c703ab81b9c0cee0607
|6,1=>0x126b8919c47ee2387118b88a9c448c21d7
|7,0=>0x21f410da085d0426820fb9061c82104088200b8fe607e303e981f0c0f6607a303c981e0c0ee6076303aa71d140e6dc727038b81c238df206eae36d81b2c0d7606ab034d81a338cfdc670e330819440c8206310310818440c0205f2e2f18174c0b8605b302d2716540b0a057502b2815540a8a053502928145b8a0e04f7027381363899204b902548
|7,1=>0x314398820c32e6118304c1809cbf505f282f54178a0bb505d282e54170dcb78e5b482d6b96960b3ce59682c8316220b01057882b8415a5cac3055a72a9b952e0a88e53c829b314ba0a4d051e828b414418a110501727cc13c609d304e1826cc1349c99504c2825d412ca0956e4a3824dc124e0918e484823e411d208dcc466822f4115a089d04468
|7,2=>0x1fb60fcb07dd83eac1f360f8b07be73dc31ec5cf56c7a473ce41e55cf1ce78683bf41dda0edd076683afb9d61cea2e74983a139cea0e66e72b8391c1c6e0e27070b8381c1bee0de706eb8371c1b6e0da706cb8361c1af1cd6ae6ad8352c1a79cd2d068e8343419fdccef066f8333c197e0caf064f8323c18fe0c6f062f8
|8,0=>0x500ba7e253e109e884efca75a539d09c594de4a6ce535709a474ce426521317298294bd425c652d1296084ac4253e528f0940749bca4be124f091e948aca439d20d08ff747b4a3b651cb08dc9469ca331d18728bb84594a2a6514308998448c22261104e8799438c21a610c3085984284a122107f28369416ca099d03b28158406c20124ffae7f58
|8,1=>0x60342ffa17f0cbef95f3c2f7e17af0bcf85e43af05d7712bb175d53ae8a17332b9185c4c2e0256f10b6f95b3c2d7a56ab2b4d85a2c2cf9d66d0b2d95924ac7216272b0c7581cabee15e70aec757242b6e55a70acb85614aaea15650aaa8550caa6615212a87953f4a9d654dcea66852f4295dd4a0ea47951fc28de1460ea2795103a85e541f0a087
|8,2=>0x705cb811dbf72df296f54378ddbb70dd386e54b7065b712db086d3cb67e1b2d2d8e86c3bb5fa5aeeed6f86b43b57e5aaf0d4f86a43b505da712d2f96943b485da312d0f96843b3fe59ef0cf07674bb38259b10ccf96634b2f659692cab96523b27219272c8c7641cb1f1d8e72c6b86323b175d8a92c4c8622430f2186aec2d86124b075d82b0c0e7
|8,3=>0x809c402a60050ff997f9b3faa5fc32fd987e84bf25df830fb897d7cbe9a5f3b2f9587c6c3e125ef72f7477b643d921eb90f5577a64bd0e5e770f347795cbc91de372f14778643c121dfaeef4977643b8e5db52ed377654bb0a1d732eb187553ba8ddd352e937745c3a0a5cf6ee738735c398a5cb50e5197253b9065c74ee3287154388ddc370e147
|8,4=>0x829441266083103a7819440ade048f01b9
|9,0=>0x92fc495e249f1247891fc48da645d1226890f4485a241b320588fec47d623db11e498eebc756239b11c588dec46d6235931a488ce446522317318388bd4c5ca22d3316188ad3c54a2296f142989ccc4c622531120988c44442220f30fe987b443ba21cb30dd886a4c332218730bb8859c42b1e149109c8849cc22e2105307a8839441aa20c5105a8
|9,1=>0xa34cd18628b314518a244d102286f342e9a134507de82f14107a044500227f113f089f3ccf7a67ad13cd99e33cefa276d13ae89d344e7a272d138d99c24cdee66e7136b89b1c4d6a66a5134b79a14ccea2665132a899144c6a2626f30b8981c4bf1e5eaf2ec997244b7225a732cb89614caea256512aa895144a6a2525128a8940cc9e264df32678
|9,2=>0x2974f4b28a55452866934f4937a45c520a68f514728
|10,0=>0x2a5315218a8cc54462a1315018a7cc53c629d314e18a6cc5346299314c18
|11,0=>0x15317
|_,_=>0
def wAt:=mkWire dB 300 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x200000881901875108180581905801058190189d13018058650581904875108180580100019048751081805801048e11b81805819058d905819018e11b818058d90100205831000190488d1100001019088c90100118800010c10581a0888d110000100101019058190001904875108180580105819018751081805801058190489d130180586508802058190488d11000010190001905819048751081805801
|1=>0x8801000c1050080581a0500b05945088010001a1b818058d9010020581908882010010280f05819278440103105819000191b818058d91b019011350282b058190880108801000191081810818058011b019058190187510818058011b019048e11b818058d901001088010280f058192400d240320491d00019000180487510818058010c819058190487510818058010001904875108180580100019048b9
|2=>0x1081805801000192800f059450001a10044010010583100019018e11b818058d901002000190487510818058013084401181000c30581a1081b0580110044110000583101019000190280f058190880210904058010c8191081805819058010109d1301805865088020280f058190880208801000190580110044010012c8d90100202803058192b827059291b01901002100441081a0580108802050080581a
|3=>0x1019000190500b0880105831000191c80b08831000190588d1100001019000191a0270583100019088010280f0189d1301805865110000100101019058190100204875108180580135018059a51400208809060770001910818058010199d0282a0581908801010c1100440581a01001000190500b08801048e11b818058d9010020608f000191100001019011370282b058190880110044058190580101001
|4=>0x280f058190500b088010506b0500808801059450001a05008088011b81b058d91b019010023880f028810581901001088020280f01002058193780f059b90c81a00019200000881900019048b920000088191a00f0583100019018751081805801010e60583108831000190280f05819000191a00f0583100019278440580101031000191b8180500b0581905801088010280f0581910044010010188d11000
|5=>0x1081b08802058013e80b08981000c30581a010bb2000008819058192400d0491d0001900018200000881905819000192800f059450001a0280f088190581902803058191004408801010b92000008819100440280f058193d00b3c801088c10581a0500b088010280f058193a027059050c819088010280f05819298471400105819010450488d1100001019000193a00f059050c81905831278440103100019
|6=>0x1b1081805819048b920000088191b81b058d901002000190280f0581901001088014180b0282905819088014284418801010c10581a2b80f059291b019010021a027028010581941827028290581908801018750581910818058010487510818058011a027058310001927847010310581900019089fc05819012050001b01028088010c81908802058c918800010c10581a010e11b818058d9010020c819
|7=>0x100201a49028da010020581908880010010280f058190123e0581908a050001b0500b088011081805801060bb2000008819000191b81805819058d91a00f05831000191081805819058011081805801000194580f028a10581908809200000280f08819058191301405865088020581908809058190100108801088013c800088c10581a108180580110044010010001b0280f05819000191a00f0583140819
|8=>0x282905819088014d003088f905832000193780f059b90c81a0880205819059a514002088091a027058310001935019059a51400208809058190888d11000010191081805801000190487510818058010880205819050080880105a59060db010020001942844000c10581a0187510818058010001b1a02705831000192800f059450001a240320491d000190001804a1d3c800088c10581a048e11b818058d9
|9=>0x58010607700019108180580105819048751081805801018c918800010c10581a00019048751081805801088e31b818058d90100201001088090581a0880101075000191081805801088c918800010c10581a348c10581a140020280f058190881901019088010280f0100205819058190101910044010011081805801058190001910888010190580110a7f058010280005819088cb18800010c10581a41808
|10=>0x280f058191a00b05831000190280f058190001b11000010190001905a4108a060001b05832408190001b1c8030883100019011020881905819058310103100019050090581a088015501808819058450581910044010010282b058190880118802010c10581a1301a058650581910818058011b81b058d9010020280f14019058191a00f058310001905a953481a1400208809088da0280f058190187510818
|11=>0x58193481a1400208809088091081a058011a00b058310001908aeb5c818058020001a0500b088010888f11000010190581a010650880205819012050001b028a3058190880908865088020581a000c10581a048b9200000881908801000c10581a05abd0c81808802058a501032000191301b058650880259019550000584518803010c10581a00019010190580127847010310001905abf0c8180880201001
|12=>0x1401a088090280105819088090001b0581900019060db010020001900019058310101900019059291b01901002028db010020581962844600010580905a310501b08801011551081a05801058650c819088021081b058010030560018058090581901001088010580100019088090280f08819058195e0010280b0581908819058320001955030000190584508809010010880105832000190880108af10280b
|13=>0x10010c8c1088020581a058320883200019060db0100200019058190501b08801012e95c81805802100440581a010012f0471081b058012400d0491d000180123e08a050001b20000088190581905819050080880105b390501808801018751081805801058010c819088020611f00019000180580105819088091b0c1010020581a08b2f6001a05809013211401a0880902803058193c801088c10581a05b21
|14=>0x58011004401001013815501a058450581a0500b088011b019010022000208819058190894a000c10581a08802010020581a01b7105a060001b059050c8190880208b550588a010196c819058820100101ae5058020001b0280f0581908809010010101905819059060c819088026a8010588a010190881905819000190611f00019000180001910818058010597211003010190286708802058190288205819
|15=>0x180500b0581a08801058e605019088011b81a058d9010020001a0500808801050c30581a088011c80805019088010888d11000010190883205819000190001908b950101a010280880208801000771081805801088090581a0880105801408190001b05b8d1001a0100105945088010001a0581910047010011b818058d9010026c81a0588201001010021081805801058191004701001010190588201001
|16=>0x2864088020581905831408190001b0188d1100001019010020280f058190588d11000010191081a05801600330001905809010751081805801010191004401001058e608831000192c8090280305819010011b019010021c80808831000190123c08a050001b0c9b90c81a08802100440581a010015c81a058020001b058010500b08801000190891d00018058d90100205819058b920000088190491d00019
|17=>0x284705819028a1058190880901bdd1b018010021a00f0583100019058190100208801058190580108801013dd1b0180100204ae95c818058021004705819010010880105831000190101910018010010581a010010880105bcd1b01a01002058bb20000088190001911000010190581901002010010580102847058191081b058010880100019000c10581a058010001908801028030581904abd0c81808802
|18=>0x196000005801058090583108832000190100205832000190c945088020001a0506b0500808801088010280f05819010f90583200019058d90100200019088091081805801059b90c81a088020280f058190001905819088d9010021a00f0583100019000c10581a0887510818058017d80b550010584505801088320001905abd0c81808802000191004401001409450001b0001a05819088190101978002
|19=>0x88090288005819010011a0270583100019048751081805801058192000308819014130501a088010598908832000190280f058190880905801028000581905a9a1401908809059291b0190100205819140020880908981000c30581a100470581a010012800f059450001a0001920000088190880101001010c10581a108880101905801000190491d00018000190500b088011c80b0501908801010f905832
|20=>0x1b818058d90100208a7d028000581908bdd1b01801002058190c81908802000c10581a02866088020581901c35600020580905945010020001a088771081805801059060c8190880208bdf1b0180100284819108470580102881058190100101ae505802000190883105819000191a02705831000191400105819088090880102803058198380f55019058450100105819088093c800088c10581a1401905819
|21=>0x58010581a140020880918847010c10581a0581908802010023c809088c10581a0581901002058010611f00019000180580108831000190100205831000190580102800058191081b010020580108b8d1001a01001059a51400208809010020001905819058d9010021081a058010880110818058013481914002088091081b058010001908801010020581a058320001905a7d0280005819001b90c81a08802
|22=>0x5902088191b019010020c81a08802010320001901019000190580105845058320001908819010190100205801010020880155002058450146f0881a088190101a1004701001088090001a0888a010190586508802058320001901002010015c81805802012e505802012060001b001551081a0580105945088090001a0280f010020581901ae95c8180580201ae505802000190611f00019000180001910818
|23=>0x100200019600190580901001088091401908809000190881a10847058010891f000185501a058450001b0001a11000010192000308819059450001a0581a0880905a050001b0c8180880214002088090581908801089450001a0581900019000c30581a088190580102847058190146d0881a1401a088090491d000180103200019010190584510018010015500b05845058010001b5c81905802088d901002
|24=>0x280f05819088190584505809058450111d0001810044010010101905819088190880110847058010583100019003970101a1b01a010025500105845058190580105831000191081b058015501b058450c8190880205882010010883100019408190001b088010001a058020001905801000190501a088010591d000180046d0881a1081a058010580108809088190001a05019088010011f000181400108809
|25=>0x1450001a0191d000181081805801408190001b01ae5058020100108801058190001b0881901019012050001b0100205819000190001802803058195c81a058020280005819100440100105b950101a6001805809058010880105802000190580100019088c10581a60000058090146d0881a000190880955003058450500b088010581a088010880201002058a1088090101900019058d9010020590208819
|26=>0x584508801000190580205801088090581a000180001b0001a0100205819010190101a0001b0001a000c10581a05a060001b010020581a0591f0001801ae505802000190001805819088090280f0581910047010010001905845058020001b058010001b0111d0001800019088010580205801010020001a05a050001b0501b088010591d00018
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x948119021203e4000000000000000074800000000364064800001720000054800000000000000009541028000036a00000000000000000000000000000000000b280000000000000001240000000007200000000000004a8000000000000228004000000000000000000000000000000
|6,1=>0xb68000000005740a6800002728000
|7,0=>0x21e642d0850906420483f907d20f731e6800007818ee21d6639d071a00001be800006da0d74000034d06818cc4190800006220c0417a600005d18b6416482b90552000014e628d0501800013a6268c4b209240000239045208641066000000007f4000000003e187840e881c1036206930ca8000031185f3
|7,1=>0x3b6875d0e9a1cf4000072d0e3a1c3437e86f84dd21b6436486b90d52000034c868cccfa00003368660cca9991431a86250000185430285f50bca17542e285b50b5196732c865810ae995942aa8548ca798000296851d00000000288650109e2139326a84c5096a129424c648cc8fa11c3232600008aa1123
|7,2=>0xa30c000289350a8a08d3f9a7b44ee89cd137a26b44ce898d12fa25c34b08951128224d34928915120a000047a88e511aa000046288b8d15222644466880d0e221840000854d091a0e4416681d101a000000007fd0000000000007ed0fba00003e687bd0f5a1e833ca6788cef98000
|8,0=>0x68c6d109a09b3e36766ce0d9a9b3416626cb8d959b28364a6c88d8f9b1d26346c5cd8a1b11361c6c2cd841b0536046bfcd7e1af935ec6bccd781aed35d46b9cd721ae135be4b70d6c9ad635a66b40d669aca358e6b10d609abe35766ae0d5a9ab2355e6ab0d549aa635466a80d4e9a9a352e6a549491a8f3
|8,1=>0x80a7008dff9bfc37f26fd8df99bf037da6fa8df39be437c26f78ded9bd837aa6f48de79bcc37926f18de19bc0377a6ee8ddb9bb527646ebcdd61ba9374c6e8cdd01b9d37346e5cdca1b91371c6e2cdc41b8537046dfcdbe1b7936ec6dccdb81b6d36d46d9cdb21b6136bc6d6cdac1b5536a46d3cda61b493
|8,2=>0x97e72f0e5c9cb6396672c0e569caa394e7290e509c9e39367260e4b149339207234e451c8739087204e3f1c7b38f071d4e391c6f38d871a4e331c6338c07174e2d1c5738a87144e271c4b38943120a229c43288070f4e1d1c37386870c4e17942c38527098e119c20383a7068e0b9c1438227038e059c083
|8,3=>0xaf275d8eb99d703ada75a8eb39d643ac27578ead9d592aac7550aa89d4e3a967520ea315433a8074f4e9d1d373a6874c8a979d2c3a527498e919d203a3a7468e8b9d143a227438e859d083a0a7408e7f9cfc39f273d8e799cf039da73a8e739ce439c27378e6d9cd839aa73506689cce39967320e629cc23
|8,4=>0xb227638ec59d883b0a7608ebf9d7c3
|9,0=>0xc245840b07160c2c145820b0316042c045800aff15fc2bf457e0afb15f42be457c0af715ec2bd457a0af315e42bc45780aef15dc2bb45760aeb15d42ba45740ae715cc2b945720ae315c42b845700adf15bc2b7456e0adb15b42b6456c0ad715ac2b5456a0ad315a42b445680acf159c2b345660acb15942
|9,1=>0xd245a40b47168c2d145a20b4316842d045a00b3f167c2cf459e0b3b16742ce459c0b37166c2cd459a0b3316642cc45980b2f165c2cb45960b2b16542ca45940b27164c2c945920b2316442c845900b1f163c2c7458e0b1b16342c6458c0b17162c2c5458a0b1316242c445880b0f161c2c345860b0b16142
|9,2=>0x35316a42d445a80b4f169c2d345a60b4b16942
|10,0=>0x35a8eb41d663ac87588eb01d5e3ab87568eac1d563aa87548ea81
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x12a0000000002180000000004200000000008200000000010000000000017c0000000002c80000000004a0000000000920000000001200000000002080000000003100000000004800000000007c0000000000e00000000001900000000002a00000000004c0000000000880000000001000000000001e0000000000380000000000600000000000b0000000000140000000000200000000000280000000000400000000000600000000000800000000000800000000000
|1=>0x20040000000040040000000080000000000097f0000000012800000000022200000000042f80000000085d00000000102200000000202c00000000400800000000421000000000832000000001014000000001e88000000001df00000000030e000000000618000000000ad80000000014a00000000027e00000000044c0000000008580000000010a00000000020e00000000040c000000000810000000001010000000001900000000003000000000005200000000009d
|2=>0x2000400000003d0fc00000007a0f80000000f40f00000000c83e00000001000400000000c2f80000000180a00000000280600000000477c000000008e980000000119f00000000230c0000000044fc0000000088f80000000110600000000220600000000437c0000000085f80000000109f00000000210800000000417c0000000082880000000103f00000000207600000000407c0000000080980000000101200000000202200000000404000000000804000000001004
|3=>0x400940000000801240000001002400000002000800000004000e0000000447fc000000088ef80000001119f00000002233200000004457c0000000887f8000000110df00000002217600000004427c0000000882f80000001101f00000002203a0000000407fc000000080ef8000000101bf0000000202be000000040428000000080840000000101030000000201be00000004017c0000000800f80000001001d00000002001600000004002400000008003800000010004
|4=>0x10103e0000002006000000004008180000008001d0000000a33be00000014626c00000028c0f80000005111f0000000a20be00000014415c0000002880f80000005081f0000000a103a00000014027c0000002802b80000004185f0000000820be00000010257c0000002042f80000003105f00000006003e00000008437c0000001082f8000000210480000000412be00000008217c0000001040700000002010b0000000400fe0000000801e40000001003480000002005f
|5=>0x3223be00000060427c000000c08070000001810020000002a31be00000054277c000000a042f80000012085f0000002231be00000044477c0000008886f8000001110db0000002203be000000406028000000808af80000010101f0000002012fe00000040217c0000008040780000010080b000000201006000000400618000000800bf80000010013f00000020020c0000004002940000006084f8000000b181f0000001610be00000028617c0000005040f8000000a000a
|6=>0x120233e00000240427c0000048004b8000008811bf00000110213e0000022006fc000004400cf80000088009f0000010830be0000020065fc00000400caf80000080185f00000100233e00000200457c0000040084f80000080105f0000010020a600000200217c000004000db80000080019f0000010002fe0000020004fc0000040003f800000800002000000c000be000001044f7c000002088ef80000041105f0000008007be00000100077c000001008468000001e101f
|7=>0x310037e00000610657c00000c208ef80000182007f00000230213e0000044c417c0000087800f8000010d009f0000021811be00000430217c0000084886f80000108119f00000210213e000004204254000008400cf80000104185f00000208233e00000410457c0000082086f80000104105b0000020820ae00000410407c000008208050000010410060000020800be00000410003c0000082000700000104000700000200213e00000400417c0000080000700000098109f
|8=>0x4000221fe0008000442fc0010000288f800200001803000400002a2e00080000457c0010000089f80020000111f00040000207e00080000404c001000000cf8002000001870004000000b60008000000ac0010000000c80018000103f00030000203e00040014407c000800088ef80010001105f00008000262c00008000000400008008a4c80000c01108f00000610213e00000840407c000010408df8000020000d700000330013e00000630617c00000c508af80000188119f
|9=>0x100110233e00200200427c004000c08cf80080010119f0010000223be0020000444180040000886f80080000118400100000030a00200000060c004000000088008000000000008010020fe0010001061fc002000088840004000101bd00080002033e001000040024002000000a180040000000f00040610217e0008026042fc001004008bf80020018049f00040020207e0008000841fc001000100158002000111ff0004000223be00080004474c001000088cf800200011103
|10=>0x8100010233e10200020067c202000084ef84040000005f0800021812fe10000008217c2000000082f82000001109f0400000030be0800000000200910000089f81200002101e02400000223e04800000407c0900000080f00a80100109f00a0000a00be00c20004437c018000080ef80200000121f00400000243c00800000447c008400088ef8010100116df0020000221be00400004077c004010400cf8008018c095f0010030810be0020042407fc004008400df8008010400df
|11=>0x20010000288fa000006110df20000100212a4000000002104100000080f0408018c19df
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x30000006048006200000000000020180c02000000000020000004030000800030000000000501c001b8000000000000000000000600000000006000000c00000006800000000206000000000000000000
|7,0=>0x642c1a0b003c8343e1f06c0669048341e000601a1400880180c03019900043248901a03618c80c060b3000c0d04810f80001c200000020641802008901809020098e06020001a060301c441508c241a023b8000c3d0200c82004f8007e0c000e00441100013817020000c1922170de000b0380c0002010920500060665a0b000005f000003a012380c063a068019023
|7,1=>0x180006008180c0e2f108b60d42b3c32060482406060d1141a000687018001a8101a03030100601000580c3e0230982000015c000000030060001c10c006020180800
|8,0=>0x39ced84bd78930e4b0263ea6cee329d1412247cddd89a832d1c890333a9d625133441547153f15149aa470ecca8a1e4e8d209aa4802e31274e24a663192f1b264f21f3a3ca0498462c819e64a41482b09e89c449a399eb40a07dac82cff616714ebea19c50d18880c1c12c7174cb4b2610b590967116140f3576b388e11264d2cf26b27d8e582d5e3cd58f348010906c
|8,1=>0x7802d4b2e1829c207a98a3d165f31819baa42ab84fa753b1ca7295341f4d74f14ac0a0706c23a9c268eaac43503daf90927b29745e4c6cc963e878a8d8e8e8a64d1ea906ab152ced164c26a283b236a2cb352284f4b7252aad3ea0078e27136b9a503c8754c16a64cb115a1f483964274338219a2e1dd89547d621c62d48891e43b5c681645d3349930e476591c52279
|8,2=>0x271faa30ca38c08c58
|9,0=>0x9f9e6489b5a9b8f0795f1e4f30d231d28cf6923f5771e2b45ce91f574a6b2b3919e60f5d7f226bce770196b4d736416a4f3ad9e4351a79bfe30b64c504a5192957ce2af6f1e57f232938cf4d32320e00fb3cae0e53243289beda3b38cf2b76dc65127a38a8e55008c9d1b92b779298ad4b02c689233cbe1e8953b35daada28c0a5ef9a115202b944c08d6524a1d17472
|9,1=>0xf2463c9c8e94d3cc9aaaf7
|10,0=>0x28b03231b45680231e4e8514945daed2
|11,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 47 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_222 9 roots_222 ops++addP pm 2 dom_238 9 roots_238 ops++addP pm 3 dom_252 9 roots_252 ops++addP pm 4 dom_246 10 roots_246 ops++addP pm 5 dzo_222_32 7 roots_222 ops++addP pm 6 dzo_188_2 6 roots_188 ops++addP pm 7 dzo_174_16 6 roots_174 ops++addP pm 8 dzo_94_32 6 roots_94 ops++addP pm 9 dzo_122_4 6 roots_122 ops++addP pm 10 dzo_90_4 5 roots_90 ops++addP pm 11 dzo_252_2 7 roots_252 ops++addP pm 12 dom_126 8 roots_126 ops++addP pm 13 dom_118 6 roots_118 ops++addP pm 14 dzo_86_32 5 roots_86 ops++addP pm 15 dom_214 7 roots_214 ops++addP pm 16 dom_190 7 roots_190 ops++addP pm 17 dom_236 7 roots_236 ops++addP pm 18 dzo_236_2 6 roots_236 ops++addP pm 19 dzo_238_16 7 roots_238 ops++addP pm 20 dom_172 5 roots_172 ops++addP pm 21 dzo_166_16 5 roots_166 ops++addP pm 22 dom_182 6 roots_182 ops++addP pm 23 dzo_172_2 5 roots_172 ops++addP pm 24 dzo_236_16 6 roots_236 ops++addP pm 25 dzo_172_16 5 roots_172 ops++addP pm 26 dzo_180_2 5 roots_180 ops++addP pm 27 dom_244 7 roots_244 ops++addP pm 28 dom_248 7 roots_248 ops++addP pm 29 dzo_230_16 6 roots_230 ops++addP pm 30 dzo_90_32 5 roots_90 ops++addP pm 31 dom_218 8 roots_218 ops++addP pm 32 dom_122 7 roots_122 ops++addP pm 33 dom_90 5 roots_90 ops++addP pm 34 dom_220 6 roots_220 ops++addP pm 35 dom_206 6 roots_206 ops++addP pm 36 dom_186 6 roots_186 ops++addP pm 37 dzo_218_4 6 roots_218 ops++addP pm 38 dzo_248_2 6 roots_248 ops++addP pm 39 dzo_234_16 6 roots_234 ops++addP pm 40 dzo_218_32 6 roots_218 ops++addP pm 41 dom_124 5 roots_124 ops++addP pm 42 dom_204 5 roots_204 ops++addP pm 43 dom_234 7 roots_234 ops++addP pm 44 dom_110 5 roots_110 ops++addP pm 45 dom_230 7 roots_230 ops++addP pm 46 dzo_214_32 6 roots_214 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_222_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_188_2_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_174_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_94_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_122_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_90_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_252_2_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_236_2_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_238_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_166_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_172_2_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_zo_236_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_172_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_180_2_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_zo_230_16_164 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_zo_218_4_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_zo_248_2_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_234_16_168 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_zo_218_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_zo_214_32_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 72 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 187 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 59 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 187 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 264 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 264 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 138 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 10 128 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 138 → Z 9 i = true := (range_split z9_0 z9_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000ccc800000000000000000000ccc800008800
def gsh_173_2:=0x33330000333200000000000000000000333200002200
theorem lowS_zo_173_2_173:Lower true dzo_173_2 roots_173 gzo_173_2 8:=lower_iso_b (d1:=dom_173) (r1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (lower_slice_b (T:=gsh_173_2) [] (by decide +kernel) lowS_173)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000fffe00000000000000000000fffe0000eeee0000
def gsh_175_16:=0xffff0000fffe00000000000000000000fffe0000eeee
theorem lowS_zo_175_16_172:Lower true dzo_175_16 roots_175 gzo_175_16 7:=lower_iso_b (d1:=dom_175) (r1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (lower_slice_b (T:=gsh_175_16) [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa,0,1),(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2)] (by decide +kernel) lowS_172)
def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccc8ccccccccccccccccccccccc8cccc8800
def gsh_253_2:=0x3333333333333333333333333333333233333333333333333333333233332200
theorem lowS_zo_253_2_173:Lower true dzo_253_2 roots_253 gzo_253_2 10:=lower_iso_b (d1:=dom_253) (r1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (lower_slice_b (T:=gsh_253_2) [(0x3333000033330000333300003333000033330000333300003333000033330000,0,16),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64)] (by decide +kernel) lowS_173)
def dzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def gzo_237_2:=0xcccc0000cccc0000cccc0000ccc80000cccc0000cccc0000ccc800008800
def gsh_237_2:=0x333300003333000033330000333200003333000033330000333200002200
theorem lowS_zo_237_2_173:Lower true dzo_237_2 roots_237 gzo_237_2 9:=lower_iso_b (d1:=dom_237) (r1:=roots_237) (T1:=gsh_237_2) [(dom_237,2)] (by decide +kernel) (lower_slice_b (T:=gsh_237_2) [(0x333300003333000000000000000000003333000033330000000000000000,0,64)] (by decide +kernel) lowS_173)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000e0e0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000e0e0a00
theorem lowS_zo_219_4_91:Lower true dzo_219_4 roots_219 gzo_219_4 8:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (lower_slice_b (T:=gsh_219_4) [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_91)
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0a00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0a
theorem lowS_zo_219_32_82:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffefffa00000000
def gsh_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffefffa
theorem lowS_zo_223_32_82:Lower true dzo_223_32 roots_223 gzo_223_32 8:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8),(0xffffffff00000000ffffffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffefffa00000000
def gsh_95_32:=0xfffffffe00000000fffefffa
theorem lowS_zo_95_32_82:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_82)
def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0f0f0e000000000e0e0a000
def gsh_91_4:=0xf0f0f0e000000000e0e0a00
theorem lowS_zo_91_4_91:Lower true dzo_91_4 roots_91 gzo_91_4 7:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (lower_slice_b (T:=gsh_91_4) [] (by decide +kernel) lowS_91)
def dzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def gzo_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000a000
def gsh_235_4:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0e00000f0f00000a00
theorem lowS_zo_235_4_75:Lower true dzo_235_4 roots_235 gzo_235_4 7:=lower_iso_b (d1:=dom_235) (r1:=roots_235) (T1:=gsh_235_4) [(dom_235,4)] (by decide +kernel) (lower_slice_b (T:=gsh_235_4) [(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000000,0,32),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
def dzo_239_16:=0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def gzo_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000eeee0000
def gsh_239_16:=0xffff0000ffff0000ffff0000fffe0000ffff0000ffff0000fffe0000eeee
theorem lowS_zo_239_16_172:Lower true dzo_239_16 roots_239 gzo_239_16 8:=lower_iso_b (d1:=dom_239) (r1:=roots_239) (T1:=gsh_239_16) [(dom_239,16)] (by decide +kernel) (lower_slice_b (T:=gsh_239_16) [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,0,1),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,0,2),(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_172)
def dzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0e0e0a000
def gsh_251_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0f0f0f0f0e0e0a00
theorem lowS_zo_251_4_91:Lower true dzo_251_4 roots_251 gzo_251_4 9:=lower_iso_b (d1:=dom_251) (r1:=roots_251) (T1:=gsh_251_4) [(dom_251,4)] (by decide +kernel) (lower_slice_b (T:=gsh_251_4) [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,0,32),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_91)
def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0
def gzo_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000a000
def gsh_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000a00
theorem lowS_zo_203_4_75:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso_b (d1:=dom_203) (r1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (lower_slice_b (T:=gsh_203_4) [(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_75)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(3,131),(4,36),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,17),(16,18),(16,80),(20,21),(20,22),(20,52),(20,84),(20,148),(24,25),(24,26),(24,56),(24,88),(24,152),(28,29),(28,30),(28,60),(28,92),(28,156),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(64,192),(68,69),(68,70),(68,76),(68,84),(68,100),(68,196),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,132),(128,136),(128,160),(128,192),(130,131),(130,134),(130,138),(130,146),(130,162),(130,194),(144,145),(144,146),(144,148),(144,152),(144,176),(144,208)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|8=>1
|9=>19
|10=>50
|11=>32
|12=>6
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|8,0=>0xb73f9
|9,0=>0xfe2d7f633cf5348d4de4d236fc0df9bd4e2ba183a33b4948898d61a8bb2a7dc9975d905f142594531a62f0de0404895
|10,0=>0xfe595f3e8eeb385db214da826d6871cf14bcee02c6417c0ad7bf7a1bd0a2b158aaa914a82ffa8215a7754a5a919f5eb9f4339cd929c1349b68497842942178e23284dcf82b377cb2d5c02a532ea52cb54bba74008f3ce9b3c85f36d1a2f51d2ab05259e223e8f1f85b1b3c419bb718b66177ea142b90dbe1058f1027cb
|11,0=>0xf7f3ef2f5ced241ecb32d8230d2767c3e3fc1893b4102b2e999d9fc9c8c79b4f297a63975d28501a7e9c37c24273cc6732c86c4d75cbf958c9947d6c433cd31fd228a2e18846092f707de905d8e01f4c
|12,0=>0xdd9d2c33a39892d8fd7c792e40eef7
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffffffffffffffff00000000ffff0000ffff0000ffff000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
|0,1=>0xffff0000ffff00000000000000000000ffff00000000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff00000000000000000000ffffffffffffffff0000000000000000ffff0000ffff00000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0000ffffffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f000000000000ffff0000ffff00000f0f00000f0f0000ffff0000ffff00000f0f00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff000000003333333333333333333300003333000033333333333333333333000033330000
|0,2=>0xffff0000ffff0000ffff00000000000000000000000000000000ffffffff000000000000000000000000ffff000000000000000000000000000000000000ffffffffffffffffffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffffffff000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff00000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000000000000000ffff000000000000ffff000000000000ffff0000000000000000ffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff00000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000
|0,3=>0xffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0f0fffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff000000000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x813d62472881020582475ca2040813c91ca4c40c205624728810140f24728b10308158024a4c810204d24718510308124728b20408134024a20510308100a2040813d424738a4c810204d24744a2040503c91ce28b2040813402461440c2040
|1=>0x28b2040817491e02881030812472881020553c91d12922040813c91ca2040c205f24778c2040c20491c630810308100778a2040817491ce28810204f24728810205a2472992040813c91ca20408135624718c2c40c20402881020580091ca204
|2=>0x10204f24730a2c810308100c2881030815891ca2040c206624730a2040813491ce28810204d0091ce2881030815891ca2040c20642472881030812631ce28810204d24788a2c40c20491d12881030815891ca2051030812475d1288103081247
|3=>0x288103081247288103081bc91ca2040813491cc2932040c20401ca2040c206e2472922040813c91c628b103081009b0a2040c20491eb28810308124718c2c40c20491cc2040c20652472a92040c20491de28810204f2472881030819c91cc448
|4=>0x1030819491d128810305024770a2040c20491ca2040817491cad4810204f247cca2040c20491ce2932040c20491f2288103081247288103081c091ca2040c20560091ce28b2040c20402572881030810091ca2040813402472881030815891d7
|5=>0xc20491ca2040813c91cc4481030812473912881030812472932040c204024718c2040c20491ca4c810308124730a2c810308124728b2040c204024a2040c20682472a12040c20491d12922040c20491ce2881030810091c628b103081247288
|6=>0x491c62881030810091ca48b10308124730a2040c20401ca2040c2071247b4a2040c20491de28b2040c20491ce30a2040c20491ca21b10308124728810308126a1ca2040c2049d0788c28810308124728810305024778a2040c20491ca4cb204
|7=>0x28810308124744a2040c20491c628810308124728b2040c20491ca4881030812472881030810091cc28810308124779128810308124738a2040c20491d128810204f24788a2040c2
|_=>0
def sO:Nat→Nat→Nat
|8,0=>7
|9,0=>0xa68276494923208391ea47281a6460916204f911a43e80d642d809241aa046407a
|10,0=>0x9c2667997e2569936643a8ea631989ea1da84ea0a98065f897be5e787769d4972e5c296e65b0969e59e965658c960e57a95c6567a57a555952e941a4e252f949a51d944e90a94028f793ba4e5936e8d293264c092de4ae9
|11,0=>0xe62b8f9e1a77d9dceb6a9d867589d3e745aceeb329ca67209c5ab0e8c166fbabce2ea9b82ad6ab366c49aeaab19aa269f9a56a8baa0a6799
|12,0=>0xf3e7c69ef67b49eae7a29
|13,0=>0x3d88
|_,_=>0
def wAt:=mkWire dB 54 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2934801247510f388d125287570f3885125287510f45248252874801388ca01247510f482c8252874e232074a012474e0f28048012474a2130b0a252074e0f2074a01247491d30b0a2520748563c9510f2874801383ca01247510f482c825287481d383ca012474a212474c2c289481d
|1=>0x448ca1d1808a212474e0f4494a1d29248252074e234494a1d30b0a2520751492094a1d783ca2d2076121449ca1d3c9510f287510f2094a1d452c825287461d2884a252474a212895e0f4484a1d443d1252875c0f29b4b27207523d443c8252874e0f388d1252874a252074a21247570f
|2=>0x38851252874c2f289481d383d1252874a25200491d30b8a25207510f2094a1d2074a212476d21307ca25887ca49209481d2884a25448ca2528748a9280891d443d121287681d308ca25443ca25287491d289481d388cc1d2894a4e2c9481d383cc1d2894e0f280491d388d1252876525
|3=>0x287512528748012474a212894b252074a25207491d2074c23289512728748252874a012474a212075123287520b2094a1d29b4b272075e0f4484a1d20f510f2874ad1200891d28048012475e274484a1dc494a2e2074e23280491d2074a012474a4d200491d383ca012474e234494a1d
|4=>0xa1d288481d209491d28951212875125287510f2874a492094a2124748252074a252474a2e2074c1f2894a2d2074c1d2894b272074a0224748022474c21289520b20951212874b25207510f2874a25
|_=>0
def oO:Nat→Nat→Nat
|8,0=>5
|9,0=>0x135092845420a0f5072835418a0b5052825410a075032815408a0350128054
|10,0=>0x1c86e136f1b6cdb06d53691b3cd986c93631b0cd806bd35d1adcd686b13571aacd506a53511a7cd3869934b1a4cd2068d3451a1cd0868133f19eccf067533919bccd8669333198ccc065d32d195cca86513
|11,0=>0x92948ca4251f28e946ca3251728a944ca2250f286942ca12507282940ca024ff27e93ec9f24f727a93cc9e24ef27693ac9d24e72
|12,0=>0x25832b1950ca46503271
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 13
def pmP:Nat→Nat
|0=>0xc02a6c00104a9f00040ea7c00100adf000402a7c000c0a9f000302a740003fa9f0000f6a7c00023a9f000086a7c0001ffbf00007eafc00008b9f000022afc00004b9f000012a7c00003fbf00000ebfc00003adf00000abfc00002adf00000aafc00002a9f000006a7c00000b9f000002b7c00000abf000002a7c000007b40000003fc00000000
|1=>0x100006b7c40000a9f0a2072a7c1020ca9f02240aafc08900abf02200aefc08800a9f02040aa7c08100a9f01240aefc04900bbf012002e6c0280caff00840befc02023aff008086afc0200861600800befc02002abf006022a6c00904b9f002402e7c00808a9f002012a7c00802bbf00200aafc00801adf002002efc00800aff002002a7c0040fa9b
|2=>0xc40c02a7d00300a9f322406b7ca0028adf222006f7c80d01bdf202006f7c6000caff120486a7c40021bdf10007ea7c4000caff100016a7c40001aff
|_=>0
def pmB:Nat→Nat→Nat
|8,0=>1
|9,0=>0xde381a71983565cd074014e893eb8c82
|10,0=>0xd156d34414421d60e94dd0a808d89873c308be809c44808d18257ce98a50c21dc2420dec50d31512482e5b5
|11,0=>0x92994c615056070911307102191a8f0cda372611435e5820620b5f86
|12,0=>0x3050e3c404
|13,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 34 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_253 12 roots_253 ops++addP pm 2 dom_251 12 roots_251 ops++addP pm 3 dom_247 12 roots_247 ops++addP pm 4 dom_239 11 roots_239 ops++addP pm 5 dom_159 8 roots_159 ops++addP pm 6 dom_207 9 roots_207 ops++addP pm 7 dom_191 11 roots_191 ops++addP pm 8 dom_91 7 roots_91 ops++addP pm 9 dom_223 11 roots_223 ops++addP pm 10 dom_27 4 roots_27 ops++addP pm 11 dom_127 11 roots_127 ops++addP pm 12 dom_111 8 roots_111 ops++addP pm 13 dom_63 8 roots_63 ops++addP pm 14 dom_173 8 roots_173 ops++addP pm 15 dzo_173_2 8 roots_173 ops++addP pm 16 dom_45 5 roots_45 ops++addP pm 17 dzo_175_16 7 roots_175 ops++addP pm 18 dzo_253_2 10 roots_253 ops++addP pm 19 dzo_237_2 9 roots_237 ops++addP pm 20 dzo_219_4 8 roots_219 ops++addP pm 21 dzo_219_32 7 roots_219 ops++addP pm 22 dom_235 10 roots_235 ops++addP pm 23 dzo_223_32 8 roots_223 ops++addP pm 24 dom_169 7 roots_169 ops++addP pm 25 dzo_95_32 7 roots_95 ops++addP pm 26 dom_187 10 roots_187 ops++addP pm 27 dzo_91_4 7 roots_91 ops++addP pm 28 dzo_235_4 7 roots_235 ops++addP pm 29 dom_141 5 roots_141 ops++addP pm 30 dzo_239_16 8 roots_239 ops++addP pm 31 dom_75 5 roots_75 ops++addP pm 32 dzo_251_4 9 roots_251 ops++addP pm 33 dzo_203_4 6 roots_203 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_173_2_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_175_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_253_2_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_237_2_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_219_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_219_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_223_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_zo_95_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_zo_91_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_zo_235_4_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_239_16_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_zo_251_4_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 19 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 50 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 32 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 32 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 6 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 6 0 = true)
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
  · exact z8 i (Nat.zero_le i) hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 6] }, { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.or, inputs := [3, 7] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [3, 2] }, { op := GateOp.or, inputs := [12, 0] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [10, 9] }, { op := GateOp.and, inputs := [14, 13] }, { op := GateOp.and, inputs := [8, 4] }, { op := GateOp.and, inputs := [11, 15] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51684_aux

theorem PEqualNP.Outside.L_meta_51684 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51684_aux.main
