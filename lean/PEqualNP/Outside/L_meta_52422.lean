import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52422_aux
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
def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeeeefcfc0000fefeeeeefcfc0000fefeeeeefcfc0000fefeeeeefcfc0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffaffaafaf0aa00fffaffaafaf0aa00fffaffaafaf0aa00fffaffaafaf0aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000fffcffccfcfc0000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00fffeffeefefcaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffaaaaffffaaaacccc0000cccc0000ffffaaaaffffaaaacccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafaf0f00000f0f00000fffffafafffffafaf0f00000f0f00000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffff0f0fffff0f0fcfc0000fcfc0000fffff0f0fffff0f0fcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffafafffffafafcfc0000fcfc0000fffffafafffffafafcfc0000fcfc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaa00aa00aa00aa00ffffffaaffffffaaaa00aa00aa00aa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffff00ffffff00cccc0000cccc0000ffffff00ffffff00cccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffaaffffffaaeeccaa00eeccaa00ffffffaaffffffaaeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafaf0aa00faf0aa00fffffffafffffffafaf0aa00faf0aa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffff0fffffff0fcfc0000fcfc0000fffffff0fffffff0fcfc0000fcfc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffafffffffafefcaa00fefcaa00fffffffafffffffafefcaa00fefcaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafaaaaaaaaa00000000fafafafafafafafaaaaaaaaa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefafafafaeeeeeeee00000000fefefefefafafafaeeeeeeee00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccff00ff00ffccffcc00000000ffccffccff00ff00ffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffaaffaaffeeffeeaa00aa00ffeeffeeffaaffaaffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0fff0fff0ff00ff0000000000fff0fff0fff0fff0ff00ff0000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffaffaaffaaaa00aa00fffafffafffafffaffaaffaaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfff0fff0ffccffcc00000000fffcfffcfff0fff0ffccffcc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffafffaffeeffeeaa00aa00fffefffefffafffaffeeffeeaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaa00000000ffffaaaaffffaaaaaaaaaaaa00000000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffff0000cccccccccccc0000ffffccccffff0000cccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffaaaaeeeeeeeecccc0000ffffeeeeffffaaaaeeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafaaaaaf0f00000fffffafafffffafafafaaaaaf0f00000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffff0f0fcfcccccfcfc0000fffffcfcfffff0f0fcfcccccfcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffafafefeeeeefcfc0000fffffefefffffafafefeeeeefcfc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaa00aa00ffffffaaffffffaaffaaffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffff00ffccffcccccc0000ffffffccffffff00ffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffaaffeeffeeeeccaa00ffffffeeffffffaaffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0ff00f0f00000fffffff0fffffff0fff0ff00f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffaffaafaf0aa00fffffffafffffffafffaffaafaf0aa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffff0fffcffccfcfc0000fffffffcfffffff0fffcffccfcfc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffafffeffeefefcaa00fffffffefffffffafffeffeefefcaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeecccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaf0f00000f0f00000f0f00000f0f00000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000fcfc0000fcfc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefcfc0000fcfc0000fcfc0000fcfc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_156 : Nat := 0x1111111100000000000000000000000011111111
def goal_156 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
def roots_156 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffafaf0aa00faf0aa00faf0aa00faf0aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfafafafafafafafafafafafafafafafaaaaaaaaa00000000aaaaaaaa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccccccc00000000cccccccc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefefefefefefefefefefefefeeeeeeeee00000000eeeeeeee00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffafffafffafffafffafffafffafffaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffafafffffafafffffafafffffafafafaaaaaf0f00000fafaaaaaf0f00000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcccccfcfc0000fcfcccccfcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefefffffefefffffefefffffefefefeeeeefcfc0000fefeeeeefcfc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffafffffffafffffffafffffffafffaffaafaf0aa00fffaffaafaf0aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffefffffffefffffffefffffffefffeffeefefcaa00fffeffeefefcaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011
def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffaaffaaffaaffaaaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa0000000000000000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffff0000ffff0000cccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffaaaaffffaaaacccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafaf0f00000f0f00000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffff0f0fffff0f0fcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefffffafafffffafafcfc0000fcfc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffffccffffffccffffff00ffffff00cccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffaaffffffaaeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafaf0aa00faf0aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffefffffffefffffffafffffffafefcaa00fefcaa00
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

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafaaaaaaaaa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefefefefefefefefefafafafaeeeeeeee00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffeeffeeffeeffeeffaaffaaffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0ff00ff0000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffafffafffafffafffafffafffafffaffaaffaaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffefffefffefffefffefffefffafffaffeeffeeaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaa00000000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffff0000cccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffaaaaeeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffafafffffafafffffafafffffafafafaaaaaf0f00000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffff0f0fcfcccccfcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffefefffffefefffffefefffffafafefeeeeefcfc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffccffffffccffffffccffffff00ffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffeeffffffeeffffffeeffffffaaffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffafffffffafffffffafffffffafffaffaafaf0aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffcfffffffcfffffffcfffffff0fffcffccfcfc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffefffffffefffffffefffffffafffeffeefefcaa00
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
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_137:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32)]
theorem lowS_137:Lower true dom_137 roots_137 goal_137 4:=lower_iso_b isoMvS_137 (by decide +kernel) lowS_41
def isoMvS_146:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_146:Lower true dom_146 roots_146 goal_146 4:=lower_iso_b isoMvS_146 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_193:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_193:Lower true dom_193 roots_193 goal_193 4:=lower_iso_b isoMvS_193 (by decide +kernel) lowS_41
def isoMvS_196:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_196:Lower true dom_196 roots_196 goal_196 4:=lower_iso_b isoMvS_196 (by decide +kernel) lowS_41
def isoMvS_200:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_200:Lower true dom_200 roots_200 goal_200 4:=lower_iso_b isoMvS_200 (by decide +kernel) lowS_41
def isoMvS_208:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_208:Lower true dom_208 roots_208 goal_208 4:=lower_iso_b isoMvS_208 (by decide +kernel) lowS_41
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,32,34)] (by decide +kernel) lowS_41
namespace S_51
def pG:List (Nat×Nat):=[(1,33),(2,18),(2,34),(3,19),(3,35),(16,18),(17,19),(17,49),(32,33),(32,34),(48,49),(48,50)]
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
def symsG:List (List (Nat×Nat)):=[[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
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
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_slice_b [(0x303000000000000030300000000,1,33)] (by decide +kernel) lowS_73
namespace S_201
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(8,9),(8,72),(8,136),(64,65),(64,72),(64,192),(128,129),(128,136),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_201.map (·&&&dom_201)
def gM:=goal_201&&&dom_201
def NN:Nat→Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x64b4b1903600d53
|4,0=>0x69260381401ea121ad4610232048c0
|5,0=>0x462633e64c01756
|6,0=>0x46263
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c000000000000080b03000000000000030300000000000003000000000000000300c080000000000000c080000000000000c080000000000000c0b0300000000000003030000000000000303000000000000020200c000000000000000c000000000000000c000000000000000303000000000000020200000000000003030000000000000202c0c0000000000000c0c0000000000000808000000000000080b03000000000000030300000000000003030000000000000000c0c00000000000000000000000000000c0800000000000000030300000000000003030000000000000000000000000000000000000000000000000000000000000000c0c0000000000000c0b0000000000000003000000000000000300000000000000030080800000000000008080000000000000808000000000000080b03000000000000000000000000000003030000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2104210421604271042d104c216028704b27042a10421094287621543210
|_=>0
def sO:Nat→Nat→Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x344bd6a5
|6,0=>0x384
|_,_=>0
def wAt:=mkWire dB 14 202 0x3ffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4045124501414412150504505
|_=>0
def oO:Nat→Nat→Nat
|3,0=>0x20000
|4,0=>0x6242220000
|5,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfcba630
|_=>0
def pmB:Nat→Nat→Nat
|3,0=>0x40
|4,0=>0x3540
|5,0=>0x136
|6,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 4 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_200 4 roots_200 ops++addP pm 1 dom_137 4 roots_137 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dom_193 4 roots_193 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_201 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_193 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_200 4 s (0,roots_200.map (·&&&dom_200)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_201 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_200 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_201==dom_201)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_201 gM v ys):RunD true dom_201 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_201 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_201 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_201 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_201 roots_201 goal_201 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_201
theorem lowS_201:Lower true dom_201 roots_201 goal_201 7:=S_201.noCircuit
def isoMvS_54:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_51
def isoMvS_58:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_51
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_83:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 4:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_51
def isoMvS_85:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_43
def isoMvS_86:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_43
def isoMvS_89:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_43
def isoMvS_90:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 4:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_51
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_43
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_51
def isoMvS_101:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_101:Lower true dom_101 roots_101 goal_101 4:=lower_iso_b isoMvS_101 (by decide +kernel) lowS_51
def isoMvS_106:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 4:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_51
def isoMvS_108:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_108:Lower true dom_108 roots_108 goal_108 4:=lower_iso_b isoMvS_108 (by decide +kernel) lowS_51
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 4:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_51
def isoMvS_114:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_114:Lower true dom_114 roots_114 goal_114 4:=lower_iso_b isoMvS_114 (by decide +kernel) lowS_51
def isoMvS_120:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_51
def isoMvS_141:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_141:Lower true dom_141 roots_141 goal_141 5:=lower_iso_b isoMvS_141 (by decide +kernel) lowS_43
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_43
def isoMvS_149:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_149:Lower true dom_149 roots_149 goal_149 5:=lower_iso_b isoMvS_149 (by decide +kernel) lowS_43
def isoMvS_150:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_150:Lower true dom_150 roots_150 goal_150 5:=lower_iso_b isoMvS_150 (by decide +kernel) lowS_105
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_156:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_156:Lower true dom_156 roots_156 goal_156 5:=lower_iso_b isoMvS_156 (by decide +kernel) lowS_43
def isoMvS_165:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_165:Lower true dom_165 roots_165 goal_165 4:=lower_iso_b isoMvS_165 (by decide +kernel) lowS_51
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 4:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_51
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 4:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_51
def isoMvS_178:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_178:Lower true dom_178 roots_178 goal_178 5:=lower_iso_b isoMvS_178 (by decide +kernel) lowS_43
def isoMvS_195:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_195:Lower true dom_195 roots_195 goal_195 5:=lower_iso_b isoMvS_195 (by decide +kernel) lowS_43
def isoMvS_197:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_197:Lower true dom_197 roots_197 goal_197 5:=lower_iso_b isoMvS_197 (by decide +kernel) lowS_105
def isoMvS_204:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_204:Lower true dom_204 roots_204 goal_204 5:=lower_iso_b isoMvS_204 (by decide +kernel) lowS_105
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_105
def isoMvS_210:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_210:Lower true dom_210 roots_210 goal_210 5:=lower_iso_b isoMvS_210 (by decide +kernel) lowS_105
def isoMvS_212:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_212:Lower true dom_212 roots_212 goal_212 7:=lower_iso_b isoMvS_212 (by decide +kernel) lowS_201
def isoMvS_216:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 5:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_105
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_43
def isoMvS_226:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_226:Lower true dom_226 roots_226 goal_226 4:=lower_iso_b isoMvS_226 (by decide +kernel) lowS_51
def isoMvS_232:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 5:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_43
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_slice_b [(0xaa00aa00aa00aa,32,33)] (by decide +kernel) lowS_54
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0c0000
def gsh_43_16:=0xf0e00000e0c
theorem lowS_zo_43_16_41:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (lower_slice_b (T:=gsh_43_16) [(0xc0c00000c0c,0,2)] (by decide +kernel) lowS_41)
namespace S_59
def pG:List (Nat×Nat):=[(1,9),(1,33),(2,18),(2,34),(3,11),(3,19),(3,35),(8,9),(8,40),(10,11),(10,26),(10,42),(16,18),(17,19),(17,25),(17,49),(24,25),(24,26),(24,56),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56)]
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
|4,0=>0xb120e1f10d
|5,0=>0xdeb70a6f001a42
|6,0=>0x9abd7
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0a0f0a0f0a0f0af0f0f0f0f000f0000f000f00000000f000f000f000f00505050505000500f0f0f0f00000000f0f00000f0f0000f000f000a000a00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x436104396108436104361074361543210
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
|0=>0x11b
|_=>0
def oO:Nat→Nat→Nat
|5,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0x1f41c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xca
|6,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_43 5 roots_43 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dzo_43_16 5 roots_43 ops++addP pm 3 dom_58 4 roots_58 ops++addP pm 4 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_59 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_43 5 s (0,roots_43.map (·&&&dom_43)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_59 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_43 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_slice_b [(0x3030303030303030,16,20),(0x3333000033330000,4,20)] (by decide +kernel) lowS_41
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_86
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,65),(4,20),(4,68),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,20),(16,80),(17,21),(17,25),(17,81),(24,25),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0xe790
|4,0=>0x5c0794e1e218ea208903
|5,0=>0x89ed47031f6af214c25331d9631668306801f22409fb104b5f
|6,0=>0x56bb74011c1e1fd11d1c
|7,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0ccc0cc00000000c0c0c0c333033300000000033303330c8c8c8c800000000c8c8c8cb232323200000000000000000000cccc000000000000c8cb33333330000000033003300c0c0c0c000000000c0c0c0c333033300000000000000000ccccccc000000000c0c0c0c3333000000000000333300000c0c0404000000000c0c000333333330000000000000000ccccccc000000000cccc000330033000000000033003300cccccccc00000000c0c0c0c222222220000000022222222
|0,1=>0xcccccccc000000008888888800033330000000000003030cccccccc00000000ccc0ccc11111111000000001100110000cc00cc0000000000000000000003300000000000000000000000000000000ccc0ccc030303030000000003000300
|_,_=>0
def sP:Nat→Nat
|0=>0x1849010c26a4043092021849b8086124049882905886a892021849a10ca4809330920248d11240430920810c27a40433841010c24808c1240b21949020c238086100a418820
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47684af19b330654c918f3186
|6,0=>0xc8d7d6cb536
|7,0=>0x6a5
|_,_=>0
def wAt:=mkWire dB 24 94 0x3fffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x4810111123064914a9111112491690
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52320000000000211101
|6,0=>0x91008171
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 8
def pmP:Nat→Nat
|0=>0xffde705cc286080
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x6204000135
|6,0=>0x9788
|7,0=>9
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 4 (j%128);fld (pmP (k/32)) 6 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_73 4 roots_73 ops++addP pm 2 dom_84 4 roots_84 ops++addP pm 3 dom_85 5 roots_85 ops++addP pm 4 dom_89 5 roots_89 ops++addP pm 5 dom_77 5 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 5 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s:Nat) (hs:s≤7):∀ i<NN s,bar dom_93 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤7) (h:RunD true dom_93 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_93 roots_93 goal_93 8:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_93
theorem lowS_93:Lower true dom_93 roots_93 goal_93 8:=S_93.noCircuit
def dzo_105_2:=0xc0c00000c0c00000c0c00000c0c
def gzo_105_2:=0xc0c00000c0800000c0c00000800
def gsh_105_2:=0x303000003020000030300000200
theorem lowS_zo_105_2_73:Lower true dzo_105_2 roots_105 gzo_105_2 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_2) [(dom_105,2)] (by decide +kernel) (lower_slice_b (T:=gsh_105_2) [(0x303000000000000030300000000,0,32)] (by decide +kernel) lowS_73)
namespace S_107
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,34),(3,11),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,42),(10,74),(32,33),(32,34),(32,40),(64,65),(64,72),(66,67),(66,74),(66,98),(96,97),(96,98),(96,104)]
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
|4,0=>0x2659
|5,0=>0xf3574
|6,0=>0xb40cf
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0a00000f0a00000f0a00000f0af0f00000f0f0000000000000000f0f0000000000000f0f000000000000000000000000f0a00000f0af0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a
|_,_=>0
def sP:Nat→Nat
|0=>0x888b3222c688
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
addP pm 0 dom_105 5 roots_105 ops++addP pm 1 dom_43 5 roots_43 ops++addP pm 2 dom_106 4 roots_106 ops++addP pm 3 dzo_105_2 5 roots_105 ops++addP pm 4 dom_73 4 roots_73 ops++addP pm 5 dom_99 4 roots_99 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_107 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_105_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_73 _ g hchk
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
namespace S_115
def pG:List (Nat×Nat):=[(1,33),(1,65),(2,18),(2,34),(3,19),(3,35),(3,67),(16,18),(16,80),(17,19),(17,49),(17,81),(32,33),(32,34),(48,49),(48,50),(48,112),(64,65),(64,80),(66,67),(66,82),(66,98),(96,97),(96,98),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_115.map (·&&&dom_115)
def gM:=goal_115&&&dom_115
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x8f0901313
|5,0=>0x88c8c245e20f31a
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000c000f000c000f000c000f000cf000f000f000f000c000c000c000cf0000000f0000000c0000000c0000f000f000f000f0000000000000000f000f00000000000f000f000000000000000000000000f000a000f000af0000000f0000000f0000000f0000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a
|_,_=>0
def sP:Nat→Nat
|0=>0x42105421054821054271054160543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 116 0xfffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def pmP:Nat→Nat
|0=>0x7c40
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>5
|6,0=>2
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_114 4 roots_114 ops++addP pm 1 dom_113 4 roots_113 ops++addP pm 2 dom_51 4 roots_51 ops++addP pm 3 dom_99 4 roots_99 ops++addP pm 4 dom_83 4 roots_83 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_83 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_114 4 s (0,roots_114.map (·&&&dom_114)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_114 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_115==dom_115)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_115 gM v ys):RunD true dom_115 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_115 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_115 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_slice_b [(0xaa00aa00000000000000000000000000aa00aa,128,129)] (by decide +kernel) lowS_150
theorem lowS_167:Lower true dom_167 roots_167 goal_167 5:=lower_slice_b [(0xaa000000aa0000000000000000000000aa000000aa,32,33)] (by decide +kernel) lowS_166
theorem lowS_179:Lower true dom_179 roots_179 goal_179 6:=lower_slice_b [(0xa000a000a000a0000000000000000000a000a000a000a,32,33)] (by decide +kernel) lowS_178
theorem lowS_203:Lower true dom_203 roots_203 goal_203 8:=lower_slice_b [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,128,130)] (by decide +kernel) lowS_201
theorem lowS_205:Lower true dom_205 roots_205 goal_205 8:=lower_slice_b [(0x3030000000000000303000000000000030300000000000003030,64,68)] (by decide +kernel) lowS_201
namespace S_211
def pG:List (Nat×Nat):=[(1,65),(1,129),(2,18),(2,130),(3,19),(3,67),(3,131),(16,18),(16,80),(16,144),(17,19),(17,81),(17,145),(64,65),(64,80),(64,192),(66,67),(66,82),(66,194),(128,129),(128,130),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_211.map (·&&&dom_211)
def gM:=goal_211&&&dom_211
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x50762
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000000000000000f000000000000000f000000000000000f0000c000c00000000000c000c00000000000c000c00000000000c000ca000a00000000000a000a00000000000a000a00000000000a000af000f000000000000000000000000000f000f0000000000000000f000f00000000000f000f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 212 0xfffffffffffffffffffffffffffffffffffffffffffffffffffff
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
addP pm 0 dom_210 5 roots_210 ops++addP pm 1 dom_147 5 roots_147 ops++addP pm 2 dom_209 5 roots_209 ops++addP pm 3 dom_195 5 roots_195 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_211 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_210 5 s (0,roots_210.map (·&&&dom_210)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_211 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_210 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_211==dom_211)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_211 gM v ys):RunD true dom_211 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_211 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_211 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_211 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_211 roots_211 goal_211 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_211
theorem lowS_211:Lower true dom_211 roots_211 goal_211 7:=S_211.noCircuit
def isoMvS_62:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_62:Lower true dom_62 roots_62 goal_62 5:=lower_iso_b isoMvS_62 (by decide +kernel) lowS_55
def isoMvS_91:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_91:Lower true dom_91 roots_91 goal_91 7:=lower_iso_b isoMvS_91 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 6:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_87
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_55
def isoMvS_109:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_109:Lower true dom_109 roots_109 goal_109 7:=lower_iso_b isoMvS_109 (by decide +kernel) lowS_107
def isoMvS_110:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 5:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_55
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 7:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_59
def isoMvS_118:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_59
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_107
def isoMvS_122:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 7:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 8:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_93
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 8:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_93
def isoMvS_173:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_173:Lower true dom_173 roots_173 goal_173 7:=lower_iso_b isoMvS_173 (by decide +kernel) lowS_107
def isoMvS_181:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_181:Lower true dom_181 roots_181 goal_181 7:=lower_iso_b isoMvS_181 (by decide +kernel) lowS_59
def isoMvS_182:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_182:Lower true dom_182 roots_182 goal_182 7:=lower_iso_b isoMvS_182 (by decide +kernel) lowS_107
def isoMvS_213:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_213:Lower true dom_213 roots_213 goal_213 8:=lower_iso_b isoMvS_213 (by decide +kernel) lowS_205
def isoMvS_214:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 8:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_205
def isoMvS_217:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 8:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_205
def isoMvS_218:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_211
def isoMvS_220:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_220:Lower true dom_220 roots_220 goal_220 8:=lower_iso_b isoMvS_220 (by decide +kernel) lowS_205
def isoMvS_227:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_179
def isoMvS_229:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_229:Lower true dom_229 roots_229 goal_229 7:=lower_iso_b isoMvS_229 (by decide +kernel) lowS_107
def isoMvS_233:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 8:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_205
def isoMvS_236:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 7:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_107
def isoMvS_241:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_107
def isoMvS_242:List (Nat×Nat):=[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_242:Lower true dom_242 roots_242 goal_242 7:=lower_iso_b isoMvS_242 (by decide +kernel) lowS_107
theorem lowS_63:Lower true dom_63 roots_63 goal_63 8:=lower_slice_b [(0xf0f0f0f0f0f0f0f0,16,20)] (by decide +kernel) lowS_59
theorem lowS_95:Lower true dom_95 roots_95 goal_95 9:=lower_slice_b [(0xcccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_93
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_109
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00ee00000000
def gsh_87_32:=0xff00fe0000000000fe00ee
theorem lowS_zo_87_32_84:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_84)
namespace S_119
def pG:List (Nat×Nat):=[(1,33),(1,65),(2,18),(2,34),(3,19),(3,35),(3,67),(4,20),(4,68),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,23),(7,39),(7,71),(16,18),(16,20),(16,80),(17,19),(17,21),(17,49),(17,81),(32,33),(32,34),(36,37),(36,38),(36,52),(36,100),(48,49),(48,50),(48,52),(48,112),(64,65),(64,68),(64,80),(66,67),(66,70),(66,82),(66,98),(96,97),(96,98),(96,100),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffff
def xsM:=roots_119.map (·&&&dom_119)
def gM:=goal_119&&&dom_119
def NN:Nat→Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe7e0dcefe6a65d7
|5,0=>0xe1eecd8193a8e485ab191dc8b
|6,0=>0xfd584f89eca8e4873eed633535d38a4f8473eb1e2b7ce
|7,0=>0xe8d9f6aedf5d38a
|8,0=>0xdaa04
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff00cc00ff00cc00cc00cc00cc00cc0000000000000000ff000000ff00000000ff000000ff0000000000000000ff00ff00ff000000ff00ff00000000ff00f000ff00f000f000f000f000f0ff000000ff000000ff000000ff0000ff00ff00ff00ff0000000000000000f000f000f000f000f000f000f000f0ff000000ff00000000000000000000ff00ff00ff00ff00ff000000ff000000000f0000000f000f0000000f0000ff00ff0000000000ff00ff000000000000ff000000ff00ff000000ff0000cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa0f000f000f000f000f0000000f0000
|0,1=>0xff0000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8a40829229020a5a45204149c86520414914b10530520414914208124521e1491c8105a4329020a48640827629020a48650820490cb104834082450820490c340824308203906209486104a418820
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2942a805
|5,0=>0x26542a6d8ab0f6
|6,0=>0x5d6aed45a5b4567cee19932b7
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def wAt:=mkWire dB 17 120 0xffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x52652452553552652452552552552431f52452531f524525
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x62198000600
|6,0=>0x592480081
|7,0=>0x3c5c2d1
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 9
def pmP:Nat→Nat
|0=>0xffccb8c0c10100
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1208
|6,0=>0x4014741
|7,0=>0x1ff
|8,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_118 7 roots_118 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_103 5 roots_103 ops++addP pm 3 dom_55 5 roots_55 ops++addP pm 4 dom_117 7 roots_117 ops++addP pm 5 dom_87 6 roots_87 ops++addP pm 6 dzo_87_32 6 roots_87 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_119 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_118 7 s (0,roots_118.map (·&&&dom_118)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_119 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_118 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_119==dom_119)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_119 gM v ys):RunD true dom_119 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_119 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_119 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_119 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_119 roots_119 goal_119 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_119
theorem lowS_119:Lower true dom_119 roots_119 goal_119 9:=S_119.noCircuit
def dzo_73_2:=0xc0c0000000000000c0c
def gzo_73_2:=0xc080000000000000800
def gsh_73_2:=0x3020000000000000200
theorem lowS_zo_73_2_73:Lower true dzo_73_2 roots_73 gzo_73_2 4:=lower_iso_b (d1:=dom_73) (r1:=roots_73) (T1:=gsh_73_2) [(dom_73,2)] (by decide +kernel) (lower_slice_b (T:=gsh_73_2) [] (by decide +kernel) lowS_73)
def dzo_121_2:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2:=0xc0c0c0c0c0c0c080c0c0c0c0c0c0800
def gsh_121_2:=0x3030303030303020303030303030200
theorem lowS_zo_121_2_73:Lower true dzo_121_2 roots_121 gzo_121_2 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_2) [(dom_121,2)] (by decide +kernel) (lower_slice_b (T:=gsh_121_2) [(0x3030000030300000303000003030000,0,16),(0x3030303000000000303030300000000,0,32)] (by decide +kernel) lowS_73)
def dzo_89_2:=0xc0c0c0c000000000c0c0c0c
def gzo_89_2:=0xc0c0c08000000000c0c0800
def gsh_89_2:=0x30303020000000003030200
theorem lowS_zo_89_2_73:Lower true dzo_89_2 roots_89 gzo_89_2 5:=lower_iso_b (d1:=dom_89) (r1:=roots_89) (T1:=gsh_89_2) [(dom_89,2)] (by decide +kernel) (lower_slice_b (T:=gsh_89_2) [(0x30300000000000003030000,0,16)] (by decide +kernel) lowS_73)
def dzo_41_16:=0x303000003030000
def gzo_41_16:=0x302000002000000
def gsh_41_16:=0x30200000200
theorem lowS_zo_41_16_41:Lower true dzo_41_16 roots_41 gzo_41_16 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_16) [(dom_41,16)] (by decide +kernel) (lower_slice_b (T:=gsh_41_16) [] (by decide +kernel) lowS_41)
def dzo_107_16:=0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16:=0xf0f00000f0f00000f0e00000e0c0000
def gsh_107_16:=0xf0f00000f0f00000f0e00000e0c
theorem lowS_zo_107_16_41:Lower true dzo_107_16 roots_107 gzo_107_16 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_16) [(dom_107,16)] (by decide +kernel) (lower_slice_b (T:=gsh_107_16) [(0xc0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_41)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(16,18),(16,80),(17,19),(17,25),(17,49),(17,81),(24,25),(24,26),(24,56),(24,88),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(64,65),(64,72),(64,80),(66,67),(66,74),(66,82),(66,98),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x21e2d114b1
|5,0=>0x9fc1b940397cd967a638636a95964f55ff14594e3ede912494117ce0ea2d09ce1091b307073
|6,0=>0xec765e3150d8dd0c066fb179db0d0faf437a73fca326d9ee0b9132b8b9cb822f17dd79767bc74c90749e96bac261a7e5b8485964f56f6f55438531e75097a4a56b476a0465d5436d23f0b93cf8f3cd203833437ec73300f293d928eff23eb7231ca1e7f81ddb31afdf1a66e1827b174021340c107f50ed2a0d1770cac50c48a0c09c0909d05eae05d3a024bd
|7,0=>0xae6f7a3af3881828532078e1077981729586a42d63b3d6240e5f86f4938f446b53c00a3b21c36ea935a1e3004b2e1d02cd922a039297df1fafa1d0481489e12c1f0fa2d0eefb0d8d10ce6c0ca2c
|8,0=>0xcdd92a269a93d036900d62b5b32d0c1cf4b07721
|9,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f000f000a0a0a0a0a000a00f0f0f0f000000000f0e0f0e00000000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f00000000a0a0a0a0a0a0a0a0a0a0a0a0a000a0000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0a0f0a0f0a0f0a0f0a0f0a00000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f000f000a000a00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
|0,1=>0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f000f000000000000000000505050505000500f0f0f0f0f0f0f0f0f000f000f000f0050505050505050505000500050005005050505050505050505050500000000004000400040004000400040c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af0f00000f0f0f0a00000000000000000000000000000000f0a0f0a0f0a0f0af0f00000f0f00000c0c00000c0c000000f000f000f000f000f000f000a000a00000000c0c0c0c000000000f0e0f0ef0e0f0e0f0e0f0e0f0e0f0e0c0c0c0c0000000000000000f0f0f0f0f0f0f0a00000000f0f0f0f000000000f000f00
|0,2=>0xf0a00000f0a00000f0a00000f0ac0c00040c0c00040c0c00040c0c0004c0c0f0e0c0c0f0e0c0c0f0e0c0c0f0ef0f0f0f0f0f0f0a0f0f0f0f0f0f0f0a0000f0f00000f0a00000f0f00000f0af0f000f0f0f000a0f0f000f0f0f000a5050505050505050505050505000500f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0ef0e0f0e000000000f0e0f0e00000000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e000000000000000000e000e000e000ef0f0f0f0f0f0f0f0504050405040504f0f0f0f0f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f00000f0a0f0f0f0f00000f0a00000000f0f0f0f000000000a0a0a0a
|0,3=>0x5050505050005000505050505000500f0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a005000500050005000500050000000000f000f000f000a000f000f000f000af0f0f000f0f0f000f0f0f000f0f0f00f0f0f000a0a0a000f0f0f000a0a0a00f030f030f030f030f020f020f020f0200000000f0e0f0e000000000f0e0f0e0000f0f00000f0f00000c0c00000c0cf000f000f000f000f000f000a000a00f000f000f0f0f0a0f000f000f0f0f0af0f0f0f0f0f0f0f050505050500050000000000f0f0f0a000000000f0f0f0aa0a0a0a0a0a0a0a0f0f0f0f0f0a0f0a00000000f0f0f0f000000000f0a0f0af0f0f0f0f0f0f0f0f0f0f0f0f0a0f0a
|0,4=>0xf0f0f0f0a0a0a0a0000f0f00000a0a00000f0f00000a0a30303030303000003030303030300005050500050505000505050005050500f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0cf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0af0f0f0f0f0f0a0a0f0f0f0f0f0f0a0af0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f00000f0f0f0a0f0f00000f0f0f0af0f0f0f0f0f00000f0f0f0f0f0f000000000000f0a0f0a000000000f0a0f0aa0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a000000000000000000000000f0a0f0af0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
|0,5=>0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f00000f0f00003020302030203020302030203020302
|_,_=>0
def sP:Nat→Nat
|0=>0x160ce0d002840b063400c3a2020b063400c361c18d0030d08160c68c32203980608008080c68100305831a0061716586802a305830030a08063400c26205832434608222c18d00303840608005160c1000a405830400788063868018203830c00608160c00a12203830c002840608080
|1=>0x1ab8608160c6ad182160b063400c102c18d0031588302c19c1a0060b067068018805aa063400c1010583047000c160ce0d00a44034e0868018205831a00625102c18d0030a08160c680189040b063400c46205821a00a8c10605830434008422c18d003040b0608680402039f0608008
|2=>0x30f8b063401a102c18d0031e88160c68018f041f080c68034205ba063400c102c180185040b06e4680182018d0031c08160868018dc418160db0018205836a3400c10785830030488160c68018d040b063408018205831a0063310c85831a00608160c68018c4430160c6801820583
|3=>0x1a0060817181821a00608160d4021a006080e2c182003040b063400a102e2831a006080e2c1820014403043400c7020c0b0600614111018d0032188069c68018205831a0210c10105831a01488160c6801904404160c68014205c0063403f102c1861a006080e1018d0014604160df0d
|4=>0x106020b063400c102c18d00328080e2c18d00146089e2c18d003040b063400c12205831a0064e102c18d193440b063400c982258b06086801820f0b063400c102c18d94006083c1c5831a006083e1018d003040b072468018205831a0061b102c19c1a9800c102e4031a006088e7c583
|5=>0x60868018205c6063400c11485831a0060816ec18d003040b063400c107c5831a00608882c18d0030404160c68018205831a00643102c6802a30444160c10d003040b06f8680182290b0634005182039f063400c1010583043400c102c1be1a0028c102e883043400c10105831a0061a
|6=>0x2c18d003040b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x77d9d87745dca770ddbc76d99af76a1da17669d937631d8575f9d7775c1d697589d5b755594e752194174e9d3374b1d257479d177441d097409cfc63d98ef73a1ce17369cd37331cc572f9cb772c1ca97289c9b7251c8d7219c8061e5c7271adc647
|7,0=>0x2c37af5ab58ab9ea68a7de978a3e28789fe27789c1e688985e5a794de4d6919e3e88dde3078a22217869e13782e20477f21f487b21e57
|8,0=>0xbe9ef37bb1ee57b7dad87b45eca7
|9,0=>0x3016
|_,_=>0
def wAt:=mkWire dB 83 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x83716213c3308353c30083516210e331a2d080816211a3104211a313e210837162116213eec182d440f00210e210e331a2d3e701a21182d00bf040f1a311a310a2d18213e373c33382d16a00401389a1a211a31440c00213e21182d0a2f18211a311635182d3c30382d38331a21083316210a2d18210e1418211a2d0808102d
|1=>0x18211635182d16211a310a35182106211a31083316210831162104031a3118211a2d3e23182d083716213e0f182d8803062d76330635042d1a310e211a2d109a00310e211a2d1621182d38011a2138331a2100311a21040d1a313e0d182d06011a3104011a311a2d18350e211a2d16a204013e21182d042f1a31502c04011a31
|2=>0x1a310601002d0635182d062d1621042f1a31440c0021062d1a3104211a31002d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x52000000000000000000000000000023000002000
|6,0=>0x4920000004724524324033e23c20003933723430003223112f20002e12c20000000002a20000002912722430000000000002130002010001e20001d10001b21921720000000001431220001020d30b2000092072
|7,0=>0x8728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b2
|8,0=>0x8f18e18d18c10008b18a1891
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 12
def pmP:Nat→Nat
|0=>0x222020025404004381800837300102e60018fcc0011f9800170300026e600040040006210000c0200007e60000c0c0000d9800017300002860000504000099800010200002000000384000051800004000000460000080000008000000c000000600000080000008000000
|1=>0x82407e70000285002050910001112442e610087cc200050830001d02442ee04885cc08008a80c23f300712e600887cc0109b980213710041ee600825cc0101b98018803
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x800000000000000c0080
|6,0=>0x400010854412c03053c02d60400420000010005080c000000700400200400204600000a0800920802c2
|7,0=>0x1c4e99ed60f83039f64f961aa6bde8da564a2226ab32c5d
|8,0=>0x6f3baa357ae1
|9,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 27 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_115 7 roots_115 ops++addP pm 2 dom_73 4 roots_73 ops++addP pm 3 dzo_73_2 4 roots_73 ops++addP pm 4 dom_107 7 roots_107 ops++addP pm 5 dom_121 7 roots_121 ops++addP pm 6 dom_59 7 roots_59 ops++addP pm 7 dzo_121_2 6 roots_121 ops++addP pm 8 dom_91 7 roots_91 ops++addP pm 9 dzo_89_2 5 roots_89 ops++addP pm 10 dom_83 4 roots_83 ops++addP pm 11 dom_51 4 roots_51 ops++addP pm 12 dom_90 4 roots_90 ops++addP pm 13 dzo_105_2 5 roots_105 ops++addP pm 14 dom_120 4 roots_120 ops++addP pm 15 dom_114 4 roots_114 ops++addP pm 16 dom_58 4 roots_58 ops++addP pm 17 dzo_43_16 5 roots_43 ops++addP pm 18 dom_41 4 roots_41 ops++addP pm 19 dzo_41_16 4 roots_41 ops++addP pm 20 dzo_107_16 6 roots_107 ops++addP pm 21 dom_106 4 roots_106 ops++addP pm 22 dom_89 5 roots_89 ops++addP pm 23 dom_99 4 roots_99 ops++addP pm 24 dom_43 5 roots_43 ops++addP pm 25 dom_113 4 roots_113 ops++addP pm 26 dom_105 5 roots_105 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_73_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_121_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_89_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_105_2_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_41_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_105 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
def dzo_84_32:=0x110011000000000011001100000000
def gzo_84_32:=0x110010000000000010000000000000
def gsh_84_32:=0x1100100000000000100000
theorem lowS_zo_84_32_84:Lower true dzo_84_32 roots_84 gzo_84_32 4:=lower_iso_b (d1:=dom_84) (r1:=roots_84) (T1:=gsh_84_32) [(dom_84,32)] (by decide +kernel) (lower_slice_b (T:=gsh_84_32) [] (by decide +kernel) lowS_84)
def dzo_93_32:=0x33333333000000003333333300000000
def gzo_93_32:=0x33333332000000003332332200000000
def gsh_93_32:=0x333333320000000033323322
theorem lowS_zo_93_32_84:Lower true dzo_93_32 roots_93 gzo_93_32 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (lower_slice_b (T:=gsh_93_32) [(0x222222220000000022222222,0,1),(0x330033000000000033003300,0,8)] (by decide +kernel) lowS_84)
def dzo_57_4:=0x3030303030303030
def gzo_57_4:=0x3030302030302000
def gsh_57_4:=0x303030203030200
theorem lowS_zo_57_4_41:Lower true dzo_57_4 roots_57 gzo_57_4 5:=lower_iso_b (d1:=dom_57) (r1:=roots_57) (T1:=gsh_57_4) [(dom_57,4)] (by decide +kernel) (lower_slice_b (T:=gsh_57_4) [(0x303000003030000,0,16)] (by decide +kernel) lowS_41)
def dzo_45_16:=0x3333000033330000
def gzo_45_16:=0x3332000032300000
def gsh_45_16:=0x333200003230
theorem lowS_zo_45_16_41:Lower true dzo_45_16 roots_45 gzo_45_16 5:=lower_iso_b (d1:=dom_45) (r1:=roots_45) (T1:=gsh_45_16) [(dom_45,16)] (by decide +kernel) (lower_slice_b (T:=gsh_45_16) [(0x303000003030,0,4)] (by decide +kernel) lowS_41)
def dzo_121_4:=0x30303030303030303030303030303030
def gzo_121_4:=0x30303030303030303030302030302000
def gsh_121_4:=0x3030303030303030303030203030200
theorem lowS_zo_121_4_41:Lower true dzo_121_4 roots_121 gzo_121_4 6:=lower_iso_b (d1:=dom_121) (r1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (lower_slice_b (T:=gsh_121_4) [(0x3030000030300000303000003030000,0,16),(0x3030303030303030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_92_32:=0x11111111000000001111111100000000
def gzo_92_32:=0x11111110000000001110110000000000
def gsh_92_32:=0x111111100000000011101100
theorem lowS_zo_92_32_84:Lower true dzo_92_32 roots_92 gzo_92_32 5:=lower_iso_b (d1:=dom_92) (r1:=roots_92) (T1:=gsh_92_32) [(dom_92,32)] (by decide +kernel) (lower_slice_b (T:=gsh_92_32) [(0x110011000000000011001100,0,8)] (by decide +kernel) lowS_84)
def dzo_105_4:=0x3030000030300000303000003030
def gzo_105_4:=0x3030000030300000302000002000
def gsh_105_4:=0x303000003030000030200000200
theorem lowS_zo_105_4_41:Lower true dzo_105_4 roots_105 gzo_105_4 5:=lower_iso_b (d1:=dom_105) (r1:=roots_105) (T1:=gsh_105_4) [(dom_105,4)] (by decide +kernel) (lower_slice_b (T:=gsh_105_4) [(0x303000003030000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33330000333300003332000032300000
def gsh_109_16:=0x3333000033330000333200003230
theorem lowS_zo_109_16_41:Lower true dzo_109_16 roots_109 gzo_109_16 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (lower_slice_b (T:=gsh_109_16) [(0x3030000030300000303000003030,0,4),(0x3333000033330000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_85_32:=0x330033000000000033003300000000
def gzo_85_32:=0x330032000000000032002200000000
def gsh_85_32:=0x3300320000000000320022
theorem lowS_zo_85_32_84:Lower true dzo_85_32 roots_85 gzo_85_32 5:=lower_iso_b (d1:=dom_85) (r1:=roots_85) (T1:=gsh_85_32) [(dom_85,32)] (by decide +kernel) (lower_slice_b (T:=gsh_85_32) [(0x2200220000000000220022,0,1)] (by decide +kernel) lowS_84)
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,20),(16,80),(17,21),(17,25),(17,49),(17,81),(24,25),(24,28),(24,56),(24,88),(32,33),(32,40),(36,37),(36,44),(36,52),(36,100),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xc4dc457c81434b31e6e3
|6,0=>0xd7b3ba183a9cce098c616496a61eff5c4c95b93e3723934fb22aad3218a61e578173500cce0
|7,0=>0xdb0cfd5699ab9d8a35f5a0ab38c3b48bb348a48c75a1770b7d508c13dc6e37a1a339c62a3601f1a2109bf1099d0bf9807eb303c2202f7101a5b00ecb
|8,0=>0xec553c4d75b382a8e226789cf774924624f067c2
|9,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccccccccccccccccccc0000cccc00033223322332233223322332233223322cccccccccccccccccc00cc00cc00cc033333333333333332222222222222222cccc0000cccc0000c0c00000c0c0000333333330000000033333333000000004444444444444444440044004400440003300330033003300220022002200220c0c0c0c0c0c0c0c0c0c00000c0c00000000000332233220000000033223322cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c222222222222222222222222222222220c0c0c0ccc8ccc8c00000000cc88cc8b3333333333333330000000000000000
|0,1=>0xccc8ccc8ccc8ccc8ccc8ccc8ccc8cccb33333003333330033333300333333004444440044444400444444004444440003300330033003300000000000000008c8c8c8c8c8c8c8c888888888888888b3333333333333333333333300000000cccccccccccccccc00000000cc88cc8b3333030333330303333303033333030ccccccccccccccccc0c0c0c0c0c0c0c00220033002200330022002200220022cccccccccccccccccc88cc88cc88cc8a22233332222333322222222222222220000cccc0000cccc000000000000000332233333322333333223322332233220c0c0c0c0c0c0c0c00000000000000033033303330333033300330033003300
|0,2=>0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc33333333003300333333333300000000cccccccc0c0c0c0ccccccccc000000033113311331133113300330033003300004400440044004400000000000000011111111111111110000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x851170c21801440c264060510308600a3840cb08028510309600a14e34330a14e34330028554308800a15210308028534330220510308601128538330800a14e40308028538408700a1440cc2401032c21802850c92001440871801440c2040
|1=>0xc200a1440c22008c51030802853840c201329814e1030802858840c200a1440c20216851030a06853440c200a15f1030802851021c028510309d00a15510330200a14e34308028510330270a14d10308900a1440db0802855440c201a1440cc
|2=>0xa1440c201a1440c200a1440c20202851170c200a1440cc0802981440c200a14e1030802859440c200a1440c20112853440cc08a14d10330200a14e1170c200510308600a1032c2024144
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce4c6b7323975caec50724b909c76e34716b899c3ee187
|7,0=>0x8fbc5e21f109681b3f59ecef067443821b2ed27663315d7ceb8658baa6144e9b749c231d0ae7f6
|8,0=>0xabb541e92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def wAt:=mkWire dB 38 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10244810808e02102420228044012804e0d102433e1405e0b144443108044010844402080423610042450c08e0110242012804a3a102440928e8409102455c0c044091004201102440108055133804211114424d1408c130804a3a0c0840910c82011114302102433e1404d0b1004201
|1=>0xa010808301080450d10243110c08401080440108044090c04a3a102455c0c04a7110084320804a450c08502102450d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x849009e2366000c19532463cc690a310418819803
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x6b560d6a4185c82bfb051d2096e411dd823b90475e08eac1057820a90407e0220002448033f0067a00ce400400004000076000e800180002f000540002c0004800080000e0000c000100000
|1=>0x21adcc048d4cb528122495fd8b8fb157f628eec3954835b9
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1000
|6,0=>0xd30d4403cb0c22521c4146
|7,0=>0x38ba1b69c5a44e66599627e084841029d5dc
|8,0=>0x8d8a589d579d
|9,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 19 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_93 8 roots_93 ops++addP pm 1 dzo_84_32 4 roots_84 ops++addP pm 2 dom_84 4 roots_84 ops++addP pm 3 dom_124 7 roots_124 ops++addP pm 4 dom_61 6 roots_61 ops++addP pm 5 dom_117 7 roots_117 ops++addP pm 6 dzo_93_32 6 roots_93 ops++addP pm 7 dom_121 7 roots_121 ops++addP pm 8 dzo_57_4 5 roots_57 ops++addP pm 9 dzo_45_16 5 roots_45 ops++addP pm 10 dzo_121_4 6 roots_121 ops++addP pm 11 dzo_92_32 5 roots_92 ops++addP pm 12 dzo_105_4 5 roots_105 ops++addP pm 13 dom_109 7 roots_109 ops++addP pm 14 dzo_109_16 6 roots_109 ops++addP pm 15 dzo_85_32 5 roots_85 ops++addP pm 16 dom_92 5 roots_92 ops++addP pm 17 dom_105 5 roots_105 ops++addP pm 18 dom_41 4 roots_41 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_zo_84_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_93_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_57_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_45_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_zo_121_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_92_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_85_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_93 8 s (0,roots_93.map (·&&&dom_93)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_93 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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
def dzo_151_32:=0xff00ff00000000000000000000000000ff00ff00000000
def gzo_151_32:=0xff00fe00000000000000000000000000fe00ee00000000
def gsh_151_32:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_32_148:Lower true dzo_151_32 roots_151 gzo_151_32 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_32) [(dom_151,32)] (by decide +kernel) (lower_slice_b (T:=gsh_151_32) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
namespace S_183
def pG:List (Nat×Nat):=[(1,33),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,131),(4,20),(4,132),(5,21),(5,37),(5,133),(6,22),(6,38),(6,134),(7,23),(7,39),(7,135),(16,18),(16,20),(16,144),(17,19),(17,21),(17,49),(17,145),(32,33),(32,34),(36,37),(36,38),(36,52),(36,164),(48,49),(48,50),(48,52),(48,176),(128,129),(128,130),(128,132),(128,144),(160,161),(160,162),(160,164),(160,176)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_183.map (·&&&dom_183)
def gM:=goal_183&&&dom_183
def NN:Nat→Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xe4bbfd57328e2585c3454b346
|5,0=>0xfcb6efb964e65a2c4dabb980ba531e9c9da961a18657878c52644cc1acdd19ad30adf10494b
|6,0=>0xfed70f4680e30b0da542d49a5cb550ca919c9042c4d7cc2de9bab12b58a3b34a2aab8aa886d9e7789b7128263b71534662c0652a364b44646c4644cc5b6f25b34757a833c7733678f3386e2d7bd27c20246ea2048f189eb156ff0df13
|7,0=>0xcf017bc3d3ac7aaa886da2cd06b2e960448490a5329ef04aba
|8,0=>0x8a6fe
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xff000000ff000000000000000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000000000000000000ff00f000ff00f0f000f000f000f0000000000000000000f000f000f000f0ff00cc00ff00cc000000000000000000cc00cc00cc00cc0f000f000f000f0000000000000000000f0000000f0000ff000000ff0000000000000000000000ff000000ff0000fe00fe00fe00fe000000000000000000fe00ee00fe00eefc00fc00fc00fc000000000000000000fc00cc00fc00ccff00ff00ff00ff000000000000000000000000000000000000ff000000ff000000000000000000ff000000ff0000ff00ff00000000000000000000000000ff00ff00000000ff00ff00ff00ff000000000000000000ff000000ff0000cc00cc00cc00cc000000000000000000cc00cc00cc00ccaa00aa00aa00aa000000000000000000aa00aa00aa00aa00000f0000000f0000000000000000000f0000000f0000
|0,1=>0xf0000000f0000ff00ff00ff00ff000000000000000000ff00f000ff00f0ff00ff00ff0000000000000000000000ff00ff0000000000000000000000000000000000000000ff000000ff00000000f0000000f0000000000000000000f000f000f000f00000ff000000ff00000000000000000000000000000000ff00ff000000ff000000000000000000ff00ff00000000f000f000f000f0000000000000000000f0000000f00000ff00ff00ff00ff0000000000000000000f0000000f0000ff00f000ff00f0000000000000000000ff00f000ff00f0ff00ff00ff00ff000000000000000000f000f000f000f0ff000f00ff000f000000000000000000ff000000ff0000ff00f000ff00f0000000000000000000f000f000f000f000000000000000000000000000000000ff00ff000000000f0000000f00000000000000000000000f0000000f00000f000f000f000f00000000000000000000000000000000
|0,2=>0xff00ff000f000f000000000000000000ff00ff00000000ff000000000000000000000000000000ff00ff00000000f000f000f000f0000000000000000000ff00f000ff00f0ff00aa00ff00aa000000000000000000aa00aa00aa00aaf0000000f00000000000000000000000ff000000ff00000000ff00000000000000000000000000ff00ff00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8144640425808119924c0811842470461053020442420574045835420445020511840c204a3c40d308138908128648908128610308145010908128610324704610314c08110330b04e3493020440cb04a1050812842481c61050810040c2040
|1=>0x25530204434930204610324204a1a024c08118424c0817c611424c08118458954204638930205118424204a1840cc08144611e24c08119d24c08118425308118e58930204610325808118458330204611670c0811840c93020501096c2046109
|2=>0x24c08119a10954c08118424c08144611624c0811a524c0811a424c0811848c930204638324c08118e25c30204610330204f48324c08118424c0815c648970c08118424c08128611c30205a10930288610984c08118424c2c11840c9302046103
|3=>0x424c08118424c08119038930204648930204610324c08118425c3020461093020463c4
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a94caa5f62cb14d89ac4852130f186cc30615309183ea196
|6,0=>0x15f6acb549e96f4479f34dde60f297913c71a2cd0f784b409df6ef4776bb9d9c0ed97693b2dd8acbe75bbac5956ca474eba59d1ee8874131edceac6f6
|7,0=>0x344f9c6cb363df10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wAt:=mkWire dB 38 184 0xffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1a106441b246491b246091a306493324c4441306846b24689182464919246891b04f4918250c23d2460919246443f24604190ccc919246443d2460c3d2460419246491b2464c3f2460330246446924698090cc09190cfc918246491930f4918246423d2460919
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0xa31cc00184000003300000000000000000c00
|6,0=>0x2f2b480000000acaa1000000028298a518c80088400845f200000001e1709b1001925c9610015150531448003c8d2
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xf9fe5edfb5e9e49916448821584202801f76958518047108370882004c0b01c0500800
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x1460380030000008480
|6,0=>0xd6020f5440f05693b24e0330000984b032a709cd39010c
|7,0=>0x317c6b5bde5ce
|8,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_182 7 roots_182 ops++addP pm 1 dom_51 4 roots_51 ops++addP pm 2 dom_181 7 roots_181 ops++addP pm 3 dom_165 4 roots_165 ops++addP pm 4 dom_147 5 roots_147 ops++addP pm 5 dom_179 6 roots_179 ops++addP pm 6 dom_167 5 roots_167 ops++addP pm 7 dzo_151_32 6 roots_151 ops++addP pm 8 dom_151 6 roots_151 ops++addP pm 9 dom_55 5 roots_55 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_183 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_151_32_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_55 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_182 7 s (0,roots_182.map (·&&&dom_182)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_183 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_182 h
def ori (zs:List Nat):=zs
theorem ori_ok {v ys} (h:RunD true dom_183 gM v ys):RunD true dom_183 gM v (ori ys):=h
def Z (s:Nat):=barP dom_183 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
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
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_slice_b [(0xf0f0f0f0000000000000000000000000f0f0f0f00000000,1,33)] (by decide +kernel) lowS_155
theorem lowS_215:Lower true dom_215 roots_215 goal_215 9:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,64,65)] (by decide +kernel) lowS_214
namespace S_219
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(2,18),(2,130),(3,11),(3,19),(3,67),(3,131),(8,9),(8,72),(8,136),(10,11),(10,26),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,81),(17,145),(24,25),(24,26),(24,88),(24,152),(64,65),(64,72),(64,80),(64,192),(66,67),(66,74),(66,82),(66,194),(128,129),(128,130),(128,136),(128,144),(128,192)]
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
|6,0=>0xcec38
|7,0=>0xac13f99d425abc0501e506cc2
|8,0=>0x60ca92fd77
|9,0=>0x798d4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0a0f0a000000000f0a0f0a5050505000000000505050500000000050005000000000005000500f000f00000000000f000f00000000000f000f00000000000f000f00a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x5827065482706538270653821705a8270654821065a3827065827906543210
|_=>0
def sO:Nat→Nat→Nat
|6,0=>6
|7,0=>0x23771d5736067
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
|0=>0x21d865d9864dd865e1764dd864df86619785d9
|_=>0
def oO:Nat→Nat→Nat
|6,0=>3
|7,0=>0xb292725232
|8,0=>0xe1d1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0xfff337f7f5f9fc7e00
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>1
|7,0=>0x4f72
|8,0=>0x1a
|9,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 9 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_217 8 roots_217 ops++addP pm 1 dom_155 8 roots_155 ops++addP pm 2 dom_218 7 roots_218 ops++addP pm 3 dom_211 7 roots_211 ops++addP pm 4 dom_91 7 roots_91 ops++addP pm 5 dom_203 8 roots_203 ops++addP pm 6 dom_83 4 roots_83 ops++addP pm 7 dom_210 5 roots_210 ops++addP pm 8 dom_90 4 roots_90 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_219 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_90 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_217 8 s (0,roots_217.map (·&&&dom_217)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_219 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_217 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
namespace S_221
def pG:List (Nat×Nat):=[(1,9),(1,65),(1,129),(4,20),(4,68),(4,132),(5,13),(5,21),(5,69),(5,133),(8,9),(8,72),(8,136),(12,13),(12,28),(12,76),(12,140),(16,20),(16,80),(16,144),(17,21),(17,25),(17,81),(17,145),(24,25),(24,28),(24,88),(24,152),(64,65),(64,68),(64,72),(64,80),(64,192),(128,129),(128,132),(128,136),(128,144),(128,192)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffff
def xsM:=roots_221.map (·&&&dom_221)
def gM:=goal_221&&&dom_221
def NN:Nat→Nat
|4=>12
|5=>44
|6=>158
|7=>121
|8=>30
|9=>5
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x46df940a003eb4d39dd53660b28f12272892720b2419a1aa4a0da2609a30
|5,0=>0x94ec091e715aed5510bf4deb14a4bb48d1d44e1c3da983852f3678030b1a300292f5572c67b2c1cc2975c295e327c81266f5237d6207651f46c1e808180d215674141111395711f5b104c60f9f00d7e40c9780c4370bd680a6b8072090656303038027ae0239000aea00a34005dd
|6,0=>0x3be6c3b77d3b4623a6a639bf638fdc36d0535947350a233aa131f1330d2f30c33308842f3182f0542ecbb2ddf02c4c62b17f2b12e2a2b229b3b28d7d288ec27dfa27c282623d237f22346f23447228fc21403200491f2fd1f1c71e5b31e2fb1dc4b1d7511cd441c7a51c7631b60c1a8971a20c193ff193cd18fc818785180ec17988173e21670b1642715e7a15e1a15a88156741562e14ecc14d1114ce714c84149fa142aa12ff112bb212af412a911211611bf411abd1113010eb8104ea100730ff520fe8b0f1450e89f0e3360c8560c51e0b54c0b3e90b3b70a7780a44b09b49096b408ee1082be07b0a07a20079e5076560741e06ceb0667c0664006301061b8051fc0500504e980496a047de043a80412803adb0357403337031800317f028bf020c201f1301e0501bf800e9c00e8d0076a005830030d002b700232001b5
|6,1=>0x9e470956ac8511f82faf7f58b7da3678b8e762fb73e586c7ed6824763c6160bf05e1605cc9c5bbcf52f93513ae4fd404e12e4b11d49dc24812246149454a44341c42b5b429d33fcb33c4ad
|7,0=>0x88515802e770bdf6fee26b04e67ebe6719065b0864bea613425e7b05b2845b2545acda53a584e4054e08c4d8204d6e44cff24c6fe488f64646642fd43f7423f3f83eba53e3383deeb3aa743a88c3a7163a6be3908938032375f13139430e8a2e1412d6262cac52c2c82bde22adad27ee42778c26f5123c38228572230620cec20c201f1e71eca01e2471e06e1dd801dd471d74f1d5f31ce101c5a51bca31b53919852191831811c17da216a7c15bf81562e13e611318012627121d311db711c6f11c501130c110f8104a21026a0febe0fc740fbfc0fa970fa240e6980ddb60c9e00c8de0bee00b7990b1d20afe509cac0996a08dd808682083c207cc507be20794d063320600505e8405b8805b0b05abd049620482d04012037b403736033c5028bf0267101b0301a9500b3100808
|8,0=>0x76be26fae7611bd5bf894ec674421040db0407253afac34f4b32ec62aed9292f224f65246c2213062022b1c36f1b9301a74c1695c15dee1596e0e73c0c3c4098a00877c0814806f7c05ef9
|9,0=>0xf8f3f9f6c47369e125d80bcff
|10,0=>0x7369e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc888800000000cccc888800000000cccc888800000000000000033332222000000003333222200000000333322220000000033332222cccccccc00000000cccccccc00000000cccccccc00000000cccc00033333322000000003333332200000000333333220000000033003300cccccccc00000000cccccccc0000000088888888000000008888888b0303030000000003030303000000000303030300000000030303030cccc000000000000cccc000000000000cccc000000000000cccc00033303330000000003330333000000000333033300000000000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc000000000ccc0ccc33333333000000003333333300000000333333330000000000000000cccccccc00000000cccccccc000000000000000000000000000000033333330000000003333333000000000333333300000000033330000cccccccc00000000cccccccc00000000cccccccc00000000cc00cc0333333330000000033333333000000003030303000000000303030308888888800000000888888880000000088888888000000008888888b3333333000000000000000000000000333333330000000000000000
|0,1=>0xc0c000c000000000c0c000c000000000c0c000c000000000c0c00080330033000000000033003300000000003300330000000000220022ccccccc000000000ccccccc000000000ccccccc000000000c0c0c0c33333333000000002222222200000000333333330000000022222222c8c8c8c800000000c8c8c8c800000000c8c8c8c800000000000000032323232000000003232323200000000323232320000000032323232ccccc8c800000000ccccc8c800000000ccccc8c800000000cccc00033333300000000003333330000000000333333000000000000000000cccccccc00000000cccccccc00000000cc00cc0000000000cc00cc033333300000000003333330000000000333333000000000033333300cccccccc00000000cccc000000000000cccccccc00000000cccc00033333322000000003333332200000000333333220000000022222222cccccccc00000000cccccccc00000000cccc000000000000cccc00033333333000000003333333300000000333333330000000022222222ccccc8c800000000ccccc8c800000000ccccc8c800000000c0c0c0c33003300000000003300330000000000330033000000000033003300
|0,2=>0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c800300030000000000030003000000000003000300000000000000000000000000000000cccccccc000000000000000000000000cccc88880003333000000000000333300000000000033330000000000002222440444040000000044044404000000004404440400000000440044033330033000000003333003300000000333300330000000033330000cc00cccc00000000cc00cccc00000000cc00cccc00000000cc00cc00000000000000000000000000000000033333333000000003333330000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc000000011110000000000001111000000000000111100000000333300000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0003333333300000000330033000000000033333333000000003300330000000000000000000000000000000000cccccccc00000000cccc88891111111000000001111111100000000111111110000000011110000cccccccc00000000c0c0c0c000000000cccccccc00000000c0c0c0c33323332000000003332333200000000333233320000000022222222
|0,3=>0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000808080b33333330000000033330000000000003300330000000000330000004444444400000000444444440000000044444444000000004400440222233330000000022223333000000002222333300000000222222220000cccc000000000000cccc000000000000cccc00000000000000000220033000000000022003300000000002200330000000000220022ccc8ccc800000000ccc8ccc800000000ccc8ccc800000000cc00cc000003033000000000000303300000000000030330000000000003030c4c4c4c400000000c4c4c4c400000000c4c4c4c400000000c0c0c0c111111110000000011111111000000001111111100000000000000000000cccc000000000000cccc000000000000cccc000000000000c0c000000000000000000003333000000001111111100000000000000000000cccc000000000000cccc000000000000cccc000000000000c8c800031310000000000003131000000000000313100000000000030300000000000000000cccccccc000000000000000000000000cccccc033333333000000003333333300000000333333330000000030303030
|0,4=>0xcccccccc00000000cccccccc00000000cccccc0000000000cccccc000000000000000000000000000000000111111110000000010101010cccccccc00000000cccccccc000000004444444400000000404040433333333000000003300330000000000333300000000000033000000000000000000000044444444000000000000000000000000404040433333333000000003333333300000000333333330000000032323232cccccccc00000000cccc888800000000cccccccc00000000cccc888b0303030000000003030303000000000333333330000000033303330cccccccc00000000cccccccc00000000cccc888800000000cccc888b333333300000000323232320000000033333333000000003232323200000000000000000000000000000000cccccccc00000000c8c8c8c83030303000000000303030300000000030303030000000000000000cccccccc00000000ccc0ccc000000000cccccccc00000000ccc0ccc00000000000000000000000000000000333333330000000033303330cccccccc00000000cccccccc00000000cccccccc00000000cccc88891111111000000001111111100000000111111110000000010101010
|0,5=>0xc0c0c0c0000000008080808000000000c0c0c0c000000000808080b333333300000000333333330000000033333333000000003330333000cc00cc0000000000cc00cc0000000000cc00cc0000000000c000c0000003300000000000000330000000000000033000000000000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000000003333111100000000333311110000000033331111000000003333110000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc008b3333333000000003300330000000000303030300000000030003000cccccccc00000000cccccccc00000000c8c8c8c800000000c8c8c8c800000330000000000000033000000000000003300000000000000300000cccc000000000000cccc000000000000cccc000000000000cc000000000000000000303030300000000000000000000000002020202cccccccc000000000c0c0c0c00000000cccccccc000000000808080b3333333000000003333333300000000333333330000000033333300cccccccc00000000cccccc0000000000cccccccc00000000cccccc011111111000000001111111100000000111111110000000011111100
|0,6=>0xc0c0404000000000c0c0404000000000c0c0404000000000c0c0000000111100000000000011110000000000001111000000000000000000000c0c0000000000000c0c0000000000000c0c000000000000000333311110000000033331111000000003333111100000000333300008c8c8c8c000000008c8c8c8c000000008c8c8c8c000000008888888b33333330000000033333333000000003330333000000000333033304444444400000000444400000000000044444444000000004444000030303030000000003030303000000000303030300000000030003000c0c0c0c000000000c0c0c0c000000000c000c00000000000c000c000000000000000000000000000000000000000000000000033303330cccccccc00000000cccccccc000000000000000000000000ccc0ccc11001111000000001100111100000000110011110000000011001100000044440000000000004444000000000000444400000000000040403030003000000000303000300000000030300030000000003030000040404040000000004040404000000000404040400000000000000000003333000000000000333300000000000033330000000000003330
|0,7=>0xcccccccc00000000c0c0c0c2222222200000000222222220000000033333333000000003232323200cc00cc0000000000c000c00000000000cc00cc0000000000c000c00003333000000000000222200000000000033330000000000002222cccccccc00000000cccccccc000000000000cccc000000000000888800033330000000000003300000000000000333300000000000033000000000000000000c8c8c8c8000000000000000000000000c8c8c8c800000000000000000000000000000000000333300000000000033000000cccc000000000000cccc0000000000008888000000000000888b30033330000000033003333000000003300333300000000330033304444444400000000404040400000000044444444000000004040404030303030000000003030303000000000303030300000000030303000000000000000000cccccccc000000000000000000000000c8c8c8c80000000000000000033003300000000000000000000000000300030cc00cc0000000000cccccccc00000000cc00cc0000000000ccc0ccc30333033000000003033303300000000303330330000000030303030
|0,8=>0xcccc888800000000cccc8888000000000000000333322220000000000000000000000003333222200cc00cc0000000000cc00000000000000cc00cc0000000000cc00033333333000000003333333300000000000000000000000032323232cc0ccc0c00000000cc0ccc0c00000000cc0ccc0c00000000cc00cc000000000000000003330333000000000000000000000000033303330000000000000000000000000000000000000cccc00000000000088880000000000000003333333300000000000000000000000033003300000000000000000000000000000000000000000000000000cccccc000000000000000000000000000000000003300330000000000300030cccccccc00000000c0c0c0c000000000cc00cc0000000000c000c0000000000000000003333333300000000000000000000000022222222c0c0c0c000000000cccccccc00000000c0c0c0c000000000c8c8c8c80000000000000000000000000000000333333330000000033330000
|_,_=>0
def sP:Nat→Nat
|0=>0x106002a290a01000528090a01270026100a01000504030a01000515100a120f0509241701250613240a01182309100a220009102120060509011f1e000515100a0b060f1310111c0615171d01061910021c06130c0a1c060d10111c0519100212000d170a140015030a1405130c0a12000d10110b000d0c0a0b000403020100
|1=>0x50901251e000509390a120005240a01380605100a123200050a012f350005090c0a12000509100a0106340a012f330005100a0b320600090c0a0b060019100a0b06001510110105283109100a01092430010805090a012f000504102101060509240201062e2d100a012c0513101d010019102101050910212b000509171d
|2=>0xa01050948100201000547100a012c0005091a0a0b1e0005091046450a0b0013100125003b0510300135004405094224100a010609100b01250600410910012500050910403f0005163e0a01060d101101000504170a0106000d0c0a010005091021023d06130a013a060009240a140509170a2006000d0a013a000509101112
|3=>0x10609070321010605511609170a0106091012012500050910210a01530509240a010805094310210201061609100a5000054f09240a01061329100a0106000e090a0b1e000513100a01001809100a0b014d0009100a0b2200054709100a1c0b06164c0a01000509104a0a01000509170a01270600100a0b01350600492d0910
|4=>0xa015d000509100a1c061b0509170a0106005c100a01330600051509170a01065b5a09100a3d00050910370a1c060515100a0155000541090a0159000509104a450a010009100a580106160d030a0100054909100a1c0b0609100a3d004405091046570a0106100a013556000513100a0106000f09100a3d5500054f1513100a
|5=>0x50910020106002e09104602010609030a015d0005100a0135630005231513100a0100091045020a01000943071002010609100a50060005091046013f000509300a012f000509240a01062e050924100a500005163109240a010509100162005b050910210100610510020a0160000509100a0b5f061513100a0106360907
|6=>0x60517100a0160000509240a016706091030010008050910450a0b0100091046450a0106281613100a010009300a011e00050965100a01060010370a013200051615170a010609100a640005101a30013500050910020a3d060009101d010005090a012f000509100a01005c05104a0a0133000509240a01005c050e15100a22
|7=>0x125006d050910370100610509100a120061056c09100a12000509103701004405091046021c01062a100a01005c05090730015d00050910012527000509100a3c0036050910026b0100053109100a0106056a100a01600005096a07240a0106091045210a010613100a0169060e100a1c2c0005091045570a01000910210168
|8=>0x509460a011e00051615100125000509210a012f0005472d15100a0105471309100a1c060971240a010005100a013806000509460a012f00050910016f00050e6c100a010005310d09100a010510570a013500054f3109100a0106280903100a01000910460a40000509100a1c0b0644094203100a0100090a121e0036051310
|9=>0x100a2200050910016206000509031021020106091001250036051324100a01063b09100a1400050d100a01550005091046450201000910020175064913100a1c01061609100174000541100a012c00052d09100a1c0b0509100a2b004405310924170a01050910732102010509030a01002e0509101a37010005090724300106
|10=>0x76100a0135000510300135006d050d100a01005c050910306b01000552090a012700050907030a3d00050d100a01001805095e10016800050e0d10012500050910021c01064409100a3c006e05090c0a0106000519100a0106000509170a015d06000d0910017400050d09100a1c0b062a09030a010005090703016800050e0d
|11=>0x73020a01000509436a100a01000509100a12060036054f09100a01060009100a0100363b05470e09100a0106004f1517100a01000509170a017a00050910790a0b000509100a0106006e050910300a1c01060509104a0a010005094310210a010605094324170a010005520d09100a01000509100a0178000509100a1c770005
|12=>0x100050910012506000509100a0106000f050910730a0b01000510300a01350600050910210100440509100a012700050910460a12010005095e10020a0100050929100a010600050910210a0b01060903100a010044050910460a1c0b0005470e09100a1c000509103021010044050903100a0155000509100a010008050910
|13=>0x1005c051509100a010636050910810a0100051680100a0100050910460a010605091057300a01000509107e0a0100050d0924100a01060509104a0a1c01000509100a014d0005091002017d0005094307100a010605511509170a010005091057730a01000509100a017b0005100a0135060005520917100a01000509431002
|14=>0x20a0135000509100a018400051609030a0106000509100a83010005281609100a01000509101a30210100050d091001250005160903240a01000509100a0122060005090a011e000509100a01670600096a240a010005091021020106095e6a100a010005091046210a0b0005090310020a01060009100a3c0106000509100a
|15=>0xa010036050910700a0100051609860a0100058509100a0106000509431021020100050910020a0106005b0d09100a012200054709100a1c0b0005094224100a010005090710020106000910450a0100050907240a01060510020a0135000509100a0169060509104a210a0100050910460a1c010605090a12011e0600051030
|16=>0x13100a01060907030a010005090310210a010605091079020100050924100a0172000509100a0100366e0509240a01065b050965100a0100051615170a01000509100a01004461051309100a018700050e09100a1200050d0903100a010005094307100201000509100a017c0605090710300106000509101a0a120005091030
|17=>0x9100a0106000509100a6b0100050910370a0100360509030a01005b05410e09100a010005098810020100050966100a0100050910210a0140000509100201060044160d100a01000509100a015506000509108a0a01000509101a0a0100610509100a0b01060044090724020100050989100a010044050924100a01063b0515
|18=>0x177000509101a210100051615100a010005510924100a01000509107f0a0100050910020a1c0100050910210a0106050924170a0100050910570a010005491509100a01000509100a018b00051609170a0100050d09100a010005091030020a01000509100a1c0106050910461a0a01000509100125000509100a1200360541
|19=>0x509100a01000509100a0b0100050910020a01000509100a12010600050910300a01000509100a017d000509100a01060044054709100a0b01000509100a01003b050910210201000509100a0106005b050910860a01000509100a010036058d09100a0100050903100a010600058c09100a0100050907100a0106000509100a
|20=>0x9100a01000509100a010600050907100a0100
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x375032502d50285023501e50195014500f500a500550005
|5,0=>0x1386133512d61276121611b61156110510a610460fe60f860f260ec60e660e060da60d460ce60c860c260bc60b750b160ab60a5609f60996093608e50895083607d60776071606b6065605f60596054504e60486042603c6
|6,0=>0x2f162ea72e372dc72d572ce72c772c072b972b272ab72a4729d7296728f72896282727b7274726d7266725f72587251724a7243723c7236622f72287221721a7213720c720571fe71f771f071e971e271dc61d571ce71c861c171ba71b461ad71a6719f71996192718b7184717d7176716f71687161715a7153714c7145713e7
|6,1=>0x4a974a2749b7494748d7486747f74787471746a7463745c7455744e74477441643a7433742c7425741e741774107409740273fb73f473ed73e673df73d873d173ca73c373bc73b573ae73a773a073997393638c7385737e73777371636a7363735c7355734e73477340733a6334632d73267320631a6313730c730572fe72f77
|6,2=>0x5797572756b7564755d7556754f75487541753a7533752c7525751e751775107509750274fb74f474ed74e674df74d964d274cb74c564be74b774b07
|7,0=>0x75c8754874d7745873d8737673077297723671b8713870b870386fc76f486ed76e676df76d786d076c886c086b976b276aa86a2869a8693768c7684867d7676766e8666865e86577650764886408638863176298621861986118609860275fa85f285ea85e375db85d385cb85c475bd75b585ad85a6759e8596858e858775807
|7,1=>0x908690178f988f278ea88e378db88d478cd78c588be78b778af88a878a08898889178898881887b6874786c8865785d8855884e78477840783888308829782188198812780a880377fb87f477ed77e587dd87d587cd87c587bd87b677af77a877a1779a7792878a8782877a8773776b87647
|8,0=>0x9e389dc79d579cd89c589be79b779af89a879a1799a7992898b7983897c7975796e7966895f7957895079497942793a8933792c7925791d8916790e8
|9,0=>0xa0679ff79f969f279eb7
|10,0=>0xa0d6
|_,_=>0
def wAt:=mkWire dB 142 222 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 8 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x90043818010941401100041c18050042801090841c18050040015090542861160604025000542801091b468180a0140015090841c18000543818050042401100542836090641401100045818090540015010043818050042815091b468180500404611005458180005424011606000150905438180005404150e060001501054403d0e06014010a0542421070600015
|1=>0xa0d84c010a068c0270a06400154305c289110004283609064001501054342b09064001517150244110054283d0e0602419010940015100f43818000540c07100642815050044001011845818091040015010841c181005400153c10c04ed00054283d0e060001501064406d1a06028050005424de0a364001501064403d0e060042500054403d01054381800054283d
|2=>0x105440010706028410500484410a00400150a0554807510545801000544c410905440010906848430b0042405010545818090542441000553815210bc28010b1542401090b404150500404012413024410905440011c4b408730a05404010d10c24190005404150930828190500438014700c3815022484001091282c01090b40429101282c01010551817210142801
|3=>0x1a060042905004581a1009400154a09c6819010a4401a09004040e170044015010694827510545441090044106131c42415010052817021c428150500408900a05440011006424190005400151c09404150100468010500468150a01424c20200428150e06024150901400151310400150900424151006428010500414011600424410d0ac2419000555001210b82801
|4=>0x910440011505424010706828410005484050a00400150a05440193010c28190005424c20200428154905c5405090052817021c428150100400150700428415201c5819100947029120ac70154a10cc005000541c1a0a1040015015284c910905458150910429023001c84150a004257a0224440011c0ac04150500404010106824150500424015e10d0c15070040401
|5=>0x5424151c05404014a05d5c010a0b4280e100640015095e8845d0a0045c2b000544001100541c180a0642841000552817210b428014605c2871010045801091044843010640015660541c1b0a10400150a364041a0005414010900440150129840ed0906800153009c28050a06400150301c28151006414010a1845818091040015094a808710a0540401160389015
|6=>0x5200c2419000553c030917440155205c0c250005484150a004040101054281a000550c172405440011210c04d9010680015092582836130042415370ac28d90106800150144804190a06800150936400150a364041a0a06800150a054287101004a827095b4401a00054c0430a06400150906800155200c5819100941401050041c15100a518172101428011501c2401
|7=>0x5518170a1c4040101218280100054281509054247101005482b5105458014109c4c710905404014700c2c25010553c030917440155700c04090a05440190706800150a614681a0005428190500440010a0d824411505424014a10c842d010551c03090b40415010044c050905441c90224c28151000425c20a5b4401a0005429b209364041a0005425b90e0680015
|8=>0x90640015010384019100a400151606024191009400151006400150d0ac24050906400150a0680401090680015100f43818010940015091b46818010a400153010c281900055482b0d104241900054041509064140101004256d000540c2b1006400150d01c241900054a82b095b4401a0005440190a05414010a00440010906804611606024410005548270d1042419
|9=>0x555c03020142815070541c010a10404d901068001500054245d10054041a0906800150500438150901424010917440152409c40011005468030a01404150e0680425000542819050040401021c42815010044085050042801240a44015100043441090640015132482415100042c270100404153009c28190005428d63009c281900054581a090640015014440015
|10=>0x100545441090055c030a0b404157c05470270100424c20a06400154f004245d1005428910a05440010d0ac24190005438180109400155700c282d0105424c20a0640015300ac84150a00434430906400151c05428710100408910a0544001103b4241a0005414010a00404150a06800151c0a404010105404010e0542405300ac84150a0040c27100640015070602841
|11=>0x100043407090640015101282c0101054285e0005440150210428151000428150500428016a004285d1005484050a00404151006428150005404ed090680015095b8401a00054041a090041401820a42c030105424411505c24010a1c414010100408050200428157f01484170a0044001090640015021c4281501005d4150121828010a05484430a0041c010a1040015
|12=>0x1606c24412110428150a00428151006800150d01c241900054242d0100404154305c28911000428150a10400154605c28710100440010a10414010930808010a05400151501c24014605484050a00428710500404011210c04190005424c20200428152117c28011005440190910400152117028011005544171600424410a01484150a004342b090640015240542441
|13=>0x5428410a05440010a0680015090681401100040015090042415100a440190005428011006400150a0546803010a408930a054041a00054401a050044001880541c030a10424010910440150a0680015131c804010106404250005424191006400150a0541c010a10424720500404010a06428410005404190a01400150106800150a5b4401a000545c03091044015
|14=>0xa00414011000440150a0b404151501424011015824010910440150906400150200428150500404011a00428050d0ac24190005404190106800150e06404250005405110a0680015010680015105b4401a0005524150e0041c03100a428150706c284100054c0072105428010a068281500054244109064001509038401900055e4151a00c04291a068001501054281a
|15=>0x5428410105428150106400150200428152110c28010a0680015090b404150906800150a00428151006800151700c40150106800150e05c04251006400150e00c04250a1040015090b804150a01428011009424010924440012105c28010a0540401
|_=>0
def oO:Nat→Nat→Nat
|4,0=>0x64c15404500e302cc0830110004
|5,0=>0x6d31a14000194c61400005c51610553148c0001354000128c0001154000000000010500000f140000e4c0000d5034100002f50a940000000000000000009cc24308101c400000000000000
|6,0=>0x4d513144b8d2b349d1243484d1e346cd183454d13200010f4430d08441110133f50fa33dccf523c8cf113b50e94398ce2437ccdb40000d74350cd040000cc4324cc6330ccbf42ed0b742d0cb042bc4ab429d0a4328889e4269096424cc8f4230c8a221cc834200c7e21e907731cd0703
|6,1=>0x7acc0007a0de53788ddf3770c0007611d53748dcf372d1c740001c34700dbd30001ba36dcdb526c51ae36a91a6468919e46709984654d914638c00063080006210000614d8235f917c25e4d7635ccd6f45ad1683594d632580d5c4564d56354914e45291464000000050913e44f09393
|6,2=>0x924e454908e4028f8a3a48d923428c122e28b0a2848912213875219485ca143844e0d4825000081ca0347fd1fc37e11f537c8dee4
|7,0=>0xc20f053c08eff3bf0ef93bd8ef33bc0eed3ba8ee73b90ee13b78edb3b60ed53b48ecf3b30ec93b18ec33b00ebd3ae8eb73ad0eb13ab8eab3aa0ea53a88e9f3a70e993a58e933a40e8e2a2ce883a14e8239fce7c39e4e7639cce7039b4e6a399ce643984e5e396ce583954e52393ce4c3
|7,1=>0x3a93e98fa33e80f9e2e6cf992e58f933e40f8d3e28f873e10f822dfcf7c3de8b773dd0f713db8f6b3da4b672d90f613d78f5c2d68b573d50f513d38f4b3d20f462d0cf403cf8b3b3ce0f353cc8f2f3cb0f293c98f233c80f1d3c68f173c50f113c38f0b3
|8,0=>0xf98be42f88be02f78bdc2f68bd82f58bd42f48bd02f38bcc2f28bc82f18bc42f08bc02ef8bbc2ee8bb82ed8bb42ec8bb02eb8bac2
|9,0=>0x3eb1fa84000fa47e81
|_,_=>0
def PO:=mkPO wAt oP oO 18 8 255 14
def pmP:Nat→Nat
|0=>0x100000190000280000400000620000c0000140000260000480000880001000001b0000340000640000c000016000028000048000088000100000180000280000480000800000e0000180000280000400000600000800000800000
|1=>0x576000ac00014c000297000522000a20001408002800004720008980011200022000042400084400108000204000404000804001000001800002200003000005f0000b80001620002840004c80009800012200023400044800088
|2=>0x41f000830001040002022004000006ed800d98001b16003020005efc00a830013bf00257e00414000800000ebf001d72003a8800709800e1100176e002800004100007bf000d7e0012200021300041000064c000bfc0015f8002bd
|3=>0x221580440f0083df8107a0020d60040ec00817f0102bf0203000402d00800701000c020010038afc0704f80e09801c11203821c05040008a97010900020afc040400062bf00857e0102000200800400a00617c00c2b80115f80229a
|4=>0x48032088afc1115d8222b9044430088820111010220be04412608822c1104502203a0440060843f81015f8200ff0401fc080268100100200070241fc0483e0090780120e80241b0044afc0895e8112b60225280448d0089180110b5
|5=>0x210d7e421a448015f900291200100400058800080800040d003e190afc3200c8482bf09057a120a5c2410a8480b50900621200842400a84800508813e1100642104f84201f081020101a5c2030b8402bf08001c0c0bfc1415f82409f
|6=>0x200158a002b828157e502a40a0508940891
|_=>0
def pmB:Nat→Nat→Nat
|4,0=>0x204020404020204
|5,0=>0x440e000211003a080204000f0004000f0000002d0026000200151c001b26000000000004041a4300000000
|6,0=>0xb9002b650b035c001a08b9a7191a00270315005715012508ae46030b04936d161600ac001a005269a52d0173156213016d1f02112d553d2e11c500003031012a6e0b01bb095e0c01021d150c000d08b73b08122c0c1f2f5b3416012936be00231539005974770409798a155851384b0101c17a06490d01080120664a9a5d0db8
|6,1=>0x179916021709330a091f0532128d194d040b031a7e001fc41666a86b1503
|7,0=>0x40b0ba410a80078f42218e5081670125a2173e50867fa0152d764256012db436896c94b46441540c892803c25f9041799ca6a36faf9b6182417b974f834c3f63929e106f7eb1413ba4487114614e8c6198877cb56a9c458b4f3c9f9b6041227582a91e70c2953542aa24ad5a2ec05984abbc964188871878b2
|8,0=>0xb39e613fc3419e405341bd85bd42a468487d61a16186b6bf4754509d6a72
|9,0=>0x414237a491
|10,0=>0x41
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 23 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_220 8 roots_220 ops++addP pm 1 dom_201 7 roots_201 ops++addP pm 2 dom_212 7 roots_212 ops++addP pm 3 dom_217 8 roots_217 ops++addP pm 4 dom_157 8 roots_157 ops++addP pm 5 dom_213 8 roots_213 ops++addP pm 6 dom_209 5 roots_209 ops++addP pm 7 dom_93 8 roots_93 ops++addP pm 8 dom_197 5 roots_197 ops++addP pm 9 dom_205 8 roots_205 ops++addP pm 10 dom_141 5 roots_141 ops++addP pm 11 dom_77 5 roots_77 ops++addP pm 12 dom_85 5 roots_85 ops++addP pm 13 dom_153 5 roots_153 ops++addP pm 14 dom_216 5 roots_216 ops++addP pm 15 dom_156 5 roots_156 ops++addP pm 16 dom_149 5 roots_149 ops++addP pm 17 dom_89 5 roots_89 ops++addP pm 18 dom_92 5 roots_92 ops++addP pm 19 dom_200 4 roots_200 ops++addP pm 20 dom_204 5 roots_204 ops++addP pm 21 dom_196 4 roots_196 ops++addP pm 22 dom_193 4 roots_193 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_221 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_156 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_193 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_220 8 s (0,roots_220.map (·&&&dom_220)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_221 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_220 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xffffffffffffffff0000000000000000,64),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_221==dom_221)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_221 gM v ys):RunD true dom_221 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_221 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 44 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 44 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 158 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 30 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 158 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 121 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 121 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 30 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 30 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 5 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_221 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_221 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_221 roots_221 goal_221 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_221
theorem lowS_221:Lower true dom_221 roots_221 goal_221 11:=S_221.noCircuit
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_slice_b [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,32,34)] (by decide +kernel) lowS_233
def dzo_196_32:=0x1100000000000000110000000000000011000000000000001100000000
def gzo_196_32:=0x1100000000000000100000000000000010000000000000000000000000
def gsh_196_32:=0x11000000000000001000000000000000100000000000000000
theorem lowS_zo_196_32_196:Lower true dzo_196_32 roots_196 gzo_196_32 4:=lower_iso_b (d1:=dom_196) (r1:=roots_196) (T1:=gsh_196_32) [(dom_196,32)] (by decide +kernel) (lower_slice_b (T:=gsh_196_32) [] (by decide +kernel) lowS_196)
def dzo_41_4:=0x303000003030
def gzo_41_4:=0x302000002000
def gsh_41_4:=0x30200000200
theorem lowS_zo_41_4_41:Lower true dzo_41_4 roots_41 gzo_41_4 4:=lower_iso_b (d1:=dom_41) (r1:=roots_41) (T1:=gsh_41_4) [(dom_41,4)] (by decide +kernel) (lower_slice_b (T:=gsh_41_4) [] (by decide +kernel) lowS_41)
def dzo_233_4:=0x303000003030000030300000303000003030000030300000303000003030
def gzo_233_4:=0x303000003030000030300000303000003030000030300000302000002000
def gsh_233_4:=0x30300000303000003030000030300000303000003030000030200000200
theorem lowS_zo_233_4_41:Lower true dzo_233_4 roots_233 gzo_233_4 6:=lower_iso_b (d1:=dom_233) (r1:=roots_233) (T1:=gsh_233_4) [(dom_233,4)] (by decide +kernel) (lower_slice_b (T:=gsh_233_4) [(0x30300000303000000000000000000000303000003030000000000000000,0,64),(0x30300000303000003030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
def dzo_204_32:=0x111100000000000011110000000000001111000000000000111100000000
def gzo_204_32:=0x111100000000000011100000000000001110000000000000110000000000
def gsh_204_32:=0x1111000000000000111000000000000011100000000000001100
theorem lowS_zo_204_32_196:Lower true dzo_204_32 roots_204 gzo_204_32 5:=lower_iso_b (d1:=dom_204) (r1:=roots_204) (T1:=gsh_204_32) [(dom_204,32)] (by decide +kernel) (lower_slice_b (T:=gsh_204_32) [(0x1100000000000000110000000000000011000000000000001100,0,8)] (by decide +kernel) lowS_196)
def dzo_197_32:=0x3300000000000000330000000000000033000000000000003300000000
def gzo_197_32:=0x3300000000000000320000000000000032000000000000002200000000
def gsh_197_32:=0x33000000000000003200000000000000320000000000000022
theorem lowS_zo_197_32_196:Lower true dzo_197_32 roots_197 gzo_197_32 5:=lower_iso_b (d1:=dom_197) (r1:=roots_197) (T1:=gsh_197_32) [(dom_197,32)] (by decide +kernel) (lower_slice_b (T:=gsh_197_32) [(0x22000000000000002200000000000000220000000000000022,0,1)] (by decide +kernel) lowS_196)
def dzo_205_32:=0x333300000000000033330000000000003333000000000000333300000000
def gzo_205_32:=0x333300000000000033320000000000003332000000000000332200000000
def gsh_205_32:=0x3333000000000000333200000000000033320000000000003322
theorem lowS_zo_205_32_196:Lower true dzo_205_32 roots_205 gzo_205_32 6:=lower_iso_b (d1:=dom_205) (r1:=roots_205) (T1:=gsh_205_32) [(dom_205,32)] (by decide +kernel) (lower_slice_b (T:=gsh_205_32) [(0x2222000000000000222200000000000022220000000000002222,0,1),(0x3300000000000000330000000000000033000000000000003300,0,8)] (by decide +kernel) lowS_196)
def dzo_169_4:=0x30300000303000000000000000000000303000003030
def gzo_169_4:=0x30300000303000000000000000000000302000002000
def gsh_169_4:=0x3030000030300000000000000000000030200000200
theorem lowS_zo_169_4_41:Lower true dzo_169_4 roots_169 gzo_169_4 5:=lower_iso_b (d1:=dom_169) (r1:=roots_169) (T1:=gsh_169_4) [(dom_169,4)] (by decide +kernel) (lower_slice_b (T:=gsh_169_4) [(0x3030000030300000000000000000000000000000000,0,128)] (by decide +kernel) lowS_41)
namespace S_237
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(8,9),(8,40),(8,72),(8,136),(12,13),(12,44),(12,76),(12,140),(32,33),(32,40),(36,37),(36,44),(36,100),(36,164),(64,65),(64,68),(64,72),(64,192),(96,97),(96,100),(96,104),(96,224),(128,129),(128,132),(128,136),(128,192),(160,161),(160,164),(160,168),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_237.map (·&&&dom_237)
def gM:=goal_237&&&dom_237
def NN:Nat→Nat
|4=>3
|5=>12
|6=>20
|7=>13
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xb45bc8f7165b08a
|5,0=>0x9feb17a6cb772836b82562cfc5fd3249ff744ad337de72a2d80f2dd0130e
|6,0=>0xf5e34f4ce5a04357a2d5745ae734975d2d95b03b46ee63c82b316a92723b155bd107fb0bde50b586094f0077fc06d2603293
|7,0=>0x8d186869345768150104435b23f6603e8e7343353378a24c36243c41b2d21801f
|8,0=>0xbad384e2f64664b
|9,0=>0xf0cad
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc0000cccc00008888000088880000cccc0000cccc000088880000888803300000033000000330000003300000022000000220000002200000022cccc0000cccc0000cccc0000cccc0000cc000000cc000000cc000000cc0333300003333000033330000333300003333000033330000222200002222cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc02222000022220000222200002222000022220000222200002222000022220c0c0000cc8c00000c0c0000cc8c00000c0c0000cc8c000000000000cc8b33300003333000000000000000000003333000033330000000000000000cccc0000cccc0000cccc0000cccc0000000000000000000000000000000332200003322000033220000332200003322000033220000332200003322cccc0000cccc0000cccc0000cccc0000cccc0000cccc000000000000000333300000000000033330000000000003333000000000000333300000000cccc0000cccc0000cc000000cc000000cccc0000cccc0000cc000000cc0303000003030000030300000303000003030000030300000303000003030cccc0000cccc0000cccc0000cccc0000888800008888000088880000888b33300003333000022220000222200003300000033000000220000002200
|0,1=>0xcccc0000cccc00000000000000000000cc880000cc8b33300003333000033330000333300003333000033330000330000003300cccc0000cccc0000cccc0000cccc000000000000cc88000000000000cc8b33300003333000033330000333300003333000000000000333300000000ccc00000ccc00000ccc00000ccc00000ccc00000ccc00000ccc00000ccc3333000033330000333300003333000033330000333300003333000000004444000044440000440000004400000044440000444400004400000044033330000333300003333000033330000111100001111000011000000110000000000000000000000000000000000cccc0000cccc000088880000888b33300003333000033000000330000002222000022220000220000002200cc8c0000cc8c0000cc8c0000cc8c0000cc8c0000cc8c0000cc880000cc88000000033220000000000003322000000000000332200000000000033220c0c00000c0c00000c0c00000c0c00000c0c00000c0c000000000000000110100001101000011010000110100001101000011010000110000001100ccc80000ccc80000ccc80000ccc80000ccc80000ccc80000ccc80000cccb33300003333000000000000332200003333000033330000000000003322
|0,2=>0x3333000033330000333300000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cc880000cc8800000000000000011110000111100000000000000000000110000001100cccc0000cccc0000cccc000000000000cccc0000cccc0000cccc000000032320000323200003232000032320000323200003232000032320000323200c8000000c8000000c8000000c8000000c8000000c8000000c8000000cb33300003333000033330000333300003322000033220000332200003322
|_,_=>0
def sP:Nat→Nat
|0=>0x20418b08c20768b08f28710b08a6451c42c229820710d2c23c12040cb0972871063423c510d08a5881152ca2071033423c11060802072ca5084c710334230a10b29220711134120b08a4051c42c23ce14418d08c20b2892071060801440c2040
|1=>0x8a3881c478b08a20710b2884c798b08a20771b2ca20710d2c228520b08a5052071252c22881c42c22a42078cb08c3ca1c418d08120418d08f20710b3e120711f2c22881c42c22802071062c204520478b08128811b0cf2872c229d20771b34a
|2=>0x10b08a20710b08a1481c40cb08a20770b08a2071062c22852071112ca20710d2c23ca2071033422881e30cb08a1c40cb88a20712034b08a20710b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x283129888c3e61c30c9858c26610a86d82ac0f6
|6,0=>0x6a3b35d8cebf75cb2c9d58ca574f3a5dd20e8a64231fd4f0e72635b991cbae567
|7,0=>0x12c893347a22ef116853c0a1f6ef477733a19c4cdb7
|8,0=>0x505e74f346
|9,0=>0x1486
|_,_=>0
def wAt:=mkWire dB 39 238 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34f4a212c748113c74a211ca472d28b4a2d20a622f08a60231c64a2d34f0a212c74a2d2074b152074b2120a422d1d4441a2ca4b1d08b441d3c748292ca441528847210cacb211c8591d0cac82d3c7c82928b47210430b212874d3c20a472d14a481d18247291cb4a2d20741211ca4a2d
|1=>0x2074b211074b292075b2908b4a212c74b1d2c84b21108482d08a4d291cb412f1ca4b152074216207631f108422d1074b1d20747211068a2d
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x20434c000001460004100008800018803
|6,0=>0x806f4c003a36e6d8599b035a6ac94926346680ce99a32e650c00122
|7,0=>0x5b2b255caa9532a253ca694b29251ca29432
|8,0=>0x17c6f0dd1
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0x20317f2030671098771090731010670fb2ff0732ff06106f02002700987300500100315e001c7f00187700107f00106700103e00083100046f0004180003f000005900004800002800002200001800001400001200001100000e000008000000
|1=>0x80844e80106f53106f44503d42107f3030d6203267
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3070000801002c0044
|6,0=>0x54a00e34650944c1615da123203184
|7,0=>0x1380f7247e695d7a2656
|8,0=>0x126d8
|9,0=>0x10
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 24 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_233 8 roots_233 ops++addP pm 1 dom_229 7 roots_229 ops++addP pm 2 dom_236 7 roots_236 ops++addP pm 3 dzo_196_32 4 roots_196 ops++addP pm 4 dzo_41_4 4 roots_41 ops++addP pm 5 dom_109 7 roots_109 ops++addP pm 6 dom_205 8 roots_205 ops++addP pm 7 dom_225 5 roots_225 ops++addP pm 8 dom_232 5 roots_232 ops++addP pm 9 dzo_105_4 5 roots_105 ops++addP pm 10 dom_196 4 roots_196 ops++addP pm 11 dom_41 4 roots_41 ops++addP pm 12 dom_173 7 roots_173 ops++addP pm 13 dzo_233_4 6 roots_233 ops++addP pm 14 dzo_204_32 5 roots_204 ops++addP pm 15 dom_101 4 roots_101 ops++addP pm 16 dzo_197_32 5 roots_197 ops++addP pm 17 dzo_205_32 6 roots_205 ops++addP pm 18 dom_77 5 roots_77 ops++addP pm 19 dom_201 7 roots_201 ops++addP pm 20 dom_165 4 roots_165 ops++addP pm 21 dzo_169_4 5 roots_169 ops++addP pm 22 dom_141 5 roots_141 ops++addP pm 23 dom_108 4 roots_108 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_237 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_zo_196_32_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_zo_41_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_zo_105_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_233_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_204_32_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_197_32_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_205_32_196 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_169_4_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_108 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_233 8 s (0,roots_233.map (·&&&dom_233)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_237 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_233 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffffffffffffffff0000000000000000,64),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_237==dom_237)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_237 gM v ys):RunD true dom_237 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_237 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 20 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 20 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_237 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_208_32:=0x1000100000000000100010000000000010001000000000001000100000000
def gzo_208_32:=0x1000100000000000100000000000000010000000000000000000000000000
def gsh_208_32:=0x10001000000000001000000000000000100000000000000000000
theorem lowS_zo_208_32_208:Lower true dzo_208_32 roots_208 gzo_208_32 4:=lower_iso_b (d1:=dom_208) (r1:=roots_208) (T1:=gsh_208_32) [(dom_208,32)] (by decide +kernel) (lower_slice_b (T:=gsh_208_32) [] (by decide +kernel) lowS_208)
def dzo_209_32:=0x3000300000000000300030000000000030003000000000003000300000000
def gzo_209_32:=0x3000300000000000300020000000000030002000000000002000200000000
def gsh_209_32:=0x30003000000000003000200000000000300020000000000020002
theorem lowS_zo_209_32_208:Lower true dzo_209_32 roots_209 gzo_209_32 5:=lower_iso_b (d1:=dom_209) (r1:=roots_209) (T1:=gsh_209_32) [(dom_209,32)] (by decide +kernel) (lower_slice_b (T:=gsh_209_32) [(0x20002000000000002000200000000000200020000000000020002,0,1)] (by decide +kernel) lowS_208)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500040000000000050004000000000004000400000000
def gsh_210_32:=0x50005000000000005000400000000000500040000000000040004
theorem lowS_zo_210_32_208:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso_b (d1:=dom_210) (r1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (lower_slice_b (T:=gsh_210_32) [(0x40004000000000004000400000000000400040000000000040004,0,2)] (by decide +kernel) lowS_208)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e00000000
def gsh_211_32:=0xf000f00000000000f000e00000000000f000e00000000000e000e
theorem lowS_zo_211_32_208:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xc000c00000000000c000c00000000000c000c00000000000c000c,0,2)] (by decide +kernel) lowS_208)
namespace S_243
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,67),(3,131),(16,18),(16,80),(16,144),(17,19),(17,49),(17,81),(17,145),(32,33),(32,34),(48,49),(48,50),(48,112),(48,176),(64,65),(64,80),(64,192),(66,67),(66,82),(66,98),(66,194),(96,97),(96,98),(96,112),(96,224),(128,129),(128,130),(128,144),(128,192),(160,161),(160,162),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_243.map (·&&&dom_243)
def gM:=goal_243&&&dom_243
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xa606c74ec26e783653665b8855a329586053c68e3bc701ed6b18af3
|5,0=>0xf69d9f2a83e1bcddf375de708d6babd5df0d4894cddeccb228cad50c79e8ba652b6c27b410fb0f87ad6a6ad26caa128a6ecfa2a13a1211a10a49fcb598c929513293f21903678d6338ba768951a86d5a84b4283e0182f1b81cf780b897ea9d71d986fdd86bd836b60668e866613565689646c0623865e47f5beeb5ae955972e55af6522f0517c551055506494fba8495d0491b841bd23f8e33ceb23bbed37f263782a3765936dd936ce033c4b32d89305c8301b52f96d2a7af2a6c22917a28eaf28686285f2278a425f61240ef2224820aa11e14e1d68b126510b61907dbc0716405a3c04e2f03071026e1023f001fb9
|6,0=>0x51fcf4fb4b4f5724e8544da314ce5c4cbf84b4134ad044977c46de143f3a437d041ca4412ae3f1c33e0503cbf43c8403c3c63c1df3b64b39a003919438bd73826b3782a35e8735c4f35ac534a4e335e63214231f153125b3123830c18304862fbcc2f6812f07d2d8142d64a2c3f92ae8c2a47d298a728e5b28cef28bff2878b284e52752526a8b23da7228a4218d420aa11ed451da421d7d51d39d1cf751cb851c5371bed01bbbb1b2331ae2a19f1b193b1185ef1838f1787417354156ab154871547c14ddc14baf135b51356c1312712b10127de115af114d110b08109fd109a6107ed1043c101b80f8c40f48d0ef940eee00ed210d8560c9e30c78f0bf7d0bc8b0b4620b1930af070a91d0a555092470923708dc908821084f7083be078650716406f2006909068f40672e0668d05fdf03d1302d18028f1016cd00c2c009b6
|6,1=>0xbd7f4bc14dbbce3babccb929fb7759b6d56b668bb5d2fb4836b3a59b3580b26aeb23b7b2285b1e75b1b8fb1671aed7cae5b0ae00bace4cabac1aad80a98e8a902fa6c05a60e0a58d8a4535a1957a09569e9d89cdca9cdbb99cb999c8298cbe98c9295e6495b12952eb93b209300891f6591b799162d8eb698eab88af558755e86d5a8657c852248486c81a307ea797d8b27d3647be6e7b71d7ab687ab2e7a08878715785627798277227767d6752f974e747418e73c3a71ac17062d6ed976ea856e26e6db356d6e66c3c06c3b36c1bd6bb476b8ed6ad626a76e699a06948867dbf65fa465ba7656316533864d23642c0639cd620a16179c5fcfe5f2755d5a45cb855c97a5bb02599f05972e59200587f8584775823a57fdd57fc756ac5568b9562e25597f5524354fcf54f1354b725447f5433553da95385f52b195289552299
|6,2=>0xfd072f53fdf0b0cf0ac7f0154ece3cea6eae86c2e850fe8291e58bce25a9de862d98add7f91d2a9fcf2a5ce638cb5d3c7ffcc7444c4d94c2dfbc2dc1c2981c0fa2bf8f1bf7d9be383be349
|7,0=>0xeffd5ec2f9d79eacfd02cc6e6cb13ecaeddbdeeebddd7bbc98bb3a5b7f75b50efae1f0ad74baced8a4535a2ab9a0e129dbc69b901963b5917fd8fc0284d77845c87f8977f3de7e4717b89a78d6c77b5776ef176e2374c4a7439472bae71868703026f8906f5776e591648ab6442f62f6c628e962108607d25ffa25fc665edc45ece35d4155cb7c5c8c95bf8e5b1795b0375b0175aa695a65f59cbe59c5158ef85866b565b85577e54f1f538f65191450f264de834da5e4c1b1465b84562a450bc43b3643ad53e0503d8cd37d4736c0f35c4f3586e34f363361e31b27306e82f07d2e2d52b91d28cdc21ed21fad41a64b1838f17a9717543150311352e131dd130bf1143e10b08100220ffd40ef800dcf70d9880c0150b55c0b4360ae6109a1708ee3073020691106256059aa0599d0467f0360702a06016140108400d7c00966
|7,1=>0xfec70f9951
|8,0=>0xd70edcdcdec8a36bbc98aed33a25797a9f6762ce6c50a66535655b06340b3d1cf22ce7227e01972117c560fc84
|9,0=>0x7a9f6
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000a000f000a000f000a000f000a000f000a000f000a000f000a000f000af000f000f000f000f0000000f0000000a000a000a000a000a0000000a0000f000f000f000f000e000e000e000e000f000a000f000a000e000a000e000af0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f000f000f000f000c000c000c000c000a000a000a000a0008000800080008f000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000ef000a000f000a000c0008000c0008000f000a000f000a000c0008000c0008f000f000f000f000f000f000f000f00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f00000000000f000f0000000000000000000000000000000000000000f000f000f000f000f0000000f00000000f0000000f000f0000000f00000000000f0000000f000f0000000f0000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a
|0,1=>0xf0005000f0005000f0000000f0000000f0005000f0005000f0000000f0000f0000000f0000000f0000000f0000000f0000000f0000000c0000000c0000f000f000f000f0000000000000000000f000a000f000a0000000000000000f000f000f000f000f000f000f000f000f0000000f000f0000000000000000f000f000f000f000f000f000f000f000f000f00000000000f000f000500000000f0000000f0000000f0000000f0000000d0000000d0000000c0000000c5000500050005000500050005000500050005000500050005000500050000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f000f000f000f000f000f000f000f000f000f0000000f000f00000000f000f000f000f000f000f000f000f000a000a000a000a000a000a000a000af000f000f000f000c000c000c000c000f000f000f000f000c000c000c000cf000f000f000f000f0000000f0000000c000c000c000c000c0000000c0000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000a000f000a000f000a000f000a000f000a000f000a0000000000000000000000000000000000000000000000000000f0000000f000f0000000f0000
|0,2=>0x50000000500000005000000050000000500000005000000050000000500000000f0000000f00000000000000000000000f0000000f00000000000000000000000000000000000000000000000050005000500050005000000050000f000f000f0000000f000f00000000000f000f000f0000000f000f00050000a000a000a000a000f000f000f000f0008000800080008000c000c000c000cf000e000f000e000f000e000f000e000f000e000f000e000c000c000c000c00000000000000000000000000000000f000f000f000f0003000000030000c000c000c000c000c000c000c000c000f000f000f000f000c000c000c000cf000f000f000f000f000f000f000f000c000c000c000c000c000c000c000c30003000300030003000300030003000300030003000300000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000c0000000c0000000000000000f000f000f000f0000000000000000000f000e000f000ea000a000a000a000f000a000f000a000a000a000a000a000f000a000f000a0000000000000000f000f000f000f0000000000000000000a000a000a000af000f000f000f000f000f000f000f000a000f00000000000a000f000000005000500050005000000000000000000050005000500050000000000000000
|0,3=>0xf000f000f000f0000000000000000000f000c000f000c0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000c000c000c000cf0003000f0003000f0000000f0000000f0003000f0003000f0000000f00007000500070005000300000003000000070005000700050003000000030000f000f000f000f000f000f000f000f00000000000000000000000f00000000f0000000f00000000000000000000000f0000000f00000000000000000000f000f000f000f000f000a000f000a000f000f000f000f000f000a000f000af000f000f000f000f000f000f000f00050000000500000005000000050000f000f000f000f000a000f000a000f000f000f00000000000a000f00000000f000f000f000f000f000f000f000f000f0000000f000000000000000000005000500050005000500000005000000050005000500050005000000050000f000f000f000f000f000f000f000f000f000f00030003000f000f00000000000000000000000020002000200020000000a0000000a0002000a0002000ac000c000c000c000c000c000c000c000f000f000f000f000f000c000f000cf000f000f000f0000000000000000000b000a000b000a0000000000000000f000f000f000f000f000e000f000e00000000000000000000000000000000
|0,4=>0xf0000000f00000000000000000000000f0000000f000f0000000f00000000f0000000f0000000c0000000c0000000f0000000f0000000c0000000c0000000000000000b000b000b000b0000000000000000000b000a000b000ab000b000b000b0000000000000000000b000a000b000a0000000000000000f000f00000000000f000f00000000000f000f00000003000f000f000000000000000000000000f000f000f000f0000000000000000000c000c000c000cf000f000f000f0000000000000000000f000e000f000e0000000000000000f000c000f000c000c000c000c000c000f000c000f000f000c000c000c000cf000e000f000e000f000e000f000e000f000e000f000e000f000e000f000ef0000000f0000000f000f000f000f000f0000000f0000000f000a000f000a0000000000000000f0000000f00000000000000000000000f0000000f0000f000f00000000000f000f00050005000f000f00000000000f000f00050000f000f000f000f000c000c000c000c000f000c000f000c000c000c000c000cf000c000f000c000f000c000f000c000f000c000f000c000f000c000f000cf000f000f000f000c000c000c000c000f0000000f0000000c0000000c0000f000f000f000a000f000f000f000a000f000f000f000a000f000f00000000
|0,5=>0x300030003000300030000000300000003000300030003000300000003000000000000000000000000000000000000f0005000f0005000f0000000f0000c000c000c000c000c000c000c000c000f000e000f000e000f000e000f000e00000000000000000000000000000000f000f000f000f000f000e000f000e0000000000000000f000a000f000a0000000000000000000f000a000f000a00000000000000000000000000000000f0003000f0003000f0000000f0000f000f000f000f000f000f000f000f0000000f0000000f000f0000000f0000f000f000f000f000f0000000f0000000f000c000f000c000f0000000f00000000f0000000f000f000f000f000f0000000f0000000f000f0000000f0000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f000000000000000000000000000000000000f000f000f000f000f000a000f000a0000f0000000f0000000f0000000f0000000c0000000c0000000c0000000cf000f000f000f000a000a000a000a000f000a000f000a000a000a000a000a5000500000005000500050000000500050005000000050005000500000000f000a000f000a000f000a000f000a000c0008000c0008000c0008000c00080000000000000000f000f000f000f0000000000000000000f000a000f000a
|0,6=>0x30003000300030000000000000000f000f00000000000f000f00000000000c000c00000000000f000f00000000d000d000d000d000c000c000c000c000d000d000d000d000c000c000c000cc000f000c000f000c000c000c000c000c000f000c000f000c000c000c000c0000f0000000f0000000f0000000f0000000a0000000a0000000a0000000a0000f0000000f0000000f0000000f0000000f000000000000000f00000000f0000000f00000000000000000000000f0000000f000f000000000000000000000000000000000000000000000000f0000000f0000000f0000000f00003000300030003000300030003000300030000000300000003000000030000f000f000f000f000f000c000f000c000f000f000f000f000f000c000f000cc000f000c000f000c000f000c000f000c000f000c000f0000000000000000f000f0000000f000f000f0000000f000f000f0000000f000f000f00000000f000f000f000f0000000000000000000f0000000f000000000000000000000000000000000000f000f000000000000000f00000000000f000f00000000f000f000f000f000f000f000f000f00030003000300030003000000030000f0000000f0000000f000f000f000f000f0000000f0000000f000f000f0000
|0,7=>0xf000e000f000e0000000000000000000f000e000f000e0000500000005000000040000000400000005000000050000000400000004f0000000f0000000f0000000f0000000f0000000f0000000a0000000a0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000000000000000300030003000300000000000000000002000200020002f0000000f000f000f0000000f000f000f0000000f000f000f0000000f0000a000f00000000000a000f00000000000a000f00000000000a000f000000000000000000000000f000f000f000f0000000000000000000f0000000f00000000000000000000000000000000000050000000500000005000000050000f000f00000000000f000f00000000000f000f00050000000f000f00050000300000003000000030000000300000003000000030000000300000003000000000000000000000000000000000000f000f000f000f0000000000000000f0000000f0000000f0000000f0000000f000f000f000f000f0000000f00005000500050005000400040004000400050005000500050004000400040004f0000000f0000000f0000000f0000000f0000000f000000000000000000000000c0000000c0000000c0000000c0000000c0000000c000c000c000c000c
|0,8=>0xf000f000f0000000f000f00000000000f000f000f0000000f000f00000000000000000000000000000000000000000000000000000000f0000000f0000f000f000f000f0000000000000000000f000f000f000f000f0000000f00000000000000000000000000000000000050005000500050004000400040004f000f000f000f000e000e000e000e000f000f000f000f000e000e000e000ef000f000f000f000f000f000f000f000f0003000f0003000f0000000f0000f000f000f000f000f0000000f0000000f000f00000000000f0000000000005000500050005000500040005000400050005000500050005000400050004f000f000f000f000f000f000f000f0000000f0000000f00000000000000000000f0000000f00000000000000000000000f000f000f0000000000000000f000f00000000000f000f00000000000f000f000f000f000f000f000f0000b000b000b000b000b000a000b000a000b000b000b000b000b000a000b000af000c000f000c000f000c000f000c000f000f000f000f000f000c000f000cf000f000f000f000f000f000f000f000b000a000b000a000b000a000b000af000f000f000f000f000f000f000f000f000f000f0000000f000f000f00003000300030003000300030003000300030003000300000003000300030000
|0,9=>0xf0000000f0000000f0000000f0000000f0000000f0000000f00000000f0000000f00000000000000000000000f0003000f00030000000000000000c000c000c000c000f000f000f000f000c000c000c000c000f000c000f000ca0000000a0000000a0000000a0000000a0000000a0000000f0000000f0000f000f000f000f000f000f000f000f000e000e000e000e000e000e000e000ef000f000f000f000f000f000f000f000f000e000f000e000f000e000f000ef000f000f000f0000000000000000000f000f000f000f000500000005000000000000000000000000f0000000f00000000000000000000000c0000000c30003000300030003000300030003000300030003000300030000000300003000300030003000300030003000300030003000300030002000200020002f000f000f0000000f000f000f0000000f000f000f0000000f000f000f00000000f0000000f0000000f0000000f0000000f0000000f000000000000000000000000e000e00000000000e000e00000000000e000e00000000000e000e00000000f000000000000000f000000000000000f000000000000000f0000a000a000f000a000a000a000f000a000a000a000f000a000a000a000f000af000f000f000f0000000f0000000f000f000f000f000f0000000a0000000a
|0,10=>0xf000f000f000f000f000f000f000f000f0000000f000f000f0000000f0000100010001000100010000000100000001000100010001000100000001000000000000000000000000000000000000f000f000f000f000c000c000c000cf000f000f000f000f000f000f000f000f0005000f0005000f0000000f00000000000000000000000000000000000030003000300030003000000030000f000f000f000f0003000000030000000f000f000f000f00030000000300000000f0000000f000f000f000f000f0000000f00000000000f000f00000000f0000000f0000000f0000000f0000000f000f000f000f000f000c000f000cf000f000f000f000f000f000f000f00030000000300000003000000030000f000f000f000f000f000f000f000f00030003000300030000000000000000a000f000a000f000a000e000a000e000a000f000a000f000a000e000a000ef000f00000000000f000f00050000000f000f00000000000f000f0005000000000000000000000000000000000000f000f000f000f000f000c000f000c00000000f000f000000000000000000000000000f000f0000000000000000f0000000f000f000f0000000f0000000f0000000f000f000f0000000f0000f000f000f000f000f000f000f000f000f000a000f000a000f000a000f000a
|0,11=>0xf000f000f000f000f000f000f000f000f000f000f000f000f000c000f000c00000000f000f00000000000f000f00000000000f000f00000000000f000000000000000000000000000000000000f0000000f000f000f0000000f0000f000f000f000f0000000f0000000f000f000f000f000f0000000c0000000cf000f000f000f000f000f000f000f00050005000500050000000000000000f0000000f0000000f0000000f0000000f000000000000000f000000000000f000f000f000f000f0000000f0000000f000f000f000f000f000000000000f000f000f000f000f000f000f000f00000000000f000000000000000f0000c000f000c000f000c000f000c000f000c000e000c000e000c000e000c000e00000000000000000000000000000000f000a000f000a000f000a000f000a5000500050005000500050005000500050000000500000005000000050000a0000000a0000000f0000000f0000000a0000000a0000000f0000000f00005000500050005000100000001000000050005000500050001000000010000f000f000f000f0000000000000000000c000c000c000c000000000000000000000000000000000000f0000000f00000000000000000000000f00000000f000f000f000f000f000f000f000f00000000000f000f0000000000000000
|0,12=>0xf0000000f0000000f000f000f000f000c0000000c0000000c000c000c000c0000000000000000500050005000500000000000000000004000400040004a000a000a000a000a000a000a000a000f000a000f000a000f000a000f000a0000a0000000a000a000a000a000a0000000a0000000a000a000a000a000af000f000f000f000f000f000f000f000f000c000f000c000f000c000f000c0000000000000000000000000000000000003000000030000000000000000f000f000f000f000f000f000f000f00000000000e000e00000000000e000ea000f000a000f000a000f000a000f000a000f00000000000a000f000000000000000000000000300030003000300000000000000000003000000030000f000f000f000f000f000f000f000f00000003000000030000000000000000f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a50005000500050000000000000000000f0005000f0005000f0000000f0000e000e00000000000e000e00000000000e000e00000000000e000e00000000f000f000f000f000f000f000f000f000e000e00000000000e000e0000000030003000300030003000300030003000200020002000200020002000200023000300030003000000000000000000030003000300030000000000000000
|0,13=>0xa000f000a000f000a000f000a000f000a000e000a000e000a000e000a000e3000300030003000300030003000300030002000300020003000200030002f000f000f000f000f0000000f0000000f000f000f000f000a0000000a0000f000f000f000f000f000f000f000f000a0000000a0000000f0000000f0000f000f000f000f000f000f000f000f0000000000000000000f000a000f000af000f000f000f000f000f000f0000000f000f000f000f000f000f000f000000000000000000000000000000000000f000f000f000f000f000f000f00000000000000000000c000c000c000c0000000c0000000c000c000c000c000cd000d000d000d000d000d000d000d000d000d000d000d000c000c000c000cf000f00050000000f000f00050000000f000f00050000000f000f00050000f000f000f000f0005000500050005000f000f000f000f00050000000500000000f0000000f0000000f0000000f0000000f0000000f0000000a0000000a0000000000000000500000005000000000000000000000005000000050000f000f00000000000f000f000f000f000f000000000000000f0000000f0000f000f00030003000f000f00030003000f000f00030003000f000f00000000b000b000b000b000b000b000b000b000b000b000b000b000a000a000a000a
|0,14=>0x5000500050005000500050005000500040004000400040004000400040004f0005000f0005000f0005000f0005000f0004000f0004000f0004000f0004f0005000f0005000f0004000f0004000f0005000f0005000f0004000f0004f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000050005000500050005000500050005000500050005000500050005000000003000000030000000300000003000000030003000300030003000000030000000000000000000000000000000000000000f0000000f0000000c0000000ca000a000a000a000a000a000a000a000a000a000a000a000f000a000f000aa000a000a000a000f000f000f000f000a000a000a000a000f000a000f000a0000000000000000f000f000f000f0000000000000000000e000e000e000ef000d000f000d000f000c000f000c000f000d000f000d000f000c000f000c1000100010001000100010001000100010001000100010000000000000000f000f000f000f000f000f00000000000f000f000f0000000f000f00000000f000f000f000f000f000f000f000f0003000200030002000300020003000200000000000000000000000000000000c000f000c000f000000000000000000000000000000000000000000000000f000e000f000e000f000e000f000e
|0,15=>0xf000f000f000f000f000e000f000e000f000f000f000f000f000e000f000e0000f00000000000f000f000000000000000f00000000000f000f00000000f000f000f000f000f000f000f000f0000000f00000000000f000f00000000f0005000f0005000f0005000f0005000f0005000f0005000f0000000f0000f000f000f000f0005000500050005000f000f000f000f0004000400040004000030000000300000003000000030000000300000003000000000000000000000000f000f00000000000f000000000000000f000f00000000000f0000f000f000f000f000f000f000f000f00000000000f000f00000000000f0000f000f000f000f0000000f0000000f000f000f000000000000000f00000000f000f000f000f000f000f000f000f000c000f000c000f000c000c000c000cc000c00000000000c000c00000000000c000c00000000000f000f00000000f000f000f000f0005000000050000000f000f000f000f0005000000050000b000a000b000a000b000a000b000a000b000a000b000a000b000a000b000ac000c000c000c000f000f000f000f000c0000000c0000000f0000000f00000000000000000000000000000000000000000000f000f00000000000f0000f000c000f000c000c000c000c000c000f000c000f000c000c000c000c000c
|1,0=>0xc000c00000000000f000f00000000000c000c00000000000f000f000000000000000000000000f000f000f000f0000000000000000000f000f00000000f0000000f0000000f0000000f00000000000000000000000f0000000f0000000000000000000000000000000000000000f0000000f00000000000000000000f0000000f000f000f000f000f00000000000000000000000000000000f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000ac000f000c000f0000000000000000000c000f000c000f000000000000000000000000000000000000000000000000f000f00000000000f000f00000000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000c000c00000000000c000c000c000c000c000c00000000000c000c000c000cf0000000f0000000f0000000f0000000a0000000a0000000a0000000a000000000000f000f00000000000f000f00000000000f000f0000000000000000f000f00030003000f000f00000000000f000f00030003000f000f00000000c000c000f000f000c000c000c000c000c000c000f000f000c000c000c000c30002000300020003000200030002000300020003000200030002000300025000500050005000500050005000500050005000500050000000000000000
|1,1=>0xf000f000f000f00000000000f0000000f000f000f000f00000000000f0000
|_,_=>0
def sP:Nat→Nat
|0=>0x2824480c008000a091183002220281018010b0003a0c008842c000c0243e130080014090087800180282418010003814090601c021d02810180100060381b0600400180282402000d0600a090600432180285c10100080012080085822040605428000484c0212088101010008000802080040009078041c0a048301a01050241807058281208038180a04018080200
|1=>0x1b8003005020300200070601208008006c09098040035050d01827008003009060046618028241e080085814041903002000c0241801000c40a09060040018180100601000bc3004060544e00170101801000b4302c06004001802810460c0085830090601c561802824182a000600a040600400290c01018281380030090784c0212050241013008004c09008004a18
|2=>0xc0241801001240a040100400050203c10010b060080c2400030050200c18150080012470989c00180480c04010001412462280400052203002000c014120c2180030050490882000c014800c0080030050483c260713860120c0a8007e0504820263e00800123d09804000a048300e3c0c014080c008007618020200601000e8123909804000a0482002001c0281801
|3=>0x6004a60a0484c02000c04412080800400050483002520c014120208004000504820260100028120c0394430050202002001b0241001030000a04280300216000241807030600a090400c02001b010060c0080030090413c0200028241e08038540a09040040011028101827001383009060049a0002824720c00858140906004004c0292c1801000600a092104c9400
|4=>0x28101801000606c092e83002000c014125c060040018049581001000d8120c0085830110496c0200270142e08008006c042d03002000c0241059008000a092c808020002824b00c0a8000a090415c0200028241010008006c092b00802000282484131f00030042a83002000c02418150a0000a041c83002160c0242a002a0b80a0906004000b050101002008000a09
|5=>0x800306902824d001000d43005048300e00338600a0933030005f0c014120c00800306502810182700800302e0491c18010b0600a09210307c000c01412010f0003005320241801000600a0904030500100014c40c008003005048300251000600a090600400610c014c004060040018028241013008001418048300e002f8600a092f03002000c0141247060540018
|6=>0x1ec3005048300e4a000600a093d03002000c014180110800300504908186d000600a092d83002160c014120c0a804002202824cc0c1380030050483cf001000600a76060042c000c014121300800ea0a0c024e60c0a8040005048080200028241801001c8140504830e0000c014dc0c13804001802824186d13800300504830d827000600a0906004246b0c014080c
|7=>0x2824180142000300504a0c1801000600a040403002000c014120c00a080018028244e01000943005020300216001dc300906001001802824fe0c008003005048308601000600a6e06004001802824ac0c0a80400050202018010b000300906004007e0c014120f228042c18028241801001f430053e0241801000600a091c9a002000c0141208098040018028241801
|8=>0x780c02000c0152a09008003094028300200498283005048300291050600a090600400900c0142e0c0080030050480400250c014120c0094c300504a341801000280a0906004008c0c014120c458042c18028241827001c8300504a281801000600a092d03002000c014080c448040018028241801002203005048302a010021c0a04060040018430150a09060040018
|9=>0x2825421300800300504a801801000283009040300e1500014120c008013e1802810cc0c0080030050483002000c2780a091184c02000c014127306004001802824840c0a800140504a741801000600a04061b002000c014120c4e004001802825340c0080030050483002004c8600a090600400980c014120c008012e1802824cc130080030050483002004b0600a09
|10=>0x210315a000c01412ac06004001802825400c008003005048300e750c0800a090600400ab0c01412a0040040018028241878008014405048300200550280a045483002000c014120c1f004002e02825500c008003005048300e00538600a09040040036048201801002980a092b03002000c014120c00a94001802a901801000600a090983002000c21c12a3060040018
|11=>0xf00030050483002005e0600a090983002000e81412130600400185d81018b90080030050483002005c02830090a8043c000c014120c5b8040018028256c0800800300504820040100014120c008016a0a0c02426b40080030050b83002000c0d8120c008016618028241815002c80a040600400b10c01412af060040018028241801002b830050483c1001000280a09
|12=>0x28241801000618c050483086000c014125b060540200028241801208003005049082615000600a04060058a1600060120c00858001d028241001002d4300504b101801000600a0c610040018028241e0c00b0430050484c1801000614c095f83002000c014121f06004000a0282418070085814180483002005f0600a04062d002000c01412bd060040018028247c01
|13=>0x5061a20c0080030050483002d0000600a090a80400250c014080f060042c180483002cf000600a090600400ce0c01412cd060042418028241013138040018048313615000600a092104c4e000c02418010009430050203002cc0c014120f09804000a0c010840c0a8003005048300e3e000600a090600400186501418010032430050600590000c014120c008018e18
|14=>0x5483002000c015ac0c008001418028240601000bc30050487c1807008600a040782002000c014080c00801a618029d81801000600a090600400d50c014120c22804002202824260c0092800180483002006a0600a040600400aa0c014123e008004a1802825960c0a80030050484c0200698600a090634802000c01408420609c0018048305027000600a09099140200
|15=>0xbc14050483002000c3840a090400c02001d014080306004001804b801801000600a090601c2a0005014120c008006a0a0282418016f8003005048302a002a0600a0906004000e0c014120c00801bc1802824180100374300504831b801000600a096d83002000c015b2090600400180282418d8000600a091903002000c014080c1f09c02000c02418d7008003005
|16=>0x606c090600400aa3a014120f060042c0a0c0241e0c0389c300504831cc01000600a091e83002000501412e5060040018028241801158003005048300ead000600a090404c020005024180100061c80504820060c00800140906004005f05014124206054007402b8c1801000600a0404004003a028241001001c40a0406054020017014120c00801c418028241001
|17=>0xc014120c45804000a028241801003c430050483d1c01000600a090981c00750c014080c780003005048300216000e0300909804001838825dc0c0080030050484c020017828300422804002e02825da0c0080030050483c10010b0600a0906005d60a0c014c009060040018028241801003a83005048300200748600a097403002000c01412e7060040018028241801
|18=>0x483002007c0600a090784c4e0100060080c00801ee18028101001000bc30050480c18010002830090622402000c014120c7b00400180282484130080014187a83002000c014120800800ee18028241801003d014050483002001e0600a0909805e6000c0141239098040018028101801000d43005048300200270280a09008004a0a0c01418c2008003009063c80200
|19=>0x4004003a028241e0c008d4300502024060c0080030090600400b10c014120c0389c302002825fe0c0080030057e83002000c01412560183002000c0d01801000600a092b004002f0c0141208008006c050216c1801000600a080600400930c014083d06004001802824100c0a800be0504bf01801000600a040400c180100060120c00801f61802824180100061f405
|20=>0x4830021600028300406004001860014120c0389c0018028241902000600a090983002000c2880a090600401010c014120c00b3030050484c1801000283009040302a01000600a09210302a000c014120c00800310002824720f0600400180282418ad0080030054783002000c014120c00b1400180282418010300030050483c1015008000a09078300e150c0141256
|21=>0xc0140808060040018028241e08008003005048300200698600a09330201801000600a09210300216000600a090600401050c01412470783002000c014120c008015418028241013008003005048307c150080030050483c1827008003005048201807008003005020300212000600a090400c1801000600a0906004001882014124206004000a0c016060c008003005
|22=>0x800306302b68120c00800300504a801801000600a0906004001843815d80906004000a0c0160e090983002000c0141256060040018028241001000e80a0906054020017014120c830003005048300200110600a09060a002000c0141273060040018028241801003e43005020304e0100060080c5d0040018028101801001d43005020302a01000600a09098040075
|23=>0xc014120c008006a18028241827008003020028241801002d430050482018010b0003005048302a01000283005048311c01000600a09063c0001802824186800800302002824181500800e80504914020017014120806004000a0c014120c13804001817016100f06004001802824100c00800e8050483002000c0d80a090600424160c014121306004001860014120c
|24=>0x178600a0906005e6000c014120c03804000a0c0141239060040018028241e0c0a804001802c2812130600400180282418010006212050483002000c2980a090600400b80c014124206004001810014120c03800ea18028241801000617605048307c01000283005048300200778600a09098302a01000600a09060042c003b8600a090601c2a000c014120c00800ea0a
|25=>0x643402000c014120c00800309402810184500800300502024100c0080030050496c1801000600a090600494000c014121322804001802824ac0806004001802825961306004001802824189b008580018028248e0c008003005048f41801000600a092103002000c1d00a090983002000c4300a0906004001885824100c00801f218028241e13008003005048200200
|26=>0x1f09c02000c014120c00800ee1802824100c0080030050484c0200178600a09061140200050600a090600401100c014120c00800ea1810014120f060042c1802824840c008480018028241801000606cec0483002000c015fc0c0080030050483002c50b0003005048201801000d430058783002000c01418010024c300504c381801000600ada048201801000600a09
|27=>0x48300200178600a950483002000c014120c00800302002810120c008003005048308a01000600a090600400920c014120f0600400180282418010b0003005048300200050600a040600400181d01418c3008003005840201801000600a048703002000c014120c4d804001802824186c0080030050480c1801000600a092104c02000c014125606004000a0c014120c
|28=>0x120c0080030050203002000c014120c03804001802c28120c008003005048201801000600b080600400180282418010006074050483002000c0141242060040018028241868008003005
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1af61a961a3619d61976191618b6185617f61796174516e61686162615c61566150614a6144613e61386132612c61266120611a6114610e6108610260fc60f660f150eb60e560df60d960d360cd60c760c160bb60b560af60a960a3609d60976091608b6085607f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6255524f62496243623d62376231622b6225621f62196213620d6207620161fc51f661f061ea61e461de61d861d351cd61c761c161bb61b56
|6,0=>0x422741b7414740d740673ff73f873f173ea73e373dc73d573cf63c873c173bb63b473ad73a6739f73987391738a7383737c7375736e73686361735a7353734c7345733e73377330732b5324731e631773107309730272fb72f472ed72e672df72d872d172ca72c462bd72b672b062a972a2729b7294728d7286727f727962727
|6,1=>0x5d975d275cb75c475be65b775b075aa65a3759d6596758f75887581757a7573756c7565755e7557755075497542753b7534752d75285521751a7513750d650674ff74f874f174ea74e374dc74d574ce74c774c074b974b274ab74a4749d7496748f74887481747a7473746c7465745e74586452644c6445743e7437743074297
|6,2=>0x78e77877780777a6773776c7765775e77577751674a7743773c7735772e7727772077197712770c670576fe76f866f176ea76e466dd76d676cf76c876c176bb66b476ae66a776a076997692768c6686667f76787672666b7664765d7656764f76487641763b6634762d7626761f76187611760a760375fc75f575ee75e775e07
|6,3=>0x942693b7934792d7926791f79187911790a790558fe78f778f078e978e278dc68d578cf68c878c178bb68b478ad78a6789f78987891788a7883787d6876786f78687861785a7853784c7845783f68387831782a7823781d68176811680a780377fc77f577ee77e867e177da77d377cc77c577be77b777b077a977a2779b77956
|6,4=>0xa107a097a0279fb79f479ed79e679df79d879d269cb79c569be79b869b179aa79a3799c7995798e7987798079797972796b7964795d7956794f79487
|7,0=>0xbd88bd17bcb6bc38bbc7bb66bae8ba68b9f7b987b917b8a7b828b7b7b747b6d7b667b5e8b568b4f7b496b427b3c6b357b2e7b277b207b1a6b137b0c7b057afe7af77af07ae97ae18ad98ad27aca8ac37abc7ab48aac8aa48a9d7a958a8e7a868a806a797a727a6b7a656a5d8a567a506a497a418a3a7a337a2b8a247a1e6a177
|7,1=>0xdad7da67d9f7d987d917d8a7d828d7a8d737d6c7d657d5d8d567d4e8d477d3f8d396d327d2c6d248d1c8d166d106d097d018cfa7cf37cec7ce48cdd7cd67ccf7cc78cbf8cb78cb07ca97ca18c998c936c8b8c847c7d7c767c6e8c677c5f8c578c507c497c427c3a8c337c2c7c248c1d7c158c0d8c067bfe8bf77bef8be87be08
|7,2=>0xdba7db46
|8,0=>0xe366e2f7e287e217e1b6e147e0e6e077e007df97df27deb7de47ddd7dd67dcf7dc87dc17
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 273 244 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x606006061040eb0606006061040eb06060060612b0eb0606006061040db06060060610c09d040010c0310a85800861040eb06060060610503c06001040db0606006061040eb0606006061228610c0150c032048151d015060600606106001008610606107828090310006104815040eb06060060612100100831060150985406015000310c09d090310c001040580c0310c0150601510031000620405806061
|1=>0x32000620083107863060010b063000150a8310c0050c04e06015049dd0605b0c015061d10c017040eb06060060610a80300861009c706028049bf0c09f008810c003170050606235062020330084e060150c03106062048150780506001000150c09d1f0300c09d0602a0c0170498f0c04c060150789c000310601506061040070c0310601d1d01506060048150781706060060610782806001048d91d015
|2=>0x228010c0320c0154d8312106100831040170c031050330c0150481e00801002490483247815048e9060601f0330c09d0018d0c04c060150c2390602b0c0150a85b0001500849000610c00500815020200606117015060620017d0c03122861048150c032060fa0c09d0605b408070484d06015049bf0c09f0081504015060610c0310481507856000310001504015228610c032060150c09e008153c815048bf
|3=>0x6059618150481c0080100015060156001510031000620c0150c2800004d060155d061020300c01549015060f80a81507817040eb060600606106015100320c003048d91d015060600c09c0c0050081502023060615803151015060610a817078153a86106007020eb060600c0153a815008321d01506060060610a833090320006106015060620601551031048620605900861060610c109008310c15313833
|4=>0x20eb0606004815048bd060031003100062048150c0310604b049dd0605b0c09e0c1d5008320c09d0081504815008310c09f008150c0150c03206015048990082a0c015000990c015060fa0a8150481506001000150081500061060170081500815008310601504815000eb0606004815008290c0150c32f0481e00801020bf0481500032008310098d0c04c060150786300031098540c00506015048150c280
|5=>0x601509005000610c0150602b0c015008e90c030048153b8150605b00015060280c015063bd0081504815060620c032390310086176003048290c04e060150c04c060150a817008610c015060150c0310c0150401706061060050498d0c04c0481506060060610c031060280c01504815060620606006061040170606123817008610c015040030606113833040580606107863000316d017060610098f0c04c
|6=>0xc01507861000310a81700861048e9060600b061000150785400861000310c031060600606106061040170606102023060610c003060617f015048eb060600606104a9960015008621d01506060060610481e600310086206061060610c0157c8150606100031060150606102020060610c0150489b0082a0c0150c0bd06003001d500832090310c00104003060610a83300861060fa00829618150481c09b03
|7=>0x6061048150081502030048150481500832048150086100832060150481506061000310c03109032000610c0310600500015060580001507805000310c1d500832060150c0310a81500861000310081506061048150006104017060610482a0c015060050c01504b01008620c015000150481500862000050081500a890486206015048620780700031000eb06060060150c015008610606100831008610002a
|8=>0x500861060070c01504003060610c003008150004e0601506061008610c0150602b0c015008e90c03000062060170c01700861060620c0320c015060610c0330081504817000310c017060611d0150606000061000150c007060150c04c06015048210606106059000151701506062048290c0150601504861040150606106060060610c0330086100a8b048620b063000153a0050c0173a0310c01704822
|9=>0x60613a0320c0170602a0c015048150c0320606107863000310c09e008150c03206015060610084d06015008590001507805000316003100862008310c0170c04f060151d01606060060610003106015000320c031001d500832008010c0150400106061008610003104801060150c1d70083260015008624901504832000620083100005008321001500062008290c0150009e008150c005060150605b00015
|10=>0x4817060600083106017000320483100062048150c0320483200031000150c01506060048150481c00801048170606102063048150085900015170050606204017060610083106015060290c0150c09d008150605b00015060610003206015060630c01549061048320600700062060010001500061008311d01506060048290c015048eb060600b06100015040030606104b03008620481e008010206304815
|11=>0x4815008010480106061
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x18305c400000001520000000000000004500000000000038c000000000000000d100000b200000a100000000000000020800000000620144000000000000000000000000000000000000000000000000000000000410000000000000000000000088000000800000000000000000
|5,1=>0x44210880000f900000ecc38300003530c8c0000c4400000002f200002d20a8c0000a08253000022307cc00006d000000000000000000
|6,0=>0x9f200009d2000000026c8000260c0002588951248c00000008f323488b2224888100008710000843000082200007f31f487b21e487721d487321c847021b4c6b21a486721948632000061200005f21784000170859316045621544541144c4f2000000013484b200004a111cc461
|6,1=>0x3bc8ed20000ec13a4ce813988e330000e033788dc236c4000368400000000000000d910000d723548d410000d2233cc0000000ce13308ca20000c733184c420000c223008be20000bd100000000000bc100000000000ba20000b822d88b422c880002bccad22a8ca732948a322848000
|6,2=>0x13d34ec80004e493724d8534200000004cc40004c49301000000000012d34ac9283494d23248491e3474400046c8000468517300011430001131444910143890b300010a141cd052408c0004044ff200000003f0cfb13e480003dc8f61000000000000000000f423cc4f12
|6,3=>0x63cc000634800062c989261c985260c98125fc97c300017a200017735d0d7225c080005b4d6b200016920000000000000059c96520000000000000000000000001632580d5f1574800057055a255cd5435488000000000054094e253454b252494810001462000000000014425089402
|6,4=>0x6d85b330001b126c05ae26b09ab16a85a736985a330001a0300019f167499c100019b100019a16609962000000065459320001921
|7,0=>0x8cca3128bca2d28aca29289ca25288ca21287ca1d286ca19285ca15284ca11283ca0d282ca09281ca05280ca0127fc9fd27ec9f927dc9f527cc9f127bc9ee17b09ea27a09e627909e227809df17749db27649d727549d327449cf27349cb27249c727149c327049bf26f49bb26e49b72
|7,1=>0xab4aab2aa4aa72a94aa32a84a9f2a74a9c1a68a982a58a942a48a902a38a8c2a28a882a18a842a08a8029fc67d29eca7929e067629d0a7229c466f29b4a6b29a4a672994a6329886602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a351
|7,2=>0xac4aaf2
|8,0=>0xb0c6c21b046c01afc6be10002bd1af06bb1ae86b91ae06b71ad86b51ad06b31
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0xc4000060000027a00012900008c000042000020200010000007c80003e00001d00000e200006000002a4000134000088000040000014000009000004100002000000e000005000002000000c00000440000200000090000040000018000002000000
|1=>0x49400024440012000008f8000478000226800110000085a000420800206800103200081800040b00020280010100008000003c08001c04000b10000508000260000100400080000030000016000009040003fe0001fd0000f780007b40003820001bd
|2=>0x112000088000043020021080010400008120004010002001000cfc80065ec0032f2001929000c0580060240022900011280008080004020002000000de90006c400030b00013fe0009fd0004fc800275400137a0009880004c080026000012fa000939
|3=>0x1040d0082060041000020139010095808010004003402000a01000400625e4023bfa011d3d008b9680417a4020b820104000081be8040d240204020101fd0080000038fa40102d60080040040008020000008b7200419a0020cc000a40400462a002300
|4=>0x440dc821a6a410c2720859e90424f482125b41020500810240406f482027f41013f20809b904049c820032010017208002c04001202000801000100688490340b48182104091092048169024000010067c0800220319690140b480867a40432f2021929
|5=>0x200cfc90067c48033d24019692004c810024208003002910281464968a324a440801018e1a90c30c40528fa42846021200000871c484287a420835210018a08008e040000019425209d92d04709482364f411a37a08d12d0454b482246ec1123720881c9
|6=>0x109416d840004a1205ad09027281897140c0bca0605a50147f280a3e94040fea0204ed00470280217d400420a000004a41200520108210484107af84809b624041a9
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3030014000303000303000f000003000303000303000307000a0000000000002e0b00000300000000150000001a000000000f0028000f000000000300000302000000000000000000000000000000000b00000000000003000d0000000000
|6,0=>0x4f18000b240b033b00ba03085e000f000000000b0003090f00012300005e683100310b2f00032c03000f0000005e0000000300010803030092035207185a58000009001800001800070018870900003f180c18050070003100010017390318030167051822030318590300b5002ab9001e5c0f1f6b0f09100000310100273b5e
|6,1=>0x50000300030303030371180400010016061101003c01000300000000013300005b00000000017f5e3100300316071800000003085e6d035eaa0d000000038e0300b000150300180c660300000f00030f000000b33d341a1818a930000e005f630012000f01298d91004d53182d007a010000725b390003260000000000037d4e
|6,2=>0x13192b03c60809605e1578510025000f0318000300298e1800007703000f
|7,0=>0x74b6b2bf406479c52440867ea13ed12148a8478a374ca0b798487c9490cfad3a78acb1cd574432458fca46c86ece21d34182a2436180c4ae1f85c21b7662690cc3204835bc487e426f3849894b56a4d281b8997b24be9788bd55a6b49f9d9eab93d06cb95d24c91d36c45d2fa334a41f9c8c9baf9a4acc457fbbc183c7c0968b
|7,1=>0x9572
|8,0=>0xa76ad475734840652024a554a448a1cb8884
|9,0=>0x1c
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_242 7 roots_242 ops++addP pm 1 dom_99 4 roots_99 ops++addP pm 2 dom_195 5 roots_195 ops++addP pm 3 dom_115 7 roots_115 ops++addP pm 4 dom_227 6 roots_227 ops++addP pm 5 dom_211 7 roots_211 ops++addP pm 6 dom_178 5 roots_178 ops++addP pm 7 dom_225 5 roots_225 ops++addP pm 8 dom_241 7 roots_241 ops++addP pm 9 dom_208 4 roots_208 ops++addP pm 10 dom_193 4 roots_193 ops++addP pm 11 dom_179 6 roots_179 ops++addP pm 12 dom_147 5 roots_147 ops++addP pm 13 dzo_208_32 4 roots_208 ops++addP pm 14 dzo_209_32 5 roots_209 ops++addP pm 15 dzo_210_32 5 roots_210 ops++addP pm 16 dom_146 4 roots_146 ops++addP pm 17 dom_51 4 roots_51 ops++addP pm 18 dom_114 4 roots_114 ops++addP pm 19 dzo_211_32 6 roots_211 ops++addP pm 20 dom_113 4 roots_113 ops++addP pm 21 dom_83 4 roots_83 ops++addP pm 22 dom_177 4 roots_177 ops++addP pm 23 dom_226 4 roots_226 ops++addP pm 24 dom_210 5 roots_210 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_243 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_208_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_209_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_zo_210_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_211_32_208 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_210 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_242 7 s (0,roots_242.map (·&&&dom_242)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_243 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_243==dom_243)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_243 gM v ys):RunD true dom_243 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_243 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 11 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 96 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_256 : ∀ i, 256 ≤ i → i < 286 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 30 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 286 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 130 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 130 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_243 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_213_32:=0x33003300000000003300330000000000330033000000000033003300000000
def gzo_213_32:=0x33003300000000003300320000000000330032000000000032002200000000
def gsh_213_32:=0x330033000000000033003200000000003300320000000000320022
theorem lowS_zo_213_32_212:Lower true dzo_213_32 roots_213 gzo_213_32 8:=lower_iso_b (d1:=dom_213) (r1:=roots_213) (T1:=gsh_213_32) [(dom_213,32)] (by decide +kernel) (lower_slice_b (T:=gsh_213_32) [(0x220022000000000022002200000000002200220000000000220022,0,1)] (by decide +kernel) lowS_212)
namespace S_245
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(4,20),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(16,20),(16,80),(16,144),(17,21),(17,49),(17,81),(17,145),(32,33),(36,37),(36,52),(36,100),(36,164),(48,49),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(96,97),(96,100),(96,112),(96,224),(128,129),(128,132),(128,144),(128,192),(160,161),(160,164),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_245.map (·&&&dom_245)
def gM:=goal_245&&&dom_245
def NN:Nat→Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xc54013114909c19
|5,0=>0xdf1468e04d764216042c53a4d3ff9e24ed51b6211ac25125df0f2350d1bf0bc73053460515a
|6,0=>0xdf146d7e81bf323aa90b9fa559eee689dd28958e7d39f7ab95750a26d4ea6b84a6a1f261e3958198572184ef8e4516f4262f2db6d2c63a2c415284781db4a1bc8e1ae92159a6114780f7cc0958f094f1082140676b00b22
|7,0=>0xc71d3abe927d85075d23754426b9d757ec93731f269d32331a1e9811d1591c4390d1000a5ee
|8,0=>0xfdbf56d48e59b17
|9,0=>0xbf1f1
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcc00cc00cc00cc00cc00cc00cc00cc00c000c000c000c000c000c000c000c33003300330033003300000033000000330033003300330033000000330000cc000000cc000000cc000000cc000000cc000000cc000000c0000000c000003000300030003000300030003000300030003000300030000000000000000cc00cc00cc00cc000000000000000000cc00cc00cc00cc00000000000000033003300330033003300330033003300000000000000000000000000000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00033003300330033003300220033002200320032003200320032002200320022c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c33003300330033003300330033003300330000003300000033000000330000cc00cc00cc00cc00c000c000c000c000cc00cc00cc00cc00c000c000c000c33003300000000003300330000000000330033000000000033003300000000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c000cc00c330033003300330033000000330000003000300030003000300000003000008800880088008800880088008800880088008800880088008800880088008b3003300330033003300330033003300330033003300330000000000000000
|0,1=>0xcc000000cc000000cc000000cc000000cc000000cc000000c0000000c000033000000330000003300000033000000300000003000000030000000300000000000000000cc00cc00cc00cc000000000000000000cc00c000cc00c33003300330033000000330000003300330033003300330000003000000030c000c000c000c000c000c000c000c000cc00cc00cc00cc00cc00c000cc00c000003000000030000000300000003000000030000000300000000000000000000000000000000cc00cc00cc00cc000000000000000000c000c000c000c300030003000300030003000300030003000300030003000300000003000000c000c000c000c000c000c000c000c000c000c000c000c000c0000000c000330033003300330033003300330033003300300033003000330030003300300000cc000000cc000000c0000000c0000000cc000000cc000000c0000000c3300330033003300330030003300300033003300330033003300300033003000000000000000000000000000000000cc00cc00cc00cc00cc000000cc00000003300000033000000330000003300000033000000330000000000000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc00033003300330033003300330033003300330033003300330030003000300030
|0,2=>0xcc00cc00cc00cc00c000c000c000c33003300330033003300330033003300330033003300330033003000330030000000000000000000000000000000000000cc000000cc000000c0000000c33000300330003003300030033000300330003003300030033000000330000
|_,_=>0
def sP:Nat→Nat
|0=>0xb3040c96412ca1096012ca1062501c12c42415cb28424708100438614f0445891410040c204b28424f0550045063c12c40d31412842453c148444914f0442481cb2840ce4012842450812843412cc2840c61410042481c01061420440c2040
|1=>0x1c184b2840ce1c100a12024704b2840c94012ca10318504b2842580402ca10e18f1c12c42451c148a1162470402c458e1c12ca1051c17cb2842415c02ca1091c17802c47491c12ca1091c170b2846c91c12ca10f1cd04b28424704b68a1093c1
|2=>0x1142451c12ca10e24f1c12ca1091c100b30a11624704b2840c91412ca1090572ca1091c204b2848891c12ca11125804b2844c914704a10318f04b1093c154b28418914704010e1870401091412cc28440705f2ca1091c15cb28444704b48a109
|3=>0x1091c12ca1091c100b2840c91c12ca1093c704b2843861c12ca1032470402ca1091c154b2842501c100b2842631c12ca1091c12d22843891c100a10940704b28444e24704b2841893c704b
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x551a9af4679fbce1e64d2b7923c79a2ef10784bc09df6ef4776bb99dbeed8768bb29d86ebc75abab9d4eea074cba49d16e8473eb9d9ce0c697
|7,0=>0x709f751b37d5c691f3af967c7be1e300f788b845a22c2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wAt:=mkWire dB 36 246 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1cb47012ca51272404b2928b47022ca47012ca47442404b292408a2d18749290ca4725409c5291d189012ca4f271ca562f0ca491d24f87294090f2d1d289022ca47022ca4f2f1ca47442404b291c04b2938f072924b461d24a4e3c24b47290cb491d18b49291c04a2d3ce072924b4b29
|1=>0xb29247472924b49292474b29245872d1c04b2914ac72d2408b2924b4a2d1c04b2938a492d24a4729245472d24b47291c08b290ca491d1cb491d1d189012ca4e3c24b472938ac92d24749291ca49161cb492924b4a2d407c529
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x798001a428c000820000003100008404c00001
|6,0=>0x13ce6180000128a39c5200108df9bd2000e8c003916e4d4800323000c09712c25449cd29223404000f11b33245c8a1922
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xb3773d7374784113e736733f33b33732731113f1251171111051011000e20c1036030020014012010008006004002000
|1=>0xf37d15bbfbb3
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0xc0089001000140207004
|6,0=>0xe5800055c10156c800b00420801200508214f08d080150188508
|7,0=>0x1a4dd89d5998cc81c29185e
|8,0=>0x1661f
|9,0=>0x16
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_213 8 roots_213 ops++addP pm 1 dom_117 7 roots_117 ops++addP pm 2 dom_181 7 roots_181 ops++addP pm 3 dom_225 5 roots_225 ops++addP pm 4 dom_241 7 roots_241 ops++addP pm 5 dom_229 7 roots_229 ops++addP pm 6 dom_165 4 roots_165 ops++addP pm 7 dom_101 4 roots_101 ops++addP pm 8 dzo_213_32 8 roots_213 ops++addP pm 9 dom_212 7 roots_212 ops++addP pm 10 dom_177 4 roots_177 ops++addP pm 11 dom_113 4 roots_113 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_245 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_213_32_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_113 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_213 8 s (0,roots_213.map (·&&&dom_213)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_245 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xffffffffffffffff0000000000000000,64),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_245==dom_245)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_245 gM v ys):RunD true dom_245 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_245 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_245 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_126:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_126:Lower true dom_126 roots_126 goal_126 9:=lower_iso_b isoMvS_126 (by decide +kernel) lowS_119
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 10:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_125
def isoMvS_231:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 9:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_183
def isoMvS_246:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 10:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_245
def isoMvS_249:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_249:Lower true dom_249 roots_249 goal_249 10:=lower_iso_b isoMvS_249 (by decide +kernel) lowS_237
def isoMvS_250:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_243
def dzo_111_16:=0xffff0000ffff0000ffff0000ffff0000
def gzo_111_16:=0xffff0000ffff0000fffe0000fefc0000
def gsh_111_16:=0xffff0000ffff0000fffe0000fefc
theorem lowS_zo_111_16_41:Lower true dzo_111_16 roots_111 gzo_111_16 7:=lower_iso_b (d1:=dom_111) (r1:=roots_111) (T1:=gsh_111_16) [(dom_111,16)] (by decide +kernel) (lower_slice_b (T:=gsh_111_16) [(0xcccc0000cccc0000cccc0000cccc,0,2),(0xf0f00000f0f00000f0f00000f0f0,0,4),(0xffff0000ffff0000000000000000,0,64)] (by decide +kernel) lowS_41)
def dzo_43_4:=0xf0f00000f0f0
def gzo_43_4:=0xf0e00000a000
def gsh_43_4:=0xf0e00000a00
theorem lowS_zo_43_4_43:Lower true dzo_43_4 roots_43 gzo_43_4 5:=lower_iso_b (d1:=dom_43) (r1:=roots_43) (T1:=gsh_43_4) [(dom_43,4)] (by decide +kernel) (lower_slice_b (T:=gsh_43_4) [] (by decide +kernel) lowS_43)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfffe0000fefc0000
def gsh_47_16:=0xfffe0000fefc
theorem lowS_zo_47_16_41:Lower true dzo_47_16 roots_47 gzo_47_16 6:=lower_iso_b (d1:=dom_47) (r1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (lower_slice_b (T:=gsh_47_16) [(0xcccc0000cccc,0,2),(0xf0f00000f0f0,0,4)] (by decide +kernel) lowS_41)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554554400000000
def gsh_94_32:=0x555555540000000055545544
theorem lowS_zo_94_32_84:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x444444440000000044444444,0,2),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_84)
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054004400000000
def gsh_86_32:=0x5500540000000000540044
theorem lowS_zo_86_32_84:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x4400440000000000440044,0,2)] (by decide +kernel) lowS_84)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffeffee00000000
def gsh_95_32:=0xfffffffe00000000fffeffee
theorem lowS_zo_95_32_84:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xcccccccc00000000cccccccc,0,2),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_84)
def dzo_107_4:=0xf0f00000f0f00000f0f00000f0f0
def gzo_107_4:=0xf0f00000f0f00000f0e00000a000
def gsh_107_4:=0xf0f00000f0f00000f0e00000a00
theorem lowS_zo_107_4_43:Lower true dzo_107_4 roots_107 gzo_107_4 6:=lower_iso_b (d1:=dom_107) (r1:=roots_107) (T1:=gsh_107_4) [(dom_107,4)] (by decide +kernel) (lower_slice_b (T:=gsh_107_4) [(0xf0f00000f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def gzo_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0a000
def gsh_123_4:=0xf0f0f0f0f0f0f0f0f0f0f0e0f0f0a00
theorem lowS_zo_123_4_43:Lower true dzo_123_4 roots_123 gzo_123_4 7:=lower_iso_b (d1:=dom_123) (r1:=roots_123) (T1:=gsh_123_4) [(dom_123,4)] (by decide +kernel) (lower_slice_b (T:=gsh_123_4) [(0xf0f00000f0f00000f0f00000f0f0000,0,16),(0xf0f0f0f0f0f0f0f0000000000000000,0,64)] (by decide +kernel) lowS_43)
def dzo_59_4:=0xf0f0f0f0f0f0f0f0
def gzo_59_4:=0xf0f0f0e0f0f0a000
def gsh_59_4:=0xf0f0f0e0f0f0a00
theorem lowS_zo_59_4_43:Lower true dzo_59_4 roots_59 gzo_59_4 6:=lower_iso_b (d1:=dom_59) (r1:=roots_59) (T1:=gsh_59_4) [(dom_59,4)] (by decide +kernel) (lower_slice_b (T:=gsh_59_4) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) lowS_43)
def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000ccc80000cccc00008800
def gsh_109_2:=0x3333000033320000333300002200
theorem lowS_zo_109_2_77:Lower true dzo_109_2 roots_109 gzo_109_2 6:=lower_iso_b (d1:=dom_109) (r1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (lower_slice_b (T:=gsh_109_2) [(0x3333000000000000333300000000,0,32)] (by decide +kernel) lowS_77)
def dzo_93_2:=0xcccccccc00000000cccccccc
def gzo_93_2:=0xccccccc800000000cccc8800
def gsh_93_2:=0x333333320000000033332200
theorem lowS_zo_93_2_77:Lower true dzo_93_2 roots_93 gzo_93_2 6:=lower_iso_b (d1:=dom_93) (r1:=roots_93) (T1:=gsh_93_2) [(dom_93,2)] (by decide +kernel) (lower_slice_b (T:=gsh_93_2) [(0x333300000000000033330000,0,16)] (by decide +kernel) lowS_77)
def dzo_77_2:=0xcccc000000000000cccc
def gzo_77_2:=0xccc80000000000008800
def gsh_77_2:=0x33320000000000002200
theorem lowS_zo_77_2_77:Lower true dzo_77_2 roots_77 gzo_77_2 5:=lower_iso_b (d1:=dom_77) (r1:=roots_77) (T1:=gsh_77_2) [(dom_77,2)] (by decide +kernel) (lower_slice_b (T:=gsh_77_2) [] (by decide +kernel) lowS_77)
namespace S_127
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(2,18),(2,34),(3,11),(3,19),(3,35),(3,67),(4,20),(4,68),(5,13),(5,21),(5,37),(5,69),(6,22),(6,38),(6,70),(7,15),(7,23),(7,39),(7,71),(8,9),(8,40),(8,72),(10,11),(10,26),(10,42),(10,74),(12,13),(12,28),(12,44),(12,76),(14,15),(14,30),(14,46),(14,78),(16,18),(16,20),(16,80),(17,19),(17,21),(17,25),(17,49),(17,81),(24,25),(24,26),(24,28),(24,56),(24,88),(32,33),(32,34),(32,40),(36,37),(36,38),(36,44),(36,52),(36,100),(48,49),(48,50),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(66,67),(66,70),(66,74),(66,82),(66,98),(96,97),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1fffffffffffffffffff
def xsM:=roots_127.map (·&&&dom_127)
def gM:=goal_127&&&dom_127
def NN:Nat→Nat
|5=>5
|6=>50
|7=>195
|8=>308
|9=>125
|10=>14
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xe7292b8221948e35410a1ac2f
|6,0=>0xf8c83e53d5ddb31d05bbb69f3aeac0a5c809add296da695682954689512d942e5850f283fc47a9ad7a49c7912d74295724936d2096c4a46abe469613660bc5b67d4e5384a2634804546d36457344002c3e7673d5433bb733a28c399c136e26351da27ed722e511ac2f13cc00b66b0a7df0547703fa5022980120300f85
|7,0=>0x6ae506ab346a1276a0636990a68dde68d32651b961c31619e15f8385f6145f3365e9315bc5e5b8375b64959ba5583c65725a552f153f0d53c9f516f94f3fb4e99e4d2e84d27f4cebf4c7f14b8c74b5d44af0b4ae9c49fba49c2748124479d2476ce45a57459384588a44dd742180417ae3e2b63e1a43d6a43d5d53b7bd3b1eb380e737b173753736e8a3672e3543234de7343333423b32f8d320c22ff3c2c3c82c19b2c05a2bebd2b77e2b34828dc7288482863f2826727dd52706026817267ef25bd1259ef259d7252db241c722fad22944227d722130211442032e1fcdb1fcb81fa3b1f42b1f0f21eef31c0f01b0391ac2f1abb61951417fb617d7217c371619c15dc413f8213e7b13d6d13807135331315b11daf1137f1100310b0a0febb0ef9d0cefd0c4bb08a44051c6027c501f0a017e00162b01281012510107e005a9
|7,1=>0xfdf4ff7be7f5de5f5394efc39e9781e5634e3debdc293d6d27d4e28d3ad8d302cd055fcd287caf3cc6e5ac4460c022abd92ab86c5b7c64b68bab5506ac840aa4caaa1bda92f9a9020a850fa24c8a09f39d4ac9b6509a9939855a95694944e79422a8f29b8d68b8d4998c62f8bf7f8b5db8ab848842586f4386cba865d4855a380d87803eb7e4567b9917a3637635c75c27740d4736877306172f70723d8713946febf6cfd56c2dc
|8,0=>0x3edd73ec2d3e3fd3d3b33b9dd3b9aa3b5263a7a13a4ca3a3293a2ea395ed394e2364263627135f7b3521334b5533639331ae32f5032d1432a733208a31f2830f192f6db2ece92eac02e9862e6352e02c2deff2ad392abd229f96292f127956266cd265ae255cf24af32370e22d7022c1a22be922a3a217b62171e21414212e82122d20c892064e201071fe1c1fd931fad61fa241f42b1ec0c1dff01c8231c6031c4411c2761ac511aaf41a88b1a1771949818ff918f3218c34184f91731a16f7d16c9e16b1716a72167341624b1606715dd515c2d15bf6154b31549614fb614dfe1487d1443a1417913d8513c89132ef12819114a210fdd0ff810febb0f7620ee700e69c0d1df0c7fb0c3000be5c0ad6a0aa520a535080550721d0719b065f30517b04b9204b79047060407c03c1c0353d0304402e9b02db201b1b0120300e28
|8,1=>0xa640fa24eaa2180a1c1b9fd879f6d79c5eb9c0ef993f1990d89627695baa956829555b94279935c89342f90bbb8f9708e87f8c8068a8f38946a872e28609285ca7842a583f2a8360682ece82df782dba7f0c27e1c37e0317d5537cf637cbc37ba127ad617938178a1c776fa77487769f3733ec72d2071de97195c711e0711376febf6f2c86ee166e9426daa06d33f6cb696c7ac6bea36baf26b8ad6b3026a3166a063691f468f9168ae7682ee681e267c336763f64b8b64aca642da6410f63c4e62b7b625e16237b618246125d5e8545e4615db0c5c9a65b6d75939c5854f57a4957833565ee5635755b46552ed551b854a42539db535f752a9f528c0524f35197c5153a511834fbe84f4354f40d4e4dc4de7a4d9914d48b4d1654cf704ceea4b5324b42b4a86e488fb475c046afc44987440f643fbf43b8742de04178a4127d
|8,2=>0xfeacafa280f2e0bf2cd8f226df1a77f006fefc2eef3a8edd33ec4f9e7224e5d68e4755e14a9e0396dbed3dbda2d88fed6c2ad641ed4e28d3b51d1d76d0c3ad055fce9c0ce2f9cb260ca6a7c9c81c73a5c5102c21f8c0b77c0638bd488bcbe4bcac7b9634b948eb935ab70e6b588fb4eb2b3c51afc7daf005ae8e3ab8ddaa1bda7ad8
|9,0=>0xfcb54fb74afa280f80d3f6f03f673be259de20b7d5822d1b83cec71cdf47c6e0bbdd15bb383ba879ba0a2b38c7b0480afed3afc7daf7f2ad125acea9aab24a8a85a8201a79fea576da4c3aa36faa24cba21faa125c9fc329bd299b7a09b2b79954c98d89956828dc818c1808b3068a35989ecd7cf22794fc77b19776fa707586fc266d2926a3f76a35a69a566765b64aca60eb95f6e15ef435e22c5d2755839a56d99559705254f4b3f949cb64816946fad46f5d44531426593eb213e2c43d5ff3d36c3c2ee3bea03b2ce3a6793a623395c7375e83733034b53348ea3254f2bc42292d4291b828ef024f8b2479722dec2258c224dc2150d1b4fc1ab8a195c21927417b87156f1155f214af80eebe0d80a0d12b0c8070c0cf0bb3f0baf90a10409fe00969706d14068b8065f80570f053570398a037ed0272a
|10,0=>0xce280bbe949e7bb928f2918968d3bf83c7d761fa715435254f43a533b65b2676305c14
|11,0=>0x2654f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffff0000000000000000ffffffffff00ff00ffffffffff00ff00ffffffffaaaaaaaaffffffffaaaaaaaaffaaffaaffaaffaaffaaffaaffaaffaafffff0f0fffff0f0f0f0f0f0f0f0f0f000000055000000555555555555005500ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00fffffafafffffafaf0f0f0f0f0f0f0f055555555550055005555555555005500ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccffffffaaffffffaaaaaaaaaaaaaaaaaa
|0,1=>0x5555000055550000ffffffffffffffffff55ff00ff55ff000f0f0f0f0f0f0f0f0f0f00000f0f0000ffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffaaffffffffff00ff00ffffffaaffffffaaff00ff00ff00ff0000ff00ff00aa00aa00ff00ff00aa00aaffffffffffffffffaaaaaaaaaaaaaaaaffffaaaaffffaaaa0000000000000000ffffaaaaffffaaaaaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00aa00aa0000000000000000ffff0000ffff00000000ffff0000ffff00000000000000000000ffff0000ffffffff0000ffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffff0000ffff00000000000000000000
|0,2=>0xffffffffffffffffffffaaaaffffaaaa00ff00ff00ff00aa00ff00ff00aa00aa000000ff000000ff00000000ff00ff00ffff0000ffff0000aaaa0000aaaa0000ffffffffffaaffaaffffffffffaaffaaffffff00ffffff00ff00ff00ff00ff00ffffffaaffffffaaffaaffaaffaaffaa00000f0f00000f0f0f0f00000f0f00000f0f05050f0f05050f0f05000f0f0500ff00ff00ff00ff00ff00ff00aa00aa000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f000f0f0f000f0f0f000a0f0f000affffffaaffffffaa0000000000000000ffffffaaffffffaaffffffaaffffffaafffffffafffffffaf0f0f0f0f0f0f0f0ffffffffffffffff5555000055550000
|0,3=>0xffffffff00000000ff00ff005555555555555555550055005500550000ff00ff00ff00ff00ff00aa00ff00aa000000ff000000ffffffffffff00ff00ffffccccffffccccccccccccccccccccffffffffffffaaaaffffffffaaaaaaaaffffff00ffffff000000000000000000ffffff00ffffff00ffffff00ffffff00fffffff0fffffff0f0f0f0f0f0f0f0f0ffffffffffffffffffffffff000000000000ffff0000ffff5555aaaa5555aaaa55555555555555555555550055555500ffffffffffffffffffffff00ffffff0000000000000000005555550055555500ffffffffffffffffffffffffaaaaaaaa0f0f05050f0f05050f0f00000f0f0000
|0,4=>0xff00ff00aa00ff00ff00ff00aa00aa55555555555555555555555555005500ffffffff00000000ffffffff005500000f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0a0000000000000000ffffff00ffffff00ffff0000ffff00ff0000000000000000ffffccccffffccffcccccccccccccccc00000000000000000055000000550000ffffffffffffffffffaaffaaffaaffaaffffffffffffffff0055000000550000ffff0000ffffffffffff0000ffffff000000000000000000ffff0000ffffff00ffffffff0000ffffaaaaaaaa0000aaaa0000ffff0000ffff0000ffff0000aaaaffffff00ffffff00ff00ff00ff55ff00ffff0000ffff0000ffff0000aaaa0000
|0,5=>0x55555555555555005555555555005500ffffff00ffffff00ffffff00ff00ff00000000ff000000ff0000000000000000ffffffffaaaaffffffffffffaaaaaaaa55555555000055555555555500000000000000000000000000ff000000ff0000aaaaaaaaaaaaaaaaaaffaaaaaaffaaaa0000ffff0000ffff5555ffff0000aaaaffffffff00000000ffaaffff0000000000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff55ff00aa55ff00aa00ff00aa00ff00aa00aa00aa00aa00aaaaaaaaaaaaaaaaaaaaffaa00aaffaa00ffffffffffffffffffffffffff00ff0055555555555555555555555500000000aaaaffffaaaaffffaaaaaaaaaaaaaaaa
|0,6=>0xffffffffffffffaaffffffff00000000ffffff00ffffff00aaaaaa00aaaaaa00555555555555555555550000555500000000000000000000ffffffaaffffffaaaaaa0000aaaa0000aaff0000aaff0000ffffffffffffffffaaff0000aaff0000000000ff000000aa00ff00ff00aa00aa00005555000055550000555500000000ffffff00ffffff00ffaaff00ffaaff00ff00ffffff00ffffff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f000f0f0f00ffff00ffffff00ffffff0000ffff0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000ffffffffaaaaaaaaffffffffffffffffffffffaaffffffaaff00ff00ff00ff00ff55ff00ff55ff00
|0,7=>0xffffffffffff0000ffffffffaaaa00000000555500005555aaaaaaaaaaaaaaaaffffaaaaffffaaaaffffaaaa0000000000000000ffffffff00ff0000ffffff00ffffffffffffff00ffffffffff00ff00ffffffffffffffaaffffffffffaaffaa00ff00ff00ff00ff00000000000000000f0f000f0f0f000f0f0f00000f0f0000ffff0000ffff0000ff000000ff00000033333333333333333333333333332222ffffffffffffffff00ff000000ff0000ffff5555ffff5555ffff5500ffff5500aaaaaaaaaaaaaaaaffffaaaaffffaaaaffffffffffffffff55555500555555000000ffff0000ffff0000aaaa0000aaaaffffffff00ff00aaffffffff00aa00aa
|0,8=>0xf0f0f0f0f0f0f0f0f0f0fffff0f0fafaffff00ffffff00ffffff00aaffff00aa0000ffff0000ffff0000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00aaffffffccffffffccccccccccccccccccffff000000000000ffff000000ff0000ffffffffffffffffffff000000ff00005555550055555500555555005555550000ff00aa00ff00aa00ff00aa00ff00aaffffffffff00ffffffffffffff00ff00aaaaaaaaaa00aaaaaaaaaaaaaa00aa00aaffaaaaaaffaaaaaaaaaaaaaaaaaaaaffffffff0000ffffffffffff0000aaaa0000005500000000ffffffff00000000aaaaaaaaaaaaaaaaaaaaaaaaaa00aa000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00
|0,9=>0x33333333333300003333333333330000ffffffffffff0000ffffffff00000000ffffffff00000000ffffffff00ff00000000555500000000ffffffff00000000ffffffffffff0000ffffffffffff0000000000000000000000ff00ff00ff000000ff000000ff000000ff000000ff0000ffffffff0000ffff000000000000000000000000ffff000000000000ffff0000ffffffffaaaaffffaaaaaaaaaaaaaaaaffffffeeffffffeeccccccccccccccccffff0055ffff0055ffff0000ffff0000005500550055005500000000000000000f0f00050f0f00050f0f00000f0f00000000000000000000ffff5500ffff5500ffffffffffffffffffffffff00ff0000
|0,10=>0xffff0000ffff0000ffff0000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000555500000000000055550000ff00ff00ff55ff00ff00ff00ff55ff0000000000555555550000000055550000ffffffffffffff00ffffffff00000000ff00ffffff00ffff0000000000000000ffaaffffffaaffffaaaaaaaaaaaaaaaaffffffffffff00000000000000000000ffffffffffffff00ff00ff00ff00ff00ffffffffffffffffffffffffffff0000333333333333333333333333333300000000ffff0000ffff0000ffff00000000aaaaffffaaaaffffaaaaffffaaaaaaaa00000000ff00ffff00000000ff00ff0000000000ffffffff00000000aaaaaaaa
|0,11=>0xff000000ff000000ff0000000000000000000000005555555555550000ffaaffffffaaffffffaaffaaffaaffaaffff0000aaaa0000ffffffffaaaaaaaa00ff00ff00ff00ff00ff000000ff0000ffffffffaaaaaaaaffffffffffffaaaaff00ffffff00ffffff00ffff0000000055555500555555005500550055005500ffff0000ffff0000ffaa0000ffaa0000ffffffffffffffffff00ff00ffffff00ff55ff55ff55ff55ff55ff00ff55ff0000000000ffffaaaa00000000aaaaaaaa0000ff000000ff00ff00ff00ff00ff000000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffffff00ffffffffff00ffffffffffff00000000
|0,12=>0xffffffff00000000ffffaaaa000000000000000000000000ffffff00ffffffffff00ff000000000000000000ffffffffffffff00ffff0000ffff0000ffffffffffff0000aaaaaaaaaaaa000000000000000000000000ffff0000ff0000000000ffffff0000000000ff00ff0055550000555500005555000055550000ff55ff00ff55ff00ff55ff00ff55ff000000555500005555000055000000550000ff000000ff000000ff000000000000000000000000000000ff00aa00ff00aaffffff00ffffff00ffffff0000000000ffffffffffffff00ffffffffffffff000000000000000000ffffffffffffff0000ff00ff00ff00ff00ff00ff00000000
|0,13=>0x33333333333322223333333333332222ffffffffffffffff00000000ffff0000ffffffffffffffffaaaaaaaaffffaaaaffffffff0000ffffffffffff0000ff00ffff0000ffff0000ffff0000ff000000ff00ffffff00ffffff00ffaaff00ffaa0000000000000000ffffaaaaffffaaaaffffffffffffff000000000000000000ffffffff55555555ffffffff55550000ffffffff000000ffffffffff00000000ff000000ff000000ff550000ff550000ffff5555ffff5555ffff0000ffff00005555555555555555000000000000000000000000ffffffff00000000ffff0000ff00ff00ffffffffff00ff00ffffff0055005555550055555500550055005500
|0,14=>0xffff0000ffff00ffffff0000ffff0000ffffffffaaaaffff0000000000000000ffffaaaaffffaaaaffaaaaaaffaaaaaa000000000000ffff0000000000000000ccccccccccccffffccccccccccccccccffffffffff00ff00ffff0000ff000000ffffffffff00ff000000ffff0000ff00ffffffffffffaaaaffffffff000000000000550000005500ff00ff00ff00ff00ffff0000ff000000ffff0000ff0000000000ffff00ffffff0000000000000000ffffffffffffffffffffffffffffaaaa0000ffff0000ffff0000ffaa0000ffaaffaa0000ffaa0000ffff0000ffff0000ffffffffffffffff00ff00aa00ff00aaffffffffffffaaaaffffffffffffaaaa
|0,15=>0xffffffffffffffff0000000055550000ccccccccccffccffcccccccccccccccc00000000aaaaaaaa00000000ffffaaaaffffffffffffffffffff0000ff0000000000ffff0000ff000000ffff0000ff00ffffffffffffffff0000ffff0000ff00ffff0000ffff55550000000000000000ffffffffffffffffaaffaaaaaaffaaaaaaffaaaaaaffaaaaaaffaaaaaaffaaaaffffffffffff0000ffffffffff0000000000ffff0000aaaa0000ffff0000aaaaff000000ff000000ffff0000ffff0000ff00ff00ff00ff00ffffff00ffffff0055005500550055005555550055555500ff00ff00ffffff00ff00ff00ffffff000000000000ff00ff0000000000000000
|1,0=>0x333333330000000033333333333300000055000000550000005500000055000000000000ffffaaaa00000000ffffaaaaffffffffffffffff00000000ffffaaaa0000000000ff00000000000000ff0000aaaaaaaaaa00aaaaaaaaaaaaaa00aaaaffaaffaaffaaffaaffffffaaffffffaa00ff00ff00ff00ff00ff00ff00ff000000550055005500550055000000550000aaaaffffaaaaffffaa00ff00aa00ff000000ffff0000ff00ffffffffff00ff0000005555000055550000000000000000ff00ff55ff00ff55ff00ff00ff00ff0000ff00ff000000ff00ff00ff00000000ffffffff0000ffffffffffff0000000055550000555500005500000055000000
|1,1=>0xff00ff00ffffffffff00ff00ff00ff00aaaa0000aaaa0000ffff0000ffff000000000000ffffff0000000000ffffff000000ffff00000000ffffffff00000000000000550000005500000000000000000000000000ff0000ffff0000ffff0000ffaaffff00000000ffaaffff00000000ffffffff00550000ffffffff00550000ffff0000ffff000000000000555500000000000000000000aaffaaaaaaffaaaaffaaffffffaaffff0000000000000000ffff0000ffffffffffff0000ffffaaaa00000000555555550000000000000000ffff0000aaaa0000ffff0000ffff0000ffffaaaaffffaaaaff00aa00ff00aa00ffffffff00000000ffffffffffff0000
|1,2=>0xff00ff00ff000000ff00ff00ff0000ffffffff55555555ffffffff00000000ccccccccffffffffccccccccccccccccffffffff00ff0000ffffffff00ff0000ffff000000000000ffff0000ffff0000ffff0000ffffffffffff0000ffff00000000000000000000ffffffffffff0000aaaaaaaaffffaaaaaaaaaaaaffffaaaa0000aaaa0000aaaaaaaaaaaaaaaaaaaaffff0000aaaa0000ffff0000aaaa0000ff55ff55ff55ff55ff00ff00ff00ff00000000000000000000000000ffff0000ffffffffaaaaaaaa000000000000000000000000ffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x83c1c05090200211140140808008604e0f028104c01088941e050200c0218088900a09040840211028100602008000a090400802060b814080c0f0080218028101803008603a1b028103402008600a040100430150b8142408010042219028101002008602e050200802160a83c1c0d09030040107034120c058040a0401808020a028241007008180a04018080200
|1=>0x10040c0f07034120c01004200e0681018010e83c1a05048206e01088140808038040c0f158142408010042236028200401088d41a0504830100b008380a09040042228028101803010046431028103402008600a04040040c3007814080c018043025028100401000b81e05048201601088180a04018080211168143802008b02a0f15814120805804220e068105202
|2=>0x40080218088800a0413004221d07814240c04004221d07034240801004220e06810180b0083c0a04008444a15078381a090402c021102824180800844500e0284810010887478050200c040108814082a01004220f06814080301004000d028481808010041c0d0a0300401098381a0406008760f02848180800844500e1d01052020083c0a04008443a1507814081a
|3=>0x70140808008444a0f028101002248441e050211c1002008448c0d028105402008441e0522010060801004220502020043b088181e050e02004010c10c1e2b0281010021d8441e050400802110f9081e050210404010883c0a040f02004010c0440a1c2002004010c03c0a0404004221d1f83c0a0404004223e1383c0a040600802181e83c0a04018200218088740a38
|4=>0x1004220609814080801004a61107814080301004000e02824100b008440a330202004012703c0a040400422510e83c0a0401004a0112783c56050a02004010884c9a042382004010883c0a042382002112603c0a040400802160c83c0a040a09804010883c5605020a804010883c0a380200c04012703c9a0404008021107814080800844980f0292c080c018080211
|5=>0x10042219079740a040a0300602008600a040400802502d83c0a040182004012c8600a040400802180891808572382004010883c0a041300802110f83c1a05048301002008400a040400802112c03c1a050203010010e83c0857040080211078380a0414808021107814080801004225507814080c04004221d078d80a040400430110e8340a04040080254078142808
|6=>0x1d0101002008581e05020300601088741e0d028101866010041e050202004010303c2e52028101001089941e05320100401088641e050202004013183cc4050202002110e83c7405020a410020083c9a040400802180883c0a040400430112603c1c050482002110e84036050206804010883c0a043000c04010883c0a041500802112f83c0a5e0200c04010883c0a04
|7=>0x83c1c360202002110e83c0a1204004221d02810060800860222502810100200818da0f028101021008441e0502030c002008601e05360108e080100422050202002111f1941e050200c1002009a82231028701002008b01e05020a80401089a41e042b82004010c0441e05020300602008603e050202004010c1a01e0d028101808010ec1e0e02810ce02008441e0e
|8=>0x28241002008447205398101002008181e050202004010c044e4050200802110a9c41e05048200e0108814d804040080218088380a12040080211380140808010042c0f028e0080301004303e02810060200860223d378101002008441e050200c0401089b81a050202004010003c0a04018200401088c81a050a03010020084c0a0404004221d2b03c1a05020305402
|9=>0x78380a040400802180b8340a0404004227807814080800844ca3f078d80a04040043011128d80a04018a80401088140808058042206078340a04148a80401078141204010042215078ac0a040402c021107814080801044ec0f0281006020084446051c00c04010c0443e05020200401271681e0e06824080c010041e0502030060200844ea053a0101002008601e0d
|10=>0x600c04010c014081a01004220f029f4080801004300e0681018020083c2605020200401089f01e0e0682410020084420050e0241002008181e7b028105402008441e050200802112783c6c05178200401088b01c0d0202002110e83c0a09060201601088140847040080234079e80a04040080216078145e04130080211078e80a04040080254078340a383b8080211
|11=>0x28e0080301005020f07034082a01004220f02810180300844ca0f0681408081b804220f028101002008580c0f02810100108a001e0d028101808058041e0e0681010021d8441e050211c1001088741e7f028701002008601e0e0282424080100422050202004010c0d01e31028101001088741e050202004010c1f80a040d02004010c014120c04004221d080145e04
|12=>0x4480c1002008440a04010051087078140847040080259078140808008444e0f02810100200a141e050202004014203c0a040a00802110a83ca4050200c0401088e40a12060200401088141208010042219080381a040a0300401078140808008443a19078381a0406008020f08014080801004305b07a08080801004220f070342808010042213028bc800801004220f
|13=>0x78140803040042227078152204018200401088381a040402c021107a400a0401820040108814121206020040108814080847804220f02a3808030100430110281004011f1581e050211c1001088941e36028200401089691a050200802114603c0a1c0a02004010303c0a040f02004010883c1a0502020048b0883c6c051c00cee02008440a0401004222c0a83c0a04
|14=>0x2803c0a040400802110788c0a040400802180b8380a090202002110e83c0a09040042228158141208010042210158140808008443a0f028880803010043052028105402008441e050482004010888c0a09020300602008600a04040092a110781424080084450050400802111a83c1c050202002110e83c0a090209804010883c0a04040042292078140808010042232
|15=>0xb81408030400802111a03d3a050200c1002008441e0504810180301004220f4e0101002008441e051c0108e0301004220f028101002008602248078340a040400876110781408030400802114d03c1a0504820040108a641e050202004014b0441e6202824080801004220f02810060800844ca0f1b01408030400802112d0380a040400802111603c0a04060200401
|16=>0x400802a20883c0a040400802180b03c0a040400802115083c0a040400802112103c5605020501002008441e2b028101002008441e1006814082a01004220f0282408080100422a007814080c01004305607814280801004228807814080801060229f07a78080c0400802110781466042382004010883c1a0502020040108a341e05020206e010883c0a09040080211
|17=>0x8441e36028240803040080211028e0067701004220f0681470090400802110781408080100422ab07aa8080801004220f028bc100200845320f02810100200aa0220f028108e08010047c0f0281028080100422060781408a604008021107814080801045480f0287008080100430a0078140808010042206078400a040400802590883c1a050a02004010884c0a04
|18=>0x282408080100422560781466083b80802110781408140182004010c0440a040400802165a03c1a05022cc04010883ca40502020ee02008441e0d028101808010041e1358814080801004220f070d8120404008021107ac00a0404008021107814bc04040080211078141212040080211029d0080801004223e078144404018080211078140808008455c0f028115802
|19=>0x602004010c03c0a1c0202004010c1581e86028101002008441e0e0681018020083c0a09060200401088400a044502004010883c0a045c82004010883c0a610202004010883c0a041500802115c03c0a045b82004010883c0a045b00c1002008441e3a4f0101002008441e05020301001088741e05022d41002008441e05020200401089501e05020501002008447e0f
|20=>0x60814080801004220f028bc10020086022990781408030400802180887c0a040400802115f83c0a0401004221507814080801004303e0781408080100422be0781408080100430112103c0a045e82004010883d78050202004010883c1a0502020040108aec1e05308108e0801004220f028200401089691a0f5d014080801004220f068140866040080211078145e04
|21=>0x883c1a05020a81002008441e0502020040108b241e0502050100200844a20f07014080805804220f070141204060080211078e80a040400802160883c0a0406020043b0883c0a046380c04010883c0a450200c1002008441e0502020040108b181e0502020040108b141e0502020048b0883c0a043002004010c0441e050200c100200845880f02b0c080801004220f
|22=>0x6882004010883c0a040100430110a83c0a04060a804010883c1c05178101002008441e0502020040108b401e0d02810280c04008020f028701002008b01e0d028101808010041e10028101002008459e0f1b01408140400802180881408080100422ce0781598040400802110781408080100422cb0781408030100422880781408080100422ca07814c204040080218
|23=>0x202004010883db0050202004010c045960f02824080c04004221d07b5c0a040400802110781438080100430970781408140600c04010883dac050202004010883c0a040400802000883c6205020200401089c41e6202810280801004220f0703412040400802110781408d50400802112b03c0a04238200401089681e050a03010020084426050202002111803c0a04
|24=>0x1004300f02811c40801004220f0281114030400802110781408080100422e107814080801045be0f02810100200b74220f6e014080801004220f48014080801004220f0281010020086022cf0781408db040080211078c40a090202004010883c0a046d02004010883c0a940202004010883c0a1c0400802112d03c6c050202004010c04458056c820040108a641e05
|25=>0x400802110fa801e050202004010883dca0502050100200844ac0f028e00803010043011070d8081404008021107b900a040400802110781408080100422e307814080801004d611078340a380a02004010883c0a04148a804010883c6c050200c1002008451a050200c04010c044ac05048108e0801004220f1b0101002008454e05470101002008441e31028700808
|26=>0xc0441e0504810100200844320f02810100200845c287078145e040182004010c0440a0404009d611078340a04040080211078e53c040400802110781438080100422750781408ea040080211079480a330202004010883c1c0d0202004010883c26050202004010c1441e050202004010890c1e0502020040108ba41ee8028101002008441e050239c04010883c0a04
|27=>0x20200401088f81e5c02810100200940220f1b0101002008459af6028101002008441e056c810100200860223602020040108bd41e0502100100200860220f0681408f40400802110781408080100422f20781408f101808021107814080801004221f2b03c0aef0202004010883cf605020a804010883c0a0404008021107bb80a047682004010883c0a8e020200401
|28=>0x4008021107aa40a380180802116403c0a380400802113683c0a040400802117f83c0a0404009fc11078340a04040080216078140808008443a0f02810100200860224307814080c0180802180781408080100422fd078380ad90202004010883c0a047e02004010883c0a040400802117d03c0a0404008021107be40a040400802f87b8441e050206804010883c0a33
|29=>0x4008021107814080304008026b0883c0a040400802110c83c26050240c1002008441e36028bc080801004301102810100200846040f0703408140400802110783a0204040080211078381a04040080211078400a090400802f70883db8050200c1002008441e050e00c100200844b40f06814700401808021107814080801004230007814080c0402c0211078340a04
|30=>0x8441e050e020040108b481e050202004018503c0b090202004010883ca405020200401089681e36028e008030100422a502820040108a641e05020a804010883c0a040a11c1002008441e0502020040108c201e05198101002008447e0f02888080801005100f028101002008460e0f028101002008460c0f18814081404008021107814080800860221d07c140a04
|31=>0x2d03c0a04040080218088800a040444404010883c1a05320101002008441e050202002111283c1c05048101002008441e05110241002008441e050202004118783c0a090400802118703c0a040f02004010883c0a0413008021107a6d5e0801004220f07014080c01004300f07014080801004220f82014080801004230c078380a730202004010883dec050200c1002
|32=>0x88c81e050202004017c060220f02824100200845100f028101002008448c0f0282410010887420058a0101002008441e36028101001088741e050e0101002008181e0e4f0101002008441e05024481002008441e050202004010303da605048201601088140826010043011078380a040400802111003c0a040600c04010c01438080100422de078340a04040080211
|33=>0x1004220f028481002008440a041482004010883c091904008021107814080c0400802180f83c74050202004010883e30040400802110781412040182004010c0440a040400802118b83c0a040400802111a03c1c05048200401088413a050202004010883c1c050202002110e83c0a040400803160883c0a0404008021107c545605048101002008441e05020200401
|34=>0x2820040108b201e050202004010c044ac0f028e0380801004220f028e0080301004220f02810100200845ea0f028101002008441ea98e010180801004220f02824080c0400802110781412040400802112883c0a04238200401089201e05360101002008441e050202004010883e3605020200401089201e2b028101002008441e1302888280801004220f028123408
|35=>0x7814091f04008021107815b204040080211078380a0404008021107b4c0a048f02004010883c0a3802020040108c741e0d02810280801004220f80814080801004220f06814080801004220f080d80a1c0202004010883c0a380202004010c0441e0d1b0101002008441e05110101002008441e05198101002008441e0e028101802008441e0502020040108c381e9b
|36=>0x20200401089b41e050200c100200845a60502020040108a201e050211c1002008441e05024901002008441e050231c1002008441e050248c1002008441e050202004010883c2e050202004010883de031028101002008441ee0028101002008441e0502020040108c881e050202004010883e420e02870080801004220f02810180801004220f098381a04040080211
|37=>0x7bb00a730202004010883c0a040400802112d03c0a042382004010c0441eb2028101002008441e0502020040108c741e05020200401088641e05020200401930441e0519810060801004220f02990080801004220f02810280c04008021107814080c0400802110784062050202004010c0441e050202004019283c6c0502020040108a641e050202004010883cba05
|38=>0x7a78080801004220f02870120801004220f06814080801004229907a6c0a0404008229f07a940a040400802110781408080100430113883c0a0401820040108b201f1c0202004010883c0a040400802113a83c0a090202004010883d3c050202004010883c6c0502020040108b4c0a040400802113883c0b280202004010883e4e050202004010883c0a04040080211
|39=>0x2810100200845a40f028101002008447c0f1b0140808010043011078140808010ec220f02824100200845320f95014080801004220f0282410020084420050202004010b0441e050202002110e83c0a04018200401089681e051c020040108b201e050200c100200860220f02810100200845460f02812520801004220f02810180801004300f028240808010043011
|40=>0x4008021107a9c0a043302004010883c0a040a02004010c0441e05020200401088b01e2b028101002008441e05048101001088741e9b02810100200860220f1b014120404008021107814381404008021107c400a0404008021107a6c0a1c04008021107814080801004301190014080801004220f49814280801004221307014080801004301107814082a01004220f
|41=>0x4383c1c050202004010883c2636028101002008602205020200401089441e0502020040108cb41f2c028101002008441e050202004010c044580f1b01408080100422a30781408080100430114b83c0a040400802111f83c0a040182004010c0441c05048101002008441e0502020052b0883c0a1c0400802114b83c0a045782004010883c0a040400802116f03c0a04
|42=>0x202004010883c2605048101002008441e050202004010883e40050202004010c0441e0502020040108b201e050202004010883cf236028115e0801004220f028101002008455a0f02824080c040080211078140808010453e0f028101002008441e984d8d8080801004220f1b01408140400802110781408030400802111f83c0a040402c0211078143804040080211
|43=>0x28101002008441e05020301002008441e050e0101002008441e0502020040108a5c1e05020501002008441e050202004010883c209b028101002008441e0e028101002008441e36028101002008441e05
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x18600930031800cc0006
|6,0=>0x2e6e16c70b2b8579c2aee15070a4b8509c276e1347096b8499c23ee1187088b8429c206e0fc707ab83b9c1cee0e0706cb8349c196e0c4705eb82d9c15ee0a87050b8269c126e08c7042b81f9c0eee0707034b8189c0b8c0566027b8121c082e03a7019b80b1c04ae01e7
|7,0=>0x1b4c0d8606b3035181a538d0a06750332819540c8a06350312818540c0a05f502f2817540b8a05b502d2816540b0a057502b28155b8a8e053702938145c0a0e04f702738136b0999c4bd025681274091a047d023681174089a043d02168107b8821c40101f880f8b87a603c301d980e8c0726038301b980d9386aa0345019a80c94062a0305017a8
|7,1=>0x2aec15560a9b0545829f394da0a5d0527728fc145e0a1f0507827fc13de09df04e7826fc135e099f04c7825fc12de0960e4a97250c1266092304898240c11e608e304698230c116d88a7044c7222410f20869042d72133907a082d040e820340ffa07ed03f061f440f8207b2e3d181e4c0f06077303b181d4c0e860733039181c4c0e0606f303718
|7,2=>0x3a4b9d060e74e7328395b9c958e3ce716838741c1dcdff06f78377c1b9e0dbf06d7836839b220d82e6b98358c1aa9cd45069a834941a2a0d05067a8339b99ae0cc8e65d732b3993a0c8d063f731bc18be0c4f061f830bc1841cc11060082fc417c20bd105e082ec41745cb9305c182dcc16c60b5305a182ccc1649cb16e58382bdc15d1cadae5658
|7,3=>0x1d818eb107508
|8,0=>0x4b7c259a52bd095684a6ca512527909339495c248e1238e9139485c2411d1fae8f494764238e51b708d4746642312117908b39455c2291d137289294454220a10f5087284354218a10b328509424420fe506f082f8413c207e102d280d940339ffdcfed27ed93f249f75cfa927cb93e1c1eea4f6327a983d049e620f1f278693bf41dda0edee7669
|8,1=>0x5c13adea16e50b6a85b0cad6616a12b4975a04ace2165f2b27858fc2c5e161f0b07857f4abd655db0ae4956e42b4e55952ac2855d42ac655530aa1854d3aa4655112a80853c429be54cd2a5e852bba93e148f0a3e951b428ba144b2a1c950a42832140729fa94f8ca7a613c4e9da84e94272a138509ba84d9426a65343099984c8c2626130129779
|8,2=>0x6cb4363a1b0d0d7d96ba4b5ae5ac52d5b76a94b52dda870d3b86994b4a65a430d198688c34261a04ecf99678c33a259c10cd79667c331e197f0cb6965743296593b0c949646bb21618f92c748635cb18e18b8ec5486264311218772c3386154b08a18350c128604cb00617f30bf095f3caf7e17af0bce95e342efa176b2bac95d1cae6a57232b898
|8,3=>0x7d43be821f2f2f8f87c34bdf65eeb0f6e77b343d765eab0f4d87a33bcf65e6b0f2c979243c721e290f0b9781c3bee1de52ee99770c3b625da10ec7975fc3ada5d5d0ea5974e4ba4e5d170e83873d4b9ca1cd50e62872dbb94e1c98ee43971dc38ce1c552e22870d4384a1c132e0276fccb7c25bd2ede186ecc37461b912dbf96dbc36be1b4d2d9e8
|8,4=>0x8a4444fe626d312d9892c4476222b110c9882443f221ecd0ee8873bc37a61ad10cf78634c2fa216d10ae88534427a212d108e8842cc1f620e9306c883244175e0ab104d8822c40f6206b102d8813b407e202d300f7803c3ffa5fed0fee87f2cbf79dfab2fcd87e33befa1f6d0faf7
|9,0=>0x9abc4d3a668b333e799b44cba264d131e898b44c3a260d12fe897b44bba25cb32dd896ac4b36258b12bc995a44aae6545329999493ca26650312798938c49a624c312598928c4926248312398918c48a62443121989084c81e63ff11f788f7c479a63bd11d598e64c712237731b298d4cc6862333119188c4c460622f3117098b44458222b111508
|9,1=>0x15489aa0454de6a60f5288a904545e6a1d35077a7f4d3d669db14e58a6ec5356299934c39a5d4d2ca295514a19a4d3d24a291514828a3d451ca28d334618a2cc51462891343f9a1bc50be284f141f8a0bc5041e80f340079fc44fc227cf33e079ec44f422792f3c189dd3cec6675313a099cc44e422711137f99bc3cdc226cf335f8
|10,0=>0x2b7315b18ad4c56862b3315918ac4c56062af315718ab4c55862ab315518
|11,0=>0x15c17
|_,_=>0
def wAt:=mkWire dB 302 128 0xffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 17
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x10e50203d028451c03c02021178b302061020600283d0882102845010410203c0203d0e8430480b0203c0203d1a03f198470200d0403d0405d0e03c020450883d1780b0403d020610883d1504502821040410203c0900b048430203c0203d0203d0108d1103c0203104045040810f83d020630883d0480b0403d0203d0883d0405d0e03c020450a04d0203f02845028210203e0282102845010410203c0203d
|1=>0x18810020450883d020610883d0403d0480b0883d0203d0480b048430203c0203d0284502821048430203c0203d02821010410203c028450284502821010410203c0203d0900b048430203c0203d048430480b0203c0203d0882102845048430203c0203d0203f02845028210203e00841028210203c028450900b048430203c0203d028590b021088410203c028210203d0203c0284502845028210480b0203d
|2=>0x480b02845040450203d06041088210203c028210f9590c023020630883d0480b0204d0203e0283d0480b0883d0203d0405a088410203c198fb0200d0403d0403d088e51c03c0202102821010410203c0203d290470200d0280d0403d188201b04506821028451983f0200d1780b020610883d0092907013028212403d0211f0603d04045040e51c03c020212283f020fd0280e0683f02845040810f83d02063
|3=>0x40b1020600883d02859088410203c088210480b0403d0203d0203e0e03c0282107025028210203d0b02102859088410203c029210211f040613080b0211d040610480b0203c0203d028690405d0e03c02045041210211f0880d0403d290e00280d020210403d1c03e0203f040450403d0883d2e047029410884d0203e089690200f0403d2403d0211f040610883d18820020630883d0203d040450203c02845
|4=>0x17823020610883d0288d1103c020311c0600883d020210403d088e5028451c03c02021198630883d0200d0403d02845040450203f0203e04041040450203c02845028210480b0283d0203d048430480b0203c0203d1780b0403d020610883d0203d0108d1103c0203104045020630883d3083f0211d0603d040453583d020fb0880e0403d029230211f040610403d08821020630883d00841040450203c02845
|5=>0x28610883d0b023088410203c0200c020210403d0883d0e03c02045028453200b021e50403e1780b0283d020610883d041dd0200c0403d0283d15045040410203c188231b0450283d0203d1103c020310403d088210284502821088210203d2d03d0200f0203d028451c03c0202107047028211903d1c063020210883d0203d0105d0e03c020453083f0211d040610883d02821048430203c0203d020210880e
|6=>0x2045020600883d02821048430203c0203d308470211d040610883d0c05f0e03c020450883d0883d0405d0e03c020450480b0203c0203d040450403d020610883d1100c020310403d088210883d1b070020450283d0404502845028210203e02845028210203c0203d0203d028211c00c020210403d02061020600283d02845028210480b0203d01041040450203c0203d198470200d0880d0403d0206118820
|7=>0x403d0283d4503d020ff0280e0403d04045089210211f0603d040453a00b020f90880e0403d430440704d028210203e02158040620883d188231b0451c03c020210403d0a04d040450203f0203e0203f028450282102821040450203c0284541847020620203f02845028210203e02821040410203c1980b0200d0403d010e5028451c03c02021070470282101041040450203c0284502821008410203c02845
|8=>0x203d0883d020310403d088211103c02031040450203d040450403d0883d0203d0088d02031040450900b048430203c0203d178b302060020610883d0480b0204d0203e0203d188200683d028454a00b0224d0603e040453a00b020f90880e3a03f020f90880e0403d0284502821010410203c029d52d03d0200f04843040450203c0203d040620200f0283d0200e0704702821008e51c03c02021020210200c
|9=>0x28450200e0403d010e51c03c020210203d0e03c02045198470200d0403d029690200f0403d0403d088210203d0285f0e03c0204501845020210403d0211f04061008410203c028454d80f028110403d020230203d08a614b83e028120203d0683f028451980b0200d0403d0283d0200f0403d020600883d02821088210884d0203e1103c02031040450e03c020450883d028210480b0203d0e8430480b0203c
|10=>0x20230880e0880d0403d070470203f028210429d4d83c0281152807028250203d02862020450883d070470203c02821089690200f0403d028450203f0203e08a8d1b0130283d0e060020450883d0299a0404d0203e188130683d028450203f07045028210203c0704502821040410203c028450203d028620883d040620883d040451c047020210203f4d807028110883d04045028410203c0200d0880d0403d
|11=>0x883d0203d0200c0200d0403d0403d0883d0203f0285a088410203c02845040430203c08821028450203e590110703f02821028210283d0203d02aa54c83e02023578211b0100283d048430203c0203d020f90880e0403d020310403d088215280b028250203d042b506812028450403d0283d0203d0200c020210403d02845020210203d06826028450203d028e51c03c020210e03d020450202308aa54c83e
|12=>0x28450203e02845048230203d0211d0603d040450200f0200e0403d068510203f028450404d0203e020610883d040450c023020450883d0704d028210203e040450284502821040450203c0203d020ff0280e0403d1b2670283d0202304831040450203d15047040410203c0211c0603d0404501a5d0403d028124f045028410203c0480b040450203d041b5048470203d0405a088410203c0203f0280e04062
|13=>0x2821010410203c02821088210203d02859088410203c008410203c04045043210403d02047020fd0280e0403d020fa0880e0403d023001b0230283d008e51c03c020210407d020630883d0e00f020450403d1b0e0020210283d6103f0701102821020610883d020230403d020630883d023021b0230283d188230683d0284523847040610883d4d863028110883d18813028610883d330450404d0203e0684f
|14=>0x403d040450203f0203e6a00b0234d0883e04349028260203d18823028610883d08821040410203c020610883d02821330470404d0203e040450203f0284502060020450883d040450203c02845028be048450203d0883d0283d0203f0292e1c03f02021023350703c028214d860028110883d1c047020210403d07027028210203d0211d040610883d040410203c02845028aa040410203c1b0470283d0203f
|15=>0x200e0403d029d54c83d02023028be020610883d290100703d028211b0450283d0203d041c5020620883d0224d0603e04045020450200f0403d020600883d0283d0e03f02045020236103c07011028214d860028110883d0480b040450203d029b5048470203d02812020450883d088210403d0203f029751c03e02021088e51c03c020210883d0683f0203f028450203d0284502821040620883d0200f0880d
|16=>0x405f0e03c020457303e0701002821040620883d0203f0883d020210403d028210283d0203f06825028450203d0211e0603d04045020fb0880e0403d020210203f0284515045040410203c0283d0200e0403d0403d040620883d0603d040450203d0283d4d83c0281102159040620883d02861020450883d0224f0603e04045020ff0280e0403d4383d0e0230204570007068110284508b794b83d0281202a35
|17=>0xa0210203f0425d0403d028120c0230883d023c10703e02821028a9040410203c5683e0681202845089dd0200c0403d02159040620883d0203d06823028454383d0e023020450403d020610883d00bb14d83e02811028451c03c0202102abd1b0100283d4c83d020450202307024028210203d0200d0280d0403d02845028210203e18847028610883d0c25f0883d02812070530203f028210285d0e03c02045
|18=>0x20210203d5683d068120284500bc10703e02821088410203c028450480b0204d0203e0c25f0883d02812040450403d0883d029ce0a0450203f028210e03f020457303d07010028217d83d07013028217a83e068130284508a65020230405d0e03c02045018470200d0403d0884d0203e0283d0703c02821029dd0200c0403d1783f020610883d0283d068130284518810028610883d021e70403e0284579847
|19=>0x4833040450203d01b230403d020471b0450283d0203f0480b0883d0203d070430203c02821020fb0880e0403d06823028450203e044110e03e020450283d020610883d808230284d0203e028210203f028450284d028210203e028210203c0284508a65020230203d02a350200e0403d020450200f0403d02845020210403d020f80880e0403d04045010410203c028454c83e0202302047020210403d04847
|20=>0x203d88007028510203f02033040450203d040816403d02047188200683d02845028111b0100283d040450883d028210e03e02045028218683d02872020450a0450203f02821029dd0200c0403d02826020450203d08c2f07012028210a0310203f040450200f0280d0403d0283d020210403d02825020230203d1c00c020210403d040610883d0203f52823028250203d0200d0280e0403d110470203104045
|21=>0xc2650883d020231c047020210203d8703d02033040450480b0203c0203d02281028620883d0480b0283d0203d020450704702821028410203c028210244f0683e02845070470883e02821010410203c0203d18820028610883d6403d020470403d0883d040454b83d02045028120200f0403d028450f83d020630883d0e00c020450403d02845021e50403e1780b048450203d028210204d0203e0203104045
|22=>0x40451103e02031040450211f0603d040450203e0704502821020310203f04045023370703c02821048430203c0203d04059088410203c02c3b020330404508821020630883d068410203c0284502c3902033040450403d0883d0203d310120683f0284519847048210203d028210203c0203d029690200f0403d028210480b0203d7b83f08a65020238703e02033040450203d0704502821258471c03f02021
|23=>0x283d0683c028450204502821040450203e0284502821044810283e0e03f020450883e028210234f0883e028e2020210203f028450284d0203e0203c02845020450283d020210883d0283d028450203104045048210203d040450282102033040450281102047040620883d0202102045020210403d06813028454c83e0202304045028430203c040450204d0203e1b0470283d0203d0603d040451103f02031
|24=>0x203c0883e0283d020620883d024810283e4d83f028114d83e028110a0450203f0200f0403d040610883d0703f02821028e202021068230284508a5d028120200d0403d021e50403e0203f040450203c04045028610883d088430203c0283d020231c03e02021048470203d0403d0883e1c047020210603d04045068100284504321020470434d0883e0e03c020450703e028210683d0284506811028451b012
|25=>0x20450283e0883d0603e040450203f0203e0883d02821040410203c028260203d0880e0403d0883d0283d008410203c020230203d02a65020230203c0203d088410203c0480b0203d0200f0403d02021020470403d0883d1b0130283d024830283e0883d040450883d0203d028410203c020450203d02023028454d80702811028250203d020620883d0403d02047028430203c4c83d020230204d0203e02841
|26=>0x28114b83e02812028110283d0283d0203f0280e0403d010410203c0e02302045028210203e0883d0283d1b0470283d4d8230281102b4d0883e020600883d1b0130283d0883d028120280e0403d0403d0883d028210203d00c810283e02045028121b0100283d4b83d028124d83c028110404d0203e0883d0203f020600883d07045028210480b0203d028110883d0283d0203d020450203f028510203f02811
|27=>0x404502045028120203f0203c02811028210283d0203e0203d0283e0883d020470403e1b0100283d0681202845040450203d4d807
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x55000a00000000000
|6,0=>0x7340dca1a9000006550c2817500000000000016142a20504098812100000000088810101da800000000dd019282e4054809900000224000000000000000000007900d20000000000000aa80000000048c07200a4000000000000000
|7,0=>0x1ea23cc800000001e0600007620e931cc638cc6fa0db4000035d06b08d2419c832cc63a0000188630100000bc400002e105a20b1315a82a8c0000a73146827d04da0000000000000000000000026484b90000000000004a9092311e622d044188530000000000000001064200c3e9800000001ec83ba0000
|7,1=>0x6590ca119130000638cc52186430480000bf217b32f065d4cb8a00002da85a5000016632c48000000015e400000000ad2158200005510a9114e400005290a321424000050089e993a326c84c9097212a40000499091211e4234846448aa113221e8000085a00000000420c822000020083f4c7d18f64
|7,2=>0x476800011ba233446068b1114222534428875000021a342c88491079a0b400008284000000040e60001029000040467f900001fa43f227d50f8a1ed43d467a08f299e140000778c0001da43b040000ea200000000744ce719ca439040000e221c0400006f4cdca1b5400006c50d6a1aa334c86890cf219a4
|7,3=>0x8fd00000000
|8,0=>0x5f66be0d7a9af230000bbcd761ae935cc6b8cd701add35b46b5cd6a1ad1359c6b2cd641ac535846afcd5e1ab9356c6accd581aad35546a9cd521aa1353c6a6cd4c1a9535246a3cd461a89350c6a0cd401a7d34f469dcd3a1a7134dc69acd341a6624c66980d2f125b34b06954d291a4f34986924d231a433
|8,1=>0x7726ed8dd99bb0375a6ea8dd39ba437426e78dcd9b98372a6e48dc79b8c37126e18dc19b8036fa6de8dbb9b7436e26db8db59b6836ca6d88daf9b5c36b26d58da99b50369a6d28da39b4436826cf8d9d9b38366a6cc8d98132d36546c9cd921b21363c6c6cd8c1b1536246c3cd861b09360c6c0cd8092fe3
|8,2=>0x8e671c0e369c6a38ce7190e309c5e38b67160e2a9c52389e7130e249c4638867100e1e9800087470dce1a1c31385c70ace141c253844707ce0e1c19382c704ce081c0d3814701ce021c0137fc6fecdfc1bf537e46fbcdf61be937cc6f8cdf01bdd37b46f5cdea1bd1379c6f2cde50bc737886f089df9bbc3
|8,3=>0xa6074b4e951d273a487484e8f1d1b3a307454e891d0f3a187424e831d033a0073f4e7d1cf739e873c4e771ceb39d07394e711cdf39b87364e6b1cd339a07334e651cc739887304e5f1cbb397072d4e591caf395872a4e531ca339407274e4d9498392a724ca481c8d3914721ce421c8138fc71ece3c94763
|8,4=>0xb94771cee21dc22b7e76f0edc9db63b6676c0ed69daa3b4e7690ed09d9e3b367660eca9d923b1e7630ec49d863b067600ebe9d7a3aee75d0eb89d6e3ad675a0eb29d623abe7570ead15573aa87544ea71d4b3a907514ea11d3f3a7874e4e9b1d333
|9,0=>0xc965924b2396452c865904b1f963d2c7658e4b1b96352c6658c4b17962d2c5658a4b1396252c465884b0f961d2c365864b0b96152c265844b07960d2c165824b0396052c065804aff95fd2bf657e4afb95f52be657c4af795ed2bd657a4af395e52bc65784aef95dd2bb65764aeb95d52ba65744ae795cd2
|9,1=>0x6c52d865b04b5f96bd2d765ae4b5b96b52d665ac4b5796ad2d565aa4b5396a52d465a84b4f969d2d365a64b4b96952d265a44b47968d2d165a24b4396852d065a04b3f967d2cf659e4b3b96752ce659c4b37966d2cd659a4b3396652cc65984b2f965d2cb65964b2b96552ca65944b27964d2
|10,0=>0x36a0ed31da43b447680ecf1d9c3b347660ecb1d943b247640ec71
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 15
def pmP:Nat→Nat
|0=>0x21b800000010d80000000840000000041f00000002080000000101800000008080000000402000000020000000000c00000000040800000002000000000049000000001200000000084000000004000000000180000000007c00000000380000000016000000000a800000000500000000020000000000c000000000500000000020000000000c000000000500000000020000000000c00000000040000000000
|1=>0x92200000004908000000240c000000106600000008310000000411800000020800000001022000000080600000004020000000200c00000010040000000801000000040040000001cfe0000000e1f00000006af8000000347c0000001a3a0000000c5d000000061f8000000307c00000018080000000c00000000040f800000020180000001004000000080100000004000000000117c00000008aa000000043f
|2=>0x1c1f8000000d07c000000604800000030000000001406000000081200000004018000000200800000010020000000800400000040000000001e000000000e29000000070fc000000386c0000001c1f0000000e040000000701000000030a800000018500000000c2200000006100000000307e000000180c0000000c03000000060100000002c0800000014540000000a050000000500800000028000000001323
|3=>0x860f800000428fc0000021468000001083f00000084190000004207c000002100c00000108000000008129000000408d000000200ac00000100320000008001000000400000000011c1e0000008c1f00000046078000001c048000000e00c0000007002000000340500000019038000000c0040000005c1f0000002c1f8000001507c000000a07e0000004c3f000000260f8000001207c00000080080000003c1f
|4=>0x10a3b0000008507c000004207e000002101f000001078f800000838fc0000041c3e0000020c3f000001060f8000008207c0000040cbe000002045f000001021f8000008087c000003047e000001803f000000a60f8000004d060000002583e000001201c0000008f08000000470fc000002383e00000116140000008a0f8000004487c000002242c0000011056000000881f8000004407c000002202c0000010c3f
|5=>0x1860f800000c305c000006123e000003085f000001840f800000c00fc000004787e000002383d0000011c0f8000008c0fc000004587e000002201f0000010f1f800000878dc0000043c3e0000021c7f0000010e1f800000870dc000004383e0000021b3f0000010d2b800000868fc000004327e000002191f0000010c1f800000860ec000004306c00000218170000010b2b000000859400000042c3e0000021576
|6=>0x80a01000002000fc00000c0cbe0000060636000003022b8000018107c00000c040e00000600000000028e1f8000014605800000a28280000050c150000021806000001071fc00000838be00000418000000020a03000001031fc00000818f60000040c5f000002042a80000102000000006683e000003281f0000018e1f800000c68dc000006342e000003141f000001871f800000c387c0000061a3e0000030c5f
|7=>0x400002000020000000000c0007e0000201c3f000010080f8000080307c000040107e000013341f000009840f8000048f0fc000024483e0000121c3f000009081f800004840b0000024203e0000110412000008240f800004120000000208810000010421f000008210b8000041007c000020802e000010401000000820030000040f0fc000020682e0000102c3f000008160f800004090ec000020383e0000101c00
|8=>0x411c1f800020864fc000104207e0000820c3f000041060f800020810fc000102583e000081101a000040840100002014058000100a0180000805004000040260700002012010000100883e000080421b0000402007000020100300001008014000080400600004020000000200b0fc0001003030000080180a0000400c04000020040fc0001002044000080100a000040060f8000200207c000100004c000080000a
|9=>0x83000f800040c587c000206283e0001020c1f000081021f8000408107c00020404960001011c3f0000808e0f800040071fc0002003020000100180a0000800c03000040040400002001cfe0001000c7f000049961f800024c307c000126007e000092383f000049161f8000248907c0001242876000092043f0000489e0f800024430fc000120787e0000902c3f000048060f8000240107c000106283e0000830c1f
|10=>0x8088e08000404160fc002020183e001007141f0008018c0e8004008907c002004387e001002181d000801020f800400130fc002000380000100010080006100617800108030fc000406103e000202183f000101081f8000808347c000404183e0002010844000100840200008041000000400306c00020014350001000a100000800408000040018be0002000c1f0000c1020f8000600602800020e283e0001060e3f
|11=>0x80082e0f8040041107c020020503e0100100c3f008008000f804000c307c020002987e0100005c1f008000260f8040000a07c0200005008010000241e0060481c1f803020060fc018004387e00c0021c3e0060010c1f8010008707c0040001c3c0020000c1f001000060f000480860fc002120903e0010901c1f0008480c1f80042405074002120083e001090001f000840020f800420010280021000024001013341f
|12=>0x2000410c1f9000208207c8001005c2e4000121c1f200001901f9000008f0fc800004707e4000021c3f200000140f90000008030800000183e4000000414200000002010000000040608000187e180003141f0c00001a0f8410000b0fc080010187e0200221c3f0100108e1f808008070fc0400401c5e0200200c3f0100100617804020870fc020022187e010010783f0080083a0f8040041907c020020c43e010010620e
|13=>0x2000840185e8000901c1f208040060f9004008e0fc800126503e4000922c1f
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x5028000000
|6,0=>0x30281400050180400000001c0a050181c0000028140a000000c0e01028480005000000000000200200000001e000000c0a06000000000
|7,0=>0x14ae060000c0a91190001206018040a000401c00120d80000211c800181400014460400378088200104e6051e01c0a070043430fb029543c01190004c100000c74000381822198595c0000018000e03018041002000d9fc3d2b0d008002c01c000700020260304018000398a4012000000000000005c4600000002c010e89006330000000003c00c0c00000040a10
|7,1=>0x3f40000510403e850ebec88010d86800011a8140276001c9b00000800460001c000025a3090680b1405c24860001400eb2e0000a00081842a05118000e0500160e8040032d9a033a865e4e7
|8,0=>0xa94b6ae9b374ec0e52882d86f1e3466940650543e364f378372d6d60d093d20c88d470f42fd30749eb1cff3248a055a184c29e921c7767b91d87e5dbdd3a2e6145e47895d53484d5298d68a2a08436fef08dde9073551e3205189b4064d1c52a5e73758e5c5a7765d8aab2cc8d5a1dcef16651b251b86749b15c6880f304440ac7e03b5c15fe97afbf2086b6e2699c74
|8,1=>0x73600d4f336c11702758c1e52a6179523b922030978e0a9dde676249a325005713a57f081dc52787189aad8d02c7d11f42950adcd86233992943199169cba3a4598904654481946016c0d84d6b0d1d098e88b8d8b7984b9d6896bc2d45600319393edf832c576471790db68b92272a8509a53ee4c8c3678b68dafacd12a42cd25c85d3b66eb0458d26b2755063409630
|8,2=>0x151f51c4a5524d76ed28941054e138fa479740a3d3a7ccf61ea297742a696ae5dbe5e3a5beb8ca17448088d295adc49a8b08b628f6b2b72f97a1c
|9,0=>0x1278130ede9792b868670a85f1eaf5cfbe1a3255fca92985c85a97ebf4c4c0a07f7662d728a296714f5c620ab042a97ce9936c40684f945c44dd59417a2b52ad7ca94ad37357b49802a3fa0341602931f310a281fdbb7e96591913845265335a154b856809f2a52a625ecf4565eb2d9e3266c2269d5212960ca11eaecaebaf6584895452c0aef44da5394abc2a
|10,0=>0x124495d8a8551fbdca8568062070f487
|11,0=>0xe
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 9 (j%128);fld (pmP (k/32)) 41 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_125 10 roots_125 ops++addP pm 1 dom_119 9 roots_119 ops++addP pm 2 dom_126 9 roots_126 ops++addP pm 3 dom_95 9 roots_95 ops++addP pm 4 dom_123 10 roots_123 ops++addP pm 5 dzo_111_16 7 roots_111 ops++addP pm 6 dom_54 4 roots_54 ops++addP pm 7 dzo_43_4 5 roots_43 ops++addP pm 8 dom_103 5 roots_103 ops++addP pm 9 dom_118 7 roots_118 ops++addP pm 10 dom_63 8 roots_63 ops++addP pm 11 dom_111 8 roots_111 ops++addP pm 12 dzo_47_16 6 roots_47 ops++addP pm 13 dzo_94_32 6 roots_94 ops++addP pm 14 dom_86 5 roots_86 ops++addP pm 15 dom_107 7 roots_107 ops++addP pm 16 dom_43 5 roots_43 ops++addP pm 17 dzo_86_32 5 roots_86 ops++addP pm 18 dom_62 5 roots_62 ops++addP pm 19 dom_59 7 roots_59 ops++addP pm 20 dzo_95_32 7 roots_95 ops++addP pm 21 dzo_107_4 6 roots_107 ops++addP pm 22 dzo_123_4 7 roots_123 ops++addP pm 23 dzo_87_32 6 roots_87 ops++addP pm 24 dom_55 5 roots_55 ops++addP pm 25 dom_110 5 roots_110 ops++addP pm 26 dzo_59_4 6 roots_59 ops++addP pm 27 dom_122 7 roots_122 ops++addP pm 28 dom_94 6 roots_94 ops++addP pm 29 dom_109 7 roots_109 ops++addP pm 30 dzo_109_2 6 roots_109 ops++addP pm 31 dzo_109_16 6 roots_109 ops++addP pm 32 dom_87 6 roots_87 ops++addP pm 33 dzo_107_16 6 roots_107 ops++addP pm 34 dom_115 7 roots_115 ops++addP pm 35 dzo_93_2 6 roots_93 ops++addP pm 36 dom_61 6 roots_61 ops++addP pm 37 dom_117 7 roots_117 ops++addP pm 38 dom_77 5 roots_77 ops++addP pm 39 dzo_77_2 5 roots_77 ops++addP pm 40 dom_91 7 roots_91 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_127 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_111_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_zo_43_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_47_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_zo_94_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_86_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_zo_95_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_107_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_123_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_87_32_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_59_4_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_zo_109_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_109_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_107_16_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_zo_93_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_zo_77_2_77 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_91 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_125 10 s (0,roots_125.map (·&&&dom_125)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_127 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_125 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_127==dom_127)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_127 gM v ys):RunD true dom_127 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_127 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 50 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 50 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_128 : ∀ i, 128 ≤ i → i < 195 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 67 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 195 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_256 : ∀ i, 256 ≤ i → i < 308 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 52 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 308 → Z 8 i = true := (range_split z8_0 (range_split z8_128 z8_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 125 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 125 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)
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
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_slice_b [(0xcccccccccccccccc0000000000000000cccccccccccccccc,16,18)] (by decide +kernel) lowS_189
theorem lowS_223:Lower true dom_223 roots_223 goal_223 12:=lower_slice_b [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,16,18)] (by decide +kernel) lowS_221
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=lower_slice_b [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,32,34)] (by decide +kernel) lowS_237
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00ee00000000
def gsh_215_32:=0xff00ff0000000000ff00fe0000000000ff00fe0000000000fe00ee
theorem lowS_zo_215_32_212:Lower true dzo_215_32 roots_215 gzo_215_32 9:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2)] (by decide +kernel) lowS_212)
namespace S_247
def pG:List (Nat×Nat):=[(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,23),(7,39),(7,71),(7,135),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,49),(17,81),(17,145),(32,33),(32,34),(36,37),(36,38),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,112),(48,176),(64,65),(64,68),(64,80),(64,192),(66,67),(66,70),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,192),(160,161),(160,162),(160,164),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3fffffffffffffffff
def xsM:=roots_247.map (·&&&dom_247)
def gM:=goal_247&&&dom_247
def NN:Nat→Nat
|6=>7
|7=>18
|8=>18
|9=>11
|10=>4
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0xfb8acf5837b383da1511702a8424673e397
|7,0=>0xf94e5f3470eb00be1b50dbadbd370dcf824c75d4c155fbc51bb844bb26ccae5fca2a77877b5750fe0a2810561e
|8,0=>0xced18b3452a619b785dd735996f4c9568d5439724168837839317c42d42f2ceb62c7802a99d286b015b310fabc
|9,0=>0xc6b3ac1903b18ed88c4385d966f2da52ea730b150e181026a7019af
|10,0=>0xcd3dd7fd216aad412103
|11,0=>0x3ef7d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f0000000000000000000f0000000f0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000000000000000000000000000000000000f000f000f000f000f0000000f0000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000ff000000ff000000ff000000ff000000ff000000ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000
|0,1=>0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000000000000000000000000000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000
|_,_=>0
def sP:Nat→Nat
|0=>0x39a0418820399a208168398ad20820598691050731483488267104103166690410316668d220c5062906910626715220ad067082f51cd0105ea399c41058f3344162d4628d220a0c310408398a418820
|1=>0x39a041a44139a0d1a44139a0522441899a910568398820822b398ad22441599c41040b39a041040b399c34882839a034882839a0568d22099c41040f39a041040f399c520820599a20816a399c418820
|2=>0x488313ce044882b39889105683ca044882b39a052244159ccd224418acc41040b399a41a44189a0d4883133a041a441399cd4882b41cce2b489105667408208167338a44882b339a41040b399c41a441
|3=>0x188910567911220ace6811220ace6691220acf32244159cce811220ace6291220ace67348910567334834882b399c44882b39a04
|_=>0
def sO:Nat→Nat→Nat
|6,0=>0xa9c46e1c70ab839c0ee007
|7,0=>0x16f0af853c27e12f08f843c1fe0ef06f833c181cb2e51824c1060730318
|8,0=>0x296f4389e3cce65532198c4c4220f2ff87bc3be1cf0df86bc33e18f0bf8
|9,0=>0x69673b1949c5ce0e2f71738b5c58e2b53528
|10,0=>0xe2bef636b1ae7
|11,0=>0x1cc7
|_,_=>0
def wAt:=mkWire dB 20 248 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 5 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x21d81f02f81d22d02f72781d22d72781d81f22d0137276ad21d6af7276ad21d72772f81d22d7137276ad21d71f7276ad21d6af7136ad21d6af71f6ad21d01f81d22d01f7276ad21d6af59d72f71f89159d81f71381d59102f72781d01f7276ad
|1=>0x21d72781d22d6af59d21d22d59d21d72f81d22d7136ad21d71f6ad21d72781d22d81d81f22d7276ad21d58d6af21d72f81d22d5b621d59159d81f22d7136ad21d72789159d71f6ad21d72781d22d72781d22d6af7136ad21d71372f81d22d5b6
|2=>0x31f22d21d31d81d22d81f22d6ad21d6af21d81d22d59d22d22d31d89359d22d31f81f22d59d
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x33000003000000000
|7,0=>0x4544143e33b33743342f42b42742341f41b41741431040e20a4064
|8,0=>0x7c37937637337036d36a36736436135e35b35835535234f34c3493
|9,0=>0x9329128f28d28b28928728528328127f2
|10,0=>0x981971961951
|_,_=>0
def PO:=mkPO wAt oP oO 12 5 31 12
def pmP:Nat→Nat
|0=>0x3df97e177fddf37c7f17c5713c2f058120380c028060140400c0200400
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x4010000
|7,0=>0x87510c1404631a0a430944
|8,0=>0x24f932944b96d83df595652
|9,0=>0x4e56b4a5294672
|10,0=>0x8ca52
|11,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 10 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_246 10 roots_246 ops++addP pm 1 dom_231 9 roots_231 ops++addP pm 2 dom_243 10 roots_243 ops++addP pm 3 dom_119 9 roots_119 ops++addP pm 4 dom_183 9 roots_183 ops++addP pm 5 dom_167 5 roots_167 ops++addP pm 6 dom_245 10 roots_245 ops++addP pm 7 dom_215 9 roots_215 ops++addP pm 8 dzo_215_32 9 roots_215 ops++addP pm 9 dom_103 5 roots_103 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_247 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_215_32_212 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_103 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_246 10 s (0,roots_246.map (·&&&dom_246)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_247 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_247==dom_247)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_247 gM v ys):RunD true dom_247 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_247 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_247 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(16,18),(16,80),(16,144),(17,19),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(64,192),(66,67),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,136),(128,144),(128,192),(160,161),(160,162),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|10=>1
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|10,0=>0x294df
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x1ec688fac688
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
|0=>0xa5
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
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_123 10 roots_123 ops++addP pm 2 dom_249 10 roots_249 ops++addP pm 3 dom_243 10 roots_243 ops++addP pm 4 dom_219 10 roots_219 ops++addP pm 5 dom_235 9 roots_235 ops++addP pm 6 dom_187 9 roots_187 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_187 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
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
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_slice_b [(0x3333333300000000333333330000000033333333000000003333333300000000,1,33)] (by decide +kernel) lowS_221
def isoMvS_254:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_254:Lower true dom_254 roots_254 goal_254 12:=lower_iso_b isoMvS_254 (by decide +kernel) lowS_247
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,18),(2,34),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,40),(8,72),(8,136),(10,11),(10,26),(10,42),(10,74),(10,138),(12,13),(12,28),(12,44),(12,76),(12,140),(14,15),(14,30),(14,46),(14,78),(14,142),(16,18),(16,20),(16,80),(16,144),(17,19),(17,21),(17,25),(17,49),(17,81),(17,145),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,34),(32,40),(36,37),(36,38),(36,44),(36,52),(36,100),(36,164),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,68),(64,72),(64,80),(64,192),(66,67),(66,70),(66,74),(66,82),(66,98),(66,194),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,136),(128,144),(128,192),(160,161),(160,162),(160,164),(160,168),(160,176),(160,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|12=>1
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|12,0=>0x8fd7c
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x86543210876543210
|_=>0
def sO:Nat→Nat→Nat
|12,0=>9
|13,0=>0x98
|_,_=>0
def wAt:=mkWire dB 9 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x185
|_=>0
def oO:Nat→Nat→Nat
|12,0=>1
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 5
def pmP:Nat→Nat
|0=>0xff00
|_=>0
def pmB:Nat→Nat→Nat
|12,0=>1
|13,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 1 (j%128);fld (pmP (k/32)) 8 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_127 12 roots_127 ops++addP pm 2 dom_253 12 roots_253 ops++addP pm 3 dom_251 12 roots_251 ops++addP pm 4 dom_247 12 roots_247 ops++addP pm 5 dom_223 12 roots_223 ops++addP pm 6 dom_239 11 roots_239 ops++addP pm 7 dom_191 11 roots_191 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_191 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [4, 7] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.or, inputs := [6, 1] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [12, 2] }, { op := GateOp.or, inputs := [11, 2] }, { op := GateOp.or, inputs := [1, 9] }, { op := GateOp.and, inputs := [5, 15] }, { op := GateOp.and, inputs := [13, 10] }, { op := GateOp.and, inputs := [8, 14] }, { op := GateOp.and, inputs := [3, 0] }, { op := GateOp.or, inputs := [16, 17] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_52422_aux

theorem PEqualNP.Outside.L_meta_52422 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_52422_aux.main
