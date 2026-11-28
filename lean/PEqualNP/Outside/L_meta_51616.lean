import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51616_aux
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
def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00fcfccc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefeee00fefeee00fefeee00fefeee00fefeee00fefeee00fefeee00fefeee00
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffaaffaaee00ee00ffaaffaaee00ee00ffaaffaaee00ee00ffaaffaaee00ee00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00fffafffaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfff0fff0cc00cc00fff0fff0cc00cc00fff0fff0cc00cc00fff0fff0cc00cc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffafffaee00ee00fffafffaee00ee00fffafffaee00ee00fffafffaee00ee00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcf0f0fcfc0000fcfcf0f0fcfc0000fcfcf0f0fcfc0000fcfcf0f0fcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefafafefe0000fefefafafefe0000fefefafafefe0000fefefafafefe0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccff00cccccc00ffccff00cccccc00ffccff00cccccc00ffccff00cccccc00
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffaaeeeeee00ffeeffaaeeeeee00ffeeffaaeeeeee00ffeeffaaeeeeee00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0xfff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000fff0fff0f0f00000
def roots_60 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafffafafaaa00fffafffafafaaa00fffafffafafaaa00fffafffafafaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefffafefeee00fffefffafefeee00fffefffafefeee00fffefffafefeee00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_74 : Nat := 0x5050000000000000505
def goal_74 : Nat := 0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
def roots_74 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeee00ee00ee00ee00ffeeffeeffeeffeeee00ee00ee00ee00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfffafffafffafffaaa00aa00aa00aa00fffafffafffafffaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_78 : Nat := 0x55550000000000005555
def goal_78 : Nat := 0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
def roots_78 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfffefffefffefffeee00ee00ee00ee00fffefffefffefffeee00ee00ee00ee00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_84 : Nat := 0x1100110000000000110011
def goal_84 : Nat := 0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
def roots_84 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfffffafafffffafafafa0000fafa0000fffffafafffffafafafa0000fafa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfcfcfc0000fcfc0000fffffcfcfffffcfcfcfc0000fcfc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefefefe0000fefe0000fffffefefffffefefefe0000fefe0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffffaaffffffaaaaaaaa00aaaaaa00ffffffaaffffffaaaaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccccc00cccccc00ffffffccffffffcccccccc00cccccc00
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffeeffffffeeeeeeee00eeeeee00ffffffeeffffffeeeeeeee00eeeeee00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_92 : Nat := 0x111111110000000011111111
def goal_92 : Nat := 0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
def roots_92 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffffffafffffffafafaaa00fafaaa00fffffffafffffffafafaaa00fafaaa00
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffffffcfffffffcfcfccc00fcfccc00fffffffcfffffffcfcfccc00fcfccc00
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffffefffffffefefeee00fefeee00fffffffefffffffefefeee00fefeee00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefafafafa00000000fefefefefefefefefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaffaaffaaaa00aa00ffaaffaaffaaffaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffccff00ff00cc00cc00ffccffccffccffccff00ff00cc00cc00
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeeffaaffaaee00ee00ffeeffeeffeeffeeffaaffaaee00ee00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafffafffaaa00aa00fffafffafffafffafffafffaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcfff0fff0cc00cc00fffcfffcfffcfffcfff0fff0cc00cc00
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffefffefffafffaee00ee00fffefffefffefffefffafffaee00ee00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeaaaaeeee0000ffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f0f0f00000fffff0f0fffff0f0f0f0f0f0f0f00000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafafffffafafafafafafafa0000fffffafafffffafafafafafafafa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcf0f0fcfc0000fffffcfcfffffcfcfcfcf0f0fcfc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefafafefe0000fffffefefffffefefefefafafefe0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_120 : Nat := 0x1010101010101010101010101010101
def goal_120 : Nat := 0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffffaaffaaffaaaaaaaa00ffffffaaffffffaaffaaffaaaaaaaa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffffccffccff00cccccc00ffffffccffffffccffccff00cccccc00
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffeeffeeffaaeeeeee00ffffffeeffffffeeffeeffaaeeeeee00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_124 : Nat := 0x11111111111111111111111111111111
def goal_124 : Nat := 0xfffffff0fffffff0fff0fff0f0f00000fffffff0fffffff0fff0fff0f0f00000
def roots_124 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffffffafffffffafffafffafafaaa00fffffffafffffffafffafffafafaaa00
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffffffcfffffffcfffcfff0fcfccc00fffffffcfffffffcfffcfff0fcfccc00
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffffefffffffefffefffafefeee00fffffffefffffffefffefffafefeee00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfefefefefefefefefefefefefefefefeee00ee00ee00ee00ee00ee00ee00ee00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_148 : Nat := 0x11001100000000000000000000000000110011
def goal_148 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
def roots_148 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefefefe0000fefe0000fefe0000fefe0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeee00eeeeee00eeeeee00eeeeee00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffafafffffafafffffafafffffafafafaaa00fafaaa00fafaaa00fafaaa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffefefffffefefffffefefffffefefefeee00fefeee00fefeee00fefeee00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffefefefefffffffffefefefefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeffaaffaaee00ee00ffaaffaaee00ee00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfff0fff0cc00cc00fff0fff0cc00cc00
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffefefefefffffffffefefefefffafffaee00ee00fffafffaee00ee00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafafafafafa0000fafafafafafa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0fcfc0000fcfcf0f0fcfc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefefefefafafefe0000fefefafafefe0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffff0000ffffffffffff0000ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffaaffaaaaaaaa00ffaaffaaaaaaaa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffeeffaaeeeeee00ffeeffaaeeeeee00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffafafffffffffffffafafffafffafafaaa00fffafffafafaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffcfff0fcfccc00fffcfff0fcfccc00
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffefefffffffffffffefefffefffafefeee00fffefffafefeee00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaaaaaaaaaaaaaaaaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccccccccccccccccccffccffccffccffcccc00cc00cc00cc00
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeeeeeeeeeeeeeeeeeffeeffeeffeeffeeee00ee00ee00ee00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafafafafafafafafafffafffafffafffaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfcfcfcfcfcfcfcfcfffcfffcfffcfffccc00cc00cc00cc00
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefefefefefefefefefffefffefffefffeee00ee00ee00ee00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfcfc0000fcfc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefefffffefefffffefefefe0000fefe0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffff0000ffff0000ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffaaaaffffaaaaffffffaaffffffaaaaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffccccffffccccffffffccffffffcccccccc00cccccc00
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffeeeeffffeeeeffffffeeffffffeeeeeeee00eeeeee00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffafffffafafffffafafffffffafffffffafafaaa00fafaaa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffcfcfffffcfcfffffffcfffffffcfcfccc00fcfccc00
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffefefffffefefffffffefffffffefefeee00fefeee00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffefefefefefefefefefefefefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ffffffff00000000ff00ff00ff00ff00ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffaaaaaaaaffaaffaaffaaffaaffaaffaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffccccccccffccffccffccffccff00ff00cc00cc00
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffeeeeeeeeffeeffeeffeeffeeffaaffaaee00ee00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffff0f0f0f0fff0fff0fff0fff0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffafafafafffafffafffafffafffafffaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffcfcfcfcfffcfffcfffcfffcfff0fff0cc00cc00
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffefefefefffefffefffefffefffafffaee00ee00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeffffeeeeeeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafffffafafffffafafafafafafafa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcfffffcfcfcfcf0f0fcfc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffefefffffefefffffefefefefafafefe0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffff0000ffffff00ffffff00ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffaaaaffffffaaffffffaaffaaffaaaaaaaa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffccccffffffccffffffccffccff00cccccc00
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffeeeeffffffeeffffffeeffeeffaaeeeeee00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffff0f0fffffff0fffffff0fff0fff0f0f00000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffafafffffffafffffffafffafffafafaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffcfcfffffffcfffffffcfffcfff0fcfccc00
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffefefffffffefffffffefffefffafefeee00
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
def isoMvS_74:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_74:Lower true dom_74 roots_74 goal_74 4:=lower_iso_b isoMvS_74 (by decide +kernel) lowS_41
def isoMvS_81:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_81:Lower true dom_81 roots_81 goal_81 4:=lower_iso_b isoMvS_81 (by decide +kernel) lowS_41
def isoMvS_82:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_82:Lower true dom_82 roots_82 goal_82 4:=lower_iso_b isoMvS_82 (by decide +kernel) lowS_41
def isoMvS_84:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_84:Lower true dom_84 roots_84 goal_84 4:=lower_iso_b isoMvS_84 (by decide +kernel) lowS_41
def isoMvS_145:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_145:Lower true dom_145 roots_145 goal_145 4:=lower_iso_b isoMvS_145 (by decide +kernel) lowS_41
def isoMvS_148:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_148:Lower true dom_148 roots_148 goal_148 4:=lower_iso_b isoMvS_148 (by decide +kernel) lowS_41
def isoMvS_161:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_161:Lower true dom_161 roots_161 goal_161 4:=lower_iso_b isoMvS_161 (by decide +kernel) lowS_41
namespace S_29
def pG:List (Nat×Nat):=[(1,9),(1,17),(4,20),(5,13),(5,21),(8,9),(12,13),(12,28),(16,17),(16,20),(24,25),(24,28)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfff
def xsM:=roots_29.map (·&&&dom_29)
def gM:=goal_29&&&dom_29
def NN:Nat→Nat
|3=>1
|_=>0
def HT:Nat→Nat→Nat
|3,0=>0x36cd4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xcccc00033003300c0c0c0c22222222
|_,_=>0
def sP:Nat→Nat
|0=>0xe4
|_=>0
def sO:Nat→Nat→Nat
|3,0=>4
|_,_=>0
def wAt:=mkWire dB 4 30 0x3fffffff
def SS:=mkSS wAt sP sO 2 7
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def PO (_ _:Nat):List (Nat×Nat×Nat):=[]
def mkPools (_ _:Nat):List (Nat×Nat×(Nat×List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat×Nat×Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_29 gM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_29 gM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_29==dom_29)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 gM v ys):RunD true dom_29 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_29 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s:Nat) (hs:s≤3):∀ i<NN s,bar dom_29 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPoolG e.1 e.2.1 (s'-1) e.2.2 g zs) s i=true;rw [←barP_eq];interval_cases s
  · simp [NN] at hi
  · simp [NN] at hi
  · simp [NN] at hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤3) (h:RunD true dom_29 gM s xsM):False:=by
  have hmin:3≤s:=by have hl:=run_len h;change 4≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29 4:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_29
theorem lowS_29:Lower true dom_29 roots_29 goal_29 4:=S_29.noCircuit
theorem lowS_43:Lower true dom_43 roots_43 goal_43 5:=lower_slice_b [(0xc0c00000c0c,8,10)] (by decide +kernel) lowS_41
theorem lowS_75:Lower true dom_75 roots_75 goal_75 5:=lower_slice_b [(0xa0a0000000000000a0a,8,9)] (by decide +kernel) lowS_74
def isoMvS_30:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_30:Lower true dom_30 roots_30 goal_30 4:=lower_iso_b isoMvS_30 (by decide +kernel) lowS_29
def isoMvS_45:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45:Lower true dom_45 roots_45 goal_45 5:=lower_iso_b isoMvS_45 (by decide +kernel) lowS_43
def isoMvS_46:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_46:Lower true dom_46 roots_46 goal_46 4:=lower_iso_b isoMvS_46 (by decide +kernel) lowS_29
def isoMvS_51:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_51:Lower true dom_51 roots_51 goal_51 4:=lower_iso_b isoMvS_51 (by decide +kernel) lowS_29
def isoMvS_54:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_54:Lower true dom_54 roots_54 goal_54 4:=lower_iso_b isoMvS_54 (by decide +kernel) lowS_29
def isoMvS_57:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_57:Lower true dom_57 roots_57 goal_57 5:=lower_iso_b isoMvS_57 (by decide +kernel) lowS_43
def isoMvS_58:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_58:Lower true dom_58 roots_58 goal_58 4:=lower_iso_b isoMvS_58 (by decide +kernel) lowS_29
def isoMvS_60:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_60:Lower true dom_60 roots_60 goal_60 4:=lower_iso_b isoMvS_60 (by decide +kernel) lowS_29
def isoMvS_77:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_77:Lower true dom_77 roots_77 goal_77 5:=lower_iso_b isoMvS_77 (by decide +kernel) lowS_43
def isoMvS_78:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_78:Lower true dom_78 roots_78 goal_78 5:=lower_iso_b isoMvS_78 (by decide +kernel) lowS_43
def isoMvS_83:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_83:Lower true dom_83 roots_83 goal_83 5:=lower_iso_b isoMvS_83 (by decide +kernel) lowS_75
def isoMvS_85:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_85:Lower true dom_85 roots_85 goal_85 5:=lower_iso_b isoMvS_85 (by decide +kernel) lowS_75
def isoMvS_86:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_86:Lower true dom_86 roots_86 goal_86 5:=lower_iso_b isoMvS_86 (by decide +kernel) lowS_75
def isoMvS_89:List (Nat×Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_89:Lower true dom_89 roots_89 goal_89 5:=lower_iso_b isoMvS_89 (by decide +kernel) lowS_75
def isoMvS_90:List (Nat×Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_90:Lower true dom_90 roots_90 goal_90 5:=lower_iso_b isoMvS_90 (by decide +kernel) lowS_75
def isoMvS_92:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_92:Lower true dom_92 roots_92 goal_92 5:=lower_iso_b isoMvS_92 (by decide +kernel) lowS_43
def isoMvS_99:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_99:Lower true dom_99 roots_99 goal_99 4:=lower_iso_b isoMvS_99 (by decide +kernel) lowS_29
def isoMvS_102:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_102:Lower true dom_102 roots_102 goal_102 4:=lower_iso_b isoMvS_102 (by decide +kernel) lowS_29
def isoMvS_105:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_105:Lower true dom_105 roots_105 goal_105 5:=lower_iso_b isoMvS_105 (by decide +kernel) lowS_75
def isoMvS_106:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_106:Lower true dom_106 roots_106 goal_106 5:=lower_iso_b isoMvS_106 (by decide +kernel) lowS_43
def isoMvS_113:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_113:Lower true dom_113 roots_113 goal_113 5:=lower_iso_b isoMvS_113 (by decide +kernel) lowS_43
def isoMvS_116:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_116:Lower true dom_116 roots_116 goal_116 5:=lower_iso_b isoMvS_116 (by decide +kernel) lowS_43
def isoMvS_120:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_120:Lower true dom_120 roots_120 goal_120 4:=lower_iso_b isoMvS_120 (by decide +kernel) lowS_29
def isoMvS_147:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_147:Lower true dom_147 roots_147 goal_147 5:=lower_iso_b isoMvS_147 (by decide +kernel) lowS_75
def isoMvS_153:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_153:Lower true dom_153 roots_153 goal_153 5:=lower_iso_b isoMvS_153 (by decide +kernel) lowS_43
def isoMvS_163:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_163:Lower true dom_163 roots_163 goal_163 5:=lower_iso_b isoMvS_163 (by decide +kernel) lowS_43
def isoMvS_166:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_166:Lower true dom_166 roots_166 goal_166 5:=lower_iso_b isoMvS_166 (by decide +kernel) lowS_43
def isoMvS_169:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_169:Lower true dom_169 roots_169 goal_169 5:=lower_iso_b isoMvS_169 (by decide +kernel) lowS_75
def isoMvS_172:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_172:Lower true dom_172 roots_172 goal_172 5:=lower_iso_b isoMvS_172 (by decide +kernel) lowS_43
def isoMvS_177:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_177:Lower true dom_177 roots_177 goal_177 5:=lower_iso_b isoMvS_177 (by decide +kernel) lowS_75
def isoMvS_184:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_184:Lower true dom_184 roots_184 goal_184 4:=lower_iso_b isoMvS_184 (by decide +kernel) lowS_29
def isoMvS_201:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_201:Lower true dom_201 roots_201 goal_201 5:=lower_iso_b isoMvS_201 (by decide +kernel) lowS_43
def isoMvS_202:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_202:Lower true dom_202 roots_202 goal_202 5:=lower_iso_b isoMvS_202 (by decide +kernel) lowS_43
def isoMvS_209:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_209:Lower true dom_209 roots_209 goal_209 5:=lower_iso_b isoMvS_209 (by decide +kernel) lowS_75
def isoMvS_216:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_216:Lower true dom_216 roots_216 goal_216 4:=lower_iso_b isoMvS_216 (by decide +kernel) lowS_29
def isoMvS_225:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_225:Lower true dom_225 roots_225 goal_225 5:=lower_iso_b isoMvS_225 (by decide +kernel) lowS_43
def isoMvS_228:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_228:Lower true dom_228 roots_228 goal_228 5:=lower_iso_b isoMvS_228 (by decide +kernel) lowS_43
def isoMvS_232:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_232:Lower true dom_232 roots_232 goal_232 4:=lower_iso_b isoMvS_232 (by decide +kernel) lowS_29
def isoMvS_240:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_240:Lower true dom_240 roots_240 goal_240 4:=lower_iso_b isoMvS_240 (by decide +kernel) lowS_29
theorem lowS_31:Lower true dom_31 roots_31 goal_31 5:=lower_slice_b [(0xaaaaaaaa,8,9)] (by decide +kernel) lowS_30
theorem lowS_47:Lower true dom_47 roots_47 goal_47 6:=lower_slice_b [(0xcccc0000cccc,8,10)] (by decide +kernel) lowS_45
theorem lowS_59:Lower true dom_59 roots_59 goal_59 6:=lower_slice_b [(0xc0c0c0c0c0c0c0c,8,10)] (by decide +kernel) lowS_57
namespace S_62
def pG:List (Nat×Nat):=[(2,10),(2,18),(4,20),(4,36),(6,14),(6,22),(6,38),(8,10),(8,40),(12,14),(12,28),(12,44),(16,18),(16,20),(24,26),(24,28),(24,56),(32,36),(32,40),(34,38),(34,42),(34,50),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x1ffffff
def xsM:=roots_62.map (·&&&dom_62)
def gM:=goal_62&&&dom_62
def NN:Nat→Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x1a4f618e85
|5,0=>0xaaa4e38f8b0600b
|6,0=>0xaaa4e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5454545454545454aaaaaaaaa0a0a0a111111111111111100002a2a00002a2a5555555500000000aaaa0000aaaa000154015401540154028282828282828284444440044444400
|_,_=>0
def sP:Nat→Nat
|0=>0x43216432164328167432164216543210
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def wAt:=mkWire dB 9 63 0x7fffffffffffffff
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
|5,0=>6
|6,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 5 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_60 4 roots_60 ops++addP pm 1 dom_58 4 roots_58 ops++addP pm 2 dom_54 4 roots_54 ops++addP pm 3 dom_46 4 roots_46 ops++addP pm 4 dom_30 4 roots_30 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_62 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_30 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_60 4 s (0,roots_60.map (·&&&dom_60)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_62 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_60 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_62==dom_62)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_62 gM v ys):RunD true dom_62 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_62 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_62 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_62 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_62 roots_62 goal_62 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_62
theorem lowS_62:Lower true dom_62 roots_62 goal_62 7:=S_62.noCircuit
theorem lowS_79:Lower true dom_79 roots_79 goal_79 6:=lower_slice_b [(0xaaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_78
theorem lowS_87:Lower true dom_87 roots_87 goal_87 6:=lower_slice_b [(0xaa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_86
theorem lowS_91:Lower true dom_91 roots_91 goal_91 6:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_90
namespace S_93
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,65),(4,20),(4,68),(5,13),(5,21),(5,69),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,88),(64,65),(64,68),(64,72),(64,80)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffff
def xsM:=roots_93.map (·&&&dom_93)
def gM:=goal_93&&&dom_93
def NN:Nat→Nat
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|6,0=>0x4011c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x333300000000000033330000cc00cc0000000000cc00cc030303030000000003030303088888888000000008888888b33333330000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x4688
|_=>0
def sO:Nat→Nat→Nat
|6,0=>5
|_,_=>0
def wAt:=mkWire dB 5 94 0x3fffffffffffffffffffffff
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
addP pm 0 dom_92 5 roots_92 ops++addP pm 1 dom_89 5 roots_89 ops++addP pm 2 dom_85 5 roots_85 ops++addP pm 3 dom_77 5 roots_77 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_93 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_77 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_92 5 s (0,roots_92.map (·&&&dom_92)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_93 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_92 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_93==dom_93)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_93 gM v ys):RunD true dom_93 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_93 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s:Nat) (hs:s≤6):∀ i<NN s,bar dom_93 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤6) (h:RunD true dom_93 gM s xsM):False:=by
  have hmin:4≤s:=by have hl:=run_len h;change 5≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_93 roots_93 goal_93 7:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_93
theorem lowS_93:Lower true dom_93 roots_93 goal_93 7:=S_93.noCircuit
theorem lowS_109:Lower true dom_109 roots_109 goal_109 6:=lower_slice_b [(0x3030000030300000303000003030,32,36)] (by decide +kernel) lowS_105
def dzo_83_32:=0xf000f00000000000f000f00000000
def gzo_83_32:=0xf000e00000000000e000a00000000
def gsh_83_32:=0xf000e00000000000e000a
theorem lowS_zo_83_32_82:Lower true dzo_83_32 roots_83 gzo_83_32 5:=lower_iso_b (d1:=dom_83) (r1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (lower_slice_b (T:=gsh_83_32) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) lowS_82)
namespace S_115
def pG:List (Nat×Nat):=[(1,17),(1,33),(1,65),(2,18),(2,66),(3,19),(3,35),(3,67),(16,17),(16,18),(16,80),(32,33),(34,35),(34,50),(34,98),(48,49),(48,50),(48,112),(64,65),(64,66),(64,80),(96,97),(96,98),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffff
def xsM:=roots_115.map (·&&&dom_115)
def gM:=goal_115&&&dom_115
def NN:Nat→Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0x4f55d
|5,0=>0xda97c
|6,0=>0x88c8c
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf000f000f000f000f0000000f0000c000c000c000c000c000c000c000cf000f00000000000f000f00000000f0000000f0000000f0000000f0000a000a000a000a000a000a000a000a30003000300030003000000030000f000f000f000f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x8ea133a84688
|_=>0
def sO:Nat→Nat→Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wAt:=mkWire dB 7 116 0xfffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x61
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
addP pm 0 dom_113 5 roots_113 ops++addP pm 1 dom_99 4 roots_99 ops++addP pm 2 dzo_83_32 5 roots_83 ops++addP pm 3 dom_83 5 roots_83 ops++addP pm 4 dom_82 4 roots_82 ops++addP pm 5 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_115 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_113 5 s (0,roots_113.map (·&&&dom_113)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_115 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_115==dom_115)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_115 gM v ys):RunD true dom_115 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_115 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
def isoMvS_55:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_55:Lower true dom_55 roots_55 goal_55 5:=lower_iso_b isoMvS_55 (by decide +kernel) lowS_31
def isoMvS_61:List (Nat×Nat):=[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_61:Lower true dom_61 roots_61 goal_61 6:=lower_iso_b isoMvS_61 (by decide +kernel) lowS_59
def isoMvS_94:List (Nat×Nat):=[(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_94:Lower true dom_94 roots_94 goal_94 7:=lower_iso_b isoMvS_94 (by decide +kernel) lowS_93
def isoMvS_103:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_103:Lower true dom_103 roots_103 goal_103 5:=lower_iso_b isoMvS_103 (by decide +kernel) lowS_31
def isoMvS_107:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_107:Lower true dom_107 roots_107 goal_107 7:=lower_iso_b isoMvS_107 (by decide +kernel) lowS_93
def isoMvS_110:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_110:Lower true dom_110 roots_110 goal_110 6:=lower_iso_b isoMvS_110 (by decide +kernel) lowS_59
def isoMvS_117:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_117:Lower true dom_117 roots_117 goal_117 6:=lower_iso_b isoMvS_117 (by decide +kernel) lowS_109
def isoMvS_118:List (Nat×Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_118:Lower true dom_118 roots_118 goal_118 7:=lower_iso_b isoMvS_118 (by decide +kernel) lowS_115
def isoMvS_121:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_121:Lower true dom_121 roots_121 goal_121 7:=lower_iso_b isoMvS_121 (by decide +kernel) lowS_93
def isoMvS_122:List (Nat×Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_122:Lower true dom_122 roots_122 goal_122 7:=lower_iso_b isoMvS_122 (by decide +kernel) lowS_115
def isoMvS_124:List (Nat×Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_124:Lower true dom_124 roots_124 goal_124 6:=lower_iso_b isoMvS_124 (by decide +kernel) lowS_59
def isoMvS_143:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_143:Lower true dom_143 roots_143 goal_143 5:=lower_iso_b isoMvS_143 (by decide +kernel) lowS_31
def isoMvS_151:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64)]
theorem lowS_151:Lower true dom_151 roots_151 goal_151 6:=lower_iso_b isoMvS_151 (by decide +kernel) lowS_87
def isoMvS_155:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_155:Lower true dom_155 roots_155 goal_155 6:=lower_iso_b isoMvS_155 (by decide +kernel) lowS_109
def isoMvS_157:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_157:Lower true dom_157 roots_157 goal_157 7:=lower_iso_b isoMvS_157 (by decide +kernel) lowS_115
def isoMvS_167:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_167:Lower true dom_167 roots_167 goal_167 6:=lower_iso_b isoMvS_167 (by decide +kernel) lowS_79
def isoMvS_171:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_171:Lower true dom_171 roots_171 goal_171 6:=lower_iso_b isoMvS_171 (by decide +kernel) lowS_109
def isoMvS_174:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_174:Lower true dom_174 roots_174 goal_174 6:=lower_iso_b isoMvS_174 (by decide +kernel) lowS_59
def isoMvS_179:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_179:Lower true dom_179 roots_179 goal_179 7:=lower_iso_b isoMvS_179 (by decide +kernel) lowS_93
def isoMvS_185:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_185:Lower true dom_185 roots_185 goal_185 7:=lower_iso_b isoMvS_185 (by decide +kernel) lowS_93
def isoMvS_203:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)]
theorem lowS_203:Lower true dom_203 roots_203 goal_203 6:=lower_iso_b isoMvS_203 (by decide +kernel) lowS_109
def isoMvS_205:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_205:Lower true dom_205 roots_205 goal_205 6:=lower_iso_b isoMvS_205 (by decide +kernel) lowS_59
def isoMvS_206:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_206:Lower true dom_206 roots_206 goal_206 6:=lower_iso_b isoMvS_206 (by decide +kernel) lowS_59
def isoMvS_211:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_211:Lower true dom_211 roots_211 goal_211 6:=lower_iso_b isoMvS_211 (by decide +kernel) lowS_91
def isoMvS_214:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_214:Lower true dom_214 roots_214 goal_214 6:=lower_iso_b isoMvS_214 (by decide +kernel) lowS_91
def isoMvS_217:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_217:Lower true dom_217 roots_217 goal_217 7:=lower_iso_b isoMvS_217 (by decide +kernel) lowS_93
def isoMvS_218:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_218:Lower true dom_218 roots_218 goal_218 7:=lower_iso_b isoMvS_218 (by decide +kernel) lowS_93
def isoMvS_227:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]
theorem lowS_227:Lower true dom_227 roots_227 goal_227 6:=lower_iso_b isoMvS_227 (by decide +kernel) lowS_59
def isoMvS_230:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_230:Lower true dom_230 roots_230 goal_230 6:=lower_iso_b isoMvS_230 (by decide +kernel) lowS_59
def isoMvS_233:List (Nat×Nat):=[(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_233:Lower true dom_233 roots_233 goal_233 7:=lower_iso_b isoMvS_233 (by decide +kernel) lowS_93
def isoMvS_234:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_234:Lower true dom_234 roots_234 goal_234 6:=lower_iso_b isoMvS_234 (by decide +kernel) lowS_59
def isoMvS_236:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_236:Lower true dom_236 roots_236 goal_236 6:=lower_iso_b isoMvS_236 (by decide +kernel) lowS_59
def isoMvS_241:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]
theorem lowS_241:Lower true dom_241 roots_241 goal_241 7:=lower_iso_b isoMvS_241 (by decide +kernel) lowS_93
def isoMvS_248:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_248:Lower true dom_248 roots_248 goal_248 7:=lower_iso_b isoMvS_248 (by decide +kernel) lowS_62
namespace S_63
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(2,10),(2,18),(3,11),(3,19),(3,35),(4,20),(4,36),(5,13),(5,21),(5,37),(6,14),(6,22),(6,38),(7,15),(7,23),(7,39),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,18),(16,20),(24,25),(24,26),(24,28),(24,56),(32,33),(32,36),(32,40),(34,35),(34,38),(34,42),(34,50),(48,49),(48,50),(48,52),(48,56)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xfffffffffff
def xsM:=roots_63.map (·&&&dom_63)
def gM:=goal_63&&&dom_63
def NN:Nat→Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xf4716c32efbb27373fbb5be7f
|5,0=>0xca973ca592c802ebffb2b08c8ae63f9be199981895e6384f7c7079e60bbe34cda2a5990cd48086b9
|6,0=>0xf131fe3250dd808d6184cf6b2ce108b40d5a9467a33d79d4fa9c2ed908be8d95f8ad1584f7c81958785bc78555754dd7314b72b0e6ed14692a46324a5a9d257b684d9543a92e39e34362712b4e324193077970481104701028d7
|7,0=>0xdd808ba6a9b12a65f7114017b2a68d29ed4297201fb9e
|8,0=>0xc6758
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0fff0fff0fff0f0f0f0f0ffffffff00000000ff00ff00ff00ff00555555555555550000ff00ffffffff000000ffff0000ff00ffffffffffffff00ffff0000ffff0000ffccffccccccccccaaaaaaaaaaaaaaaaffffffffffff0000ffffff00ffffff00ffaaffaaaaaaaaaaf0f0f0f0f0f0f0f0cccccccccccccccc
|0,1=>0x3333333300000000cc00cc00ff00ff0000000000ffccffcc0000000033003300ff000000ff00ff00ffffffffccccccccf0fff0fff0f0f0f03333000033333300ffffff0000000000ffffffffff00ff0000ff00ffff00ff0000ff00ff0000000000000000ffffff00ffffff00ffff0000ff00ff00000000000f0f0f0f0f0f0f00
|0,2=>0xfffffffffff0fff0333333003333330000cc00cccccccccc00000000ff00ff00000000ff000000000f0f0f0f0f0f0000ffffffff330033000000ff000000ff0000ff00ff00ff0000ffccffccffccffccff33ff33ff00ff000000ffff00000000ccccffffccccccccffff0000ffffff00ffff3333ffff00000f0f0f0f0f000f00
|0,3=>0xf000f000f000f003300330033003300fff0fff0fff0fff0ff00ff00ff00000000ff0000ffff0000ff00ffffff00ff00
|_,_=>0
def sP:Nat→Nat
|0=>0x53473190401561c20403431c60451d10401492074410055870401553473011581173010051c10055470401544cd48c0401441c23010040d104014d1cc00540d1cc3c014d0c738014d1cc0402c704014a1c20402481c20401031811440c2040
|1=>0x529347301005347040154a041cc4410053473010059cd1c630114434330100568d1e630114d1e530100534708c0403473018c55873010057cd88730100536130100534730100580d1cc04078534730100574d1cc04015c34731b040156687301
|2=>0x17534730100550d1cc040174347ccc04014d4873010053473320401563473010053473010052561d104014834730100534c040171347c0c04016f3473010053431cc045b8d1cc045b47040154b0d1cc04016b34730016a3523010053431c1005
|3=>0x34730100558d1cc04014d0c7301005347301005a0d1cc44100534798c04014d1cc040
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18ccc6062d315189cc49521b0f586ec31615b09583ec196
|6,0=>0xb13d6dea8f4d7a3b501e74d337963c95e3ed196893c31a0ccff77c3bc5dd4ee376eb359d9eec876132f196aeae7543285d34e937463a15cfce777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wAt:=mkWire dB 54 64 0xffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x34c47311cc8d303004c0730d8c033014d3034c561d34c474734c0c910c0c7314408d3034c8c36343c4071cd474534c0d3330d0c124404d30024473634c877d340cc7f34c564734c0d31
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x300000000000000000000
|6,0=>0x7c9d26c9a100182589424c5123c8e100000344c1288000000000082000711480010400000000c400
|7,0=>0x291a0671986519063188611
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 10
def pmP:Nat→Nat
|0=>0xed5b9d6d56bd67539d3952f518218111010408108006106002001401101000c008002001000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x10000000010000000000
|6,0=>0x160628ce01c2f40425000a57a46080408081a000080
|7,0=>0x128c6f5b4eb8
|8,0=>0x14
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 5 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_62 7 roots_62 ops++addP pm 1 dom_54 4 roots_54 ops++addP pm 2 dom_61 6 roots_61 ops++addP pm 3 dom_29 4 roots_29 ops++addP pm 4 dom_47 6 roots_47 ops++addP pm 5 dom_45 5 roots_45 ops++addP pm 6 dom_43 5 roots_43 ops++addP pm 7 dom_55 5 roots_55 ops++addP pm 8 dom_31 5 roots_31 ops++addP pm 9 dom_59 6 roots_59 ops++addP pm 10 dom_57 5 roots_57 ops++addP pm 11 dom_51 4 roots_51 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_63 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_51 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_62 7 s (0,roots_62.map (·&&&dom_62)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_63 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_63==dom_63)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_63 gM v ys):RunD true dom_63 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_63 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_63 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_63 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_63 roots_63 goal_63 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_63
theorem lowS_63:Lower true dom_63 roots_63 goal_63 9:=S_63.noCircuit
theorem lowS_95:Lower true dom_95 roots_95 goal_95 8:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_94
theorem lowS_111:Lower true dom_111 roots_111 goal_111 8:=lower_slice_b [(0xf0f00000f0f00000f0f00000f0f0,32,36)] (by decide +kernel) lowS_107
theorem lowS_119:Lower true dom_119 roots_119 goal_119 8:=lower_slice_b [(0xaa00aa00aa00aa00aa00aa00aa00aa,16,17)] (by decide +kernel) lowS_118
def dzo_91_32:=0xf0f0f0f000000000f0f0f0f00000000
def gzo_91_32:=0xf0f0f0e000000000f0e0f0a00000000
def gsh_91_32:=0xf0f0f0e000000000f0e0f0a
theorem lowS_zo_91_32_82:Lower true dzo_91_32 roots_91 gzo_91_32 6:=lower_iso_b (d1:=dom_91) (r1:=roots_91) (T1:=gsh_91_32) [(dom_91,32)] (by decide +kernel) (lower_slice_b (T:=gsh_91_32) [(0xa0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00,0,8)] (by decide +kernel) lowS_82)
namespace S_123
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(2,10),(2,18),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(16,18),(16,80),(24,25),(24,26),(24,56),(24,88),(32,33),(32,40),(34,35),(34,42),(34,50),(34,98),(48,49),(48,50),(48,56),(48,112),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_123.map (·&&&dom_123)
def gM:=goal_123&&&dom_123
def NN:Nat→Nat
|7=>2
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x4f9492881b
|8,0=>0x62b5b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f000000000f0f0f0f000000000000000000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x34688f1a22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0xcc06
|8,0=>0xc6
|_,_=>0
def wAt:=mkWire dB 8 124 0xfffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xc1c3
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x441
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfefcf80
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>6
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 2 (j%128);fld (pmP (k/32)) 7 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_121 7 roots_121 ops++addP pm 2 dom_115 7 roots_115 ops++addP pm 3 dom_107 7 roots_107 ops++addP pm 4 dom_91 6 roots_91 ops++addP pm 5 dom_59 6 roots_59 ops++addP pm 6 dzo_91_32 6 roots_91 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_123 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_123 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_123==dom_123)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_123 gM v ys):RunD true dom_123 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_123 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
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
namespace S_125
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(4,20),(4,36),(4,68),(5,13),(5,21),(5,37),(5,69),(8,9),(8,40),(8,72),(12,13),(12,28),(12,44),(12,76),(16,17),(16,20),(16,80),(24,25),(24,28),(24,56),(24,88),(32,33),(32,36),(32,40),(48,49),(48,52),(48,56),(48,112),(64,65),(64,68),(64,72),(64,80),(96,97),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_125.map (·&&&dom_125)
def gM:=goal_125&&&dom_125
def NN:Nat→Nat
|5=>3
|6=>5
|7=>4
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0xcd8f4ace6f76423
|6,0=>0x393fc37917204bc0406700ecb
|7,0=>0xb324d8e2268d60a53413
|8,0=>0x7f2e4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x33333300333333003333330033333300cccc8888cccc8888cccc8888cccc888b3333333333333333300330033003300cccccccccccccccccccccccccc00cc030303030303030303030303030303030888888888888888888888888888888880003333000033330000323200003232cccccccc00000000cccccccc000000033333333333333333333333322222222cccccccccccccccc00000000000000033333333333333333333333300000000cccc0000cccc0000cccc0000cccc00033003300330033003300330033003300c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8cb3333333333333332222222222222222
|_,_=>0
def sP:Nat→Nat
|0=>0x732a95732195732a0957e32a957d32a9543c2a96432a95432195b432a95432a0972198564321543210
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x2d82b005
|6,0=>0x2b648e798bb916
|7,0=>0x8ccfddc3b17
|8,0=>0x4c6
|_,_=>0
def wAt:=mkWire dB 15 126 0x3fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 11
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x2a5954c9395d5255d5756a5755d5955d5
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x100
|6,0=>0x7261423112
|7,0=>0xc1b1a191
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x9fd5ed57d2801fd016006000
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>8
|6,0=>0x64e5
|7,0=>0xedb
|8,0=>3
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_121 7 roots_121 ops++addP pm 1 dom_92 5 roots_92 ops++addP pm 2 dom_116 5 roots_116 ops++addP pm 3 dom_61 6 roots_61 ops++addP pm 4 dom_124 6 roots_124 ops++addP pm 5 dom_109 6 roots_109 ops++addP pm 6 dom_93 7 roots_93 ops++addP pm 7 dom_117 6 roots_117 ops++addP pm 8 dom_45 5 roots_45 ops++addP pm 9 dom_85 5 roots_85 ops++addP pm 10 dom_29 4 roots_29 ops++addP pm 11 dom_120 4 roots_120 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_125 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_93 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_85 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_120 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_121 7 s (0,roots_121.map (·&&&dom_121)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_125 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_121 h
def symsG:List (List (Nat×Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_125==dom_125)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_125 gM v ys):RunD true dom_125 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_125 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_125 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def dzo_82_32:=0x50005000000000005000500000000
def gzo_82_32:=0x50004000000000004000000000000
def gsh_82_32:=0x500040000000000040000
theorem lowS_zo_82_32_82:Lower true dzo_82_32 roots_82 gzo_82_32 4:=lower_iso_b (d1:=dom_82) (r1:=roots_82) (T1:=gsh_82_32) [(dom_82,32)] (by decide +kernel) (lower_slice_b (T:=gsh_82_32) [] (by decide +kernel) lowS_82)
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054005000000000
def gsh_86_32:=0x5500540000000000540050
theorem lowS_zo_86_32_82:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso_b (d1:=dom_86) (r1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (lower_slice_b (T:=gsh_86_32) [(0x5000500000000000500050,0,4)] (by decide +kernel) lowS_82)
def dzo_94_32:=0x55555555000000005555555500000000
def gzo_94_32:=0x55555554000000005554555000000000
def gsh_94_32:=0x555555540000000055545550
theorem lowS_zo_94_32_82:Lower true dzo_94_32 roots_94 gzo_94_32 6:=lower_iso_b (d1:=dom_94) (r1:=roots_94) (T1:=gsh_94_32) [(dom_94,32)] (by decide +kernel) (lower_slice_b (T:=gsh_94_32) [(0x505050500000000050505050,0,4),(0x550055000000000055005500,0,8)] (by decide +kernel) lowS_82)
def dzo_90_32:=0x5050505000000000505050500000000
def gzo_90_32:=0x5050504000000000504050000000000
def gsh_90_32:=0x50505040000000005040500
theorem lowS_zo_90_32_82:Lower true dzo_90_32 roots_90 gzo_90_32 5:=lower_iso_b (d1:=dom_90) (r1:=roots_90) (T1:=gsh_90_32) [(dom_90,32)] (by decide +kernel) (lower_slice_b (T:=gsh_90_32) [(0x50005000000000005000500,0,8)] (by decide +kernel) lowS_82)
namespace S_126
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(4,20),(4,36),(4,68),(6,14),(6,22),(6,38),(6,70),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(16,18),(16,20),(16,80),(24,26),(24,28),(24,56),(24,88),(32,36),(32,40),(34,38),(34,42),(34,50),(34,98),(48,50),(48,52),(48,56),(48,112),(64,66),(64,68),(64,72),(64,80),(96,98),(96,100),(96,104),(96,112)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_126.map (·&&&dom_126)
def gM:=goal_126&&&dom_126
def NN:Nat→Nat
|4=>11
|5=>96
|6=>286
|7=>130
|8=>18
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|4,0=>0xeb6acc839e92b377bc5b69d4a5d88e5bfcb57e7a38c7c37ba50b8e2
|5,0=>0xfbe14fba4df941ef875dedbbded458e9c15e9779e4f38d45c7d034dcda63cd7c8b90a4b69f0af58fadc83ab0e7a9d94a538da0deb9f3d99e8ba96a239459e929fa9103e8f6e489e0e85f6684f13820cf803b87dd2e7ab5d73eb273c8e736ee6eb2969b726159c610b66022c600d75f36e5cda95b1bd5a1b559375577b7570ae5435052c9651f98510754aa36494e04677e4455942dfd41bbf3de873dccf3dbd53d4ec3b6fb3a2613960536c9435c72337fd3361831a173194e2bd822a8ce2a2a9284f3209671efa31c386199371914314fce12fce1109c0c0eb0b5f30a0900902b08208073c905d2c044160263600c46
|6,0=>0x43fd843f494390241bcc4193f414bb40bf93fef23f8a33e91d3e8e43d04c3caf43bb4c3bb0b3ba453b6b83b6533b5cf3b5b939bd4398b1396bc3859138567380f137ce037c92378cc375243543e34bc834a9f3432c33de433a793361833131327953236f322ae31b9e318fa318ca316e52fd372f5ea2e8362e2262e0e92de512ddc42d6882d65b2cbe02c6122bb9a2b3492af072a6e32a67f2955428cbb28158280b027b9826de5267af26003245742427423a5e225fb224a5219be2138420375202271ea341e70e1bab21b7791b11619c1518c0818bfa18ae9180b6173e216de216d6816c981684b160901515f1511514fce14f8b131f910f0110e85101940e6f20dccf0ce150c49d0c0600bbd60b4aa0b4730a4740a09008989082b10799107465070f805d8a04c8303b1c033750330202dbd0272301e030174f0155c003d2
|6,1=>0xc8ef7c8bd5c8a39c89e1c7e63c6f8dc4a33c4619c4493c0c50bfe26bfaa3bc43fbb769b8ab8b89d5b84c8b66d6b0777af95daf809af58fad998ac3a8abae8aabdca9887a91b4a89f8a6bcea59f6a38afa2725a1e609ec0a9ea969c2ee9a3a698571964df9600b95f4791a0f915f2909438f8dd8eba98e0ba8b775874998486f840337fbad7f5c27f2427d9257d2707c9fa7beb57aa057a9247a0dd79c6678d9c76df27664475a0a7590c756807549374417743127406771619708dc70516701977010e6ea536d3796ae9d68fbe689db67d6f6671f65ac56595e655f1643ef639e06398062ead61f126158260e495f3035ba965b8415acce5a8005a0a759d6959362576e4573f35717256b735589254a4454a0f5296b5241d51b985136b50d6e502274ef2e4ef254e9be4cb5c4c9554acc9489d747e32455b5453f64476d44559
|6,2=>0xfba4df94a8effaaeef64ee730eb525e5da1e53b0e4805e3ec4e1480e1013e06a4df94edf243dd430dd307da434d9c6fd8f20d5245d407ad23ead0a12cf90acf75dcf722cb895cb80dca943
|7,0=>0xf7733f7575f6923e6156e4a5edf94ed9d5ed7bcfd5137d4a31c8c63c77c8c63cac2b00c2560bd264b4514b1900a38afa09c0a05f99e8f79c7a59b6c69b5f09ac049a21c9109e8bf738ba978b2418a198865ca8340382783818788148c7f9407b5fe7afd57707c75c45757aa7284a71290711677083f6d54269d30697b266e7765be462ffd5f20d5e4d45d6645b5f65a85e57bf45757d570c153b905374b52da051bab4fe594f7be4f6804d67f4ca5d4730246e92469b745476436423d9333c9b43600c359f6341e53264931b0e318fa316e53047e2fc6b2d9892d0ce2cc912bf1e28cb3288932867f25f6925b0e24c082427423b97239902324c21aea219892041f1fa121ea6c1e9051adc21a6b218c0818119174cc166b9139e412ebf100140f79e0f1160dc370c9350abf30943606b3c05c63048a3030b9024ec00a19007f0
|7,1=>0xf9b1af8222
|8,0=>0xe9649e6db0c8943c11f3524f44f5f649279464f44457d43c3238cc63188f25b0e1ff1e1b6ef08cc00093500334
|9,0=>0x464f4
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaaaaaaaaaaaaaaaaaa0000aaaa000155555541555555415151514151515142222222222222222222222222222222255555050555550505555505055555050a8a8a8a8a8a8a8a8a8a80000a8a8000155555555555555551111111111111112aaaaaaa800000002aaaaaaa8000000055554444555544445555444455554444aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa151515001515150015151500151515002aaaaaaaaaaaaaaa800000000000000055555555555555555555555500000000aaaa0000aaaa0000aaaa0000aaaa000154015401540154015401540154015402a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a55554444555544445050404050504040
|0,1=>0xaaaa0000aaaa0000aa880000aa88000111111111111111111111100111111000282828282828282820202020202020255005500550055005555554455555544aaaaaaaaaaaaaaaaaaaa8888aaaa888955555555555555551110000111100002aaaaaaaaaaaaaaaa22200002aaa800001000100010001000100550001005500a8a8a0a0a8a8a0a0a8a8a0a0a8a8a8a9555555555555555541414141414141400000000000000002aaaa2222aaaa22211114444111144441111444411114444a8a8a8a8a8a8a8a8a800a800a800a80155555555555555555555555511100002828282828282828282828282828282800000000000000001111444411114444
|0,2=>0xaaaaaaaaaaaaaaaaaa00aa00aa00aa0000000000000000015555515155555152aaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a555555005555550050505000505050002222222222222222220222002202220155555555111000015555555511101012aaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a00000000000000000505040405050404aaaaaaaaaaaaaaaa000022220000000155555554000014155555555400001012222000022220000222200002222000055555500555555005544550055445500aaaa8888aaaa8888aa008800aa00880155544445555444455554440155544400888800008888000088880000888800055555500555555005555550055555500
|0,3=>0xaaaaaaaa00000000aaaaaaaa002200015555555555555401555555551111100002a802a8000002a802a802a80000022005500440055004400550044005500440000aaaa0000aaaa0000a8a80000a8a8000155540001555400014140000141400002222000022220000222200002222111111001111110011111100111111002222222222222222222222202222222155551111555511115555010155550102aaaaa802aaaaa80222222002222220011110000111100001111444411114444aaaaaaaaaaaaaaaaaaaaaa00aaaaaa0155115511551155115511551155115512aaa80002aaa80002a2a00002a2a000050505454505054545050545450505454
|0,4=>0xaaaa0000aaaa0000a0a80000a0a800000001555400015554000154000001540002a8000002a8000002a8000002a8000110111011101110111011100110111008888888888888888888888808888888044444444444444444444440044444402aaaaaaaaaaaaaaaaa802aaa8000000055555544555555445555554455555544aaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa800000000000000015554011155540112aaaa8282aaaa8282a2a28282a2a28285555555455555554000000000000000000880088008800880088008800880089555401115554011155540111555401100000000000000002aaa82022aaa820255555555555555550055000000550000
|0,5=>0x88088808880888088808880088088800000000000000000155555551555555528282828282828282a2a2a2a2a2a2a2a5555555555555555111144441111444488aa888888aa888888aa888888aa888954455445544554454041404140414042aaaaaaaaaaaaaaaaaaaaaaa8008800005450044054500440545004405450044aa22aa00aa22aa00aa22aa00aa22aa004444444444444444440044004400440002a802a802a802a802a802a802a8022000054540000545400005454000054542222aaaa2222aaaa222288882222888955554545555545455555454400000002aaa2aaa2aaa2aaa2aaa2a802aaa2a8055555555555555555555555500550000
|0,6=>0x22222222222222222220222022202221555400015554000111100001111000000002a8000002a8008802a8008802a8055505550000000005550555000000000aaaaaaaaaaaaaaaaaaa0aaa00000000154155415541554155415540154155400282800002828000028280000282800045454444454544444545444445454444aa00aaaaaa00aaaaaa00aa88aa00aa8800000000000000015554000155540002aaaaaaaaaaaaaaa888888800888888055555555555555555555505055555050aa00aa00aa00aa00aaaaaa00aaaaaa0155555554444444455555555444440002aaa802aaaaa802aaaaa80222aaa802244445555444455554444555500000000
|0,7=>0xaa88aa88aa88aa88aa88aa00aa88aa0044444444444444444040404040404042aaaaaaaaaaa80002aaaaaaaa222000055555555005500005555555500550000aaaa0000aaaa0000aaaa00000000000155551111555511115555111111111112aaaaaaaaaaaaaaa802200220022002204040404040404040404040404040404aaaa0a0aaaaa0a0aaaaa0808aaaa080955555554000155551111111000011110282828282828282828280000282800000110000001100000011000000110000aaaaaaaaaaaaaaaaaa88aa88aa88aa880000000000000000004400000044000002a002a002a002a002a002a002a002a00000054000000540000005400000054
|0,8=>0xaaaaaaaaaaaaaaaaaaaaaaaa080808094141414141414141555555415555554002a802a802a802a802a8022002a802200000055000000550000005000000050aa00aaaaaa00aaaaaa00aaaa00000000000000000000000044444400444444008888888888888888888800008888000000000004444444400000000444444448888888888888888aaaa8888aaaa888954440001544400015444000154440002aaaaaa82aaaaaa82aaaaaa82aaaaaa855555555555555550505050005050500aaaaa0a0aaaaa0a0aaaaa8a8aaaaa8a80001555400015554000155100001551000000002aa82aa8000000002aa82aa844444444444444444444000044440000
|0,9=>0xaaaaaaaaaaaaaaaaaaaa0808aaaa080911551155115511551151115111511150282820202828202028282020282820255055504550555045505550455055504aaaa0808aaaa0808aaaa0808aaaa0809111155551111555511115151111151528282aaaa8282aaaa8282aa828282aa8050505050505050505000500050005008a8a8a8a8a8a8a8a8a888a888a888a8955555555555555540000101000001012aa22a802aa22a802aa22a802aa22a80550000005500000055110000551100008888aaaa8888aaaa8888aa888888aa8911100001111000011154000111540002aaaaaaaaaaaaaaa800000002222222255555555555555550404040404040404
|0,10=>0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa954155401541554015415540154155402aaaaaaaaaaaaaaaaa82aa802a82aa80005500550055005500500050005000500000aaaa0000aaaa0000aaaa0000000111100001111000011110000111111110888888888888888888888888888800000000000000000000055000000550000aaaaaaaa00000000aaaaaaaa00aa000000140014001400140014000000140002aaaaaaaaaaaaaaa828282020282820255555555555555550000444400004444aaaaaaaaaaaaaaaaaaaaaaaaaaaa888844444444000000004445555400000000000088880000888800008800000088055555054555550545555505455555054
|0,11=>0xaaaaaaaaaaaaaaaaa0a0a8a8a0a0a8a9414155554141555501011111010111108082828080828280808282808082828505450545054505450545054505450540000000000000000aa220000aa22000141414140000000014545454400000000000000000000000002a8022002a80220505050005050500050505000505050000aa00aa00aa00aa00aa00a000aa00a15555555400000001540155540000000282828282828282828282a2a28282a2a55115511551155115511550055115500aaaa2222aaaa2222aaaa2222aaaa000145454545454545454544000145440000888aaaa8888aaaa8888aaaa8000000000000000000000005555000055554444
|0,12=>0xaaaaaaaaaaaaaaaaaaa8aaa8aaa8aaa955555555111111115555555511111110000088880000888800008888000000000000000555500000000000055550000aaaaaaaaaaaaaaaa88888888aaaa8888440044004400440044015400440154000000000000000002aaaaa802aaaaa8011110000111100001111000055550000a2a2a2a200000000a2a2a2a20000000155555555555555554545454400000002a802aaa2a802aaa2a802aaa2a802aaa5555000055554444555500005555444400000000aaaaaaaa00000000aaaa888800000000000000015551555155515552aaaaaaaaaaaaaaaaaa82aa82aa82aa844444444444444444040404040404040
|0,13=>0xaaaaaaaaaaaaaaaa00000000aaa0aaa155555554141414155555555410101010000000000000000088880000888800005050004050500040505000405050004aaaaaaaaaaaaaaaaaaaaa8a8aaaaa8a955540001555400015555515155555150000000000000000028282800282828000050004000500040005000400050004aaaa8888aaaa8888aaaa88880000000000000000000000001010101010101012aaaaaaa8000000028a8a8a8800000005555000055550000555504045555040488888888aaaaaaaa88888888aaaa888945454545454545454541454145414540022002200220022002a8022002a802255550054555500545555005455550054
|0,14=>0x88008800880088aaaa0088aaaa00881414141014141410141414101414141002a802a802a802a802a8000002a80005055505550555055505550505055505000000000aaaa888800000000aaaa8889555555555555555400000001555511102828282828282828282828002828280000000550000005500000044000000440000000000000000888888888888888941414141515151514141414151515150000028280000282800002800000028000000000000000000000444400004444aaaaaaaaaaaaaaaaaaaa0088aaaa00895555555555555555555555551111111002a802a802a802a802a802a8022002200000000000000000000000055554444
|0,15=>0xaaaaaaaa00000001555400015554000044440000444400020202222202022222020222220202222444444444444444444444444000000000000aaaa0000aaaa0000888800008889414141404040404141414140404040400088008800880088008800000088000555555550000000055555555555544442222aaaa000000002222aaaa0000000155555555555555544445555400000002aaaaaaa800880002aaaaaaa8008800055551111555511115050101050501010aaaaaaaaaaaa8888aaaaaaaaaaaa888800000000000000015555555555551112aaaaaaaaaaaaaaaa02022222020222200005554000055540000555400005554
|1,0=>0x444555544445555400000000000000000000000000000002a2a2a2a2a2a2a2a55555555555555550000000055550000aa00aa00aaaaaa00aa00aa00aaaaaa0155555555111000015555555511100002aaaaaaaa82828282aaaaaaaa828282855005555000000005500555500000000aaaaaaaa08080808aaaaaaaa080808095555555555555554444400004444000000000002aaaaaaa800000002aaa800011111111111111111111111100000000
|_,_=>0
def sP:Nat→Nat
|0=>0x282406020584414091008c220d028244402088840a091007c220d028240602088780a090403c04110e8103803010441a0401808220006824360801044340401808220d0c8240611068600a04018082e0d02824100205858081501044280401044281002020041108024060709828120f0100400120400822100483c040e068241802058281208038180a04018080200
|1=>0x18082237028246c03010040a09040082235028241002088d00a091980c6411050240e02188340a04018086016068240607030340a09100205e1105024100208868121b010442805020b8060208834082d018082c0d0483c04111603412030104456051500c04110681412080780852110200c0411068a00803010441a271300c0411068140802088500a0901890220d
|2=>0x6814080317808224a019245e0208834124807808220a0480c8e2f08828084601808220d0483c044506824060208834880907808220006824840f0104414042080c0411068241002088288009040082210028fc0602088340a040400c04010b0f80602088340a09018441a3d028241e02088287809010441a3b0282404011d0e40a04018bc220d1c0241002088682009
|3=>0x1044a6052900c04110681412150104428050480ca211068141220078c8220a2800c5e02088341202278441a050480c6411051380815010441a4d0200862160883412080101822050480c041126014120301044960502054060200844122d078082c0d0200c04010b0e412200781c2c0d020202a020889412080a808221a04830040b0681412020885020050480c0e2c
|4=>0x49840602088340a04018082260068141202089702805048201e0208828120301044be050202004110a014125e01808220d0202004110d01006022e8581a09018081616068241002089700a0907808225b0502406072d0340a5901808220d02848100208868120303834b0050480cae112b014081501808220d0480c220d2a81412200401c02050480822382a0141208
|5=>0x1808220d37814120308834da05019ac0411068241e020896c1a050480c04110f014122e01808220d02824066a010441a050483c0411340340a0901808220d2c014120f01808220d0e8240667010441a0504920cc02088340a0901808220d32814126401808020d02824c603190441a05048b406020b0340a090403c040108814c40901808220d028242a0f01808220d
|6=>0x68e80a7d01808220d029f00602088281a05021e80602088340a090780c0411069e4120f01808221e02824360301044f005049dc0602088340a0901890220d02824060208834ec050480c0e02069d40a0401808220d3a0141203010441a7202824060208828e2050480c0411069c00a0901808601606814122001808221e02824060717834d2050480c0e2f008340a09
|7=>0x4380c041106814080343008220d028241e02088281a2104a141e02088340a0901808220d420141233010441a21028250603010441a050480c041106a080a090780c042908834120301044b40d028244003190441405048803602088340a0f01808220d408141203038441a79028243603010441a050480c5e11068e00a09019fc220d02824180301034fc050480c0401
|8=>0x68f00a090187c041106814120301045240d028241e03010441a91048b40602088280a0410008220d108151e03010441a0504a380602088340a0901808220d468140803010441a3c0282406020883518050480c0e0d3490c0a0345808220d028241003010042c050480c041106a280a091021c04110681412030104512880282406070100414050480c5e02008441409
|9=>0x88340a0901808229a06814124601808220d0282406024c8441a050482004110d0240602118441a050480c04114b8340a091000c8e11068141203010441a96028241002089b80a090403c0411068141220018bc220a0682406020883434090405406020882808034a8441a050480d2802088340a0901808229306814124101808220d02824100f01044f005048801011
|10=>0x1808220d5281412030100422a4028108403010441a05518240602088340a09101986411068141203010441a35028240624010441a0501808220d51014123601808220d028240602088354205048800411068e80a09018bc04112501412a001808220d028253e03010441a050480c04114f0340a090180860110501408032b808220d02824069c010441a0504a6c1e02
|11=>0x18082c0d028116603010441a050480c04b2088340a0901808220d1d8141202088347605021200602088340a03010441ab1028256003010441a0504abc0602088340a0907ab8041106814120356808220d0282406020083558050480c0411052740a0401808220d55014120801044280504808220d1d0e40a0901808220d548154e03010441a050480c041106a980a09
|12=>0x8440a0901808220d5c814120301044d00a02824100317808220a0200822211c8141203178441ab8028240602088356e050480c04110503480090180802161c81406b617808220d02824060208828a8050480c04b5088340a040180802160682406b4010441a05048800611068f00a040400c0416088340803190bc220d048202a02088940a043200c0416088341285
|13=>0x883590050480c04bc0b0340a0301318220d0282406c5010441a0504b101e02088340a0901808220d61814120f010441a740282406c2010441a050488006c1088340a09010c42c11068141202088500a090180802c00282406025f8441a050480c041106af80a04018081abd028241803012f01a050480d7602088340a03012e8220d028250a03178441a05048540602
|14=>0x4b500602088340a090600c040105014120301045a60d028240602690441a050480c041106b440a096800c041106814120367808220d02b3812030104512050200c041106b340a090180822cb068141233018c8220d028259203038441a050483c060208834fc0931820041106814120801808229002824061106b280a096480c6411068141215010441a4d028100602
|15=>0x10441a05020cc062f010441a091980c041125014120301018220d02824062f010441a406f00c041106814128701808220a02824060208835b80504b6c0602088340a0901044140d1d81412da01808220d02824060208835b205020800632088340a0901808220d6c01408d701808220d0280c04d5088340a091980c0e1106814080301058220d1c8241e86010441a05
|16=>0x68141208018085211028240602148441a055380c5e02088340a090181c220a21814080317808220d540241e03010441443019ac04110681412e301808220d02824061106b840a0910008220d4481408090a80c0411068241e03038082c0d0200c0411068e00a0901808220d70014060208835be05049200611068f00a0404054060208834120801808221d028256603
|17=>0x4008220d26814123301808221e028240607010353a050483c063201044140901808220d74814080301044b60d028240602088359a05020200602008440a0901808222c068141203010441ae8028102a03010441a090180822e74e814120f01809cc0d02824060208835ca050483c0411069b812030100422e4028244003038041a050480c0401088e00a09100200e11
|18=>0x11a01a050480c220a06b840a09648200411068141203010441af002825de03010441a050900c041106868120301044143c028241e0301004220a04820060208b580a0901808220d770141203038081a7e028240602760441a050486c2a03010441a0901808220d750140808010444a050480c04113439c0a0904008221a0282406022e8581a0504b5c0602088340a04
|19=>0x10441a050400c041106a040a0401808220d0d0241e03010441aa4048301e020b0340803010441ab10280c041106bd80af501808220d02824060208bd01a050900c041106814080801808220d028243803010441a05048b41e02088340a090d820041112815e40901808220d028241e02088281a4d048201e02088281a091000c0411250141203010441af1028240607
|20=>0x480c041106bec0a0901808220d540141203013e81a0501808220d40814066c010441a05670241e03010441a05048200411128140803010441a3902824060208835d605048200411069340a091983c0602088340a041000c041106814120323808021106814120f010441a69028241e0301004220d02824100f010441409100200401088141203010441af902be01203
|21=>0x780c041106814128701808220d02824100301058220d028240632178441a057f8200602088340a090181c0411050340a093200c041106814120301004223902824c80301058220d02824060208835fc050480c041106bf40a090181c041606814120c01808020d028243603010441a05798240602088340a0401808220d7e014128501808220d028240602088357005
|22=>0x808141203010441a3a0282406025e0441a050483c0411069340a090403c0602088340a090403c0411068141203010441a1a0480c041106c000a0901808220d3701412640780c041106814120301044140d34814120301004220a06814120f01808220d3c014129b01808220d02824400801808220d028244008010441a050480c04010b0340a090400c041106814121b
|23=>0x1808220d3a014120301044140d66014120317808220a06b881203010441a050480c0429008441a050482006020883478050480c0401088280a0901808220d27014120301058220d1c8160603010441a050488006020b0441a050480c0e110690c0aff1000c0411068141203010441b02028240666010441a430282406320104414050480c0411069d40a0901808220d
|24=>0x88340a0401808220d558160c03010441a05048300602088281a050480c0411068f00a04018082c1106c14120301044140d02824900801808220d028240602088352005048202a03010441a0501c100411068141203010441aac02824660317808220d02824066619008220d028241e03010441a3902824062f010441a69028258803010441a050480c041106b000a09
|25=>0x6814120208884720501808220d7b814120319008220d348141203010441a1d02824c603010441a05710240602088281a05049200602088340a090a80c041106814120360808220d028100602088348605049080602088340a0901b040416088340a091680c0401088340a090195c041106814120f010441a2102824060208834d24302824062f010441aa8028240695
|26=>0x3c0141203010441a3802824180319008220d028240602848441a05048200607010441a05048800607088340a04048200602088340a0401808220d128141203010441a1a02824060200845ce050480c041106b740a0901808220d840141203010a4220d02824060206af40a0904198041106814120c018bc041106814080319008220d02824060208834f2050480e0e11
|27=>0x6815fe03010441a05048300602088340b050480c041106814120801808220d02824060208834f0050480c041106b300a0901808220d128159c0901808220d028100602088340a090780c041105034121b0400c041106815e6090400c0411068141220018080211068141203010441b0a04820060208835d6050483c060208835c805020200602088340a0401808220d
|28=>0x1203010441a050480c0e02088340a040480c0411068141203010441a43028240666010441a050483c0602088340a0901808220d1c814122001808220d028240602088340a09018082c11
|_=>0
def sO:Nat→Nat→Nat
|4,0=>0x32502d50285023501e50195014500f500a500550005
|5,0=>0x1ae61a861a2619c61966190618a6184617e61786172616c61666160615b5155614f61496143613d61376131612b6125611f61196113610d6107610160fb60f560ef60e960e360dd60d760d160cb60c650c060ba60b460ae60a860a2609c60966090608a6085507f60796073606d60676061605b6055604f60496043603d60376
|5,1=>0x26c62666260625a6254624f52496243623d62376231622b62265220621a6214620e6208620261fc61f661f061ea61e461de61d861d261cc61c661c061ba61b46
|6,0=>0x424741d7416740f7408740173fa73f373ec73e573de73d773d073c973c273bb73b473ad73a6739f73987391738b6384737d7377637073697362735b7354734d7347634073397332732b7324731d7316730f7308730172fa72f462ef52e872e262db72d472cd72c672bf72b872b172aa72a3729c7295728e72877280727972727
|6,1=>0x5d975d365cc75c575be75b775b075a975a2759c6595758e75886581757a7573756c7565755e75577550754a6543753c7535752e7527752075197512750b750474fd74f674ef74e874e354dc74d574ce74c774c164ba74b374ad64a674a064997492748b7484747d7476746f74687461745a7454644d7446743f74387431742b6
|6,2=>0x78e7787778077797772776b7764775d7756774f77487741773a7733772c7725771e77177711670a770376fc76f576ef66e876e176da76d376cc76c576be76b956b366ac76a5769f66987691768b6684767d7676766f76687662665b7654764d7646763f76387631762b6624761d761676106609760275fb75f475ed75e675e06
|6,3=>0x945793e7937793079297922791c6915790f6908790178fa78f378ec78e578de78d778d078c978c278bb78b568ae78a778a0789a6893788c7885787e7877787078697862785b7854784e68477841683a7833782c7825781e78186811780a780377fc77f577ee77e777e077da67d377cc77c577be77b777b077a977a2779b77956
|6,4=>0xa116a0a7a0379fc79f579ef69e879e269db79d569cf69c879c269bb79b479ad79a6799f79987991798a7983797c7975796e79677960795a6953794c7
|7,0=>0xbdc8bd48bcd7bc67bbe8bb86bb08ba97ba27b9b7b938b8c7b857b7e7b777b707b697b618b5a7b546b4d7b467b3e8b368b2e8b268b1f7b178b107b097b027afa8af37aeb8ae47add7ad58ace7ac77abf8ab87ab17aaa7aa37a9c7a957a8e7a877a807a797a727a6c6a666a606a588a526a4b7a447a3d7a358a2e7a268a1f7a178
|7,1=>0xdaa8da28d9c6d948d8c8d857d7e7d777d6f8d687d608d597d518d4a7d437d3c7d357d2e7d277d216d1a7d128d0b7d047cfe6cf86cf26cea8ce37cdc7cd48ccd7cc67cbf7cb87cb17ca98ca18c9a7c937c8b8c838c7d6c767c706c688c617c5b6c538c4b8c447c3c8c366c2f7c278c1f8c178c0f8c087c017bfa7bf28beb7be47
|7,2=>0xdba7db28
|8,0=>0xe357e2e7e277e207e197e127e0b7e056dfe7df86df17dea7de37ddc7dd57dce7dc77dc16
|9,0=>0xe3c6
|_,_=>0
def wAt:=mkWire dB 267 127 0x7fffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 9 16
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x409701834018350481512815018340183507804088350409701834018350183504869128150183401835088350100d0d897018340183501815040450183501815018090083c040970183401835040090680d0681d068150880904058018350190d010360a89701834018350406b0183401835050800181501815040450183510058018090681504815040970183401835078040684504058018350183401835
|1=>0x18090181501815068150683d018150481e088092181501036100370100d012010783401815049b90500c049350100e069ed0200c018151983407809011b90500c068150784701815018cb3980e0100606845100060100d088e501836068cc100150880e011bb0500c360150481c068cc0780901815069a50184706815100370100d01035018170404501835078370183504097018340183506885018150680e
|2=>0x100d0681504a0307834018150185a08815198371780d088e5018360127501835019e108836128150183401835040bc0680d06a6101015038350880d0500c0680d06815018e501815018360681501815040170680d04815010950680c0680d0195b068be44015018150180506845048150680e04a413c01508836100170400b0680d02137048150100e069990181706815088350681506845018150680e08881
|3=>0x6009010150880d0401701835069a50880e0183704815018360100d0101526815068150881504aa31780e0080f0883508835048150881507837018150183501835048150680904815010150183401835048151004501809079e301815018a605045040090680d02097018340481510005011a50880e0881506aaf0200f04097018340183504aa11780e018151c815018360190d0103607835018150680905080
|4=>0x68151480f050451005b08815048150680d020200183504b5b0b03608815078090181501836048150190f0103606815068be019c50080b0681507837018150202301835053310681501815100170100d0685a018170120307834100170890d0103663815049e3088360080f01a21048360181523817010591480c0b035040970183401835088350b034088150889701834048150184501036048770504706815
|5=>0x18350481501834018351281501834018350b036088150202001835040470183501815069350100e020230183501835048151005801809040170183508a21048360500c068150783601815100370100d018350100d0681504aa11780e1780e01815360150481c010457100b04829068150683e018150401701835018150481e010450680d018350181510004540151780e0101504875050470681506b750500e
|6=>0x100d0481500809088350184701815088350181506815018350181501835088350100d018150481e128150183404815018150183608815018150880d02097018347b81504897018341900e0103508815020950183404815018e50481501836040450183501834018357981701835018150680d068ce10015069a50880e7100b04829100170486912815018340400b0680d0b0370881508bb5018150183575815
|7=>0x18350100d018350100d0883508815018350783501815330350181701835010150103501835048170681501045060150880d088350183601859088157380e06817069a70880e0881501045088350880d078350181504821018350203404815060090880d100470100d0500f068151780e0101508a23048360481e010450481c0104504835018150183401835048150183604822018350680d0100e0780901815
|8=>0xb034088151900e010350480e068150101506815048290681500815088350400b0680d06845068151780f010150881501836049e10883601809088150103601045048170100d108150680e0103601817068150103507847018150483e018150185a088150890d01036018150100e01835018150183501815128150183402037048150500c0681507845018150880e0681506845068150181508836019e108836
|9=>0x18340880e010350504706815330090181704829068151900d010350401701835038150104501036048150190d0103601059088150080d08835010850680e018150680e01847010361780e01015010950680c0200f048150489501834068150880d0400b0680d048150881506815048450680d3c015088360401701835049370100e0105a088151780d01015018170103501815018360880e0101501a2104836
|10=>0x18360100d08815048170880d0484501835088360480e01834048350481506815018150183501835088350100d128160183401835078360181501835048150481508836100370100d010350880d0081708835018350100d08809018350183404815128150183406817088350500e06815660150480e050450681508897018340183501817010150880d04815010352181501036013310480e018370183604897
|11=>0x104504815010360181701815
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x272000025200000000904213000000000001f2070c000000000006881820000000054c0000000000000000000000000000123000000004440000404000000000000000f1000000003480b20000000028400000000000190000010800000000000000000000002200080000000000
|5,1=>0x10cc40300003d3000039400003720d0c00000000000c10000000000000002d300002a3000000000002910000000000000000000000000000
|6,0=>0x21c80002148832000000020487e300007d100000001f0400000007a21e0876200007421c4c00000006f21b486b21a846820000000194c00018c862118445f217485b21648581000000015885420000513000000013c8000138400000004c200004a2120800011c44610000000
|6,1=>0x35c8d430000d31344800034040003388cb300000003248c810000c623108c223044be30000bb300000002e48b7200000000000b520000b322c4800000000002b8cac22a88a912a04a53288c00028089e226cc000000000000009a10000982258894224888f3238400023080000000893
|6,2=>0x4c893024b880004b440004b040004a8929149c925248c922148091f1478400047091b10000000464916345451230000000444510143890b3420c000000105340c8000400cfd33ec80003e480003d8cf420000f223c44ef23b480003a8ce8239c4e52388ce0237c4dd20000db20000d92
|6,3=>0x610982260457f25f0c0005e4d7725d4800000017325c840005c096e25b096a2000168200016620001642588800058095e2574400056c80005685591558c00054cd51253c94e1000000053094b1528400000000005245481514d4234fcc00000013d200013b24e853914dc9343
|6,4=>0x6d4db236c440006c05ad36ac9a836989a336849a01674d9a3000198265899420001922640800063898c262c400000018836188000
|7,0=>0x8d0a3228c0a2e28b0a2a28a0a262890a222880a1e2870a1a2860a162850a122840a0e2830a0a2820a062810a0228009fe27f09fa27e45f727d49f417c89f027b89ec27a89e827989e427889e027789dc27689d827589d427489d027389cc27289c827189c427089c026f89bc26e89b82
|7,1=>0xac06ae2ab0aab1aa4aa72a94aa32a84a9f2a7869c2a6c6992a5ca952a4ca912a3ca8d2a2ca892a1ca852a0ca8129fca7d29eca7929dca7529cca7129bca6d29aca69299ca65298ca61297ca5d296ca59295ca55294ca521940a4e2930a4a2920a462910a422900a3e28f0a3a28e0a362
|7,2=>0xac8ab11
|8,0=>0xb106c31b086c11b006bf1af84000af46bc1aec6ba1ae46b81adc6b61ad46b41
|_,_=>0
def PO:=mkPO wAt oP oO 20 9 511 14
def pmP:Nat→Nat
|0=>0x63000029400010e000084000040000018c0000a400004a0000248000114000088000042000020800010000007e00003b00001c80000e000006c0000340000130000090000042000020000008000002400000c0000050000020000008000002000000
|1=>0x42200020a000101000080500040200020080010020007e70003d28001b9c000d4a0006240002f380014000009ce00048500020380010100008000003a50001800000b1c00058c000285000142000090400048000022200010200008040004000001c2
|2=>0x200200089140041ee0020730010100008040004000001821000bf38005c00002dce0016a7000a4a0004d100025ce0012c60009610004a9400244800122100090200043dc00204c001023000810000401400200800100200080000038a40010c2000848
|3=>0x10240008020004008c02000400c0000044adc02064c010020008000003c39401a5ca00b6f7005b5a80292f40127ca0092e500493180244140121ee0090e700487280242fc010400005344002982001481000a0880043040021020010694008208004040
|4=>0x8805b8424b9c2121ce10122208001104000801810520b0826048193024089812014e090000046832821000010204004900502282081101140800000354e5018c5380c539406154e030aa50142400088b9c042dce0212e70109538084a940421c8020484
|5=>0x30000210812506271d63018ef1804778b023bc4c11ca2608a5122072890239c4810da2400e511cb5288e1ad4470d4e2384a511845288a0a9c440dce2202e7110153888019c4211de2040e510187288041144003ca1850200c2012046439c2225661102b7
|6=>0x10324e5810002a900a954803caa032e15001d2a80039508020a8016e3400820a003b950010568006a7400182a000814c7054a6310a5
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x3230003002700030300000020000000000f00030000000200000000000000000003000600001203000000030a000000150300000300000000000000000300000200020000000032000003030000120000001f00030000000000000303000000
|6,0=>0x31f003d03003a00bf360000033d0001035a430d001c0000080800000003000103000000330501182d4523005623290000000008000c6903082f3d0003000081000008000e080000230400020000120000080301000334008d03032e2b0300006e005b7707030103083e3a00035c000b000003001200000300440300595f0000
|6,1=>0x808617e29003822030000080200031c1315001b00030065011901101200780094215d001c081b1700007c9b0300009202144704450000030008023d1c280113030012003d00013d1b031b0201120200030200003b2a3d2300003d400131c200001d2500303c010003005039004421080300b8089a139803603f00010003
|6,2=>0x67090700024f23a61c1f7b217d230003037e0023080008030200004f0300
|7,0=>0x871a517f6382aca01aca10bd808457c46b8ccd54524189378a555148a59dbe9f4eba883599c79e684c9155c085167ab9cf9b384b4ab6a4496658ae366d5397b2c924cb9526ad41426a754d79a8b0b4c693666655c1718e46c35e369ca1ce4e647013967311b7c88f5554b5cc62b0abbcbb2c6c86aa5d803683b36fa38bc59016
|7,1=>0x6761
|8,0=>0xa9b0356b7655a24eb472a7d074368a55b1af
|9,0=>0x1e
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 8 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_122 7 roots_122 ops++addP pm 1 dom_116 5 roots_116 ops++addP pm 2 dom_62 7 roots_62 ops++addP pm 3 dom_82 4 roots_82 ops++addP pm 4 dom_84 4 roots_84 ops++addP pm 5 dom_118 7 roots_118 ops++addP pm 6 dom_106 5 roots_106 ops++addP pm 7 dom_94 7 roots_94 ops++addP pm 8 dom_60 4 roots_60 ops++addP pm 9 dom_124 6 roots_124 ops++addP pm 10 dom_92 5 roots_92 ops++addP pm 11 dzo_82_32 4 roots_82 ops++addP pm 12 dom_110 6 roots_110 ops++addP pm 13 dom_74 4 roots_74 ops++addP pm 14 dom_46 4 roots_46 ops++addP pm 15 dom_78 5 roots_78 ops++addP pm 16 dzo_86_32 5 roots_86 ops++addP pm 17 dzo_94_32 6 roots_94 ops++addP pm 18 dom_58 4 roots_58 ops++addP pm 19 dom_54 4 roots_54 ops++addP pm 20 dom_102 4 roots_102 ops++addP pm 21 dzo_90_32 5 roots_90 ops++addP pm 22 dom_30 4 roots_30 ops++addP pm 23 dom_120 4 roots_120 ops++addP pm 24 dom_90 5 roots_90 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_126 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_84 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_94 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_124 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_92 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_74 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_zo_94_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_zo_90_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_30 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_90 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_122 7 s (0,roots_122.map (·&&&dom_122)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_126 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h
def symsG:List (List (Nat×Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_126==dom_126)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_126 gM v ys):RunD true dom_126 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_126 gM mpG SD SS NN hAt idxH ori 0 mkPools s
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
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_126 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤9) (h:RunD true dom_126 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_126 roots_126 goal_126 10:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_126
theorem lowS_126:Lower true dom_126 roots_126 goal_126 10:=S_126.noCircuit
theorem lowS_207:Lower true dom_207 roots_207 goal_207 7:=lower_slice_b [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa,8,9)] (by decide +kernel) lowS_206
theorem lowS_215:Lower true dom_215 roots_215 goal_215 7:=lower_slice_b [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,16,17)] (by decide +kernel) lowS_214
theorem lowS_219:Lower true dom_219 roots_219 goal_219 8:=lower_slice_b [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,8,9)] (by decide +kernel) lowS_218
namespace S_238
def pG:List (Nat×Nat):=[(2,10),(2,66),(2,130),(4,36),(4,68),(4,132),(6,14),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(12,14),(12,44),(12,76),(12,140),(32,36),(32,40),(32,160),(34,38),(34,42),(34,98),(34,162),(64,66),(64,68),(64,72),(96,98),(96,100),(96,104),(96,224),(128,130),(128,132),(128,160),(136,138),(136,140),(136,168),(136,200),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffff
def xsM:=roots_238.map (·&&&dom_238)
def gM:=goal_238&&&dom_238
def NN:Nat→Nat
|7=>3
|8=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0x3cb3c35aed1305b
|8,0=>0x1305b
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000001555400015554000141400001414000015554000155540001414000014142aaa8000000000002aaa8000000000002aaa8000000000002aaa80000000550000005500000055000000550000005500000055000000550000005500a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a1111000011110000111100001111000011110000111100001111000011112aaa80002aaa800000000000000000002aaa80002aaa8000000000000000555500005555000055550000555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x2c688b1ae4599a22c688
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x35cce06
|8,0=>0x146
|_,_=>0
def wAt:=mkWire dB 8 239 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 3 9
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 3 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x212d
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x11040
|_,_=>0
def PO:=mkPO wAt oP oO 8 3 7 6
def pmP:Nat→Nat
|0=>0xfff77f3ff01f000
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0xd1
|8,0=>4
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_236 6 roots_236 ops++addP pm 1 dom_174 6 roots_174 ops++addP pm 2 dom_234 6 roots_234 ops++addP pm 3 dom_230 6 roots_230 ops++addP pm 4 dom_206 6 roots_206 ops++addP pm 5 dom_106 5 roots_106 ops++addP pm 6 dom_110 6 roots_110 ops++addP pm 7 dom_202 5 roots_202 ops++addP pm 8 dom_172 5 roots_172 ops++addP pm 9 dom_166 5 roots_166 ops++addP pm 10 dom_78 5 roots_78 ops++addP pm 11 dom_228 5 roots_228 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_238 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_78 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_228 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_236 6 s (0,roots_236.map (·&&&dom_236)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_238 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h
def symsG:List (List (Nat×Nat)):=[[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xffffffff00000000ffffffff00000000,96),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccccccccccccccccccccccccccccccc,126)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_238==dom_238)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_238 gM v ys):RunD true dom_238 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_238 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s:Nat) (hs:s≤8):∀ i<NN s,bar dom_238 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
theorem noRunFull (s:Nat) (hs:s≤8) (h:RunD true dom_238 gM s xsM):False:=by
  have hmin:5≤s:=by have hl:=run_len h;change 6≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_238 roots_238 goal_238 9:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_238
theorem lowS_238:Lower true dom_238 roots_238 goal_238 9:=S_238.noCircuit
namespace S_249
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(8,9),(8,40),(8,72),(16,17),(16,80),(16,144),(24,25),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(48,49),(48,56),(48,112),(48,176),(64,65),(64,72),(64,80),(96,97),(96,104),(96,112),(96,224),(128,129),(128,144),(128,160),(136,137),(136,152),(136,168),(136,200),(192,193),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0xffffffffff
def xsM:=roots_249.map (·&&&dom_249)
def gM:=goal_249&&&dom_249
def NN:Nat→Nat
|5=>4
|6=>26
|7=>17
|8=>4
|9=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x228451f1da04aeb03d0f
|6,0=>0x60fe254c984cbe54a5da489ab4841d4542c40eea2fc562e98e2dcb82c5d22759a22c69209b31b2271b0b20aa390a68d08fdb08c72060f902c4d02a490209d02044
|7,0=>0x659b354cc74f77a4f37b47d1147aa431eab25e681fce612854102730ea7b0d45c0d0cd0a4c20943c08a93
|8,0=>0x54c622c020263cd262dc
|9,0=>0x2c020
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xc0c00000c0c00000c0c0000080800000c0c00000c0c00000c0c000008080003030000030300000303000003030000030300000303000003030000020200c000c000c000c0000000000000000000c000c000c000c000c000c0008000b03030303030300030303030303030003030303030303000303030303030300c0c0c0c080808080c0c0c0c080808080c0c0c0c080808080c0c0c0c0808080b02030203020302030203020302030203020302030203020302030203020302c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c030303030303030303030303030303030000000000000000000000000000000080808080808080808080808080808080808080808080808080808080808080b03000003030000030300000303000003030000030300000303000003030000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c0000000303030003030300030303000303030003030300030303000303030003030300c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c080b03030303030303030303030303030303000300030003000300030003000300c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0808080808080808080808080808080b03030303030303000000000000000003030303030303030000000000000000
|0,1=>0xc0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c0c0c0c0c0c0c0c0c000000030303030303030303030303030303030303030303030303020202020202020200000000000000000000000000000000c0c0c0c0c0c0c0c080808080808080b000300030003000300030003000300030303030303030303020302030203020000c0c0000080800000c0c0000080800000c0c0000080800000c0c0000080b00030303000302030003030300030203000303030003020300030303000302c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c00000c0c0c0c0c0c000303030203030302030303020303030203030302030303020303030203030302c0c0c0c0c0c0c0c0c0c0c0c080808080c0c0c0c0c0c0c0c0c0c0c0c0808080b0303030303030302020202020202020303030303030303020202020202020200c000c000c000c000c000c00080008000c000c000c000c000c000c0008000b03030303000300030303030300030003030303030003000303030303000300c0c0c0c0c0c0c0c0c000c000c000c000c0c0c0c0c0c0c0c0c000c000c000c0000000300000002000000030000000200000003000000020000000300000002c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000303030303030303030303030303030303030303030303030300030003000300
|0,2=>0xc0c0c0c0c0c0c0c0000000000000000080808080808080b030303030303030303000003030000030303030303030303030000030300004040404040404040404040404040000040404040404040404040404040400030303030303020203030303030302020303030303030202030303030303020200000000000000000000000000000000c0c0c0c0c0c08080c0c0c0c0c0c08080000000000000003030202030302020000000000000000030302020303020200c000c00080008000c000c00080008000c000c00080008000c000c0008000b0003000303030203000300030303020300030003030302030003000303030200000000c0c0c0c000000000c0c0c0c0000000008080808000000000808080b03030303030303000000000303030303030303030303030000000002020202c0c0c0c0c0c0c0c00000c0c000008080c0c0c0c0c0c0c0c00000c0c000008080000000000000000000303000002020000000000000000000003030000020200000000c0c0c0c000000000c0c0c0c000000000c080c08000000000c080c0803000300030003000300030003000300030002000300020003000200030002c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c080c0c0c080c0c0c0800030200000302000003020000030200000302000003020000030200000302
|0,3=>0x303030303030303030303030303030303030000030300000303000003030000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c0c0c000c0c0c000c0c0c0303030303020302030303030302030203030303030203020303030303020302c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c080c080c080c080c080c0800000000000000000000000000000003020302030203020302030203020302c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c08080c0c08080c0c08080c0c080800000000000000030203020302030200000000000000000302030203020302
|_,_=>0
def sP:Nat→Nat
|0=>0x14608780021f14625e1c814628258020c1462870081467091c02192c42470081466891c02191582470081465875402142c628020518a4070081462474802051902411c01462473c020b14418a0081491ce0081461cd00830b18a0081440c2040
|1=>0x1c0205c46247008146c091c02192c62470081462931c021f146247448146247bc0205b862561c8146247b4022cac51891c07c5a862472051061e9008146a091c02051891e60081462479402051891e40081891e3008146247880205846247008
|2=>0x51891c0205d862470081462470081460891c020b1462470085cb14624700814625e1c020b16e1891c02050c62410082df1891c0205d462470082c51891d1008d0b146247008146cc9047008146c89
|_=>0
def sO:Nat→Nat→Nat
|5,0=>0x9303180cc006
|6,0=>0x18aebe75bbac1d52ea274dba51d1cc8774039e5ce4e6b7323975cace4f7243905c76c34716b899c3ee187
|7,0=>0x14089cbcc6254f2378e3c5221910487ebbd9ddeee8770bb69da6ecc7
|8,0=>0xae3d59a9ef487
|9,0=>0x1636
|_,_=>0
def wAt:=mkWire dB 55 250 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 13
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 6 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x1c84a231c943211c64a031c9471518549011c9480114041031c840191c0591d14643031c64b271c56701218441d286c725447480120947251c0465124547257495623147451925b4715107462525796151c549151c953212404725449481d2004715247491910546251c549211c84719
|1=>0x18849211c54b011c5511d00846011c547211c6451d140421920947152004b251c54125
|_=>0
def oO:Nat→Nat→Nat
|5,0=>0x19803
|6,0=>0x2d2564a4800281000000000004c4909111f3386688c1162284488798c300024c00063
|7,0=>0x4f29a52ca494728a50ca093f27a4ec9c93726a4cc9892f2
|8,0=>0xa6200290d11
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 11
def pmP:Nat→Nat
|0=>0xd226384013041c0a0a040045012263804a00c022dce00b503003109800d71c004d8e001a43000beb800131c00088e00041200020080010000006000001400000400000180000094000041000020000008000003800000a000002000000c000002000000
|1=>0x808233b09139d040fce8007df2120528c053985228022114c5
|_=>0
def pmB:Nat→Nat→Nat
|5,0=>0x85
|6,0=>0xb1c300600000034b29020e10330150f002009
|7,0=>0x217dc8e091e6975665a76226dd
|8,0=>0x9514d9
|9,0=>0x12
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 25 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_248 7 roots_248 ops++addP pm 1 dom_241 7 roots_241 ops++addP pm 2 dom_233 7 roots_233 ops++addP pm 3 dom_225 5 roots_225 ops++addP pm 4 dom_113 5 roots_113 ops++addP pm 5 dom_73 4 roots_73 ops++addP pm 6 dom_217 7 roots_217 ops++addP pm 7 dom_121 7 roots_121 ops++addP pm 8 dom_161 4 roots_161 ops++addP pm 9 dom_81 4 roots_81 ops++addP pm 10 dom_185 7 roots_185 ops++addP pm 11 dom_209 5 roots_209 ops++addP pm 12 dom_145 4 roots_145 ops++addP pm 13 dom_240 4 roots_240 ops++addP pm 14 dom_120 4 roots_120 ops++addP pm 15 dom_177 5 roots_177 ops++addP pm 16 dom_216 4 roots_216 ops++addP pm 17 dom_41 4 roots_41 ops++addP pm 18 dom_169 5 roots_169 ops++addP pm 19 dom_184 4 roots_184 ops++addP pm 20 dom_57 5 roots_57 ops++addP pm 21 dom_153 5 roots_153 ops++addP pm 22 dom_232 4 roots_232 ops++addP pm 23 dom_105 5 roots_105 ops++addP pm 24 dom_201 5 roots_201 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_249 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_120 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_232 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_105 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_248 7 s (0,roots_248.map (·&&&dom_248)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_249 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_248 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffffffff00000000ffffffff00000000,96),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_249==dom_249)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_249 gM v ys):RunD true dom_249 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_249 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 26 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 17 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 4 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s:Nat) (hs:s≤9):∀ i<NN s,bar dom_249 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_159:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_159:Lower true dom_159 roots_159 goal_159 8:=lower_iso_b isoMvS_159 (by decide +kernel) lowS_119
def isoMvS_175:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_175:Lower true dom_175 roots_175 goal_175 8:=lower_iso_b isoMvS_175 (by decide +kernel) lowS_111
def isoMvS_183:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_183:Lower true dom_183 roots_183 goal_183 8:=lower_iso_b isoMvS_183 (by decide +kernel) lowS_95
def isoMvS_187:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_187:Lower true dom_187 roots_187 goal_187 9:=lower_iso_b isoMvS_187 (by decide +kernel) lowS_125
def isoMvS_189:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_189:Lower true dom_189 roots_189 goal_189 9:=lower_iso_b isoMvS_189 (by decide +kernel) lowS_123
def isoMvS_190:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_190:Lower true dom_190 roots_190 goal_190 10:=lower_iso_b isoMvS_190 (by decide +kernel) lowS_126
def isoMvS_221:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_221:Lower true dom_221 roots_221 goal_221 9:=lower_iso_b isoMvS_221 (by decide +kernel) lowS_123
def isoMvS_222:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff00000000ffffffff00000000,96),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_222:Lower true dom_222 roots_222 goal_222 9:=lower_iso_b isoMvS_222 (by decide +kernel) lowS_123
def isoMvS_231:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_231:Lower true dom_231 roots_231 goal_231 7:=lower_iso_b isoMvS_231 (by decide +kernel) lowS_207
def isoMvS_235:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_235:Lower true dom_235 roots_235 goal_235 9:=lower_iso_b isoMvS_235 (by decide +kernel) lowS_125
def isoMvS_237:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112)]
theorem lowS_237:Lower true dom_237 roots_237 goal_237 9:=lower_iso_b isoMvS_237 (by decide +kernel) lowS_125
def isoMvS_243:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]
theorem lowS_243:Lower true dom_243 roots_243 goal_243 9:=lower_iso_b isoMvS_243 (by decide +kernel) lowS_123
def isoMvS_245:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_245:Lower true dom_245 roots_245 goal_245 8:=lower_iso_b isoMvS_245 (by decide +kernel) lowS_219
def isoMvS_246:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_246:Lower true dom_246 roots_246 goal_246 9:=lower_iso_b isoMvS_246 (by decide +kernel) lowS_123
def isoMvS_250:List (Nat×Nat):=[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)]
theorem lowS_250:Lower true dom_250 roots_250 goal_250 10:=lower_iso_b isoMvS_250 (by decide +kernel) lowS_126
def isoMvS_252:List (Nat×Nat):=[(0xffffffff000000000000000000000000ffffffff00000000,32),(0xffff0000ffff0000ffff0000ffff0000,112),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)]
theorem lowS_252:Lower true dom_252 roots_252 goal_252 10:=lower_iso_b isoMvS_252 (by decide +kernel) lowS_126
theorem lowS_127:Lower true dom_127 roots_127 goal_127 11:=lower_slice_b [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,8,9)] (by decide +kernel) lowS_126
theorem lowS_223:Lower true dom_223 roots_223 goal_223 10:=lower_slice_b [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,8,9)] (by decide +kernel) lowS_222
namespace S_239
def pG:List (Nat×Nat):=[(1,9),(1,33),(1,65),(1,129),(2,10),(2,66),(2,130),(3,11),(3,35),(3,67),(3,131),(4,36),(4,68),(4,132),(5,13),(5,37),(5,69),(5,133),(6,14),(6,38),(6,70),(6,134),(7,15),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,44),(12,76),(12,140),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,98),(34,162),(64,65),(64,66),(64,68),(64,72),(96,97),(96,98),(96,100),(96,104),(96,224),(128,129),(128,130),(128,132),(128,160),(136,137),(136,138),(136,140),(136,168),(136,200),(192,193),(192,194),(192,196),(192,200),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7ffffffffffffffff
def xsM:=roots_239.map (·&&&dom_239)
def gM:=goal_239&&&dom_239
def NN:Nat→Nat
|5=>1
|6=>8
|7=>32
|8=>35
|9=>8
|10=>1
|_=>0
def HT:Nat→Nat→Nat
|5,0=>0x77ed5
|6,0=>0xc7041c250cafcc8927e68f65065170540ac31d29
|7,0=>0xffe3debbe8df0d9de7bcdaa3dd7b85cd8aebd51da4420a32187ce4f7cbbf72edd6f31e6b8276b53b5087c4c8b94513843c78408d437864350ed323e031b432e2c72b5ef1a689116780e41e0a55f053fe
|8,0=>0xf6854f0c12ec0e5eb8d7c4172ba993909888f1d48e9f38ca2b89fc080d357ad9d729ed70ac66cab3661c2657e355dc054cf34efa94e59744c5c3fbd23f374358fb32bb62b7042ad9523dfd20e811bacf178901144200a19
|9,0=>0x88f057dfda704993b57832bb62b9661406801464
|10,0=>0x3ce8d
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffff000000000000ffff000000000000ff00000000000000ff000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00555500005555000055550000555500005555000055550000555500005500ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffff000000000000ffff000000000000ffff000000000000ffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000f0f00000f0f00000f0f00000f0f0000000f0000000f0000000f00000000ffff0000ffff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffff000000000000ff000000ff000000ff0000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000
|0,1=>0xff000000ff000000ff000000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff0000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff00333300003333000033330000333300003333000033330000330000003300ffff0000ffff0000ffff0000ffff000000ff000000ff000000ff000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffff0000ffff0000ffff0000ffff00000000000000000000ff000000ff000000000000000000ffff0000ffff00000000000000000000ff000000ff00ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ff0000000000ffff000000000000ffff000000000000ffff000000000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000000000000000ff000000ff000000ffff000000000000ffff0000ff0000ff000000ff000000ff00000000000000ff000000ff000000ff00000000
|0,2=>0xffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00000000000000ff00000000000000ff00000000000000ff000000000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff0000000000000000000000000000000000ffff000000000000ffff0000ff00000000000000000000ff000000000000000000000000000000ff00000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00cccc0000cccc0000ccff0000cccc0000cccc0000cccc0000ccff0000cccc00000000000000000000000000000000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f00000fff00000fff00000fff00000fff00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000000000000000000000000000ffff0000ff00ffff0000ffff0000ff000000ff000000ffff0000ffff0000ffff0000ff000000000000000000ff000000ff0000000000000000000000ff000000ff00ffff000000000000ffff0000ff000000ffff000000000000ffff0000ff00
|0,3=>0xff00000000000000ff00000000000000ff00000000000000ff0000000000ff0000ffff0000000000000000000000ff0000ffff0000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff00000000fff00000f0f00000fff00000f0f00000fff00000f0f00000fff00000f0f0ffff0000ffff0000ffff0000ffff000000000000ff00000000000000ff0000000000000000000000000000000000ffff0000ffff0000ffff00000000cccc0000cccc0000ffff0000cccc0000cccc0000cccc0000ffff0000cccc0000000000000000000000000000000000000000ff00000000000000ff00ffff0000ffff0000ff00000000000000ffff0000ffff0000ff0000000000ff000000ff000000ff000000ff00000000000000ff00000000000000ff000000000000000000ffff0000000000000000000000000000ffff00000000ff000000ff000000ffff0000ff000000ff000000ff000000ffff0000ff0000000000ff00000000000000ff00000000000000ff00000000000000ff0000000000000000000000000000000000ffff000000000000ffff00000000ffaa0000aaaa0000ffaa0000aaaa0000ffaa0000aaaa0000ffaa0000aaaa
|_,_=>0
def sP:Nat→Nat
|0=>0x1c62890c20591c660a2430811c65ca2560c204714c24308100644a2430811c650a2430811c62890c20531c648a2c90c20471440c20471912890c20400c20503c718a24204e1c628910308100a24308d1c614c2c308100a2420481c61440c2040
|1=>0x2430811ea2890c204718530b0c204718a2439c11c614a94204718c28908190718570a2c30811cc28b24308100c2430813c719e30a2430811a32890c20471a22890c20471a02890c204018a2430817c719d2890c204719c2890c20401ca24305a
|2=>0x471852890c20471853090c204718a2760c204616d0c204718ac490c20401d72a82430811c62890c20751c6cca2430811c628b0c20721c62b12610c204029b24305a1c61700c21c62891030811c6b8a2430811c60c206c1c6143081b071ab70a
|3=>0xc20471b92890c20471af2890c204718a2430813c71af14a2430811c62b1a090c20471852890c20401c6e0a24304719728b2430811e02890c204718ac498430811c648c2890c204718a243081dc719c2890c20471af30a2430811c615c2890c2
|4=>0x24308100718a26d0c20471852890c204718ac490c204718a2660c204718c2890c204718ac090c21c60c207ec8718528b2430811c628b2430810071742430811c630a2c90c204718a243081f46f0a2430811c62bb24204718a243081e87192289
|5=>0x2890c204718a243081c8718aa090c204718a
|_=>0
def sO:Nat→Nat→Nat
|5,0=>6
|6,0=>0xddc3070a5c22706dc147035c067
|7,0=>0x4ba1268481918844210a640dcfb83ce0eb8391cdd73560cd83160bd82d60ad829609d825608d821607e71da06e819a05e815a04e811a03e8
|8,0=>0x24a790de3a98ca22a888661a784a20b780e1fb87ce1eb878e1da97465c89705db986c61a8967e597863e18695f657585b6166757dd57853a54684fa1368
|9,0=>0xa2628189e627189a626189662518
|10,0=>0x2917
|_,_=>0
def wAt:=mkWire dB 63 240 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 6 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x24ac9196c2c9011c66d052890a2530b2f19147492916dca2428945b72890a25706451b289491928749290a94aa3247660d289491b483cc192894b2b2464a1d147c92984a491f2cc89197864929146ca256c2c9011c65019309ca1d286491f287492954a4919306491928749192874929
|1=>0x289ca262464a25246471924a4a1f2464a1db478928c474a1bb434928c864a26280461d306ca1d14749292cac91924a491d286ca25d024a1f2464a1984a491f247ca1b3064a1d257ca19146ca253094a1d146ca252b24a262874929b4749282890a25286c719286491dc498a1b2744a1f
|2=>0x289891d1c64a242894a1b246ca1db414a24
|_=>0
def oO:Nat→Nat→Nat
|6,0=>0x3000
|7,0=>0x3b33833713433132e32b30002832532232021f10001d21a30000001821621421220f30c30000a2082000062000033
|8,0=>0x8027e27c27a27827627427227026e26c26a26826626516326216025e25c25a25825625425225024e24c24a24824624424224023e2
|9,0=>0x891881871861851841831821
|_,_=>0
def PO:=mkPO wAt oP oO 14 6 63 12
def pmP:Nat→Nat
|0=>0x202830a04ff89dd11fa23b44668861102013f4276849e0850102417e811101fe03f406680c101600200024003c006000b8007000c001000100008000
|1=>0x50fd71da73b4d7699dd322863f4c7698dd319a6030a7f94fd29da433c866902c
|_=>0
def pmB:Nat→Nat→Nat
|6,0=>0x140
|7,0=>0x944730e3900040580c21c34800020c30c12805c600300b
|8,0=>0x2da6b76a2278ef6e5595713806c2c66651ba1e7eaba96e2229aaa
|9,0=>0xa9a3eaaa16e4
|10,0=>0xd
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 6 (j%128);fld (pmP (k/32)) 15 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_238 9 roots_238 ops++addP pm 1 dom_47 6 roots_47 ops++addP pm 2 dom_111 8 roots_111 ops++addP pm 3 dom_175 8 roots_175 ops++addP pm 4 dom_79 6 roots_79 ops++addP pm 5 dom_167 6 roots_167 ops++addP pm 6 dom_237 9 roots_237 ops++addP pm 7 dom_235 9 roots_235 ops++addP pm 8 dom_103 5 roots_103 ops++addP pm 9 dom_230 6 roots_230 ops++addP pm 10 dom_143 5 roots_143 ops++addP pm 11 dom_231 7 roots_231 ops++addP pm 12 dom_207 7 roots_207 ops++addP pm 13 dom_227 6 roots_227 ops++addP pm 14 dom_205 6 roots_205 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_239 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_205 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_238 9 s (0,roots_238.map (·&&&dom_238)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_239 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_238 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_239==dom_239)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_239 gM v ys):RunD true dom_239 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_239 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 35 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s:Nat) (hs:s≤10):∀ i<NN s,bar dom_239 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=cutRoot s xsM||found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 6=true:=by decide +kernel
theorem proper_failG:∀ zs∈xsM.sublists,zs≠xsM→unorientedCov pG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s≤10) (h:RunD true dom_239 gM s xsM):False:=by
  have hmin:6≤s:=by have hl:=run_len h;change 7≤s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [Bool.or_eq_true] at hr
  rcases hr with hcut|hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_239 roots_239 goal_239 11:=lower_of_search (pairs:=pG) (by decide +kernel) proper_failG noRunFull
end S_239
theorem lowS_239:Lower true dom_239 roots_239 goal_239 11:=S_239.noCircuit
def dzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def gzo_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0a00000000
def gsh_219_32:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0e000000000f0e0f0a
theorem lowS_zo_219_32_82:Lower true dzo_219_32 roots_219 gzo_219_32 7:=lower_iso_b (d1:=dom_219) (r1:=roots_219) (T1:=gsh_219_32) [(dom_219,32)] (by decide +kernel) (lower_slice_b (T:=gsh_219_32) [(0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00,0,8),(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a00000000
def gsh_211_32:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_32_82:Lower true dzo_211_32 roots_211 gzo_211_32 6:=lower_iso_b (d1:=dom_211) (r1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (lower_slice_b (T:=gsh_211_32) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_251
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(8,9),(8,10),(8,40),(8,72),(16,17),(16,18),(16,80),(16,144),(24,25),(24,26),(24,56),(24,88),(24,152),(32,33),(32,40),(32,160),(34,35),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,56),(48,112),(48,176),(64,65),(64,66),(64,72),(64,80),(96,97),(96,98),(96,104),(96,112),(96,224),(128,129),(128,130),(128,144),(128,160),(136,137),(136,138),(136,152),(136,168),(136,200),(192,193),(192,194),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x7fffffffffffffff
def xsM:=roots_251.map (·&&&dom_251)
def gM:=goal_251&&&dom_251
def NN:Nat→Nat
|7=>7
|8=>45
|9=>57
|10=>8
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xf4e29a164776fe061d894ffdc265dd1a474
|8,0=>0xcd8b1c5308b6095b5cb2a9e7ea3e79a1b558a06d8693184152817637dcec6a96466f316694264c3160fd65e9145c2005783954419524e35197e503fc455bd4231f3a6443649f329cf2ebde2d57527a4525a6c1f70c1ea3b1bbbe1aca211cec10957108c30e97e0ade80815b0601504f0e
|9,0=>0xd1ac6cfbf0c1f37a4324a40ab99b7d935e38f5c18a86a8a54c89f908869588354882f2849037eb067d1f67afdf74a496ff956a1bd68a73636296020f5e9145c2ca5ab025a0b3563af517bc4de06468ae40a003ef5e3cbc13bfe239b7537255351b534d1b2e45d2a09026029257702474023bdb19398182a81752116091101c00dada06e1605c1004e7b0385d016aa
|10,0=>0x840fe6c0fe65840411753ecf23e1f9294df0fda5
|11,0=>0xff75e
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a303030303030303030303030303030303030303030303030303030003030300f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000000000000000000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f0000000000000000000000f0f00000000000000000000000000000f0f00000000c0c0c0c0c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0c0c0c0c0000000000000000f0f0f0f0000000000000000000000000f0f0f0f00000000f0f00000f0f00000f0f0f0f0f0f00000f0f00000f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f00
|0,2=>0xf000000000000000f000000000000000f000000000000000f00000000f000f0f0f000f000f000f0f0f000f000f000f0f0f000f000f000f0f0f000f0000f000f000f000f000f000f00000000000f000f000f000f000f000f0000000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f00000f0f00000f0f0f0f0f0f0f000f0f00000f0f00000f0f0f0f0f0f0f00f0f0f000f0f0f000f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f000f000f000000000f0f0f0f0f0f0f0f000f000f00000000f0f0f0f000000000f0f0f0f0f0f0f000f0f0f0f000000000f0f0f0f0f0f0f000000000000000000f0f0f0f0f0f000000000000000000000f0f0f0f0f0f000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f000f0f0f0f0f0f0f00
|0,3=>0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f000000000000f0f0f0f0f0f0f0f00000f0f000000000f0f0f0f0f0f0f0f00000f0f00000000000000000000000000f000f000000000000000000000000000f000f00000000f0f0f0f0f0f0f0f0f0f000f0f0f00000f0f0f0f0f0f0f0f0f0f000f0f0f0000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f0000000000000000000000000000000000000000000000f0f0000000000000f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000f0f000000000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000000000f000f000f000f000f0000000f0000000f000f000f000f000f0000000f0000f0f0f0f000f000f0f0f0f0f000f00000f0f0f0f000f000f0f0f0f0f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00000000000000000000f000f000f00000000000000000000000f000f000f0000
|0,4=>0xf000f000f000f000f000f000f000f000f000f00000000000f000f0000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000000000000f000f00000000000f000f00000000f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000f0f000f0f0f00000f0f000f0f0f00000f0f000f0f0f00000f0f000f0f0f00000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00000000000000000000000000000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f00000000000f000f0000000000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000000000000f0f00000000
|_,_=>0
def sP:Nat→Nat
|0=>0x120c08f008830e0824181001870c120d081007830508241810018284380c0803418704120c0800c38604120c3801a18c850824187025c284120cb010018a0508241810044284120c086141420304040060a20203040400620104831e0030e182c4830e3430c0a2c4830e182840608080
|1=>0x6c00803e6c704120c0800c382ae120c0800c3828906b40800a241a158040061c10483023c02b0c64284120c386181421c0604006541420906040061454284120c0803e18c84120c3815018284120c0804c18284120c0804a18284120c0800c3828906900804618284120c0801a18284
|2=>0xc83050824187006030e18104830200686521420906040061c144090604006141420906040061c14589061c09f7410483020030508241b80200c061c14589060430508241b60200c061814584120c0b40c1420906040330c30284120c0806418284120c080563828906840800c14209
|3=>0xa104835a040061c1588906040170c14209060401f0c6420906040170c14209061c0800c40284120c08030186050824181007d5850824181001a08508241810018284120e0010018284120df8100182be0824181001860516104830e1860508241bd0018705120de010019d850824181
|4=>0x6040060a104837a0402b0a104832c040060a104836a040061c14209061c080301828b08241813e18284120c3810018284120e10100cc3050824181001948508241810035585082418100ac284120d081007c3056210483020030508241812400c061c1420906040060ab82090604006
|5=>0x8241810019d050824181001a2850824181001a2850824187020030c0a104830e003190ac420906040060a1048388040061814584120c0800c1420906843810018284120ce8100c8305082418100182880824181010c305082418100182880824187020030516104830e0431b1c14209
|6=>0x18d8508241810060284120cb0100603056210483020030508241cb02025060a1048302015860a104830e0030508241c9020030e0a241a1020030c0a1048342040480c1420906040068e14209060400618142090674080641860508241810018284120e3010018284120de010088305
|7=>0x30508241810018c850824181003430508241810018284120d08100187050824181001828b0824181007c305082418100186050824181
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x2d609601d8059c0f701e0007
|8,0=>0x197863e18785fe17785ba5659576155853614674fa13684ba1259476114943210483f20f483b20e48375cd583360c582f60b492b20a48272094823208481ee47381ae0638171c54813204390ee0338
|9,0=>0x36f8d9a75e8d5a34e8d1a33e8cd672d8c9631c9c4e70b8c0e2fb8bce2eb8b8a6da8b466c98b026b79abe2a78a7e2978a3a68689f667589b62658972654892e64388ee23388ae223886a612882660187e61f187a61e187625d0871e5bf86de1af869e19f8
|10,0=>0xebe3a78e7e3978e3e3878dfe3778
|11,0=>0x3b77
|_,_=>0
def wAt:=mkWire dB 76 252 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 7 14
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 7 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0xa110c0742050c130a110c411c070a110e170c1102010a113e070c150a050c130a1140073e110c1512750c330a0536150a110c070a0502010a1102010c110a0130050c010c1702561c010a1126490c1e0c0302010a210e11020114270a2102011c070e170a1102010a11020108010a050c11020108010a0514270a210e110201
|1=>0x2e50c670a0108010c010a116e0156170c050c0108010a050cd5181302150c2d08010a0518750c330a050c050c130a113ec708050c150c150a110c075e110c3b0a110a1156130c050c3a0c130a110e170a110201020100150c0512750c330a0520011c070a1102551c010a110a0102010c150ca518010a054e151a070c113639
|2=>0x8050c150c1e02010c010a112c110c1756130c0508050a1156010c050a010c150c1d02011c070a110c010a050c050c151c030a112c010c1730170c010c300a05020108010a053a050c330a050a110cc7021118850c1302150c3102010a050a110c010a0502650a010a110e1102010a210e110201080102010a110c150c380a11
|3=>0xa850c130c330a050c310a051a170c110cc702113e070c150c380a110c1f02010c1f020102010a0508050a010c320a0508010a050c1302010c330a053e050c150e11020156110c050e110201001102010a110c072c050c170c170c051813021502010a1100110c0102010c1542010c131a010c1118010a050c110c050c130c05
|4=>0xa010c110c130a1108010c150a050c070c010c170c01021130130c0156030c0502010c050c2f08010c130a110c13021526150c03
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x5902661030620210088004
|8,0=>0x9d34d1a5cd286913471a309126863419a00cfa67a33b99d0ce266e33599a0cca66232f9970cb26563299940c9a64a3239910c8263e31d98e0c6a63231798b0c526263119880c3a61a3
|9,0=>0x1102871430a145082831410a0450027f13f09f44f827b13d09e44f027713b09d44e827313909c44e026f13709b44d826b13509a44d026713309944c826313109844c025f12f09744b825b12d09644b025712b09544a825312909444a02
|10,0=>0x8c8c6062e31618a8c506263121
|_,_=>0
def PO:=mkPO wAt oP oO 16 7 127 13
def pmP:Nat→Nat
|0=>0x40e27801e313c00e9c1e0054e0f002862f8011303c0041cbe001ce2f000ce178006383c0031abe0018d1f000c62f8006307c003181e0009c6f00037038001703c0008c4000046000000fff80007efc0003c9e0000e4f000062f8000303c0000800000009c00000018000000800000020000000
|1=>0x22d687811570bc08a1a3e0421eaf0204fbf810279fc0811a7e0401f9f0200f7f81007abc0801e1e0400d1f0100f07807cb83c03b589e01d2ccf00e96478060005002a581e0150c8f008c6078044b83c02218be0110c1f008860780423060020391e0101c5f006d6078035303c01a181e009ac0f
|2=>0x322868f9826303cc02ba1e445dc2f20a860d9044317c822183e40f1e0f204c607901e303c80b181e4051c0f200af078915f0bc48ab85e20f9c0f1068e078830707c413189e2054e0f10287878814383c403122e2010e0f080c68f8404383c1c03c3e0e008160410f7782087abc0901a1e0480494
|3=>0x280bb85f405dc0f902ee17c10234be02a5c1f0121e0f80827024002303d822181e8150e0f40a0607a044383d02208be8050c0f
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x3c105062c201
|8,0=>0xa929ef5d4c321c56f6e43095020ae447ab5ac338d90d71c4c4da3b1e59a7c6d62a6a359779d0b3
|9,0=>0x69648e6512c4ca53ae52fe44f5541630e743d705cb228475e3653225b574bee2059a8e50b0f98e29e650eca421fa248a9692
|10,0=>0xcd808874b51a2b
|11,0=>6
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 7 (j%128);fld (pmP (k/32)) 29 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_250 10 roots_250 ops++addP pm 1 dom_249 10 roots_249 ops++addP pm 2 dom_235 9 roots_235 ops++addP pm 3 dom_123 9 roots_123 ops++addP pm 4 dom_163 5 roots_163 ops++addP pm 5 dom_59 6 roots_59 ops++addP pm 6 dom_227 6 roots_227 ops++addP pm 7 dom_115 7 roots_115 ops++addP pm 8 dom_171 6 roots_171 ops++addP pm 9 dom_147 5 roots_147 ops++addP pm 10 dom_243 9 roots_243 ops++addP pm 11 dom_187 9 roots_187 ops++addP pm 12 dzo_83_32 5 roots_83 ops++addP pm 13 dom_91 6 roots_91 ops++addP pm 14 dzo_91_32 6 roots_91 ops++addP pm 15 dom_75 5 roots_75 ops++addP pm 16 dom_219 8 roots_219 ops++addP pm 17 dom_179 7 roots_179 ops++addP pm 18 dzo_219_32 7 roots_219 ops++addP pm 19 dzo_211_32 6 roots_211 ops++addP pm 20 dom_83 5 roots_83 ops++addP pm 21 dom_99 4 roots_99 ops++addP pm 22 dom_43 5 roots_43 ops++addP pm 23 dom_51 4 roots_51 ops++addP pm 24 dom_217 7 roots_217 ops++addP pm 25 dom_155 6 roots_155 ops++addP pm 26 dom_203 6 roots_203 ops++addP pm 27 dom_211 6 roots_211 ops++addP pm 28 dom_107 7 roots_107 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_251 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_zo_83_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_zo_91_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_zo_219_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_211_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_250 10 s (0,roots_250.map (·&&&dom_250)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_251 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h
def symsG:List (List (Nat×Nat)):=[[(0xffff0000ffff00000000000000000000ffff0000ffff0000,48),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_251==dom_251)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_251 gM v ys):RunD true dom_251 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_251 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 45 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 45 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 57 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 57 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500540055005500550055005500550054004400
def gsh_246_8:=0x55005500550055005500550055005400550055005500550055005500540044
theorem lowS_zo_246_8_148:Lower true dzo_246_8 roots_246 gzo_246_8 7:=lower_iso_b (d1:=dom_246) (r1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (lower_slice_b (T:=gsh_246_8) [(0x44004400440044004400440044004400440044004400440044004400440044,0,2),(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055000000000000000000550055005500550000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_222_32:=0x5555555500000000555555550000000055555555000000005555555500000000
def gzo_222_32:=0x5555555500000000555555550000000055555554000000005554555000000000
def gsh_222_32:=0x55555555000000005555555500000000555555540000000055545550
theorem lowS_zo_222_32_82:Lower true dzo_222_32 roots_222 gzo_222_32 7:=lower_iso_b (d1:=dom_222) (r1:=roots_222) (T1:=gsh_222_32) [(dom_222,32)] (by decide +kernel) (lower_slice_b (T:=gsh_222_32) [(0x50505050000000005050505000000000505050500000000050505050,0,4),(0x55005500000000005500550000000000550055000000000055005500,0,8),(0x55555555000000005555555500000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
namespace S_254
def pG:List (Nat×Nat):=[(2,10),(2,18),(2,66),(2,130),(4,20),(4,36),(4,68),(4,132),(6,14),(6,22),(6,38),(6,70),(6,134),(8,10),(8,40),(8,72),(12,14),(12,28),(12,44),(12,76),(12,140),(16,18),(16,20),(16,80),(16,144),(24,26),(24,28),(24,56),(24,88),(24,152),(32,36),(32,40),(32,160),(34,38),(34,42),(34,50),(34,98),(34,162),(48,50),(48,52),(48,56),(48,112),(48,176),(64,66),(64,68),(64,72),(64,80),(96,98),(96,100),(96,104),(96,112),(96,224),(128,130),(128,132),(128,144),(128,160),(136,138),(136,140),(136,152),(136,168),(136,200),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffff
def xsM:=roots_254.map (·&&&dom_254)
def gM:=goal_254&&&dom_254
def NN:Nat→Nat
|9=>4
|10=>2
|11=>1
|_=>0
def HT:Nat→Nat→Nat
|9,0=>0x5ad9e50cde420ac103ed
|10,0=>0x6f64d371a0
|11,0=>0xba90f
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0x5555555555555500555555555555550055555555555555005555555555555500aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa01555555555554000155555555555400015555555555540001555555555554000002a802a802a8000002a802a802a8000002a802a802a8000002a802a802a80005555555555005500555555555500550055555555550055005555555555005500aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015554000155540001555400015554000155540001555400015554000155540002a802a802a802a802a802a802a802a802a802a802a802a802a802a802a802a80505050505050505050505050505050505050505050505050505050505050505088888888888888888888888888888888888888888888888888888888888888880001555400015400000155540001540000015554000154000001555400015402aaaaaaaaaaaaaaa80000000000000002aaaaaaaaaaaaaaa80000000000000005555555555555555555555555555555500000000000000000000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0x7654310876543107b654310c7654310a7b543107654391076543210
|_=>0
def sO:Nat→Nat→Nat
|9,0=>0x6210822008
|10,0=>0xa2208
|11,0=>0x307
|_,_=>0
def wAt:=mkWire dB 13 255 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 4 10
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 4 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x75595865d5765955a99d86dd5
|_=>0
def oO:Nat→Nat→Nat
|9,0=>0x62422202
|10,0=>0x9181
|_,_=>0
def PO:=mkPO wAt oP oO 10 4 15 8
def pmP:Nat→Nat
|0=>0x8ff6df4ff1df0ff0df000
|_=>0
def pmB:Nat→Nat→Nat
|9,0=>0x55a
|10,0=>0x34
|11,0=>1
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 3 (j%128);fld (pmP (k/32)) 12 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_252 10 roots_252 ops++addP pm 1 dom_190 10 roots_190 ops++addP pm 2 dom_126 10 roots_126 ops++addP pm 3 dom_250 10 roots_250 ops++addP pm 4 dom_246 9 roots_246 ops++addP pm 5 dzo_246_8 7 roots_246 ops++addP pm 6 dom_238 9 roots_238 ops++addP pm 7 dom_222 9 roots_222 ops++addP pm 8 dzo_222_32 7 roots_222 ops++addP pm 9 dom_206 6 roots_206 ops++addP pm 10 dom_230 6 roots_230 ops++addP pm 11 dom_214 6 roots_214 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_254 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_zo_246_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_222_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_214 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_252 10 s (0,roots_252.map (·&&&dom_252)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_254 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_252 h
def symsG:List (List (Nat×Nat)):=[[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60),(0xcccccccccccccccccccccccccccccccc,126)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_254==dom_254)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_254 gM v ys):RunD true dom_254 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_254 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 2 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s:Nat) (hs:s≤11):∀ i<NN s,bar dom_254 gM mpG SD SS NN hAt idxH ori 0 mkCut s i=true:=by
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
def isoMvS_191:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_191:Lower true dom_191 roots_191 goal_191 11:=lower_iso_b isoMvS_191 (by decide +kernel) lowS_127
def isoMvS_247:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_247:Lower true dom_247 roots_247 goal_247 10:=lower_iso_b isoMvS_247 (by decide +kernel) lowS_223
def isoMvS_253:List (Nat×Nat):=[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_253:Lower true dom_253 roots_253 goal_253 12:=lower_iso_b isoMvS_253 (by decide +kernel) lowS_251
def dzo_151_8:=0xff00ff00000000000000000000000000ff00ff00
def gzo_151_8:=0xff00fe00000000000000000000000000fe00ee00
def gsh_151_8:=0xff00fe00000000000000000000000000fe00ee
theorem lowS_zo_151_8_148:Lower true dzo_151_8 roots_151 gzo_151_8 6:=lower_iso_b (d1:=dom_151) (r1:=roots_151) (T1:=gsh_151_8) [(dom_151,8)] (by decide +kernel) (lower_slice_b (T:=gsh_151_8) [(0xaa00aa00000000000000000000000000aa00aa,0,1),(0xcc00cc00000000000000000000000000cc00cc,0,2)] (by decide +kernel) lowS_148)
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xff00fe0000000000fe00fa00000000
def gsh_87_32:=0xff00fe0000000000fe00fa
theorem lowS_zo_87_32_82:Lower true dzo_87_32 roots_87 gzo_87_32 6:=lower_iso_b (d1:=dom_87) (r1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (lower_slice_b (T:=gsh_87_32) [(0xaa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f0,0,4)] (by decide +kernel) lowS_82)
def dzo_215_8:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def gzo_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee00
def gsh_215_8:=0xff00ff0000000000ff00fe0000000000ff00ff0000000000fe00ee
theorem lowS_zo_215_8_148:Lower true dzo_215_8 roots_215 gzo_215_8 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_8) [(dom_215,8)] (by decide +kernel) (lower_slice_b (T:=gsh_215_8) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa00000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000ff00fe0000000000fe00fa
theorem lowS_zo_215_32_82:Lower true dzo_215_32 roots_215 gzo_215_32 7:=lower_iso_b (d1:=dom_215) (r1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (lower_slice_b (T:=gsh_215_32) [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def gzo_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00ff00ff00fe00ee00
def gsh_247_8:=0xff00ff00ff00ff00ff00ff00ff00fe00ff00ff00ff00ff00ff00ff00fe00ee
theorem lowS_zo_247_8_148:Lower true dzo_247_8 roots_247 gzo_247_8 8:=lower_iso_b (d1:=dom_247) (r1:=roots_247) (T1:=gsh_247_8) [(dom_247,8)] (by decide +kernel) (lower_slice_b (T:=gsh_247_8) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,0,2),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,0,32),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,0,64)] (by decide +kernel) lowS_148)
def dzo_182_8:=0x550055005500550000000000000000005500550055005500
def gzo_182_8:=0x550055005500540000000000000000005500550054004400
def gsh_182_8:=0x5500550055005400000000000000000055005500540044
theorem lowS_zo_182_8_148:Lower true dzo_182_8 roots_182 gzo_182_8 6:=lower_iso_b (d1:=dom_182) (r1:=roots_182) (T1:=gsh_182_8) [(dom_182,8)] (by decide +kernel) (lower_slice_b (T:=gsh_182_8) [(0x4400440044004400000000000000000044004400440044,0,2),(0x5500550000000000000000000000000055005500000000,0,32)] (by decide +kernel) lowS_148)
def dzo_223_32:=0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def gzo_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffefffa00000000
def gsh_223_32:=0xffffffff00000000ffffffff00000000fffffffe00000000fffefffa
theorem lowS_zo_223_32_82:Lower true dzo_223_32 roots_223 gzo_223_32 8:=lower_iso_b (d1:=dom_223) (r1:=roots_223) (T1:=gsh_223_32) [(dom_223,32)] (by decide +kernel) (lower_slice_b (T:=gsh_223_32) [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,0,8),(0xffffffff00000000ffffffff00000000000000000000000000000000,0,128)] (by decide +kernel) lowS_82)
def dzo_183_8:=0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def gzo_183_8:=0xff00ff00ff00fe000000000000000000ff00ff00fe00ee00
def gsh_183_8:=0xff00ff00ff00fe000000000000000000ff00ff00fe00ee
theorem lowS_zo_183_8_148:Lower true dzo_183_8 roots_183 gzo_183_8 7:=lower_iso_b (d1:=dom_183) (r1:=roots_183) (T1:=gsh_183_8) [(dom_183,8)] (by decide +kernel) (lower_slice_b (T:=gsh_183_8) [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa,0,1),(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc,0,2),(0xff00ff00000000000000000000000000ff00ff00000000,0,32)] (by decide +kernel) lowS_148)
def dzo_95_32:=0xffffffff00000000ffffffff00000000
def gzo_95_32:=0xfffffffe00000000fffefffa00000000
def gsh_95_32:=0xfffffffe00000000fffefffa
theorem lowS_zo_95_32_82:Lower true dzo_95_32 roots_95 gzo_95_32 7:=lower_iso_b (d1:=dom_95) (r1:=roots_95) (T1:=gsh_95_32) [(dom_95,32)] (by decide +kernel) (lower_slice_b (T:=gsh_95_32) [(0xaaaaaaaa00000000aaaaaaaa,0,1),(0xf0f0f0f000000000f0f0f0f0,0,4),(0xff00ff0000000000ff00ff00,0,8)] (by decide +kernel) lowS_82)
def dzo_181_8:=0x330033003300330000000000000000003300330033003300
def gzo_181_8:=0x330033003300320000000000000000003300330032002200
def gsh_181_8:=0x3300330033003200000000000000000033003300320022
theorem lowS_zo_181_8_148:Lower true dzo_181_8 roots_181 gzo_181_8 6:=lower_iso_b (d1:=dom_181) (r1:=roots_181) (T1:=gsh_181_8) [(dom_181,8)] (by decide +kernel) (lower_slice_b (T:=gsh_181_8) [(0x2200220022002200000000000000000022002200220022,0,1),(0x3300330000000000000000000000000033003300000000,0,32)] (by decide +kernel) lowS_148)
namespace S_255
def pG:List (Nat×Nat):=[(1,9),(1,17),(1,33),(1,65),(1,129),(2,10),(2,18),(2,66),(2,130),(3,11),(3,19),(3,35),(3,67),(3,131),(4,20),(4,36),(4,68),(4,132),(5,13),(5,21),(5,37),(5,69),(5,133),(6,14),(6,22),(6,38),(6,70),(6,134),(7,15),(7,23),(7,39),(7,71),(7,135),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(12,140),(16,17),(16,18),(16,20),(16,80),(16,144),(24,25),(24,26),(24,28),(24,56),(24,88),(24,152),(32,33),(32,36),(32,40),(32,160),(34,35),(34,38),(34,42),(34,50),(34,98),(34,162),(48,49),(48,50),(48,52),(48,56),(48,112),(48,176),(64,65),(64,66),(64,68),(64,72),(64,80),(96,97),(96,98),(96,100),(96,104),(96,112),(96,224),(128,129),(128,130),(128,132),(128,144),(128,160),(136,137),(136,138),(136,140),(136,152),(136,168),(136,200),(192,193),(192,194),(192,196),(192,200),(192,208),(192,224)]
def r1G:=pG.map Prod.fst
def r2G:=pG.map Prod.snd
def mpG:=0x3ffffffffffffffffffffffff
def xsM:=roots_255.map (·&&&dom_255)
def gM:=goal_255&&&dom_255
def NN:Nat→Nat
|7=>9
|8=>155
|9=>521
|10=>518
|11=>136
|12=>11
|13=>1
|_=>0
def HT:Nat→Nat→Nat
|7,0=>0xae2c67e58179df0670c152c5c2c0c628a24170a30dd67
|8,0=>0xa6f51a6045a32059eab29e9c99d1679b44492fde8f17f8cc5389f1e894128789b7b944785f87835a751a17502174b6674897746e6743a171d0371b6f6fa476e5b36cd396ab656a59069b4d6964a647d45f94f5f2595eb085e8da5d2ec5c2b15c1af5b6105a95e5a42c5703255a9a559d554dcb5353c4ef444ade948f83466f345aca450bf44e214478c4444f4412243d9f434e0431a2413d540690400fa3fc3b3e7943d7993cd383be413b7d53b6743b5833b39e38719340283334532fdc3272e31819311fd3052b2d9612d59e2ce8928cf62890c27a3724af5243e121d5e20c741f3671d9bc1d03b1ca071b9ff1b7941abe9194fc189a61895717f6b1772216a53158d7147971475113c9613278121041008e0f1080e8910dc7b0d08f0c91b0c11e0b79a0b5fa0b59b0b2d00b05009d5909a9b0827e044d5022af00f7300aab
|8,1=>0xfa94cf670ef3e31f2234f1489e8371e15e5e11a0db6efcbc86cb1c2c7461c4d16c1c6ebe490bda17bd9eabd4e2bc3b1b9885b8f9fb272baef02acdbfa9397a7269a70b8
|9,0=>0x23d7923871233b6230f822c0922a9c22a012229a220b1217692038c1fac11f4431ed671ea381e2421d1e91cb0a1c7da1c3511bed51bcde1b7d31b59c1b1a01b12f1ab701a46c1a25c19e2b19ddc197c4196ac18870185aa17e2e17b9016b28169ac1589115438152731512e14d2814c7114797141c313f0213ee713d8b13814134b612dad12af912a3e12a1a126f5121d011d4911755116f21168910f5510e4a1076e0fa890f3a10ef730ea820d78a0d5300d34d0cf6d0c8550c79f0bd530ba750b9450b8b80a48f09b230937108ec508ce90887b0858b0839f0839b07cd707c7507ad707991070870699a0676f05ed905930052c604c7b0486d044f3042ba042610407f03d7b03b4c03437033ef033370329202da102b98029e1021750203c0200701d9f01c3e01875011b9010a100faf00d2a00c1b00b4500841007ea001eb
|9,1=>0x4fa794fa724f6f94f2804efe54ee014e00b4d4024c9c54c96a4c0754be8f4ba944aea14aab14a71e4a1c249ed049e9b49afc49a1448dbf48c6d47de846a54467fb4571d454db4545a44dca4318d428964189f411fb410ac40abd3fee43f7f03f16b3e7a63e71c3e55f3e36a3d94a3cd123c5ac3c2f33c1953c1203b8c13b64d3af863af553a7b23a6ce3a60b39da139d4939c57398a83949938ed138ec5387123840f38209380ea380a337b6c36a5d36a3f3557734d4634d1733af6339fd333f432d5c32ad632a9a31b293196331881318193142c30ea430d393044e302382f8ff2f4de2f2c42ed642ec5c2e9952e1222da9d2d7382d44c2d0892cbbc2c3462c0f02b76c2b07429fcf295352943028c8028bb628ad62890c288e127bd627bc9278a8278882745b272e825eb125d1f256b1253a8252af2517a24e8623e4623dd4
|9,2=>0x84e29842b78399682eac8267c8257781c1a81bab811b680dab7efdc7eb727eb147e6c67e58f7dc997d00f7c9917b5e37a89e7a1d279bd37971b790f378e5b78a03787427825c78035756df756d1748b0741ae73e8373dae73a9f73a447316172879721e871e1c7196d6d93f6d39b6d1126cd396cafb6c8e56c5176c0a86c05e6be076bc0f6bbb06a6c06908068f3768b676884967e9e67de967618674066608a65eb46542f6534565269646c063b9a63a0f63831627ea624e1609746064a602e1600c9600155fe385fcb85f7855f39d5f1425eaa65e8435e8245e12c5d3e95d2885c3745be7f5aa755aa445a0aa59baf5987e592495923a588d65843257f7d57a995798d5779856a6255ecb558915565a54e2254c6f54c6a5391653838537aa536e453430533c55277551fdc51edb51d9051d6a51bc751254507be501da4fb3b
|9,3=>0xea517e993de8e07e8d77e681ae5ef8e4a81e383be3820e1734e0596dfdddde179ddfc2dd893dd3a7dc5d3dc31dd9b40d9275d8da6d84b9d637cd4de4d3694d31bbd283fd0d5bd02dfcef19cda86cb3b3ca66cc8b4fc7af9c5401c383cc379fc0c9bc08e4bff04bfeabbea3abe58ebe2a1be0febd4e2bd39bbc7d0bbea4bb94abb4e6bafc1b9c5cb966bb52a6b50e8b46d8b2b23b282eb1a79ad27cac6d0ac651ab7cbaaa57aa111a9dc0a8d16a87f4a8364a7d0ba7a40a62f2a575fa49f8a49bea2fdaa2a63a23e1a1f43a0ffda0df7a0c7ca04f69f9629f91a9f7a89e16d9df3f9d9e59cbc49cb5e9c3749bc4c9b27699edf99ec7998ed98c8598101980529744396ab496845951fa93d25939e59366192f7c9222b921c29138890d018f72b8f6d68f3178ee208e38f8d3878bcae8af9d88ec58850e87dbc87a0186f4d864e8
|9,4=>0xfa0b6f8fcef7f28f670ef6330f2ad6eaf02eadf7eac81
|10,0=>0x1cd7c1cab51c7ad1c69f1c2e81bdd51bc221bb1e1b7701b6b11b5a31b3e51b3c41b3ab1b1c31adf41ac421a63a1a0ea19df8193931935c193491928f1914418f9a18d6b18b70187ed1846717e7b177ea16207161ae151cd14d9814a8014a161451f13b0f136c9133971327612dfc12a1b12672123df12126117cc111801088410870107eb105c7103dc10175100611003b0f6e50f28f0f14f0f1450ee0b0ecbf0e8830e7030e1ad0e1730dc0f0db740da9b0bf0b0be660be020bc780b9450b8c70b66a0b6200b2630b2520a3cf0a00409ac709a380946309288091cd091ad08ebb08eae08c2408611080d307ebb07cd707c28077bd071f60659e0658904e2204db604ba904a150466603da103a0102f5402d67022d3020da01c9b019fb018d201746015a7014cd0101500d5200bd200a65009af00798004890035500253001a0
|10,1=>0x43be3439954253e41d95417944174b411fb40dbf40d0840779402d83fe1b3f2fb3f0403eed53ee5a3ee0c3e36a3e3403d1643ce9b3ccfe3c9e23c5893bf603b6ef3b46d3aef73aa4e39f7438f9838a0c382093814837a0e37405371e8368e436845365c335b1d3523b351fa34d883413e33dfc33cf63364a3303132b76329e0328ba322243219432152312703108e30f2c3043030309300bd2f9f82f5cb2f4072f2142f1052e7002e43c2e2932e1cd2de512dbd12cdb62c93a2c6752c4be2bfee2bf0b2babe2ba622b8302b7cf2b7a22b6df2b52f2b4db2b0532ab0529a032984529653290a0278a82685f267e825a8d259e2258a324a1b24926243bc2432d2425b23e8f238db2381b2222621f9121d8321cfb21be32129c20bfd20aab2074c1fe931f4601f3921f2b11ef471eb1f1e9461e7761e49e1dc5f1d62c1d47e1d307
|10,2=>0x77a857776076f0b76c7176938769257627e74e6274c4f72840720c071f5071afd710fa70ddf709696fdcf6f3286f00d6eefe6e3d66cfee6cecc6cb1f6c6df6c6016c2266beb06b9876b5966b5256b4446ac2669ac968ad0681326811967d616719c6718267148670a966f8d661e7660ad66056654c46534564b6f647df63b2e63808636d8627af625e8613a560be760b1f605f8604c45fe035fc1f5e9565e9145d59d5ce5c5c02a5bca35b22a5ad9c5aa1e5a1805a0765985a58a75587f5583a8571895677d5651c55f76558845538b546f65420a541f353e5053ce953c275385553838532ea527d2524eb5202c51ceb50b9a50597503904fa794f7b44f7654f5044efa54d6114c53e4be3d4b66b4b3ac4a7494a6064936f48e7c48a6f47e52478d847818477f04759f46ec8464d646199455b1455754510444d8e44c7c43c4a
|10,3=>0xefca7edfbbe718ae4106e3820df8b5ddd93dd6d9dd69bdbb13d9ffdd7f88d77fcd74ffd7169d56a1d568ad4a1fd3cf1d3694d27dbd203ad142fcf1a4cee02cda86cb931c92ecc8cd7c857ac6207c5401c535cc517fc4f32c2f08c07bbbff97bf231bc9e3b9a71b9376b86ebb76d6b702bb640fb528cb5182b4ba7b40abb26d0b1e04b0996afe0bac8e8ac49fac344ab74faad34aa8e1a9c63a9ae8a983ba90a4a82ffa763da761ca6f1aa5a91a4f15a4cc5a42a5a0ac89f5979ed599e4c79d74f9d31b9d0c29c0c89b6849af799a60499fb798dab97992979429495a935c592e8c91bf4900808fbaf8db0d8d60a8c7ed8bbbd8b1818ab4289ef289a028869588634885da879ef8703c86dab8578684ed383c3b835518347b825c6821ea811078107e80f217f5677d8e57d3287cde07c2bd7b5077b2747a89e78c3578aa278262
|10,4=>0xf98d7f63dcf5d7ef564ff1423f0275
|11,0=>0xd491ccf279bc5a2ba04eb6b15b0be0b08a3b04cfaf3caac49fabed0a7b29a763da5b27a571aa51fba4cc5a3abea36dca03ff9d9fc99cfb94b289467292990904578ffae8fdf08740685dbb834648320080cac7e1fd7d20a7b4e879cf277e6e76ca5766ab736916fb086e3d66debc6c4d76bd9766f0c667726649d641235ee575badc5b1195a1805925758c9957fb95631b5301652f3051a4a509124d4184c8e34ba7e4b5e64874747d6c468fc44d6d430f14175d3e5753d65f3ce943c91e3c4d53b63238fe6389f63799a35a80355f335291348f533b9133031322b631fd2310302bfee2b8302abf72a213297a62777426bc724a6b217f41f3ed1f2b11d9861d3071c2011bef31b5a318846184571839514d98130ba12a1b10f3d0f41b0c8b809e0809a3609463092f707c2805d8e055e90450602fee01f4c018c400b0800924
|11,1=>0xfff0bf9f7ef5c34ed446e803ddc596db393da8bf
|12,0=>0xfff0b99b3f8fd7c890f1792e461e18518e54ad862fee011d3a0c075
|13,0=>0x64457
|_,_=>0
def dB:Nat→Nat→Nat
|0,0=>0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000fffffffff0f0f0f0fffffffff0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000033333333333333333333333333333333333333333333333333333300333333000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000003333333333333333000000000000000033333300333333000000333300003333000033330000333300003333000033330000330000003300ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|0,1=>0xffffffffffffffff0000000000000000ffffffffffffff00ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0f0f0ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffaaffaaffaaffaaffaaffaaaaaaaaaaffaaffaaffaaffaaffaaffaaaaaaaaaaffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffaaaaaaaaffffffffaaaaaaaaffaaffaaaaaaaaaaffaaffaaaaaaaaaaffffffffccccccccffffffffccccccccffccffccccccccccffccffccccccccccffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffffff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffccffccffccffccffccffccccccccccffccffccffccffccffccffccccccccccffffffff00000000ffffffff00000000ff00ff0000000000ff00ff0000000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000
|0,2=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff0000000000ff00ffffff00ffffff00ffff00000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffff000000000000000000ffffffffffffff000000000000000000ffffffffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff00ffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff0000000000ffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff0000000000ff00ff000000ff00ff00ff0000000000ff00ff000000ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffffffffffffffff00ffffffffffffff00
|0,3=>0xffff0000ff00ffffffffffffffffffffffffffffffff00000000000000000000ffff0000ff00ffffffffffffffffffffffffffffffffffffff00ffffff00ffffff00ffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff005555555555555555555555555555555555555555555555555555555555555500ffaaffaaaaaaaaaaffaaffaaaaaaaaaaffaaffaaaaaaaaaaffaaffaaaaaaaaaa00000000ffffffff00000000ffff000000ff00ffffffffff00ff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffff000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff0000000000000000000000000000000000ffff0000ffff0000ffffffffffffff0000000000000000000000000000000000ffffffffffffffffffffffffffffff00ffffffffffffffffffffffffffffffffff00ff0000000000ff00ff0000000000ffffffffffffffffffffffffffffffffffffffffffffffffff00ff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000
|0,4=>0xffffffffffffffff000000000000ffffffffffffffffffff000000000000ff00ffffff0000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffffffffffffffffffffffffffffffffffff0000000000ffffff000000000000ff00ff0000000000ff00ff000000000000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffff00ffffff0000000000000000000000000000000000ffffffffffffffffffff0000ffff0000ccffccffccccccccccffccffccccccccccccccccccccccccccccccffcccccccc000000000000000000000000000000000000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff000000000000000000000000ff000000000000000000000000000000ff00000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ccccccccccccccccccccccffccccccccccccccccccccccccccccccffccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff0000000000ffffffffffffffffffff0000ffff0000ff00ff00ff00ff00ff000000ff000000
|0,5=>0xff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff000000ff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0f0f0fff0fff0f0f0fff0ffffffffffffffff0000000000000000ffffffffffffffff0000ffff0000ff00000000000000000000000000000000000000ffff0000ff000000ffff0000ff00ffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ff00ffffff00ffffff00ffffff00ffff0000ffffff00ffffff00ffffff00ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000ffffffffffffff00ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffffff00ffffffff00000000ffffffff00000000ffff000000000000ffff000000000000ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff00ff00ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000000000000000000000000000ffff0000000000000000000000000000ff00
|0,6=>0xffffffff00000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffffffffffffffffffffffffffffffffffffff00000000ff00ff00000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffffffffffffffffff00ff0000000000ffffffffffffffffff00ff0000000000ffffffffffffffffffffffffffffffff0000000000000000000000ff0000000000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff00000000000000000000000000000000000000000000000000000000000000ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffff00fff0fff0fff0fff0fff0fff0f0f0f0f0fff0fff0fff0fff0fff0fff0f0f0f0f00000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff0000000000000000000000000000000000000000000000ff00000000000000ff00ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffffffffffffffffffffffffffffff000000000000ff00000000000000ff00ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00ffff0000000000000000000000000000000000000000000000000000000000ff00000000ffffffffffffffff0000000000000000ffffffffffffffff000000ff00000000
|0,7=>0xffffffffffffffffffffffffffff0000ffffffffffffffffffffff00ffff00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0000ffffffffff00ff00ffff0000ff000000ffffffffff00ff00ffff0000ff000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffff0000000000ffffffff00000000ffffffff00000000ffffff0000000000ffffff000000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ff00ffffffff00000000ffffffff00000000ffffffff00000000ffffff0000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000ffffffff00ff00ffffffffff00ff00ffffff000000ff0000ffff000000ff00000000000000000000ffffffffffffffff0000000000000000ffffff00ffffff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffffff00ffff0000ffffff00ffffffffffffffffff00ff00ff00ff00ffffffff00000000ff00ff0000000000ffffffffffffffffffffffff00000000ffffffffffffffffff00ff0000000000
|0,8=>0xff00ffffffffff00ff00ffffffffff00ff0000ffff000000ff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffff000000ff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff0000ffffffffffffffffffffffffffffffff00ff00ff0000000000ff00ff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fff0ffffffffffff0000ff00ff00ff000000ffffffffffff0000ff00ff00ff000000ffffffffffff0000ffffffffffff0000ff00ff00ff000000ff00ff00ff000000000000000000000000000000ff00ff00000000000000000000000000ff00ff00ffffffffffffffffffffffff00ff00ffffff0000ffff0000ffff000000ff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffff0000000000ffff000000ff00ffffff000000000000ffff000000ff00ffffff0000ffffffffffffffffffffffff00000000ffffff00ffffff00ffffff0000000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000ff000000ff000000ffff0000ffff0000ff000000ff000000ffff0000ffff00ffccffccccccccccffccffccccccccccffccffccccccccccffccffcccccccccc0000000000000000ff00ff00ff00ff000000000000000000ffffffffffffff00
|0,9=>0xffffffffff00ff00ffffffff00000000ffffffffff00ff00ffffffff0000ff0000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000000000ffffff0000000000ffffff0000000000ffffff0000000000ffffff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffff0000ffffff00ffffff00ffffffffffffffffffffff00ffffff00ffffffffffffff0000000000000000000000ffff0000ff0000000000000000000000ffff0000ff00ffffffffffffffffffffffffffff0000ffffff00ffffff00ffffff00ffff0000ffffffffffffffffffffff00ffff0000ffffffffffffffffffffff00ffff000000000000000000000000ffff0000ffff00000000000000000000ffff00000000ffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff00000000ff0000ff0000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000ffffffffffffffffffff00ffffff0000ffffffffffffffffffff00ffffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00000000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ff000000ff00ffffffffffffffff0000000000ff00ffffff0000ffff00000000000000ff0000
|0,10=>0xffffffff00000000ffffffff0000000000ff00ff0000000000ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffff0000ffffffffffffffffffff00ffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff00ffffffffffffffffffffffffffffffff00000000000000000000ff000000ff00000000000000000000000000000000000000ffff0000ffff0000ffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000000000ff00ff00ff00ff00ff000000ff000000ff00ffffffffff00ff0000ffff0000ffffffffffffffff0000ffff00000000ffffffffffffffff0000ffff0000000000000000000000000000ffff0000000000000000000000000000ffff00000000ffffffffffffffffffffffffffffffffffffffffffffffff0000ffff00000000ffffffffffffffffffffffffff00ff00ffff0000ffff0000ffff0000ff000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000ff000000ff000000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000
|0,11=>0xff00ffffff00ff00ff00ffffff00ff00ffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffff00000000000000000000000000000000000000000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffff00000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ffffffffffffffffffffffffffffffff0000000000ff00ff0000000000ff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000ff000000ff0000ff00ff0000000000ff00ff00000000ffffffff00000000ffff00ff000000000000000000000000000000000000000000ff00ffff00ff0000ff00ffff00ff00ffffffffffffffffffffffffffffffff00000000ff00ff0000000000ff00ff000000000000000000000000000000000000000000ffffffff00000000ffffff00ff00ff0000000000ff00ffff00000000ff00ff0000000000ff00ffff0000000000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ffccffccccccccccffccffffccccccccffccffccccccccccffccffffccccccccff00ff00ff00ff00ff00ffffff00ffffff00ff00ff00ff00ff00ffffff00ff0000000000ff00ff0000000000ff00ff0000ff00ffff00ff0000ff00ffff00ff00
|0,12=>0xffffffff00000000ffffffff00000000ffffffff00000000ffff00ff000000000000000000000000000000000000000000000000ff00ff0000000000ff00ff000000000000000000ffff0000ffff00000000000000000000ffff0000ffffff00ffffffffffffffffffff00ffffff00ffffffffff00000000ffff00ff00000000ffffffffffffffff0000ffff0000ff00ffffffffffffffff0000ffff0000ff00000000000000000000000000000000000000ffff000000000000ffff00000000ffffffffffffffff0000000000000000ffffffffffffffff0000ffff0000000000000000000000000000000000000000ffffff00ffffff00ffffff00ffffff0000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000ff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff0000ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00ff00ffffff00ff00000000ff00000000000000ff00000000000000ff00000000000000ff00000000
|0,13=>0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffffff00ffffffffffffffff0000ff000000ff00ffffffffffffffff0000ff000000ff00ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff00000000ff00ff0000ff0000ff00ff0000ff0000ff00ff0000ff0000ff00ff0000ff0000000000000000000000000000000000ffffffffffff0000ffffffffffff000000000000000000000000000000000000000000000000000000ff00ff00ff0000ffffffffffffffff000000ff00000000ffffffffffffffff000000ff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fff0f0f0fff00000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000ffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff00000000000000000000ffffffff000000000000000000000000ffffffff00000000ffffffffffffffffffffffffffffffffffffff00ffffff00ffffffffffffff000000000000000000000000000000000000000000000000000000ff000000ff00
|0,14=>0xffffffffffffffffff00ff00ff00ff00ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff00ffffff000000ff00ff00ff00ff00ffffff00ffffff00ff00ff0000000000ffffff000000000000000000000000000000000000000000ff00ff0000000000ff00ff00000000ffff0000ffff0000ffff0000ffff0000ffff00ffffff0000ffff00ffffff0000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000ffff0000ffff0000ffff00ffffff00ffffff0000ffff0000ffff00ffffff000000000000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffffffffffff00000000ffffffffffffffffffffffff00000000ff00ff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ffff0000ffff0000ffff0000ffff0000ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffffffffff00ff00ffffffffff00ff000000000000000000ffff0000ffff00000000000000000000ffffffffffffff000000000000000000ffffffff00000000ff00ff00ff00ff00ffffffffff00ff00ffff0000ffff0000ffffffffffff0000ffffff00ffffff00ffffffffffffff00
|0,15=>0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff000000000000ff00ff00ff00ff00ff00ffffffffff00ff000000ff000000ff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffffff0000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff0000ffffff00ffffff00ffffff0000000000ffffff00ffffff00ffffff00000000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff0000ffffffff00000000ffffffff00000000ff00ff0000000000ff00ffff00000000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff000000ff0000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff0000000000ffffffff00000000ffffffff0000ff00ffffffff00000000ffffffff0000ff00ffffffffffffffffffffffffffffffffffffffff00000000ffffffff0000ff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff000000ffffffff00000000ffffffff00000000000000000000000000ff00ff00000000
|1,0=>0xffffffffffffffffffff0000ffff0000ffffffff00000000ffff000000000000ffffffffffffffffffffff00ffffff00ffffffffff00ff00ffffff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffff0000ff00ff00ff00000000ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffff0000ffffffff00000000ffffffff0000000000000000000000000000ffff00000000ffffffffccccccccffffffffccccccccccccccccccccccccccccffffcccccccc00000000000000000000000000000000ffffff0000000000ffffff0000000000ffffffffff00ff00ffffffffff00ff00ffffffff00000000ffffffff0000ff00ffffffffff00ff00ffffffffff00ff00ffffffffffffffffffffffffffffff00ffff0000ffff0000ffff0000ffff0000ffffff00ffffff00ffffff00ffffff00ffff000000000000ffff000000000000ffffff0000000000ffffff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff0000ff00ffffffffffffffffffffffffffffffffffffff00ffff0000ffffff00ffff00000000000000000000ffffff00ffffff000000000000000000ffffff00ffffff00000000000000000000000000ffffff00000000000000000000000000ffffff00
|1,1=>0xffffff00ffffff00ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffff000000ffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffff00ffffff00ffffff000000000000ffff00ff000000000000000000000000ffffffff00000000000000000000000000ff00ff00000000ffffffffffffffff0000000000000000ffffffffffffffffff00ff00ff00ff00ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffff00ffffff0000ffffffffffffffffffffffffffff0000ffffffffffffffffff00ff00ff000000000000000000000000000000000000000000ffff0000ffff0000ff000000ff00ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffff00ffffff00ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000ff00ff0000000000ff00ff0000000000ff00ffff00000000ff00ffff00000000ffffffffffffffffff00ff00ff00ff00ffff0000ffffffffff000000ff00ff0000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00000000ffffffffffff0000ffffffffffff0000ffffffffffffff00ffffffffffffff00
|1,2=>0xffffffffffff0000ff00ff00ff00ff00ffffffffffffff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffff00000000ffffffffff00ff00ffffffff00000000ffffffffff00ff0000000000ff00ff00ffffffffffffffff00000000ff00ff00ffff0000ffffff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffff0000ff000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffff0000ff000000ffffffffffffffff00000000ff00ff00ffffffffffffffff00000000ff00ff000000000000000000ffffffff00ff00000000000000000000ffffffff00ff0000000000ff00000000000000ff00000000ff00ffffff00ff00ff00ffffff00ff00ffffffffffffffffffffffffffffffff00000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00ffffff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00000000000000ff00ff00ff00ff00ff00000000000000ff000000000000000000ffffffffffff00000000000000000000ffffffffffff0000ffffffffff00ff00ffffffff0000ff00ffffffffff00ff00ffffffff0000ff00
|1,3=>0xffffffff00ff00ffffff000000ff0000ffffffff00ff00ffffff000000ff0000ffffffffffffffffffffffffffffffffffffffff00ff00ffffff000000ff00000000000000000000ffffffffffff0000000000000000000000ff00ff00ff0000ffffffffffffffffffffffffffffffff0000000000000000ffffff00ffffff00ffffffff00000000000000ff00000000ffffffff00000000000000ff00000000ffffffffffffffffffffffffffffffffffffffff00000000000000ff00000000ffffffffffffffffffffffff00ff00ffffffffffffffffffffff000000ff00000000ff000000ff00000000000000ff000000ff000000ff00000000000000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffff0000000000000000000000000000000000ffff0000ffff0000ffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ffffff00ffffffffffffff00000000000000ffff000000000000ffff000000000000ffff000000000000ff0000ff00ffffffffff00ff00ffffffffff00ff00ffff00ff0000ff00ffff00ff0000000000000000000000ffff0000ffff00000000000000000000ff000000ff00ffffffffffffffff0000ffff0000ffffffffffffffffffff0000ff000000ff00
|1,4=>0xff000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff00ffff0000ffff0000ffff00ffffff0000ffff0000ffff0000ffff00ffffff0000ffffffffffffffffff00ff00ff000000ffffffffffffffffff00ff00ff00000000ff00ffffffffff00ff0000ffff000000ff00ffffffffff00ff0000ffff0000ffffffffffffffffffffffffffffffff00ff00ffffffffff00ff0000ffff0000ffffffffffffffffffffff00ffffff00ffffffff00000000ffffff0000000000ffffffffffffffffffffffffffff0000ffffffffff00ff00ffffffffff000000ffffffffffff0000ffffffffffff0000000000000000000000ff00ff00ff0000000000000000000000000000000000000000ff000000ff000000ff000000ff00ffffffff00000000ffffffff00000000ffffffff0000ff00ffffffff0000ff00ffffffff00000000ffffffff00000000ffffffffff00ff00ffffffffff00ff00ffffffffffffffff0000000000000000ffffffffffffffffffffff00ffffff00ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffff00ffffffffffffffffffff0000ffff000000ff00ff00ff00ff00ff000000ff0000ffffffffffffffffffffffffffff0000ffffffff00ff00ffffffffff00ff0000ff00ff00ffffffffff000000ffff0000ff00ff00ffffffffff000000ffff0000
|1,5=>0xffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff000000000000000000000000000000000000ffff00ffffff0000ffff00ffffff000000000000000000000000ff000000ff0000000000ff00ff000000ff00ff00ff000000000000000000000000000000000000000000000000000000ffff00000000ccccccccccccccccccccccccccccccccccccccccccccccccccccffffccccccccffffffffff00ff000000000000000000ffffffffff00ff000000ffff0000ff00000000000000000000ff00ff00000000000000000000000000ff00ff00000000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff000000000000ff00ff00000000000000000000000000ff00ff00000000000000ff00ffffffff00000000ffffffff00000000ffffff0000000000ffffff000000000000000000000000000000000000000000000000000000000000000000ff00ff00ffffffffffffffffffffffffffff000000ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffffffffffffffffff00ff0000000000ff00ffff00000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00ffffffff00000000ffffffff00000000ffffffff00ff00ffffffffff00ff0000ffff0000ffff0000ffffff00ffffff00ffff0000ffff0000ffffff00ffffff00
|1,6=>0xffffffffffffffff0000000000000000ffffffffffffffff000000000000ff00ffffffffffffffffffff0000ffff0000ffffffff00ff00ffffff000000ff0000ffffffffffffffffffffffffffffffffffff0000ffffffffffff0000ffffff00ffffffffff00ff00ffffffffff000000ffffffffff00ff00ffffffffff000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff00ffffff0000ff000000ff000000ff000000ff000000ff000000ff00ff00ff000000ff00ff00ffffffffffffffffff000000ff000000ffffffffffffffffff000000ff00ff00ffffffffffffffffff00ff0000000000ffffffffffffffffff00ffff0000000000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00ffffffff00000000ffffffff00ff00ffffff000000000000ffff000000ff0000ffffff00ffffff00ffffff00ffffff00ffffff0000000000ffffff000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ffffffffffffffffffffffffffffffffffff0000ffff0000ffffff00ffffff00000000000000ffff000000000000ffff000000000000ff00000000000000ff00ff00ff00ff00ff00ff00ffffff00ffffff00ff0000000000ff00ffff00000000
|1,7=>0xff000000ff000000ff0000000000000000ffffff0000000000ffffff00ff00ff00ffffff00ff00ff00ffffff0000ff00ffffff000000ff00ffffff000000ff00ffffff000000ff00ffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff000000ff00ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff0000ff00ff0000000000ffffff0000000000ff00ff0000000000ffffff00000000ffffffffffffffffffffffffffffffff00ff00ff0000000000ffffff000000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff00ffffffffffffffffffffffffffffffff00ff00ffff00ff0000ff00ffff00ff0000000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ff00ff00ffffffffff00ff00ffffffffff00ff00ffffff00ff00ff00ffffff00ffffffffffffffffffffffff00000000ffff0000ffff0000ffff000000000000ffffffffffffffffffffffffffffffffffff0000ffffff00ffff0000ffffff00ffffffff00000000ffffff0000000000ffffffff00000000ffffff0000000000ffffffffffffffffffffffffffffffffffffffff00000000ffffff0000000000
|1,8=>0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff000000ffff0000ffff0000ffffff00ffff0000ffff0000ffff0000ffffff00ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff000000ff00ff00ffff000000000000ffffff0000000000ffff000000000000ffffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffff00ff00ffffff00ffffffffffffffff0000000000000000ffffffffffffffff00000000ff00ff00ffffffff0000000000ff00ff00000000ffffffff0000000000ff00ff00000000ffffffffffffffffffffffffffffffffffffffff0000000000ff00ff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fff0f0f0fff0f0f0fff0f0f0fff0000000000000ff00000000000000ff00000000000000ff00000000000000ff000000000000000000ffffffffffffffff0000000000000000ffff0000ffffff00ffffff00ffffff00ffffffffffffff00ffffff00ffffff00ffffffffffffff0000000000000000000000000000000000ffffff00ffffff00ffffffffffffff00
|1,9=>0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffff0000ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffff0000ff000000ff00ffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff000000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000ffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00ffffff00ffffffffffffffffff00ff00ffffffffffff0000ffff0000ff000000ffff00000000000000000000ffffffffffffffff0000000000000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffffffffffffffff0000ffff000000000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000ffffffffffffff00ffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffff00ff00ff00ffffff00ff000000000000000000ffffffff00ff00ff0000000000000000ffff000000ff0000000000000000000000000000000000000000000000000000ffffffffff00ff00ffffffffffffffffffffff0000000000ffffffffffffffffffffff0000000000
|1,10=>0xffffff00ffffff00ffffff00ffffff00ffffff00ffff0000ffffff00ffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000ffffff00000000000000000000000000ffffff0000000000ffffffffffffffffffffffffffffffff0000000000000000ffffff00000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffff000000000000000000ffffffff000000000000000000000000ffffffffffffff00ffffffffffffffffffffffffffffffff00000000000000000000ffff00000000ffffffff00000000ffff00ff00000000ffffffff00000000ffff00ff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffff00ff000000000000000000000000ffffffff000000000000000000000000ffffffffff00ff00ffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff0000000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ffffff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000ff000000ff00
|1,11=>0xffffffffffffffffffffffffffffffff00000000ffffff0000000000ffffff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffffffff00ff00ffff00ff00000000ffff00ff00000000ffff00ff00000000ffff00ff0000000000000000000000000000000000000000ffffffff0000ff00ffffffff0000ff00ffffffffffffffffffffffffffffffff0000ffff000000000000ffff00000000ffffffffffffffffffffffffffffffffff00ff00ff00ff0000000000ff00ff00ffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff00000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000ff00ffffff00ff000000ffff00000000ff00ffffff00ff00ffffffffffffffffffffff00ffffff00ffffffffffff0000ffffff00ffff00000000000000000000ff00ff00ff00ff00ffffffff00000000ffffffffff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffff00ffffff0000000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffffff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffff000000000000ff00ff0000000000ff00ff000000ff00ff00ff000000ff00ff00ff000000000000000000ffffff00ffffff000000000000000000ffffff0000000000
|1,12=>0xccccccccccccccccccccffffccccccccccccccccccccccccccccffffccccccccffffffffffffffffff00ffffff00ff00ffffffffffffffffff00ffffff00ff0000ff0000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff0000ffffffff000000000000000000000000ffffffff000000000000ffff000000000000000000000000ffffffffffffffff0000000000000000ff00ff00ff00ff00ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffff00ffffff00ffffffffffffffffffffffffffffffff0000ff000000ff000000ff000000ff00ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffff00000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000ffffffffffffffffffffffffffffffffff00ff00ff000000ff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ffffffff00000000ffffffff00000000ffffffff0000000000ff00ff000000000000000000ff00ff0000000000ff00ff0000000000ff00000000000000ff0000ffff0000ffffff00ffff0000ffffff00ffff0000ffffff00ffff0000ffffff0000ff000000ff000000ff000000ff000000ff00ff00ff000000ff00ff00ff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffffff00ff00
|1,13=>0xffff0000ffffff00ffff0000ffffff0000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffffffff00000000ffffffff00000000ffffffffffffffffffffffffff00ff00ffffff00ffffff0000000000ffffff00ffffff00ffffff0000000000ffffff00ff00ffffff00ffffff00ffffff00ffffff00ffffff00ff00ff00ffffff00ff00ffffffffffffffffffffffffffffffff000000ff00000000000000ff00000000ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ffffffffffffffffffffffffffffffffff000000ff00ff00ff000000ff00ff000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00ffff00ffffff00ffffff00ffffff00ffffff00ff00000000ffff00ff00000000ffffffffffffffffffffffff0000000000ff00ff00ff00ff00ff00ff000000000000000000000000ff000000ff00ff000000000000000000ff000000ff00ff00ffffffffffffffff00ff00ff00000000ffffffffffffffff00ff00ff00000000ffffff00ffffff00ffffff00ffffff0000000000ffffff0000000000ffffff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffff00ff00ffffffffff00ff000000000000000000ff00ff00ff00ff000000000000000000ffffffffff00ff00
|1,14=>0xffffffffffffffffffffff00ffffff00ffff0000ffffffffffff0000ffffffffff000000ff00ff00ff000000ff00ff00ffffffffffffffff00ff00ff00ff00ffffffffff0000000000ff00ff000000000000000000000000ffffffffffffffff0000000000000000ffffffffff00ff00ffffffffffffffffffffffffffffffff0000000000000000ff00ff00ff00ff000000ff000000ff000000ff000000ff00000000000000ff00000000000000ff00ffffffffffffffffff00ff00ff00ff00ffff0000ffff0000ff000000ff000000ffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff00ffffff0000ffffffffffffffffff000000ff00ff00ffffffffffffffffff000000ff00ff0000ff000000ff000000ff00ff00ff000000ff000000ff000000ff00ff00ff00000000ff000000ff000000ffff0000ff000000ff000000ff000000ffff0000ff000000000000000000ffffff00ffff00000000000000000000ffffff00ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000ffffffffff00ff00ffffffffff00ff00ffffffffff000000ffffffffff000000ffffffffffff0000ffffffffffffff00ffffffffffff0000ffffffffffffff00ffffffffffffffff0000000000000000ffffffffffffffffffffffffffff0000
|1,15=>0xffffffffffffffffffffffffffffffffff00ffffff00ff00ff00ffffff00ff00ffffffff00ff00ffffffffff00ff0000ffffffff00ff00ffffffffff00ff0000ffff000000000000ffff00ff00000000ffff000000000000ffff00ff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffffffffff0000000000000000ffffffffff00ff000000000000000000000000000000ff000000000000000000000000000000ff000000ffff0000ffff0000ffff0000ffff0000ff000000ff000000ff000000ff00ffff000000000000ffff000000000000ffff00ff00000000ffff00ff00000000ffffffff00000000ffffffff00000000000000ff00000000000000ff00000000000000000000ffff000000000000ff00000000000000ffff000000000000ff000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000ff00ffffff00ffffff00ffffff00ff00ff00ffffff00ffffff00ffffff00ff00ffffffffffffffff0000000000000000ffffffffffffffffffffffff000000000000000000000000ff00ff00ff00ff00000000000000000000000000ff00ff0000000000000000000000000000000000ff00ff00ff00ff00ffffffffff00ff00ffffffff00000000ffffffffffffff00ffffffff00000000ffffffffffffff00
|2,0=>0xff00ff00ff000000ff00ff00ff000000ffffffffffffffffffffffffffffffff000000000000000000ff00ff0000000000000000000000000000000000000000ffffffffffffffffffffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffff00ff00ffffffff00000000ffffffff00000000ffff00ff00000000ffff00ff000000000000000000000000ffff00ff000000000000000000000000ffff00ff0000000000000000000000000000000000000000ffff0000ffff0000ffffff00ffffff000000ff000000ff00ffffffff0000ff000000ff000000ff00ffffffff0000ff00ffffffff00ff00ffffffffff00ff00ffffffffff00ff0000ffffffff00ff000000ff0000ffffff0000ff0000ffffff0000ff0000ffffff0000ff0000ffffff00ffffffff00000000ffff000000000000ffffffff00000000ffff000000000000ffffffffffffffffffffffffffffffffffffffff00000000ffff000000000000ffff0000ffff0000ffff0000ffffff00ffff0000ffff0000ffff0000ffffff00ffffffffffffffffffffffffffffffff000000000000000000000000ff00ff0000000000000000000000000000000000ff00ff00ff00ff0000000000ff00ff00ffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00000000
|2,1=>0xffffffff000000000000000000000000ffff000000000000ffffffff00000000ffffff0000000000ffffffff00000000ffffff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000ff00ff00ffffffffffffffffffffffffffffffffffff00ffffff0000ffff00ffffff0000ffffffffffffffffffffffffffffffff00ff00ff00ff000000ff00ff00ff0000ffff0000ffffffffffff0000ffffffffffff0000ffffff00ffff0000ffffff00ffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00000000ffffffffffff0000ffffffffffff0000ffff00ffffff0000ffff00ffffff0000ff00ff00ffffffffff00ff00ffffffffff000000ffff0000ff000000ffff0000ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000ff00ff00ffffff00ffffff00ffffff00ffffff00ffff0000ffffff00ffff0000ffffff00000000000000000000ff00ff00ff00ff000000000000000000ff000000ff0000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffff00ff0000ff000000ff000000ff0000ffff000000ff000000ff000000ff0000ffff00000000ffff000000000000ffff0000ff000000ffff000000000000ffff0000ff000000000000000000000000000000000000000000ffffff0000000000ffffff00
|2,2=>0xffff0000ffff0000ffffffffffffff00ffff0000ffff0000ffffffffffffff0000ff00ff0000000000ff00ff0000000000ffffff0000000000ffffff00000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000ff00000000000000ff00ff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00ffffffffffffff00ffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff0000000000ff00ffffffffff00ff00ffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffff00ffff0000ffffff00ffff000000000000ffffffff000000000000000000ff00ffffffffff0000000000000000
|_,_=>0
def sP:Nat→Nat
|0=>0xc0c0a40b05c0403408000070500b064280100d00007098250100d00c0c0002301c0b0140400c0a02000084070400b01404034030301f01c0602c050100d00c000741407005034030300801c150500b064040340c03c1002c160140400c0c01c1502c190100d030180400b05c040340c03c0b0580501003030070541402c13010030300f02c0e0140d00c0c01c0b01403028090200001c060140400c0200400
|1=>0x100d00c3b000070400b014040343902000074140e0050100d0300801c0b01404034030dc0c0d0070500b01404034030203301c1002c050100d00c0c01c26040310100d00c0001c2402c300100d00c080002201c26040050100d00c0c01c0b0b8050100d00c0c01c1402c19014040340c0b0070180b0140403403000180400b04804034030300b0100d00c2b030080000702c130a80400c0001c1002c1601404
|2=>0x201d02c190a0040340001c1002c050100d00c4f0001d134050100d00c0c0200702c050104900c08000070180b0140410c030200001c26040310c8040340303c1002c0e0140d00c080000f02c160140400c08000070500b01404034031180801c1002c050104300c0c0004202c1701404034080600b104040340303007098400100d00c0c01c1402c050100d00c3e020070f40b01404034030200001c2604005
|3=>0x74260380d00c08000070985f0100d00c0c0001a02c110100d00c51030071780b01404034030200001c0b16c05034030200001c2602c1301003030000601002c170100d0200001c1402c050100d00c580200715c0b044040340303007098100700d00c0c0001d098320100d00c0801c0602c0503403158080005401c1402c050100d00c080685202c050100d00c0c0685202c280100d00c00074320100d00c51
|4=>0x1003028010200001c0602c050100d00c6b0201d050051b00403403030070540b0640403408000070400b01404034031ac0c0500b0100d00c6a0300801c68018050100d00c080001d098320100d00c0c0201d09867034030200001c10014040340319808000260e00403451020000600b064040340c000070180b014040340318c0801c57044040340303007188100140403403030070180b014040340318000
|5=>0xc750001d098190100d020000180b0100d00c6a0200001c72050050100d00c0c0200702c1117c04034030301d098710100d00c080001a02c0e0140d00c0c07c070400b01404034030000f01c0b0140400c0a02000074261c004034030001d0986e0100d00c080000f0400b05805010030200002c380100d1440c0200001c100140d00c091b4080000702c0503403158080001d098311b004034030000705005
|6=>0x3403020000988101003144080008001c1002c050100d00c0001c060140400c0a1d408000071fc6201404034030301d01c140140400c0a0200001c0602c05034031f808000070540b06c04034030300702c7d04404034030302201c0602c05034030240802c170100d1440800007050050100d00c7a0200003c7902c050100d00c08000070180b0140d00c091e0080747701404034030300801c76018050100d
|7=>0x20070500b04c28010030000702c05034031f808000070500b0140d00c560200001c0602c0522c0d00c080001a0988a0100d00c000680b0580501003030070541402c190100d020000f02622404034030200702c8701404034030308601c06014040340302000074260100d00c850200001c8402c050100d00c0c01c1002c0503403158080000709804034032080c00007188050100d00c0c020071c80601404
|8=>0xac950200001c060140d00c0925008000070400b0140d00c7e02000074260700d00c0c0200001c0b0100d00c9224408000072101402c050100d00c0c0601402c380100d03008074140146e0100d00c0801c0b01404034032400c0740b04c28010030001d014040340323c0c020070541402c1b0100d00c0c01c1002c050100d00c8e0001d098310100d00c08000070500b04c05010030301d02c160140400c0c
|9=>0x100d00c6a0300801c0602c050100d0e4080009b01c1001404034030200001c4402c050340302408000070180b01404034030f80801c1002c050100d00c3e030070540b04c0400c08000072640b014040340303007098980c404034030000702c0503403024080008601c10014040340302000074260e0040340c020000600602c380100d0200001c2602c190100d0300025807050050100d00c080000403403
|10=>0x20000601002c380100d0200001c0b014040340329808000070400b014040340328c0001c0b288050100d00c080000702c050100d00c590300802c120100d00c510200027c0702c050100d00c0800004034030ac510200002c04034030ac0800007018050100d00c66020000a40b0e0040340c020000600602c04034031a8080000702c050100d0e408000290e004034510200001c0b064110100d030180500b
|11=>0x20000601a0500b01404034030303a01c1402c050100d00c080000702cb10140403403020000600b0100d00cb00200001cad02c050100d00c080001d098a70100d00c080003c02c17014040340801c0b1dc050100d00c0c0201802c170100d0200001c0b0140403403198080001d014040340323c080000715c110100d00c080003c01c0b01404034032a808088070400b01404034030300702ca80140403403
|12=>0x1a02c0522804034030003c02c052240403403020070400b01404034031ac080000f01c2617c0403403020000a41e0100d00c510200001cb802c050100d00c08000070980b0580400c08000070400b044a70100d00c0802c04034031a8b7020000740b014040340321408000070400b01404034032d80c088070180b01404034030201d02c2806c04034030000702c050100d00cb50200001c0b2c80501003
|13=>0x100d00cc70200001c7602c050100d00c080000702c04034030ac0800007098100c80403403020290980b2040400c080000702c050100d00cc5020000a42602c6c0100d00c000740b014c40100d00c08000070400b01404034030ec0001cc20400b01404034030200001c2602cbf0100d00c08000072f80b0140403403020002f00702c050100d00c080001d050051b004034030200001c0b01404034032e808
|14=>0xc730300702c050100d00cda0200001c1002c050100d00cd900007018050100d00c750200001c1402c050100d00cd80200001c0602c050100d00c610200001c1402c0535c0d00c080000702cd501404034030ec08000d101c0b01404034030200001ccf02c050100d00c08000073340b01404034030200001ccc0400b01404034030200001c1002c050100d00ccb000070500b0a0050100d00cc9000073200b
|15=>0x100d00c080740b014040340339c080000702c0517404034030200001c0b0140403403398080000702ce50140403403020003880702c050100d00c08000e001c0b01404034030200007406050050100d00c73020000f00737c0b01404034030200003c0702c050100d00cde0005501c150500b0140403403020293480b2b804034030200001c0b0100d00cdc020000680b03805034030200001c1002c110100d
|16=>0x2c050100d00c08000f302c04034031a808000f101c0b0140403403020000a40b078040340303008000073b80b0140403403020000a40b0100d00c6a0200001c0b0380503403030080d4070500b0140403403030071780602c050100d00c080000702c050100d00ced0200001ceb02c050100d00c0c020070f40b01404034030200001ce902c050100d00c08000070546201404034030200019007054c802c05
|17=>0x300801c0b01404034034000c000070980b3fc04034030200001c0b01404034033f808000073f40b01404034030200001c1002c050100d00cfb020003d40702c050100d00c0c000073e80b01404034030300002cf801404034030200002c04034031a8950200001c0b3dc050100d00c080000702c1117c04034030200001c0b01404034031e8080001a02c053d80403403000180d40b0e00403408000f401c10
|18=>0x100d00c0c020000600b0100d00c6a03008000d301c262b804034030200001c0b01404428030200001c4402c050100d00c97020000600b06c040340303000075090140403403020000740b014310100d00c080010801c0b01404034030200041c0702c050100d00c08000070980b3100403403020000750501404034030200001c0b0140403403410080010301c0602c050100d00c08000074080b0140403403
|19=>0x1d80b0140403403020002580702c050100d00c750200001c0b014040340344408000070540b06c040340302000074d2320050100d00c080000702c7d044040340302000440d202c050100d00c080001a02c050100d00cc00300003c0b01404034033a008000074380b01404034030200001c0b0150d0100d00c08000070400b014120100d00c0c0740b044a70100d00c0801c0b01404034034300800007098dd
|20=>0x200001c0b490050100d00c080003c01c0b015230100d00c084852002c050100d00c080011e01c0b01404034030200001d1c02c050100d00c08000074640b014040340302000074260c804034030200702c0546004034030200001c1402c280140400c0a0200001d16050050100d00c0800007454050100d00c0c0200007514098050100d00c080001d44c050100d00c080000702c0544804034030200019007
|21=>0x302301c1002c0503403024080001d050051bc04034030200001c1002cb10140403403020000f0070400b01404034033780001d2c02c050100d00c080001d02c053d80403403020004ac1802c380100d0200001c0b4a4050100d00c080001d49c0b01404034030200001c57050050100d00c080001d02c050c4320100d00c080f0071c81001404034030200001c2602d260100d00c08000071fc620140403403
|22=>0x2c050100d00c0801c150500b0140400c0a020004d00702c050100d00c080001d0986c0100d00c080000702c050100d00d330200003d2101c2601404034030002301c1001404034031b408000071780b0140403403020000600b0100d00d320200001c1002c050100d00d300012f01c0b0140403403020004b4070500b01404034030300b0100d00c742740c0200002c380100d144080000702c051040403403
|23=>0x2c050100d00c08000074f01002c050100d00c0001c8402c050100d00c08000070900b01404034030200001c0b0140410c030200001c0b01404034034e8080001d050050780403403030080f00702c0503403024080000702d3901404034030200001c1402ca801404034030200001c0b354050100d00c08000070500b01404034031640c020d34dc0b0140403403020004d80702c050100d00c0c020db01c06
|24=>0x34030200050c0702c050100d00c080001a02c160140400c080014101c0b01404034030200001c0b21c050100d00c080000702c04034033f0ab020000742606c04034030200001c0b19c05034030300001c2650004034030200001c1402c050100d00c650300801c0b4f8050100d00c080004702c04034031a8080001d02c1c0140d00c0c020000601002c04034031a8080000702c050100d00d3d0200040c07
|25=>0x3fc04034030200702c050100d00d4b02000080073201402c050100d00c08068070980b3bc0403403000070988a0100d00c08000075280b0140403403020005240702c050100d00c08000071780b014320100d00c0801c0b014040340352008000070540b014040340303008518070500b0140403403030080b00702c050100d00c0c0000702cae0100d00cfc020000a41d02c380100d020005143c0400b01404
|26=>0x2c050100d00c080001d02c050100d00cc60200001c260100d00d4f0200001c3d0500b0140403403020000751402c110140403403020f501c1002c050100d00c0c000070500b0146e0100d00c0801c1002c170140403408000070500b014311b0040340301d4e040050100d00c08000070400b01404034033b00c01c0b014040340323c0c0200702c0553404034030300001c2602c310c804034030200702c05
|27=>0x70980b0700d00c0c0200001d4e050050100d00c080000702c050100d00d57020000755601404034030200001c6802c050100d00c080001d02c38014040340c0200001c0b0140403403550080000702d5301404034030200002c050100d00d520200001c0602c050100d00c590200008c2201c0602c050100d00c085440b0140403403020000680b01404034033c00001d50040050100d00c0c000f501c06
|28=>0x2c050100d00c4f0200001c0b580050100d00c08000075780b01404034030300801c0b014040340357408000070400b014320100d00c0c01c0602c050115b00c08000070500b04c05010030200001c9802c050c40403403000070180b014040340319408000070500b0146c0100d00c0001cfd0500b01404034030200003c1002c050100d00ce80200001c0b0140403403568080000709810014040340325c08
|29=>0xc3f0200001c0b598050100d00c080001d0996501404034030200001c0b0140403403590080001d02c04034030ac080002201c1402c050100d00c0801c0602c050c804034030200f01d0601404034030200002c0403403279630200001d6202c050100d00c080002c01c1002c050100d00c00518070180b01404034030200001c0b064050100d0300001c0b04c28010030006401c2402c050100d00c0800007
|30=>0x200001d6d02c050100d00c080001a1880b014040340302000074073201401404034030201d01c2653404034030200001c5e02c050c46c0100d00c0001c150500b06c0403403020005b03c02c050100d00c08000075ac0b014040340302000190070540b01404034030300801c0b015690100d00c080000702d6801404034030200001c1001404034031d4080001a02c530a0050100d00c0001c0602c050100d
|31=>0x100d00c0800026078040340314408000070180b0157a0100d00c080000702c050100d00d780200001c0b0140403403118080000b0100d00d761a808000d202d7401404034030200001c0b5cc050100d00c0c01d7202c050100d00c0c020075c00b01404034030200001c6202c050100d00c0c0200702d2a01404034030300801c0b01404034035bc080000f484070981001404034030000702d6e0140403403
|32=>0x340303000074140700503403020000740b04c05010030200001c0b5f804034030200048407418050100d00c080001d02c051b004034030000702c050100d00c900200001c8d0180b0140403403020000740b05c050100d0200001c1002c050104300c0800007098981b004034030001d01c263bc040340302000074260100d00d7d0200001c0b0157c0100d00c0800007050050100d00c750200001c0b0157b
|33=>0x100d00c080009601c0b0140403403020002f03c02c050100d00c0800007098100100d00c8c020001500702c050100d00c08000070180b01404034032a80801d8202c050100d00c080002d01c0602c050100d00c080000b07804034031440c020006000702c050100d00c08000070400b01404034032a80c01c0b44c050100d00c0c0200702c050100d00d7f0200002c04034031a851020000b4070400b01404
|34=>0xbc0c01c0b01404034030fc0800007098100700d00c080000f01c1001404034031b4080000b0100d00c2b274080002902c1b0100d00c080000b0100d00cc73a0080000702c2a06c04034030003601c0b01404034030200001c2602c0403403614080000702c050115b00c080010301c1402c050100d00c08000070500b01584034030300801c6201404034030300801c0b014040340318c0c020072101402c05
|35=>0x1c2602c13010030200001c2602c6c0100d00c000740b0146c0100d00c0c0001d0503801404034080003c01c2620c04034030200001c2602c170100d020000a41802c380100d020000758b01404034030200001d8902c050100d00c080000702d880140403403020000740b014040340361c08000070900602c050100302808000070500b014ff0100d00c0801c0b0140403403160080001a01c0b0140403403
|36=>0x20000740b01404034032d80c0208601c0b01404034030200034c07018050100d00c08000076400b01404034030300001c1002c050100d00d640200001c8d02c050100d00c080000f01c262b804034030200034c07040050100d00c0c0000763c0b01404034030200008c070900b01404034030200001c0602c050100d00ca50001d5cc050100d00c0800007634050100d00c08000070540b630040340302000
|37=>0x3480b01404034030200001c1402c050c404034030201a02c05048040340303007098890100d00c080001d02c053fc04034030201a01c1502c050100d00c0c01c1002c050100d00c3e0200001c1502d930100d00c080000702d9201404034030200002c04034031a80c020000f0073340b01404034030200001c0403403278510200001c9902c050100d00c080001d134050100d00c08000070180b0158403403
|38=>0x30000740701404034030bc0c020070400b01404034033f00c000074180b0100d00cc70200001c0b668050100d00c08000e401c0b01404034030300801c0b0a00566404034030200001d720500b014040340303008074260700d00c080001802c04034030ac080009b01c0b01404034030200001d9702c050100d00c08000070980b1b004034030300001c0b01404034036540c0740b04404034031cc0c02194
|39=>0x34030200001c1402c050100d00da00301002c04034031a8080000702d9f01404034030200001d9e018050100d00c08000070500b01404034035fc080001d068260a004034030003c01d010400b01404034030002902c04034030ac08000220f00702c050100d00c0801c0602c050100d00cfc0200001d5f050050100d00c0c020070400b0140403403674006700702c050100d00c08000070980b06c0403403
|40=>0x14040340302000074260e004034080001a02c050100d00c510300001c0602c050100d00da30200001c5e02c050c404034030200001c98454050100d00c0c0000702c051b00403403688004853702c050100d00c08000070180b0140d00c090200001c0b684050100d00c08000070980b3fc040340302007098100100d00c74030000601402c1b0100d00c08000070400b01404034030fc080008001c0b01404
|41=>0x340302000074071d81401404034030200001c8d0400b01404034030200001c0602c050100d00da80201d01c1501404034030300801da602c050100d00c080001402c04034031d073030085b00702c050100d00c0c000075c80602c050100d00c08000070500b07005034030300801c1402c0563004034030300807407098040340353c080000702c1904404034080003601c1402c050100d00c08001a401c0b
|42=>0x2c0503403024080001a01c150500b0140403403030070500b01404034032a80801c0602c050c00403403020000680b14c050100d00c0c01c1002c1c0140d00c0c000070500b0e0050100d0300801c1402c670140d00c08000070980403403208080003502c04034031a80800007098830100d00c0c00007098101b00403403001a901c0b0140403403020000e8070180b01404034030200007c070500b01404
|43=>0x98280100d00c080002101c1002c050100d00c08000180500b07804034030300801d7202c050100d00c08000076bc1001404034030200001c0b0140403403238080003c01c0b01404034034940803c070900b0140403403020004dc0702c110100d00c0c0200602c04034031d0730200001dac02c050100d00c08000070180b0700503403020006a80702c050100d00c08000070180b0158c0100d00c0800007
|44=>0x74070901401404034030200003c0709810014040340303000074d2098ae0100d00c08000180680b0440403403030076981002c050100d00c080001d06814014040340303007188050100d00c080000702c2e0140403403020000f01002c050480403403020070180b0e0050100d0200001db002c050100d00c080003a01c0b014040340302000060070500b0140403403030080600b0e00403451020000743c
|45=>0x27408001b201c1001404034030200001c7f02c051c00403403000070980b19c0d00c08000070900601404034031d4080001801c0602c050100d00c080001d02c051c404034030200001d15050050100d00c0c0200717915014040340302000074260780403403030080001802c410100d00c08000180180b0780403403020000a40b0e004034080000702c280100d00db10200003c0709806014040340302000
|46=>0xc0001d6502c050100d00c0800007098830100d00c08000076d80b0140403403020000680b044040340314408000d301d0601404034030200002c04034030ac0800007454060140403403020006d40702c050100d00c0c01c0b01404034036cc080000702c050100d00da2020000685202c050100d00c080001802c380100d03008000070400b0140400c0a0200001c1002c0503403024080000b0100d00c9e
|47=>0x2c1e0100d00c08001be01c1402c050100d00c08000070980b1bc04034030200001dbd02c050100d00c0c020000740b01404034031cc0c020006f00702c050100d00c080003c01c0b01404034032ac080000702c1101404034036ec0801c0b01404034036e808000074181401404034030200036c0702c280140403403020006e40702c2801404034030200001c0b6dc050100d00c08000071110102c050100d
|48=>0x1c0b0440403403020070400b0700503403020000743501c0b01404034030200001c2602c0403403564080000702c050100d00dc1020000680702d1a0140403403000070980b0440403403030080740702c110140403403030087000702c050100d00c08000070500b014040340345c080000702c050100d00dbf0200001c0b01404034034e0080000702c38014040340c0200001c0b01404034033240800029
|49=>0x100d00c080001801c0b044040340302000650070980b01404034030200048407098050100d00c08000070500b014040340351c0c0200702c050100d00dc3020000740b0100d00c9e1cc08000070990102c050100d00c0c0000702c280140403403230080001d02c050480403403020000400b0100d00c741cc08000bc01c0b0140403403020000a40702c050100d00c0800007098050100d00c27020000603c
|50=>0x20000f00702c0520c0403403020000a4070140403403144080000702c050100d00c7b020004d40702c050100d00c08000071d80b0140403403020006500702c050100d00c08000070400b01404034033b008000075380b01404034030200001d0102c050100d00c0c0000702c2a01404034031d4080000702c050100d00dc40200001c0b0a0050100d00dbb0200001c0b0100d00c746b80c02000060d202cae
|51=>0x2c050100d00c08000070500b0a0050100d00d590200011c3501c0b0140403403000070500b070050340302000060070181002c050100d00c080001802c1e0100d00c0c0200001c1402c0563004034030200001c150500b0a0050100d00c080000702c050100d00dc70200001c0b015c60100d00c08000070500b014040340331c0800007098dd0100d00c080001802c04034031a808001b901c140140403403
|52=>0xf00b014040340302007454050100d00c080000702c050100d00d8502000720070400b01404034030200007407054050100d00c080000f01c0b014ae0100d00c080002901c0b04404034030200001c0b0145f0100d00c08001450f00b0140403403020000740b014040340359c080018101c0b01404034030200001c26454050100d00c080000f01c0b01404034032ac08000075400b01404034030300035007
|53=>0xc080000701404034037340c0200001c0b014040340325c08000076602602c050100d00c080005501c2602c050100d00c080003c01c26040050100d00c080001801c0b0140403403030080000702c050100d00dcc0200001da702c050100d00c080000702c050100d00cf00200001dca02c050100d00c080000702c053c804034030200001c0b01404034037240c0203c01c440400b014040340302000074db
|54=>0x7400702c050100d00c08000070400b01404034034c408000070500b64c050100d00c080000702c170140403408000074540b014040340303008000070400b0140473c030200001c2602d1a0100d00c080000702dce01404034030200001c0b304ae0100d00c080001d01c0b468050100d00c08000070400b0e0050100d02000068070500b0a0050100d00c001540702c050100d00c08000070400b014320100d
|55=>0x30080000702c050100d00dd5020000600702c0403403278080000702c130140400c08000180680b2b804034030200001c0b1f4050100d00c08000070900602c050100d00c080000702c057500403403020000681402c050100d00c740200001c0b0146c0100d00c0001c0b01404034032200c0009c01c0b01404034030200002c04034031d09d0200001c0b0100d00dd36b8080000702c050100d00dd202000
|56=>0x1c1402c050100d00c74030081080702c1101404034030200702c050100d00c9e0200001c0602c050100d00d47020000f00702c050100d00d1d0200001dd602c050100d00c080003c01c0b01404034032cc080000702c0522404034030200001c0b01404034031d408000070980b04804034030200001c0b014040340342c080013701c0b01404034030200002c050100d00db8220080002901c0b0140403403
|57=>0x340377008000230f00702c050100d00c080000702c050100d00dda0200001c1002c050100d00c9a0200001c26040ae0100d00c080012101c0b014ae0100d00c08000073200b01404034031d008000074041002c050100d00c0001c0b76c050100d00c08000070980b0140403403768080000702c0576004034030200001c1402c050100d00cca0300801d8b02c050100d00c080000702c050100d00dd702000
|58=>0x100d00c08000070400b0140403403114080000702c050100d00c2f0300801c261340b01404034030200001d150140403403030080013701c0b04404034030200001c0b0140403403778080000f4840702c050100d00c0001c0b5cc050100d00c08000180400b0780403403020000740b0700503403020007740702c050100d00c080002901c0b0100d00c9e0200003c070981001404034030200001c0b01404
|59=>0x200001ddf02c050100d00c080004701c0b014040340302000060071280b01404034030200001d0102c2801404034030001801c0b01404034030bc080001801c1002c050100d00c080000702cae0100d00cb30200001c0b015230100d00c08000071340b0140403403020000740b0140403403274080001d01d0601404034030200003c0702c050100d00c73020000f00702c050100d00c6d020000740770805
|60=>0x1404034030200001c4b02c050100d00c08000070400b01404034032a808001e001c0b0140403403020000741401404034031cc08000d301c0b01404034034e0080001d0680b0a0050100d00c0001c0b014040340361c080001d6580b01404034030300801c153201402c050100d00c0801c264041001404034030000702c050100d00dd3030000f0070400b01404034032ac080002001c150500b0140403403
|61=>0x3403020007440702c050100d00c080001d0984e01404034030200001c1402c050100d00dc9020070180b014040340334008000070980b0100d00c8c020004dc0702c050100d00c0c0200001c1002c050100d00c740300001d02454050100d00c080000702c810140400c0c020000740702c0522804034030200001c0b0146c0100d00c0c0000702c050100d00da0020007840702c050100d00c08001453480b
|62=>0xd301c0b044050100d00c080001d098050100d00c9d020000740b0e0050100d020000740b014320100d00c08000070180b014040340332808000077900b0140403403020000f0077080b01404034030200001c0b014040340328c08000070180b01404034031d0080001801c1002c110100d00c080000702c050100d00c9e03008000d202c050100d00ce8020007880702c050100d00c080001d0f02601404
|63=>0x200001c0b01404034030ec080001d1080b01404034030200001c0b01404034032ac0c001d101c0b044040340302000604d301c0b01404034030200001de802c050100d00c080000702c0579c04034030200001c0b0140403403798080001a01c0b01404034030bc08000070980b0700d00c08000070980b0100d00cc70200001c0b014040340379408000070900b01404034030200001c0b0141b0100d00c0c
|64=>0x702c053fc04034030200702c050100d00ccb0200001d4e02c28014040340302000060070540b01404034030200001c1402c050100d00c7b0200001c760500b01404034030200001c2602deb0100d00c08000070980b0100d00cec0200001c9802c050100d00c080000702c050100d00dea0200001c0b015e90100d00c08000070540b01404034030300801d15040050100d00c08000180d40b0780403403
|65=>0xc000682602c04034031d0080001a02c050100d00ce80200001c0b01404034036c4080000702c110100d00c73030080f00702c050100d00cbd0200001c0b014040340336408000076600b044050100d00c0801c0b015ee0100d00c080000702c050100d00ded02000068070980b0a004034030000702c117640403403020005141a02c050100d00c080000b01404034033009d020007b00702c050100d00c08
|66=>0x20070980b0c804034030200001c0b01404034037c8080000702c050100d00d42020000601a02c050100d00c0c001f101c0b0140403403020004840702c050100d00d830200001c0b0100d00d596b8080000702c110100d00dae030084841a01c0b01404034030000702c0520c0403403030000f0070400b01404034031cc08001f001c0b01404034030200001def02c050100d00c08000070400b0146c0100d
|67=>0x140403403020000695f02c050100d00c080012b0600b07804034030200001c440180b01404034030200001c26040050100d00c0c0000702df401404034030200001c1002c050100d00cc30200001c1402c051b00403403000230f0070400b014040340302000068070540b01404034030200001d7102c050100d00c080000702c050100d00cd00200001c0b0a0050100d00dd30006401c1402c050100d00c0c
|68=>0x2c050100d00c08000070400b01404034032bc080000702c050100d00d950200001c0b044040340358c08000071480b01404034030200001df802c050100d00c08000073200b01404034037dc080000b0780403403144080000702c050100d00df602000074070992e0100d00c080001a02c0504804034030200001d4402c050100d00c08000075880b01404034030200001c0b0140403403170080001d34826
|69=>0x100d00cc0020000743c02c280140403403020000680702c050100d00c6d0200001c0b014040340380008000e301c0b01404034030300801c0b7fc050100d00c08001fe01c0b01404034030200001c0b014040340314408000077f40b0140403403020007f00702c050100d00c08001fb01c0b01404034030200001c0b01404034037e8080000747c0b0140403403020000680b01404034035d4080000734906
|70=>0x2c050100d00c080000702c110100d00c510200002c110100d00db81cc080001d6600b0140403403020004ac3c01c1002c050100d00c08000290740b07804034030200001c060400b01404034031d0080000702c050100d00d220200011c070500b0140403403020000f0070980b4b804034030200001c2602dc50100d00c08001d101c1002c050100d00c080002303c070400b01404034030200001c2602cae
|71=>0x2b80403403274080000702c050100d00c590200002c050100d00db83a0080000702c050100d00e01020000753702c050100d00c080000702c050100d00d00020003d40702c050100d00c080000f0f00702c050100d00c0800007098050100d00c510200001c0b01404034034c0080001d02c051b004034030001d0682601404034030200001c1402c050100d00da00200001c240400b0140403403020000604e
|72=>0x100d00c08000070901402c050100d00c080020701c0b01404034030200001c0b014040340319408000070980b0100d00e060200001c0b810050100d00c080001d3480b014ae0100d00c08000291380b0140403403020000600b06c04034030200001e0302c050100d00c080001801c1402c2801404034030200001c0b1dc050100d00c080000702c050100d00e02020000752101c2601404034030200001c0b
|73=>0x100d00c0c0200b0100d00c6a0200001c0b0140403403554080000782c0b01404034030200001c1002c110140403403030078280b0140403403020000740b0141e0100d00c0c020005180702c050100d00c080001d01c26454050100d00c080000702c050100d00c51030080001a02c050100d00cc00200001c4402c050100d00c08000078240b01404034030200001c1402c050100d00d28020008200702c05
|74=>0x70980b1b00403403000070980b014040340384008000180d41a02c050100d00c002b00702c050100d00c080003c01c0b0140403403724084b40702c050100d00c0c000070400b014a70100d00c080000702c0583c04034030200001c0b0a0050100d00e0e020008300702c050100d00c080000702c0403403231ae020000f00702c050100d00c2702000060070541402c050100d00c08000070541402c05
|75=>0x680702c050100d00d28000070500b0140403403340080000702c050100d00e14020000680b14c050100d00c080021301c0b01404034030200001c263200b0100d00c740200001c050100d00e120200001c260181001404034030200001c4a02c050100d00c740200002c050100d00db859c080003501c0b0a0050100d00c0001c0b0140403403844080019101c0b01404034030200001c0b014040340384008
|76=>0x1c2602cae0100d00c08000293480b01404034030200001c0b0158e0100d00c08000070980b0100d00caf0200001daf02c050100d00c080000702c050100d00e190200001e1802c050100d00c08000070540602c050100d00c080001a01c0b0a004034036b80001c0b016170100d00c080002d01c0b01404034030200001c0b19c05034030200001e1502c050100d00c080001a01c150500b014040340302000
|77=>0x2d0050100d00c080000702c050100d00d61020004841801c0b01404034030200001c0b014710100d00c080001d01c0b01404034034a008000078700b01404034030200001c0b014040340386c080001a01c2602cae0100d00c080001d4841a02c050100d00c0001e1a02c050100d00c08000074080b014320100d00c0801c0b0146e0100d00c08000070500b01404034036ec0801c0b014311b0040340300029
|78=>0x14040340387c080012101c0b044050100d00c08000070540b014040340302000518070500b0140403403020000a52101c0b01404034030200001c0b0158403403020000601a02c110100d00c080001d050050780403403020000a41802c1e0100d00c080000702c050100d00e1e0200001c0b0140403403874080000702cc10440403403020000741a050050100d00c080001a02c2801404034036e00001c0b
|79=>0x3007456210140403403020005140702c050100d00c08000070500b014040340374c080000702c050100d00e20000076780b01404034030200001c2602ca70100d00c080003c01c0b04404034031cc0801c0b014040340323c080004202c050100d00db80200001c0b2fc050100d00c080000702c050100d00ca9020000d40702c050100d00c08000076580b0152e0100d00c0c0f00b014120100d00c0801c0b
|80=>0x1d09d020006d40702c050100d00c08000075780b01404034030200001c1402c0506c04034030200001c0b01404034037e40c0203c01c0b0a004034036b8080000702c05374040340303008000070500b0140403403618080001a02c050100d00c9e020001900702c280140403403020000b4070400b014040340302000060070400b2b80403403020000740702c2a01404034030200001d960400b0140403403
|81=>0x100d00c080001d0981e0100d00c080012101c1002c050100d00c0007407540050100d00c08000070980b72c04034030200001d7202c050100d00c080000702c050100d00d8303008000071880b01404034030200001d0502c050100d00c080000702c050100d00d250200001c0b014040340388c08000070400b014040340302222190070540b01404034030200001c0b014ff0100d00c080000b0140403403
|82=>0x1404034033a8080001d02c050100d00e160200001c2602c040340374c080000702c050c40403403020000600b0e004034080000702c0562804034030200001c0b01404034038980800007188050100d00c08000d301c1401404034030200001c0b014040340389408000077080b0140403403030080000702d1301404034030200001c0b014040340366c080001801c1402c050100d00c0c022244840702c05
|83=>0x1d073030080001a01c0b044050100d00c0c0600b078040340314408000e301c0b044050100d00c0889c0702c050100d00c080001d01c260140403403030080001801c0602c050100d00c08000070500b0141e0100d00c0c0203c01c0b015eb0100d00c083480b014040340314408000e101c0b0140403403020000d4070500b01404034030200001c1402c050100d00d59020000680b0146f0100d00c0001c0b
|84=>0xc080002901c0b01404034030200007407050050100d00c080002901c2602c050100d00c08000074540b01404034030200001c050100d00dcd0200001c0b0140403403358080001d01c0b01404034031cc080003c01c0b0152e0100d00c080000702c0571404034030200001d720500b01404034030200001dc2040050100d00c080000702c0510404034030200001c0602c0507804034030200002c0403403
|85=>0x2c051b00403403000076600b01404034030200003c070400b0140403403020007cc0702c050100d00c080001801c0b0140403403030080003c01c0b0a0050100d00c0800007454050100d00c080001a01c0b0140403403220080001d01c0b014040340360c080001a01c2602c050100d00c080003c01c0b044050100d00c0801c2602c110140403403020000600702c110100d00c080003c01c1002c050100d
|86=>0x1404034030200001c0b01404034032bc080001d36c0702c050100d00c080000702c0578c0403403020000743c02c050100d00c080000702c050780403403030080000702c050100d00cc30200001cd202c052b80403403020000f00702c050100d00dae0200001c0b0140403403278080000702c050100d00df9020004dc0702c050100d00c080000702c810140400c080003c01c0b01404034031cc0800007
|87=>0x1c0b015d90100d00c080000702c050100d00d280200001c1002c110140403403020004ac3c01c0b0140403403020000600702c280140403403020000f00702c050100d00cce0200001cc802c050100d00c080001a01c0b014ae0100d00c08001d101c0b01404034030200001c263200b01404034030200001c1402c050100d00c0c020073481402c050100d00c080004701c0b014040340302000060070400b
|88=>0x34030200001c0b014a70100d00c08000076582602c050100d00c08000070180b014040340302000074d202c050100d00c080000702c050100d00db803008000180d40702c050100d00c080000702c28044050100d00c08000073480b01404034036b808000070400b0141e0100d00c080000702c280100d00dae020000743c01c0b01404034030200001c0b0152e0100d00c0c0000702c050100d00d4702000
|89=>0x740b0141e0100d00c08000075400b01404034030200001c0b0140403403144080000b01404034036e073020000741a02c050100d00c080012b0600702c050100d00c08000074040b01404034030200001c0b0152e0100d00db80200001c0b0140403403328080000702c2a0140403403020000680702c050100d00dae020000680702c050100d00c730200001c1502c1101404034030200003c1d01c0b01404
|90=>0x70980b014040340303008000076581002c050100d00c08000070181002c050100d00c08000070500b014040340351c08000071100b01404034030200001d9602c054b80403403020001083c01c0b01404034030200001c440980b01404034030200001c0b015cb0100d00c080000702c050100d00c74030080000702c050100d00c88020004ac0702c110140403403020000741801c0b014040340302000
|91=>0x2c0520c04034030200001c4a02c050100d00c080000702c050100d00c2f0200034c0702c050100d00c08000070500b014040340332808000070500b01404034031d008000183480b01404034030200001c0b0141b0100d00c080000702c050100d00d86020000740702c050100d00c9e0200001c1002c050100d00c740200001c0b0146c0100d00c080000702c050100d00dc90200001c0b014040340374c08
|92=>0x100d00c73020000600702c110140403403020000d40702c050100d00c080000702c050100d00d590200001c0b044050100d00c0c0200702c050100d00cb30200001c1502c050100d00c08000071100b0a0050100d00c08000290600702c050100d00c080000702c053740403403020001081a01c0b01404034030200001c440400b0140403403020000759602c050100d00c080000702c050100d00c0888807
|93=>0x2b804034030200002c04034031d073020000f0070980b01404034030200001c261380b01404034030200001c0b01404034036ec080001d01c2601404034030200001dc202c050100d00c080000702d1a0140403403020000680702c1101404034030200001c2602c04034031d0080000702c050100d00ce80200001c0b014040340360c080000702c110100d00dae020005140702c050100d00c080000702c11
|94=>0x2c2801404034030200001c1002c050100d00c080000702c052b804034030200001c0b014040340303008000070980b01404034030200001c0b01404034031d008000076580b01404034030200001c0b01404034036e0080000702c0507804034030200001c0b044050100d00c080001801c0b0140403403020000600b0780403403020000600702c050100d00c510200001c0b0e0050100d020000740702c05
|95=>0x1c0b0140403403020000600702c050100d00c0800007
|_=>0
def sO:Nat→Nat→Nat
|7,0=>0x3c800d2002d70099c01f7005e00107002200008
|8,0=>0x91e423f808e1c22f908a1c221708624211708260200907e5c1f1807a601e09076201d08072201bf906de01af806a1c19f9065a418e8061a017f705e1c16f9059e015f8055a414e80516413d804d2412b90491c11d70459c10d9041240fb903ca40ea8038a00d99034240c8802fe40b6902ba00a6802764095802360086701fa0077701be00678017a40559013240448
|8,1=>0x11664450911220440810e20431710a604209105e440f8101e03ff80fde03ef80f9a43dd90f59c3cf70f1a43bf70ede03ae90e9a039e80e56438d80e16037c90dd5c36c90d8e435b80d4a434990d06033980cc2432970c82431790c3a430680bf642f670bba02e590b7602d580b39c2c590af242b570ab602a490a72029390a2e0283809ea4271909a602618096242508
|8,2=>0x53a714cdc52a9148a051991446050a7140dc4fa913c644e89137e44d69133644c5812f604b5812b604a4912720494812320483911f1c473911aa44628
|9,0=>0x1dae476291d62874ea1d16473ba1cca472991c824716a1c364703a1bea46f191ba606e181b6606d091b2206bf91ada46aca1a8e469a91a464688919fe4677819be0665a197246548192e4643818ea4632818a646209185e460f8181a45fe817d645eba178a45da8174645c981709c5b9916c9c5a9916860599816424587915fa4576815b645649156e45529152a05419
|9,1=>0x269a499d92652498c8260e497a925c64968925820956a253a0946824f64934924ae49229246a09119241e88fe923d648ec9238e48da9234288c7922fa48b6822ba08a59227248939222e0883821e68871821a2485f9215a484e8211a083d920ce882a9208648189203e480691ff287f391faa47e191f6247cf91f1a47bca1eca87a991e7e879691e3a078681df647749
|9,2=>0x2f9e4bde92f5a0bcd92f124bbb92eca4ba8a2e7e4b95a2e324b8392dea4b70a2d9e4b5f82d5a4b4d92d0e8b3a92cca0b2992c824b1792c3a4b0772bfe0af5a2bb24ae2a2b628acf92b1a4abe82ad64aac92a8e4a9a92a428a87929fa4a75929b24a639296a4a51929224a41728e24a2ea28964a1c9284e4a0b8280a49f8a27ba89e59277249d39272a49c1926e249af9
|9,3=>0x389a4e1ca384a8e09937fe8df6937b64de4937720dd39372a4dc1936e24db08369a8d9ca36520d8c8360e4d79a35c24d688357a8d559352e8d42934e64d309349e4d1e934564d0c9340e4cfb833ca4ce8a337e4cd78333a4cc5932f24cb3932aa4ca0a325e4c8e9321a0c7ca31ce4c6b8318a4c59931424c48831020c38830ba8c25930760c149302e4c0292fe64bf09
|9,4=>0x4192105b9414e104a941029038840be50278407a501684036500493fee4ff383fa68fe093f5e4fcf83f1a4fbe83ed64fac93e8e4f9a93e464f87a3dfa4f7593db24f6393d6a4f50a3d1a8f3d93cd24f2aa3c864f1893c3e4f0693bf28ef393baa4ee193b660ed093b1e4ebe93ada0ead93a924e9aa3a4a0e8b73a068e78939be4e66939764e549392e4e42938e64e2fa
|9,5=>0x4a62128f94a1e127e949d6526c9498e525a949429247948fa5235948b25222a48665211848261200947e211f08479e51df8475a51ce8471a11be846d651ac9468e5199a46425187945fa5175945b61163a456e11538452e1143844ea5131944a6111fa445a510e8441650fba43ca50e99438250d79433a50c5942ee90b2942a650a09425e508e9421a107ca41d2106c8
|9,6=>0x535a54cd9531254bb952c694a89527a9495952361483a51ea5473751aa5460a515a944d95112543b950ca54299508614189503e5405a4ff253f394fae13e294f6653cfa4f1e13bda4ed613ac94e8a939994e42538794dfa537594dae936294d66535094d1a933ca4cd5d32d84c92531b94c4a530a84c0652f894bbe52e784b7e12d784b3a52c4a4aee52b294aaa12a0a
|9,7=>0x5c5e170e95c1656fd85bd256eb95b8e16d9a5b3e96c695af656b495aae56a385a6a569375a2a5680a59da966ca598e565b859469649859061638958be56269587656149582a9602857e655efa579a55dd9575255cb9570a55b8a56be55a69567655949562e5581a55e6156fa559a555ca5552154b9550a5539954c61529854861519854425506a53f294f2a53a294df9
|9,8=>0x176495d6e575295d2dd74295cea173195ca2571f9
|10,0=>0x66ced9aa966865997a663e1987865fa5974a65ae59629656659509651e593da64d2592b9648699189643a9904a63ee58f2963a298df9635698cc9630e58b9a62be98a69627658949622e5882961e658709619a985d96152584b9610a5838a60be5825a607258139602a580195fe617efa5f9a57dca5f4a97c995efe97b695eb657a495e6a9790a5e1e577e95dd6576d8
|10,1=>0x701e5bfda6fd25beb96f8e1bda96f465bc7a6efa5bb4a6eb21ba396e6a5b9286e265b8096dde5b6da6d8e9b5b86d469b4896cfe5b3696cb65b23a6c6a5b10a6c1e5afda6bd25aeb96b869ad7a6b369ac3a6aea5ab196aa25a9f96a5a5a8d96a0ada79969c61a689697a9a559692e9a42968e65a309689e5a1e968565a0ba680a59f9967bad9e59677259d1b672259bea
|10,2=>0x797a5e559792e9e42978e65e309789a9e1d978525e09b77faddf5977b25de2a77665dcfa77169dbc976ce5daa976865d989763a9d84a75ee5d71a75a25d5ea75565d4c9750e5d3a974c65d28974821d179743a5d04a73ee5cf1a73a25cdea73565ccba73069cb8972be5ca5a72725c92a72265c80971da9c6d971925c5aa71429c47970f69c34970ae5c22970665c109
|10,3=>0x82b260a39826a609198222607f981de206e98192a05aa8142a046a80f66034980ae60229806660109801e5ffe97fd65fec97f8e5fda97f429fc797efa5fb597eae9fa387e6a5f9197e225f7f97dd69f6c97d921f5b97d469f4897cfa9f3597cae9f21a7c5e9f0e97c165efc97bce5eea97b865ed7a7b3a5ec4a7aea9eb197aa25e9ea7a565e8c97a0e5e7a979c65e67a
|10,4=>0x8beaa2f0a8b9aa2dd98b5262cb98b0a62b998ac262a798a7a629598a326283989e6a26fa899a625d98952624b98906a239888c262279887a6215988326203987ea61f1987a261dea875661cc9870aa1b9986bae1a4a866e619298626617fa85da616d98592615b9854a6148a84fe6136984b6612498466e1109841e60fe983d660ec9838e60da98342a0c7982fa60b59
|10,5=>0x954a6549994fea536994b2a5239946a6510a9416e4fba93d1e4eb9938a64d99934264c6a92f664b3a92a6a4a09925e648e99212a47b991c6a4689917e6456991366443a90ea6432890a6641eb9056640c9900aa3f998fc263e798f7a63d598f3263c398ee6a3b098e9e639f88e5a638ca8e0aa37998dc2636798d7a6353b8d2a633fb8cda632ca8c8aa31998c3ea304b
|10,6=>0x9e72679399e2a678289de6676fa9d9a675ca9d4aa74a89d06673899cbe672699c76671499c2e670299be666f099b9aa6dd99b4ea6ca99b0666b7a9aba66a599a72669399a2a6681999dea66e99996665c9994e664a999066637a98ba66259987266148982e6600b97de65eda979265db9974a65c8a970225b6a96b2a5a39966a659199622657f995de256da9592655b9
|10,7=>0xa7a669e09a75e69cdaa70ea9b9aa6c269a79a67a6994aa62aa9828a5e669709a59e695e9a55de94e9a516693d8a4d2692b9a486a9189a43e6905aa3eea8f38a3aa68e19a36268cf9a316a8bc9a2ce68aa9a28668989a23aa8859a1f268739a1aa6860aa15e684daa10ea839aa0c26826aa072a812aa022a7ff99fda67ed99f8ea7db89f4a67c999f0267b799eba67a59
|10,8=>0xa882aa179a83a6a04aa7ee69f29
|11,0=>0xb1f2ac739b1a6ac609b15e6c4dab10eac39ab0beac25ab0726c12ab0266c009afde6bee9af92abdaaaf42abc6aaef66bb3aaeaa6ba0aae5e6b8daae126b7aaadc66b67aad7a6b559ad2eab429ace2ab2eaac966b1c9ac4e6b0b8ac06aaf98abc26ae6aab766ad3aab26aac18aadeaaadaaa8eaa9a9aa42aa879a9f6aa749a9ae6a61aa9626a508a91e6a3daa8ceaa2a9
|11,1=>0xbb566ecc9bb0e6eba9bac2aea79ba7a6e959ba326e839b9ea6e70ab99e6e5e9b9566e4c9b90e6e39ab8beae269b872ae12ab8266e018b7e26def9b79a6ddd9b74eadc9ab7026db79b6ba6da4ab66aad919b6226d7f9b5d6ad6bab586ad57ab53a6d44ab4eaad30ab49e6d1dab4526d0aab402acf79b3ba6ce59b3726cd39b326acc09b2daacad9b2926c9aab242ac86a
|11,2=>0xbc7a6f168bc32af048bbeaaef28bba2aedea
|12,0=>0x2f819bde26f6f9bd9a6f5d9bd526f4b9bd0a6f399bcc26f279
|13,0=>0x2f8a8
|_,_=>0
def wAt:=mkWire dB 552 256 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def SS:=mkSS wAt sP sO 10 18
def SD (s j:Nat):=(SS s j).map (fun w=>(w,projBit r1G w,projBit r2G w))
def hAt (s i:Nat):=fld (HT s (i/128)) 20 (i%128)
def idxH (s h:Nat):=bsr (hAt s) h 11 0 (NN s)
def idx (s:Nat) (zs:List Nat):=idxH s (hk 0 zs)
def oP:Nat→Nat
|0=>0x480d40002101c110050010740541200d02c074070440140040502102c0041b00d0141a0070210140b40509f0000840704202c0840601d0900dc060150400040b0210880540704102c084200230500841501d0141440b0010780440501c02c0040002102c074070210140041b00d0680500505101c0840002102c0040800101c0540b02104803407044014004080010480d41001d02c08407044014004070210480441101c01c104050010200040b021
|1=>0x50084050510f010c070010e803c18019040004070150200040b0010780340501c02c0740002104012c0b02101c110050010d800c3505102c004180230140741804102c0840501d0c80841e0010140700b02102c0540b01503c00c070410200041a0bf01c0840505202c0040002102c0041b00d0141a0070210b408c0f01501c1040b0210440700b0210140040800101c0542907b01c050070990200040b0150440840500106c0d40506801c0840b021
|2=>0x141a0070211400841103f0140040704102c0840b01d0200044e00101c2600b0150344c40712f1280541000302c0840b0210140b432021078004070140480441001d02c08407044014004120350400740b02101c11005001120004470530600840501d02c00408001034454071130400540b0210f00841200d01c004070440140041a044014004070210000840501d044100000210140040b02102c0543f00106006c140210140740b00105423007019
|3=>0x400740b02102c054050010600bc070210000840501d1740440517301807c1402102c0040502d06c0d4080010141a00702101c0540b021048034070440140045a001164084180530140740500102c1b4080010141a0070210780440701402c0840800102c0541200101c0b40502d01c1100500115408c200030540740505101c0840514d01c1400002102c004070210145341401c0140840b0010780042902f0140700507502c0740b01d06c03405021
|4=>0x1c44c1001502c0841807b01c0500b0010200040701502c6940508f0180741402102c0040502d02c074000210780040701406c0440502d01c0b40506801c0843a02f0600641000101c0540b0210a40bc1e00d01c0500709902c0541b00d068050070210000840501d194004051930500740b0010140040b06d0200040506801c0840b02102c1240002101c11005001184084070930180541000102c0841201101c0b40502d01c110050010140f000021
|5=>0x1c0841201101c110050010e808c180190400040701502c0840502d0480840b01d01c110050010140b46f0010a00700502102c074120350400740b02101c110050010200041e00d01c0501802f01c0542302f08c04c0f00101c1040b0210e804c1801902c0c4000210140740502d01c0b46c0010780840501c02c0a8240370540840505102c00410001114004071130400540b0210200041e02101c0500b00102c0740505102c0041b00d0141a007021
|6=>0x500840b01d0680500505101c0840002102c0041804002c084050010200040701508c00c230130180741402102c0041802f01c0541200d01c1100500102c7c87b02105407c0505101c240050190400040704102400c0601d0500840b00101c0b40800105073c0501f02c0041000106c0340502d01c0b40506801c084741cd0400040701601c05c0b02102c654051930500740503c01c104050010200040b02102c0543c0a002c0740502101c00408001
|7=>0x1c0040b0150441d00500102c0740800105088c0506b01c0840b00102c3f41801b02c0c40800101c0540b0150746fc2801c0140840b01d0681500505101c0840002102c0043a0130600641000101c0542620f02c054050400200040b021074150080010500540b00102c0740b19501464c1401d02c0041e0350a40bc0701401c2640b01508408c0508903c00c070410900bc240370180541000102c0846202102c1240002101c110050010900dc05019
|8=>0x6008c0501d01c0b41b0350140840506801c0840702d0200041407b0140700b0010200040b0010141a0070211ac0844500101c44c1001502c0540b01d0c80841e00101c0500b00106c0d4080010141a00702102c07412035000084070440140041b03502c004050210141a00702123404c102311d00040701702c0843a01306006414021014074070210140b4280740140840b01d01c08412035000084070440140040505102c0041b00d0141a007021
|9=>0x1b00040502d02c6c41e021014070230130409743c04301c0040b02102c3f41801b0400040701502c084080010780340b0150140700b01d0400040b0210780340501c0140740002106c0340b0150141a00702102c2b82907b0740540501c02c0740b02608c04c0601d0500840b00123404c93001040744070170200041e01102c0740701402c0540505102c0041e00d01c0500b0010200040701502c0046f0010a00700502102c074350520200040b001
|10=>0x2c0042902f0a41ec1d0150140700b01d2789d42901f0141d80507502c0743a02f01c244060150400040b0210200041d0150780340501c02c0740b0310e803c1801902c0c40800101c0541e00d0600bc070140600b4070150200041b00d0140040506801c0841807b01c0500b001020004070150149c40b25d0f010c070010400049a00106010c0701502c0841804301c0540b02106c0d41401502c0040506801c0840800102c4141a04401c08405001
|11=>0x2c0541200d01c004070440140040800105073c0501f02c0040701504803407044014004ac02f0f0284070010140840702d0501ec0501c02c0040b06d0140040506801c084070012ac0041001602c0840002103c00c0704102c084052a50501a80702102c0040b0210780340501c0140741029f0f00500700102c084a50012900840704302c084470500600840501d02c0041805302c0040800101c054070440140041802f01c05407285014a0c14023
|12=>0x1c054072e71280581000302c084120350140b407044014004050010f00500700102c0846a0030601ec0701401c0541d1bf0a00700502102c0747300102c0840002101c058230030180741402102c0040b01d0140840506801c084440f302c28407001014084b403501cb3c1001702c0840b00101c08400021014074180190500840501d02c0040525d0f010c0700102c0841804b01407407044014004102bd02c084072bb01400c0702d0f005007001
|13=>0x2c0841e03501c0500709902c0540b31a1cc0c40002101c0581e02101c0500709902c054a70210f00500700102c074970210f010c0700102c0841030d0f005c0700102c084c1003014c040709b02c0541029d0f00500700102c084072f50f01080700102c0841e02101c0500b00102c074bb0010601080701502c084070210a01d00502102c074110740140040700102c0744500101c44c1001502c0840503c0400740b02102c0541802f01c0501802d
|14=>0x2c0744502101c44c1001502c0842402f0180541000102c084070920540840505102c004070930180541000102c0840434101406c1402102c004050ed3580840b0f201c004d401534c0040b34901c08c073430180581000102c0847202302cce4050f301c0043c2af01c0041001602c0849a02106010c0701502c084050213280841401e02c0042600306805c0702102c054150230142f40505202c0047327901c0580507602c0740502d07800407014
|15=>0x2c0740705105400c0505102c004e802104407c0500102c0740517301807c1402102c0041801a02c0c40800101c0540517101807c1402102c004e402338c0b41800301c054e102d348ae40702301400c1402102c0740501f02c004103390f00580700102c0841001d2ac0841001602c084200030540740505102c0041802d01c0540702301400c1837701c0540507402c0740702104804407044014004070160140040800102c084db0a30140841d003
|16=>0x140042a01c01c084280010140841e00d06008c0501c014074f500101cab41001602c0840b1a90601ec0701401c054073c90180501000102c0840701401c2640800102c0540b3c13bc078280030140841807b01c0501802d01c05412011000084070440140040800102c00418023014074060790400040701402c0843c20f0400500700102c0840002102cec4070470140045700102c1b40506801c0840b3a90a03c80502101c0041d0540500540b001
|17=>0x2c0540741802c0740b2b901400c073cb0180501000102c084073410180581000102c084000210501e40501c02c0040800101d0182602302c0541b00102c0540506801c0841406f02c0040506801c084142210141ac0702102c004fc00103c05c0704102c084072ad0000841001602c084000210682600702102c054073e704011c0500102c0840b1aa0601ec0701401c054061cf02c0c40002101c0580503c01c1040500102c0840b39e3a008407046
|18=>0x2c0840543d0f01000700102c0848a0010a01d00502102c0740b02100008407044014004050f00140040700102c0740607b0400040701402c0841d01401c0b40800102c054080010601ec0701401c0540500302c0540b34901c08c0d42d01c4ac1000302c084050410f010c0700102c0841a01401c084000210140740b01d01cc802600302c0540b01d0c80841e00101c050072e51280581000302c0841812904000c0701502c084a70210f005007001
|19=>0x2c074890210441d00500102c074240370a01440502102c0040b45d0a014c0502102c0041d09801c0b40800102c0540b01d0140b4d200101c08c0702d01c2fc0505202c0042832b0140841401e02c0040705105408c0505102c004071d502c2a828001014084050ee3580840b0f201c0041401502c0040506801c0842600302c0740702302c0541804002c0840500101c054070234180740b2b901400c2601e01c0840800102c0541001d01c11805001
|20=>0x2c004070a801c0b4280010140841e00d01c0501800101c0552a0210601400501d02c0041d4a301c0b47302101c0580b00102c1b40506801c0840b01d0c80841e00101c0500b3390f00580700102c084ae30101400c0709b02c0546202102c124070440140040549509c0040704202c084830010400500700102c0840748901521c1d02302c0740747d0980cc0800102c0543c47702c288070010140840b46d01d1acae02101400c1e00102c0540501c
|21=>0x2c054071d602c2a8280010140840f0230400740b02102c0542302f03c0040704102c0840b0c51b00041e0210140712b07b01c0501800101c055310210401180500102c085212b907408c0500302c0740002102c0052e01d01408c0501e01c2680800102c0541e00d01c0501802f01c0541a044020004070210140042301303c0040704102c0840b0010a00700502102c0740525d0f010c0700102c084070012ac0841001602c084a01cd05008c0501f
|22=>0x2c0841a0540141440702102c0041445d0a014c0502102c0040d11501c44c2602102c0553b00101d01c2602302c0540501c02c0040002102c074230130f01040700102c0847702105073c0501f02c004052a50501a80702102c0042835902c3c80502101c0041805302c0040800101c054074e134c0580b34901c08c00021014db41d00302c0741402119000c1401d02c004240370540840505102c0053501534c00c0b34901c08c1e02102c07407014
|23=>0x1c004075113200842600302c054070210480d407044014004075092b81080500302c084142230141ac0702102c0040504303c05c0704102c0840502d01c0b40506801c0841b0110200040506801c0840502d04074c0701702c0840002101464c1401d02c0053f00104073c0701602c0841807b01407018021014074080010780440501c02c0740b0210601ec0501c0140741d46b01c0b4ae02101400c073410180581000102c0850100111008c10015
|24=>0x2c0740502d0c80841e00101c050420440140043c02101c0054c0010401ec0701402c0840705505400c0505102c004070210a000c0502102c0540502d0a01d00502102c074440f002c284070010140844001d0401100500102c084100c90780040701402c084ef0760a000c0502102c074080010142f40505202c0040800101d4740505302c004000210a408c0507502c0740f0170400740500302c0841e00d0140700507502c0740b02101cce4050f3
|25=>0x2c004073e504011c0500102c084070213bc078280030140840b2ad0000841001602c0841000101cab41001602c0840b01d1cc0c40002101c0582637702c0540507402c0741406d02c0040506801c084d200102c0740500101c08c072ad0000841001602c0846f0010a00700502102c0040b021048034070440140046c0010780840501c02c0040b11501c44c1001502c0840800101c11c0500102c084080010501ec0501c02c0040002137408405074
|26=>0x1464c1401d02c0046f0210a00700502102c004142210141ac0702102c0041001d01c1180500102c0841828305008c0501d02c0040502d0f010c070010200041e01101c0500b01502c0040b56501c28c0502101558ca001d05008c0b00101c1501401502c0040b01d02d5540510b0f0084070010200041e00d0140700b01d03caec1001d01400c0b0212d0004072cf04005c0b0210a44ec0709901c2600b01506014c0501d02c0042300301807414021
|27=>0x2c0840b2b901400c0534b01c08c0507602c0741434101406c1402102c0042d02303c0540704102c0841402101d4740505302c0041b00d0200040506801c0841b0350140840506801c084280510500740502102c005610210441dc0500102c0743c2cf04005c0700102c0855f00302c744080010140780543f0f01000700102c0840b0210000841e00101c0500d5710180781402102c0040b00106c0d40506801c0846c00102c6c41e02101407014021
|28=>0x141d00b01d02c3146c0010780840501c0500540b0010141a00702101c8341001401c0040b0215380040b56501c28c0502101c144000210141440b0015a80840535b02c3c80700144c084070bf0141480b0010900bc100450140040b02101c0841401c0140840b00102c0c41459f0a007c0502102c0040b01d0f02600700102c0552b0430600040701502c0842907b0140700507502c074230030501a40702102c004140210780040501c02c0041001d
|29=>0x500840b0015e40040720f0400500b0215dc0044702f0600840501d1a80041807b01c0500701501c08c055d505007c0b0010200041406801c0840b001020004141cd01407c0b0015c4004071100980840b01502c1240002101c110050010601400b00102000407015194084051930740040b01d0140b40f02301c1040b021040cec0b0210143cc070010516742801f0140840b00101c0840b04901c1100500105400c0b01d0141440b0013740840502d
|30=>0x140700b01d01c0b41b0350141a0070212b89d40500301c2680b01507408c0b01d02cae4050031bc0842801c0140840b01d0d41480b00106008c0501d0187440b0310200040501e0480340b01d01c11005001034454071130400540b0210140b40b1b10780840501c02c074280030140840b0150741ec0b01d01c0500b015014bdc3c04201c0040b0210900bc150210141440b00101497c3c04301c0040b0210a40bc0701401c2640b0150155cc0601e
|31=>0x141dc0b01d068150070210141440b00101c7540b0aa0a00040502101cbd43c04201c0040b0210140b47400101c05c0b02115408c2900301c2640b015040004ab0010400580b0215c808c141cd01407c0b0010400040f01501c1040b02101c0501802f0200040701560400cd301502cd24070232ac004000210400580b02101c2fc080010141480b00106815c0505101c0840b0010601ec070140600bc070150601040b0210000840501d02c0041e011
|32=>0x141a0070211440c41802f0200040701501c084080010141480b00106006c0b0310200040701502c0841e01101c0500b01508c0bc0f00101c1040b0211d09d40501e01c2680b0150141d40702d0141a00702106805c1101f014004070210140c4080010141a0070210d41440b00106008c0501d6180052e01e01408c0b0150355c40601e0500840b00101cd040501b0500840b0010000840451d01414c0b00102c1240002101c1100500100008583001
|33=>0x1c10c0b0210681400702102c0040b01d02d8e40548407408c0b01d0500540532b0500780b00102c0541b0350141a007021068280070210140840b01501c0b4080010780840501c02c0041e00d0140700b01d02c0541001401c0040b0210480340502d01c11005001078034070140600b40701501c0b4075404b80b40502302d8a4051080f008407001014bd43c04201c0040b0213380840b01d0143cc070010900dc060150400040b02102c0041b001
|34=>0x200040501e1c808c0b3390143cc070010a40bc050760141d40b01d02c4141a04401c0840500101c0b44e00101c2600b0150500840451d01414c0b0010000840b01d1cc004070166440b43500306008c0501d02ca441000101c10c0b021138084070980200040b0154ac10c1800101c0540b0210408c47400101c05c0b02101400c1001d02c0840b0150000840b29101c10c0b0210984200502d0f00840700101c064060150400040b021040004a4021
|35=>0x1c0500b0150a41ec070140600b4070152700559802d0f008c070011340844e00101c2600b01502c054080010780840501c0200059604201c00c0b0210000840501f0140040b01d01c08c0732109800c0b0150c80841e0010140700b00101c0840002101c1100500102c054110740140040b01d06c0040702d0141a007021014144070210000840b0012680041804301c0540b021050054053290500780b00105128c7302101407c0b0011d073407016
|36=>0x140840b01511008c1001501c0040b0210a41ec1d0150140700b01d08c00c3c04101c0040b0210400040f01701c1040b0210000840b00102c7440501e2ac0c4000210400580b0210f08341001401c0040b02102c054080010141a00702101c0b4080010141480b0010140f80800101c1040b0210141a80702102cae4050030159b57502105007c0b001000084e302d06000c0701505159c2801e0140840b001020004141cd01407c0b0010780440b01d
|37=>0x780840501c0000851502102c1e40501c02c3186c0010780840501c01d8340507707408c0b01d08c04c0601d0500840b001014c94ca0210500780b00106c0040b0150141a0070210000840b01501c05c0b0210141a00b00101c0840501d06006c1000101c0540b0214d808c0536d07400c0b01d0200054702101414c0b0011d07340701601c05c0b0210600600b0310200040701502cd04060160400040b02106815c070210141440b00101c0b407021
|38=>0x1c05c0b021040004a400101c10c0b0210200041401502c0040b01d69c004072af0400580b0210000840501e01407c0b00101c834050400200040b021050084141cd01407c0b0010200041e0110140700b001014cac080010500780b001098ddc0502d0141d00b01d06c034050010141a0070210d41440b00106008c0501d6940b54502301cae4050030780340b0150140700b01d0600bc070210000840501d0142380601d0500840b00102c3146c001
|39=>0x2c0042301302c4243c02101c004070213400040501b0500840b0010142300601d0500840b00101c084070500000840b0010200041e01101c0500b02102c0041e00d0200040701402c0041b0110141a00702109883c0504002c0840b0150601ec180230140700501d02c054050400200040b02102c0541e02101c0500b02165008c0732109800c0b01501c244060150400040b02108008c1501d0141440b00101c0b4150230141440b00124c004101d1
|40=>0x1c0540002101c7340501f02c0041e00d01c0501802f01c0540b01502c0740502101c0040508903c00c0704102c0840701402c0040800101c05414631014cac1401e02c0040b29d0f00500700102c084d90013000840709b02c054bd0010f01080700102c084050190400040704102c084076b90140040002102c0581000101c0580701702c085ad00101d0102602302c054140210780440501c02c004056ad19008c1d00102c07414021014cac1401e
|41=>0x140040701402c0c40800101c0541d0150780340501c02c0740514f0500700502102c004070410400040b02102c054050190500840b00102c0740502d0200040704102c0840500302c0740702302c0540500101c08400021014075a700101cabc1001602c0840800101c0840b00102c0741d0540500540b00102c0741a0bf01c0840505202c0040b02101c004070440140040b0310780340800101c051010f001c0042602302c0541801902c0c408001
|42=>0x14a041402302c0040b0c61b00041e021014070070210145341401c02c004070150780340800101c050240370401140500102c0842301303c0040704102c0842901f0141d80507502c0740b57101c06c1000102c0840b1c1048084070440140041b01102c0540506801c0842402f0180541000102c0841000102c0843c0a002c0740502101c0040002102c1e40501c02c005020214540040b07901c0500800102c0540501c02c0741a04401c05407021
|43=>0x1daec0002102c0580b01d000084070164dc00c076b902c058070010400580b0216e00040500102c07963001014d2c0702302d4740505302c0040502107400c0b01d02d9640502101c00d2e6e101408c0b01e09808c2602102c0543c09801c0040b0150141000b02102c0540b1c50f0280070010140841802f01c05407021014004d202d01c08c0b2b901400c2907b0740540501c02c0741000102c1e40701402c085964b901c00c0002101408db401f
|44=>0x140040701601c05c0b02101c4a41000302c0840770902c734070160140b40704202c08407001014004070150780440701402c0840702d06008c0501d02c054070a3014084056e66580b40700301c084ae02101400c050010200040b0150140040002102c0752d0014b8074050230a014c0502102c0049d00101c2680b01534c0580b34901c08c1e00d020004070143280841401e02c0041d0150140700b01d02c0040534901c08c2801c0140840b015
|45=>0x600bc0701501c1582600102c054d300302cd240702305408c2600102c0540732109800c0b01501c11c0500102c0840b56501c28c0502109808c0800102c0540b0aa0a00040502101dc5c05033020005b80010140840b01e02c058080010140780701501c08c05003014744050010140780732109800c0b0150140b41d02302c074140160000840b0010601480501d02c004070160141d80b01d09808c0800102c0547400101c05c0502102c07407044
|46=>0x1cce4050f301c0042801f0140840b01d34c0540b34901c08c4e02d01c2600b0150400741001602c0840b4b90000840502334c0040b34901c08c2801e0140840b0010d4084180230140741e0110140700b0010400040701502c0840701402000407015014cac1401e02c004050210141440b0010441a80500101c084dd0010141d00b01d0141a80702102c0040b0150141d00b01d0601ec0701401c0540b3290500780b0010400500700102c0840b145
|47=>0x2c0840800102c1ec070140f010c0700102c0843c02301c0040b0150a400c0709902c0540700102c0840b01501474408001014078a001e05008c0b00101cabc1001602c084ef01e0a000c0502102dcb411023014004060140400040b0216b80040002102c0581001501c0040b02107400c0700102c0740b3750141d00b01d6180052e01e01408d9604101c00c0b0210500540b00102c0741001d01400c0b0210980740500102c0540503c0740840b01d
|48=>0x6e00840b01e01c0840501e02c0041b0210141a0070210141ac070210000859802d0f008c070010140780709a02c0540b0161d00840501e6582680700302c055d1023658054070030401180500102c084053290500780b001048034070440140040b07902000407014034a440704302c0840b0152b808405003304084056e102c07805003015b840b01e01c0b4ae02101400c1e00d01c0500b02101c0840502102c0042900301c2640b01507800407014
|49=>0x4ac0bc1800101c0540b0010200040501e0140043c02101c0041d3770141d00b01d0500840505302c0040b0a201c004050210f1aec0700102c0581001701c0040b0210441d00500102c0740b0aa0a0004050210140b4070440140040712b04000c0b02101d8340507702c0740506b01c0840b01e01c2640800102c0541a2bb01c084050030a405c1802d01c0541b0350141a00702101c0840500301c0541804001c0540b0210180541000102c08405297
|50=>0x2c058070aa0a0004050210740841d02302c0741406801c0840b00101c0500701502c0841e0110140700b01d3bc07428003014084050760141d40b01d02c0540704102c0842634b01c08c0b0150f01040700102c084c000101c26c0b01506010c0701502c0840500302c0840b01507408c0500302c0740701709800c0b01511008c1001502c0840535902c3c8070013000040709b02c055d9001015b8c0b01e0200041401e02c004075404b80b405023
|51=>0x200040501e01c0041001602c0841501d0141440b00170800c0b1cd01c0581a2210141ac0702104000c0701502c084260230140840b01501c0540505202c004051d101c05c0b0210141080500302c084830010400500b0211380040709802c0542901f0141d40b01d02c0740b2b901400c1001d01c0580b0211080bc3c02101c0040702d02c7340701601c44c1001502c084080010141480b0011380040709802c0540800102c1e40701401dae405001
|52=>0x180581000102c0840502d1d00040501e01dae40002102c0580b0210200040501e4540040b07901c050080010780d4070140a01d00502102c074080010780840501c51c0840505302c0052d02d4b80740502301cae40702301400c4a01504000c0b0212ac0041001602c084db02107400c0b01d02c0740501f02c004d301602cd24070230140840702102c074ce0210143cc0700101c00c0002102c074150030141440b00109808c0b02102c05474021
|53=>0x2c0541a01701c0840b0156f80bc0534901c08c0b0a90a0004050210200040506801c0840500102cd240702302c0740709a02c0541e00d0140700b01d0780040501c02c074140210500780b00145408c0b0790140700700102c734070166e00c40800102c0780b0310200040501e02c0840500101c054050760000840b01d04407c0500101c08c0778d0141400b00102c0540700102c074053b101c11c0500101c0b40709802c0554700101414c0b001
|54=>0x1c28c050210141440501d02c0041501f0141440b00105408c0505102c0040502d4b8004050230440780500102c0541007901c0500b021015b9d9602d01c00c280500140840b0010980040800102c0540b07901c0500b02106008c0501c014074d602102c3c80700102c0743c02101c004000210400580b021014ec407047014004d301502cd240702302cc34050f201c005d9021015b8c0b01e34c05c0b34901c08c070210141480b00107804407014
|55=>0x141000800102c0840700101c0580b02101d0142602302c054440030980840b0150780840701402c0840701701c0840b01504407c0500101c0840514f0500700b0010140040002101c0583c04201c0040b0213000840709b02c0543c02301400407001045b8c0500102c0783c4bb01c0040502301c0840502102c05405001015b8c0b01e01cae40702101400c2601e01c2680b0154ac08c1800101c0541b0010141a0070211440841802f0140740b565
|56=>0x1407807014060004070150400041001502c0840b0210200040b015015f540b06a01c0843c01701c0040b0210780840501c02c0043c04101c0040b0210141440702102c004071100980840b0150180581000102c0847402101c05c0502101c1440002102c0041e00101c0500b0157cc0599602101c00cae04201400c0b02101c08400021014075be003014d24070230141dc1d02302c074070a30140840b0160140040002102c0581d02301c0840b01d
|57=>0x2c2880502101d1a4ae02101400c3500106008c0501d0140fc1d02102c074260330200040b01505007c0702102c0040702302cae40500302c084072bb01400d9604201c00c0b021014d2c0500101c08c0514d0500700b00101df9c0b0460140040732309800c0b01501c0501802f01c054280770140840b01d0140b40502302c0740702101c110050013200842600302c055eb02d4b80040502301807c1402102c0040b01d01c08c0b01501c0840b1d1
|58=>0x140740709802c054050010600bc0701501407c0500102c0783c02301c0040b01d02c084050f101c0040501c0141d40b01d0400040701702c0840548707408c0b01d0600840501d02c0040700101408c0b0150140cc0800102c0540b0216580540700303c0040704102c0840500301c26c0b01502c0740502101c0044202f0680040702130c084050f201c0040002106000c07015304004056e102c078072cd04005c0b0210600bc051d101407807477
|59=>0x1c08c0709901c2600b01501c0540506801c0840b2210141ac070210140840501d02c004141cf01407c0b0012200040506b01c0840502d07408c0b01d01400c0709a02c054e302f06000c0701504407c0500102c078054533480040702301d8340507702c0740740609808c0b01501cab41001602c0840704101c0040b0210a40bc0709902c055f902102c118050010780840501c02c0740b01501c0840b01d51c0840505302c004100450140040b021
|60=>0x141440b0010000840505102c0041807b01c0500701501442c3c02101c0040751f01414c0b0010140040800102c0840737b6b80840b0160140700002102c0740751d01414c0b0010742600702d02c0541802f0200040701501c0840709b02c054102ad0400580b02154000d2e02d01408c7302101407c0b001349ae40702302c058150210141440b00101c2f40505202c004051930740040b01d0981ec0701402c0560500101c1000b02102c07405003
|61=>0x1c05c2600302c0540b06f0141a0070210400040b02102c0541000301c05c0b0210a007c0502102c0780502106008c0501d4b40bd2e01d01408c3500306008c0501d01cc882600302c0541e02101c0500b0150f02680700102c0541802301c0840501d0f028407001014085ae00101c0040b0160000852e01d01408c3c01401c0040b021014db01d00302c0755900101c28c050210160d41a00301c0840502f1d00040501e01c0040704202c0840501d
|62=>0x14084ca0010500780b0011b00041e0210140700500301c2640b0150980740702302c0540548407408c0b01d02c054072bb01400c0b29d0143c0070011d00c4080010140780b2bd01caec050030500840505102c004070210140840b01605074c0501e02c0040503d0740840b01d06c0440506801c0840b8596580580700301c0840505102c004880210141ac0702101406c1402102c004280520140840b0010500700702102c004077150140cc08001
|63=>0x141d40b01d0114740505302c0040701501c0840500101c0500b00102c074070140600b40701501c4482602102c0540583706800c07021014004056e102c0780702102c0040b01d0140840702102c078072cf04005c0b0210441dc0500102c0740501d07408c0b01d0f0280070010140847302101407c0b01d57c0040b1d10140789e0010141d80b01d02c0540702101400c0702107408c0b01d02ce84070460140040b0c9078004070141bc004070a0
|64=>0x2c0840500301c0540702d0a00040502102c0840800101c00d1500302c1e40701401cce4050f301c004740210140780b001048088070440140040b7150140cc080010f00500700102c0540500101407c070010501ec0501c02c0040b01e0f00840700130400c056e102c0781406a01c0840b00106008c071cd01c058070030000840502301c004070440140041406b01c0840b0010140041d02302c074050bd0141480b00101d4740505302c0041d023
|65=>0x2c074110230140040b0150507340501f02c004050770000840b01d02c124070440140050601c02cae40500309c0040704202c084c70010141a80702102c0841e00201c0501401d0141440b00106c0040506801c0840501e01c2680b0156592e40502301c00d5f00302c7440501e02c0040506801c0840b0460140040800102c05807001014084050740000840b01d4b80780502302c0041d01701c0840b01d02c3c40502101c0040f01501c1040b021
|66=>0x1c08c0500302c004180230140740b00101c28c050210a007007021014084280f2014084070016580580700302c0740b0151d00840501e1b00041e0210140701e00d01c050070150144203c02101c0040778f0141400b00102c124070440140040b00102cd2407023014dbc1d00302c0740b1cd0000840701601c2fc0505202c0057502105007c0b00102c0040800101c0540548507408c0b01d02c0540501c02c0740f02301c1040b0214b80b405023
|67=>0x1c0540700102c0840709902c0540b00102c0740709902c0540b07901c0500b07b01c0500b0f201c0040501f02c0740700101408c05033020004141cd01407c0b00102c0840b1cd01c0581a04401c084050010400040701402c084070160200040501e02000407021014004070140600bc070150140041800301c0543502d06008c0501d01c0b40800102c0540b0310200040701501c0500002102c004070014b80040502301c08c1802f014074d22b9
|68=>0x1400d9601501c00c2600302c0540002102c0040702302c004180210140740701502c084072bb01400c1d00302c0740505002c0040700102c0740800101c050050f201c0040702301400c0700102c0580507602c0740b046014004076b902c0581e03501c0500501f01c0041e0210140703c02301c0040704102c0859602101c00c0800101c054070010140840b07901c0500506b01c0840507702c0740702102c0540500101c0040500102c05405001
|69=>0x1c0540701602c0780702102c0741800101c0542602302c0540502302c0781401e02c004280010140840702102c0580702101c0580b0450140041d02102c074050f001c0040700302c0541000102c0840702302c0740800102c07818023014074050010140840702302c0580701402c0840502102c0580700102c0740002101408c0505302c004056e302c0787302101c0580500102c084050f101c00405021014074050f301c0042600302c05407021
|70=>0x2c0840700302c0741e00201c0501001402c0841000302c0840505202c0040b34901c08c1401e02c0040501e02c004070230140740506801c0852e01e01408c0507602c0740701702c0841e021014071ae00102c058740210140780800102c0540700302c0841000102c0840505302c0042602102c0540502301c00c3c02101c0042602102c05411023014004080010140780506b01c084070450140040501d02c0740501c02c0752e02d01408c1802f
|71=>0x140780700302c07807014014004051d10140780701401c0541802f01c0541e00d01c0500500302c074070160140780700102c0540709802c055b800102c0780702d02c0540b1cd01c058ae02101400c070210140040701702c054070460140040507702c0740500102c058072b901400c0500101c0580500101c05418023014074070a3014084050010200041001702c0842600102c0540b0a10140841802d01c0540507402c0741a00101c08410015
|72=>0x1c0540502102c084050030200040b015
|_=>0
def oO:Nat→Nat→Nat
|7,0=>0x1a100c8804d801ac007600308001800000000
|8,0=>0x99a84b94252a124508fa8469422c811150862841d4204a0fd507c2800001e6a0ee5074a839501c0a0db506b2800001a480cd50642830d417ca0b9505a282bd400000aa5052a82814136a0965048a8231410ea082503f201f080f080735037281a540cc6061500000178c0b2a05450282012d408ca041501e280dd4064a02d501428094c040a01b5
|8,1=>0x9348490a243511f288e54468a23041162089d4444a21d510c2884d441e80000105288154400a1fb50fb287c543d8a1e750f1a077943b2a1d540e828731038ea1c250df200000372a1b450d7a86a9434c81a240cf206654330219350c72862cc30ca18150be285dd4000017250b6a85a142c6a15e50aca8551429ea14a50a2a8501427a61385
|8,2=>0xae9456aa2b05155a8aa8454aa2a0514da8a5940000292400000a35451462855140289ed44eca27151362899d44c4a000012ea896144a8824f5
|9,0=>0x1dda0edd076683af41d5a0e9d0746839f41cda0e5d0726838f41c5a0e1d0706837f41bda0ddd06e6836f41b5a0d9d06c6835f41ada0d5d06a6834f41a5a0d1d0686833f419da0cdd0666832f4195a0c9d0646831f418da0c5d0626830f4185a0c1d060682ff417da0bdd05e682ef4175a0b9d05c682df416da0b5d05a682cf4165a0b1d058682bf4
|9,1=>0x25da12dd096684af4255a129d0946849f424da125d0926848f4245a121d0906847f423da11dd08e6846f4235a119d08c6845f422da115d08a6844f4225a111d0886843f421da10dd0866842f4215a109d0846841f420da105d0826840f4205a101d080683ff41fda0fdd07e683ef41f5a0f9d07c683df41eda0f5d07a683cf41e5a0f1d078683bf4
|9,2=>0x2dda16dd0b6685af42d5a169d0b46859f42cda165d0b26858f42c5a161d0b06857f42bda15dd0ae6856f42b5a159d0ac6855f42ada155d0aa6854f42a5a151d0a86853f429da14dd0a66852f4295a149d0a46851f428da145d0a26850f4285a141d0a0684ff427da13dd09e684ef4275a139d09c684df426da135d09a684cf4265a131d098684bf4
|9,3=>0x35ca1ad50d6286ad435519a990d44869e434d21a590d24868e434521a190d06667f433da19dd0ce6866f4335a199d0cc6865f432da195d0ca6864f4325a191d0c86863f431da18dd0c66862f4315a189d0c46861f430da185d0c26860f4305a181d0c0685ff42fda17dd0be685ef42f5a179d0bc685df42eda175d0ba685cf42e5a171d0b8685bf4
|9,4=>0x3db21ec90f5c87aa43d321e890f3c879a43cb21e490f1c878a43c321e090efc877a43bb21dc90edc876a43b321d890ebc875a43ab21d490e9c874a43a321d090e7c873a439b21cc90e5c872a439321c890e3c871a438c89c550e22870d4384a1c150e0286fd437ca1bd50de286ed4374a1b950dc286dd436ca1b550da286cd4364a1b150d8286bd4
|9,5=>0x45b222c9115c88aa445322289113c889a444b22249111c888a44432220910fc887a443b221c910dc886a44332218910bc885a442b22149109c884a442322109107c883a441b220c9105c882a441322089103c881a440b22049101c880a4403220090ffc87fa43fb21fc90fdc87ea43f321f890fbc87da43eb21f490f9c87ca43e321f090f7c87ba4
|9,6=>0x4db226c9135c89aa44d322689133c899a44cb22649131c898a44c32260912fc897a44bb225c912dc896a44b32258912bc895a44ab22549129c894a44a322509127c893a449b224c9125c892a449322489123c891a448b22449121c890a44832240911fc88fa447b223c911dc88ea44732238911bc88da446b22349119c88ca446322309117c88ba4
|9,7=>0x558a2ab515528aa54550a2a7515328a95454992a3d15168a874541a29fd14f68a774539a29bd14d68a674531a297d14b68a574529a293d14968a474521a28fd14768a374519a28bd14568a274511a287d14368a174509a283d14168a074501a27fd13f689fa14fb227c913dc89ea44f32278913bc89da44eb22749139c89ca44e322709137c89ba4
|9,8=>0xad54568a2b3515928ac54560a2af515728ab54
|10,0=>0x5cb1ae4cd7206b8d35c51ae1cd7086b8135bf1adecd6f06b7535b91adbcd6d86b6935b31ad8cd6c06b5d35ad1ad5cd6a86b5135a71ad2cd6906b4535a11acfcd6786b39359b1acccd6606b2d35951ac9cd6486b21358f1ac6cd6306b1535891ac3cd6186b0935831ac0cd6006afd357d1abdcd5e86af135771abacd5d06ae535711ab7cd5b86ad93
|10,1=>0x62b1b14cd8a06c4d36251b11cd8886c41361f1b0ecd8706c3536191b0bcd8586c2936131b08cd8406c1d360d1b05cd8286c1136071b02cd8106c0536011affcd7f86bf935fb1afccd7e06bed35f51af9cd7c86be135ef1af6cd7b06bd535e91af3cd7986bc935e31af0cd7806bbd35dd1aedcd7686bb135d71aeacd7506ba535d11ae7cd7386b993
|10,2=>0x68b1b44cda206d0d36851b41cda086d01367f1b3ecd9f06cf536791b3bcd9d86ce936731b38cd9c06cdd366d1b35cd9a86cd136671b32cd9906cc536611b2fcd9786cb9365b1b2ccd9606cad36551b29cd9486ca1364f1b26cd9306c9536491b23cd9186c8936431b20cd9006c7d363d1b1dcd8e86c7136371b1acd8d06c6536311b17cd8b86c593
|10,3=>0x6eb1b74cdba06dcd36e51b71cdb886dc136df1b6ecdb706db536d91b6bcdb586da936d31b68cdb406d9d36cd1b65cdb286d9136c71b62cdb106d8536c11b5fcdaf86d7936bb1b5ccdae06d6d36b51b59cdac86d6136af1b56cdab06d5536a91b53cda986d4936a31b50cda806d3d369d1b4dcda686d3136971b4acda506d2536911b47cda386d193
|10,4=>0x74b1ba4cdd206e8d37451ba1cdd086e81373f1b9ecdcf06e7537391b9bcdcd86e6937331b98cdcc06e5d372d1b95cdca86e5137271b92cdc906e4537211b8fcdc786e39371b1b8ccdc606e2d37151b89cdc486e21370f1b86cdc306e1537091b83cdc186e0937031b80cdc006dfd36fd1b7dcdbe86df136f71b7acdbd06de536f11b77cdbb86dd93
|10,5=>0x7ab1bd4cdea06f4d37a51bd1cde886f41379f1bcecde706f3537991bcbcde586f2937931bc8cde406f1d378d1bc5cde286f1137871bc2cde106f0537811bbfcddf86ef9377b1bbccdde06eed37751bb9cddc86ee1376f1bb6cddb06ed537691bb3cdd986ec937631bb0cdd806ebd375d1badcdd686eb137571baacdd506ea537511ba7cdd386e993
|10,6=>0x80b1c04ce020700d38051c01ce008700137ff1bfecdff06ff537f91bfbcdfd86fe937f31bf8cdfc06fdd37ed1bf5cdfa86fd137e71bf2cdf906fc537e11befcdf786fb937db1beccdf606fad37d51be9cdf486fa137cf1be6cdf306f9537c91be3cdf186f8937c31be0cdf006f7d37bd1bddcdee86f7137b71bdacded06f6537b11bd7cdeb86f593
|10,7=>0x86b1c34ce1a070cd38651c31ce18870c1385f1c2ece17070b538591c2bce15870a938531c28ce140709d384d1c25ce128709138471c22ce110708538411c1fce0f87079383b1c1cce0e0706d38351c19ce0c87061382f1c16ce0b0705538291c13ce098704938231c10ce080703d381d1c0dce068703138171c0ace050702538111c07ce03870193
|10,8=>0x21d070e538711c37ce1b870d93
|11,0=>0x8b49459ca2ca516328b09457ca2ba515b28ac9455ca2aa515328a89453ca29a514b28a49451ca28a514328a0944fca27a513b289c944dca26a51332898944bca25a512b28949449ca24a512328909447ca23a511b288c9445ca22a511328889443ca21a510b28849441ca20a51032880943fca1fa50fb287c943dca1ea50f32878943bca1da50eb2
|11,1=>0x8f49479ca3ca51e328f09477ca3ba51db28ec9475ca3aa51d328e89473ca39a51cb28e49471ca38a51c328e0946fca37a51bb28dc946dca36a51b328d8946bca35a51ab28d49469ca34a51a328d09467ca33a519b28cc9465ca32a519328c89463ca31a518b28c49461ca30a518328c0945fca2fa517b28bc945dca2ea517328b8945bca2da516b2
|11,2=>0x8fc947dca3ea51f328f8947bca3da51eb2
|12,0=>0x48146408320319010c804640031ff18ff0c7f463f831fb1
|_,_=>0
def PO:=mkPO wAt oP oO 22 10 1023 17
def pmP:Nat→Nat
|0=>0x429fa000000002283f0000000016997000000001299700000000080000000000007c920000000002c93000000000291000000000028d300000000028bb000000000289300000000020160000000002006000000000200100000000020000000000000810000000000080000000000004bb00000000004930000000000400000000000023d00000000001fa000000000018000000000001200000000000108000000000003f000000000002400000000000110000000000010000000000000200000000000010000000000000
|1=>0x10028b3000000100289b000000100289300000010021bf00000010009340000001000811000000080008200000007078920000000452c830000000452897000000041a8930000000417897000000041689300000004129930000000407893000000040789200000004028b300000001168930000000112c97000000010699300000001028100000000102010000000010081000000001008000000000100093000000010008300000000fac8b00000000fac8300000000f2cc2000000009288300000000828930000000082110
|2=>0x20028b300000020028930000002000cb300000020004b3000000145a893000000141ac9b000000141a89b0000001412d9300000014128930000001402893000000110a8930000001102d9b0000001102c930000001102993000000110289b000000110289300000010f2c8b00000010d2c9300000010c2893000000108a89300000010821b30000001052c93000000104689300000010429bf00000010408180000001040118000000104001800000010228930000001012c9b000000100a893000000100689b0000001002d9f
|3=>0x30028bb00000030028b3000000300289f000000300289b000000300289300000030008bf000000300018600000025068930000002432c830000002422893000000241a893000000241289f000000240a11000000021028b7000000210211000000020b2c9300000020528930000002032893000000202a89300000020228930000002020034000000201a8b300000020128b300000020128930000002010110000000200a8b3000000200a89300000020089f200000020068b30000002002cb70000002002cb300000020029b3
|4=>0x30168930000003012c93000000301299b000000301289f000000301289b0000003012897000000300e893000000300ac93000000300a8b3000000300a89300000030089930000003006c970000003006c9300000030068970000003006893000000300389e0000003002df20000003002dbf0000003002dbb0000003002db30000003002d970000003002d930000003002cd30000003002cbb0000003002c9b0000003002c930000003002c8b00000030029bf00000030029bb0000003002997000000300299300000030028d3
|5=>0x308ac93000000308a9b3000000308a8930000003086d9b00000030868930000003082cbf00000030829b3000000308299300000030828b7000000308289b00000030828930000003062893000000305a8930000003052cbb0000003052c9b00000030529b3000000305289f000000305289b0000003052897000000305089f00000030428bb000000304289300000030368930000003032897000000302299300000030228b30000003022893000000302288b000000301e893000000301acb3000000301a9b7000000301a893
|6=>0x340a893000000340689f000000340689300000034028b300000034028970000003402893000000318e8b3000000318ad93000000318a8b30000003186993000000318689300000031829b300000031828b3000000311a8b70000003106c930000003106893000000310289300000030fa89300000030f28d300000030f289b00000030f289300000030d299300000030d289300000030c289300000030b289300000030aac9b00000030aac9300000030aa89300000030a28d300000030a28930000003092cb30000003092997
|7=>0x70828bf000000708289b000000704289b000000702a993000000700a893000000700299300000070028930000006082cb30000006082893000000510689b0000005042893000000500a8b300000050068930000005002c9b00000050028930000004502893000000441a8b300000044028930000004000810000000351e8b3000000351a8930000003512cb300000035129b300000034b2cb3000000349a8b3000000344a89300000034368930000003412d9300000034128b300000034128970000003412893000000340a9b3
|8=>0x91068930000009042993000000900a9930000009002d9b0000009002d93000000900299b0000009002993000000900001400000085068d3000000850689300000081068d200000081068930000008102c97000000810201000000080168970000008006010000000749a9b3000000746289b0000007412c93000000740a8b300000071868b30000007182c93000000710a8930000007106893000000710289300000070d289300000070ba9b3000000709a9b30000007092c97000000708a9930000007082d9b0000007082c93
|9=>0x110401180000011002993000001100201400000110001300000011000108000001040a000000001000a0110000010002c930000010000800000000f506893000000f08289b000000b50a110000000b506893000000b40e893000000b186d93000000b106893000000b0a2893000000b08699b000000b086993000000b03289b000000b032893000000b016893000000b012893000000b006893000000b002893000000b002093000000a102c97000000a022893000000a002c97000000a0028b3000000a0028930000009506893
|10=>0x1910a9930000019102c93000001900299b0000018102cd20000018102c9300000160029b300000134128970000013182d9700000130a2c9300000130a2893000001309a9b3000001308ac9300000130528970000013042893000001302ac930000013022893000001301a99300000130128930000013002cd20000013002c9300000130029b300000130029930000013002893000001211003000000121001140000012018110000001201289f000001201089f000001200289300000114028930000011180014000001110ad93
|11=>0x2349ad9b000002342289300000234129930000023402c9300000230e289300000230a2c9b00000230a2893000002308a993000002308a8930000023042c9b000002304289300000230368930000023032893000002302299b000002302289b00000230228930000023002d830000023002c9b000002300289b000002202a093000002202289300000220181800000022002010000002100002400000200220930000020000002000001b440118000001b086c93000001b086993000001b016993000001a102c97000001a002893
|12=>0x430028930000042002893000003b402893000003b016893000003b000118000003a022893000003a002893000003900299300000330b289300000330aa893000003309299f000003309299b0000033092993000003302a993000003301a993000003300a8930000033002c9300000330029930000033002893000003110a8930000031102d93000003110299300000310028930000030000919000003000010800000274a289300000270ea89300000270ba89300000270b28930000027002093000002608289300000250f2893
|13=>0x814068930000081402c930000081142c93000008114289f00000811428930000081106c93000008110289700000811000000000081042d970000081042c9700000810428970000081002c9f00000805028b300000804068c3000008040689300000804000100000080106cd200000801020930000080100000000008000281000000800025b3000008000200000000800005b300000800000010000080000000000004341289700000434028930000043082d1f0000043002dbf0000043002c930000043002c1f00000430029bf
|14=>0x8340689b000008340689300000834048930000083402cb300000834028b30000083402893000008310e8b300000830d289300000830c299700000830c28b700000830aa9b30000083082893000008305ac930000083042cb300000830228930000083012df60000083012db70000083012cb300000830129b300000830128b300000830128930000083002db30000083002c9300000830028b30000082006c9300000815024b300000814568930000081452c970000081412c9f000008141289b000008141289700000814068d3
|15=>0x91412897000009104a8970000091002c93000008f406893000008f00689b000008b41289b000008b406893000008b40289b000008b086d93000008b006893000008945299f000008940689300000894028930000089102c93000008904289f000008900289f0000088516c930000088416893000008840689300000884028d30000088102cd300000874a289300000874068930000087402cbb00000870469930000086012c930000083492993000008345289300000834429930000083442893000008341289b000008340a8b3
|16=>0x203012c930000203012893000020300a89b000020300289b000020300289700002030028930000202082893000020108289f000020100049f0000201000011000020051689300002000168930000200000010000020000000100001c140689300000c344289300000c301289300000b345689300000b3002c9300000b30029b300000b3002893000009b41299b000009b41299300000934c2893000009340489300000930a2d9300000930929b70000093082dbf0000093082db70000091412c9f000009141289f000009141289b
|17=>0x20701a8b3000020701a893000020701689300002070068930000207002c9300002070028b7000020700289b0000207002893000020700209300002060a299300002060a28b300002060829b30000205006893000020500289700002050028930000204422893000020441289700002040828b30000204002cd200002040028d700002040004930000203482993000020313a893000020311acb300002030ba99300002030a2cd200002030a2c9300002030a289b0000203082c93000020308289b000020305289f000020304289f
|18=>0x216002993000021500288300002130a2cd200002130129b3000021300a8930000213002c9300002130028930000212022d9700002120229930000210002010000020f002c93000020f00289f000020d006c93000020c006cd3000020b50689b000020b08299b0000209102010000020750a8b300002075028b300002074a289300002074268930000207412897000020740e8b300002070ba89300002070b289300002070a289300002070928930000207052897000020702a89300002070228d300002070228970000207022893
|19=>0x288102893000028749289300002874068b30000287002cb30000283482c930000283106c9300002831028930000283092dbf00002830929bf0000283002c9f0000283002c93000028300289300002814028930000281006c930000281002893000028041689300002804028d30000280002893000023740299300002330a2c9300002330a28d300002330a2893000023200299300002230b2d9700002230b299f00002230a2c9300002230a299b0000223092d9f000021a022993000021740a8b300002170028930000216082db3
|20=>0x6003002bbf00012330a289300012130a2c9100012030a2c9100010330028930001013002c910001011102d930001011102993000100900299300010030f289300010030a28930001003052c9100010030528930001003002db300010030029b100010030028b300010000f2c810000c030029330000c020089330000483012d370000403002d330000400042939000029b102c93000029b006893000029300a9b3000029300a8b30000293002cb30000293002c93000028b506c93000028b40289b000028b106c93000028b102c93
|21=>0x80030004bb0008002102c9700080021028970008002002c97000800200249f00080020020b30008001492893000800141289f0008001102d9b000800110299b000800110289300080010881b300080010828b300080010828930008001042897000800100ad93000800100299b000800100289b000800100289300080005004bb0008000412493000800010091000080000828bf000800004289300080000120970008000002c930008000002893000800000200400080000008110007003002fbf0007003002e9f00060234b2a97
|22=>0x80220228930008022002897000802200003400080130828a300080130628830008013002cd20008013002c930008013002c8300080130024930008010102c9700080090808140008009080014000800808001000080075028bb000800700289300080044028930008003402893000800311a8b3000800311689700080030d299700080030b28930008003082c9f00080030829b700080030828b3000800305ac93000800305289300080030428b3000800301289b00080030128830008003002c9f0008003002c9b00080030028bb
|23=>0x8283002c9f000820700689300082070028b700082060a28b300082060828b300082030028930008202022993000820110289b0008201002c9b000820100049b00080930028930008091102c930008090102cd2000808f006cb3000808900299f0008083402c9300080834028b30008083402893000808310289300080830928970008083002c9300080830028930008081142c97000808104289f0008081012c9f0008081002c9f000808100289f0008081002897000804300289300080230a289300080220a00b30008022022c97
|24=>0x200030d2c8300200030c2893002000305a89300200030588930020003052893002000304a8930020003042c930020003042c8300200030429930020003042893002000303289300200030128830020003002c9300200030028930020002052c930020002002893002000200019c0020001452893002000114299300200010428930020000012997002000000209300200000008800010c070829930010c060889930010c0300a8b30010c030028b30010c024189b30009013002c910009003052c910009003002c91000828340289f
|25=>0x2020304289300200931d28b700200930929bf002008b0068930020083482d9300200830928b70020083012db7002008104299700200810428970020081002c970020033082d9f002003100211c0020030002900002003000098000200230f289300200230ba8970020023092d9700200230428930020023002c8300200210f2c8300200190429930020013042c93002001100001800200074d289300200070d299700200070929b70020007042897002000405289300200034f2893002000349a9b30020003452893002000344a893
|26=>0x28081002893002808051689300280801028d3002804210289700280220228930028020002c340028003412893002800311289700280030929b30028003092897002800305289b0028003052897002800304289300280030128b7002800300a89300280030028d3002800300289b0028003002897002800300289300280021228b7002800145a893002800141a893002800141289300280010088140028000102897002800000a0250028000002893002800000200400210070d299700210030528b700202070428930020203052c97
|27=>0x400030128b3004000301289f00400030128970040003012893004000300e893004000300ac93004000300a893004000300289f004000300289b004000300289300400021028b7004000200a893004000200289b0040002002893004000104289300400000128930030c830528b70029003052893002900300289300282831028930028202002993002809104289700280835068930028083102893002808305a89300280830028930028081452897002808141289700280811028930028081042897002808100a8970028081002c97
|28=>0x4000b082893004000b01a89f004000b01289b004000a00289300400071868b3004000709a8930040007092cbf0040007092897004000701289f004000700289300400070008140040006082cb30040006082c9300400060828930040005002800004000348ac930040003422893004000340a8930040003402cb30040003402893004000311a893004000310689300400030b2c83004000309a893004000309289b0040003092897004000308a893004000308289700400030828930040003052893004000304a8930040003042893
|29=>0x40083082db3004003a022893004003a0028930040038000011004003309299b00400330928930040030050019004002a00289300400260a2893004002608289300400230b289300400230a28930040020000012004001a002893004001709a893004001701289700400130b28930040013012893004001300a8930040012402893004000f40289f004000f40289b004000f01289b004000f002893004000d100818004000d08289b004000c49289b004000b41689b004000b412893004000b08a893004000b08289f004000b08289b
|30=>0x60013452893006001104089300600074d289300600030c29930060003012897006000200289700600010800040048026082893004802208289300480060828b30048006082893004800400080000480030d289700480030928970048003052893004800303289300480030128970048003002893004800200289b004800200289300480010800140048000080010004028b00689b0040232002d93004020b03289b00400a00000100040093402893004008f41289b004008f40289b004008b41289b00400834028930040083092c97
|31=>0x2080110020000208010002c930208002000c97020022000000302002120029930200210002c93020020200289302000800000000200012002c970200011002d93020001002249302000030001040200002100104020000208289302000010000040200001000000020000010012401400050830bf014000300389b01002230a399b0100003413897010000300389b00a00070d29d700800884068d300800060889d30080003002dff0080003002df300800030029ff0068083086893006800309289700680030028930060033042893
|32=>0x40001300a8930400010002093040000300a89b040000300a893040000300889304000030028930400001412c93024800608289302400061828b702400001000040228202002893022809100ac970228091002c970228012000c100228010002c930228010000c1002200810000800220080000081022000200010c0220000002c000209011102d930208293102c930208232002d930208093002c9302080900028930208052102c970208031102d930208013002c930208012102c970208012002c870208011102d930208011002993
|33=>0x924802000081290000220000028040020000012804000a002c934048006082893400000600289322280b1002c9b222003101a893202003105289b2020031002c9f2020031002897200021304289b200001104a018200001004201820000010020101248022000832120002000001310280020028b310080200008111008000002d930808001012c9f042803100040004200230028930420020002010042001000081004200030088930408023002093040001300a89b
|_=>0
def pmB:Nat→Nat→Nat
|7,0=>0x700a0280d00600e02c00000
|8,0=>0x20ae06d01ac1cab93b006095459a451a004018001de68c233a5456004b39a90060dcb781142200cd408526e0001e2f64240e007803004979fc3e95ac0310b822544010000e80ee1acd7804002091848012a207c0795b00213da18043809480888810e005503145580010b28c06000d5fb0221c0000185c0be3d9f3804712048002c60d6078020107dc7195580400606c01a5d57601007ac7000a90d588f01e71c16b043420d0322c300403c00a9d
|8,1=>0x8510a00145a6b41c9b27cc4480001100000407a8a01cc7000804046bcce800005c59801a8f
|9,0=>0x79a551610fe5b2c7cf795033cf652997b18c0f538b801840f5f99763a42c0a58fd79624ce78db2288690c0431d4fa16981d07a6f84b270542a121303d2f82add6145772b110d26e4349d448bff7a8ad0c409f478a7d7f86e57501ca30095304603403d1eaf28d714805e7051eb5542087d9010002af1903b811ee659680f474c061ab9bf07a699bb82c2d8bddfd10257283d428276e66c4531067da968188ee2ac1fc3e4280ccd75e70622189e43c07b
|9,1=>0x12a1156e949688a503b21a76a3c5132b26f8714d53fc0ac28974c1643ac8423bc7554dd04841f574bc0a60bf1622e96cbbc6441d567aae8425e0de0713ccac92103a61668156a61096c9d492ee028be90aa9c6bc5dc1eaa839a0d4d289e4d90dd2c9416e0958932257eaca4360ce0b0b8615c253dcabc26964622454473b3324b501d2592fa7b14324358a5e9c89dd1488643e1820941943d8cc5944e5853187a0ebc3d9680ce48c243d15f02ecee2a9
|9,2=>0x496b01d7c0b47224e011ce3607516e2e02061e5fea2e1682b1b78e618a9ac56beb4de4bc7cad11f703c41a7f4069e5b74296488c40b0a14dce00cf14753221c7913c064e497aa7b7ec878141ba0dcadce486922c0a54f3081541307e26e874fb171b1d3226007cc1e6ec6fdf887b1e0444a1861440e30b72841e2d19688a00fef78c2c2327e245c79696f27315306a34e53deebc348e4e16bab30886e553bef7cac18b50f26fa745bb2c180ca3a11013
|9,3=>0x3d709deba305bc1e9a140e3702f59532d6586cd7a22c12d0319935a5b67a1e52602e4735bc2da7009b9279177100acaf0af6e2e3410b0f178b64a9303302fc61b18727cfc02eb0129aa441b1ed37ad9c27026054cce1cbf766a1eca60d185aa689eb317c8440248cd5e4fd2123198368de04863164bc119a130e0501a3a7480008087aa345e08606a065601059c9580760fdf92722750b94b270770dfce9abc472c561008e0e8405021ac288538898ed
|9,4=>0x3ad5a41ec0e2d812882e0d069
|10,0=>0x24ecec5b9ea60ae6db441324ea1c4b25577a1bc5c8ad124bc4b13ea632d70ff0ec7142f5a8155454d3c3db727b6791f12830bc1ec501f007a151a43b765ce0da61955907847d3a82042a590ac936eef839a49537040f914985e3a51125c1920cd31b833d2564921ff194bb8bf1b60b4209c588a6f67e190b303169b5231c4720995a6b6b494d59d5b6d5fc368540d7386990fd98c2a649c449224646707088a476341c1b7e13acad13a29250d2dbe1bb
|10,1=>0x70839c3e90b3c8f0c441d91be828ca4315d07698d0cf084809a99f4870e50299f82e8ee85017340aa4c719280ae2309632818689201975760dd6043004d026c96b983bcc8caec0178a4c575b2e3446104c11d3ce265afab65f29849590421296219b65394b54cdb3f49adb02da096d2ab428bae682c797eb93488ba8febdf6264b8722fc0c0d8d4a8d8498d498dc18718bb5b51793c6ac5cebc113858493baa41ae64c340570ae0de92508323898823c
|10,2=>0x7407ddf08a571c8a1c1bd52cb0c80a907102b9893a6625acc5409db6c84792d92886864c7cb217b4b88f10f364a4d12ca543083206809c1028e0eb0d57ac7788e0c464c57d739da4a21f5ec3a74810485c2627a6ce166c2c410e687c3c04f4e917613312c365e4a3866e5698b34e57a2749507d62e47c812cc108d88f8bf9596754f9c146c0349e7990876cf46d03d1c0f205721b56a9f048a4124e1511a85372a761a4b513c03fc3da767aa371cf09c
|10,3=>0x24077d9e32f81463dd0928122a20ce89774630977c1d02e4284096d3342d5a01297f6a24b98cb6b675d5c2214765c5894151821eddd88d3c82485394b080e891198e20aec5ac3e32feaf98b1084181f186b8272e5260b8d00c07e445b774be99cfa963490a5cf426a4e6d645b8de4c0b38e5935490de51f3b432ecf91a89c2dade9d941c41c394b80ad7c0efcbcc3517c52922a9015acd11f98a28417c6b1e20fd04db30a02644a049bdc166f753e90d
|10,4=>0x21835410901043278
|11,0=>0x738300568554ee7685b0f92342ed0e1fa3ec368da2e4402d293f0b5728d852b87b0a0d14c496b2c06345187e0f660d750962347219b2bd822661a5082728d288d1c91f2f09228c236a4c03da347886d4939210b43511d2005f6dd84d3fe5be494fe05924ed342abb62364643d8965caea475b9661834c4fb0e270665272ed0f68d88cbb610cdf03db9f18e4685d99f72c259ce42a0e4a01c407b4748e19d387384a09e61e54d27919707b7388e1cf852
|11,1=>0x1ba0f49b08016a1edc3321
|12,0=>0x1ec212a507a0641e87b0bc1783d83e
|13,0=>0x15
|_,_=>0
def PM (s j:Nat):=let k:=fld (pmB s (j/128)) 11 (j%128);fld (pmP (k/32)) 52 (k%32)
def mkPools (s i:Nat):List (Nat×Nat×(Nat×List Nat)):=let pm:=PM s i;if pm==0 then [] else let ops:=PO s i;
addP pm 0 dom_254 12 roots_254 ops++addP pm 1 dom_251 12 roots_251 ops++addP pm 2 dzo_151_8 6 roots_151 ops++addP pm 3 dom_119 8 roots_119 ops++addP pm 4 dom_239 11 roots_239 ops++addP pm 5 dom_159 8 roots_159 ops++addP pm 6 dom_246 9 roots_246 ops++addP pm 7 dom_253 12 roots_253 ops++addP pm 8 dzo_87_32 6 roots_87 ops++addP pm 9 dom_115 7 roots_115 ops++addP pm 10 dom_63 9 roots_63 ops++addP pm 11 dom_127 11 roots_127 ops++addP pm 12 dom_222 9 roots_222 ops++addP pm 13 dom_191 11 roots_191 ops++addP pm 14 dom_215 7 roots_215 ops++addP pm 15 dom_183 8 roots_183 ops++addP pm 16 dzo_215_8 7 roots_215 ops++addP pm 17 dom_207 7 roots_207 ops++addP pm 18 dom_231 7 roots_231 ops++addP pm 19 dzo_215_32 7 roots_215 ops++addP pm 20 dom_151 6 roots_151 ops++addP pm 21 dom_238 9 roots_238 ops++addP pm 22 dzo_247_8 8 roots_247 ops++addP pm 23 dzo_182_8 6 roots_182 ops++addP pm 24 dom_247 10 roots_247 ops++addP pm 25 dom_223 10 roots_223 ops++addP pm 26 dzo_223_32 8 roots_223 ops++addP pm 27 dom_87 6 roots_87 ops++addP pm 28 dom_111 8 roots_111 ops++addP pm 29 dom_79 6 roots_79 ops++addP pm 30 dom_221 9 roots_221 ops++addP pm 31 dzo_183_8 7 roots_183 ops++addP pm 32 dom_237 9 roots_237 ops++addP pm 33 dzo_95_32 7 roots_95 ops++addP pm 34 dom_157 7 roots_157 ops++addP pm 35 dom_245 8 roots_245 ops++addP pm 36 dom_243 9 roots_243 ops++addP pm 37 dom_123 9 roots_123 ops++addP pm 38 dom_219 8 roots_219 ops++addP pm 39 dom_175 8 roots_175 ops++addP pm 40 dom_189 9 roots_189 ops++addP pm 41 dom_167 6 roots_167 ops++addP pm 42 dom_95 8 roots_95 ops++addP pm 43 dom_190 10 roots_190 ops++addP pm 44 dom_126 10 roots_126 ops++addP pm 45 dom_47 6 roots_47 ops++addP pm 46 dom_55 5 roots_55 ops++addP pm 47 dzo_181_8 6 roots_181 ops++addP pm 48 dom_143 5 roots_143 ops++addP pm 49 dom_103 5 roots_103 ops++addP pm 50 dzo_219_32 7 roots_219 ops++addP pm 51 dom_31 5 roots_31 ops
def mkCut (s i:Nat) (g:Nat×Nat×Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPoolG e.1 e.2.1 (s-1) e.2.2 g zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬RunD true dom_255 gM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h;split at h
  · simp at h
  · rw [List.any_eq_true] at h;obtain ⟨e,he,hchk⟩:=h;simp only [List.mem_append,or_assoc] at he
    rcases he with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51
    · obtain ⟨_,rfl⟩:=mem_addP h0;exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h1;exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h2;exact cpcs (by decide +kernel) lowS_zo_151_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h3;exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h4;exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h5;exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h6;exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h7;exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h8;exact cpcs (by decide +kernel) lowS_zo_87_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h9;exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h10;exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h11;exact cpcs (by decide +kernel) lowS_127 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h12;exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h13;exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h14;exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h15;exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h16;exact cpcs (by decide +kernel) lowS_zo_215_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h17;exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h18;exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h19;exact cpcs (by decide +kernel) lowS_zo_215_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h20;exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h21;exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h22;exact cpcs (by decide +kernel) lowS_zo_247_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h23;exact cpcs (by decide +kernel) lowS_zo_182_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h24;exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h25;exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h26;exact cpcs (by decide +kernel) lowS_zo_223_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h27;exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h28;exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h29;exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h30;exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h31;exact cpcs (by decide +kernel) lowS_zo_183_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h32;exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h33;exact cpcs (by decide +kernel) lowS_zo_95_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h34;exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h35;exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h36;exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h37;exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h38;exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h39;exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h40;exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h41;exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h42;exact cpcs (by decide +kernel) lowS_95 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h43;exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h44;exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h45;exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h46;exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h47;exact cpcs (by decide +kernel) lowS_zo_181_8_148 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h48;exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h49;exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h50;exact cpcs (by decide +kernel) lowS_zo_219_32_82 _ g hchk
    · obtain ⟨_,rfl⟩:=mem_addP h51;exact cpcs (by decide +kernel) lowS_31 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool dom_254 12 s (0,roots_254.map (·&&&dom_254)) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬RunD true dom_255 gM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h
def symsG:List (List (Nat×Nat)):=[[(0xffffffffffffffff0000000000000000,64),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256&&(applyMoves ms dom_255==dom_255)&&(applyMoves ms gM==gM))=true:=by decide +kernel
def ori (zs:List Nat):=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_255 gM v ys):RunD true dom_255 gM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP dom_255 gM mpG SD SS NN hAt idxH ori 0 mkPools s
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_128 : ∀ i, 128 ≤ i → i < 155 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 155 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_128 : ∀ i, 128 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_256 : ∀ i, 256 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_384 : ∀ i, 384 ≤ i → i < 512 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_512 : ∀ i, 512 ≤ i → i < 521 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 512 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 521 → Z 9 i = true := (range_split (range_split z9_0 z9_128) (range_split z9_256 (range_split z9_384 z9_512)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_128 : ∀ i, 128 ≤ i → i < 256 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_256 : ∀ i, 256 ≤ i → i < 384 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_384 : ∀ i, 384 ≤ i → i < 512 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 128 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_512 : ∀ i, 512 ≤ i → i < 518 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 6 512 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 518 → Z 10 i = true := (range_split (range_split z10_0 z10_128) (range_split z10_256 (range_split z10_384 z10_512)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11_0 : ∀ i, 0 ≤ i → i < 128 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11_128 : ∀ i, 128 ≤ i → i < 136 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 8 128 = true)
private theorem z11 : ∀ i, 0 ≤ i → i < 136 → Z 11 i = true := (range_split z11_0 z11_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 11 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 11 0 = true)
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
  · exact z7 i (Nat.zero_le i) hi
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
theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.and, inputs := [10, 11] }, { op := GateOp.or, inputs := [3, 7] }, { op := GateOp.or, inputs := [13, 8] }, { op := GateOp.and, inputs := [5, 14] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [16, 6] }, { op := GateOp.and, inputs := [3, 17] }, { op := GateOp.and, inputs := [4, 9] }, { op := GateOp.or, inputs := [12, 15] }, { op := GateOp.or, inputs := [20, 18] }, { op := GateOp.or, inputs := [21, 19] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 22⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51616_aux

theorem PEqualNP.Outside.L_meta_51616 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51616_aux.main
